(* ========================================================================= *)
(* word_allocProof_p1: part 1 (HOL4 lines 1-5707) of the port of HOL4        *)
(* compiler/backend/proofs/word_allocProofScript.sml (CakeML v3479).         *)
(* Correctness proof for word_alloc.  Part 2 is word_allocProof_p2.ml;       *)
(* word_allocProof.ml loads both.                                            *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - wordLang/wordSem names as in names.tsv: wl_evaluate, wl_get_var,        *)
(*   wl_state_locals st (HOL4 st.locals), wl_state_permute_fupd (K p) st     *)
(*   (HOL4 st with permute := p), wl_Seq, wl_Move, wordSem_Break (result),   *)
(*   wl_Error, ...; HOL4 numset_list_insert (word_alloc's, brought to the    *)
(*   front by the script) is word_alloc_numset_list_insert; HOL4 merge_moves *)
(*   is word_alloc_merge_moves; hide is word_allocProof_hide.                *)
(* - Library: EVERY = ALL, set = set_of_list, FOLDR f e l = ITLIST f l e,    *)
(*   GENLIST = list_of_seq, ZIP (a,b) = ZIP a b (HOL Light's ZIP has the     *)
(*   length of its first list; every ZIP statement here has the length       *)
(*   hypothesis or a context that implies it), n2w n = word n, () = one.     *)
(* - HOL4 paired lambdas \(x,y). t are \xy. match xy with (x,y) -> t (the    *)
(*   form of word_alloc.ml, pair_CASE).                                      *)
(* - Free variables of the HOL4 statements are universally quantified at the *)
(*   front; the states of one statement share the type (A,C,FFI)wl_state    *)
(*   (HOL4 would let two unrelated states have different 'c and 'ffi).       *)
(* - LET_FORALL_ELIM': the S combinator is written out as a lambda.          *)
(* - Blocks commented out in the HOL4 script (colouring_ok_alt and the       *)
(*   get_clash_sets lemmas, every_var_in_get_clash_set,                      *)
(*   stack_size_map_excp_const) are not ported.                              *)
(* - WALLOCPAUX_ names are local helpers of this file (not HOL4 names).      *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mllist.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/reg_alloc/proofs/reg_allocProof.ml";;
needs "compiler/backend/reg_alloc/proofs/linear_scanProof.ml";;
needs "compiler/backend/reg_alloc/linear_scan.ml";;
needs "compiler/backend/word_alloc.ml";;

prioritize_num();;
type_invention_error := true;;

(* helper: destructure a tuple-valued term into the given variables, keeping *)
(* the equation as an assumption                                            *)

let WALLOCPAUX_TUPLE_TAC (tm:term) (vs:term list) : tactic =
  let eq = mk_eq(tm, end_itlist (curry mk_pair) vs) in
  SUBGOAL_THEN (list_mk_exists(vs,eq))
    (REPEAT_TCL CHOOSE_THEN (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)) THENL
   [REWRITE_TAC[GSYM EXISTS_PAIR_THM] THEN MESON_TAC[]; ALL_TAC];;

(* the defining equations of some case constants (for rewriting) *)

let WALLOCPAUX_wl_result_CASE = (case_info_of_tyname "wl_result").ci_def;;

let WALLOCPAUX_reg_imm_CASE = (case_info_of_tyname "reg_imm").ci_def;;

let WALLOCPAUX_exc_CASE = (case_info_of_tyname "exc").ci_def;;

let WALLOCPAUX_word_loc_CASE = (case_info_of_tyname "word_loc").ci_def;;

let WALLOCPAUX_memop_distinct = (case_info_of_tyname "memop").ci_distinct;;

let WALLOCPAUX_wl_result_distinct = (case_info_of_tyname "wl_result").ci_distinct;;

let WALLOCPAUX_stack_frame_CASE = (case_info_of_tyname "stack_frame").ci_def;;

let WALLOCPAUX_stack_frame_inject = (case_info_of_tyname "stack_frame").ci_inject;;

(* case split of a ((A)wl_result)option variable into all constructors *)

let WALLOCPAUX_RESULT_CASES_TAC (r:term) : tactic =
  MP_TAC(ISPEC r (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `rr:(A)wl_result` SUBST_ALL_TAC)) THENL
   [ALL_TAC;
    MP_TAC(ISPEC `rr:(A)wl_result` (cases "wl_result")) THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC))] THEN
  REWRITE_TAC([option_CASE; WALLOCPAUX_wl_result_CASE; option_INJ; pair_CASE] @
              WALLOCPAUX_wl_result_distinct);;

(* HOL4 lines 17-24: simpset and parser settings (temp_delsimps,            *)
(* diminish_srw_ss, Parse.hide "mem", numset_list_insert brought to the     *)
(* front): nothing to do in HOL Light                                       *)

let WALLOCPAUX_CASES_IF (v:term) (th:thm) : tactic =
  fun (asl,w as g) ->
    if mem v (frees w) then STRUCT_CASES_TAC (ISPEC v th) g else ALL_TAC g;;

let WALLOCPAUX_INST_CASES_TAC : tactic =
  STRUCT_CASES_TAC (ISPEC `i:(A)inst` (cases "inst")) THEN
  WALLOCPAUX_CASES_IF `a:(A)asm_arith` (cases "asm_arith") THEN
  WALLOCPAUX_CASES_IF `a:fp` (cases "fp") THEN
  WALLOCPAUX_CASES_IF `a0:memop` (cases "memop") THEN
  WALLOCPAUX_CASES_IF `a2:(A)addr` (cases "addr") THEN
  WALLOCPAUX_CASES_IF `a3:(A)reg_imm` (cases "reg_imm");;

(* HOL4 line 27: the same theorem is SUBSET_OF_INSERT of hol4/basic.ml       *)
(* (quantifiers in the order x, s); bound here as an alias of it            *)
let SUBSET_OF_INSERT = SUBSET_OF_INSERT;;

(* HOL4 line 33 *)
let INJ_UNION = prove
 (`!(f:A->B) (A:A->bool) B.
     INJ f (A UNION B) UNIV ==> INJ f A UNIV /\ INJ f B UNIV`,
  REWRITE_TAC[INJ; IN_UNION; IN_UNIV] THEN MESON_TAC[]);;

(* HOL4 line 43: INJ_less *)
let word_allocProof_INJ_less = prove
 (`!(f:A->B) s s'. INJ f s' UNIV /\ s SUBSET s' ==> INJ f s UNIV`,
  REWRITE_TAC[INJ; SUBSET; IN_UNIV] THEN MESON_TAC[]);;

(* HOL4 line 51 (S written out: S g f = \x. g x (f x)) *)
let LET_FORALL_ELIM' = prove
 (`!(f:A->bool) v. LET f v <=> (!) (\x. ((==>) o (=) v) x (f x))`,
  REWRITE_TAC[LET_DEF; o_THM] THEN MESON_TAC[]);;

(* HOL4 line 57: hide *)
let word_allocProof_hide_def = cake_def
  `word_allocProof_hide (x:A) = x`;;

(* HOL4 line 61 *)
let INJ_IMP_IMAGE_DIFF = prove
 (`!(f:A->B) s t.
     INJ f (s UNION t) UNIV ==> IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t`,
  REWRITE_TAC[INJ; EXTENSION; IN_IMAGE; IN_DIFF; IN_UNION; IN_UNIV] THEN
  MESON_TAC[]);;

(* HOL4 line 70 *)
let INJ_IMP_IMAGE_DIFF_single = prove
 (`!(f:A->B) s n.
     INJ f (s UNION {n}) UNIV ==> IMAGE f s DIFF {f n} = IMAGE f (s DIFF {n})`,
  REWRITE_TAC[INJ; EXTENSION; IN_IMAGE; IN_DIFF; IN_UNION; IN_UNIV; IN_SING] THEN
  MESON_TAC[]);;

(* HOL4 line 79 *)
let INJ_ALL_DISTINCT_MAP = prove
 (`!(f:A->B) ls. ALL_DISTINCT (MAP f ls) ==> INJ f (set_of_list ls) UNIV`,
  GEN_TAC THEN REWRITE_TAC[INJ; IN_SET_OF_LIST; IN_UNIV] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL_DISTINCT; MEM] THEN
  REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[]);;

(* HOL4 line 100: colouring_ok (Seq: normal live sets, internal clash sets; *)
(* If: all of them must be live at once; Call: returning handler and        *)
(* exception handler; the rest: live before must be fine, and the clash set *)
(* must be fine) *)
let colouring_ok_def = sem1aux_def_wf
  `measure (\(f:num->B,p:(A)wl_prog,live:num_set,lt:(num_set#num_set)list).
              wl_prog_size (\x:A. 0) p)`
  SEM1AUX_TC_TAC (list_mk_conj
 [`(colouring_ok:(num->B)->(A)wl_prog->num_set->(num_set#num_set)list->bool)
      f (wl_Seq s1 s2) live lt <=>
     let s2_live = get_live s2 live lt in
     let s1_live = get_live s1 s2_live lt in
       INJ f (domain s1_live) UNIV /\
       colouring_ok f s2 live lt /\ colouring_ok f s1 s2_live lt`;
  `(colouring_ok:(num->B)->(A)wl_prog->num_set->(num_set#num_set)list->bool)
      f (wl_If cmp r1 ri e2 e3) live lt <=>
     let e2_live = get_live e2 live lt in
     let e3_live = get_live e3 live lt in
     let union_live = union e2_live e3_live in
     let merged = match ri with
                    Reg r2 -> insert r2 one (insert r1 one union_live)
                  | _ -> insert r1 one union_live in
       INJ f (domain merged) UNIV /\
       colouring_ok f e2 live lt /\ colouring_ok f e3 live lt`;
  `(colouring_ok:(num->B)->(A)wl_prog->num_set->(num_set#num_set)list->bool)
      f (wl_Call (SOME (v,cutset,ret_handler,l1,l2)) dest args h) live lt <=>
     let args_set = word_alloc_numset_list_insert args LN in
     let allnames = union (SND cutset) (FST cutset) in
       INJ f (domain (union allnames args_set)) UNIV /\
       INJ f (domain (word_alloc_numset_list_insert v allnames)) UNIV /\
       colouring_ok f ret_handler live lt /\
       (match h with
          NONE -> T
        | SOME (v,prog,l1,l2) ->
            INJ f (domain (insert v one allnames)) UNIV /\
            colouring_ok f prog live lt)`;
  `(colouring_ok:(num->B)->(A)wl_prog->num_set->(num_set#num_set)list->bool)
      f (MustTerminate p) live lt <=>
     colouring_ok f p live lt`;
  `(colouring_ok:(num->B)->(A)wl_prog->num_set->(num_set#num_set)list->bool)
      f (wl_Loop names body exit_names) live lt <=>
     INJ f (domain names) UNIV /\
     INJ f (domain exit_names) UNIV /\
     colouring_ok f body names (CONS (names,exit_names) lt)`;
  `(colouring_ok:(num->B)->(A)wl_prog->num_set->(num_set#num_set)list->bool)
      f prog live lt <=>
     let lset = get_live prog live lt in
     let iset = union (get_writes prog) live in
       INJ f (domain lset) UNIV /\ INJ f (domain iset) UNIV`]);;
let colouring_ok_ind = cake_ind "colouring_ok";;

(* HOL4 line 148 *)
let word_state_eq_rel_def = cake_def
  `word_state_eq_rel (s:(A,C,FFI)wl_state) (t:(A,C,FFI)wl_state) <=>
     wl_state_fp_regs t = wl_state_fp_regs s /\
     wl_state_store t = wl_state_store s /\
     wl_state_locals_size t = wl_state_locals_size s /\
     wl_state_stack t = wl_state_stack s /\
     wl_state_stack_limit t = wl_state_stack_limit s /\
     wl_state_stack_max t = wl_state_stack_max s /\
     wl_state_stack_size t = wl_state_stack_size s /\
     wl_state_memory t = wl_state_memory s /\
     wl_state_mdomain t = wl_state_mdomain s /\
     wl_state_sh_mdomain t = wl_state_sh_mdomain s /\
     wl_state_gc_fun t = wl_state_gc_fun s /\
     wl_state_handler t = wl_state_handler s /\
     wl_state_clock t = wl_state_clock s /\
     wl_state_code t = wl_state_code s /\
     wl_state_ffi t = wl_state_ffi s /\
     wl_state_be t = wl_state_be s /\
     wl_state_termdep t = wl_state_termdep s /\
     wl_state_compile t = wl_state_compile s /\
     wl_state_compile_oracle t = wl_state_compile_oracle s /\
     wl_state_code_buffer t = wl_state_code_buffer s /\
     wl_state_data_buffer t = wl_state_data_buffer s`;;

(* HOL4 line 177 *)
let strong_locals_rel_def = cake_def
  `strong_locals_rel (f:num->num) (ls:num->bool) (slocs:A spt) (tlocs:A spt) <=>
     !n v. n IN ls /\ lookup n slocs = SOME v ==> lookup (f n) tlocs = SOME v`;;

(* HOL4 line 184 *)
let strong_locals_rel_subset_domain = prove
 (`!f s (l1:A spt) (l2:A spt).
     strong_locals_rel f s l1 l2 /\ s SUBSET domain l1
     ==> !v. v IN s ==> f v IN domain l2`,
  REWRITE_TAC[strong_locals_rel_def; SUBSET; domain_lookup] THEN MESON_TAC[]);;

(* HOL4 line 200: domain_numset_list_insert *)
let word_allocProof_domain_numset_list_insert = prove
 (`!ls locs.
     domain (word_alloc_numset_list_insert ls locs) =
     domain locs UNION set_of_list ls`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[word_alloc_numset_list_insert_def; set_of_list; UNION_EMPTY;
                  domain_insert] THEN
  SET_TAC[]);;

(* HOL4 line 208 *)
let strong_locals_rel_get_var = prove
 (`!f live (st:(A,C,FFI)wl_state) (cst:(A,C,FFI)wl_state) n x.
     strong_locals_rel f live (wl_state_locals st) (wl_state_locals cst) /\
     n IN live /\
     wl_get_var n st = SOME x
     ==> wl_get_var (f n) cst = SOME x`,
  REWRITE_TAC[wl_get_var_def; strong_locals_rel_def] THEN MESON_TAC[]);;

(* HOL4 line 218 *)
let strong_locals_rel_get_var_imm = prove
 (CASE_TERM
  `!f live (st:(A,C,FFI)wl_state) (cst:(A,C,FFI)wl_state) n x.
     strong_locals_rel f live (wl_state_locals st) (wl_state_locals cst) /\
     (match n with Reg n -> n IN live | _ -> T) /\
     wl_get_var_imm n st = SOME x
     ==> wl_get_var_imm (apply_colour_imm f n) cst = SOME x`,
  REPEAT GEN_TAC THEN CASES_ON `n:(A)reg_imm` THEN
  SIMP[wl_get_var_imm_def; apply_colour_imm_def] THEN
  MESON_TAC[strong_locals_rel_get_var]);;

(* HOL4 line 229 *)
let strong_locals_rel_get_vars = prove
 (`!ls y f live (st:(A,C,FFI)wl_state) (cst:(A,C,FFI)wl_state).
     strong_locals_rel f live (wl_state_locals st) (wl_state_locals cst) /\
     (!x. MEM x ls ==> x IN live) /\
     wl_get_vars ls st = SOME y
     ==> wl_get_vars (MAP f ls) cst = SOME y`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wl_get_vars_def; MAP; MEM] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[option_case_eq; option_DISTINCT; option_INJ] THEN STRIP_TAC THEN
  EXISTS_TAC `a:(A)word_loc` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[strong_locals_rel_get_var]; ALL_TAC] THEN
  EXISTS_TAC `a':((A)word_loc)list` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 248 *)
let strong_locals_rel_UNION = prove
 (`!f A B (t:A spt) l.
     strong_locals_rel f (A UNION B) t l <=>
     strong_locals_rel f A t l /\ strong_locals_rel f B t l`,
  REWRITE_TAC[strong_locals_rel_def; IN_UNION] THEN MESON_TAC[]);;

(* HOL4 line 255 *)
let domain_big_union_subset = prove
 (`!ls (a:(A)wl_exp).
     MEM a ls ==>
     domain (get_live_exp a) SUBSET domain (big_union (MAP get_live_exp ls))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; MAP; big_union_def; ITLIST] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[domain_union; SUBSET_UNION] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:(A)wl_exp`) THEN
  ASM_REWRITE_TAC[GSYM big_union_def] THEN SET_TAC[]);;

(* HOL4 line 265: val size_tac (ML) *)

(* HOL4 line 267 *)
let apply_nummap_key_domain = prove
 (`!f (names:A spt). domain (apply_nummap_key f names) = IMAGE f (domain names)`,
  REWRITE_TAC[apply_nummap_key_def; domain_fromAList; EXTENSION; IN_SET_OF_LIST;
              IN_IMAGE; MEM_MAP; EXISTS_PAIR_THM; FORALL_PAIR_THM; pair_CASE;
              PAIR_EQ] THEN
  REWRITE_TAC[domain_lookup; MEM_toAList] THEN MESON_TAC[]);;

(* HOL4 line 277 *)
let cut_names_lemma = prove
 (`!(names:B spt) (slocs:A spt) tlocs x f.
     INJ f (domain names) UNIV /\
     cut_names names slocs = SOME x /\
     strong_locals_rel f (domain names) slocs tlocs
     ==> ?y. cut_names (apply_nummap_key f names) tlocs = SOME y /\
             domain y = IMAGE f (domain x) /\
             strong_locals_rel f (domain names) x y /\
             INJ f (domain x) UNIV /\
             domain x = domain names`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_names_def; apply_nummap_key_domain] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `domain (inter (slocs:A spt) (names:B spt)) = domain names`
    ASSUME_TAC THENL [REWRITE_TAC[domain_inter] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:num->num) (domain (names:B spt)) SUBSET domain (tlocs:A spt)`
    ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[strong_locals_rel_def; SUBSET; domain_lookup]) THEN
    REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[option_INJ] THEN
  EXISTS_TAC `inter (tlocs:A spt) (apply_nummap_key f (names:B spt))` THEN
  ASM_REWRITE_TAC[domain_inter; apply_nummap_key_domain] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[strong_locals_rel_def; lookup_inter] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `v:A`] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  SUBGOAL_THEN `?w. lookup n (names:B spt) = SOME w` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[domain_lookup]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `lookup n (slocs:A spt) = SOME v` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN CASES_ON `lookup n (slocs:A spt)` THEN
    ASM_REWRITE_TAC[option_CASE; option_DISTINCT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[option_CASE] THEN
  SUBGOAL_THEN `lookup ((f:num->num) n) (tlocs:A spt) = SOME v` SUBST1_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[strong_locals_rel_def]) THEN
    ASM_MESON_TAC[domain_lookup];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:num->num) n IN domain (apply_nummap_key f (names:B spt))`
    MP_TAC THENL
   [REWRITE_TAC[apply_nummap_key_domain] THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[domain_lookup] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[option_CASE]);;

(* helpers: apply_nummaps_key on a pair, the SOME cases of cut_envs and    *)
(* cut_env                                                                  *)

let WALLOCPAUX_apply_nummaps_key_pair = prove
 (`!f (n1:A spt) (n2:B spt).
     apply_nummaps_key f (n1,n2) = (apply_nummap_key f n1,apply_nummap_key f n2)`,
  REWRITE_TAC[apply_nummaps_key_def; apply_nummap_key_def]);;

let WALLOCPAUX_cut_envs_SOME = prove
 (`!n1 n2 (env:A spt) x1 x2.
     cut_envs (n1,n2) env = SOME (x1,x2) <=>
     cut_names n1 env = SOME x1 /\ cut_names n2 env = SOME x2`,
  REWRITE_TAC[cut_envs_def; FST; SND; pair_case_eq; option_case_eq;
              option_DISTINCT; option_INJ; PAIR_EQ] THEN
  MESON_TAC[]);;

let WALLOCPAUX_cut_env_SOME = prove
 (`!names (env:A spt) x.
     wl_cut_env names env = SOME x <=>
     ?x1 x2. cut_envs names env = SOME (x1,x2) /\ x = union x2 x1`,
  REWRITE_TAC[wl_cut_env_def; pair_case_eq; option_case_eq;
              option_DISTINCT; option_INJ; PAIR_EQ] THEN
  MESON_TAC[PAIR]);;

(* HOL4 line 313 *)
let cut_envs_lemma = prove
 (`!f (n1:num_set) (n2:num_set) (slocs:A spt) x1 x2 tlocs.
     INJ f (domain n1) UNIV /\
     INJ f (domain n2) UNIV /\
     cut_envs (n1,n2) slocs = SOME (x1,x2) /\
     strong_locals_rel f (domain n1) slocs tlocs /\
     strong_locals_rel f (domain n2) slocs tlocs
     ==> ?y1 y2.
           cut_envs (apply_nummaps_key f (n1,n2)) tlocs = SOME (y1,y2) /\
           domain y1 = IMAGE f (domain n1) /\
           domain y2 = IMAGE f (domain n2) /\
           strong_locals_rel f (domain n1) x1 y1 /\
           strong_locals_rel f (domain n2) x2 y2 /\
           INJ f (domain x1) UNIV /\
           INJ f (domain x2) UNIV /\
           domain x1 = domain n1 /\
           domain x2 = domain n2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_apply_nummaps_key_pair; WALLOCPAUX_cut_envs_SOME] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`n2:num_set`; `slocs:A spt`; `tlocs:A spt`; `x2:A spt`; `f:num->num`]
    cut_names_lemma) THEN
  MP_TAC(ISPECL [`n1:num_set`; `slocs:A spt`; `tlocs:A spt`; `x1:A spt`; `f:num->num`]
    cut_names_lemma) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:A spt` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `y2:A spt` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`y1:A spt`; `y2:A spt`] THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 340 *)
let cut_env_lemma = prove
 (`!f (names:num_set#num_set) (slocs:A spt) x tlocs.
     INJ f (domain (FST names) UNION domain (SND names)) UNIV /\
     wl_cut_env names slocs = SOME x /\
     strong_locals_rel f (domain (FST names) UNION domain (SND names)) slocs tlocs
     ==> ?y. wl_cut_env (apply_nummaps_key f names) tlocs = SOME y /\
             domain y = IMAGE f (domain x) /\
             strong_locals_rel f (domain (FST names) UNION domain (SND names)) x y /\
             INJ f (domain x) UNIV /\
             domain x = domain (FST names) UNION domain (SND names)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?n1 n2. names:num_set#num_set = (n1,n2)`
    (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC)) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  REWRITE_TAC[FST; SND; WALLOCPAUX_cut_env_SOME] THEN
  REWRITE_TAC[WALLOCPAUX_apply_nummaps_key_pair; WALLOCPAUX_cut_envs_SOME] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->num`; `n1:num_set`; `n2:num_set`;
                 `slocs:A spt`; `x1:A spt`; `x2:A spt`; `tlocs:A spt`] cut_envs_lemma) THEN
  ASM_REWRITE_TAC[WALLOCPAUX_apply_nummaps_key_pair; WALLOCPAUX_cut_envs_SOME] THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[strong_locals_rel_UNION]) THEN
    ASM_MESON_TAC[INJ_UNION];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:A spt` (X_CHOOSE_THEN `y2:A spt` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `union (y2:A spt) y1` THEN
  CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`y1:A spt`; `y2:A spt`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[domain_union; IMAGE_UNION] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC; ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[UNION_COMM]] THEN
  REWRITE_TAC[strong_locals_rel_def; lookup_union] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `v:A`] THEN
  CASES_ON `lookup n (x2:A spt)` THEN ASM_REWRITE_TAC[option_CASE] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `n IN domain (n1:num_set) /\ ~(n IN domain (n2:num_set))`
      STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[domain_lookup; lookup_NONE_domain]; ALL_TAC] THEN
    SUBGOAL_THEN `lookup ((f:num->num) n) (y2:A spt) = NONE` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[lookup_NONE_domain; IN_IMAGE] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INJ; IN_UNION; IN_UNIV]) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[option_CASE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[strong_locals_rel_def]) THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `lookup ((f:num->num) n) (y2:A spt) = SOME v` SUBST1_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[strong_locals_rel_def]) THEN
      ASM_MESON_TAC[domain_lookup; option_INJ];
      REWRITE_TAC[option_CASE]]]);;

(* HOL4 line 381 *)
let nummaps_to_nummap = prove
 (`!f (a:A spt#B spt).
     FST (apply_nummaps_key f a) = apply_nummap_key f (FST a) /\
     SND (apply_nummaps_key f a) = apply_nummap_key f (SND a)`,
  REWRITE_TAC[apply_nummaps_key_def; apply_nummap_key_def]);;

(* HOL4 line 388 (HOL4's variable C is c: C is a constant here) *)
let INJ_union = prove
 (`!(f:A->B) A B c. INJ f (A UNION B) c ==> INJ f A c /\ INJ f B c`,
  REWRITE_TAC[INJ; IN_UNION] THEN MESON_TAC[]);;

(* HOL4 line 394 *)
let LENGTH_list_rerrange = prove
 (`!mover (xs:A list). LENGTH (list_rearrange mover xs) = LENGTH xs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[list_rearrange_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH_LIST_OF_SEQ]);;

(* HOL4 line 403 *)
let list_rearrange_perm = prove
 (`!(xs:A list) ys. PERM xs ys ==> ?perm. list_rearrange perm xs = ys`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP PERM_BIJ) THEN
  STRIP_TAC THEN EXISTS_TAC `f:num->num` THEN ASM_REWRITE_TAC[list_rearrange_def]);;

(* HOL4 line 415 *)
let GENLIST_MAP = prove
 (`!(l:A list) m (f:A->B) k.
     (!i. i < LENGTH l ==> m i < LENGTH l) /\ k <= LENGTH l ==>
     list_of_seq (\i. EL (m i) (MAP f l)) k =
     MAP f (list_of_seq (\i. EL (m i) l) k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MAP_LIST_OF_SEQ] THEN
  MATCH_MP_TAC GENLIST_CONG THEN REWRITE_TAC[o_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC EL_MAP THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 425 *)
let list_rearrange_MAP = prove
 (`!l (f:A->B) m. list_rearrange m (MAP f l) = MAP f (list_rearrange m l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[list_rearrange_def; LENGTH_MAP] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC GENLIST_MAP THEN REWRITE_TAC[LE_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[BIJ; INJ]) THEN
  REWRITE_TAC[IN_COUNT] THEN MESON_TAC[]);;

(* HOL4 line 432: val ALL_DISTINCT_FST = ALL_DISTINCT_MAP |> Q.ISPEC FST     *)
(* (ML, an instance of a library theorem) *)

(* HOL4 line 442 *)
let env_to_list_perm = prove
 (CASE_TERM
  `!(y:((A)word_loc)spt) x f perm tperm.
     domain y = IMAGE f (domain x) /\
     INJ f (domain x) UNIV /\
     strong_locals_rel f (domain x) x y
     ==> let (l,permute) = env_to_list y perm in
         ?perm'.
           let (l',permute') = env_to_list x perm' in
             permute' = tperm /\
             MAP (\xy. match xy with (x,y) -> (f x,y)) l' = l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[env_to_list_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE] THEN
  ABBREV_TAC `xls = sort key_val_compare (toAList (x:((A)word_loc)spt))` THEN
  ABBREV_TAC `yls = sort key_val_compare (toAList (y:((A)word_loc)spt))` THEN
  ABBREV_TAC `g = \xy:num#(A)word_loc. pair_CASE xy (\x y. ((f:num->num) x,y))` THEN
  SUBGOAL_THEN `!t:((A)word_loc)spt. ALL_DISTINCT (sort key_val_compare (toAList t))`
    ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`toAList (t:((A)word_loc)spt)`;
                   `sort key_val_compare (toAList (t:((A)word_loc)spt))`]
      ALL_DISTINCT_PERM) THEN
    REWRITE_TAC[sort_PERM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC (ISPEC `FST:num#(A)word_loc->num` ALL_DISTINCT_MAP) THEN
    REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList];
    ALL_TAC] THEN
  SUBGOAL_THEN `PERM (MAP (g:num#(A)word_loc->num#(A)word_loc) xls) yls`
    ASSUME_TAC THENL
   [MATCH_MP_TAC PERM_ALL_DISTINCT THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN CONJ_TAC THENL
       [ALL_TAC; ASM_MESON_TAC[]] THEN
      MAP_EVERY EXPAND_TAC ["xls"; "g"] THEN
      REWRITE_TAC[sort_MEM; FORALL_PAIR_THM; pair_CASE; PAIR_EQ; MEM_toAList] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[INJ; IN_UNIV]) THEN
      ASM_REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      MAP_EVERY EXPAND_TAC ["xls"; "yls"; "g"] THEN
      REWRITE_TAC[FORALL_PAIR_THM; MEM_MAP; sort_MEM; EXISTS_PAIR_THM; pair_CASE;
                  PAIR_EQ; MEM_toAList] THEN
      REPEAT GEN_TAC THEN EQ_TAC THENL
       [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[strong_locals_rel_def]) THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[domain_lookup] THEN
        ASM_MESON_TAC[];
        DISCH_TAC THEN
        SUBGOAL_THEN `p1 IN domain (y:((A)word_loc)spt)` MP_TAC THENL
         [ASM_MESON_TAC[domain_lookup]; ALL_TAC] THEN
        ASM_REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
        FIRST_ASSUM(MP_TAC o REWRITE_RULE[domain_lookup]) THEN
        DISCH_THEN(X_CHOOSE_TAC `w:(A)word_loc`) THEN
        MAP_EVERY EXISTS_TAC [`k:num`; `w:(A)word_loc`] THEN ASM_REWRITE_TAC[] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[strong_locals_rel_def]) THEN
        ASM_MESON_TAC[option_INJ; domain_lookup]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `PERM (yls:(num#(A)word_loc)list) (list_rearrange (perm 0) yls)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC PERM_list_rearrange THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?p. list_rearrange p (MAP (g:num#(A)word_loc->num#(A)word_loc) xls) =
                    list_rearrange (perm 0) yls`
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC list_rearrange_perm THEN ASM_MESON_TAC[PERM_TRANS]; ALL_TAC] THEN
  EXISTS_TAC `\n. if n = 0 then (p:num->num) else tperm (n - 1)` THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; ADD_EQ_0; ARITH_EQ; ADD_SUB];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[list_rearrange_MAP]]);;

(* HOL4 line 669 *)
let env_to_list_keys = prove
 (CASE_TERM
  `!(x:((A)word_loc)spt) perm.
     let (l,permute) = env_to_list x perm in set_of_list (MAP FST l) = domain x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[env_to_list_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE] THEN
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_MAP; mem_list_rearrange; sort_MEM;
              EXISTS_PAIR_THM; MEM_toAList; FST; domain_lookup] THEN
  MESON_TAC[]);;

(* HOL4 line 515 *)
let push_env_s_val_eq = prove
 (CASE_TERM
  `!(st:(A,C,FFI)wl_state) (cst:(A,C,FFI)wl_state) x y x' y' f
    (b:(num#(A)wl_prog#num#num)option) b' tperm.
     wl_state_handler st = wl_state_handler cst /\
     wl_state_stack st = wl_state_stack cst /\
     wl_state_locals_size st = wl_state_locals_size cst /\
     domain y = IMAGE f (domain x) /\
     INJ f (domain x) UNIV /\
     domain y' = IMAGE f (domain x') /\
     INJ f (domain x') UNIV /\
     strong_locals_rel f (domain x) x y /\
     (match b with
        NONE -> b' = NONE
      | SOME (w,h,l1,l2) ->
          (match b' with
             NONE -> F
           | SOME (a,b,c,d) -> c = l1 /\ d = l2))
     ==> ?perm.
           (let (l,permute) = env_to_list y (wl_state_permute cst) in
            let (l',permute') = env_to_list x perm in
              permute' = tperm /\
              MAP (\xy. match xy with (x,y) -> (f x,y)) l' = l /\
              (!x y. MEM x (MAP FST l') /\ MEM y (MAP FST l') /\ f x = f y
                     ==> x = y)) /\
           s_val_eq
             (wl_state_stack (wl_push_env (x',x) b (wl_state_permute_fupd (K perm) st)))
             (wl_state_stack (wl_push_env (y',y) b' cst))`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; option_CASE; pair_CASE;
              option_DISTINCT] THEN
  REPEAT GEN_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  (MP_TAC(ISPECL [`y:((A)word_loc)spt`; `x:((A)word_loc)spt`; `f:num->num`;
                 `wl_state_permute (cst:(A,C,FFI)wl_state)`; `tperm:num->num->num`]
         env_to_list_perm) THEN
  ASM_REWRITE_TAC[] THEN
  SUBST1_TAC(ISPEC `env_to_list (y:((A)word_loc)spt)
                      (wl_state_permute (cst:(A,C,FFI)wl_state))` (GSYM PAIR)) THEN
  REWRITE_TAC[pair_CASE] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num->num->num` MP_TAC) THEN
  SUBST1_TAC(ISPEC `env_to_list (x:((A)word_loc)spt) p` (GSYM PAIR)) THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  EXISTS_TAC `p:num->num->num` THEN
  SUBST1_TAC(ISPEC `env_to_list (x:((A)word_loc)spt) p` (GSYM PAIR)) THEN
  REWRITE_TAC[pair_CASE] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`x:((A)word_loc)spt`; `p:num->num->num`] env_to_list_keys) THEN
    SUBST1_TAC(ISPEC `env_to_list (x:((A)word_loc)spt) p` (GSYM PAIR)) THEN
    REWRITE_TAC[pair_CASE; EXTENSION; IN_SET_OF_LIST] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INJ; IN_UNIV]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[wl_push_env_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN SIMP[] THEN
  SUBST1_TAC(ISPEC `env_to_list (x:((A)word_loc)spt) p` (GSYM PAIR)) THEN
  SUBST1_TAC(ISPEC `env_to_list (y:((A)word_loc)spt)
                      (wl_state_permute (cst:(A,C,FFI)wl_state))` (GSYM PAIR)) THEN
  REWRITE_TAC[pair_CASE] THEN SIMP[s_val_eq_def; s_val_eq_refl; s_frame_val_eq_def2] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl) o
    check (can (find_term ((=) `wl_state_permute (cst:(A,C,FFI)wl_state)`)) o concl)) THEN
  REWRITE_TAC[MAP_MAP_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; pair_CASE]));;

(* HOL4 line 565 *)
let gc_frame = prove
 (`!(st:(A,C,FFI)wl_state) st'.
     wl_gc st = SOME st'
     ==> wl_state_fp_regs st' = wl_state_fp_regs st /\
         wl_state_mdomain st' = wl_state_mdomain st /\
         wl_state_sh_mdomain st' = wl_state_sh_mdomain st /\
         wl_state_gc_fun st' = wl_state_gc_fun st /\
         wl_state_handler st' = wl_state_handler st /\
         wl_state_clock st' = wl_state_clock st /\
         wl_state_code st' = wl_state_code st /\
         wl_state_locals st' = wl_state_locals st /\
         wl_state_locals_size st' = wl_state_locals_size st /\
         wl_state_stack_size st' = wl_state_stack_size st /\
         wl_state_stack_max st' = wl_state_stack_max st /\
         wl_state_stack_limit st' = wl_state_stack_limit st /\
         wl_state_be st' = wl_state_be st /\
         wl_state_ffi st' = wl_state_ffi st /\
         wl_state_compile st' = wl_state_compile st /\
         wl_state_compile_oracle st' = wl_state_compile_oracle st /\
         wl_state_code_buffer st' = wl_state_code_buffer st /\
         wl_state_data_buffer st' = wl_state_data_buffer st /\
         wl_state_permute st' = wl_state_permute st /\
         wl_state_termdep st' = wl_state_termdep st`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_gc_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[option_case_eq; pair_case_eq; option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN SIMP[]);;

(* helpers: s_frame_val_eq against a StackFrame, and rebuilding a list from *)
(* its keys and values                                                      *)

let WALLOCPAUX_s_frame_val_eq_StackFrame = prove
 (`!n ls1 ls h f.
     s_frame_val_eq (StackFrame n ls1 ls h:(A)stack_frame) f <=>
     ?ls1' ls'. f = StackFrame n ls1' ls' h /\ MAP SND ls = MAP SND ls'`,
  REPEAT GEN_TAC THEN CASES_ON `f:(A)stack_frame` THEN
  REWRITE_TAC[s_frame_val_eq_def2; injectivity "stack_frame"] THEN MESON_TAC[]);;

let WALLOCPAUX_ZIP_MAP_FST_SND = prove
 (`!(x:(A#B)list) (l:(A#C)list) (l':(D#B)list).
     MAP FST x = MAP FST l /\ MAP SND x = MAP SND l'
     ==> ZIP (MAP FST l) (MAP SND l') = x`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ZIP_MAP_FST_SND_EQ]);;

(* HOL4 line 596 *)
let s_key_eq_val_eq_pop_env = prove
 (CASE_TERM
  `!(s:(A,C,FFI)wl_state) s' n lsz ls opt keys vals.
     wl_pop_env s = SOME s' /\
     s_key_eq (wl_state_stack s) (CONS (StackFrame n lsz ls opt) keys) /\
     s_val_eq (wl_state_stack s) vals
     ==> ?lsz' ls' rest.
           vals = CONS (StackFrame n lsz' ls' opt) rest /\
           wl_state_locals s' =
             union (fromAList (ZIP (MAP FST ls) (MAP SND ls'))) (fromAList lsz) /\
           s_key_eq (wl_state_stack s') keys /\
           s_val_eq (wl_state_stack s') rest /\
           (match opt with
              NONE -> wl_state_handler s' = wl_state_handler s
            | SOME (h,l1,l2) -> wl_state_handler s' = h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_pop_env_def]) THEN GVS(all_case_eqs()) THEN
  CASES_ON `vals:((A)stack_frame)list` THEN
  GVS[s_val_eq_def; s_key_eq_def; s_frame_key_eq_def2;
      WALLOCPAUX_s_frame_val_eq_StackFrame] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC WALLOCPAUX_ZIP_MAP_FST_SND THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 619 *)
let ALOOKUP_key_remap_2 = prove
 (`!(ls:A list) (vals:B list) (f:A->C) n v.
     (!x y. MEM x ls /\ MEM y ls /\ f x = f y ==> x = y) /\
     LENGTH ls = LENGTH vals /\
     ALOOKUP (ZIP ls vals) n = SOME v
     ==> ALOOKUP (ZIP (MAP f ls) vals) (f n) = SOME v`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ZIP_def; ALOOKUP_THM; option_DISTINCT] THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; ZIP_def; MAP; ALOOKUP_THM; MEM] THEN
  MAP_EVERY X_GEN_TAC [`f:A->C`; `n:A`; `v:B`] THEN
  ASM_CASES_TAC `h:A = n` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `MEM (n:A) t` ASSUME_TAC THENL
   [UNDISCH_TAC `ALOOKUP (ZIP (t:A list) (t':B list)) n = SOME v` THEN
    DISCH_THEN(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    ASM_SIMP_TAC[MEM_ZIP; PAIR_EQ] THEN ASM_MESON_TAC[MEM_EL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((f:A->C) h = f n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 639 *)
let ALOOKUP_key_remap_INJ = prove
 (`!(f:A->B) n ls (vals:C list).
     INJ f (n INSERT set_of_list ls) UNIV /\
     LENGTH ls = LENGTH vals
     ==> ALOOKUP (ZIP ls vals) n = ALOOKUP (ZIP (MAP f ls) vals) (f n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x y. MEM x ls /\ MEM y ls /\ (f:A->B) x = f y ==> x = y`
    ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[INJ; IN_INSERT; IN_SET_OF_LIST; IN_UNIV]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  CASES_ON `ALOOKUP (ZIP (ls:A list) (vals:C list)) n` THENL
   [CONV_TAC SYM_CONV THEN
    UNDISCH_TAC `ALOOKUP (ZIP (ls:A list) (vals:C list)) n = NONE` THEN
    ASM_SIMP_TAC[ALOOKUP_ZIP_FAIL; LENGTH_MAP] THEN
    REWRITE_TAC[MEM_MAP] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INJ; IN_INSERT; IN_SET_OF_LIST; IN_UNIV]) THEN
    ASM_MESON_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC ALOOKUP_key_remap_2 THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 657: val lookup_alist_insert (ML, a type instance of the       *)
(* sptree theorem) *)

(* HOL4 line 659 *)
let strong_locals_rel_subset = prove
 (`!s s' f (stl:A spt) cstl.
     s SUBSET s' /\ strong_locals_rel f s' stl cstl
     ==> strong_locals_rel f s stl cstl`,
  REWRITE_TAC[strong_locals_rel_def; SUBSET] THEN MESON_TAC[]);;

(* HOL4 line 682 *)
let list_rearrange_keys = prove
 (`!perm (ls:(A#B)list) e.
     list_rearrange perm ls = e ==> set_of_list (MAP FST e) = set_of_list (MAP FST ls)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_MAP; mem_list_rearrange]);;

(* HOL4 line 690 *)
let list_rearrange_keys_2 = prove
 (`!perm (ls:(A#B)list).
     set_of_list (MAP FST (list_rearrange perm ls)) = set_of_list (MAP FST ls)`,
  MESON_TAC[list_rearrange_keys]);;

(* HOL4 line 696 *)
let MAP_FST_list_rearrange_keys_SORT = prove
 (`!perm (x:((A)word_loc)spt).
     set_of_list (MAP FST (list_rearrange perm (sort key_val_compare (toAList x)))) =
     domain x`,
  REWRITE_TAC[list_rearrange_keys_2] THEN
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_MAP; sort_MEM;
              EXISTS_PAIR_THM; MEM_toAList; FST; domain_lookup] THEN
  MESON_TAC[]);;

(* HOL4 line 704 *)
let MAP_FST_keys_SORT = prove
 (`!f (x:A spt). set_of_list (MAP FST (sort f (toAList x))) = domain x`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_MAP; sort_MEM;
              EXISTS_PAIR_THM; MEM_toAList; FST; domain_lookup] THEN
  MESON_TAC[]);;

(* HOL4 line 710 *)
let pop_env_frame = prove
 (`!(r':(A,C,FFI)wl_state) st' y' y''.
     s_val_eq (wl_state_stack r') st' /\
     s_key_eq (wl_state_stack y') (wl_state_stack y'') /\
     wl_pop_env (wl_state_stack_fupd (K st') r') = SOME y'' /\
     wl_pop_env r' = SOME y'
     ==> word_state_eq_rel y' y''`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_pop_env_def; list_case_eq; case_eq "stack_frame"; option_case_eq;
              pair_case_eq; option_DISTINCT; option_INJ; NOT_CONS_NIL] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FS[s_val_eq_def; s_key_eq_def; s_frame_val_eq_def2; s_frame_key_eq_def2;
     word_state_eq_rel_def] THEN
  UNDISCH_TAC `s_val_eq (wl_state_stack (r':(A,C,FFI)wl_state)) st'` THEN
  ASM_REWRITE_TAC[s_val_eq_def; s_frame_val_eq_def2; option_DISTINCT; option_INJ;
                  PAIR_EQ] THEN
  ASM_MESON_TAC[s_val_and_key_eq]);;

(* HOL4 line 724 *)
let key_map_implies = prove
 (CASE_TERM
  `!(f:A->B) (l':(A#C)list) l.
     MAP (\xy. match xy with (x,y) -> (f x,y)) l' = l
     ==> MAP f (MAP FST l') = MAP FST l`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MAP_MAP_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; pair_CASE; FST]);;

(* helper: memory loads agree on word_state_eq_rel states *)

let WALLOCPAUX_mem_load_eq = prove
 (`!w (s:(A,C,FFI)wl_state) cst.
     word_state_eq_rel s cst ==> wl_mem_load w cst = wl_mem_load w s`,
  SIMP_TAC[word_state_eq_rel_def; wl_mem_load_def]);;

(* HOL4 line 744 *)
let apply_colour_exp_lemma = prove
 (`!(st:(A,C,FFI)wl_state) w cst f res.
     wl_word_exp st w = SOME res /\
     word_state_eq_rel st cst /\
     strong_locals_rel f (domain (get_live_exp w))
       (wl_state_locals st) (wl_state_locals cst)
     ==> wl_word_exp cst (apply_colour_exp f w) = SOME res`,
  MATCH_MP_TAC wl_word_exp_ind THEN
  REWRITE_TAC[wl_word_exp_def; apply_colour_exp_def; get_live_exp_def] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    REWRITE_TAC[wl_get_var_def; strong_locals_rel_def; domain_insert; domain_def;
                IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    REWRITE_TAC[wl_get_store_def; word_state_eq_rel_def] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[option_case_eq; case_eq "word_loc"; option_DISTINCT] THEN
    STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[WALLOCPAUX_mem_load_eq];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[option_case_eq; option_DISTINCT] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `MAP (wl_word_exp (cst:(A,C,FFI)wl_state)) (MAP (apply_colour_exp f) wexps) =
      MAP (wl_word_exp (s:(A,C,FFI)wl_state)) (wexps:((A)wl_exp)list)`
      SUBST1_TAC THENL
     [REWRITE_TAC[MAP_MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
      REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN
      X_GEN_TAC `e:(A)wl_exp` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP the_words_EVERY_IS_SOME) THEN
      REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN
      DISCH_THEN(MP_TAC o SPEC `wl_word_exp (s:(A,C,FFI)wl_state) e`) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IS_SOME_EXISTS] THEN
      DISCH_THEN(X_CHOOSE_TAC `r:(A)word_loc`) THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:(A)wl_exp`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC strong_locals_rel_subset THEN
      EXISTS_TAC `domain (big_union (MAP get_live_exp (wexps:((A)wl_exp)list)))` THEN
      ASM_MESON_TAC[domain_big_union_subset];
      ASM_MESON_TAC[]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[option_case_eq; case_eq "word_loc"; option_DISTINCT] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[domain_union; strong_locals_rel_UNION]) THEN
    ASM_MESON_TAC[]]);;

(* HOL4 line 785 *)
let strong_locals_rel_insert = prove
 (`!f n l (st:A spt) cst v.
     INJ f (n INSERT l) UNIV /\
     strong_locals_rel f (l DELETE n) st cst
     ==> strong_locals_rel f l (insert n v st) (insert (f n) v cst)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[strong_locals_rel_def; lookup_insert; INJ; IN_INSERT; IN_DELETE;
              IN_UNIV] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`m:num`; `w:A`] THEN
  ASM_CASES_TAC `m:num = n` THEN ASM_REWRITE_TAC[option_INJ] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 lines 798-811: val exists_tac, exists_tac_2, setup_tac (ML) *)

(* HOL4 line 815 *)
let LASTN_LENGTH2 = prove
 (`!(x:A) xs. LASTN (LENGTH xs + 1) (CONS x xs) = CONS x xs`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `LENGTH (xs:A list) + 1 = LENGTH (CONS (x:A) xs)` SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH] THEN ARITH_TAC; REWRITE_TAC[LASTN_LENGTH_ID]]);;

(* HOL4 line 822 *)
let toAList_not_empty = prove
 (`!(t:A spt). ~(domain t = {}) ==> ~(toAList t = [])`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
  DISCH_TAC THEN REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; GSYM toAList_domain] THEN
  ASM_REWRITE_TAC[MAP; MEM]);;

(* HOL4 line 830 *)
let PAIR_CASE_PAIR_MAP = prove
 (CASE_TERM
  `!(f:A->C) (g:B->D) e (h:C->D->E).
     pair_CASE ((f ## g) e) h = (match e with (x,y) -> h (f x) (g y))`,
  REPEAT GEN_TAC THEN SUBST1_TAC(ISPEC `e:A#B` (GSYM PAIR)) THEN
  REWRITE_TAC[PAIR_MAP_THM; pair_CASE]);;

(* helper: updating permute with its own value *)

let WALLOCPAUX_permute_same = prove
 (`!st:(A,C,FFI)wl_state. wl_state_permute_fupd (K (wl_state_permute st)) st = st`,
  GEN_TAC THEN REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;

(* HOL4 line 836 *)
let permute_swap_lemma4 = prove
 (`!(prog:(A)wl_prog) (st:(A,C,FFI)wl_state) P.
     (!st'. wl_evaluate (prog,st) = (SOME wl_Error,st') ==> P (SOME wl_Error,st')) /\
     (?perm. P ((I ## (\s. wl_state_permute_fupd (K perm) s)) (wl_evaluate (prog,st))))
     ==> (?perm. P (wl_evaluate (prog,wl_state_permute_fupd (K perm) st)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`; `st:(A,C,FFI)wl_state`; `perm:num->num->num`]
    permute_swap_lemma) THEN
  SUBGOAL_THEN `?res rst. wl_evaluate (prog:(A)wl_prog,st:(A,C,FFI)wl_state) = (res,rst)`
    (CHOOSE_THEN (CHOOSE_THEN (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th))) THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  REWRITE_TAC[pair_CASE] THEN RULE_ASSUM_TAC(REWRITE_RULE[PAIR_MAP_THM; I_THM]) THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `res:((A)wl_result)option = SOME wl_Error` THENL
   [EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN
    ASM_REWRITE_TAC[WALLOCPAUX_permute_same] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* HOL4 line 853 *)
let MEM_ZIP_weak = prove
 (`!(l1:A list) (l2:B list) x1 x2.
     LENGTH l1 = LENGTH l2 /\ MEM (x1,x2) (ZIP l1 l2) ==> MEM x1 l1 /\ MEM x2 l2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; ZIP; MEM; NOT_SUC; SUC_INJ; HD; TL; PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 865 *)
let strong_locals_rel_set_vars_dom = prove
 (`!ns (ls:((A)word_loc)list) f X (s:(A,C,FFI)wl_state) (t:(A,C,FFI)wl_state) d.
     LENGTH ns = LENGTH ls /\
     INJ f X UNIV /\
     domain (wl_state_locals s) SUBSET X /\
     set_of_list ns SUBSET X /\
     strong_locals_rel f d (wl_state_locals s) (wl_state_locals t)
     ==> strong_locals_rel f d (wl_state_locals (wl_set_vars ns ls s))
                               (wl_state_locals (wl_set_vars (MAP f ns) ls t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[strong_locals_rel_def; wl_set_vars_def] THEN SIMP[] THEN
  ASM_SIMP_TAC[lookup_alist_insert; LENGTH_MAP] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `v:(A)word_loc`] THEN
  CASES_ON `ALOOKUP (ZIP (ns:num list) (ls:((A)word_loc)list)) n` THEN
  REWRITE_TAC[option_CASE] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `ALOOKUP (ZIP (MAP (f:num->num) ns) (ls:((A)word_loc)list)) (f n) = NONE`
      SUBST1_TAC THENL
     [UNDISCH_TAC `ALOOKUP (ZIP (ns:num list) (ls:((A)word_loc)list)) n = NONE` THEN
      ASM_SIMP_TAC[ALOOKUP_ZIP_FAIL; LENGTH_MAP; MEM_MAP] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INJ; SUBSET; IN_SET_OF_LIST; IN_UNIV]) THEN
      ASM_MESON_TAC[domain_lookup];
      REWRITE_TAC[option_CASE] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[strong_locals_rel_def]) THEN ASM_MESON_TAC[]];
    SUBGOAL_THEN `ALOOKUP (ZIP (MAP (f:num->num) ns) (ls:((A)word_loc)list)) (f n) = SOME v`
      SUBST1_TAC THENL
     [MATCH_MP_TAC ALOOKUP_key_remap_2 THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INJ; SUBSET; IN_SET_OF_LIST; IN_UNIV; option_INJ]) THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[option_CASE]]]);;

(* HOL4 line 892 *)
let s_key_eq_push_env_imp_MAP_FST = prove
 (`!x' x'' o0 (s:(A,C,FFI)wl_state) n' bb l opt ls ll res.
     s_key_eq (wl_state_stack (wl_push_env (x',x'') o0 s))
              (CONS (StackFrame n' bb l opt) ls) /\
     env_to_list x'' (wl_state_permute s) = (ll,res)
     ==> MAP FST ll = MAP FST l /\ set_of_list (MAP FST bb) = domain x'`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`o0:(num#(A)wl_prog#num#num)option`,`o0:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[wl_push_env_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[pair_CASE] THEN
  SIMP[s_key_eq_def; s_frame_key_eq_def2] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o
    check (fun th -> rhs(concl th) = `bb:(num#(A)word_loc)list`)) THEN
  REWRITE_TAC[set_MAP_FST_toAList_domain]);;

(* HOL4 line 906 *)
let strong_locals_rel_set_var_dom = prove
 (`!f X (s:(A,C,FFI)wl_state) (t:(A,C,FFI)wl_state) n d l.
     INJ f X UNIV /\
     domain (wl_state_locals s) SUBSET X /\
     n IN X /\
     strong_locals_rel f d (wl_state_locals s) (wl_state_locals t)
     ==> strong_locals_rel f d (wl_state_locals (wl_set_var n l s))
                               (wl_state_locals (wl_set_var (f n) l t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[strong_locals_rel_def; wl_set_var_def] THEN SIMP[lookup_insert] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `v:(A)word_loc`] THEN
  ASM_CASES_TAC `m:num = n` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  TRY COND_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INJ; SUBSET; IN_UNIV; strong_locals_rel_def;
                              domain_lookup]) THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 922 *)
let strong_locals_rel_extend_aux = prove
 (`!(src:A spt) s f tgt t.
     domain src SUBSET s /\ strong_locals_rel f s src tgt
     ==> strong_locals_rel f t src tgt`,
  REWRITE_TAC[strong_locals_rel_def; SUBSET; domain_lookup] THEN MESON_TAC[]);;

(* helper: the statement of evaluate_apply_colour for one starting state   *)
(* and program, as a predicate, so that each case of the induction on the  *)
(* size of the program is a lemma                                          *)

(* HOL4 line 2698 *)
let get_reads_exp_get_live_exp = prove
 (`!exp:(A)wl_exp. set_of_list (get_reads_exp exp) = domain (get_live_exp exp)`,
  MATCH_MP_TAC get_reads_exp_ind THEN
  REWRITE_TAC[get_reads_exp_def; get_live_exp_def; set_of_list; domain_insert;
              domain_union; domain_def; SET_OF_LIST_APPEND] THEN
  REPEAT CONJ_TAC THEN TRY(SIMP_TAC[] THEN NO_TAC) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; FLAT; big_union_def; ITLIST; set_of_list; domain_def; MEM;
              SET_OF_LIST_APPEND; domain_union] THEN
  REWRITE_TAC[GSYM big_union_def] THEN ASM_MESON_TAC[]);;

let WALLOCPAUX_INJ_SUB_TAC : tactic =
  let hd_name tm = try fst(dest_const(fst(strip_comb tm))) with Failure _ -> "" in
  FIRST_ASSUM(fun th ->
    if hd_name (concl th) = "INJ" then
      MATCH_MP_TAC word_allocProof_INJ_less THEN
      EXISTS_TAC (el 1 (snd(strip_comb(concl th)))) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; domain_union; domain_insert; domain_delete; IN_UNION; IN_INSERT;
                  IN_DELETE; word_allocProof_domain_numset_list_insert;
                  reg_allocProof_domain_numset_list_delete; IN_DIFF; IN_SET_OF_LIST; MEM;
                  domain_def; NOT_IN_EMPTY; list_insert_def;
                  GSYM get_reads_exp_get_live_exp; set_MAP_FST_toAList_domain;
                  domain_difference] THEN
      MESON_TAC[]
    else NO_TAC);;

let WALLOCPAUX_sh_mem_set_var_cases = prove
 (CASE_TERM
  `!x v (s:(A,C,FFI)wl_state).
     (sh_mem_set_var x v s:((A)wl_result)option#(A,C,FFI)wl_state) =
     (match x with
        NONE -> (SOME wl_Error,s)
      | SOME r ->
          (match r with
             FFI_final outcome -> (SOME (wl_FinalFFI outcome),wl_flush_state T s)
           | FFI_return new_ffi new_bytes ->
               (NONE,wl_set_var v (wl_Word (word_of_bytes F (word 0) new_bytes))
                       (wl_state_ffi_fupd (K new_ffi) s))))`,
  REWRITE_TAC[FORALL_OPTION_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[sh_mem_set_var_def; option_CASE];
    GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `a:(FFI)ffi_result` (cases "ffi_result")) THEN
    SIMP[sh_mem_set_var_def]]);;

let WALLOCPAUX_seq_NONE = prove
 (`!(c1:(A)wl_prog) c2 (s:(A,C,FFI)wl_state) s1.
     wl_evaluate (c1,s) = (NONE,s1) ==> wl_evaluate (wl_Seq c1 c2,s) = wl_evaluate (c2,s1)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [wl_evaluate_def] THEN
  ASM_REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF]);;

let WALLOCPAUX_seq_SOME = prove
 (`!(c1:(A)wl_prog) c2 (s:(A,C,FFI)wl_state) r s1.
     wl_evaluate (c1,s) = (SOME r,s1) ==> wl_evaluate (wl_Seq c1 c2,s) = (SOME r,s1)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [wl_evaluate_def] THEN
  ASM_REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF; option_DISTINCT]);;

(* helpers for evaluate_apply_colour: word_state_eq_rel ignores the locals  *)
(* and the permutation and is kept by dec_clock and flush_state             *)

let WALLOCPAUX_wser_locals = prove
 (`!(s:(A,C,FFI)wl_state) t a b.
     word_state_eq_rel s t
     ==> word_state_eq_rel (wl_state_locals_fupd (K a) s) (wl_state_locals_fupd (K b) t)`,
  REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let WALLOCPAUX_wser_permute = prove
 (`!(s:(A,C,FFI)wl_state) t p.
     word_state_eq_rel s t ==> word_state_eq_rel (wl_state_permute_fupd (K p) s) t`,
  REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let WALLOCPAUX_wser_dec_clock = prove
 (`!(s:(A,C,FFI)wl_state) t.
     word_state_eq_rel s t ==> word_state_eq_rel (wl_dec_clock s) (wl_dec_clock t)`,
  REWRITE_TAC[word_state_eq_rel_def; wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let WALLOCPAUX_wser_flush = prove
 (`!b (s:(A,C,FFI)wl_state) t.
     word_state_eq_rel s t ==> word_state_eq_rel (wl_flush_state b s) (wl_flush_state b t)`,
  REWRITE_TAC[FORALL_BOOL_THM; word_state_eq_rel_def; wl_flush_state_def;
              wl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let WALLOCPAUX_apply_nummap_key_LN = prove
 (`!f. apply_nummap_key f (LN:A spt) = LN`,
  REWRITE_TAC[apply_nummap_key_def; toAList_def; foldi_def; MAP; fromAList_def]);;

(* name the result of the run wl_evaluate (p,_) found in the goal *)

let WALLOCPAUX_NAME_EVAL_TAC (p:term) (vs:term list) : tactic =
  fun (asl,w as g) ->
    let tm = find_term (fun t ->
        try fst(dest_const(rator t)) = "wl_evaluate" && fst(dest_pair(rand t)) = p
        with Failure _ -> false) w in
    (WALLOCPAUX_TUPLE_TAC tm vs THEN REWRITE_TAC[pair_CASE]) g;;

(* size facts of the datatypes (for the induction on the program size) *)

let WALLOCPAUX_SIZE_TAC : tactic =
  fun g -> (REWRITE_TAC (!the_size_defs @ flat (map snd (!the_size_aux_eqs))) THEN
            ARITH_TAC) g;;

let WALLOCPAUX_eac_Q_def = new_definition (CASE_TERM
 `WALLOCPAUX_eac_Q (st:(A,C,FFI)wl_state) (prog:(A)wl_prog) <=>
   !cst f live lt.
     colouring_ok f prog live lt /\
     word_state_eq_rel st cst /\
     strong_locals_rel f (domain (get_live prog live lt))
       (wl_state_locals st) (wl_state_locals cst)
     ==> ?perm'.
           let (res,rst) = wl_evaluate (prog,wl_state_permute_fupd (K perm') st) in
           if res = SOME wl_Error then T else
           let (res',rcst) = wl_evaluate (apply_colour f prog,cst) in
             res = res' /\
             word_state_eq_rel rst rcst /\
             (match res with
                NONE ->
                  strong_locals_rel f (domain live)
                    (wl_state_locals rst) (wl_state_locals rcst)
              | SOME (wordSem_Break n) ->
                  (match oEL n lt with
                     SOME (_,exit_names) ->
                       strong_locals_rel f (domain exit_names)
                         (wl_state_locals rst) (wl_state_locals rcst)
                   | NONE -> T)
              | SOME (wordSem_Continue n) ->
                  (match oEL n lt with
                     SOME (names,_) ->
                       strong_locals_rel f (domain names)
                         (wl_state_locals rst) (wl_state_locals rcst)
                   | NONE -> T)
              | SOME _ -> wl_state_locals rst = wl_state_locals rcst)`);;

let WALLOCPAUX_with_same_permute = prove
 (`!st:(A,C,FFI)wl_state. wl_state_permute_fupd (K (wl_state_permute st)) st = st`,
  GEN_TAC THEN REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;

(* opening of a case of evaluate_apply_colour that needs no induction      *)
(* hypothesis and no permutation: the source run is evaluated as is        *)

let WALLOCPAUX_EAC_OPEN_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_eac_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN
  REWRITE_TAC[WALLOCPAUX_with_same_permute];;

(* the same, running the source with the permutation of the target, so that *)
(* push_env makes the same choices on both sides                            *)

let WALLOCPAUX_EAC_OPENC_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_eac_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `wl_state_permute (cst:(A,C,FFI)wl_state)` THEN
  REWRITE_TAC[apply_colour_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV);;

(* strong_locals_rel f S x y from an assumption strong_locals_rel f S' x y  *)
(* with S a subset of S'                                                    *)

let WALLOCPAUX_SLR_SUB_TAC : tactic =
  let hd_name tm = try fst(dest_const(fst(strip_comb tm))) with Failure _ -> "" in
  fun (asl,w as g) ->
    let args = snd(strip_comb w) in
    FIRST_ASSUM(fun th ->
      let c = concl th in
      let a = snd(strip_comb c) in
      if hd_name c = "strong_locals_rel" && el 0 a = el 0 args && el 2 a = el 2 args &&
         el 3 a = el 3 args then
        MATCH_MP_TAC strong_locals_rel_subset THEN EXISTS_TAC (el 1 a) THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; domain_union; domain_insert; domain_delete; IN_UNION; IN_INSERT;
                    IN_DELETE; word_allocProof_domain_numset_list_insert;
                    reg_allocProof_domain_numset_list_delete; IN_DIFF; IN_SET_OF_LIST; MEM;
                    domain_def; NOT_IN_EMPTY; list_insert_def; domain_FOLDR_delete;
                    GSYM get_reads_exp_get_live_exp; set_MAP_FST_toAList_domain;
                    domain_difference] THEN
        MESON_TAC[]
      else NO_TAC) g;;

(* expand the colouring and liveness assumptions of a case *)

let WALLOCPAUX_EAC_EXPAND_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[get_live_def; colouring_ok_def; get_writes_def; LET_DEF;
                              LET_END_DEF; word_state_eq_rel_def]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;

(* from strong_locals_rel f S (wl_state_locals st) (wl_state_locals cst),   *)
(* derive wl_get_var (f r) cst = SOME v for every assumption                 *)
(* wl_get_var r st = SOME v with r (visibly) in S                            *)

let WALLOCPAUX_EAC_GETVAR_TAC : tactic =
  fun (asl,w as g) ->
    let hd_name tm = try fst(dest_const(fst(strip_comb tm))) with Failure _ -> "" in
    let slrs = filter (fun (_,th) -> hd_name (concl th) = "strong_locals_rel") asl in
    let gvs = filter (fun (_,th) -> let c = concl th in
                        is_eq c && hd_name (lhs c) = "wl_get_var" &&
                        hd_name (rhs c) = "SOME") asl in
    let tac_for (_,slr) =
      let a = snd(strip_comb(concl slr)) in
      let f = el 0 a and sl = el 1 a and locs = el 2 a and clocs = el 3 a in
      let st = rand locs and cst = rand clocs in
      MAP_EVERY (fun (_,gv) ->
          let l = lhs(concl gv) in
          let r = el 0 (snd(strip_comb l)) and s0 = el 1 (snd(strip_comb l)) in
          if s0 <> st then ALL_TAC else
          let goal = mk_eq(mk_comb(mk_comb(rator(rator l), mk_comb(f,r)), cst), rhs(concl gv)) in
          if exists (fun (_,a) -> concl a = goal) asl then ALL_TAC else
          TRY (SUBGOAL_THEN goal ASSUME_TAC THENL
                [MATCH_MP_TAC strong_locals_rel_get_var THEN
                 MAP_EVERY EXISTS_TAC [sl; st] THEN
                 ASM_REWRITE_TAC[domain_union; domain_insert; domain_delete; IN_UNION; IN_INSERT;
                                 IN_DELETE; word_allocProof_domain_numset_list_insert;
                                 IN_SET_OF_LIST; MEM; list_insert_def] THEN NO_TAC;
                 ALL_TAC])) gvs in
    EVERY (map tac_for slrs) g;;

(* the same for wl_get_vars ls st = SOME vs: wl_get_vars (MAP f ls) cst     *)

let WALLOCPAUX_EAC_GETVARS_TAC : tactic =
  fun (asl,w as g) ->
    let hd_name tm = try fst(dest_const(fst(strip_comb tm))) with Failure _ -> "" in
    let slrs = filter (fun (_,th) -> hd_name (concl th) = "strong_locals_rel") asl in
    let gvs = filter (fun (_,th) -> let c = concl th in
                        is_eq c && hd_name (lhs c) = "wl_get_vars" &&
                        hd_name (rhs c) = "SOME") asl in
    let tac_for (_,slr) =
      let a = snd(strip_comb(concl slr)) in
      let f = el 0 a and sl = el 1 a and locs = el 2 a and clocs = el 3 a in
      let st = rand locs and cst = rand clocs in
      MAP_EVERY (fun (_,gv) ->
          let l = lhs(concl gv) in
          let ls = el 0 (snd(strip_comb l)) and s0 = el 1 (snd(strip_comb l)) in
          if s0 <> st then ALL_TAC else
          let mapf = mk_icomb(mk_icomb(`MAP:(num->num)->num list->num list`, f), ls) in
          let goal = mk_eq(mk_comb(mk_comb(rator(rator l), mapf), cst), rhs(concl gv)) in
          if exists (fun (_,a) -> concl a = goal) asl then ALL_TAC else
          TRY (SUBGOAL_THEN goal ASSUME_TAC THENL
                [MATCH_MP_TAC strong_locals_rel_get_vars THEN
                 MAP_EVERY EXISTS_TAC [sl; st] THEN
                 ASM_REWRITE_TAC[domain_union; domain_insert; domain_delete; IN_UNION;
                                 IN_INSERT; IN_DELETE; word_allocProof_domain_numset_list_insert;
                                 IN_SET_OF_LIST; MEM; list_insert_def] THEN MESON_TAC[];
                 ALL_TAC])) gvs in
    EVERY (map tac_for slrs) g;;

let WALLOCPAUX_slr_delete = prove
 (`!f n l (st:A spt) cst.
     INJ f (n INSERT l) UNIV /\ strong_locals_rel f (l DELETE n) st cst
     ==> strong_locals_rel f l (delete n st) (delete (f n) cst)`,
  REWRITE_TAC[strong_locals_rel_def; lookup_delete; INJ; IN_INSERT; IN_DELETE; IN_UNIV] THEN
  MESON_TAC[]);;

(* peel inserts and deletes on both sides of a strong_locals_rel goal *)

let WALLOCPAUX_SLR_CHAIN_TAC : tactic =
  REPEAT((MATCH_MP_TAC strong_locals_rel_insert ORELSE MATCH_MP_TAC WALLOCPAUX_slr_delete) THEN
         CONJ_TAC THENL [WALLOCPAUX_INJ_SUB_TAC; ALL_TAC]) THEN
  WALLOCPAUX_SLR_SUB_TAC;;

(* from wl_cut_env N (wl_state_locals st) = SOME x, get the renamed cut of  *)
(* the target locals, named y                                               *)

let WALLOCPAUX_EAC_CUTENV_TAC : tactic =
  let hd_name tm = try fst(dest_const(fst(strip_comb tm))) with Failure _ -> "" in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && hd_name (lhs c) = "wl_cut_env" &&
       hd_name (rand(lhs c)) = "wl_state_locals" && hd_name (rhs c) = "SOME" then
      let nm = rand(rator(lhs c)) and sl = rand(lhs c) and x = rand(rhs c) in
      let cl = mk_comb(rator sl, `cst:(A,C,FFI)wl_state`) in
      MP_TAC(ISPECL [`f:num->num`; nm; sl; x; cl] cut_env_lemma) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [WALLOCPAUX_INJ_SUB_TAC; ACCEPT_TAC th; WALLOCPAUX_SLR_SUB_TAC];
        DISCH_THEN(X_CHOOSE_THEN `y:((A)word_loc)spt` STRIP_ASSUME_TAC)]
    else NO_TAC);;

let WALLOCPAUX_EAC_FINISH_TAC : tactic =
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[word_state_eq_rel_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(SIMP[] THEN MATCH_MP_TAC strong_locals_rel_insert THEN CONJ_TAC THENL
       [WALLOCPAUX_INJ_SUB_TAC; WALLOCPAUX_SLR_SUB_TAC] THEN NO_TAC) THEN
  TRY(SIMP[] THEN WALLOCPAUX_SLR_SUB_TAC THEN NO_TAC);;

(* name the result of the source run res,rst; dispose of the error case;    *)
(* unfold the source run once                                               *)

let WALLOCPAUX_EAC_SRC_TAC : tactic =
  fun (asl,w as g) ->
    let tm = find_term (fun t ->
        try fst(dest_const(rator t)) = "wl_evaluate" &&
            (let _,s = dest_pair(rand t) in
             fst(dest_const(fst(strip_comb s))) = "wl_state_permute_fupd")
        with Failure _ -> false) w in
    (WALLOCPAUX_TUPLE_TAC tm [`res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`] THEN
     REWRITE_TAC[pair_CASE] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = tm)) THEN
     ONCE_REWRITE_TAC[wl_evaluate_def] THEN DISCH_TAC) g;;

let WALLOCPAUX_clock_induct = prove
 (`!P. (!st:(A,C,FFI)wl_state.
          (!st'. wl_state_clock st' < wl_state_clock st ==> P st') ==> P st)
       ==> !st. P st`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n (st:(A,C,FFI)wl_state). wl_state_clock st = n ==> P st`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN ASM_MESON_TAC[]);;

(* helpers for the Loop case: the relation of a body result that continues *)
(* the loop, and of one that leaves it                                      *)

let WALLOCPAUX_cont_loop_match = prove
 (CASE_TERM
  `!(r:((A)wl_result)option) (x:B spt) y (f:num->num) (names:num_set)
    (exit_names:num_set) (lt:(num_set#num_set)list).
     wl_cont_loop r /\
     (match r with
        NONE -> strong_locals_rel f (domain names) x y
      | SOME (wordSem_Break n) ->
          (match oEL n (CONS (names,exit_names) lt) with
             SOME (_,exit_names) -> strong_locals_rel f (domain exit_names) x y
           | NONE -> T)
      | SOME (wordSem_Continue n) ->
          (match oEL n (CONS (names,exit_names) lt) with
             SOME (names,_) -> strong_locals_rel f (domain names) x y
           | NONE -> T)
      | SOME _ -> x = y)
     ==> strong_locals_rel f (domain names) x y`,
  REWRITE_TAC[FORALL_OPTION_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[option_CASE] THEN MESON_TAC[]; ALL_TAC] THEN
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `a:(A)wl_result` (cases "wl_result")) THEN
  REWRITE_TAC[wl_cont_loop_def; option_CASE; WALLOCPAUX_wl_result_CASE] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> not (is_eq (concl th)))) THEN
  ASM_REWRITE_TAC[oEL_DEF; option_CASE; pair_CASE]);;

let WALLOCPAUX_exit_loop_match = prove
 (CASE_TERM
  `!(r:((A)wl_result)option) (x:B spt) y (f:num->num) (live:num_set) (names:num_set)
    (exit_names:num_set) (lt:(num_set#num_set)list).
     ~wl_cont_loop r /\ ~(r = SOME (wordSem_Break 0)) /\
     (match r with
        NONE -> strong_locals_rel f (domain names) x y
      | SOME (wordSem_Break n) ->
          (match oEL n (CONS (names,exit_names) lt) with
             SOME (_,exit_names) -> strong_locals_rel f (domain exit_names) x y
           | NONE -> T)
      | SOME (wordSem_Continue n) ->
          (match oEL n (CONS (names,exit_names) lt) with
             SOME (names,_) -> strong_locals_rel f (domain names) x y
           | NONE -> T)
      | SOME _ -> x = y)
     ==> (match wl_exit_loop r with
            NONE -> strong_locals_rel f (domain live) x y
          | SOME (wordSem_Break n) ->
              (match oEL n lt with
                 SOME (_,exit_names) -> strong_locals_rel f (domain exit_names) x y
               | NONE -> T)
          | SOME (wordSem_Continue n) ->
              (match oEL n lt with
                 SOME (names,_) -> strong_locals_rel f (domain names) x y
               | NONE -> T)
          | SOME _ -> x = y)`,
  REWRITE_TAC[FORALL_OPTION_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[wl_cont_loop_def]; ALL_TAC] THEN
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `a:(A)wl_result` (cases "wl_result")) THEN
  REWRITE_TAC([wl_cont_loop_def; wl_exit_loop_def; option_CASE; WALLOCPAUX_wl_result_CASE;
               option_INJ] @ WALLOCPAUX_wl_result_distinct @
              (case_info_of_tyname "wl_result").ci_inject) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> not (is_neg (concl th)))) THEN
  ASM_REWRITE_TAC[oEL_DEF]);;

(* unfold one iteration of the source and target loops, with the body runs *)
(* named by assumptions                                                     *)

let WALLOCPAUX_LOOP_UNFOLD_TAC : tactic =
  REWRITE_TAC[apply_colour_def] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[wl_cut_state_def; option_CASE; wl_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[wl_state_INFO.ri_fupdcanon] THEN
  ASM_REWRITE_TAC([pair_CASE; wl_cont_loop_def; wl_exit_loop_def; option_INJ; option_DISTINCT;
                   wl_STOP_def; wl_state_INFO.ri_accfupds; K_THM] @
                  WALLOCPAUX_wl_result_distinct);;

(* HOL4 line 931 *)
let evaluate_apply_colour_Loop_helper = prove
 (CASE_TERM
  `!(st:(A,C,FFI)wl_state) cst f names body exit_names live lt.
     colouring_ok f (wl_Loop names body exit_names) live lt /\
     word_state_eq_rel st cst /\
     strong_locals_rel f
       (domain (get_live (wl_Loop names body exit_names) live lt))
       (wl_state_locals st) (wl_state_locals cst) /\
     (!(st:(A,C,FFI)wl_state) cst f live lt.
        colouring_ok f body live lt /\
        word_state_eq_rel st cst /\
        strong_locals_rel f (domain (get_live body live lt))
          (wl_state_locals st) (wl_state_locals cst)
        ==> ?perm'.
              (let (res,rst) = wl_evaluate (body,wl_state_permute_fupd (K perm') st) in
                 res = SOME wl_Error \/
                 let (res',rcst) = wl_evaluate (apply_colour f body,cst) in
                   res = res' /\ word_state_eq_rel rst rcst /\
                   (match res with
                      NONE ->
                        strong_locals_rel f (domain live)
                          (wl_state_locals rst) (wl_state_locals rcst)
                    | SOME (wordSem_Break n) ->
                        (match oEL n lt with
                           SOME (_,exit_names) ->
                             strong_locals_rel f (domain exit_names)
                               (wl_state_locals rst) (wl_state_locals rcst)
                         | NONE -> T)
                    | SOME (wordSem_Continue n) ->
                        (match oEL n lt with
                           SOME (names,_) ->
                             strong_locals_rel f (domain names)
                               (wl_state_locals rst) (wl_state_locals rcst)
                         | NONE -> T)
                    | SOME _ -> wl_state_locals rst = wl_state_locals rcst)))
     ==> ?perm'.
           (let (res,rst) =
                wl_evaluate (wl_Loop names body exit_names,
                             wl_state_permute_fupd (K perm') st) in
              res = SOME wl_Error \/
              let (res',rcst) =
                  wl_evaluate (apply_colour f (wl_Loop names body exit_names),cst) in
                res = res' /\ word_state_eq_rel rst rcst /\
                (match res with
                   NONE ->
                     strong_locals_rel f (domain live)
                       (wl_state_locals rst) (wl_state_locals rcst)
                 | SOME (wordSem_Break n) ->
                     (match oEL n lt with
                        SOME (_,exit_names) ->
                          strong_locals_rel f (domain exit_names)
                            (wl_state_locals rst) (wl_state_locals rcst)
                      | NONE -> T)
                 | SOME (wordSem_Continue n) ->
                     (match oEL n lt with
                        SOME (names,_) ->
                          strong_locals_rel f (domain names)
                            (wl_state_locals rst) (wl_state_locals rcst)
                      | NONE -> T)
                 | SOME _ -> wl_state_locals rst = wl_state_locals rcst))`,
  MATCH_MP_TAC WALLOCPAUX_clock_induct THEN
  X_GEN_TAC `st:(A,C,FFI)wl_state` THEN DISCH_THEN(LABEL_TAC "cih") THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[colouring_ok_def; get_live_def] THEN
  STRIP_TAC THEN POP_ASSUM(LABEL_TAC "bih") THEN
  MP_TAC(ISPEC `wl_cut_env (names,LN) (wl_state_locals (st:(A,C,FFI)wl_state))`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `env:((A)word_loc)spt` ASSUME_TAC)) THENL
   [EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[WALLOCPAUX_with_same_permute] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC[wl_cut_state_def; option_CASE; pair_CASE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:num->num`; `(names:num_set,LN:num_set)`;
                 `wl_state_locals (st:(A,C,FFI)wl_state)`; `env:((A)word_loc)spt`;
                 `wl_state_locals (cst:(A,C,FFI)wl_state)`] cut_env_lemma) THEN
  ASM_REWRITE_TAC[domain_def; UNION_EMPTY; FST; SND; WALLOCPAUX_apply_nummaps_key_pair;
                  WALLOCPAUX_apply_nummap_key_LN] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
  USE_THEN "bih" (MP_TAC o SPECL [`wl_state_locals_fupd (K env) (st:(A,C,FFI)wl_state)`;
    `wl_state_locals_fupd (K y) (cst:(A,C,FFI)wl_state)`; `f:num->num`; `names:num_set`;
    `CONS (names:num_set,exit_names:num_set) lt`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[WALLOCPAUX_wser_locals] THEN
    REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
    MATCH_MP_TAC strong_locals_rel_extend_aux THEN EXISTS_TAC `domain (names:num_set)` THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm1:num->num->num` MP_TAC) THEN
  REWRITE_TAC[wl_state_INFO.ri_fupdcanon] THEN
  WALLOCPAUX_NAME_EVAL_TAC `body:(A)wl_prog`
    [`r1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] THEN
  WALLOCPAUX_NAME_EVAL_TAC `apply_colour f (body:(A)wl_prog)`
    [`r2:((A)wl_result)option`; `s2:(A,C,FFI)wl_state`] THEN
  ASM_CASES_TAC `r1 = SOME (wl_Error:(A)wl_result)` THENL
   [DISCH_TAC THEN EXISTS_TAC `perm1:num->num->num` THEN WALLOCPAUX_LOOP_UNFOLD_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `wl_state_clock (s2:(A,C,FFI)wl_state) = wl_state_clock (s1:(A,C,FFI)wl_state)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `word_state_eq_rel (s1:(A,C,FFI)wl_state) s2` THEN
    REWRITE_TAC[word_state_eq_rel_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `wl_cont_loop (r1:((A)wl_result)option)` THENL
   [SUBGOAL_THEN `strong_locals_rel f (domain (names:num_set))
                    (wl_state_locals (s1:(A,C,FFI)wl_state))
                    (wl_state_locals (s2:(A,C,FFI)wl_state))` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`r1:((A)wl_result)option`; `wl_state_locals (s1:(A,C,FFI)wl_state)`;
                     `wl_state_locals (s2:(A,C,FFI)wl_state)`; `f:num->num`;
                     `names:num_set`; `exit_names:num_set`; `lt:(num_set#num_set)list`]
                    WALLOCPAUX_cont_loop_match) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `wl_state_clock (s1:(A,C,FFI)wl_state) = 0` THENL
     [EXISTS_TAC `perm1:num->num->num` THEN WALLOCPAUX_LOOP_UNFOLD_TAC THEN
      REWRITE_TAC([option_CASE; WALLOCPAUX_wl_result_CASE; option_INJ] @
                  WALLOCPAUX_wl_result_distinct) THEN
      REPEAT CONJ_TAC THEN
      TRY (MATCH_MP_TAC WALLOCPAUX_wser_flush THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      REWRITE_TAC[wl_flush_state_def; wl_state_INFO.ri_accfupds; K_THM];
      ALL_TAC] THEN
    USE_THEN "cih" (MP_TAC o SPEC `wl_dec_clock (s1:(A,C,FFI)wl_state)`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP wl_evaluate_clock o check (fun th ->
        is_eq(concl th) &&
        rhs(concl th) = `(r1:((A)wl_result)option, s1:(A,C,FFI)wl_state)`)) THEN
      REWRITE_TAC[wl_state_INFO.ri_accfupds] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`wl_dec_clock (s2:(A,C,FFI)wl_state)`; `f:num->num`;
      `names:num_set`; `body:(A)wl_prog`; `exit_names:num_set`; `live:num_set`;
      `lt:(num_set#num_set)list`]) THEN
    REWRITE_TAC[colouring_ok_def; get_live_def] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[WALLOCPAUX_wser_dec_clock] THEN
      REWRITE_TAC[wl_dec_clock_def; wl_state_INFO.ri_accfupds] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `perm2:num->num->num` (LABEL_TAC "p2")) THEN
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) &&
         rhs(concl th) = `(r1:((A)wl_result)option, s1:(A,C,FFI)wl_state)` then
        MP_TAC(ISPECL [`body:(A)wl_prog`; snd(dest_pair(rand(lhs(concl th))));
                       `perm2:num->num->num`] permute_swap_lemma)
      else NO_TAC) THEN
    ASM_REWRITE_TAC[pair_CASE] THEN
    REWRITE_TAC[wl_state_INFO.ri_fupdcanon; wl_state_INFO.ri_fupdfupds; K_o_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `perm3:num->num->num`) THEN
    EXISTS_TAC `perm3:num->num->num` THEN WALLOCPAUX_LOOP_UNFOLD_TAC THEN
    REMOVE_THEN "p2" MP_TAC THEN
    REWRITE_TAC[apply_colour_def; wl_STOP_def; wl_dec_clock_def; wl_state_INFO.ri_accfupds;
                K_THM] THEN
    REWRITE_TAC[wl_state_INFO.ri_fupdcanon] THEN
    DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `r1 = SOME (wordSem_Break 0:(A)wl_result)` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `r1:((A)wl_result)option`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "option_CASE"
      with Failure _ -> false)) THEN
    REWRITE_TAC[option_CASE; WALLOCPAUX_wl_result_CASE; oEL_DEF; pair_CASE] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `wl_cut_env (exit_names,LN) (wl_state_locals (s1:(A,C,FFI)wl_state))`
      (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `env2:((A)word_loc)spt` ASSUME_TAC)) THENL
     [EXISTS_TAC `perm1:num->num->num` THEN WALLOCPAUX_LOOP_UNFOLD_TAC THEN
      ASM_REWRITE_TAC[wl_cut_state_def; option_CASE; pair_CASE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:num->num`; `(exit_names:num_set,LN:num_set)`;
                   `wl_state_locals (s1:(A,C,FFI)wl_state)`; `env2:((A)word_loc)spt`;
                   `wl_state_locals (s2:(A,C,FFI)wl_state)`] cut_env_lemma) THEN
    ASM_REWRITE_TAC[domain_def; UNION_EMPTY; FST; SND; WALLOCPAUX_apply_nummaps_key_pair;
                    WALLOCPAUX_apply_nummap_key_LN] THEN
    DISCH_THEN(X_CHOOSE_THEN `y2:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `perm1:num->num->num` THEN WALLOCPAUX_LOOP_UNFOLD_TAC THEN
    ASM_REWRITE_TAC[wl_cut_state_def; option_CASE; pair_CASE] THEN
    REWRITE_TAC[option_DISTINCT; wl_state_INFO.ri_accfupds; K_THM] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC WALLOCPAUX_wser_locals THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC strong_locals_rel_extend_aux THEN
      EXISTS_TAC `domain (exit_names:num_set)` THEN ASM_REWRITE_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  EXISTS_TAC `perm1:num->num->num` THEN WALLOCPAUX_LOOP_UNFOLD_TAC THEN
  MP_TAC(ISPECL [`r1:((A)wl_result)option`; `wl_state_locals (s1:(A,C,FFI)wl_state)`;
                 `wl_state_locals (s2:(A,C,FFI)wl_state)`; `f:num->num`; `live:num_set`;
                 `names:num_set`; `exit_names:num_set`; `lt:(num_set#num_set)list`]
                WALLOCPAUX_exit_loop_match) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* helpers for the If case *)

let WALLOCPAUX_get_var_permute = prove
 (`!n p (s:(A,C,FFI)wl_state). wl_get_var n (wl_state_permute_fupd p s) = wl_get_var n s`,
  REWRITE_TAC[wl_get_var_def; wl_state_INFO.ri_accfupds]);;

(* the source run fails: run it with its own permutation *)

let WALLOCPAUX_EAC_SRCERR_TAC : tactic =
  EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN
  REWRITE_TAC[WALLOCPAUX_with_same_permute] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_word_loc_CASE];;

(* a branch of an If: the induction hypothesis for the branch p *)

let WALLOCPAUX_EAC_IFBR_TAC (p:term) : tactic =
  REMOVE_THEN "ih" (MP_TAC o SPEC p) THEN
  ANTS_TAC THENL [WALLOCPAUX_SIZE_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `st:(A,C,FFI)wl_state`) THEN REWRITE_TAC[WALLOCPAUX_eac_Q_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`cst:(A,C,FFI)wl_state`; `f:num->num`; `live:num_set`;
                             `lt:(num_set#num_set)list`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[word_state_eq_rel_def] THEN WALLOCPAUX_SLR_SUB_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm:num->num->num` (fun th ->
    EXISTS_TAC `perm:num->num->num` THEN MP_TAC th)) THEN
  REWRITE_TAC[apply_colour_def] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[WALLOCPAUX_get_var_permute; apply_colour_imm_def; wl_get_var_imm_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN DISCH_THEN ACCEPT_TAC;;

(* the If case: split on the values of the guard in the source *)

let WALLOCPAUX_EAC_IF_TAC : tactic =
  fun (asl,w as g) ->
    let iff = find_term (fun t ->
        try fst(dest_const(fst(strip_comb t))) = "wl_If" with Failure _ -> false) w in
    let args = snd(strip_comb iff) in
    let cmp = el 0 args and r1 = el 1 args and ri = el 2 args
    and c1 = el 3 args and c2 = el 4 args in
    let stt = `st:(A,C,FFI)wl_state` in
    let gv = list_mk_icomb "wl_get_var" [r1; stt]
    and gvi = list_mk_icomb "wl_get_var_imm" [ri; stt]
    and wc = list_mk_icomb "wl_word_cmp" [cmp; `x:(A)word_loc`; `y:(A)word_loc`] in
    (MP_TAC(ISPEC gv (cases "option")) THEN
     DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:(A)word_loc` ASSUME_TAC)) THENL
      [WALLOCPAUX_EAC_SRCERR_TAC; ALL_TAC] THEN
     MP_TAC(ISPEC gvi (cases "option")) THEN
     DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:(A)word_loc` ASSUME_TAC)) THENL
      [WALLOCPAUX_EAC_SRCERR_TAC; ALL_TAC] THEN
     MP_TAC(ISPEC wc (cases "option")) THEN
     DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `b:bool` ASSUME_TAC)) THENL
      [WALLOCPAUX_EAC_SRCERR_TAC; ALL_TAC] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_imm_def; option_INJ]) THEN
     REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
       is_eq(concl th) && rhs(concl th) = `y:(A)word_loc`))) THEN
     WALLOCPAUX_EAC_GETVAR_TAC THEN
     ASM_CASES_TAC `b:bool` THENL
      [WALLOCPAUX_EAC_IFBR_TAC c1; WALLOCPAUX_EAC_IFBR_TAC c2]) g;;

(* helper for the Move case: renamed simultaneous assignment *)

let WALLOCPAUX_slr_alist_insert = prove
 (`!f (ks:num list) (vs:A list) (x:A spt) y live.
     LENGTH ks = LENGTH vs /\ INJ f (set_of_list ks UNION live) UNIV /\
     strong_locals_rel f (live DIFF set_of_list ks) x y
     ==> strong_locals_rel f live (alist_insert ks vs x) (alist_insert (MAP f ks) vs y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[strong_locals_rel_def] THEN
  ASM_SIMP_TAC[lookup_alist_insert; LENGTH_MAP] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `v:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALOOKUP (ZIP (ks:num list) (vs:A list)) (n:num) =
                ALOOKUP (ZIP (MAP (f:num->num) ks) vs) (f n)`
    (SUBST_ALL_TAC o SYM) THENL
   [MATCH_MP_TAC ALOOKUP_key_remap_INJ THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `INJ (f:num->num) (set_of_list (ks:num list) UNION live) (:num)` THEN
    REWRITE_TAC[INJ; IN_INSERT; IN_UNION; IN_UNIV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  MP_TAC(ISPEC `ALOOKUP (ZIP (ks:num list) (vs:A list)) (n:num)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w:A` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[option_CASE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~MEM (n:num) (ks:num list)` ASSUME_TAC THENL
   [UNDISCH_TAC `ALOOKUP (ZIP (ks:num list) (vs:A list)) (n:num) = NONE` THEN
    ASM_SIMP_TAC[ALOOKUP_ZIP_FAIL];
    ALL_TAC] THEN
  UNDISCH_TAC `strong_locals_rel (f:num->num) (live DIFF set_of_list (ks:num list))
                 (x:A spt) y` THEN
  REWRITE_TAC[strong_locals_rel_def; IN_DIFF; IN_SET_OF_LIST] THEN ASM_MESON_TAC[]);;

(* helpers for the Inst case: simplification of the assumptions only, and   *)
(* transfer of the source lookups to the renamed target                     *)

let WALLOCPAUX_GVS_ASM thl : tactic =
  REPEAT (CHANGED_TAC (GVS_ONE_PASS thl)) THEN RVEQ_TAC;;

let WALLOCPAUX_FTRANSFER_TAC : tactic =
  fun (asl,w as g) ->
    let hd_name tm = try fst(dest_const(fst(strip_comb tm))) with Failure _ -> "" in
    let slrs = filter (fun (_,th) -> hd_name (concl th) = "strong_locals_rel") asl in
    let tac_for (_,slr) =
      let args = snd(strip_comb(concl slr)) in
      let f = el 0 args and locs = el 2 args and t = el 3 args in
      let facts = filter (fun (_,th) ->
          let c = concl th in
          is_eq c && hd_name (lhs c) = "lookup" &&
          (try rand(lhs c) = locs with Failure _ -> false) &&
          hd_name (rhs c) = "SOME") asl in
      MAP_EVERY (fun (_,fa) ->
          let c = concl fa in
          let lk = rator(rator(lhs c)) and r = rand(rator(lhs c)) in
          let goal = mk_eq(mk_comb(mk_comb(lk, mk_comb(f, r)), t), rhs c) in
          if exists (fun (_,a) -> concl a = goal) asl then ALL_TAC else
          TRY (SUBGOAL_THEN goal ASSUME_TAC THENL
                [MP_TAC slr THEN REWRITE_TAC[strong_locals_rel_def] THEN
                 DISCH_THEN MATCH_MP_TAC THEN
                 ASM_REWRITE_TAC[domain_insert; domain_delete; domain_union; IN_INSERT;
                                 IN_DELETE; IN_UNION] THEN NO_TAC;
                 ALL_TAC])) facts in
    EVERY (map tac_for slrs) g;;

let WALLOCPAUX_inst_colour = prove
 (`!i (live:num_set) f (st:(A,C,FFI)wl_state) cst s1.
     wl_inst i st = SOME s1 /\
     INJ f (domain (get_live_inst i live)) UNIV /\
     INJ f (domain (union (get_writes_inst i) live)) UNIV /\
     word_state_eq_rel st cst /\
     strong_locals_rel f (domain (get_live_inst i live))
       (wl_state_locals st) (wl_state_locals cst)
     ==> ?cs1. wl_inst (apply_colour_inst f i) cst = SOME cs1 /\
               word_state_eq_rel s1 cs1 /\
               strong_locals_rel f (domain live) (wl_state_locals s1) (wl_state_locals cs1)`,
  GEN_TAC THEN WALLOCPAUX_INST_CASES_TAC THEN
  REWRITE_TAC[get_live_inst_def; get_writes_inst_def; apply_colour_inst_def;
              apply_colour_imm_def; WALLOCPAUX_reg_imm_CASE] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_state_eq_rel_def]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  WALLOCPAUX_GVS_ASM[wl_inst_def; wl_assign_def; wl_set_var_def; wl_set_fp_var_def;
      wl_word_exp_def; the_words_def; wl_get_var_def; wl_get_vars_def; wl_get_fp_var_def;
      wl_mem_store_def; wl_mem_load_def; option_case_eq; pair_case_eq; case_eq "word_loc";
      list_case_eq; COND_CASE_EQ] THEN
  WALLOCPAUX_FTRANSFER_TAC THEN
  SIMP[wl_inst_def; wl_assign_def; wl_set_var_def; wl_set_fp_var_def;
       wl_word_exp_def; the_words_def; wl_get_var_def; wl_get_vars_def; wl_get_fp_var_def;
       wl_mem_store_def; wl_mem_load_def] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[word_state_eq_rel_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  WALLOCPAUX_SLR_CHAIN_TAC);;

(* helper for the Alloc and Call cases: popping two stacks whose top frames *)
(* hold renamed copies of the same environment                             *)

let WALLOCPAUX_pop_env_rel = prove
 (CASE_TERM
  `!f (x1:((A)word_loc)spt) (y1:((A)word_loc)spt) (lsB:(num#(A)word_loc)list) lsA
    (s2:(A,C,FFI)wl_state) (t2:(A,C,FFI)wl_state) s3 t3 (n:num option)
    (opt:(num#num#num)option) keysS keysT.
     MAP f (MAP FST lsB) = MAP FST lsA /\
     INJ f (domain x1 UNION set_of_list (MAP FST lsB)) UNIV /\
     strong_locals_rel f (domain x1) x1 y1 /\
     s_key_eq (wl_state_stack s2) (CONS (StackFrame n (toAList x1) lsB opt) keysS) /\
     s_key_eq (wl_state_stack t2) (CONS (StackFrame n (toAList y1) lsA opt) keysT) /\
     s_val_eq (wl_state_stack s2) (wl_state_stack t2) /\
     wl_pop_env s2 = SOME s3 /\ wl_pop_env t2 = SOME t3
     ==> strong_locals_rel f UNIV (wl_state_locals s3) (wl_state_locals t3) /\
         s_key_eq (wl_state_stack s3) keysS /\ s_key_eq (wl_state_stack t3) keysT /\
         s_val_eq (wl_state_stack s3) (wl_state_stack t3) /\
         wl_state_locals_size s3 = n /\ wl_state_locals_size t3 = n /\
         (match opt with
            NONE -> wl_state_handler s3 = wl_state_handler s2 /\
                    wl_state_handler t3 = wl_state_handler t2
          | SOME (h,l1,l2) -> wl_state_handler s3 = h /\ wl_state_handler t3 = h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s2:(A,C,FFI)wl_state`; `s3:(A,C,FFI)wl_state`; `n:num option`;
                 `toAList (x1:((A)word_loc)spt)`; `lsB:(num#(A)word_loc)list`;
                 `opt:(num#num#num)option`; `keysS:((A)stack_frame)list`;
                 `wl_state_stack (t2:(A,C,FFI)wl_state)`] s_key_eq_val_eq_pop_env) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lszT:(num#(A)word_loc)list` (X_CHOOSE_THEN
    `lsT:(num#(A)word_loc)list` (X_CHOOSE_THEN `restT:((A)stack_frame)list`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`t2:(A,C,FFI)wl_state`; `t3:(A,C,FFI)wl_state`; `n:num option`;
                 `toAList (y1:((A)word_loc)spt)`; `lsA:(num#(A)word_loc)list`;
                 `opt:(num#num#num)option`; `keysT:((A)stack_frame)list`;
                 `wl_state_stack (s2:(A,C,FFI)wl_state)`] s_key_eq_val_eq_pop_env) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    ONCE_REWRITE_TAC[s_val_eq_sym] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lszS:(num#(A)word_loc)list` (X_CHOOSE_THEN
    `lsS:(num#(A)word_loc)list` (X_CHOOSE_THEN `restS:((A)stack_frame)list`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `MAP SND (lsS:(num#(A)word_loc)list) = MAP SND (lsT:(num#(A)word_loc)list) /\
                s_val_eq (restS:((A)stack_frame)list) restT /\
                MAP FST lsS = MAP FST (lsB:(num#(A)word_loc)list)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `s_key_eq (wl_state_stack (s2:(A,C,FFI)wl_state))
                   (CONS (StackFrame n (toAList (x1:((A)word_loc)spt)) lsB opt) keysS)` THEN
    UNDISCH_TAC `s_val_eq (wl_state_stack (s2:(A,C,FFI)wl_state))
                   (wl_state_stack (t2:(A,C,FFI)wl_state))` THEN
    ASM_REWRITE_TAC[s_val_eq_def; s_key_eq_def; s_frame_val_eq_def2; s_frame_key_eq_def2] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC s_val_eq_trans THEN EXISTS_TAC `restT:((A)stack_frame)list` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC s_val_eq_trans THEN
      EXISTS_TAC `restS:((A)stack_frame)list` THEN
      ONCE_REWRITE_TAC[s_val_eq_sym] THEN ASM_REWRITE_TAC[]) THEN
  TRY(MAP_EVERY (fun (s,t) ->
        UNDISCH_TAC (mk_eq(mk_comb(`wl_pop_env:(A,C,FFI)wl_state->((A,C,FFI)wl_state)option`, s),
                           mk_comb(`SOME:(A,C,FFI)wl_state->((A,C,FFI)wl_state)option`, t))))
        [`s2:(A,C,FFI)wl_state`,`s3:(A,C,FFI)wl_state`; `t2:(A,C,FFI)wl_state`,`t3:(A,C,FFI)wl_state`] THEN
      ASM_REWRITE_TAC[wl_pop_env_def] THEN
      SPEC_TAC(`opt:(num#num#num)option`, `opt:(num#num#num)option`) THEN
      REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; option_CASE; pair_CASE;
                  WALLOCPAUX_stack_frame_CASE; list_CASE; option_INJ] THEN
      REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
      REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN NO_TAC) THEN
  TRY(REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
        try let h,args = strip_comb(concl th) in
            fst(dest_const h) = "option_CASE" && hd args = `opt:(num#num#num)option`
        with Failure _ -> false))) THEN
      SPEC_TAC(`opt:(num#num#num)option`, `opt:(num#num#num)option`) THEN
      REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; option_CASE; pair_CASE] THEN
      MESON_TAC[] THEN NO_TAC) THEN
  SUBGOAL_THEN `LENGTH (MAP FST (lsB:(num#(A)word_loc)list)) =
                LENGTH (MAP SND (lsT:(num#(A)word_loc)list))` ASSUME_TAC THENL
   [UNDISCH_TAC `MAP FST (lsS:(num#(A)word_loc)list) = MAP FST (lsB:(num#(A)word_loc)list)` THEN
    UNDISCH_TAC `MAP SND (lsS:(num#(A)word_loc)list) = MAP SND (lsT:(num#(A)word_loc)list)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[LENGTH_MAP];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (MAP FST (lsA:(num#(A)word_loc)list)) =
                LENGTH (MAP SND (lsT:(num#(A)word_loc)list))` ASSUME_TAC THENL
   [UNDISCH_TAC `MAP (f:num->num) (MAP FST (lsB:(num#(A)word_loc)list)) =
                 MAP FST (lsA:(num#(A)word_loc)list)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[LENGTH_MAP] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[strong_locals_rel_def; IN_UNIV; lookup_union; lookup_fromAList;
                  ALOOKUP_toAList] THEN
  MAP_EVERY X_GEN_TAC [`nn:num`; `v:(A)word_loc`] THEN
  MP_TAC(ISPEC `ALOOKUP (ZIP (MAP FST (lsB:(num#(A)word_loc)list))
                   (MAP SND (lsT:(num#(A)word_loc)list))) (nn:num)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w:(A)word_loc` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[option_CASE] THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `~MEM (nn:num) (MAP FST (lsB:(num#(A)word_loc)list))` ASSUME_TAC THENL
     [UNDISCH_TAC `ALOOKUP (ZIP (MAP FST (lsB:(num#(A)word_loc)list))
                     (MAP SND (lsT:(num#(A)word_loc)list))) (nn:num) = NONE` THEN
      ASM_SIMP_TAC[ALOOKUP_ZIP_FAIL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(nn:num) IN domain (x1:((A)word_loc)spt)` ASSUME_TAC THENL
     [REWRITE_TAC[domain_lookup] THEN EXISTS_TAC `v:(A)word_loc` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `ALOOKUP (ZIP (MAP FST (lsA:(num#(A)word_loc)list))
                    (MAP SND (lsT:(num#(A)word_loc)list))) ((f:num->num) nn) = NONE`
      SUBST1_TAC THENL
     [ASM_SIMP_TAC[ALOOKUP_ZIP_FAIL] THEN
      UNDISCH_TAC `MAP (f:num->num) (MAP FST (lsB:(num#(A)word_loc)list)) =
                   MAP FST (lsA:(num#(A)word_loc)list)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[ISPEC `f:num->num` MEM_MAP] THEN
      UNDISCH_TAC `INJ (f:num->num) (domain (x1:((A)word_loc)spt) UNION
                     set_of_list (MAP FST (lsB:(num#(A)word_loc)list))) (:num)` THEN
      UNDISCH_TAC `(nn:num) IN domain (x1:((A)word_loc)spt)` THEN
      UNDISCH_TAC `~MEM (nn:num) (MAP FST (lsB:(num#(A)word_loc)list))` THEN
      REWRITE_TAC[INJ; IN_UNION; IN_SET_OF_LIST; IN_UNIV] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[option_CASE] THEN
    UNDISCH_TAC `strong_locals_rel (f:num->num) (domain (x1:((A)word_loc)spt)) x1 y1` THEN
    REWRITE_TAC[strong_locals_rel_def] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    SUBGOAL_THEN `ALOOKUP (ZIP (MAP FST (lsA:(num#(A)word_loc)list))
                    (MAP SND (lsT:(num#(A)word_loc)list))) ((f:num->num) nn) = SOME w`
      SUBST1_TAC THENL
     [UNDISCH_TAC `MAP (f:num->num) (MAP FST (lsB:(num#(A)word_loc)list)) =
                   MAP FST (lsA:(num#(A)word_loc)list)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC ALOOKUP_key_remap_2 THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `INJ (f:num->num) (domain (x1:((A)word_loc)spt) UNION
                     set_of_list (MAP FST (lsB:(num#(A)word_loc)list))) (:num)` THEN
      REWRITE_TAC[INJ; IN_UNION; IN_SET_OF_LIST; IN_UNIV] THEN MESON_TAC[];
      REWRITE_TAC[option_CASE]]]);;

let WALLOCPAUX_s_key_eq_pop_env_SOME = prove
 (`!(s:(A,C,FFI)wl_state) n l0 l (opt:(num#num#num)option) rest.
     s_key_eq (wl_state_stack s) (CONS (StackFrame n l0 l opt) rest)
     ==> ?s'. wl_pop_env s = SOME s'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_pop_env_def] THEN
  MP_TAC(ISPEC `wl_state_stack (s:(A,C,FFI)wl_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `hd:(A)stack_frame`
    (X_CHOOSE_THEN `tl:((A)stack_frame)list` SUBST1_TAC))) THEN
  REWRITE_TAC[s_key_eq_def] THEN
  STRUCT_CASES_TAC (ISPEC `hd:(A)stack_frame` (cases "stack_frame")) THEN
  REWRITE_TAC[s_frame_key_eq_def2; list_CASE; WALLOCPAUX_stack_frame_CASE] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`a3:(num#num#num)option`] THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; option_CASE; pair_CASE] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[option_INJ] THEN
  MESON_TAC[]);;

let WALLOCPAUX_push_env_NONE_stack = prove
 (`!(e1:((A)word_loc)spt) e2 (s:(A,C,FFI)wl_state).
     wl_state_stack (wl_push_env (e1,e2) NONE s) =
     CONS (StackFrame (wl_state_locals_size s) (toAList e1)
             (FST (env_to_list e2 (wl_state_permute s))) NONE) (wl_state_stack s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT PAIRARG_TAC THEN SIMP[]);;

let WALLOCPAUX_store_eq_get_has = prove
 (`!(s:(A,C,FFI)wl_state) (t:(A,C,FFI)wl_state).
     wl_state_store t = wl_state_store s
     ==> (!v. wl_get_store v t = wl_get_store v s) /\
         (!x. wl_has_space x t = wl_has_space x s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[wl_get_store_def; wl_has_space_def]);;

(* rewrite all assumptions but the equation itself, and the goal, with an  *)
(* equation that is an assumption                                          *)

let WALLOCPAUX_NORM_EQ_TAC (eq:term) : tactic =
  fun (asl,w as g) ->
    let th = snd(find (fun (_,th) -> concl th = eq) asl) in
    (RULE_ASSUM_TAC (fun th' -> if concl th' = eq then th' else REWRITE_RULE[th] th') THEN
     REWRITE_TAC[th]) g;;

let WALLOCPAUX_prog_size_induct = prove
 (`!P. (!p:(A)wl_prog. (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) p ==> P q)
                       ==> P p)
       ==> !p. P p`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n (p:(A)wl_prog). wl_prog_size (\x:A. 0) p = n ==> P p`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN ASM_MESON_TAC[]);;

let WALLOCPAUX_eac_Skip = prove
 (`(!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Skip:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_Skip:(A)wl_prog)`,
  WALLOCPAUX_EAC_OPEN_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[apply_colour_def; LET_DEF; LET_END_DEF; pair_CASE; option_DISTINCT] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[pair_CASE; option_CASE] THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[get_live_def]);;

let WALLOCPAUX_eac_Move = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Move a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_Move a0 a1:(A)wl_prog)`,
  WALLOCPAUX_EAC_OPEN_TAC THEN WALLOCPAUX_EAC_EXPAND_TAC THEN
  REWRITE_TAC[apply_colour_def] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_CASES_TAC `ALL_DISTINCT (MAP FST (a1:(num#num)list))` THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPEC `wl_get_vars (MAP SND (a1:(num#num)list)) (st:(A,C,FFI)wl_state)`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `vs:((A)word_loc)list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  SUBGOAL_THEN `LENGTH (MAP ((f:num->num) o FST) (a1:(num#num)list)) =
                LENGTH (MAP (f o SND) a1)` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  ASM_SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP] THEN REWRITE_TAC[MAP_o] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_allocProof_domain_numset_list_insert; domain_union;
                              domain_FOLDR_delete; domain_def; UNION_EMPTY]) THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP (f:num->num) (MAP FST (a1:(num#num)list)))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (term_match [] `INJ (f:num->num) (s UNION t) UNIV`) (concl th) &&
      can (find_term (fun t -> t = `MAP FST (a1:(num#num)list)`)) (concl th))) THEN
    REWRITE_TAC[INJ; IN_UNION; IN_SET_OF_LIST; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  WALLOCPAUX_EAC_GETVARS_TAC THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; option_DISTINCT] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[word_state_eq_rel_def; wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    MATCH_MP_TAC WALLOCPAUX_slr_alist_insert THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[get_vars_length_lemma; LENGTH_MAP];
      WALLOCPAUX_SLR_SUB_TAC]]);;

let WALLOCPAUX_eac_Inst = prove
 (`!a0.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Inst a0:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_Inst a0:(A)wl_prog)`,
  WALLOCPAUX_EAC_OPEN_TAC THEN WALLOCPAUX_EAC_EXPAND_TAC THEN
  REWRITE_TAC[apply_colour_def] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  MP_TAC(ISPEC `wl_inst (a0:(A)inst) (st:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `s1:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  MP_TAC(ISPECL [`a0:(A)inst`; `live:num_set`; `f:num->num`; `st:(A,C,FFI)wl_state`;
                 `cst:(A,C,FFI)wl_state`; `s1:(A,C,FFI)wl_state`] WALLOCPAUX_inst_colour) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[word_state_eq_rel_def]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cs1:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; option_DISTINCT]);;

let WALLOCPAUX_eac_Assign = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Assign a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_Assign a0 a1:(A)wl_prog)`,
  WALLOCPAUX_EAC_OPENC_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; wl_set_var_def] THEN WALLOCPAUX_EAC_EXPAND_TAC THEN
  SUBGOAL_THEN `wl_word_exp (cst:(A,C,FFI)wl_state) (apply_colour_exp f a1) = SOME a`
    SUBST1_TAC THENL
   [MATCH_MP_TAC apply_colour_exp_lemma THEN EXISTS_TAC `st:(A,C,FFI)wl_state` THEN
    ASM_REWRITE_TAC[word_state_eq_rel_def] THEN WALLOCPAUX_SLR_SUB_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[option_CASE; pair_CASE] THEN WALLOCPAUX_EAC_FINISH_TAC);;

let WALLOCPAUX_eac_Get = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Get a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_Get a0 a1:(A)wl_prog)`,
  WALLOCPAUX_EAC_OPENC_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; wl_set_var_def; wl_get_store_def] THEN WALLOCPAUX_EAC_EXPAND_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[wl_get_store_def; option_CASE; pair_CASE] THEN
  WALLOCPAUX_EAC_FINISH_TAC);;

let WALLOCPAUX_eac_Set = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Set a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_Set a0 a1:(A)wl_prog)`,
  WALLOCPAUX_EAC_OPENC_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; wl_set_store_def; COND_CASE_EQ] THEN WALLOCPAUX_EAC_EXPAND_TAC THEN
  SUBGOAL_THEN `wl_word_exp (cst:(A,C,FFI)wl_state) (apply_colour_exp f a1) = SOME a`
    ASSUME_TAC THENL
   [MATCH_MP_TAC apply_colour_exp_lemma THEN EXISTS_TAC `st:(A,C,FFI)wl_state` THEN
    ASM_REWRITE_TAC[word_state_eq_rel_def] THEN WALLOCPAUX_SLR_SUB_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; wl_set_store_def] THEN
  WALLOCPAUX_EAC_FINISH_TAC);;

let WALLOCPAUX_eac_Store = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Store a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_Store a0 a1:(A)wl_prog)`,
  WALLOCPAUX_EAC_OPENC_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; pair_case_eq; case_eq "word_loc"; wl_mem_store_def; COND_CASE_EQ] THEN
  WALLOCPAUX_EAC_EXPAND_TAC THEN
  SUBGOAL_THEN `wl_word_exp (cst:(A,C,FFI)wl_state) (apply_colour_exp f a0) = SOME (wl_Word a)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC apply_colour_exp_lemma THEN EXISTS_TAC `st:(A,C,FFI)wl_state` THEN
    ASM_REWRITE_TAC[word_state_eq_rel_def] THEN WALLOCPAUX_SLR_SUB_TAC;
    ALL_TAC] THEN
  WALLOCPAUX_EAC_GETVAR_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; wl_mem_store_def; WALLOCPAUX_word_loc_CASE] THEN
  WALLOCPAUX_EAC_FINISH_TAC);;

let WALLOCPAUX_eac_MustTerminate = prove
 (`!a0.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (MustTerminate a0:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (MustTerminate a0:(A)wl_prog)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_eac_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  WALLOCPAUX_EAC_EXPAND_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `a0:(A)wl_prog`) THEN
  ANTS_TAC THENL [WALLOCPAUX_SIZE_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC
    `wl_state_clock_fupd (K (MustTerminate_limit (:A)))
       (wl_state_termdep_fupd (K (wl_state_termdep st - 1)) (st:(A,C,FFI)wl_state))`) THEN
  REWRITE_TAC[WALLOCPAUX_eac_Q_def] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`wl_state_clock_fupd (K (MustTerminate_limit (:A)))
       (wl_state_termdep_fupd (K (wl_state_termdep (st:(A,C,FFI)wl_state) - 1))
          (cst:(A,C,FFI)wl_state))`;
     `f:num->num`; `live:num_set`; `lt:(num_set#num_set)list`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm:num->num->num` (fun th ->
    EXISTS_TAC `perm:num->num->num` THEN MP_TAC th)) THEN
  REWRITE_TAC[apply_colour_def] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_state_INFO.ri_fupdcanon] THEN
  WALLOCPAUX_NAME_EVAL_TAC `a0:(A)wl_prog`
    [`r1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] THEN
  WALLOCPAUX_NAME_EVAL_TAC `apply_colour f (a0:(A)wl_prog)`
    [`r2:((A)wl_result)option`; `s2:(A,C,FFI)wl_state`] THEN
  ASM_CASES_TAC `wl_state_termdep (st:(A,C,FFI)wl_state) = 0` THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  ASM_CASES_TAC `r1 = SOME (wl_Error:(A)wl_result)` THEN
  ASM_REWRITE_TAC([pair_CASE; option_INJ] @ WALLOCPAUX_wl_result_distinct) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `r1 = SOME (wl_TimeOut:(A)wl_result)` THEN ASM_REWRITE_TAC[pair_CASE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_state_eq_rel_def]) THEN
  REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]);;

(* the Call case of evaluate_apply_colour: the tail call *)

let WALLOCPAUX_wser_refl = prove
 (`!s:(A,C,FFI)wl_state. word_state_eq_rel s s`,
  REWRITE_TAC[word_state_eq_rel_def]);;

let WALLOCPAUX_eac_Call_tail = prove
 (`!(dest:num option) (args:num list) (h:(num#(A)wl_prog#num#num)option)
    (st:(A,C,FFI)wl_state).
     WALLOCPAUX_eac_Q st (wl_Call NONE dest args h:(A)wl_prog)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WALLOCPAUX_eac_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  WALLOCPAUX_EAC_EXPAND_TAC THEN
  EXISTS_TAC `wl_state_permute (cst:(A,C,FFI)wl_state)` THEN
  REWRITE_TAC[apply_colour_def; LET_DEF; LET_END_DEF; option_CASE] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
  MP_TAC(ISPEC `wl_get_vars args (st:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:((A)word_loc)list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_wl_result_CASE] THEN
  WALLOCPAUX_EAC_GETVARS_TAC THEN ASM_REWRITE_TAC[option_CASE] THEN
  SUBGOAL_THEN `bad_dest_args (dest:num option) (MAP (f:num->num) args) <=>
                bad_dest_args dest args` SUBST1_TAC THENL
   [REWRITE_TAC[bad_dest_args_def; MAP_EQ_NIL]; ALL_TAC] THEN
  ASM_CASES_TAC `bad_dest_args (dest:num option) (args:num list)` THEN
  ASM_REWRITE_TAC[pair_CASE; option_CASE; WALLOCPAUX_wl_result_CASE] THEN
  REWRITE_TAC[add_ret_loc_def] THEN
  MP_TAC(ISPEC `wl_find_code (dest:num option) (x:((A)word_loc)list)
                  (wl_state_code (st:(A,C,FFI)wl_state)) (wl_state_stack_size st)`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `fc:((A)word_loc)list#(A)wl_prog#(num)option` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_wl_result_CASE] THEN
  SUBGOAL_THEN `?args1 prog ss. fc = (args1:((A)word_loc)list,prog:(A)wl_prog,ss:(num)option)`
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  REWRITE_TAC[pair_CASE] THEN
  STRUCT_CASES_TAC (ISPEC `h:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; pair_CASE; WALLOCPAUX_wl_result_CASE] THEN
  ASM_CASES_TAC `wl_state_clock (st:(A,C,FFI)wl_state) = 0` THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_wl_result_CASE] THENL
   [REWRITE_TAC(WALLOCPAUX_wl_result_distinct @ [option_INJ]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC WALLOCPAUX_wser_permute THEN MATCH_MP_TAC WALLOCPAUX_wser_flush THEN
      ASM_REWRITE_TAC[word_state_eq_rel_def];
      REWRITE_TAC[wl_flush_state_def; wl_state_INFO.ri_accfupds; K_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_call_env args1 ss (wl_dec_clock (wl_state_permute_fupd
                  (K (wl_state_permute cst)) (st:(A,C,FFI)wl_state))) =
                wl_call_env args1 ss (wl_dec_clock (cst:(A,C,FFI)wl_state))` SUBST1_TAC THENL
   [REWRITE_TAC[wl_state_component_equality; wl_call_env_def; wl_dec_clock_def] THEN
    SIMP[];
    ALL_TAC] THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (prog:(A)wl_prog,
     wl_call_env args1 ss (wl_dec_clock (cst:(A,C,FFI)wl_state)))`
    [`r:((A)wl_result)option`; `t:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN
  COND_CASES_TAC THEN REWRITE_TAC[pair_CASE; WALLOCPAUX_wser_refl] THEN
  UNDISCH_TAC `~wl_bad_fun_return (r:((A)wl_result)option)` THEN
  SPEC_TAC(`r:((A)wl_result)option`, `r:((A)wl_result)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; wl_bad_fun_return_def; option_CASE] THEN
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `a:(A)wl_result` (cases "wl_result")) THEN
  REWRITE_TAC[wl_bad_fun_return_def; WALLOCPAUX_wl_result_CASE; COND_ID]);;

(* the Call case of evaluate_apply_colour: the returning call *)

(* helpers for the returning call: the permutation oracle of the caller is  *)
(* the push permutation followed by the oracle of the callee                *)

let WALLOCPAUX_push_env_perm = prove
 (`!(e1:((A)word_loc)spt) e2 (b:(num#(A)wl_prog#num#num)option) (s:(A,C,FFI)wl_state)
    (P:num->num->num) perm2.
     wl_push_env (e1,e2) b
       (wl_state_permute_fupd (K (\n. if n = 0 then P 0 else perm2 (n - 1))) s) =
     wl_state_permute_fupd (K perm2) (wl_push_env (e1,e2) b (wl_state_permute_fupd (K P) s))`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`b:(num#(A)wl_prog#num#num)option`, `b:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def; env_to_list_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE] THEN
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[] THEN
  REWRITE_TAC[FUN_EQ_THM; ADD_EQ_0; ARITH_EQ; ADD_SUB]);;

let WALLOCPAUX_call_env_permute = prove
 (`!a b p (s:(A,C,FFI)wl_state).
     wl_call_env a b (wl_state_permute_fupd (K p) s) =
     wl_state_permute_fupd (K p) (wl_call_env a b s) /\
     wl_dec_clock (wl_state_permute_fupd (K p) s) =
     wl_state_permute_fupd (K p) (wl_dec_clock s)`,
  REWRITE_TAC[wl_state_component_equality; wl_call_env_def; wl_dec_clock_def] THEN SIMP[]);;

(* the callee states of a returning call differ only in the stack *)

let WALLOCPAUX_push_env_permute_handler = prove
 (CASE_TERM
  `!(e:((A)word_loc)spt#((A)word_loc)spt) (b:(num#(A)wl_prog#num#num)option)
    (s:(A,C,FFI)wl_state).
     wl_state_permute (wl_push_env e b s) = (\n. wl_state_permute s (n + 1)) /\
     wl_state_handler (wl_push_env e b s) =
       (match b with NONE -> wl_state_handler s | SOME x -> LENGTH (wl_state_stack s))`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`b:(num#(A)wl_prog#num#num)option`, `b:(num#(A)wl_prog#num#num)option`) THEN
  SUBST1_TAC(ISPEC `e:((A)word_loc)spt#((A)word_loc)spt` (GSYM PAIR)) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def; env_to_list_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE; option_CASE] THEN SIMP[]);;

let WALLOCPAUX_push_env_stack_gen = prove
 (CASE_TERM
  `!(e1:((A)word_loc)spt) e2 (b:(num#(A)wl_prog#num#num)option) (s:(A,C,FFI)wl_state).
     wl_state_stack (wl_push_env (e1,e2) b s) =
     CONS (StackFrame (wl_state_locals_size s) (toAList e1)
             (FST (env_to_list e2 (wl_state_permute s)))
             (match b with
                NONE -> NONE
              | SOME (w,hp,l1,l2) -> SOME (wl_state_handler s,l1,l2)))
          (wl_state_stack s)`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`b:(num#(A)wl_prog#num#num)option`, `b:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN REPEAT PAIRARG_TAC THEN
  SIMP[option_CASE; pair_CASE]);;

(* two environments built from renamed copies of the same frame *)

let WALLOCPAUX_union_alist_slr = prove
 (`!f (x1:((A)word_loc)spt) (y1:((A)word_loc)spt) (lsB:(num#(A)word_loc)list)
    (lsA:(num#(A)word_loc)list) (lss:(num#(A)word_loc)list) (lss':(num#(A)word_loc)list).
     MAP f (MAP FST lsB) = MAP FST lsA /\
     INJ f (domain x1 UNION set_of_list (MAP FST lsB)) UNIV /\
     strong_locals_rel f (domain x1) x1 y1 /\
     MAP FST lss = MAP FST lsB /\ MAP FST lss' = MAP FST lsA /\ MAP SND lss = MAP SND lss'
     ==> strong_locals_rel f UNIV (union (fromAList lss) (fromAList (toAList x1)))
                                  (union (fromAList lss') (fromAList (toAList y1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[strong_locals_rel_def; IN_UNIV; lookup_union; lookup_fromAList;
              ALOOKUP_toAList] THEN
  MAP_EVERY X_GEN_TAC [`nn:num`; `v:(A)word_loc`] THEN
  SUBGOAL_THEN `lss = ZIP (MAP FST (lsB:(num#(A)word_loc)list)) (MAP SND (lss':(num#(A)word_loc)list)) /\
                lss' = ZIP (MAP FST (lsA:(num#(A)word_loc)list)) (MAP SND lss') /\
                LENGTH (MAP FST lsB) = LENGTH (MAP SND lss') /\
                LENGTH (MAP FST lsA) = LENGTH (MAP SND lss')` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `MAP FST (lss:(num#(A)word_loc)list) = MAP FST (lsB:(num#(A)word_loc)list)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `MAP SND (lss:(num#(A)word_loc)list) = MAP SND (lss':(num#(A)word_loc)list)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[ZIP_MAP_FST_SND_EQ];
      UNDISCH_TAC `MAP FST (lss':(num#(A)word_loc)list) = MAP FST (lsA:(num#(A)word_loc)list)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[ZIP_MAP_FST_SND_EQ];
      UNDISCH_TAC `MAP FST (lss:(num#(A)word_loc)list) = MAP FST (lsB:(num#(A)word_loc)list)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `MAP SND (lss:(num#(A)word_loc)list) = MAP SND (lss':(num#(A)word_loc)list)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LENGTH_MAP];
      UNDISCH_TAC `MAP FST (lss':(num#(A)word_loc)list) = MAP FST (lsA:(num#(A)word_loc)list)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LENGTH_MAP]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `lss' = ZIP (MAP FST (lsA:(num#(A)word_loc)list))
                                             (MAP SND (lss':(num#(A)word_loc)list))`
                          then SUBST1_TAC th else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if concl th = `lss = ZIP (MAP FST (lsB:(num#(A)word_loc)list))
                                             (MAP SND (lss':(num#(A)word_loc)list))`
                          then SUBST1_TAC th else NO_TAC) THEN
  MP_TAC(ISPEC `ALOOKUP (ZIP (MAP FST (lsB:(num#(A)word_loc)list))
                   (MAP SND (lss':(num#(A)word_loc)list))) (nn:num)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w:(A)word_loc` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[option_CASE] THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `~MEM (nn:num) (MAP FST (lsB:(num#(A)word_loc)list))` ASSUME_TAC THENL
     [UNDISCH_TAC `ALOOKUP (ZIP (MAP FST (lsB:(num#(A)word_loc)list))
                     (MAP SND (lss':(num#(A)word_loc)list))) (nn:num) = NONE` THEN
      ASM_SIMP_TAC[ALOOKUP_ZIP_FAIL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(nn:num) IN domain (x1:((A)word_loc)spt)` ASSUME_TAC THENL
     [REWRITE_TAC[domain_lookup] THEN EXISTS_TAC `v:(A)word_loc` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `ALOOKUP (ZIP (MAP FST (lsA:(num#(A)word_loc)list))
                    (MAP SND (lss':(num#(A)word_loc)list))) ((f:num->num) nn) = NONE`
      SUBST1_TAC THENL
     [ASM_SIMP_TAC[ALOOKUP_ZIP_FAIL] THEN
      UNDISCH_TAC `MAP (f:num->num) (MAP FST (lsB:(num#(A)word_loc)list)) =
                   MAP FST (lsA:(num#(A)word_loc)list)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[ISPEC `f:num->num` MEM_MAP] THEN
      UNDISCH_TAC `INJ (f:num->num) (domain (x1:((A)word_loc)spt) UNION
                     set_of_list (MAP FST (lsB:(num#(A)word_loc)list))) (:num)` THEN
      UNDISCH_TAC `(nn:num) IN domain (x1:((A)word_loc)spt)` THEN
      UNDISCH_TAC `~MEM (nn:num) (MAP FST (lsB:(num#(A)word_loc)list))` THEN
      REWRITE_TAC[INJ; IN_UNION; IN_SET_OF_LIST; IN_UNIV] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[option_CASE] THEN
    UNDISCH_TAC `strong_locals_rel (f:num->num) (domain (x1:((A)word_loc)spt)) x1 y1` THEN
    REWRITE_TAC[strong_locals_rel_def] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    SUBGOAL_THEN `ALOOKUP (ZIP (MAP FST (lsA:(num#(A)word_loc)list))
                    (MAP SND (lss':(num#(A)word_loc)list))) ((f:num->num) nn) = SOME w`
      SUBST1_TAC THENL
     [UNDISCH_TAC `MAP (f:num->num) (MAP FST (lsB:(num#(A)word_loc)list)) =
                   MAP FST (lsA:(num#(A)word_loc)list)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC ALOOKUP_key_remap_2 THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `INJ (f:num->num) (domain (x1:((A)word_loc)spt) UNION
                     set_of_list (MAP FST (lsB:(num#(A)word_loc)list))) (:num)` THEN
      REWRITE_TAC[INJ; IN_UNION; IN_SET_OF_LIST; IN_UNIV] THEN MESON_TAC[];
      REWRITE_TAC[option_CASE]]]);;

let WALLOCPAUX_call_states = prove
 (CASE_TERM
  `!(st:(A,C,FFI)wl_state) (cst:(A,C,FFI)wl_state) (x1:((A)word_loc)spt) x2 y1 y2
    (h:(num#(A)wl_prog#num#num)option) hh (P:num->num->num) args1 (ss:num option).
     word_state_eq_rel st cst /\
     (match h with
        NONE -> hh = NONE
      | SOME (w,hp,l1,l2) ->
          (match hh with NONE -> F | SOME (a,b,c,d) -> c = l1 /\ d = l2)) /\
     (\n. P (n + 1)) = (\n. wl_state_permute cst (n + 1)) /\
     s_val_eq (wl_state_stack (wl_push_env (x1,x2) h (wl_state_permute_fupd (K P) st)))
              (wl_state_stack (wl_push_env (y1,y2) hh cst))
     ==> wl_call_env args1 ss (wl_push_env (y1,y2) hh cst) =
         wl_state_stack_fupd
           (K (wl_state_stack (wl_call_env args1 ss (wl_push_env (y1,y2) hh cst))))
           (wl_call_env args1 ss (wl_push_env (x1,x2) h (wl_state_permute_fupd (K P) st)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP s_val_eq_stack_size) THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[wl_call_env_def; push_env_stack_max_eq; wl_state_component_equality;
              wl_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_TAC THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[wl_push_env_const; WALLOCPAUX_push_env_permute_handler;
              wl_state_INFO.ri_accfupds; K_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_state_eq_rel_def]) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "option_CASE" with Failure _ -> false)) THEN
  SPEC_TAC(`hh:(num#(A)wl_prog#num#num)option`, `hh:(num#(A)wl_prog#num#num)option`) THEN
  SPEC_TAC(`h:(num#(A)wl_prog#num#num)option`, `h:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; option_CASE; pair_CASE; option_DISTINCT] THEN
  ASM_REWRITE_TAC[]);;

(* refine an existential witness: prove ?v. body from ?v2. body[t/v] *)

let WALLOCPAUX_EX_REFINE_TAC (t:term) (v2:term) : tactic =
  fun (asl,w as g) ->
    let v,body = dest_exists w in
    let newg = mk_exists(v2, subst [t,v] body) in
    (SUBGOAL_THEN newg (X_CHOOSE_THEN v2 (fun th -> EXISTS_TAC t THEN ACCEPT_TAC th))) g;;

(* permute_swap_lemma4 for the goal ?perm. body, where body contains        *)
(* wl_evaluate (prog,wl_state_permute_fupd (K perm) sc)                     *)

let WALLOCPAUX_PERM_SWAP4_TAC (prog:term) (sc:term) : tactic =
  fun (asl,w as g) ->
    let pv,body = dest_exists w in
    let et = list_mk_icomb "wl_evaluate"
               [mk_pair(prog, list_mk_icomb "wl_state_permute_fupd"
                                [mk_comb(mk_const("K",[type_of pv,aty;
                                   `:num->num->num`,bty]), pv); sc])] in
    let r = mk_var("r", type_of et) in
    let plam = mk_abs(r, subst [r, et] body) in
    let th = BETA_RULE (ISPECL [prog; sc; plam] permute_swap_lemma4) in
    (MATCH_MP_TAC th THEN CONJ_TAC) g;;

let WALLOCPAUX_eac_Call_ret = prove
 (CASE_TERM
  `!(n:num list) (names:num_set#num_set) (ret_handler:(A)wl_prog) (l1:num) (l2:num)
    (dest:num option) (args:num list) (h:(num#(A)wl_prog#num#num)option).
     (!st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st ret_handler) /\
     (match h with
        NONE -> T
      | SOME (v,prog,l1,l2) -> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st prog)
     ==> !st:(A,C,FFI)wl_state.
           WALLOCPAUX_eac_Q st (wl_Call (SOME (n,names,ret_handler,l1,l2)) dest args h)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihr") (LABEL_TAC "ihh")) THEN
  GEN_TAC THEN REWRITE_TAC[WALLOCPAUX_eac_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?p0 p1. names = (p0:num_set,p1:num_set)`
    (X_CHOOSE_THEN `p0:num_set` (X_CHOOSE_THEN `p1:num_set` SUBST_ALL_TAC)) THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  WALLOCPAUX_EAC_EXPAND_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
  let srcerr thl =
    EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[WALLOCPAUX_with_same_permute] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC([option_CASE; pair_CASE; WALLOCPAUX_word_loc_CASE; add_ret_loc_def;
                     WALLOCPAUX_wl_result_CASE] @ thl) in
  MP_TAC(ISPEC `wl_get_vars args (st:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `xs:((A)word_loc)list` ASSUME_TAC)) THENL
   [srcerr []; ALL_TAC] THEN
  ASM_CASES_TAC `bad_dest_args (dest:num option) (args:num list)` THENL [srcerr []; ALL_TAC] THEN
  MP_TAC(ISPEC `wl_find_code (dest:num option) (CONS (wl_Loc l1 l2) (xs:((A)word_loc)list))
                  (wl_state_code (st:(A,C,FFI)wl_state)) (wl_state_stack_size st)`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `fc:((A)word_loc)list#(A)wl_prog#(num)option` ASSUME_TAC)) THENL
   [srcerr []; ALL_TAC] THEN
  SUBGOAL_THEN `?args1 prog ss. fc = (args1:((A)word_loc)list,prog:(A)wl_prog,ss:(num)option)`
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_CASES_TAC `domain (p0:num_set) = {} \/ ~ALL_DISTINCT (n:num list)` THENL
   [srcerr []; ALL_TAC] THEN
  MP_TAC(ISPEC `cut_envs (p0:num_set,p1:num_set) (wl_state_locals (st:(A,C,FFI)wl_state))`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `xx:((A)word_loc)spt#((A)word_loc)spt` ASSUME_TAC)) THENL
   [srcerr []; ALL_TAC] THEN
  SUBGOAL_THEN `?x1 x2. xx = (x1:((A)word_loc)spt,x2:((A)word_loc)spt)`
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  WALLOCPAUX_EAC_GETVARS_TAC THEN
  MP_TAC(ISPECL [`f:num->num`; `p0:num_set`; `p1:num_set`;
                 `wl_state_locals (st:(A,C,FFI)wl_state)`; `x1:((A)word_loc)spt`;
                 `x2:((A)word_loc)spt`; `wl_state_locals (cst:(A,C,FFI)wl_state)`]
                cut_envs_lemma) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (WALLOCPAUX_INJ_SUB_TAC ORELSE WALLOCPAUX_SLR_SUB_TAC);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:((A)word_loc)spt` (X_CHOOSE_THEN `y2:((A)word_loc)spt`
    STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP (f:num->num) n)` ASSUME_TAC THENL
   [MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `INJ (f:num->num) (domain (word_alloc_numset_list_insert n (union p1 p0)))
                   (:num)` THEN
    REWRITE_TAC[word_allocProof_domain_numset_list_insert; INJ; IN_UNION; IN_SET_OF_LIST;
                IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(domain (apply_nummap_key (f:num->num) (p0:num_set)) = {})` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[apply_nummap_key_domain; IMAGE_EQ_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[apply_colour_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[option_CASE; pair_CASE] THEN
  (fun (asl,w as g) ->
     let t = find_term (fun t -> try let c,a = strip_comb t in
                                   fst(dest_const c) = "wl_Call" && length a = 4 &&
                                   free_in `f:num->num` t
                                 with Failure _ -> false) w in
     let hh = last(snd(strip_comb t)) in
     ABBREV_TAC (mk_eq(mk_var("hh",type_of hh), hh)) g) THEN
  SUBGOAL_THEN
   `match (h:(num#(A)wl_prog#num#num)option) with
      NONE -> hh = NONE
    | SOME (w,hp,l1,l2) ->
        (match (hh:(num#(A)wl_prog#num#num)option) with
           NONE -> F
         | SOME (a,b,c,d) -> c = l1 /\ d = l2)` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `hh:(num#(A)wl_prog#num#num)option`)) THEN
    SPEC_TAC(`h:(num#(A)wl_prog#num#num)option`, `h:(num#(A)wl_prog#num#num)option`) THEN
    REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; option_CASE; pair_CASE; option_DISTINCT;
                option_INJ];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
  ASM_REWRITE_TAC[add_ret_loc_def; option_CASE; pair_CASE; bad_dest_args_def; MAP_EQ_NIL;
                  nummaps_to_nummap] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bad_dest_args_def]) THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  let push_tac s0 c0 tp =
    MP_TAC(ISPECL [s0; c0; `x2:((A)word_loc)spt`; `y2:((A)word_loc)spt`;
                   `x1:((A)word_loc)spt`; `y1:((A)word_loc)spt`; `f:num->num`;
                   `h:(num#(A)wl_prog#num#num)option`; `hh:(num#(A)wl_prog#num#num)option`;
                   tp] push_env_s_val_eq) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `hh:(num#(A)wl_prog#num#num)option`)) THEN
      SPEC_TAC(`h:(num#(A)wl_prog#num#num)option`, `h:(num#(A)wl_prog#num#num)option`) THEN
      REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; option_CASE; pair_CASE;
                  option_DISTINCT; option_INJ];
      ALL_TAC] in
  ASM_CASES_TAC `wl_state_clock (st:(A,C,FFI)wl_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [push_tac `st:(A,C,FFI)wl_state` `cst:(A,C,FFI)wl_state` `wl_state_permute (cst:(A,C,FFI)wl_state)` THEN
    DISCH_THEN(X_CHOOSE_THEN `P:num->num->num` (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `P:num->num->num` THEN
    REWRITE_TAC([pair_CASE; option_INJ; option_CASE; WALLOCPAUX_wl_result_CASE] @
                WALLOCPAUX_wl_result_distinct) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[word_state_eq_rel_def; wl_flush_state_def; wl_state_INFO.ri_accfupds;
                  K_THM] THEN
      ASM_REWRITE_TAC[wl_call_env_def; wl_state_INFO.ri_accfupds; K_THM;
                      push_env_stack_max_eq] THEN
      FIRST_ASSUM(fun th -> if (try fst(dest_const(fst(strip_comb(concl th)))) = "s_val_eq"
                                with Failure _ -> false)
                            then REWRITE_TAC[MATCH_MP s_val_eq_stack_size th] else NO_TAC);
      REWRITE_TAC[wl_flush_state_def; wl_state_INFO.ri_accfupds; K_THM]];
    ALL_TAC] THEN
  push_tac `wl_dec_clock (st:(A,C,FFI)wl_state)` `wl_dec_clock (cst:(A,C,FFI)wl_state)`
    `\n. wl_state_permute (cst:(A,C,FFI)wl_state) (n + 1)` THEN
  DISCH_THEN(X_CHOOSE_THEN `P:num->num->num` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  WALLOCPAUX_TUPLE_TAC
    `env_to_list (y2:((A)word_loc)spt) (wl_state_permute (wl_dec_clock (cst:(A,C,FFI)wl_state)))`
    [`lsA:(num#(A)word_loc)list`; `pA:num->num->num`] THEN
  WALLOCPAUX_TUPLE_TAC `env_to_list (x2:((A)word_loc)spt) P`
    [`lsB:(num#(A)word_loc)list`; `pB:num->num->num`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\n. (P:num->num->num) (n + 1)) =
                (\n. wl_state_permute (cst:(A,C,FFI)wl_state) (n + 1))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "env_to_list" &&
           rand(lhs(concl th)) = `P:num->num->num` with Failure _ -> false))) THEN
    REWRITE_TAC[env_to_list_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[WALLOCPAUX_call_env_permute] THEN
  WALLOCPAUX_EX_REFINE_TAC `\n. if n = 0 then (P:num->num->num) 0 else perm2 (n - 1)`
    `perm2:num->num->num` THEN
  REWRITE_TAC[WALLOCPAUX_push_env_perm; WALLOCPAUX_call_env_permute] THEN
  MP_TAC(ISPECL [`wl_dec_clock (st:(A,C,FFI)wl_state)`; `wl_dec_clock (cst:(A,C,FFI)wl_state)`;
                 `x1:((A)word_loc)spt`; `x2:((A)word_loc)spt`; `y1:((A)word_loc)spt`;
                 `y2:((A)word_loc)spt`; `h:(num#(A)wl_prog#num#num)option`;
                 `hh:(num#(A)wl_prog#num#num)option`; `P:num->num->num`;
                 `args1:((A)word_loc)list`; `ss:num option`] WALLOCPAUX_call_states) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    REWRITE_TAC[word_state_eq_rel_def; wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `hh:(num#(A)wl_prog#num#num)option`)) THEN
    SPEC_TAC(`h:(num#(A)wl_prog#num#num)option`, `h:(num#(A)wl_prog#num#num)option`) THEN
    REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; option_CASE; pair_CASE;
                option_DISTINCT; option_INJ];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `sc0 = wl_call_env args1 ss (wl_push_env (x1,x2) h
                     (wl_state_permute_fupd (K P) (wl_dec_clock (st:(A,C,FFI)wl_state))))` THEN
  ABBREV_TAC `tc0 = wl_call_env args1 ss (wl_push_env (y1,y2) hh
                     (wl_dec_clock (cst:(A,C,FFI)wl_state)))` THEN
  WALLOCPAUX_PERM_SWAP4_TAC `prog:(A)wl_prog` `sc0:(A,C,FFI)wl_state` THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE; option_CASE; WALLOCPAUX_wl_result_CASE];
    ALL_TAC] THEN
  SUBGOAL_THEN `s_val_eq (wl_state_stack (sc0:(A,C,FFI)wl_state))
                  (wl_state_stack (tc0:(A,C,FFI)wl_state))`
    ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["sc0"; "tc0"] THEN
    REWRITE_TAC[wl_call_env_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`; `sc0:(A,C,FFI)wl_state`] wl_evaluate_stack_swap) THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (prog:(A)wl_prog,sc0:(A,C,FFI)wl_state)`
    [`r1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE; PAIR_MAP_THM; I_THM] THEN
  WALLOCPAUX_RESULT_CASES_TAC `r1:((A)wl_result)option` THEN
  let stop =
    STRIP_TAC THEN EXISTS_TAC `wl_state_permute (s1:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[WALLOCPAUX_with_same_permute] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `wl_state_stack (tc0:(A,C,FFI)wl_state)` o
                  check (is_forall o concl)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC([pair_CASE; option_CASE; WALLOCPAUX_wl_result_CASE; option_INJ;
                 WALLOCPAUX_wser_refl] @ WALLOCPAUX_wl_result_distinct) in
  let result =
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o SPEC `wl_state_stack (tc0:(A,C,FFI)wl_state)`))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `st3:((A)stack_frame)list` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[pair_CASE; option_CASE; WALLOCPAUX_wl_result_CASE] THEN
    ASM_CASES_TAC `~((a0:(A)word_loc) = wl_Loc l1 l2) \/
                   ~(LENGTH (a1:((A)word_loc)list) = LENGTH (n:num list))` THEN
    ASM_REWRITE_TAC[pair_CASE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
    REWRITE_TAC[wl_pop_env_with_const] THEN
    MP_TAC(ISPEC `wl_pop_env (s1:(A,C,FFI)wl_state)` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `s1p:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[OPTION_MAP_DEF; option_CASE; pair_CASE; WALLOCPAUX_wl_result_CASE] THEN
    let hoptS = CASE_TERM `match (h:(num#(A)wl_prog#num#num)option) with
                             NONE -> NONE
                           | SOME (w,hp,k1,k2) -> SOME (wl_state_handler (st:(A,C,FFI)wl_state),k1,k2)`
    and hoptT = CASE_TERM `match (hh:(num#(A)wl_prog#num#num)option) with
                             NONE -> NONE
                           | SOME (w,hp,k1,k2) -> SOME (wl_state_handler (cst:(A,C,FFI)wl_state),k1,k2)` in
    SUBGOAL_THEN (mk_eq(hoptT,hoptS)) ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `hh:(num#(A)wl_prog#num#num)option`)) THEN
      SPEC_TAC(`h:(num#(A)wl_prog#num#num)option`, `h:(num#(A)wl_prog#num#num)option`) THEN
      REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; option_CASE; pair_CASE];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM]) THEN
    SUBGOAL_THEN (mk_eq(`wl_state_stack (sc0:(A,C,FFI)wl_state)`,
       list_mk_icomb "CONS" [list_mk_icomb "StackFrame"
         [`wl_state_locals_size (st:(A,C,FFI)wl_state)`; `toAList (x1:((A)word_loc)spt)`;
          `lsB:(num#(A)word_loc)list`; hoptS]; `wl_state_stack (st:(A,C,FFI)wl_state)`]))
      ASSUME_TAC THENL
     [EXPAND_TAC "sc0" THEN
      REWRITE_TAC[wl_call_env_def; wl_state_INFO.ri_accfupds; K_THM;
                  WALLOCPAUX_push_env_stack_gen; wl_dec_clock_def] THEN
      ASM_REWRITE_TAC[FST];
      ALL_TAC] THEN
    SUBGOAL_THEN (mk_eq(`wl_state_stack (tc0:(A,C,FFI)wl_state)`,
       list_mk_icomb "CONS" [list_mk_icomb "StackFrame"
         [`wl_state_locals_size (st:(A,C,FFI)wl_state)`; `toAList (y1:((A)word_loc)spt)`;
          `lsA:(num#(A)word_loc)list`; hoptS]; `wl_state_stack (st:(A,C,FFI)wl_state)`]))
      ASSUME_TAC THENL
     [EXPAND_TAC "tc0" THEN
      REWRITE_TAC[wl_call_env_def; wl_state_INFO.ri_accfupds; K_THM;
                  WALLOCPAUX_push_env_stack_gen; wl_dec_clock_def] THEN
      ASM_REWRITE_TAC[FST];
      ALL_TAC] THEN
    (fun (asl,w as g) ->
       let abbr v = concl(snd(find (fun (_,th) -> is_eq(concl th) && rhs(concl th) = v) asl)) in
       let push_s = rand(lhs(abbr `sc0:(A,C,FFI)wl_state`))
       and push_t = rand(lhs(abbr `tc0:(A,C,FFI)wl_state`)) in
       let ins t = rand t and bs t = rand(rator t) in
       (MP_TAC(ISPECL [`(x1:((A)word_loc)spt,x2:((A)word_loc)spt)`; bs push_s; ins push_s;
                       `s1:(A,C,FFI)wl_state`] push_env_pop_env_s_key_eq) THEN
        ANTS_TAC THENL
         [UNDISCH_TAC `s_key_eq (wl_state_stack (sc0:(A,C,FFI)wl_state))
                         (wl_state_stack (s1:(A,C,FFI)wl_state))` THEN
          EXPAND_TAC "sc0" THEN REWRITE_TAC[wl_call_env_def; wl_state_INFO.ri_accfupds; K_THM];
          ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `n0:num option` (X_CHOOSE_THEN `l0:(num#(A)word_loc)list`
          (X_CHOOSE_THEN `ls0:((A)stack_frame)list` (X_CHOOSE_THEN `o0:(num#num#num)option`
          (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `y0:(A,C,FFI)wl_state` STRIP_ASSUME_TAC)))))) THEN
        MP_TAC(ISPECL [`(y1:((A)word_loc)spt,y2:((A)word_loc)spt)`; bs push_t; ins push_t;
                       `wl_state_stack_fupd (K st3) (s1:(A,C,FFI)wl_state)`]
                      push_env_pop_env_s_key_eq) THEN
        ANTS_TAC THENL
         [UNDISCH_TAC `s_key_eq (wl_state_stack (tc0:(A,C,FFI)wl_state)) st3` THEN
          EXPAND_TAC "tc0" THEN REWRITE_TAC[wl_call_env_def; wl_state_INFO.ri_accfupds; K_THM];
          ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `n1:num option` (X_CHOOSE_THEN `l1':(num#(A)word_loc)list`
          (X_CHOOSE_THEN `ls1:((A)stack_frame)list` (X_CHOOSE_THEN `o1:(num#num#num)option`
          (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `t1p:(A,C,FFI)wl_state` STRIP_ASSUME_TAC))))))) g) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      concl th = `wl_pop_env (s1:(A,C,FFI)wl_state) = SOME y0`)) THEN
    ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
    MP_TAC(ISPECL [`f:num->num`; `x1:((A)word_loc)spt`; `y1:((A)word_loc)spt`;
                   `lsB:(num#(A)word_loc)list`; `lsA:(num#(A)word_loc)list`;
                   `s1:(A,C,FFI)wl_state`; `wl_state_stack_fupd (K st3) (s1:(A,C,FFI)wl_state)`;
                   `s1p:(A,C,FFI)wl_state`; `t1p:(A,C,FFI)wl_state`;
                   `wl_state_locals_size (st:(A,C,FFI)wl_state)`; hoptS;
                   `wl_state_stack (st:(A,C,FFI)wl_state)`;
                   `wl_state_stack (st:(A,C,FFI)wl_state)`] WALLOCPAUX_pop_env_rel) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC key_map_implies THEN FIRST_ASSUM ACCEPT_TAC;
        MP_TAC(ISPECL [`x2:((A)word_loc)spt`; `P:num->num->num`] env_to_list_keys) THEN
        ASM_REWRITE_TAC[pair_CASE] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
        WALLOCPAUX_INJ_SUB_TAC;
        ONCE_REWRITE_TAC[s_key_eq_sym] THEN
        UNDISCH_TAC `s_key_eq (wl_state_stack (sc0:(A,C,FFI)wl_state))
                       (wl_state_stack (s1:(A,C,FFI)wl_state))` THEN ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[s_key_eq_sym] THEN
        UNDISCH_TAC `s_key_eq (wl_state_stack (tc0:(A,C,FFI)wl_state)) st3` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `domain (wl_state_locals (s1p:(A,C,FFI)wl_state)) =
                  domain (p0:num_set) UNION domain (p1:num_set) /\
                  domain (wl_state_locals (t1p:(A,C,FFI)wl_state)) =
                  IMAGE (f:num->num) (domain p0) UNION IMAGE f (domain p1)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `domain (x2:((A)word_loc)spt) UNION domain (x1:((A)word_loc)spt) =
                     domain (wl_state_locals (s1p:(A,C,FFI)wl_state))`;
        UNDISCH_TAC `domain (y2:((A)word_loc)spt) UNION domain (y1:((A)word_loc)spt) =
                     domain (wl_state_locals (t1p:(A,C,FFI)wl_state))`] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `wl_state_stack (t1p:(A,C,FFI)wl_state) = wl_state_stack (s1p:(A,C,FFI)wl_state)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC s_val_and_key_eq THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[s_val_eq_sym] THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC s_key_eq_trans THEN
        EXISTS_TAC `wl_state_stack (st:(A,C,FFI)wl_state)` THEN CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC; ONCE_REWRITE_TAC[s_key_eq_sym] THEN FIRST_ASSUM ACCEPT_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `wl_state_handler (t1p:(A,C,FFI)wl_state) =
                  wl_state_handler (s1p:(A,C,FFI)wl_state)`
      ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th ->
        try fst(dest_const(fst(strip_comb(concl th)))) = "option_CASE" &&
            free_in `t1p:(A,C,FFI)wl_state` (concl th) with Failure _ -> false)) THEN
      SPEC_TAC(`h:(num#(A)wl_prog#num#num)option`, `h:(num#(A)wl_prog#num#num)option`) THEN
      REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; option_CASE; pair_CASE;
                  wl_state_INFO.ri_accfupds; K_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY (fun t ->
      FIRST_ASSUM(fun th -> if concl th = t then STRIP_ASSUME_TAC(MATCH_MP wl_pop_env_const th)
                            else NO_TAC))
      [`wl_pop_env (s1:(A,C,FFI)wl_state) = SOME s1p`;
       `wl_pop_env (wl_state_stack_fupd (K st3) (s1:(A,C,FFI)wl_state)) = SOME t1p`] THEN
    SUBGOAL_THEN `word_state_eq_rel (s1p:(A,C,FFI)wl_state) (t1p:(A,C,FFI)wl_state)`
      ASSUME_TAC THENL
     [REWRITE_TAC[word_state_eq_rel_def] THEN
      ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM];
      ALL_TAC] THEN
    REMOVE_THEN "ihr" (MP_TAC o SPEC `wl_set_vars (n:num list) a1 (s1p:(A,C,FFI)wl_state)`) THEN
    REWRITE_TAC[WALLOCPAUX_eac_Q_def] THEN
    DISCH_THEN(MP_TAC o SPECL [`wl_set_vars (MAP (f:num->num) n) a1 (t1p:(A,C,FFI)wl_state)`;
      `f:num->num`; `live:num_set`; `lt:(num_set#num_set)list`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[wl_set_vars_def] THEN MATCH_MP_TAC WALLOCPAUX_wser_locals THEN
        FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC strong_locals_rel_set_vars_dom THEN
        EXISTS_TAC `domain (word_alloc_numset_list_insert (n:num list) (union p1 (p0:num_set)))` THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          FIRST_ASSUM ACCEPT_TAC;
          FIRST_ASSUM(fun th -> if is_eq(concl th) &&
              lhs(concl th) = `domain (wl_state_locals (s1p:(A,C,FFI)wl_state))`
              then REWRITE_TAC[th] else NO_TAC) THEN
          REWRITE_TAC[word_allocProof_domain_numset_list_insert; domain_union] THEN SET_TAC[];
          REWRITE_TAC[word_allocProof_domain_numset_list_insert; domain_union] THEN SET_TAC[];
          MATCH_MP_TAC strong_locals_rel_subset THEN EXISTS_TAC `(:num)` THEN
          REWRITE_TAC[SUBSET_UNIV] THEN FIRST_ASSUM ACCEPT_TAC]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `perm3:num->num->num` ASSUME_TAC) THEN
    EXISTS_TAC `perm3:num->num->num` THEN
    REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; wl_set_vars_with_const; option_CASE] THEN
    ASM_REWRITE_TAC[] in
  let hhabbrev th = is_eq(concl th) && rhs(concl th) = `hh:(num#(A)wl_prog#num#num)option` in
  let exc_none =
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check hhabbrev) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_CASE; pair_CASE]) THEN REWRITE_TAC[option_CASE; pair_CASE] THEN
    SUBGOAL_THEN
     `wl_state_handler (sc0:(A,C,FFI)wl_state) = wl_state_handler (st:(A,C,FFI)wl_state) /\
      wl_state_stack sc0 = CONS (StackFrame (wl_state_locals_size st) (toAList x1) lsB NONE)
                             (wl_state_stack st) /\
      wl_state_stack (tc0:(A,C,FFI)wl_state) =
        CONS (StackFrame (wl_state_locals_size st) (toAList y1) lsA NONE) (wl_state_stack st)`
      STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["sc0"; "tc0"] THEN
      REWRITE_TAC[wl_call_env_def; wl_state_INFO.ri_accfupds; K_THM;
                  WALLOCPAUX_push_env_stack_gen; WALLOCPAUX_push_env_permute_handler;
                  wl_dec_clock_def; option_CASE] THEN
      ASM_REWRITE_TAC[FST];
      ALL_TAC] THEN
    SUBGOAL_THEN `wl_state_handler (st:(A,C,FFI)wl_state) < LENGTH (wl_state_stack st)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `a < b + 1 /\ ~(a = b) ==> a < b`) THEN CONJ_TAC THENL
       [UNDISCH_TAC `wl_state_handler (sc0:(A,C,FFI)wl_state) < LENGTH (wl_state_stack sc0)` THEN
        ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        DISCH_TAC THEN
        UNDISCH_TAC `LASTN (wl_state_handler (sc0:(A,C,FFI)wl_state) + 1) (wl_state_stack sc0) =
                     CONS (StackFrame m e0 e (SOME nh)) ls` THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `LENGTH (wl_state_stack (st:(A,C,FFI)wl_state)) + 1 =
                      LENGTH (CONS (StackFrame (wl_state_locals_size st) (toAList x1) lsB NONE)
                                   (wl_state_stack st))` SUBST1_TAC THENL
         [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC([LASTN_LENGTH_ID; CONS_11; option_DISTINCT] @ WALLOCPAUX_stack_frame_inject)];
      ALL_TAC] THEN
    SUBGOAL_THEN `LASTN (wl_state_handler (st:(A,C,FFI)wl_state) + 1) (wl_state_stack st) =
                  CONS (StackFrame m e0 e (SOME nh)) ls` ASSUME_TAC THENL
     [UNDISCH_TAC `LASTN (wl_state_handler (sc0:(A,C,FFI)wl_state) + 1) (wl_state_stack sc0) =
                   CONS (StackFrame m e0 e (SOME nh)) ls` THEN
      ASM_SIMP_TAC[LASTN_TL];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`wl_state_stack (tc0:(A,C,FFI)wl_state)`;
      `e0:(num#(A)word_loc)list`; `e:(num#(A)word_loc)list`; `ls:((A)stack_frame)list`] o
      check (fun th -> is_forall(concl th) && free_in `e0:(num#(A)word_loc)list` (concl th) = false &&
                       length(fst(strip_forall(concl th))) = 4)) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[LASTN_TL]; FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `st4:((A)stack_frame)list` (X_CHOOSE_THEN `locs:((A)word_loc)spt`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `lss2:(num#(A)word_loc)list` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `lss2 = (lss:(num#(A)word_loc)list)` SUBST_ALL_TAC THENL
     [ONCE_REWRITE_TAC[GSYM ZIP_MAP_FST_SND_EQ] THEN
      UNDISCH_TAC `MAP SND (lss:(num#(A)word_loc)list) = MAP SND (lss2:(num#(A)word_loc)list)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `MAP FST (e:(num#(A)word_loc)list) = MAP FST (lss2:(num#(A)word_loc)list)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `st4 = wl_state_stack (s1:(A,C,FFI)wl_state)` SUBST_ALL_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC s_val_and_key_eq THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC s_key_eq_trans THEN EXISTS_TAC `ls:((A)stack_frame)list` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `wl_state_permute (s1:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[WALLOCPAUX_with_same_permute] THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
        (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_evaluate" with Failure _ -> false) &&
        free_in `tc0:(A,C,FFI)wl_state` (lhs(concl th))
      then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[pair_CASE; option_CASE; WALLOCPAUX_wl_result_CASE] THEN
    SUBGOAL_THEN `wl_state_stack_fupd (K (wl_state_stack s1))
                    (wl_state_handler_fupd (K (wl_state_handler s1))
                       (wl_state_locals_fupd (K (wl_state_locals s1)) s1)) = (s1:(A,C,FFI)wl_state)`
      ASSUME_TAC THENL
     [REWRITE_TAC[wl_state_component_equality] THEN SIMP[]; ALL_TAC] THEN
    ASM_REWRITE_TAC([option_INJ] @ WALLOCPAUX_wl_result_distinct) THEN CONJ_TAC THENL
     [REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM]] in
  let exc_some =
    SUBGOAL_THEN `?n' hp k1 k2. hq = (n':num,hp:(A)wl_prog,k1:num,k2:num)`
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check hhabbrev) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_CASE; pair_CASE]) THEN REWRITE_TAC[option_CASE; pair_CASE] THEN
    SUBGOAL_THEN
     `wl_state_handler (sc0:(A,C,FFI)wl_state) = LENGTH (wl_state_stack (st:(A,C,FFI)wl_state)) /\
      wl_state_stack sc0 =
        CONS (StackFrame (wl_state_locals_size st) (toAList x1) lsB
                (SOME (wl_state_handler st,k1,k2))) (wl_state_stack st) /\
      wl_state_stack (tc0:(A,C,FFI)wl_state) =
        CONS (StackFrame (wl_state_locals_size st) (toAList y1) lsA
                (SOME (wl_state_handler st,k1,k2))) (wl_state_stack st)`
      STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["sc0"; "tc0"] THEN
      REWRITE_TAC[wl_call_env_def; wl_state_INFO.ri_accfupds; K_THM;
                  WALLOCPAUX_push_env_stack_gen; WALLOCPAUX_push_env_permute_handler;
                  wl_dec_clock_def; option_CASE; pair_CASE] THEN
      ASM_REWRITE_TAC[FST];
      ALL_TAC] THEN
    let lastn_whole fr =
      SUBGOAL_THEN (mk_eq(`LENGTH (wl_state_stack (st:(A,C,FFI)wl_state)) + 1`,
                          mk_comb(`LENGTH:((A)stack_frame)list->num`,
                                  list_mk_icomb "CONS" [fr; `wl_state_stack (st:(A,C,FFI)wl_state)`])))
        SUBST1_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[LASTN_LENGTH_ID] in
    UNDISCH_TAC `LASTN (wl_state_handler (sc0:(A,C,FFI)wl_state) + 1) (wl_state_stack sc0) =
                 CONS (StackFrame m e0 e (SOME nh)) ls` THEN
    ASM_REWRITE_TAC[] THEN
    lastn_whole `StackFrame (wl_state_locals_size (st:(A,C,FFI)wl_state)) (toAList (x1:((A)word_loc)spt)) lsB
                   (SOME (wl_state_handler st,k1,k2))` THEN
    REWRITE_TAC([CONS_11; option_INJ] @ WALLOCPAUX_stack_frame_inject) THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
      is_var(rhs(concl th)) &&
      mem (fst(dest_var(rhs(concl th)))) ["m"; "e0"; "e"; "nh"; "ls"]))) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `m:num option`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pair_CASE]) THEN REWRITE_TAC[pair_CASE] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`wl_state_stack (tc0:(A,C,FFI)wl_state)`;
      `toAList (y1:((A)word_loc)spt)`; `lsA:(num#(A)word_loc)list`;
      `wl_state_stack (st:(A,C,FFI)wl_state)`] o
      check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 4)) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        lastn_whole `StackFrame (wl_state_locals_size (s1:(A,C,FFI)wl_state))
                       (toAList (y1:((A)word_loc)spt)) lsA
                       (SOME (wl_state_handler (st:(A,C,FFI)wl_state),k1,k2))`;
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `st4:((A)stack_frame)list` (X_CHOOSE_THEN `locs:((A)word_loc)spt`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `lss2:(num#(A)word_loc)list` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `st4 = wl_state_stack (s1:(A,C,FFI)wl_state)` SUBST_ALL_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC s_val_and_key_eq THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC s_key_eq_trans THEN EXISTS_TAC `wl_state_stack (st:(A,C,FFI)wl_state)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `locs:((A)word_loc)spt`)) THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
        (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_evaluate" with Failure _ -> false) &&
        free_in `tc0:(A,C,FFI)wl_state` (lhs(concl th))
      then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[pair_CASE; option_CASE; WALLOCPAUX_wl_result_CASE] THEN
    ASM_CASES_TAC `(a0:(A)word_loc) = wl_Loc k1 k2` THEN ASM_REWRITE_TAC[pair_CASE] THEN
    SUBGOAL_THEN `domain (union (fromAList lss) (fromAList (toAList (x1:((A)word_loc)spt)))) =
                  domain (p0:num_set) UNION domain (p1:num_set) /\
                  domain (union (fromAList lss2) (fromAList (toAList (y1:((A)word_loc)spt)))) =
                  IMAGE (f:num->num) (domain p0) UNION IMAGE f (domain p1)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      ASM_REWRITE_TAC[domain_union; domain_fromAList; set_MAP_FST_toAList_domain] THENL
       [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `MAP FST (lsB:(num#(A)word_loc)list) = MAP FST (lss:(num#(A)word_loc)list)`)) THEN
        MP_TAC(ISPECL [`x2:((A)word_loc)spt`; `P:num->num->num`] env_to_list_keys);
        FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `MAP FST (lsA:(num#(A)word_loc)list) = MAP FST (lss2:(num#(A)word_loc)list)`)) THEN
        MP_TAC(ISPECL [`y2:((A)word_loc)spt`; `wl_state_permute (cst:(A,C,FFI)wl_state)`]
                      env_to_list_keys)] THEN
      ASM_REWRITE_TAC[pair_CASE] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `strong_locals_rel (f:num->num) (:num) (wl_state_locals (s1:(A,C,FFI)wl_state))
                    (union (fromAList lss2) (fromAList (toAList (y1:((A)word_loc)spt))))`
      ASSUME_TAC THENL
     [UNDISCH_TAC `wl_state_locals (s1:(A,C,FFI)wl_state) =
                   union (fromAList lss) (fromAList (toAList (x1:((A)word_loc)spt)))` THEN
      DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC WALLOCPAUX_union_alist_slr THEN
      EXISTS_TAC `lsB:(num#(A)word_loc)list` THEN EXISTS_TAC `lsA:(num#(A)word_loc)list` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC key_map_implies THEN FIRST_ASSUM ACCEPT_TAC;
        MP_TAC(ISPECL [`x2:((A)word_loc)spt`; `P:num->num->num`] env_to_list_keys) THEN
        ASM_REWRITE_TAC[pair_CASE] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
        WALLOCPAUX_INJ_SUB_TAC;
        UNDISCH_TAC `domain (x1:((A)word_loc)spt) = domain (p0:num_set)` THEN
        DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
        CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
    SUBGOAL_THEN `!p. wl_set_var n' (a1:(A)word_loc) (wl_state_permute_fupd (K p) (s1:(A,C,FFI)wl_state)) =
                      wl_state_permute_fupd (K p) (wl_set_var n' a1 s1)`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[wl_set_var_with_const]; ALL_TAC] THEN
    (fun (asl,w as g) ->
       let tm = find_term (fun t -> is_comb t &&
                  (try fst(dest_const(rator t)) = "wl_evaluate" with Failure _ -> false) &&
                  (try fst(dest_pair(rand t)) = `apply_colour (f:num->num) (hp:(A)wl_prog)`
                   with Failure _ -> false)) w in
       let cstT = snd(dest_pair(rand tm)) in
       (REMOVE_THEN "ihh" (MP_TAC o SPEC `wl_set_var n' (a1:(A)word_loc) (s1:(A,C,FFI)wl_state)`) THEN
        REWRITE_TAC[WALLOCPAUX_eac_Q_def] THEN
        DISCH_THEN(MP_TAC o SPECL [cstT; `f:num->num`; `live:num_set`;
                                   `lt:(num_set#num_set)list`])) g) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[wl_set_var_def] THEN MATCH_MP_TAC WALLOCPAUX_wser_locals THEN
        REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC strong_locals_rel_set_var_dom THEN
        EXISTS_TAC `domain (insert n' one (union p1 (p0:num_set)))` THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[domain_insert; domain_union] THEN SET_TAC[];
          REWRITE_TAC[domain_insert; IN_INSERT];
          MATCH_MP_TAC strong_locals_rel_subset THEN EXISTS_TAC `(:num)` THEN
          REWRITE_TAC[SUBSET_UNIV; wl_state_INFO.ri_accfupds; K_THM] THEN FIRST_ASSUM ACCEPT_TAC]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `perm3:num->num->num` MP_TAC) THEN
    DISCH_THEN(fun th -> EXISTS_TAC `perm3:num->num->num` THEN MP_TAC th) THEN
    REWRITE_TAC[] THEN DISCH_THEN ACCEPT_TAC in
  let exc =
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `e0:(num#(A)word_loc)list` (X_CHOOSE_THEN `e:(num#(A)word_loc)list`
       (X_CHOOSE_THEN `nh:num#num#num` (X_CHOOSE_THEN `ls:((A)stack_frame)list`
        (X_CHOOSE_THEN `m:num option` (X_CHOOSE_THEN `lss:(num#(A)word_loc)list`
          STRIP_ASSUME_TAC))))))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM]) THEN
    MP_TAC(ISPEC `h:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `hq:num#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
     [exc_none; exc_some] in
  FIRST [stop THEN NO_TAC; result THEN NO_TAC; exc]);;

let WALLOCPAUX_eac_Call = prove
 (`!a0 a1 a2 a3.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Call a0 a1 a2 a3:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_Call a0 a1 a2 a3:(A)wl_prog)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `a0:(num list#(num_set#num_set)#(A)wl_prog#num#num)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `q0:num list#(num_set#num_set)#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
   [DISCH_TAC THEN REWRITE_TAC[WALLOCPAUX_eac_Call_tail]; ALL_TAC] THEN
  SUBGOAL_THEN `?n names rh l1 l2. q0 = (n:num list,names:num_set#num_set,rh:(A)wl_prog,l1:num,l2:num)`
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  MP_TAC(ISPEC `a3:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `hq:num#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
   [ALL_TAC;
    SUBGOAL_THEN `?v hp k1 k2. hq = (v:num,hp:(A)wl_prog,k1:num,k2:num)`
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC]] THEN
  DISCH_TAC THEN MATCH_MP_TAC WALLOCPAUX_eac_Call_ret THEN
  REWRITE_TAC[option_CASE; pair_CASE] THEN REPEAT CONJ_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN WALLOCPAUX_SIZE_TAC);;

let WALLOCPAUX_eac_Seq = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Seq a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_Seq a0 a1:(A)wl_prog)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_eac_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  WALLOCPAUX_EAC_EXPAND_TAC THEN
  USE_THEN "ih" (MP_TAC o SPEC `a0:(A)wl_prog`) THEN
  ANTS_TAC THENL [WALLOCPAUX_SIZE_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `st:(A,C,FFI)wl_state`) THEN REWRITE_TAC[WALLOCPAUX_eac_Q_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`cst:(A,C,FFI)wl_state`; `f:num->num`;
    `get_live (a1:(A)wl_prog) live lt`; `lt:(num_set#num_set)list`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[word_state_eq_rel_def]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm1:num->num->num` MP_TAC) THEN
  WALLOCPAUX_NAME_EVAL_TAC `a0:(A)wl_prog`
    [`r1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] THEN
  WALLOCPAUX_NAME_EVAL_TAC `apply_colour f (a0:(A)wl_prog)`
    [`r2:((A)wl_result)option`; `s2:(A,C,FFI)wl_state`] THEN
  ASM_CASES_TAC `r1 = SOME (wl_Error:(A)wl_result)` THENL
   [DISCH_TAC THEN EXISTS_TAC `perm1:num->num->num` THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `r1:((A)wl_result)option`)) THEN
    ASSUM_LIST(fun ths -> REWRITE_TAC (mapfilter (MATCH_MP WALLOCPAUX_seq_SOME) ths)) THEN
    REWRITE_TAC[pair_CASE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `r1:((A)wl_result)option = NONE` THENL
   [ALL_TAC;
    SUBGOAL_THEN `?x:(A)wl_result. r1 = SOME x` (X_CHOOSE_THEN `x:(A)wl_result` SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[cases "option"]; ALL_TAC] THEN
    EXISTS_TAC `perm1:num->num->num` THEN REWRITE_TAC[apply_colour_def] THEN
    ASSUM_LIST(fun ths -> REWRITE_TAC (mapfilter (MATCH_MP WALLOCPAUX_seq_SOME) ths)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_CASE; option_INJ]) THEN
    ASM_REWRITE_TAC[pair_CASE; option_CASE; option_INJ]] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `r1:((A)wl_result)option`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_CASE]) THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `a1:(A)wl_prog`) THEN
  ANTS_TAC THENL [WALLOCPAUX_SIZE_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s1:(A,C,FFI)wl_state`) THEN REWRITE_TAC[WALLOCPAUX_eac_Q_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`s2:(A,C,FFI)wl_state`; `f:num->num`; `live:num_set`;
                             `lt:(num_set#num_set)list`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm2:num->num->num` (LABEL_TAC "ih2")) THEN
  MP_TAC(ISPECL [`a0:(A)wl_prog`; `wl_state_permute_fupd (K perm1) (st:(A,C,FFI)wl_state)`;
                 `perm2:num->num->num`] permute_swap_lemma) THEN
  ASM_REWRITE_TAC[pair_CASE; option_DISTINCT; wl_state_INFO.ri_fupdfupds; K_o_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `perm3:num->num->num`) THEN
  EXISTS_TAC `perm3:num->num->num` THEN REWRITE_TAC[apply_colour_def] THEN
  ASSUM_LIST(fun ths -> REWRITE_TAC (mapfilter (MATCH_MP WALLOCPAUX_seq_NONE) ths)) THEN
  USE_THEN "ih2" ACCEPT_TAC);;

let WALLOCPAUX_eac_If = prove
 (`!a0 a1 a2 a3 a4.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_If a0 a1 a2 a3 a4:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_If a0 a1 a2 a3 a4:(A)wl_prog)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `a2:(A)reg_imm` (cases "reg_imm")) THEN
  DISCH_THEN(LABEL_TAC "ih") THEN GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_eac_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  WALLOCPAUX_EAC_EXPAND_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[WALLOCPAUX_reg_imm_CASE]) THEN
  WALLOCPAUX_EAC_IF_TAC);;

let WALLOCPAUX_eac_Loop = prove
 (`!a0 a1 a2.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Loop a0 a1 a2:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_Loop a0 a1 a2:(A)wl_prog)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_eac_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[TAUT `(if b then T else q) <=> b \/ q`] THEN
  MATCH_MP_TAC evaluate_apply_colour_Loop_helper THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`st1:(A,C,FFI)wl_state`; `cst1:(A,C,FFI)wl_state`; `f1:num->num`;
                       `live1:num_set`; `lt1:(num_set#num_set)list`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `a1:(A)wl_prog`) THEN
  ANTS_TAC THENL [WALLOCPAUX_SIZE_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `st1:(A,C,FFI)wl_state`) THEN REWRITE_TAC[WALLOCPAUX_eac_Q_def] THEN
  REWRITE_TAC[TAUT `(if b then T else q) <=> b \/ q`] THEN
  DISCH_THEN(MP_TAC o SPECL [`cst1:(A,C,FFI)wl_state`; `f1:num->num`; `live1:num_set`;
                             `lt1:(num_set#num_set)list`]) THEN
  ASM_REWRITE_TAC[]);;

let WALLOCPAUX_eac_Alloc = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Alloc a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_Alloc a0 a1:(A)wl_prog)`,
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_eac_Q_def] THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?p0 p1. a1 = (p0:num_set,p1:num_set)`
    (X_CHOOSE_THEN `p0:num_set` (X_CHOOSE_THEN `p1:num_set` SUBST_ALL_TAC)) THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  STRIP_TAC THEN WALLOCPAUX_EAC_EXPAND_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
  MP_TAC(ISPEC `wl_get_var a0 (st:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v:(A)word_loc` ASSUME_TAC)) THENL
   [WALLOCPAUX_EAC_SRCERR_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `v:(A)word_loc` (cases "word_loc")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `w:(A)word` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `l2:num` SUBST_ALL_TAC))) THENL
   [ALL_TAC; WALLOCPAUX_EAC_SRCERR_TAC] THEN
  WALLOCPAUX_EAC_GETVAR_TAC THEN
  MP_TAC(ISPEC `cut_envs (p0:num_set,p1:num_set) (wl_state_locals (st:(A,C,FFI)wl_state))`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `xx:((A)word_loc)spt#((A)word_loc)spt` ASSUME_TAC)) THENL
   [EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[WALLOCPAUX_with_same_permute] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_word_loc_CASE; wl_alloc_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x1 x2. xx = (x1:((A)word_loc)spt,x2:((A)word_loc)spt)`
    (X_CHOOSE_THEN `x1:((A)word_loc)spt` (X_CHOOSE_THEN `x2:((A)word_loc)spt`
      SUBST_ALL_TAC)) THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:num->num`; `p0:num_set`; `p1:num_set`;
                 `wl_state_locals (st:(A,C,FFI)wl_state)`; `x1:((A)word_loc)spt`;
                 `x2:((A)word_loc)spt`; `wl_state_locals (cst:(A,C,FFI)wl_state)`]
                cut_envs_lemma) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (WALLOCPAUX_INJ_SUB_TAC ORELSE WALLOCPAUX_SLR_SUB_TAC);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:((A)word_loc)spt` (X_CHOOSE_THEN `y2:((A)word_loc)spt`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`wl_set_store AllocSize (wl_Word w) (st:(A,C,FFI)wl_state)`;
                 `wl_set_store AllocSize (wl_Word w) (cst:(A,C,FFI)wl_state)`;
                 `x2:((A)word_loc)spt`; `y2:((A)word_loc)spt`;
                 `x1:((A)word_loc)spt`; `y1:((A)word_loc)spt`; `f:num->num`;
                 `NONE:(num#(A)wl_prog#num#num)option`;
                 `NONE:(num#(A)wl_prog#num#num)option`;
                 `wl_state_permute (cst:(A,C,FFI)wl_state)`] push_env_s_val_eq) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[wl_set_store_def; wl_state_INFO.ri_accfupds; option_CASE] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm:num->num->num` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[wl_set_store_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  WALLOCPAUX_TUPLE_TAC
    `env_to_list (y2:((A)word_loc)spt) (wl_state_permute (cst:(A,C,FFI)wl_state))`
    [`lsA:(num#(A)word_loc)list`; `pA:num->num->num`] THEN
  WALLOCPAUX_TUPLE_TAC `env_to_list (x2:((A)word_loc)spt) perm`
    [`lsB:(num#(A)word_loc)list`; `pB:num->num->num`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `MAP (f:num->num) (MAP FST (lsB:(num#(A)word_loc)list)) =
                MAP FST (lsA:(num#(A)word_loc)list)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC key_map_implies THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `set_of_list (MAP FST (lsB:(num#(A)word_loc)list)) = domain (x2:((A)word_loc)spt)`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x2:((A)word_loc)spt`; `perm:num->num->num`] env_to_list_keys) THEN
    ASM_REWRITE_TAC[pair_CASE];
    ALL_TAC] THEN
  EXISTS_TAC `perm:num->num->num` THEN
  REWRITE_TAC[apply_colour_def] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[WALLOCPAUX_get_var_permute] THEN
  ASM_REWRITE_TAC[option_CASE; WALLOCPAUX_word_loc_CASE; wl_alloc_def] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  REWRITE_TAC[wl_set_store_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[wl_state_INFO.ri_fupdcanon] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_set_store_def; wl_state_INFO.ri_accfupds; K_THM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_state_INFO.ri_fupdcanon]) THEN
  WALLOCPAUX_NORM_EQ_TAC
    `wl_state_store (cst:(A,C,FFI)wl_state) = wl_state_store (st:(A,C,FFI)wl_state)` THEN
  (fun (asl,w as g) ->
     let gs = find_terms (fun t ->
         try fst(dest_const(rator t)) = "wl_gc" with Failure _ -> false) w in
     let sgc = find (fun t -> free_in `perm:num->num->num` t) gs in
     let tgc = find (fun t -> not (free_in `perm:num->num->num` t)) gs in
     (MP_TAC(ISPEC sgc (cases "option")) THEN
      DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `s2:(A,C,FFI)wl_state` ASSUME_TAC)) THENL
       [ASM_REWRITE_TAC[option_CASE; pair_CASE]; ALL_TAC] THEN
      MP_TAC(ISPECL [rand sgc; rand tgc; `s2:(A,C,FFI)wl_state`] gc_s_val_eq_gen) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[wl_push_env_const; push_env_stack_max_eq; wl_state_INFO.ri_accfupds;
                    K_THM] THEN
        REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        TRY(BINOP_TAC THENL
             [ASM_REWRITE_TAC[];
              MATCH_MP_TAC s_val_eq_stack_size THEN FIRST_ASSUM ACCEPT_TAC] THEN NO_TAC) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [rand sgc; `s2:(A,C,FFI)wl_state`] gc_s_key_eq) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN (mk_eq(list_mk_icomb "wl_stack_size" [mk_icomb(`wl_state_stack:(A,C,FFI)wl_state->((A)stack_frame)list`, rand tgc)],
                          list_mk_icomb "wl_stack_size" [mk_icomb(`wl_state_stack:(A,C,FFI)wl_state->((A)stack_frame)list`, rand sgc)]))
        ASSUME_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC s_val_eq_stack_size THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC]) g) THEN
  MP_TAC(ISPEC `wl_pop_env (s2:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `s3:(A,C,FFI)wl_state` ASSUME_TAC)) THENL
   [ASM_REWRITE_TAC[option_CASE; pair_CASE]; ALL_TAC] THEN
  SUBGOAL_THEN `s_key_eq (wl_state_stack (s2:(A,C,FFI)wl_state))
     (CONS (StackFrame (wl_state_locals_size (st:(A,C,FFI)wl_state))
             (toAList (x1:((A)word_loc)spt)) lsB NONE) (wl_state_stack st))` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[s_key_eq_sym] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `s_key_eq (wl_state_stack (wl_push_env (e:((A)word_loc)spt#((A)word_loc)spt) NONE
         (s:(A,C,FFI)wl_state))) (z:((A)stack_frame)list)`) (concl th) &&
      rand(concl th) = `wl_state_stack (s2:(A,C,FFI)wl_state)`)) THEN
    REWRITE_TAC[WALLOCPAUX_push_env_NONE_stack; wl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  SUBGOAL_THEN `s_key_eq (wl_state_stack (t2:(A,C,FFI)wl_state))
     (CONS (StackFrame (wl_state_locals_size (st:(A,C,FFI)wl_state))
             (toAList (y1:((A)word_loc)spt)) lsA NONE) (wl_state_stack st))`
    ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[s_key_eq_sym] THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> can (term_match []
      `s_key_eq (wl_state_stack (wl_push_env (e:((A)word_loc)spt#((A)word_loc)spt) NONE
         (s:(A,C,FFI)wl_state))) (z:((A)stack_frame)list)`) (concl th) &&
      rand(concl th) = `wl_state_stack (t2:(A,C,FFI)wl_state)`)) THEN
    REWRITE_TAC[WALLOCPAUX_push_env_NONE_stack; wl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if is_comb(concl th) && is_comb(rator(concl th)) &&
       rand(rator(concl th)) = `wl_state_stack (t2:(A,C,FFI)wl_state)` &&
       fst(dest_const(rator(rator(concl th)))) = "s_key_eq"
    then X_CHOOSE_TAC `t3:(A,C,FFI)wl_state` (MATCH_MP WALLOCPAUX_s_key_eq_pop_env_SOME th)
    else NO_TAC) THEN
  MP_TAC(ISPECL [`f:num->num`; `x1:((A)word_loc)spt`; `y1:((A)word_loc)spt`;
                 `lsB:(num#(A)word_loc)list`; `lsA:(num#(A)word_loc)list`;
                 `s2:(A,C,FFI)wl_state`; `t2:(A,C,FFI)wl_state`; `s3:(A,C,FFI)wl_state`;
                 `t3:(A,C,FFI)wl_state`; `wl_state_locals_size (st:(A,C,FFI)wl_state)`;
                 `NONE:(num#num#num)option`; `wl_state_stack (st:(A,C,FFI)wl_state)`;
                 `wl_state_stack (st:(A,C,FFI)wl_state)`] WALLOCPAUX_pop_env_rel) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN WALLOCPAUX_INJ_SUB_TAC; ALL_TAC] THEN
  REWRITE_TAC[option_CASE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wl_state_stack (t3:(A,C,FFI)wl_state) = wl_state_stack (s3:(A,C,FFI)wl_state)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC s_val_and_key_eq THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[s_val_eq_sym] THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC s_key_eq_trans THEN EXISTS_TAC `wl_state_stack (st:(A,C,FFI)wl_state)` THEN
      CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; ONCE_REWRITE_TAC[s_key_eq_sym] THEN FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `word_state_eq_rel (s3:(A,C,FFI)wl_state) t3` ASSUME_TAC THENL
   [MAP_EVERY (fun (a,b) ->
      FIRST_ASSUM(fun th -> if concl th = mk_eq(mk_comb(`wl_pop_env:(A,C,FFI)wl_state->((A,C,FFI)wl_state)option`, a),
                                                 mk_comb(`SOME:(A,C,FFI)wl_state->((A,C,FFI)wl_state)option`, b))
                            then STRIP_ASSUME_TAC(MATCH_MP wl_pop_env_const th) else NO_TAC))
      [`s2:(A,C,FFI)wl_state`,`s3:(A,C,FFI)wl_state`; `t2:(A,C,FFI)wl_state`,`t3:(A,C,FFI)wl_state`] THEN
    MAP_EVERY (fun b ->
      FIRST_ASSUM(fun th -> if is_eq(concl th) &&
                               rhs(concl th) = mk_comb(`SOME:(A,C,FFI)wl_state->((A,C,FFI)wl_state)option`, b) &&
                               (try fst(dest_const(rator(lhs(concl th)))) = "wl_gc" with Failure _ -> false)
                            then STRIP_ASSUME_TAC(MATCH_MP gc_frame th) else NO_TAC))
      [`s2:(A,C,FFI)wl_state`; `t2:(A,C,FFI)wl_state`] THEN
    REWRITE_TAC[word_state_eq_rel_def] THEN
    ASM_REWRITE_TAC[wl_push_env_const; push_env_stack_max_eq; wl_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s3:(A,C,FFI)wl_state`; `t3:(A,C,FFI)wl_state`] WALLOCPAUX_store_eq_get_has) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `word_state_eq_rel (s3:(A,C,FFI)wl_state) t3` THEN
    REWRITE_TAC[word_state_eq_rel_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  MP_TAC(ISPEC `wl_get_store AllocSize (s3:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `asz:(A)word_loc` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  MP_TAC(ISPEC `wl_has_space (asz:(A)word_loc) (s3:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `bb:bool` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC([pair_CASE; option_DISTINCT; option_INJ; option_CASE;
                   WALLOCPAUX_wl_result_CASE] @ WALLOCPAUX_wl_result_distinct) THENL
   [MATCH_MP_TAC strong_locals_rel_subset THEN EXISTS_TAC `(:num)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    CONJ_TAC THENL
     [MATCH_MP_TAC WALLOCPAUX_wser_flush THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[wl_flush_state_def; wl_state_INFO.ri_accfupds; K_THM]]]);;

let WALLOCPAUX_eac_StoreConsts = prove
 (`!a0 a1 a2 a3 a4.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_StoreConsts a0 a1 a2 a3 a4:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_StoreConsts a0 a1 a2 a3 a4:(A)wl_prog)`,
  WALLOCPAUX_EAC_OPENC_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; pair_case_eq; case_eq "word_loc"; COND_CASE_EQ; wl_set_var_def;
      wl_unset_var_def] THEN
  WALLOCPAUX_EAC_EXPAND_TAC THEN WALLOCPAUX_EAC_GETVAR_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_word_loc_CASE; wl_set_var_def;
                  wl_unset_var_def] THEN
  SIMP[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[word_state_eq_rel_def] THEN SIMP[] THEN ASM_REWRITE_TAC[];
    WALLOCPAUX_SLR_CHAIN_TAC]);;

let WALLOCPAUX_eac_Raise = prove
 (`!a0.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Raise a0:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_Raise a0:(A)wl_prog)`,
  WALLOCPAUX_EAC_OPENC_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; pair_case_eq; wl_jump_exc_def; COND_CASE_EQ; list_case_eq;
      case_eq "stack_frame"] THEN
  WALLOCPAUX_EAC_EXPAND_TAC THEN WALLOCPAUX_EAC_GETVAR_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; wl_jump_exc_def] THEN SIMP_NOASM[] THEN
  WALLOCPAUX_EAC_FINISH_TAC);;

let WALLOCPAUX_eac_Return = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Return a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_Return a0 a1:(A)wl_prog)`,
  WALLOCPAUX_EAC_OPENC_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; pair_case_eq; case_eq "word_loc"] THEN
  WALLOCPAUX_EAC_EXPAND_TAC THEN WALLOCPAUX_EAC_GETVAR_TAC THEN WALLOCPAUX_EAC_GETVARS_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_word_loc_CASE] THEN
  REWRITE_TAC[wl_flush_state_def] THEN SIMP[] THEN
  WALLOCPAUX_EAC_FINISH_TAC);;

let WALLOCPAUX_eac_Break = prove
 (`!a0.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Break a0:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_Break a0:(A)wl_prog)`,
  WALLOCPAUX_EAC_OPENC_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[] THEN WALLOCPAUX_EAC_EXPAND_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  CONJ_TAC THENL [WALLOCPAUX_EAC_FINISH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `oEL a0 (lt:(num_set#num_set)list)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `p:num_set#num_set`
    SUBST_ALL_TAC)) THEN
  REWRITE_TAC[option_CASE] THEN
  WALLOCPAUX_TUPLE_TAC `p:num_set#num_set` [`nm:num_set`; `en:num_set`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_CASE; pair_CASE]) THEN REWRITE_TAC[pair_CASE] THEN
  ASM_REWRITE_TAC[]);;

let WALLOCPAUX_eac_Continue = prove
 (`!a0.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Continue a0:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_Continue a0:(A)wl_prog)`,
  WALLOCPAUX_EAC_OPENC_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[] THEN WALLOCPAUX_EAC_EXPAND_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  CONJ_TAC THENL [WALLOCPAUX_EAC_FINISH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `oEL a0 (lt:(num_set#num_set)list)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `p:num_set#num_set`
    SUBST_ALL_TAC)) THEN
  REWRITE_TAC[option_CASE] THEN
  WALLOCPAUX_TUPLE_TAC `p:num_set#num_set` [`nm:num_set`; `en:num_set`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_CASE; pair_CASE]) THEN REWRITE_TAC[pair_CASE] THEN
  ASM_REWRITE_TAC[]);;

let WALLOCPAUX_eac_Tick = prove
 (`(!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Tick:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_Tick:(A)wl_prog)`,
  WALLOCPAUX_EAC_OPENC_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[COND_CASE_EQ; wl_flush_state_def; wl_dec_clock_def] THEN WALLOCPAUX_EAC_EXPAND_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; wl_flush_state_def; wl_dec_clock_def] THEN
  SIMP[WALLOCPAUX_wl_result_CASE] THEN
  WALLOCPAUX_EAC_FINISH_TAC);;

let WALLOCPAUX_eac_OpCurrHeap = prove
 (`!a0 a1 a2.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_OpCurrHeap a0 a1 a2:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_OpCurrHeap a0 a1 a2:(A)wl_prog)`,
  WALLOCPAUX_EAC_OPENC_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; wl_set_var_def] THEN WALLOCPAUX_EAC_EXPAND_TAC THEN
  SUBGOAL_THEN `wl_word_exp (cst:(A,C,FFI)wl_state)
                  (apply_colour_exp f (wl_Op a0 [wl_Var a2; Lookup CurrHeap])) = SOME a`
    (ASSUME_TAC o REWRITE_RULE[apply_colour_exp_def; MAP]) THENL
   [MATCH_MP_TAC apply_colour_exp_lemma THEN EXISTS_TAC `st:(A,C,FFI)wl_state` THEN
    ASM_REWRITE_TAC[word_state_eq_rel_def] THEN
    REWRITE_TAC[get_live_exp_def; big_union_def; ITLIST; MAP] THEN WALLOCPAUX_SLR_SUB_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  WALLOCPAUX_EAC_FINISH_TAC);;

let WALLOCPAUX_eac_LocValue = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_LocValue a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_LocValue a0 a1:(A)wl_prog)`,
  WALLOCPAUX_EAC_OPENC_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; wl_set_var_def; COND_CASE_EQ] THEN WALLOCPAUX_EAC_EXPAND_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  WALLOCPAUX_EAC_FINISH_TAC);;

let WALLOCPAUX_eac_Install = prove
 (`!a0 a1 a2 a3 a4.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Install a0 a1 a2 a3 a4:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_Install a0 a1 a2 a3 a4:(A)wl_prog)`,
  WALLOCPAUX_EAC_OPENC_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; pair_case_eq; case_eq "word_loc"; list_case_eq; COND_CASE_EQ;
      LET_DEF; LET_END_DEF] THEN
  WALLOCPAUX_EAC_EXPAND_TAC THEN WALLOCPAUX_EAC_GETVAR_TAC THEN WALLOCPAUX_EAC_CUTENV_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_word_loc_CASE; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[pair_CASE; option_CASE] THEN
  SIMP[] THEN CONJ_TAC THENL
   [REWRITE_TAC[word_state_eq_rel_def] THEN SIMP[] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC strong_locals_rel_insert THEN CONJ_TAC THENL
     [WALLOCPAUX_INJ_SUB_TAC;
      MATCH_MP_TAC strong_locals_rel_extend_aux THEN
      EXISTS_TAC `domain (FST (a4:num_set#num_set)) UNION domain (SND a4)` THEN
      ASM_REWRITE_TAC[SUBSET_REFL]]]);;

let WALLOCPAUX_eac_CodeBufferWrite = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_CodeBufferWrite a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_CodeBufferWrite a0 a1:(A)wl_prog)`,
  WALLOCPAUX_EAC_OPENC_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; pair_case_eq; case_eq "word_loc"] THEN
  WALLOCPAUX_EAC_EXPAND_TAC THEN WALLOCPAUX_EAC_GETVAR_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_word_loc_CASE] THEN
  WALLOCPAUX_EAC_FINISH_TAC);;

let WALLOCPAUX_eac_DataBufferWrite = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_DataBufferWrite a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_DataBufferWrite a0 a1:(A)wl_prog)`,
  WALLOCPAUX_EAC_OPENC_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; pair_case_eq; case_eq "word_loc"] THEN
  WALLOCPAUX_EAC_EXPAND_TAC THEN WALLOCPAUX_EAC_GETVAR_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_word_loc_CASE] THEN
  WALLOCPAUX_EAC_FINISH_TAC);;

let WALLOCPAUX_eac_FFI = prove
 (`!a0 a1 a2 a3 a4 a5.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_FFI a0 a1 a2 a3 a4 a5:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (wl_FFI a0 a1 a2 a3 a4 a5:(A)wl_prog)`,
  WALLOCPAUX_EAC_OPENC_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; pair_case_eq; case_eq "word_loc"; case_eq "ffi_result"] THEN
  WALLOCPAUX_EAC_EXPAND_TAC THEN WALLOCPAUX_EAC_GETVAR_TAC THEN WALLOCPAUX_EAC_CUTENV_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_word_loc_CASE] THEN
  SIMP[WALLOCPAUX_wl_result_CASE] THEN
  REWRITE_TAC[wl_flush_state_def] THEN SIMP[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[word_state_eq_rel_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC strong_locals_rel_extend_aux THEN
      EXISTS_TAC `domain (FST (a5:num_set#num_set)) UNION domain (SND a5)` THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN NO_TAC));;

let WALLOCPAUX_eac_ShareInst = prove
 (`!a0 a1 a2.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (ShareInst a0 a1 a2:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_eac_Q st (ShareInst a0 a1 a2:(A)wl_prog)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `a0:memop` (cases "memop")) THEN
  WALLOCPAUX_EAC_OPENC_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; pair_case_eq; case_eq "word_loc"; case_eq "ffi_result";
      share_inst_def; WALLOCPAUX_sh_mem_set_var_cases;
      wl_sh_mem_store_def; wl_sh_mem_load_def; wl_sh_mem_store_byte_def;
      wl_sh_mem_store16_def; wl_sh_mem_store32_def; wl_sh_mem_load_byte_def;
      wl_sh_mem_load16_def; wl_sh_mem_load32_def; COND_CASE_EQ; wl_set_var_def] THEN
  WALLOCPAUX_EAC_EXPAND_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE WALLOCPAUX_memop_distinct) THEN WALLOCPAUX_EAC_GETVAR_TAC THEN
  (SUBGOAL_THEN `wl_word_exp (cst:(A,C,FFI)wl_state) (apply_colour_exp f a2) = SOME (wl_Word a)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC apply_colour_exp_lemma THEN EXISTS_TAC `st:(A,C,FFI)wl_state` THEN
     ASM_REWRITE_TAC[word_state_eq_rel_def] THEN WALLOCPAUX_SLR_SUB_TAC;
     ALL_TAC]) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_word_loc_CASE; share_inst_def;
                  WALLOCPAUX_sh_mem_set_var_cases;
                  wl_sh_mem_store_def; wl_sh_mem_load_def; wl_sh_mem_store_byte_def;
                  wl_sh_mem_store16_def; wl_sh_mem_store32_def; wl_sh_mem_load_byte_def;
                  wl_sh_mem_load16_def; wl_sh_mem_load32_def; wl_set_var_def] THEN
  SIMP[WALLOCPAUX_wl_result_CASE] THEN
  REWRITE_TAC[wl_flush_state_def] THEN WALLOCPAUX_EAC_FINISH_TAC);;

(* HOL4 line 1105 *)
let evaluate_apply_colour = prove
 (CASE_TERM
  `!(prog:(A)wl_prog) (st:(A,C,FFI)wl_state) cst f live lt.
     colouring_ok f prog live lt /\
     word_state_eq_rel st cst /\
     strong_locals_rel f (domain (get_live prog live lt))
       (wl_state_locals st) (wl_state_locals cst)
     ==> ?perm'.
           let (res,rst) = wl_evaluate (prog,wl_state_permute_fupd (K perm') st) in
           if res = SOME wl_Error then T else
           let (res',rcst) = wl_evaluate (apply_colour f prog,cst) in
             res = res' /\
             word_state_eq_rel rst rcst /\
             (match res with
                NONE ->
                  strong_locals_rel f (domain live)
                    (wl_state_locals rst) (wl_state_locals rcst)
              | SOME (wordSem_Break n) ->
                  (match oEL n lt with
                     SOME (_,exit_names) ->
                       strong_locals_rel f (domain exit_names)
                         (wl_state_locals rst) (wl_state_locals rcst)
                   | NONE -> T)
              | SOME (wordSem_Continue n) ->
                  (match oEL n lt with
                     SOME (names,_) ->
                       strong_locals_rel f (domain names)
                         (wl_state_locals rst) (wl_state_locals rcst)
                   | NONE -> T)
              | SOME _ -> wl_state_locals rst = wl_state_locals rcst)`,
  SUBGOAL_THEN `!(prog:(A)wl_prog) (st:(A,C,FFI)wl_state). WALLOCPAUX_eac_Q st prog`
    MP_TAC THENL
   [MATCH_MP_TAC WALLOCPAUX_prog_size_induct THEN X_GEN_TAC `p:(A)wl_prog` THEN
    STRUCT_CASES_TAC (ISPEC `p:(A)wl_prog` (CONJUNCT1 (cases "wl_prog"))) THEN
    FIRST (map (fun th -> MATCH_ACCEPT_TAC th ORELSE MATCH_ACCEPT_TAC (SPEC_ALL th))
       [WALLOCPAUX_eac_Skip;
        WALLOCPAUX_eac_Move;
        WALLOCPAUX_eac_Inst;
        WALLOCPAUX_eac_Assign;
        WALLOCPAUX_eac_Get;
        WALLOCPAUX_eac_Set;
        WALLOCPAUX_eac_Store;
        WALLOCPAUX_eac_MustTerminate;
        WALLOCPAUX_eac_Call;
        WALLOCPAUX_eac_Seq;
        WALLOCPAUX_eac_If;
        WALLOCPAUX_eac_Loop;
        WALLOCPAUX_eac_Alloc;
        WALLOCPAUX_eac_StoreConsts;
        WALLOCPAUX_eac_Raise;
        WALLOCPAUX_eac_Return;
        WALLOCPAUX_eac_Break;
        WALLOCPAUX_eac_Continue;
        WALLOCPAUX_eac_Tick;
        WALLOCPAUX_eac_OpCurrHeap;
        WALLOCPAUX_eac_LocValue;
        WALLOCPAUX_eac_Install;
        WALLOCPAUX_eac_CodeBufferWrite;
        WALLOCPAUX_eac_DataBufferWrite;
        WALLOCPAUX_eac_FFI;
        WALLOCPAUX_eac_ShareInst]);
    ALL_TAC] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`prog:(A)wl_prog`; `st:(A,C,FFI)wl_state`]) THEN
  REWRITE_TAC[WALLOCPAUX_eac_Q_def] THEN DISCH_THEN(ACCEPT_TAC o SPEC_ALL));;

(* HOL4 lines 2270-2383 (colouring_ok_alt, get_clash_sets lemmas) and       *)
(* 2398-2590 (every_var_in_get_clash_set) are commented out in HOL4         *)

(* HOL4 line 2385 *)
let every_var_exp_get_live_exp = prove
 (`!exp:(A)wl_exp. every_var_exp (\x. x IN domain (get_live_exp exp)) exp`,
  MATCH_MP_TAC get_live_exp_ind THEN
  REWRITE_TAC[get_live_exp_def; every_var_exp_def; domain_insert; domain_union;
              IN_INSERT; IN_UNION] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC every_var_exp_mono THEN
    EXISTS_TAC `\y. y IN domain (get_live_exp (x:(A)wl_exp))` THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[SUBSET; domain_big_union_subset];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC every_var_exp_mono THEN
    FIRST_ASSUM(fun th -> EXISTS_TAC (rand(rator(concl th))) THEN
                          CONJ_TAC THENL [SIMP_TAC[]; ACCEPT_TAC th])]);;

(* HOL4 line 2592: check_col_INJ *)
let word_allocProof_check_col_INJ = prove
 (`!f (numset:A spt) q r.
     check_col f numset = SOME (q,r)
     ==> q = numset /\ INJ f (domain q) UNIV /\ domain r = IMAGE f (domain q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[check_col_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM MAP_MAP_o]) THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP INJ_ALL_DISTINCT_MAP) THEN
    REWRITE_TAC[set_MAP_FST_toAList_domain];
    REWRITE_TAC[domain_fromAList; MAP_MAP_o; o_DEF; FST; ETA_AX] THEN
    REWRITE_TAC[GSYM o_DEF; GSYM MAP_MAP_o; SET_OF_LIST_MAP;
                set_MAP_FST_toAList_domain] THEN
    REWRITE_TAC[IMAGE_o; GSYM SET_OF_LIST_MAP; set_MAP_FST_toAList_domain]]);;

(* HOL4 line 2608 *)
let wf_insert_swap = prove
 (`!(t:num_set) a c.
     wf t ==> insert (a:num) one (insert c one t) = insert (c:num) one (insert a one t)`,
  REPEAT STRIP_TAC THEN
  W(fun (asl,w) -> MP_TAC (ISPECL [lhs w; rhs w] spt_eq_thm)) THEN
  ASM_SIMP_TAC[wf_insert] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[lookup_insert] THEN GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`n:num = a`; `n:num = c`] THEN
  ASM_REWRITE_TAC[COND_ID]);;

(* HOL4 line 2620 *)
let numset_list_insert_swap = prove
 (`!ls h (live:num_set).
     wf live
     ==> wf (word_alloc_numset_list_insert ls live) /\
         word_alloc_numset_list_insert ls (insert h one live) =
         insert h one (word_alloc_numset_list_insert ls live)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[word_alloc_numset_list_insert_def] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[wf_insert] THEN
  MATCH_MP_TAC wf_insert_swap THEN ASM_SIMP_TAC[]);;

(* HOL4 line 2632: check_partial_col_INJ *)
let word_allocProof_check_partial_col_INJ = prove
 (`!ls f (live:num_set) flive live' flive'.
     wf live /\
     domain flive = IMAGE f (domain live) /\
     INJ f (domain live) UNIV /\
     check_partial_col f ls live flive = SOME (live',flive')
     ==> wf live' /\
         live' = word_alloc_numset_list_insert ls live /\
         INJ f (domain live') UNIV /\
         domain flive' = IMAGE f (domain live')`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[check_partial_col_def; word_alloc_numset_list_insert_def; option_INJ;
              PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  CASES_ON `lookup h (live:num_set)` THEN REWRITE_TAC[option_CASE] THENL
   [CASES_ON `lookup ((f:num->num) h) (flive:num_set)` THEN
    REWRITE_TAC[option_CASE; option_DISTINCT] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`f:num->num`; `insert h one (live:num_set)`;
      `insert ((f:num->num) h) one (flive:num_set)`; `live':num_set`;
      `flive':num_set`]) THEN
    ASM_SIMP_TAC[wf_insert; domain_insert; IMAGE_CLAUSES] THEN
    ANTS_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[lookup_NONE_domain]) THEN
      UNDISCH_TAC `INJ (f:num->num) (domain (live:num_set)) (:num)` THEN
      REWRITE_TAC[INJ; IN_INSERT; IN_UNIV] THEN
      UNDISCH_TAC `~((f:num->num) h IN domain (flive:num_set))` THEN
      ASM_REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[numset_list_insert_swap];
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`f:num->num`; `live:num_set`; `flive:num_set`;
                                  `live':num_set`; `flive':num_set`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `insert h one (live:num_set) = live` ASSUME_TAC THENL
     [W(fun (asl,w) -> MP_TAC (ISPECL [lhs w; rhs w] spt_eq_thm)) THEN
      ASM_SIMP_TAC[wf_insert] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[lookup_insert] THEN GEN_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[one];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:num list`; `h:num`; `live:num_set`] numset_list_insert_swap) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* HOL4 line 2685 *)
let domain_insert_eq_union = prove
 (`!num (live:num_set).
     domain (insert num one live) = domain (union (insert num one LN) live)`,
  REWRITE_TAC[domain_union; domain_insert; domain_def] THEN SET_TAC[]);;

(* HOL4 line 2692 *)
let domain_numset_list_insert_eq_union = prove
 (`!ls (live:num_set).
     domain (word_alloc_numset_list_insert ls live) =
     domain (union (word_alloc_numset_list_insert ls LN) live)`,
  REWRITE_TAC[domain_union; word_allocProof_domain_numset_list_insert; domain_def] THEN
  SET_TAC[]);;

(* HOL4 line 2720 *)
let lookup_numset_list_insert = prove
 (`!ls n (t:num_set).
     lookup n (word_alloc_numset_list_insert ls t) =
     if MEM n ls then SOME one else lookup n t`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[word_alloc_numset_list_insert_def; MEM; lookup_insert] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n:num = h` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 2729 *)
let numset_list_insert_eq_UNION = prove
 (`!(t:num_set) t' ls.
     wf t /\ wf t' /\ domain t' = set_of_list ls
     ==> word_alloc_numset_list_insert ls t = union t' t`,
  REPEAT STRIP_TAC THEN
  W(fun (asl,w) -> MP_TAC (ISPECL [lhs w; rhs w] spt_eq_thm)) THEN
  ASM_SIMP_TAC[wf_union; numset_list_insert_swap] THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[lookup_numset_list_insert; lookup_union] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `n IN domain (t':num_set)` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_SET_OF_LIST]; ALL_TAC] THEN
    REWRITE_TAC[domain_lookup] THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE] THEN
    MESON_TAC[one];
    SUBGOAL_THEN `lookup n (t':num_set) = NONE` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[lookup_NONE_domain; IN_SET_OF_LIST]; REWRITE_TAC[option_CASE]]]);;

(* HOL4 line 2751 *)
let wf_delete_swap = prove
 (`!(t:A spt) a c. wf t ==> delete a (delete c t) = delete c (delete a t)`,
  REPEAT STRIP_TAC THEN
  W(fun (asl,w) -> MP_TAC (ISPECL [lhs w; rhs w] spt_eq_thm)) THEN
  ASM_SIMP_TAC[wf_delete] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[lookup_delete] THEN GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`n:num = a`; `n:num = c`] THEN ASM_REWRITE_TAC[COND_ID]);;

(* HOL4 line 2762 *)
let numset_list_delete_swap = prove
 (`!ls h (live:A spt).
     wf live
     ==> wf (numset_list_delete ls live) /\
         numset_list_delete ls (delete h live) = delete h (numset_list_delete ls live)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[numset_list_delete_def] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[wf_delete] THEN
  ASM_SIMP_TAC[wf_delete_swap]);;

(* HOL4 line 2774 *)
let wf_numset_list_delete_eq = prove
 (`!ls (t:A spt) (live:B). wf t ==> ITLIST delete ls t = numset_list_delete ls t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[numset_list_delete_def; ITLIST] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[numset_list_delete_swap]);;

(* HOL4 line 2782 *)
let wf_get_live_exp = prove
 (`!exp:(A)wl_exp. wf (get_live_exp exp)`,
  MATCH_MP_TAC get_live_exp_ind THEN
  SIMP_TAC[get_live_exp_def; wf_insert; wf_union; wf_def] THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[big_union_def; ITLIST; MAP; MEM; wf_def] THEN
  REWRITE_TAC[GSYM big_union_def] THEN ASM_MESON_TAC[wf_union]);;

(* HOL4 lines 2791-2801: val start_tac, subset_tac (ML) *)

(* HOL4 line 2806: IMAGE_DIFF *)
let word_allocProof_IMAGE_DIFF = prove
 (`!(f:A->B) s t.
     INJ f (s UNION t) UNIV ==> IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t`,
  REWRITE_TAC[INJ; EXTENSION; IN_IMAGE; IN_DIFF; IN_UNION; IN_UNIV] THEN
  MESON_TAC[]);;

(* helpers for clash_tree_colouring_ok: a Delta node checks the writes,    *)
(* then the reads on the live set without the writes                        *)

let WALLOCPAUX_wf_numset_list_delete = prove
 (`!l (t:A spt). wf t ==> wf (numset_list_delete l t)`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[numset_list_delete_def; wf_delete]);;

let WALLOCPAUX_ctc_delta = prove
 (`!w r f (live:num_set) flive livein flivein.
     wf live /\ domain flive = IMAGE f (domain live) /\ INJ f (domain live) UNIV /\
     check_clash_tree f (Delta w r) live flive = SOME (livein,flivein)
     ==> wf livein /\ INJ f (domain livein) UNIV /\
         livein = word_alloc_numset_list_insert r (numset_list_delete w live) /\
         domain flivein = IMAGE f (domain livein) /\
         INJ f (domain (word_alloc_numset_list_insert w live)) UNIV`,
  REPEAT GEN_TAC THEN REWRITE_TAC[check_clash_tree_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MP_TAC(ISPEC `check_partial_col (f:num->num) w (live:num_set) flive` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `p:num_set#num_set`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  REWRITE_TAC[option_CASE; option_DISTINCT] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:num list`; `f:num->num`; `live:num_set`; `flive:num_set`;
                 `FST (p:num_set#num_set)`; `SND (p:num_set#num_set)`]
    word_allocProof_check_partial_col_INJ) THEN
  ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN
  SUBGOAL_THEN `INJ (f:num->num) (domain (word_alloc_numset_list_insert w (live:num_set))) UNIV`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:num list`; `f:num->num`; `numset_list_delete w (live:num_set)`;
                 `numset_list_delete (MAP (f:num->num) w) (flive:num_set)`;
                 `livein:num_set`; `flivein:num_set`]
    word_allocProof_check_partial_col_INJ) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[WALLOCPAUX_wf_numset_list_delete; reg_allocProof_domain_numset_list_delete] THEN
    UNDISCH_TAC `INJ (f:num->num) (domain (word_alloc_numset_list_insert w (live:num_set))) UNIV` THEN
    REWRITE_TAC[word_allocProof_domain_numset_list_insert; SET_OF_LIST_MAP] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INJ_IMP_IMAGE_DIFF THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC word_allocProof_INJ_less THEN
      EXISTS_TAC `domain (live:num_set) UNION set_of_list w` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let WALLOCPAUX_lookup_numset_list_delete = prove
 (`!ls n (t:A spt). lookup n (numset_list_delete ls t) = if MEM n ls then NONE else lookup n t`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[numset_list_delete_def; MEM; lookup_delete] THEN
  REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC [`n:num = h`; `MEM (n:num) t`] THEN
  ASM_REWRITE_TAC[]);;

let WALLOCPAUX_spt_eq = prove
 (`!t1 t2:A spt. wf t1 /\ wf t2 /\ (!n. lookup n t1 = lookup n t2) ==> t1 = t2`,
  MESON_TAC[spt_eq_thm]);;

let WALLOCPAUX_wf_numset_list_insert = prove
 (`!ls (t:num_set). wf t ==> wf (word_alloc_numset_list_insert ls t)`,
  MESON_TAC[numset_list_insert_swap]);;

(* equality of number sets built from wf sets by insert, delete and their  *)
(* list versions: pointwise                                                 *)

let WALLOCPAUX_SPT_EQ_TAC : tactic =
  MATCH_MP_TAC WALLOCPAUX_spt_eq THEN REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC wf_insert ORELSE MATCH_MP_TAC wf_delete ORELSE
           MATCH_MP_TAC WALLOCPAUX_wf_numset_list_insert ORELSE
           MATCH_MP_TAC WALLOCPAUX_wf_numset_list_delete ORELSE MATCH_MP_TAC wf_union) THEN
    ASM_REWRITE_TAC[wf_def];
    REPEAT(MATCH_MP_TAC wf_insert ORELSE MATCH_MP_TAC wf_delete ORELSE
           MATCH_MP_TAC WALLOCPAUX_wf_numset_list_insert ORELSE
           MATCH_MP_TAC WALLOCPAUX_wf_numset_list_delete ORELSE MATCH_MP_TAC wf_union) THEN
    ASM_REWRITE_TAC[wf_def];
    GEN_TAC THEN
    REWRITE_TAC[lookup_insert; lookup_delete; lookup_numset_list_insert;
                WALLOCPAUX_lookup_numset_list_delete; MEM; lookup_union] THEN
    (fun (asl,w as g) ->
       let conds = setify (map (fun t -> fst(dest_cond t))
                               (find_terms is_cond w)) in
       let fw = frees w in
       let cs = filter (fun c -> forall (fun v -> mem v fw) (frees c)) conds in
       (MAP_EVERY ASM_CASES_TAC cs THEN ASM_REWRITE_TAC[COND_ID]) g) THEN
    TRY(REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[COND_ID] THEN ASM_MESON_TAC[])];;

(* the cases of clash_tree_colouring_ok: open the predicate and the clash  *)
(* tree; for a Delta node, get the facts of WALLOCPAUX_ctc_delta            *)

let WALLOCPAUX_ctc_P_def = new_definition (CASE_TERM
 `WALLOCPAUX_ctc_P (prog:(A)wl_prog) (lt:(num_set#num_set)list) <=>
   !f live flive livein flivein.
     wf_cutsets prog /\
     wf live /\
     ALL (\ne. match ne with (n,e) -> wf n /\ wf e) lt /\
     domain flive = IMAGE f (domain live) /\
     INJ f (domain live) UNIV /\
     check_clash_tree f (get_clash_tree prog lt) live flive = SOME (livein,flivein)
     ==> word_allocProof_hide
           (wf livein /\
            INJ f (domain livein) UNIV /\
            colouring_ok f prog live lt /\
            livein = get_live prog live lt /\
            domain flivein = IMAGE f (domain livein))`);;

let WALLOCPAUX_CTC_OPEN_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[WALLOCPAUX_ctc_P_def; word_allocProof_hide_def] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[get_clash_tree_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC;;

let WALLOCPAUX_CTC_DELTA_TAC : tactic =
  let hd_name tm = try fst(dest_const(fst(strip_comb tm))) with Failure _ -> "" in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && hd_name (lhs c) = "check_clash_tree" &&
       hd_name (el 1 (snd(strip_comb(lhs c)))) = "Delta" then
      let args = snd(strip_comb(lhs c)) in
      let f = el 0 args and tr = el 1 args and live = el 2 args and flive = el 3 args in
      let wr = snd(strip_comb tr) in
      let livein,flivein = dest_pair (rand(rhs c)) in
      MP_TAC (SPECL [el 0 wr; el 1 wr; f; live; flive; livein; flivein] WALLOCPAUX_ctc_delta)
      THEN ANTS_TAC THENL [ASM_REWRITE_TAC[th]; STRIP_TAC]
    else NO_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th)) &&
                                                 hd_name(rhs(concl th)) =
                                                   "word_alloc_numset_list_insert")) THEN
  ASM_REWRITE_TAC[colouring_ok_def; get_live_def; get_writes_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV);;

(* INJ f S UNIV from an assumption INJ f S' UNIV with S a subset of S'      *)

let WALLOCPAUX_nli_reads = prove
 (`!(e:(A)wl_exp) (t:num_set).
     wf t ==> word_alloc_numset_list_insert (get_reads_exp e) t = union (get_live_exp e) t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC numset_list_insert_eq_UNION THEN
  ASM_REWRITE_TAC[wf_get_live_exp; get_reads_exp_get_live_exp]);;

(* equality of wf number sets by their domains *)

let WALLOCPAUX_numset_eq = prove
 (`!t1 t2:num_set. wf t1 /\ wf t2 /\ domain t1 = domain t2 ==> t1 = t2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[spt_eq_thm] THEN X_GEN_TAC `n:num` THEN
  UNDISCH_TAC `domain (t1:num_set) = domain (t2:num_set)` THEN
  REWRITE_TAC[EXTENSION; domain_lookup] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  MP_TAC(ISPEC `lookup n (t1:num_set)` (cases "option")) THEN
  MP_TAC(ISPEC `lookup n (t2:num_set)` (cases "option")) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ]) THEN
  ASM_MESON_TAC[one; option_DISTINCT]);;

let WALLOCPAUX_NUMSET_EQ_TAC : tactic =
  MATCH_MP_TAC WALLOCPAUX_numset_eq THEN REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC wf_insert ORELSE MATCH_MP_TAC wf_delete ORELSE
           MATCH_MP_TAC WALLOCPAUX_wf_numset_list_insert ORELSE
           MATCH_MP_TAC WALLOCPAUX_wf_numset_list_delete ORELSE
           (MATCH_MP_TAC wf_union THEN CONJ_TAC)) THEN
    ASM_REWRITE_TAC[wf_def; wf_get_live_exp];
    REPEAT(MATCH_MP_TAC wf_insert ORELSE MATCH_MP_TAC wf_delete ORELSE
           MATCH_MP_TAC WALLOCPAUX_wf_numset_list_insert ORELSE
           MATCH_MP_TAC WALLOCPAUX_wf_numset_list_delete ORELSE
           (MATCH_MP_TAC wf_union THEN CONJ_TAC)) THEN
    ASM_REWRITE_TAC[wf_def; wf_get_live_exp];
    REWRITE_TAC[domain_union; domain_insert; domain_delete; domain_def;
                word_allocProof_domain_numset_list_insert;
                reg_allocProof_domain_numset_list_delete; set_of_list;
                GSYM get_reads_exp_get_live_exp; list_insert_def;
                set_MAP_FST_toAList_domain; domain_difference] THEN
    SET_TAC[]];;

let WALLOCPAUX_ctc_branch_some = prove
 (`!f t t1 t2 (live:num_set) flive livein flivein.
     check_clash_tree f (reg_alloc_Branch (SOME t) t1 t2) live flive = SOME (livein,flivein)
     <=> (?a b. check_clash_tree f t1 live flive = SOME (a,b)) /\
         (?c d. check_clash_tree f t2 live flive = SOME (c,d)) /\
         check_clash_tree f (reg_alloc_Set t) live flive = SOME (livein,flivein)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[check_clash_tree_def] THEN
  MP_TAC(ISPEC `check_clash_tree f t1 (live:num_set) flive` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `p:num_set#num_set` SUBST1_TAC)) THEN
  REWRITE_TAC[option_CASE; option_DISTINCT] THEN
  MP_TAC(ISPEC `check_clash_tree f t2 (live:num_set) flive` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `q:num_set#num_set` SUBST1_TAC)) THEN
  REWRITE_TAC[option_CASE; option_DISTINCT] THEN
  MAP_EVERY (fun v -> SPEC_TAC(v,v)) [`q:num_set#num_set`; `p:num_set#num_set`] THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE] THEN SIMP[]);;

let WALLOCPAUX_WF_TAC : tactic =
  REPEAT(MATCH_MP_TAC wf_insert ORELSE MATCH_MP_TAC wf_delete ORELSE
         MATCH_MP_TAC WALLOCPAUX_wf_numset_list_insert ORELSE
         MATCH_MP_TAC WALLOCPAUX_wf_numset_list_delete ORELSE
         (MATCH_MP_TAC wf_union THEN CONJ_TAC)) THEN
  ASM_REWRITE_TAC[wf_def; wf_get_live_exp];;

(* apply a labelled induction hypothesis WALLOCPAUX_ctc_P P lt to the      *)
(* assumption that checks the clash tree of P                               *)

let WALLOCPAUX_CTC_IH_TAC (lab:string) : tactic =
  USE_THEN lab (fun ih ->
    let ih' = SPEC_ALL (REWRITE_RULE[WALLOCPAUX_ctc_P_def; word_allocProof_hide_def] ih) in
    let ant,_ = dest_imp (concl ih') in
    let chk = last (conjuncts ant) in
    FIRST_ASSUM(fun th -> MP_TAC (INSTANTIATE (term_match [] chk (concl th)) ih'))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC];;

let WALLOCPAUX_CTC_FINISH_TAC : tactic =
  ASM_SIMP_TAC[wf_numset_list_delete_eq; word_alloc_numset_list_insert_def;
               numset_list_delete_def; list_insert_def; WALLOCPAUX_nli_reads; wf_insert;
               wf_delete; WALLOCPAUX_wf_numset_list_delete] THEN
  REPEAT CONJ_TAC THEN
  TRY(WALLOCPAUX_INJ_SUB_TAC THEN NO_TAC) THEN
  TRY(WALLOCPAUX_NUMSET_EQ_TAC THEN NO_TAC) THEN
  TRY(WALLOCPAUX_SPT_EQ_TAC THEN NO_TAC);;

(* a Set node and a Seq node of a clash tree *)

let WALLOCPAUX_ctc_set = prove
 (`!f (t:num_set) (live:num_set) flive livein flivein.
     check_clash_tree f (reg_alloc_Set t) live flive = SOME (livein,flivein)
     ==> livein = t /\ INJ f (domain t) UNIV /\ domain flivein = IMAGE f (domain t)`,
  REWRITE_TAC[check_clash_tree_def] THEN MESON_TAC[word_allocProof_check_col_INJ]);;

let WALLOCPAUX_ctc_seq = prove
 (`!f t1 t2 (live:num_set) flive livein flivein.
     check_clash_tree f (reg_alloc_Seq t1 t2) live flive = SOME (livein,flivein) <=>
     ?l2 fl2. check_clash_tree f t2 live flive = SOME (l2,fl2) /\
              check_clash_tree f t1 l2 fl2 = SOME (livein,flivein)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[check_clash_tree_def] THEN
  MP_TAC(ISPEC `check_clash_tree f t2 (live:num_set) flive` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `p:num_set#num_set` SUBST1_TAC)) THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN
  SPEC_TAC(`p:num_set#num_set`,`p:num_set#num_set`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; PAIR_EQ] THEN MESON_TAC[]);;

(* helper: the statement of clash_tree_colouring_ok for one program, as a   *)
(* predicate, so that each case of the induction on get_clash_tree is a     *)
(* lemma                                                                     *)

let WALLOCPAUX_ctc_Skip = prove
 (`!(lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (wl_Skip:(A)wl_prog) lt`,
  WALLOCPAUX_CTC_OPEN_TAC THEN WALLOCPAUX_CTC_DELTA_TAC THEN WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_Move = prove
 (`!pri ls (lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (wl_Move pri ls:(A)wl_prog) lt`,
  WALLOCPAUX_CTC_OPEN_TAC THEN WALLOCPAUX_CTC_DELTA_TAC THEN WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_Inst = prove
 (`!i (lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (wl_Inst i:(A)wl_prog) lt`,
  GEN_TAC THEN WALLOCPAUX_INST_CASES_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[WALLOCPAUX_ctc_P_def; word_allocProof_hide_def] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[get_clash_tree_def; get_delta_inst_def; WALLOCPAUX_reg_imm_CASE] THEN
  TRY COND_CASES_TAC THEN STRIP_TAC THEN
  WALLOCPAUX_CTC_DELTA_TAC THEN
  ASM_REWRITE_TAC[get_live_inst_def; get_writes_inst_def; WALLOCPAUX_reg_imm_CASE] THEN
  WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_Assign = prove
 (`!nm e (lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (wl_Assign nm e:(A)wl_prog) lt`,
  WALLOCPAUX_CTC_OPEN_TAC THEN WALLOCPAUX_CTC_DELTA_TAC THEN WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_Get = prove
 (`!nm sn (lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (wl_Get nm sn:(A)wl_prog) lt`,
  WALLOCPAUX_CTC_OPEN_TAC THEN WALLOCPAUX_CTC_DELTA_TAC THEN WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_Store = prove
 (`!e nm (lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (wl_Store e nm:(A)wl_prog) lt`,
  WALLOCPAUX_CTC_OPEN_TAC THEN WALLOCPAUX_CTC_DELTA_TAC THEN WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_Seq = prove
 (`!s1 s2 (lt:(num_set#num_set)list).
       WALLOCPAUX_ctc_P s1 lt /\ WALLOCPAUX_ctc_P s2 lt
       ==> WALLOCPAUX_ctc_P (wl_Seq s1 s2:(A)wl_prog) lt`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REWRITE_TAC[WALLOCPAUX_ctc_P_def; word_allocProof_hide_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[get_clash_tree_def; check_clash_tree_def; wf_cutsets_def] THEN
  MP_TAC(ISPEC `check_clash_tree (f:num->num) (get_clash_tree (s2:(A)wl_prog) lt) live flive`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `p2:num_set#num_set`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  REWRITE_TAC[option_CASE; option_DISTINCT] THEN
  WALLOCPAUX_TUPLE_TAC `p2:num_set#num_set` [`l2:num_set`; `fl2:num_set`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  REMOVE_THEN "ih2" (MP_TAC o REWRITE_RULE[WALLOCPAUX_ctc_P_def; word_allocProof_hide_def]) THEN
  DISCH_THEN(MP_TAC o SPECL [`f:num->num`; `live:num_set`; `flive:num_set`; `l2:num_set`;
                             `fl2:num_set`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ih1" (MP_TAC o REWRITE_RULE[WALLOCPAUX_ctc_P_def; word_allocProof_hide_def]) THEN
  DISCH_THEN(MP_TAC o SPECL [`f:num->num`; `l2:num_set`; `fl2:num_set`; `livein:num_set`;
                             `flivein:num_set`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `livein:num_set`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `l2:num_set`)) THEN
  ASM_REWRITE_TAC[colouring_ok_def; get_live_def; LET_DEF; LET_END_DEF]);;

let WALLOCPAUX_ctc_If = prove
 (`!cmp r1 ri e2 e3 (lt:(num_set#num_set)list).
       WALLOCPAUX_ctc_P e2 lt /\ WALLOCPAUX_ctc_P e3 lt
       ==> WALLOCPAUX_ctc_P (wl_If cmp r1 ri e2 e3:(A)wl_prog) lt`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih2") (LABEL_TAC "ih3")) THEN
  STRUCT_CASES_TAC (ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN
  WALLOCPAUX_CTC_OPEN_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WALLOCPAUX_reg_imm_CASE; WALLOCPAUX_ctc_seq; wf_cutsets_def]) THEN
  REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
    try fst(dest_const t) = "reg_alloc_Branch" with Failure _ -> false)) (concl th))) THEN
  REWRITE_TAC[check_clash_tree_def] THEN
  MP_TAC(ISPEC `check_clash_tree (f:num->num) (get_clash_tree (e2:(A)wl_prog) lt) live flive`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `p2:num_set#num_set`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  REWRITE_TAC[option_CASE; option_DISTINCT] THEN
  WALLOCPAUX_TUPLE_TAC `p2:num_set#num_set` [`t2o:num_set`; `ft2o:num_set`] THEN
  REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPEC `check_clash_tree (f:num->num) (get_clash_tree (e3:(A)wl_prog) lt) live flive`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `p3:num_set#num_set`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  REWRITE_TAC[option_CASE; option_DISTINCT] THEN
  WALLOCPAUX_TUPLE_TAC `p3:num_set#num_set` [`t3o:num_set`; `ft3o:num_set`] THEN
  REWRITE_TAC[pair_CASE] THEN DISCH_TAC THEN
  REMOVE_THEN "ih2" (MP_TAC o REWRITE_RULE[WALLOCPAUX_ctc_P_def; word_allocProof_hide_def]) THEN
  DISCH_THEN(MP_TAC o SPECL [`f:num->num`; `live:num_set`; `flive:num_set`; `t2o:num_set`;
                             `ft2o:num_set`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ih3" (MP_TAC o REWRITE_RULE[WALLOCPAUX_ctc_P_def; word_allocProof_hide_def]) THEN
  DISCH_THEN(MP_TAC o SPECL [`f:num->num`; `live:num_set`; `flive:num_set`; `t3o:num_set`;
                             `ft3o:num_set`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`MAP FST (toAList (difference (t3o:num_set) (t2o:num_set)))`; `f:num->num`;
                 `t2o:num_set`; `ft2o:num_set`; `l2:num_set`; `fl2:num_set`]
    word_allocProof_check_partial_col_INJ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `l2:num_set`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `t2o:num_set`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `t3o:num_set`)) THEN
  WALLOCPAUX_CTC_DELTA_TAC THEN ASM_REWRITE_TAC[WALLOCPAUX_reg_imm_CASE] THEN
  WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_MustTerminate = prove
 (`!s (lt:(num_set#num_set)list). WALLOCPAUX_ctc_P s lt ==> WALLOCPAUX_ctc_P (MustTerminate s:(A)wl_prog) lt`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_ctc_P_def; word_allocProof_hide_def; get_clash_tree_def;
              wf_cutsets_def; colouring_ok_def; get_live_def] THEN
  DISCH_THEN ACCEPT_TAC);;

let WALLOCPAUX_ctc_Alloc = prove
 (`!nm numset (lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (wl_Alloc nm numset:(A)wl_prog) lt`,
  WALLOCPAUX_CTC_OPEN_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WALLOCPAUX_ctc_seq; wf_cutsets_def; wf_names_def]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `l2:num_set` (X_CHOOSE_THEN `fl2:num_set` STRIP_ASSUME_TAC) o
                check (is_exists o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WALLOCPAUX_ctc_set) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `l2:num_set`)) THEN
  SUBGOAL_THEN `wf (union (FST (numset:num_set#num_set)) (SND numset))` ASSUME_TAC THENL
   [MATCH_MP_TAC wf_union THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  WALLOCPAUX_CTC_DELTA_TAC THEN WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_Install = prove
 (`!r1 r2 r3 r4 numset (lt:(num_set#num_set)list).
       WALLOCPAUX_ctc_P (wl_Install r1 r2 r3 r4 numset:(A)wl_prog) lt`,
  WALLOCPAUX_CTC_OPEN_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WALLOCPAUX_ctc_seq; wf_cutsets_def; wf_names_def]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `l2:num_set` (X_CHOOSE_THEN `fl2:num_set` STRIP_ASSUME_TAC) o
                check (is_exists o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WALLOCPAUX_ctc_set) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `l2:num_set`)) THEN
  SUBGOAL_THEN `wf (union (FST (numset:num_set#num_set)) (SND numset))` ASSUME_TAC THENL
   [MATCH_MP_TAC wf_union THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  WALLOCPAUX_CTC_DELTA_TAC THEN WALLOCPAUX_CTC_DELTA_TAC THEN
  WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_CodeBufferWrite = prove
 (`!r1 r2 (lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (wl_CodeBufferWrite r1 r2:(A)wl_prog) lt`,
  WALLOCPAUX_CTC_OPEN_TAC THEN WALLOCPAUX_CTC_DELTA_TAC THEN WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_DataBufferWrite = prove
 (`!r1 r2 (lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (wl_DataBufferWrite r1 r2:(A)wl_prog) lt`,
  WALLOCPAUX_CTC_OPEN_TAC THEN WALLOCPAUX_CTC_DELTA_TAC THEN WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_FFI = prove
 (`!ffi_index ptr1 len1 ptr2 len2 numset (lt:(num_set#num_set)list).
       WALLOCPAUX_ctc_P (wl_FFI ffi_index ptr1 len1 ptr2 len2 numset:(A)wl_prog) lt`,
  WALLOCPAUX_CTC_OPEN_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WALLOCPAUX_ctc_seq; wf_cutsets_def; wf_names_def]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `l2:num_set` (X_CHOOSE_THEN `fl2:num_set` STRIP_ASSUME_TAC) o
                check (is_exists o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WALLOCPAUX_ctc_set) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `l2:num_set`)) THEN
  SUBGOAL_THEN `wf (union (FST (numset:num_set#num_set)) (SND numset))` ASSUME_TAC THENL
   [MATCH_MP_TAC wf_union THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  WALLOCPAUX_CTC_DELTA_TAC THEN WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_Raise = prove
 (`!nm (lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (wl_Raise nm:(A)wl_prog) lt`,
  WALLOCPAUX_CTC_OPEN_TAC THEN WALLOCPAUX_CTC_DELTA_TAC THEN WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_Return = prove
 (`!num1 nms (lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (wl_Return num1 nms:(A)wl_prog) lt`,
  WALLOCPAUX_CTC_OPEN_TAC THEN WALLOCPAUX_CTC_DELTA_TAC THEN WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_Tick = prove
 (`!(lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (wl_Tick:(A)wl_prog) lt`,
  WALLOCPAUX_CTC_OPEN_TAC THEN WALLOCPAUX_CTC_DELTA_TAC THEN WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_LocValue = prove
 (`!r l1 (lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (wl_LocValue r l1:(A)wl_prog) lt`,
  WALLOCPAUX_CTC_OPEN_TAC THEN WALLOCPAUX_CTC_DELTA_TAC THEN WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_Set = prove
 (`!n e (lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (wl_Set n e:(A)wl_prog) lt`,
  WALLOCPAUX_CTC_OPEN_TAC THEN WALLOCPAUX_CTC_DELTA_TAC THEN WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_OpCurrHeap = prove
 (`!b dst src (lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (wl_OpCurrHeap b dst src:(A)wl_prog) lt`,
  WALLOCPAUX_CTC_OPEN_TAC THEN WALLOCPAUX_CTC_DELTA_TAC THEN WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_StoreConsts = prove
 (`!a b c d ws (lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (wl_StoreConsts a b c d ws:(A)wl_prog) lt`,
  WALLOCPAUX_CTC_OPEN_TAC THEN WALLOCPAUX_CTC_DELTA_TAC THEN WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_ShareInst = prove
 (`!mop v e (lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (ShareInst mop v e:(A)wl_prog) lt`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `mop:memop` (cases "memop")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[WALLOCPAUX_ctc_P_def; word_allocProof_hide_def] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[get_clash_tree_def] THEN SIMP_NOASM[] THEN STRIP_TAC THEN
  WALLOCPAUX_CTC_DELTA_TAC THEN SIMP_NOASM[] THEN WALLOCPAUX_CTC_FINISH_TAC);;

let WALLOCPAUX_ctc_Loop = prove
 (`!names body exit_names (lt:(num_set#num_set)list).
       WALLOCPAUX_ctc_P body (CONS (names,exit_names) lt)
       ==> WALLOCPAUX_ctc_P (wl_Loop names body exit_names:(A)wl_prog) lt`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  WALLOCPAUX_CTC_OPEN_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WALLOCPAUX_ctc_seq; wf_cutsets_def]) THEN
  REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WALLOCPAUX_ctc_set o
         check (fun th -> try fst(dest_const(rator(el 1 (snd(strip_comb(lhs(concl th)))))))
                               = "reg_alloc_Set" with Failure _ -> false))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `l2'':num_set`)) THEN
  REMOVE_THEN "ih" (MP_TAC o REWRITE_RULE[WALLOCPAUX_ctc_P_def; word_allocProof_hide_def]) THEN
  DISCH_THEN(MP_TAC o SPECL [`f:num->num`; `names:num_set`; `fl2'':num_set`; `l2':num_set`;
                             `fl2':num_set`]) THEN
  ASM_REWRITE_TAC[ALL; pair_CASE] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[colouring_ok_def; get_live_def]);;

let WALLOCPAUX_ctc_Break = prove
 (`!n (lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (wl_Break n:(A)wl_prog) lt`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_ctc_P_def; word_allocProof_hide_def; get_clash_tree_def;
              colouring_ok_def; get_live_def; get_writes_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPEC `oEL n (lt:(num_set#num_set)list)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `p:num_set#num_set`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  REWRITE_TAC[option_CASE] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WALLOCPAUX_ctc_set) THEN
    ASM_REWRITE_TAC[wf_def; domain_union; domain_def; UNION_EMPTY] THEN
    REWRITE_TAC[INJ; NOT_IN_EMPTY];
    ALL_TAC] THEN
  WALLOCPAUX_TUPLE_TAC `p:num_set#num_set` [`nm:num_set`; `en:num_set`] THEN
  REWRITE_TAC[pair_CASE] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WALLOCPAUX_ctc_set) THEN
  ASM_REWRITE_TAC[domain_union; domain_def; UNION_EMPTY] THEN
  UNDISCH_TAC `oEL n (lt:(num_set#num_set)list) = SOME (nm,en)` THEN
  REWRITE_TAC[oEL_EQ_EL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "ALL" with Failure _ -> false)) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `(nm:num_set,en:num_set)`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MEM_EL]; REWRITE_TAC[pair_CASE] THEN SIMP_TAC[]]);;

let WALLOCPAUX_ctc_Continue = prove
 (`!n (lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (wl_Continue n:(A)wl_prog) lt`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_ctc_P_def; word_allocProof_hide_def; get_clash_tree_def;
              colouring_ok_def; get_live_def; get_writes_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPEC `oEL n (lt:(num_set#num_set)list)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `p:num_set#num_set`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  REWRITE_TAC[option_CASE] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WALLOCPAUX_ctc_set) THEN
    ASM_REWRITE_TAC[wf_def; domain_union; domain_def; UNION_EMPTY] THEN
    REWRITE_TAC[INJ; NOT_IN_EMPTY];
    ALL_TAC] THEN
  WALLOCPAUX_TUPLE_TAC `p:num_set#num_set` [`nm:num_set`; `en:num_set`] THEN
  REWRITE_TAC[pair_CASE] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WALLOCPAUX_ctc_set) THEN
  ASM_REWRITE_TAC[domain_union; domain_def; UNION_EMPTY] THEN
  UNDISCH_TAC `oEL n (lt:(num_set#num_set)list) = SOME (nm,en)` THEN
  REWRITE_TAC[oEL_EQ_EL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "ALL" with Failure _ -> false)) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `(nm:num_set,en:num_set)`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MEM_EL]; REWRITE_TAC[pair_CASE] THEN SIMP_TAC[]]);;

let WALLOCPAUX_ctc_Call = prove
 (`!ret dest args h (lt:(num_set#num_set)list).
       (!vs cutsets x y ret_handler.
            ret = SOME (vs,cutsets,ret_handler,x,y)
            ==> WALLOCPAUX_ctc_P ret_handler lt) /\
       (!vs cutsets ret_handler x y v x' y2 prog.
            ret = SOME (vs,cutsets,ret_handler,x,y) /\
            h = SOME (v,prog,x',y2)
            ==> WALLOCPAUX_ctc_P prog lt)
       ==> WALLOCPAUX_ctc_P (wl_Call ret dest args h:(A)wl_prog) lt`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihr") (LABEL_TAC "ihh")) THEN
  MP_TAC(ISPEC `ret:(num list#(num_set#num_set)#(A)wl_prog#num#num)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN
    `rr:num list#(num_set#num_set)#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
   [WALLOCPAUX_CTC_OPEN_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_CASE]) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WALLOCPAUX_ctc_set) THEN
    ASM_REWRITE_TAC[colouring_ok_def; get_live_def; get_writes_def; LET_DEF; LET_END_DEF;
                    domain_union; domain_def; UNION_EMPTY] THEN
    MATCH_MP_TAC WALLOCPAUX_wf_numset_list_insert THEN REWRITE_TAC[wf_def];
    ALL_TAC] THEN
  WALLOCPAUX_TUPLE_TAC `rr:num list#(num_set#num_set)#(A)wl_prog#num#num`
    [`vs:num list`; `cutsets:num_set#num_set`; `rh:(A)wl_prog`; `x:num`; `y:num`] THEN
  USE_THEN "ihr" (MP_TAC o SPECL [`vs:num list`; `cutsets:num_set#num_set`; `x:num`; `y:num`;
                                  `rh:(A)wl_prog`]) THEN
  REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ihr1") THEN
  MP_TAC(ISPEC `h:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN
    `hh:num#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
   [WALLOCPAUX_CTC_OPEN_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_CASE; pair_CASE; WALLOCPAUX_ctc_seq; wf_cutsets_def;
                                wf_names_def]) THEN
    REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WALLOCPAUX_ctc_set o
           check (fun th -> try fst(dest_const(rator(el 1 (snd(strip_comb(lhs(concl th)))))))
                                 = "reg_alloc_Set" with Failure _ -> false))) THEN
    WALLOCPAUX_CTC_IH_TAC "ihr1" THEN
    ASM_REWRITE_TAC[colouring_ok_def; get_live_def; LET_DEF; LET_END_DEF; option_CASE;
                    pair_CASE] THEN
    REPEAT CONJ_TAC THEN FIRST [WALLOCPAUX_INJ_SUB_TAC; WALLOCPAUX_WF_TAC];
    WALLOCPAUX_TUPLE_TAC `hh:num#(A)wl_prog#num#num`
      [`v':num`; `hp:(A)wl_prog`; `x':num`; `y':num`] THEN
    USE_THEN "ihh" (MP_TAC o SPECL [`vs:num list`; `cutsets:num_set#num_set`; `rh:(A)wl_prog`;
      `x:num`; `y:num`; `v':num`; `x':num`; `y':num`; `hp:(A)wl_prog`]) THEN
    REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ihh1") THEN
    WALLOCPAUX_CTC_OPEN_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_CASE; pair_CASE; WALLOCPAUX_ctc_branch_some;
                                WALLOCPAUX_ctc_seq; wf_cutsets_def; wf_names_def]) THEN
    REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (fun th -> is_exists(concl th) ||
                                                               is_conj(concl th)))) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WALLOCPAUX_ctc_set o
           check (fun th -> try fst(dest_const(rator(el 1 (snd(strip_comb(lhs(concl th)))))))
                                 = "reg_alloc_Set" with Failure _ -> false))) THEN
    WALLOCPAUX_CTC_IH_TAC "ihr1" THEN WALLOCPAUX_CTC_IH_TAC "ihh1" THEN
    ASM_REWRITE_TAC[colouring_ok_def; get_live_def; LET_DEF; LET_END_DEF; option_CASE;
                    pair_CASE] THEN
    REPEAT CONJ_TAC THEN FIRST [WALLOCPAUX_INJ_SUB_TAC; WALLOCPAUX_WF_TAC]]);;

(* HOL4 line 2813 (the conclusion is hidden: very slow when it is not) *)
let clash_tree_colouring_ok = prove
 (CASE_TERM
  `!(prog:(A)wl_prog) lt f live flive livein flivein.
     wf_cutsets prog /\
     wf live /\
     ALL (\ne. match ne with (n,e) -> wf n /\ wf e) lt /\
     domain flive = IMAGE f (domain live) /\
     INJ f (domain live) UNIV /\
     check_clash_tree f (get_clash_tree prog lt) live flive = SOME (livein,flivein)
     ==> word_allocProof_hide
           (wf livein /\
            INJ f (domain livein) UNIV /\
            colouring_ok f prog live lt /\
            livein = get_live prog live lt /\
            domain flivein = IMAGE f (domain livein))`,
  SUBGOAL_THEN `!prog (lt:(num_set#num_set)list). WALLOCPAUX_ctc_P (prog:(A)wl_prog) lt`
    MP_TAC THENL
   [MATCH_MP_TAC get_clash_tree_ind THEN REPEAT CONJ_TAC THENL
     (map MATCH_ACCEPT_TAC
       [WALLOCPAUX_ctc_Skip; WALLOCPAUX_ctc_Move; WALLOCPAUX_ctc_Inst; WALLOCPAUX_ctc_Assign;
        WALLOCPAUX_ctc_Get; WALLOCPAUX_ctc_Store; WALLOCPAUX_ctc_Seq; WALLOCPAUX_ctc_If;
        WALLOCPAUX_ctc_MustTerminate; WALLOCPAUX_ctc_Alloc; WALLOCPAUX_ctc_Install;
        WALLOCPAUX_ctc_CodeBufferWrite; WALLOCPAUX_ctc_DataBufferWrite; WALLOCPAUX_ctc_FFI;
        WALLOCPAUX_ctc_Raise; WALLOCPAUX_ctc_Return; WALLOCPAUX_ctc_Tick;
        WALLOCPAUX_ctc_LocValue; WALLOCPAUX_ctc_Set; WALLOCPAUX_ctc_OpCurrHeap;
        WALLOCPAUX_ctc_StoreConsts; WALLOCPAUX_ctc_ShareInst; WALLOCPAUX_ctc_Loop;
        WALLOCPAUX_ctc_Break; WALLOCPAUX_ctc_Continue; WALLOCPAUX_ctc_Call]);
    ALL_TAC] THEN
  REWRITE_TAC[WALLOCPAUX_ctc_P_def] THEN MESON_TAC[]);;

(* HOL4 line 3300: Finalise clash_tree_colouring_ok (HOL4 bookkeeping) *)

(* HOL4 line 3304 (actually, it should probably be exactly 0,2,4,6...) *)
let even_starting_locals_def = cake_def
  `even_starting_locals (locs:((A)word_loc)spt) <=>
     !x. x IN domain locs ==> is_phy_var x`;;

(* HOL4 line 3309: fun rm_let (ML) *)

(* HOL4 line 3311 *)
let get_forced_tail_split = prove
 (`!c (p:(A)wl_prog) ls ls'.
     get_forced c p (APPEND ls ls') = APPEND (get_forced c p ls) ls'`,
  MATCH_MP_TAC get_forced_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN REWRITE_TAC[get_forced_def] THEN ASM_REWRITE_TAC[] THEN
  TRY(EVERY_CASE_TAC THEN REWRITE_TAC[APPEND_ASSOC; APPEND] THEN NO_TAC) THEN
  REPEAT (POP_ASSUM MP_TAC) THEN
  SPEC_TAC(`h:(num#(A)wl_prog#num#num)option`,`h:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; option_CASE; pair_CASE;
              option_DISTINCT; option_INJ; PAIR_EQ] THEN
  MESON_TAC[]);;

(* HOL4 line 3320 *)
let EVERY_get_forced = prove
 (`!P c (p:(A)wl_prog) ls.
     ALL P (get_forced c p ls) <=> ALL P (get_forced c p []) /\ ALL P ls`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`c:(A)asm_config`; `p:(A)wl_prog`; `[]:(num#num)list`;
                 `ls:(num#num)list`] get_forced_tail_split) THEN
  REWRITE_TAC[APPEND] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ALL_APPEND]);;

(* HOL4 line 3328 *)
let get_forced_pairwise_distinct = prove
 (CASE_TERM
  `!c (prog:(A)wl_prog) ls.
     ALL (\xy. match xy with (x,y) -> ~(x = y)) ls
     ==> ALL (\xy. match xy with (x,y) -> ~(x = y)) (get_forced c prog ls)`,
  MATCH_MP_TAC get_forced_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN REWRITE_TAC[get_forced_def] THEN ASM_SIMP_TAC[] THEN
  TRY(EVERY_CASE_TAC THEN
      ASM_REWRITE_TAC[ALL_APPEND; ALL; pair_CASE] THEN NO_TAC) THEN
  REPEAT (POP_ASSUM MP_TAC) THEN
  SPEC_TAC(`h:(num#(A)wl_prog#num#num)option`,`h:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; option_CASE; pair_CASE;
              option_DISTINCT; option_INJ; PAIR_EQ] THEN
  MESON_TAC[]);;

(* helper: get_forced only prepends to its accumulator *)

let WALLOCPAUX_get_forced_acc = prove
 (`!c (p:(A)wl_prog) ls. get_forced c p ls = APPEND (get_forced c p []) ls`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`c:(A)asm_config`; `p:(A)wl_prog`; `[]:(num#num)list`;
                 `ls:(num#num)list`] get_forced_tail_split) THEN
  REWRITE_TAC[APPEND]);;

(* HOL4 line 3337 *)
let get_forced_in_get_clash_tree = prove
 (CASE_TERM
  `!(prog:(A)wl_prog) lt c.
     ALL (\xy. match xy with
                 (x,y) -> in_clash_tree (get_clash_tree prog lt) x /\
                          in_clash_tree (get_clash_tree prog lt) y)
         (get_forced c prog [])`,
  MATCH_MP_TAC get_clash_tree_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN
  REWRITE_TAC[get_clash_tree_def; get_forced_def; ALL; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT GEN_TAC THEN
  TRY(ONCE_REWRITE_TAC[EVERY_get_forced] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE]) THEN
      REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE; in_clash_tree_def; ALL;
                  MEM] THEN
      ASM_MESON_TAC[] THEN NO_TAC) THENL
   [REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE] THEN
    REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN
    ASM_REWRITE_TAC[MEM; APPEND; PAIR_EQ; get_delta_inst_def; in_clash_tree_def;
                    ARITH_EQ] THEN
    MESON_TAC[];
    ONCE_REWRITE_TAC[EVERY_get_forced] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE]) THEN
    REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE; in_clash_tree_def; ALL;
                MEM] THEN
    CASES_ON `ri:(A)reg_imm` THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[in_clash_tree_def; option_CASE] THEN ASM_MESON_TAC[];
    REPEAT (POP_ASSUM MP_TAC) THEN
    SPEC_TAC(`h:(num#(A)wl_prog#num#num)option`,`h:(num#(A)wl_prog#num#num)option`) THEN
    SPEC_TAC(`ret:(num list#cutsets#(A)wl_prog#num#num)option`,
             `ret:(num list#cutsets#(A)wl_prog#num#num)option`) THEN
    REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
    REWRITE_TAC[get_forced_def; get_clash_tree_def; option_CASE; pair_CASE;
                option_DISTINCT; option_INJ; PAIR_EQ; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[option_CASE; pair_CASE] THEN
    REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    ONCE_REWRITE_TAC[EVERY_get_forced] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE]) THEN
    REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE; in_clash_tree_def; ALL;
                MEM] THEN
    ASM_MESON_TAC[]]);;

(* HOL4 line 3371 *)
let select_reg_alloc_correct = prove
 (CASE_TERM
  `!alg spillcosts k heu_moves tree forced fs.
     ALL (\r12. match r12 with (r1,r2) -> in_clash_tree tree r1 /\ in_clash_tree tree r2)
         forced
     ==> ?spcol livein flivein.
           select_reg_alloc alg spillcosts k heu_moves tree forced fs = M_success spcol /\
           check_clash_tree (sp_default spcol) tree LN LN = SOME (livein,flivein) /\
           (!r. in_clash_tree tree r
                ==> r IN domain spcol /\
                    (if is_phy_var r then sp_default spcol r = r DIV 2
                     else if is_stack_var r then k <= sp_default spcol r
                     else T)) /\
           (!r. r IN domain spcol ==> in_clash_tree tree r) /\
           ALL (\r12. match r12 with
                        (r1,r2) -> sp_default spcol r1 = sp_default spcol r2 ==> r1 = r2)
               forced`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[select_reg_alloc_def] THEN
  COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`k:num`; `heu_moves:(num#num#num)list`; `tree:clash_tree`;
                   `forced:(num#num)list`] linear_scan_reg_alloc_correct);
    MP_TAC(ISPECL [`if alg <= 1 then reg_alloc_Simple else IRC`;
                   `spillcosts:((num)spt)option`; `k:num`; `heu_moves:(num#num#num)list`;
                   `tree:clash_tree`; `forced:(num#num)list`; `fs:(1)spt`]
             reg_alloc_correct)] THEN
  ASM_REWRITE_TAC[]);;

(* helpers for word_alloc_correct: the colouring is the identity on the     *)
(* physical registers (all that the starting locals contain), and the       *)
(* correctness of applying a colouring from empty live sets                  *)

let WALLOCPAUX_twice_half = prove
 (`!n. is_phy_var n ==> 2 * (n DIV 2) = n`,
  REWRITE_TAC[is_phy_var_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN ASM_ARITH_TAC);;

let WALLOCPAUX_even_locals_rel = prove
 (`!f S (st:(A,C,FFI)wl_state).
     even_starting_locals (wl_state_locals st) /\ (!n. is_phy_var n ==> f n = n)
     ==> strong_locals_rel f S (wl_state_locals st) (wl_state_locals st)`,
  REWRITE_TAC[even_starting_locals_def; strong_locals_rel_def; domain_lookup] THEN
  MESON_TAC[]);;

let WALLOCPAUX_total_colour_even = prove
 (`!col n. every_even_colour col /\ is_phy_var n ==> total_colour col n = n`,
  REWRITE_TAC[every_even_colour_def; total_colour_def; GSYM ALL_MEM] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `lookup n (col:num spt)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `y:num`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  ASM_REWRITE_TAC[option_CASE] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(n:num,y:num)`) THEN
  ASM_REWRITE_TAC[MEM_toAList; pair_CASE] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[WALLOCPAUX_twice_half]);;

let WALLOCPAUX_total_colour_spcol = prove
 (`!spcol tree k.
     (!r. in_clash_tree tree r
          ==> r IN domain spcol /\
              (if is_phy_var r then sp_default spcol r = r DIV 2
               else if is_stack_var r then k <= sp_default spcol r else T)) /\
     (!r. r IN domain spcol ==> in_clash_tree tree r)
     ==> !n. is_phy_var n ==> total_colour spcol n = n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[total_colour_alt; o_THM] THEN
  ASM_CASES_TAC `n IN domain (spcol:num spt)` THENL
   [SUBGOAL_THEN `sp_default spcol n = n DIV 2` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ASM_SIMP_TAC[WALLOCPAUX_twice_half]];
    UNDISCH_TAC `~(n IN domain (spcol:num spt))` THEN
    REWRITE_TAC[GSYM lookup_NONE_domain] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[sp_default_def; option_CASE] THEN
    ASM_SIMP_TAC[WALLOCPAUX_twice_half]]);;

let WALLOCPAUX_colouring_from_check = prove
 (`!(prog:(A)wl_prog) f q r.
     wf_cutsets prog /\ check_clash_tree f (get_clash_tree prog []) LN LN = SOME (q,r)
     ==> colouring_ok f prog LN []`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`; `[]:(num_set#num_set)list`; `f:num->num`;
                 `LN:num_set`; `LN:num_set`; `q:num_set`; `r:num_set`]
    clash_tree_colouring_ok) THEN
  ASM_REWRITE_TAC[word_allocProof_hide_def; wf_def; ALL; domain_def; IMAGE_CLAUSES;
                  INJ; NOT_IN_EMPTY] THEN
  SIMP_TAC[]);;

let WALLOCPAUX_word_alloc_apply = prove
 (CASE_TERM
  `!(prog:(A)wl_prog) (st:(A,C,FFI)wl_state) f.
     colouring_ok f prog LN [] /\
     strong_locals_rel f (domain (get_live prog LN [])) (wl_state_locals st)
       (wl_state_locals st)
     ==> ?perm'.
           let (res,rst) = wl_evaluate (prog,wl_state_permute_fupd (K perm') st) in
           if res = SOME wl_Error then T else
           let (res',rcst) = wl_evaluate (apply_colour f prog,st) in
             res = res' /\
             word_state_eq_rel rst rcst /\
             (match res with
                NONE -> T
              | SOME (wordSem_Break _) -> T
              | SOME (wordSem_Continue _) -> T
              | SOME _ -> wl_state_locals rst = wl_state_locals rcst)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`; `st:(A,C,FFI)wl_state`; `st:(A,C,FFI)wl_state`;
                 `f:num->num`; `LN:num_set`; `[]:(num_set#num_set)list`]
    evaluate_apply_colour) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[word_state_eq_rel_def]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm':num->num->num`
    (fun th -> EXISTS_TAC `perm':num->num->num` THEN MP_TAC th)) THEN
  WALLOCPAUX_TUPLE_TAC
    `wl_evaluate (prog,wl_state_permute_fupd (K perm') (st:(A,C,FFI)wl_state))`
    [`res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; pair_CASE] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (apply_colour f prog,st:(A,C,FFI)wl_state)`
    [`res':((A)wl_result)option`; `rcst:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `res:((A)wl_result)option = res'`)) THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`res:((A)wl_result)option`,`r:((A)wl_result)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM] THEN CONJ_TAC THENL
   [SIMP[];
    GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `a:(A)wl_result` (cases "wl_result")) THEN
    SIMP[]]);;

(* HOL4 line 3399: the full correctness theorem for word_alloc *)
let word_alloc_correct = prove
 (CASE_TERM
  `!fc (c:(A)asm_config) alg (prog:(A)wl_prog) k col_opt (st:(A,C,FFI)wl_state).
     even_starting_locals (wl_state_locals st) /\
     wf_cutsets prog
     ==> ?perm'.
           let (res,rst) = wl_evaluate (prog,wl_state_permute_fupd (K perm') st) in
           if res = SOME wl_Error then T else
           let (res',rcst) = wl_evaluate (word_alloc fc c alg k prog col_opt,st) in
             res = res' /\
             word_state_eq_rel rst rcst /\
             (match res with
                NONE -> T
              | SOME (wordSem_Break _) -> T
              | SOME (wordSem_Continue _) -> T
              | SOME _ -> wl_state_locals rst = wl_state_locals rcst)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[word_alloc_def; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MP_TAC(ISPEC `oracle_colour_ok k col_opt (get_clash_tree (prog:(A)wl_prog) [])
                  prog (get_forced (c:(A)asm_config) prog [])` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `cp:(A)wl_prog`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  REWRITE_TAC[option_CASE] THENL
   [WALLOCPAUX_TUPLE_TAC `get_heuristics alg fc (prog:(A)wl_prog)`
      [`heu_moves:(num#num#num)list`; `spillcosts:((num)spt)option`] THEN
    REWRITE_TAC[pair_CASE] THEN
    MP_TAC(ISPECL [`alg:num`; `spillcosts:((num)spt)option`; `k:num`;
                   `heu_moves:(num#num#num)list`; `get_clash_tree (prog:(A)wl_prog) []`;
                   `get_forced (c:(A)asm_config) (prog:(A)wl_prog) []`;
                   `get_stack_only (prog:(A)wl_prog)`] select_reg_alloc_correct) THEN
    REWRITE_TAC[get_forced_in_get_clash_tree] THEN
    DISCH_THEN(X_CHOOSE_THEN `spcol:num spt` (X_CHOOSE_THEN `livein:num_set`
      (X_CHOOSE_THEN `flivein:num_set` STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[WALLOCPAUX_exc_CASE] THEN
    MATCH_MP_TAC WALLOCPAUX_word_alloc_apply THEN CONJ_TAC THENL
     [MATCH_MP_TAC WALLOCPAUX_colouring_from_check THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`get_clash_tree (prog:(A)wl_prog) []`; `sp_default spcol`;
                     `\x:num. 2 * x`; `LN:num_set`; `LN:num_set`; `LN:num_set`]
        check_clash_tree_INJ) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[INJ; IN_UNIV; domain_def; IMAGE_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[option_CASE; pair_CASE; GSYM total_colour_alt] THEN MESON_TAC[];
      MATCH_MP_TAC WALLOCPAUX_even_locals_rel THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC WALLOCPAUX_total_colour_spcol THEN
      MAP_EVERY EXISTS_TAC [`get_clash_tree (prog:(A)wl_prog) []`; `k:num`] THEN
      ASM_REWRITE_TAC[]];
    UNDISCH_TAC `oracle_colour_ok k col_opt (get_clash_tree (prog:(A)wl_prog) [])
                   prog (get_forced (c:(A)asm_config) prog []) = SOME cp` THEN
    REWRITE_TAC[oracle_colour_ok_def; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    MP_TAC(ISPEC `col_opt:((num)spt)option` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `col:num spt` SUBST1_TAC)) THEN
    REWRITE_TAC[option_CASE; option_DISTINCT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> can (find_term (fun t ->
      try fst(dest_const t) = "every_even_colour" with Failure _ -> false)) (concl th))) THEN
    MATCH_MP_TAC WALLOCPAUX_word_alloc_apply THEN CONJ_TAC THENL
     [MATCH_MP_TAC WALLOCPAUX_colouring_from_check THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `check_clash_tree (total_colour col) (get_clash_tree (prog:(A)wl_prog) [])
                      LN LN` (cases "option")) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[PAIR];
      MATCH_MP_TAC WALLOCPAUX_even_locals_rel THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[WALLOCPAUX_total_colour_even]]]);;

(* HOL4 line 3479 *)
let apply_colour_exp_I = prove
 (`!exp:(A)wl_exp. apply_colour_exp I exp = exp`,
  GEN_TAC THEN
  SUBGOAL_THEN `!f (exp:(A)wl_exp). f = I ==> apply_colour_exp f exp = exp`
    (fun th -> SIMP_TAC[th]) THEN
  MATCH_MP_TAC apply_colour_exp_ind THEN
  REWRITE_TAC[apply_colour_exp_def; injectivity "wl_exp"] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[I_THM] THEN
  REWRITE_TAC[MAP_EQ_ID] THEN ASM_MESON_TAC[]);;

(* HOL4 line 3492 *)
let live_store_rel_def = cake_def
  `live_store_rel (nlive:A list) (sstore:(A,B)fmap) (tstore:(A,B)fmap) <=>
     !n. ~(n IN set_of_list nlive) ==> FLOOKUP sstore n = FLOOKUP tstore n`;;

(* HOL4 line 3499 *)
let live_store_rel_less = prove
 (`!(ls:A list) (st:(A,B)fmap) tt ls'.
     live_store_rel ls st tt /\ set_of_list ls SUBSET set_of_list ls'
     ==> live_store_rel ls' st tt`,
  REWRITE_TAC[live_store_rel_def; SUBSET] THEN MESON_TAC[]);;

(* HOL4 line 3508 *)
let live_store_rel_FLOOKUP_store = prove
 (`!(ls:A list) (sstore:(A,B)fmap) tstore s.
     live_store_rel ls sstore tstore /\ ~(s IN set_of_list ls)
     ==> FLOOKUP tstore s = FLOOKUP sstore s`,
  REWRITE_TAC[live_store_rel_def] THEN MESON_TAC[]);;

(* HOL4 line 3516 *)
let nlive_store_def = sem1aux_def
  `(nlive_store (nlive:store_name list) (wl_Op _ ls:(A)wl_exp) <=>
      ALL (nlive_store nlive) ls) /\
   (nlive_store nlive (Lookup s) <=> ~(s IN set_of_list nlive)) /\
   (nlive_store nlive (wl_Load e) <=> nlive_store nlive e) /\
   (nlive_store nlive (wl_Shift _ e1 e2) <=>
      nlive_store nlive e1 /\ nlive_store nlive e2) /\
   (nlive_store nlive _ <=> T)`;;
let nlive_store_ind = cake_ind "nlive_store";;

(* HOL4 line 3529 *)
let strong_locals_rel_I_get_var = prove
 (`!x (st:(A,C,FFI)wl_state) v live t tstore.
     wl_get_var x st = SOME v /\
     strong_locals_rel I (x INSERT live) (wl_state_locals st) t
     ==> wl_get_var x (wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore) st)) =
         SOME v`,
  REWRITE_TAC[strong_locals_rel_def; wl_get_var_def; I_THM; IN_INSERT] THEN
  SIMP[] THEN MESON_TAC[]);;

(* HOL4 line 3537 *)
let strong_locals_rel_I_get_var' = prove
 (`!x (st:(A,C,FFI)wl_state) v live t.
     wl_get_var x st = SOME v /\
     strong_locals_rel I (x INSERT live) (wl_state_locals st) t
     ==> wl_get_var x (wl_state_locals_fupd (K t) st) = SOME v`,
  REWRITE_TAC[strong_locals_rel_def; wl_get_var_def; I_THM; IN_INSERT] THEN
  SIMP[] THEN MESON_TAC[]);;

(* helper: memory loads do not depend on locals and store *)

let WALLOCPAUX_mem_load_fupd = prove
 (`!w t tstore (s:(A,C,FFI)wl_state).
     wl_mem_load w (wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore) s)) =
     wl_mem_load w s`,
  SIMP[wl_mem_load_def]);;

(* HOL4 line 3545 *)
let strong_locals_rel_I_word_exp = prove
 (`!(st:(A,C,FFI)wl_state) exp res live t nlive tstore.
     wl_word_exp st exp = SOME res /\
     strong_locals_rel I (domain (union (get_live_exp exp) live)) (wl_state_locals st) t /\
     live_store_rel nlive (wl_state_store st) tstore /\
     nlive_store nlive exp
     ==> wl_word_exp (wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore) st)) exp =
         SOME res`,
  MATCH_MP_TAC wl_word_exp_ind THEN
  REWRITE_TAC[wl_word_exp_def; get_live_exp_def; nlive_store_def] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    REWRITE_TAC[wl_get_var_def; strong_locals_rel_def; domain_union; domain_insert;
                IN_UNION; IN_INSERT; I_THM] THEN SIMP[] THEN MESON_TAC[];
    REWRITE_TAC[wl_get_store_def; live_store_rel_def] THEN SIMP[] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[option_case_eq; case_eq "word_loc"; option_DISTINCT] THEN
    STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[WALLOCPAUX_mem_load_fupd];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[option_case_eq; option_DISTINCT] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `MAP (wl_word_exp (wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore)
            (s:(A,C,FFI)wl_state)))) wexps =
      MAP (wl_word_exp s) (wexps:((A)wl_exp)list)`
      SUBST1_TAC THENL
     [MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
      X_GEN_TAC `e:(A)wl_exp` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP the_words_EVERY_IS_SOME) THEN
      REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN
      DISCH_THEN(MP_TAC o SPEC `wl_word_exp (s:(A,C,FFI)wl_state) e`) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IS_SOME_EXISTS] THEN
      DISCH_THEN(X_CHOOSE_TAC `r:(A)word_loc`) THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:(A)wl_exp`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      EXISTS_TAC `live:num_set` THEN EXISTS_TAC `nlive:store_name list` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC strong_locals_rel_subset THEN
        EXISTS_TAC `domain (union (big_union (MAP get_live_exp
                                     (wexps:((A)wl_exp)list))) (live:num_set))` THEN
        ASM_REWRITE_TAC[domain_union] THEN
        MP_TAC(ISPECL [`wexps:((A)wl_exp)list`; `e:(A)wl_exp`]
          domain_big_union_subset) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN ASM_MESON_TAC[]];
      ASM_MESON_TAC[]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[option_case_eq; case_eq "word_loc"; option_DISTINCT] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[domain_union; strong_locals_rel_UNION]) THEN
    ASM_MESON_TAC[]]);;

(* HOL4 line 3612 *)
let strong_locals_rel_insert_notin = prove
 (`!f live (s:A spt) t n v.
     strong_locals_rel f live s t /\ ~(n IN live)
     ==> strong_locals_rel f live (insert n v s) t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[strong_locals_rel_def; lookup_insert] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`m:num`; `w:A`] THEN
  ASM_CASES_TAC `m:num = n` THEN ASM_MESON_TAC[]);;

(* HOL4 line 3621 *)
let strong_locals_rel_I_get_vars' = prove
 (`!ls live (st:(A,C,FFI)wl_state) t vs.
     (!x. MEM x ls ==> x IN live) /\
     strong_locals_rel I live (wl_state_locals st) t /\
     wl_get_vars ls st = SOME vs
     ==> wl_get_vars ls (wl_state_locals_fupd (K t) st) = SOME vs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ls:num list`; `vs:((A)word_loc)list`; `I:num->num`; `live:num->bool`;
                 `st:(A,C,FFI)wl_state`; `wl_state_locals_fupd (K t) (st:(A,C,FFI)wl_state)`]
    strong_locals_rel_get_vars) THEN
  SIMP[MAP_I; I_THM]);;

(* helper: cut_names only reads the cut-set part of the locals *)

let WALLOCPAUX_cut_names_I = prove
 (`!(n:B spt) (env:A spt) t x.
     strong_locals_rel I (domain n) env t /\ cut_names n env = SOME x
     ==> cut_names n t = SOME x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_names_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `domain (n:B spt) SUBSET domain (t:A spt)` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `strong_locals_rel I (domain (n:B spt)) (env:A spt) t` THEN
    UNDISCH_TAC `domain (n:B spt) SUBSET domain (env:A spt)` THEN
    REWRITE_TAC[strong_locals_rel_def; SUBSET; domain_lookup; I_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[option_INJ] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_var o rhs o concl)) THEN
  SIMP_TAC[spt_eq_thm; wf_inter] THEN REWRITE_TAC[lookup_inter_alt] THEN
  X_GEN_TAC `k:num` THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `?v. lookup k (env:A spt) = SOME v` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; domain_lookup]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[strong_locals_rel_def; I_THM]) THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 3640 *)
let strong_locals_rel_I_cut_envs = prove
 (`!(cutset:num_set#num_set) (st:(A,C,FFI)wl_state) t x.
     strong_locals_rel I (domain (FST cutset) UNION domain (SND cutset))
       (wl_state_locals st) t /\
     cut_envs cutset (wl_state_locals st) = SOME x
     ==> cut_envs cutset t = SOME x`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?n1 n2. cutset:num_set#num_set = (n1,n2)`
    (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC)) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `?x1 x2. x:((A)word_loc)spt#((A)word_loc)spt = (x1,x2)`
    (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC)) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  REWRITE_TAC[FST; SND; WALLOCPAUX_cut_envs_SOME; strong_locals_rel_UNION] THEN
  MESON_TAC[WALLOCPAUX_cut_names_I]);;

(* HOL4 line 3656 *)
let strong_locals_rel_I_cut_env = prove
 (`!(cutset:num_set#num_set) (st:(A,C,FFI)wl_state) t x.
     strong_locals_rel I (domain (FST cutset) UNION domain (SND cutset))
       (wl_state_locals st) t /\
     wl_cut_env cutset (wl_state_locals st) = SOME x
     ==> wl_cut_env cutset t = SOME x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WALLOCPAUX_cut_env_SOME] THEN
  MESON_TAC[strong_locals_rel_I_cut_envs]);;

(* HOL4 line 3668: get_vars_eq *)
let word_allocProof_get_vars_eq = prove
 (`!ls (st:(A,C,FFI)wl_state).
     set_of_list ls SUBSET domain (wl_state_locals st)
     ==> ?z. wl_get_vars ls st = SOME z /\
             z = MAP (\x. THE (lookup x (wl_state_locals st))) ls`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[wl_get_vars_def; set_of_list; MAP; EMPTY_SUBSET; INSERT_SUBSET;
              wl_get_var_def] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `st:(A,C,FFI)wl_state` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `st:(A,C,FFI)wl_state`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?v. lookup h (wl_state_locals (st:(A,C,FFI)wl_state)) = SOME v`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[domain_lookup]; ALL_TAC] THEN
  ASM_REWRITE_TAC[option_CASE; THE_DEF; option_INJ] THEN MESON_TAC[]);;

(* HOL4 line 3676 *)
let get_vars_exists = prove
 (`!(st:(A,C,FFI)wl_state) ls.
     (?z. wl_get_vars ls st = SOME z) <=> set_of_list ls SUBSET domain (wl_state_locals st)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[wl_get_vars_def; set_of_list; EMPTY_SUBSET; INSERT_SUBSET;
              wl_get_var_def; option_INJ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[domain_lookup] THEN
  CASES_ON `lookup h (wl_state_locals (st:(A,C,FFI)wl_state))` THEN
  ASM_REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_iff o concl)) THEN
  CASES_ON `wl_get_vars t (st:(A,C,FFI)wl_state)` THEN
  ASM_REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

(* HOL4 line 3685 *)
let strong_locals_rel_I_insert_insert = prove
 (`!live p (A:B spt) B v v'.
     strong_locals_rel I (live DELETE p) A B /\ v = v'
     ==> strong_locals_rel I live (insert p v A) (insert p v' B)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[strong_locals_rel_def; lookup_insert; I_THM; IN_DELETE] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`m:num`; `w:B`] THEN
  ASM_CASES_TAC `m:num = p` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 3694 [simp] *)
let st_eq = prove
 (`!(rst:(A,C,FFI)wl_state) t tstore t' tstore'.
     wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore) rst) =
     wl_state_locals_fupd (K t') (wl_state_store_fupd (K tstore') rst) <=>
     t = t' /\ tstore = tstore'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_state_component_equality] THEN
  SIMP[] THEN MESON_TAC[]);;
let _ = cake_add_simps [st_eq];;

(* HOL4 line 3702 [simp] *)
let live_store_rel_NIL = prove
 (`!(sstore:(A,B)fmap) tstore. live_store_rel [] sstore tstore <=> sstore = tstore`,
  REWRITE_TAC[live_store_rel_def; set_of_list; NOT_IN_EMPTY; GSYM fmap_eq_flookup]);;
let _ = cake_add_simps [live_store_rel_NIL];;

(* HOL4 line 3710 [simp] *)
let live_store_rel_refl = prove
 (`!(ls:A list) (sstore:(A,B)fmap). live_store_rel ls sstore sstore`,
  REWRITE_TAC[live_store_rel_def]);;
let _ = cake_add_simps [live_store_rel_refl];;

(* HOL4 line 3716 [simp] *)
let with_same_store = prove
 (`!st:(A,C,FFI)wl_state. wl_state_store_fupd (K (wl_state_store st)) st = st`,
  GEN_TAC THEN REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;
let _ = cake_add_simps [with_same_store];;

(* HOL4 line 3722 [simp]: with_same_locals *)
let word_allocProof_with_same_locals = prove
 (`!st:(A,C,FFI)wl_state. wl_state_locals_fupd (K (wl_state_locals st)) st = st`,
  GEN_TAC THEN REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;
let _ = cake_add_simps [word_allocProof_with_same_locals];;

(* helper: complete induction on the clock of a state *)

let WALLOCPAUX_flush_state_locals = prove
 (`!b t (s:(A,C,FFI)wl_state).
     wl_flush_state b (wl_state_locals_fupd (K t) s) = wl_flush_state b s`,
  REWRITE_TAC[FORALL_BOOL_THM; wl_flush_state_def] THEN SIMP[]);;

let WALLOCPAUX_strong_locals_rel_I_refl = prove
 (`!ls (x:A spt). strong_locals_rel I ls x x`,
  REWRITE_TAC[strong_locals_rel_def; I_THM] THEN MESON_TAC[]);;

let WALLOCPAUX_rd_concl_refl = prove
 (CASE_TERM
  `!(res:((A)wl_result)option) (rst:(A,C,FFI)wl_state) (live:1 spt) nlive
    (lt:(1 spt#1 spt)list).
     (match res with
        NONE ->
          strong_locals_rel I (domain live) (wl_state_locals rst) (wl_state_locals rst) /\
          live_store_rel nlive (wl_state_store rst) (wl_state_store rst)
      | SOME (wordSem_Break n) ->
          wl_state_store rst = wl_state_store rst /\
          (match oEL n lt with
             SOME (_,exit_names) ->
               strong_locals_rel I (domain exit_names) (wl_state_locals rst)
                 (wl_state_locals rst)
           | NONE -> T)
      | SOME (wordSem_Continue n) ->
          wl_state_store rst = wl_state_store rst /\
          (match oEL n lt with
             SOME (names,_) ->
               strong_locals_rel I (domain names) (wl_state_locals rst) (wl_state_locals rst)
           | NONE -> T)
      | SOME _ -> wl_state_locals rst = wl_state_locals rst /\
                  wl_state_store rst = wl_state_store rst)`,
  REWRITE_TAC[FORALL_OPTION_THM] THEN CONJ_TAC THENL
   [SIMP[WALLOCPAUX_strong_locals_rel_I_refl; live_store_rel_refl]; ALL_TAC] THEN
  GEN_TAC THEN CASES_ON `a:(A)wl_result` THEN
  SIMP[WALLOCPAUX_strong_locals_rel_I_refl] THEN
  REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN SIMP[]);;

(* HOL4 line 3728 *)
let evaluate_remove_dead_Loop_helper = prove
 (CASE_TERM
  `!(st:(A,C,FFI)wl_state) t tstore names body exit_names
    live nlive lt prog' livein nlivein res rst.
     strong_locals_rel I (domain livein) (wl_state_locals st) t /\
     live_store_rel nlivein (wl_state_store st) tstore /\
     wl_evaluate (wl_Loop names body exit_names,st) = (res,rst) /\
     flat_exp_conventions body /\
     remove_dead (wl_Loop names body exit_names) live nlive lt = (prog',livein,nlivein) /\
     nlivein = [] /\
     ~(res = SOME wl_Error) /\
     (!(st':(A,C,FFI)wl_state) t' tstore' prog'' livein' nlivein' res' rst'.
        strong_locals_rel I (domain livein') (wl_state_locals st') t' /\
        live_store_rel nlivein' (wl_state_store st') tstore' /\
        wl_evaluate (body,st') = (res',rst') /\
        remove_dead body names [] (CONS (names,exit_names) lt) =
          (prog'',livein',nlivein') /\
        ~(res' = SOME wl_Error)
        ==> ?t'' tstore''.
              wl_evaluate
                (prog'',wl_state_locals_fupd (K t') (wl_state_store_fupd (K tstore') st')) =
                (res',wl_state_locals_fupd (K t'') (wl_state_store_fupd (K tstore'') rst')) /\
              (match res' with
                 NONE ->
                   strong_locals_rel I (domain names) (wl_state_locals rst') t'' /\
                   live_store_rel [] (wl_state_store rst') tstore''
               | SOME (wordSem_Break n) ->
                   wl_state_store rst' = tstore'' /\
                   (match oEL n (CONS (names,exit_names) lt) with
                      SOME (_,exit_names) ->
                        strong_locals_rel I (domain exit_names) (wl_state_locals rst') t''
                    | NONE -> T)
               | SOME (wordSem_Continue n) ->
                   wl_state_store rst' = tstore'' /\
                   (match oEL n (CONS (names,exit_names) lt) with
                      SOME (names,_) ->
                        strong_locals_rel I (domain names) (wl_state_locals rst') t''
                    | NONE -> T)
               | SOME _ -> wl_state_locals rst' = t'' /\ wl_state_store rst' = tstore''))
     ==> ?t' tstore'.
           wl_evaluate (prog',wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore) st)) =
           (res,wl_state_locals_fupd (K t') (wl_state_store_fupd (K tstore') rst)) /\
           (match res with
              NONE ->
                strong_locals_rel I (domain live) (wl_state_locals rst) t' /\
                live_store_rel nlive (wl_state_store rst) tstore'
            | SOME (wordSem_Break n) ->
                wl_state_store rst = tstore' /\
                (match oEL n lt with
                   SOME (_,exit_names) ->
                     strong_locals_rel I (domain exit_names) (wl_state_locals rst) t'
                 | NONE -> T)
            | SOME (wordSem_Continue n) ->
                wl_state_store rst = tstore' /\
                (match oEL n lt with
                   SOME (names,_) ->
                     strong_locals_rel I (domain names) (wl_state_locals rst) t'
                 | NONE -> T)
            | SOME _ -> wl_state_locals rst = t' /\ wl_state_store rst = tstore')`,
  MATCH_MP_TAC WALLOCPAUX_clock_induct THEN
  X_GEN_TAC `st:(A,C,FFI)wl_state` THEN DISCH_THEN(LABEL_TAC "cih") THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[remove_dead_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC
    `remove_dead body names [] (CONS (names,exit_names) (lt:(1 spt#1 spt)list))
       :(A)wl_prog#1 spt#store_name list`
    [`body':(A)wl_prog`; `bl:1 spt`; `bnl:store_name list`] THEN
  REWRITE_TAC[pair_CASE; PAIR_EQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  STRIP_TAC THEN POP_ASSUM(LABEL_TAC "bih") THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
               check (fun th -> is_eq(concl th) && rhs(concl th) = v)))
    [`prog':(A)wl_prog`; `livein:1 spt`; `nlivein:store_name list`] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `[]:store_name list = []`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o REWRITE_RULE[live_store_rel_NIL] o
    check (fun th -> can (term_match [] `live_store_rel [] (x:(store_name,(A)word_loc)fmap) y`)
                         (concl th))) THEN
  REWRITE_TAC[with_same_store] THEN
  UNDISCH_TAC `wl_evaluate (wl_Loop names body exit_names,st:(A,C,FFI)wl_state) = (res,rst)` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  MP_TAC(ISPEC `wl_cut_env (names,LN) (wl_state_locals (st:(A,C,FFI)wl_state))`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `env:((A)word_loc)spt` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[wl_cut_state_def; option_CASE] THENL
   [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wl_cut_env (names,LN) t = SOME (env:((A)word_loc)spt)` ASSUME_TAC THENL
   [MATCH_MP_TAC strong_locals_rel_I_cut_env THEN EXISTS_TAC `st:(A,C,FFI)wl_state` THEN
    ASM_REWRITE_TAC[domain_def; UNION_EMPTY; FST; SND];
    ALL_TAC] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds; K_THM; K_o_THM] THEN
  ASM_REWRITE_TAC[option_CASE] THEN
  WALLOCPAUX_TUPLE_TAC
    `wl_evaluate (body,wl_state_locals_fupd (K env) (st:(A,C,FFI)wl_state))`
    [`res1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(res1 = SOME (wl_Error:(A)wl_result))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
    SIMP[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "bih" (MP_TAC o SPECL [`wl_state_locals_fupd (K env) (st:(A,C,FFI)wl_state)`;
    `env:((A)word_loc)spt`; `wl_state_store (st:(A,C,FFI)wl_state)`; `body':(A)wl_prog`;
    `bl:1 spt`; `bnl:store_name list`; `res1:((A)wl_result)option`;
    `s1:(A,C,FFI)wl_state`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SIMP[WALLOCPAUX_strong_locals_rel_I_refl; live_store_rel_refl];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wl_state_locals_fupd (K env) (wl_state_store_fupd (K (wl_state_store st))
      (wl_state_locals_fupd (K env) (st:(A,C,FFI)wl_state))) =
    wl_state_locals_fupd (K env) st` SUBST1_TAC THENL
   [REWRITE_TAC[wl_state_component_equality] THEN SIMP[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:((A)word_loc)spt` (X_CHOOSE_THEN
    `ts1:(store_name,(A)word_loc)fmap` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  ASM_CASES_TAC `wl_cont_loop (res1:((A)wl_result)option)` THENL
   [SUBGOAL_THEN `strong_locals_rel I (domain (names:1 spt)) (wl_state_locals (s1:(A,C,FFI)wl_state)) t1 /\
                  ts1 = wl_state_store s1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `wl_cont_loop (res1:((A)wl_result)option)` THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        can (find_term (fun tm -> try fst(dest_const tm) = "oEL" with Failure _ -> false))
            (concl th))) THEN
      SPEC_TAC(`res1:((A)wl_result)option`, `r:((A)wl_result)option`) THEN
      REWRITE_TAC[FORALL_OPTION_THM] THEN CONJ_TAC THENL
       [SIMP[live_store_rel_NIL];
        GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `a:(A)wl_result` (cases "wl_result")) THEN
        SIMP[oEL_DEF] THEN
        ONCE_REWRITE_TAC[TAUT `(a ==> b ==> c) <=> (b ==> a ==> c)`] THEN
        DISCH_THEN SUBST1_TAC THEN SIMP[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `ts1:(store_name,(A)word_loc)fmap`)) THEN
    REWRITE_TAC[wl_state_INFO.ri_accfupds; WALLOCPAUX_flush_state_locals; with_same_store] THEN
    ASM_CASES_TAC `wl_state_clock (s1:(A,C,FFI)wl_state) = 0` THEN ASM_REWRITE_TAC[] THENL
     [MAP_EVERY EXISTS_TAC [`wl_state_locals (rst:(A,C,FFI)wl_state)`;
                            `wl_state_store (rst:(A,C,FFI)wl_state)`] THEN
      REWRITE_TAC[WALLOCPAUX_rd_concl_refl; word_allocProof_with_same_locals; with_same_store] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
    ASM_REWRITE_TAC[wl_STOP_def] THEN DISCH_TAC THEN
    SUBGOAL_THEN `wl_state_clock (wl_dec_clock (s1:(A,C,FFI)wl_state)) <
                  wl_state_clock (st:(A,C,FFI)wl_state)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`body:(A)wl_prog`; `wl_state_locals_fupd (K env) (st:(A,C,FFI)wl_state)`;
                     `res1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] wl_evaluate_clock) THEN
      ASM_REWRITE_TAC[wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
      UNDISCH_TAC `~(wl_state_clock (s1:(A,C,FFI)wl_state) = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN
    REMOVE_THEN "cih" (MP_TAC o SPEC `wl_dec_clock (s1:(A,C,FFI)wl_state)`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`t1:((A)word_loc)spt`; `wl_state_store (s1:(A,C,FFI)wl_state)`;
      `names:1 spt`; `body:(A)wl_prog`; `exit_names:1 spt`; `live:1 spt`;
      `nlive:store_name list`; `lt:(1 spt#1 spt)list`;
      `wl_Loop names body' exit_names:(A)wl_prog`; `names:1 spt`;
      `[]:store_name list`; `res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[remove_dead_def; LET_DEF; LET_END_DEF] THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[pair_CASE; PAIR_EQ] THEN
      REWRITE_TAC[wl_dec_clock_def; wl_state_INFO.ri_accfupds; live_store_rel_NIL] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `wl_dec_clock (wl_state_locals_fupd (K t1) (s1:(A,C,FFI)wl_state)) =
      wl_state_locals_fupd (K t1) (wl_state_store_fupd (K (wl_state_store s1))
        (wl_dec_clock s1))` SUBST1_TAC THENL
     [REWRITE_TAC[wl_state_component_equality; wl_dec_clock_def] THEN SIMP[]; ALL_TAC] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `res1 = SOME (wordSem_Break 0:(A)wl_result)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `strong_locals_rel I (domain (exit_names:1 spt))
                    (wl_state_locals (s1:(A,C,FFI)wl_state)) t1 /\
                  ts1 = wl_state_store s1` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th ->
        can (find_term (fun tm -> try fst(dest_const tm) = "oEL" with Failure _ -> false))
            (concl th))) THEN
      SIMP[oEL_DEF] THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      lhs(concl th) = `ts1:(store_name,(A)word_loc)fmap`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `wl_cut_env (exit_names,LN) (wl_state_locals (s1:(A,C,FFI)wl_state))`
      (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `env2:((A)word_loc)spt` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[option_CASE] THENL
     [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `wl_cut_env (exit_names,LN) t1 = SOME (env2:((A)word_loc)spt)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC strong_locals_rel_I_cut_env THEN EXISTS_TAC `s1:(A,C,FFI)wl_state` THEN
      ASM_REWRITE_TAC[domain_def; UNION_EMPTY; FST; SND];
      ALL_TAC] THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`env2:((A)word_loc)spt`; `wl_state_store (s1:(A,C,FFI)wl_state)`] THEN
    ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds; K_THM; K_o_THM;
                    option_CASE; with_same_store] THEN
    REWRITE_TAC[WALLOCPAUX_strong_locals_rel_I_refl; live_store_rel_refl; PAIR_EQ] THEN
    REWRITE_TAC[wl_state_component_equality] THEN SIMP[];
    ALL_TAC] THEN
  REMOVE_THEN "cih" (K ALL_TAC) THEN REMOVE_THEN "bih" (K ALL_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  MAP_EVERY EXISTS_TAC [`t1:((A)word_loc)spt`; `ts1:(store_name,(A)word_loc)fmap`] THEN
  REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun tm -> try fst(dest_const tm) = "oEL" with Failure _ -> false))
        (concl th))) THEN
  UNDISCH_TAC `~(res1 = SOME (wordSem_Break 0:(A)wl_result))` THEN
  UNDISCH_TAC `~wl_cont_loop (res1:((A)wl_result)option)` THEN
  SPEC_TAC(`res1:((A)wl_result)option`, `r:((A)wl_result)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM] THEN CONJ_TAC THENL
   [SIMP[];
    GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `a:(A)wl_result` (cases "wl_result")) THEN
    SIMP[oEL_DEF]]);;

(* helper: the statement of evaluate_remove_dead for one program, as a     *)
(* predicate, so that each case of the induction on remove_dead is a lemma *)

let WALLOCPAUX_rd_Q_def = new_definition (CASE_TERM
 `WALLOCPAUX_rd_Q (st:(A,C,FFI)wl_state) (prog:(A)wl_prog) (live:1 spt)
                  (nlive:store_name list) (lt:(1 spt#1 spt)list) <=>
   !prog' livein nlivein t tstore res rst.
     strong_locals_rel I (domain livein) (wl_state_locals st) t /\
     live_store_rel nlivein (wl_state_store st) tstore /\
     wl_evaluate (prog,st) = (res,rst) /\
     flat_exp_conventions prog /\
     remove_dead prog live nlive lt = (prog',livein,nlivein) /\
     ~(res = SOME wl_Error)
     ==> ?t' tstore'.
           wl_evaluate (prog',wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore) st)) =
           (res,wl_state_locals_fupd (K t') (wl_state_store_fupd (K tstore') rst)) /\
           (match res with
              NONE ->
                strong_locals_rel I (domain live) (wl_state_locals rst) t' /\
                live_store_rel nlive (wl_state_store rst) tstore'
            | SOME (wordSem_Break n) ->
                wl_state_store rst = tstore' /\
                (match oEL n lt with
                   SOME (_,exit_names) ->
                     strong_locals_rel I (domain exit_names) (wl_state_locals rst) t'
                 | NONE -> T)
            | SOME (wordSem_Continue n) ->
                wl_state_store rst = tstore' /\
                (match oEL n lt with
                   SOME (names,_) ->
                     strong_locals_rel I (domain names) (wl_state_locals rst) t'
                 | NONE -> T)
            | SOME _ -> wl_state_locals rst = t' /\ wl_state_store rst = tstore')`);;

(* helpers: a sequence whose first part ends normally or not               *)

(* helpers: jump_exc and flush_state ignore the current locals *)

let WALLOCPAUX_jump_exc_locals = prove
 (`!t (s:(A,C,FFI)wl_state). wl_jump_exc (wl_state_locals_fupd (K t) s) = wl_jump_exc s`,
  REWRITE_TAC[wl_jump_exc_def] THEN SIMP[]);;

let WALLOCPAUX_pop_env_locals = prove
 (`!t (s:(A,C,FFI)wl_state). wl_pop_env (wl_state_locals_fupd (K t) s) = wl_pop_env s`,
  REWRITE_TAC[wl_pop_env_def] THEN SIMP[]);;

let WALLOCPAUX_push_env_locals = prove
 (`!envs (h:(num#(A)wl_prog#num#num)option) t (s:(A,C,FFI)wl_state).
     wl_push_env envs h (wl_state_locals_fupd (K t) s) =
     wl_state_locals_fupd (K t) (wl_push_env envs h s)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[wl_push_env_def] THEN SIMP[] THEN REPEAT STRIP_TAC THEN
  EVERY_CASE_TAC THEN SIMP[]);;

let WALLOCPAUX_set_store_locals = prove
 (`!v x t (s:(A,C,FFI)wl_state).
     wl_set_store v x (wl_state_locals_fupd (K t) s) =
     wl_state_locals_fupd (K t) (wl_set_store v x s)`,
  REWRITE_TAC[wl_set_store_def] THEN SIMP[]);;

let WALLOCPAUX_gc_locals = prove
 (`!t (s:(A,C,FFI)wl_state).
     wl_gc (wl_state_locals_fupd (K t) s) = OPTION_MAP (wl_state_locals_fupd (K t)) (wl_gc s)`,
  REWRITE_TAC[wl_gc_def] THEN SIMP[] THEN REPEAT STRIP_TAC THEN
  EVERY_CASE_TAC THEN SIMP[]);;

let WALLOCPAUX_alloc_locals = prove
 (`!w names t (s:(A,C,FFI)wl_state).
     cut_envs names t = cut_envs names (wl_state_locals s)
     ==> wl_alloc w names (wl_state_locals_fupd (K t) s) = wl_alloc w names s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_alloc_def] THEN SIMP[] THEN ASM_REWRITE_TAC[]);;

let WALLOCPAUX_call_env_locals = prove
 (`!args ss t (s:(A,C,FFI)wl_state).
     wl_call_env args ss (wl_dec_clock (wl_state_locals_fupd (K t) s)) =
     wl_call_env args ss (wl_dec_clock s)`,
  REWRITE_TAC[wl_call_env_def; wl_dec_clock_def] THEN SIMP[]);;

let WALLOCPAUX_get_var_I = prove
 (`!x ls (st:(A,C,FFI)wl_state) t tstore v.
     x IN ls /\ strong_locals_rel I ls (wl_state_locals st) t /\ wl_get_var x st = SOME v
     ==> wl_get_var x (wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore) st)) =
         SOME v`,
  REWRITE_TAC[strong_locals_rel_def; wl_get_var_def; I_THM] THEN SIMP[] THEN MESON_TAC[]);;

(* the conclusion of WALLOCPAUX_rd_Q holds when the final target locals and *)
(* store are those of the source *)

(* helpers for the Move case: a move writes, at each destination, the value *)
(* of its (first) source; the live filter of remove_dead and lookups        *)

let WALLOCPAUX_lookup_moves = prove
 (CASE_TERM
  `!(ls:(num#num)list) vs (L:((A)word_loc)spt) (s:(A,C,FFI)wl_state) n.
     wl_get_vars (MAP SND ls) s = SOME vs
     ==> lookup n (alist_insert (MAP FST ls) vs L) =
         (match ALOOKUP ls n with
            SOME y -> lookup y (wl_state_locals s)
          | NONE -> lookup n L)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP; wl_get_vars_def; option_INJ] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[alist_insert_def; ALOOKUP_THM; option_CASE];
    ALL_TAC] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN
  REWRITE_TAC[MAP; wl_get_vars_def] THEN REPEAT GEN_TAC THEN
  SIMP[option_case_eq] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `vs:((A)word_loc)list`)) THEN
  REWRITE_TAC[alist_insert_def; ALOOKUP_THM; lookup_insert] THEN
  ASM_CASES_TAC `n:num = a` THEN ASM_REWRITE_TAC[option_CASE] THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_get_var" with Failure _ -> false)) THEN
    REWRITE_TAC[wl_get_var_def] THEN MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let WALLOCPAUX_get_vars_locals_store = prove
 (`!ls t tstore (s:(A,C,FFI)wl_state).
     wl_get_vars ls (wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore) s)) =
     wl_get_vars ls (wl_state_locals_fupd (K t) s)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[wl_get_vars_def; wl_get_var_def] THEN SIMP[]);;

let WALLOCPAUX_ALOOKUP_FILTER_live = prove
 (CASE_TERM
  `!(ls:(num#num)list) (live:1 spt) n.
     ALOOKUP (FILTER (\xy. match xy with (x,y) -> lookup x live = SOME one) ls) n =
     if lookup n live = SOME one then ALOOKUP ls n else NONE`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; ALOOKUP_THM; COND_ID] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `live:1 spt`; `n:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  ASM_CASES_TAC `lookup a (live:1 spt) = SOME one` THEN
  ASM_REWRITE_TAC[ALOOKUP_THM] THEN
  ASM_CASES_TAC `a:num = n` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a:num = n`)) THEN
  ASM_REWRITE_TAC[]);;

let WALLOCPAUX_ALL_DISTINCT_FILTER_live = prove
 (CASE_TERM
  `!(ls:(num#num)list) (live:1 spt).
     ALL_DISTINCT (MAP FST ls)
     ==> ALL_DISTINCT (MAP FST (FILTER (\xy. match xy with (x,y) -> lookup x live = SOME one)
                                  ls))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; MAP; ALL_DISTINCT] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `live:1 spt`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[MAP; ALL_DISTINCT] THEN
  UNDISCH_TAC `~MEM (a:num) (MAP FST (t:(num#num)list))` THEN
  REWRITE_TAC[MEM_MAP; MEM_FILTER] THEN MESON_TAC[]);;

let WALLOCPAUX_MEM_FILTER_live = prove
 (CASE_TERM
  `!(ls:(num#num)list) (live:1 spt) x y.
     MEM (x,y) (FILTER (\xy. match xy with (x,y) -> lookup x live = SOME one) ls) <=>
     MEM (x,y) ls /\ lookup x live = SOME one`,
  REWRITE_TAC[MEM_FILTER; pair_CASE] THEN MESON_TAC[]);;

(* helpers for the Inst case: case splits on instructions, and an          *)
(* instruction that remove_dead deletes only writes dead registers          *)

(* from the assumption strong_locals_rel I S (wl_state_locals st) t, derive *)
(* lookup r t = SOME v for every assumption lookup r (wl_state_locals st) =  *)
(* SOME v whose register is (visibly) in S                                  *)

let WALLOCPAUX_TRANSFER_TAC : tactic =
  fun (asl,w as g) ->
    let hd_name tm = try fst(dest_const(fst(strip_comb tm))) with Failure _ -> "" in
    let slrs = filter (fun (_,th) -> hd_name (concl th) = "strong_locals_rel") asl in
    let tac_for (_,slr) =
      let args = snd(strip_comb(concl slr)) in
      let locs = el 2 args and t = el 3 args in
      let facts = filter (fun (_,th) ->
          let c = concl th in
          is_eq c && hd_name (lhs c) = "lookup" &&
          (try rand(lhs c) = locs with Failure _ -> false) &&
          hd_name (rhs c) = "SOME") asl in
      MAP_EVERY (fun (_,f) ->
          let goal = subst [t,locs] (concl f) in
          if exists (fun (_,a) -> concl a = goal) asl then ALL_TAC else
          TRY (SUBGOAL_THEN goal ASSUME_TAC THENL
                [MP_TAC slr THEN REWRITE_TAC[strong_locals_rel_def; I_THM] THEN
                 DISCH_THEN MATCH_MP_TAC THEN
                 ASM_REWRITE_TAC[domain_insert; domain_delete; domain_union; IN_INSERT;
                                 IN_DELETE; IN_UNION] THEN NO_TAC;
                 ALL_TAC])) facts in
    EVERY (map tac_for slrs) g;;

(* the same for cut_env: from wl_cut_env c (wl_state_locals st) = SOME e    *)
(* derive wl_cut_env c t = SOME e when the cut set is (visibly) in S        *)

let WALLOCPAUX_TRANSFER_CUT_TAC : tactic =
  fun (asl,w as g) ->
    let hd_name tm = try fst(dest_const(fst(strip_comb tm))) with Failure _ -> "" in
    let slrs = filter (fun (_,th) -> hd_name (concl th) = "strong_locals_rel") asl in
    match slrs with
      [] -> ALL_TAC g
    | (_,slr)::_ ->
      let args = snd(strip_comb(concl slr)) in
      let locs = el 2 args and t = el 3 args in
      let facts = filter (fun (_,th) ->
          let c = concl th in
          is_eq c && hd_name (lhs c) = "wl_cut_env" &&
          (try rand(lhs c) = locs with Failure _ -> false)) asl in
      MAP_EVERY (fun (_,f) ->
          let goal = subst [t,locs] (concl f) in
          TRY (SUBGOAL_THEN goal ASSUME_TAC THENL
                [MATCH_MP_TAC strong_locals_rel_I_cut_env THEN EXISTS_TAC (rand locs) THEN
                 CONJ_TAC THENL
                  [MATCH_MP_TAC strong_locals_rel_subset THEN EXISTS_TAC (el 1 args) THEN
                   ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_INSERT; IN_UNION] THEN
                   MESON_TAC[];
                   ASM_REWRITE_TAC[]] THEN NO_TAC;
                 ALL_TAC])) facts g;;

(* close strong_locals_rel I S' x' y' from an assumption strong_locals_rel   *)
(* I S x y, after peeling the inserts that both sides share                 *)

let WALLOCPAUX_SLR_FINISH_TAC : tactic =
  let hd_name tm = try fst(dest_const(fst(strip_comb tm))) with Failure _ -> "" in
  REPEAT(MATCH_MP_TAC strong_locals_rel_I_insert_insert THEN REWRITE_TAC[]) THEN
  FIRST_ASSUM(fun th ->
    if hd_name (concl th) = "strong_locals_rel" then
      MATCH_MP_TAC strong_locals_rel_subset THEN
      EXISTS_TAC (el 1 (snd(strip_comb(concl th)))) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_INSERT; IN_DELETE; IN_UNION; domain_insert; domain_delete] THEN
      MESON_TAC[]
    else NO_TAC);;

let WALLOCPAUX_EX_LOCALS_TAC : tactic =
  fun (asl,w as g) ->
    let v,bod = dest_exists w in
    let eq = fst(dest_conj bod) in
    let l = lhs eq in
    EXISTS_TAC (rand(rand(rator l))) g;;

let WALLOCPAUX_inst_dead = prove
 (`!i (live:1 spt) (st:(A,C,FFI)wl_state) s1.
     remove_dead_inst i live /\ wl_inst i st = SOME s1
     ==> ?L. s1 = wl_state_locals_fupd (K L) st /\
             (!n. n IN domain live ==> lookup n L = lookup n (wl_state_locals st))`,
  GEN_TAC THEN WALLOCPAUX_INST_CASES_TAC THEN
  REWRITE_TAC[remove_dead_inst_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  GVS[wl_inst_def; wl_assign_def; wl_set_var_def; option_case_eq; pair_case_eq;
      case_eq "word_loc"; list_case_eq; COND_CASE_EQ] THEN
  TRY(EXISTS_TAC `wl_state_locals (s1:(A,C,FFI)wl_state)` THEN
      REWRITE_TAC[word_allocProof_with_same_locals] THEN NO_TAC) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[lookup_insert] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[lookup_NONE_domain]);;

let WALLOCPAUX_mem_load_store = prove
 (`!w tstore (s:(A,C,FFI)wl_state).
     wl_mem_load w (wl_state_store_fupd (K tstore) s) = wl_mem_load w s`,
  SIMP[wl_mem_load_def]);;

let WALLOCPAUX_inst_store = prove
 (`!i (st:(A,C,FFI)wl_state) s1.
     wl_inst i st = SOME s1 ==> wl_state_store s1 = wl_state_store st`,
  GEN_TAC THEN WALLOCPAUX_INST_CASES_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  GVS[wl_inst_def; wl_assign_def; wl_set_var_def; wl_set_fp_var_def; wl_mem_store_def;
      option_case_eq; pair_case_eq; case_eq "word_loc"; list_case_eq; COND_CASE_EQ]);;

let WALLOCPAUX_inst_live = prove
 (`!i (live:1 spt) (st:(A,C,FFI)wl_state) s1 t tstore.
     wl_inst i st = SOME s1 /\
     strong_locals_rel I (domain (get_live_inst i live)) (wl_state_locals st) t
     ==> ?t1. wl_inst i (wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore) st)) =
              SOME (wl_state_locals_fupd (K t1) (wl_state_store_fupd (K tstore) s1)) /\
              strong_locals_rel I (domain live) (wl_state_locals s1) t1`,
  GEN_TAC THEN WALLOCPAUX_INST_CASES_TAC THEN
  REWRITE_TAC[get_live_inst_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  GVS[wl_inst_def; wl_assign_def; wl_set_var_def; wl_word_exp_def; the_words_def;
      wl_get_var_def; wl_get_vars_def; wl_mem_store_def; option_case_eq; pair_case_eq;
      case_eq "word_loc"; list_case_eq; COND_CASE_EQ] THEN
  WALLOCPAUX_TRANSFER_TAC THEN GVS[WALLOCPAUX_mem_load_store] THEN
  WALLOCPAUX_SLR_FINISH_TAC);;

(* helper for the ShareInst case: the shape of the address expression      *)

let WALLOCPAUX_SPLIT_TY_TAC (ty:hol_type) (th:thm) : tactic =
  fun (asl,w as g) ->
    match filter (fun v -> type_of v = ty) (frees w) with
      [] -> NO_TAC g
    | v::_ -> STRUCT_CASES_TAC (ISPEC v th) g;;

let WALLOCPAUX_flat_ShareInst = prove
 (`!op v (e:(A)wl_exp).
     flat_exp_conventions (ShareInst op v e)
     ==> (?r. e = wl_Var r) \/ (?r c. e = wl_Op asm_Add [wl_Var r; wl_Const c])`,
  REPEAT GEN_TAC THEN
  REPEAT((WALLOCPAUX_SPLIT_TY_TAC `:(A)wl_exp` (CONJUNCT1 (cases "wl_exp")) ORELSE
          WALLOCPAUX_SPLIT_TY_TAC `:binop` (cases "binop") ORELSE
          WALLOCPAUX_SPLIT_TY_TAC `:((A)wl_exp)list` list_CASES) THEN
         REWRITE_TAC[flat_exp_conventions_def] THEN TRY(MESON_TAC[])));;

(* opening of a case lemma without induction hypotheses *)

let WALLOCPAUX_RD_OPEN_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[WALLOCPAUX_rd_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC;;

let WALLOCPAUX_rd_Move = prove
 (`!pri ls live nlive lt (st:(A,C,FFI)wl_state).
       WALLOCPAUX_rd_Q st (wl_Move pri ls) live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN
  ABBREV_TAC (CASE_TERM
    `ls' = FILTER (\xy. match xy with (x,y) -> lookup x live = SOME one) (ls:(num#num)list)`) THEN
  SUBGOAL_THEN `!n. lookup n (live:1 spt) = SOME one ==>
                    ALOOKUP (ls':(num#num)list) n = ALOOKUP ls n /\ (n IN domain live)`
    ASSUME_TAC THENL
   [EXPAND_TAC "ls'" THEN SIMP[WALLOCPAUX_ALOOKUP_FILTER_live; domain_lookup] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. n IN domain (live:1 spt) ==> lookup n live = SOME one` ASSUME_TAC THENL
   [REWRITE_TAC[domain_lookup] THEN MESON_TAC[one]; ALL_TAC] THEN
  UNDISCH_TAC `remove_dead (wl_Move pri ls) live nlive (lt:(1 spt#1 spt)list) =
               (prog':(A)wl_prog,livein,nlivein)` THEN
  ASM_REWRITE_TAC[remove_dead_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  UNDISCH_TAC `wl_evaluate (wl_Move pri ls,st:(A,C,FFI)wl_state) = (res,rst)` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_CASES_TAC `ALL_DISTINCT (MAP FST (ls:(num#num)list))` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]] THEN
  MP_TAC(ISPEC `wl_get_vars (MAP SND (ls:(num#num)list)) (st:(A,C,FFI)wl_state)`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `vs:((A)word_loc)list`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  REWRITE_TAC[option_CASE; PAIR_EQ] THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  ASM_CASES_TAC `ls':(num#num)list = []` THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
               check (fun th -> is_eq(concl th) && rhs(concl th) = v)))
    [`prog':(A)wl_prog`; `livein:1 spt`; `nlivein:store_name list`] THEN
  REWRITE_TAC[option_CASE; wl_set_vars_def] THENL
   [MAP_EVERY EXISTS_TAC [`t:((A)word_loc)spt`; `tstore:(store_name,(A)word_loc)fmap`] THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
    REWRITE_TAC[strong_locals_rel_def; I_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `v:(A)word_loc`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `ALOOKUP (ls:(num#num)list) n = NONE` ASSUME_TAC THENL
     [ASM_MESON_TAC[ALOOKUP_THM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`ls:(num#num)list`; `vs:((A)word_loc)list`;
      `wl_state_locals (st:(A,C,FFI)wl_state)`; `st:(A,C,FFI)wl_state`; `n:num`]
      WALLOCPAUX_lookup_moves) THEN
    ASM_REWRITE_TAC[option_CASE] THEN DISCH_TAC THEN
    UNDISCH_TAC `strong_locals_rel I (domain (live:1 spt)) (wl_state_locals (st:(A,C,FFI)wl_state)) t` THEN
    REWRITE_TAC[strong_locals_rel_def; I_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. MEM y (MAP SND (ls':(num#num)list)) ==> MEM y (MAP SND (ls:(num#num)list))`
    ASSUME_TAC THENL
   [EXPAND_TAC "ls'" THEN REWRITE_TAC[MEM_MAP; MEM_FILTER] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?vs'. wl_get_vars (MAP SND (ls':(num#num)list)) (st:(A,C,FFI)wl_state) = SOME vs'`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[get_vars_exists] THEN
    SUBGOAL_THEN `set_of_list (MAP SND (ls:(num#num)list)) SUBSET
                  domain (wl_state_locals (st:(A,C,FFI)wl_state))` MP_TAC THENL
     [REWRITE_TAC[GSYM get_vars_exists] THEN EXISTS_TAC `vs:((A)word_loc)list` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST] THEN
    DISCH_TAC THEN X_GEN_TAC `y:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wl_get_vars (MAP SND (ls':(num#num)list))
      (wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore) (st:(A,C,FFI)wl_state))) =
    SOME vs'` ASSUME_TAC THENL
   [REWRITE_TAC[WALLOCPAUX_get_vars_locals_store] THEN
    MATCH_MP_TAC strong_locals_rel_I_get_vars' THEN
    EXISTS_TAC `domain (word_alloc_numset_list_insert (MAP SND (ls':(num#num)list))
                  (ITLIST delete (MAP FST ls') (live:1 spt)))` THEN
    ASM_REWRITE_TAC[word_allocProof_domain_numset_list_insert; IN_UNION; IN_SET_OF_LIST] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (ls':(num#num)list))` ASSUME_TAC THENL
   [EXPAND_TAC "ls'" THEN MATCH_MP_TAC WALLOCPAUX_ALL_DISTINCT_FILTER_live THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`alist_insert (MAP FST (ls':(num#num)list)) vs' (t:((A)word_loc)spt)`;
    `tstore:(store_name,(A)word_loc)fmap`] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[option_CASE; wl_set_vars_def] THEN
  SIMP[] THEN
  REWRITE_TAC[strong_locals_rel_def; I_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `v:(A)word_loc`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALOOKUP (ls':(num#num)list) n = ALOOKUP ls n` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ls':(num#num)list`; `vs':((A)word_loc)list`; `t:((A)word_loc)spt`;
                 `st:(A,C,FFI)wl_state`; `n:num`] WALLOCPAUX_lookup_moves) THEN
  MP_TAC(ISPECL [`ls:(num#num)list`; `vs:((A)word_loc)list`;
                 `wl_state_locals (st:(A,C,FFI)wl_state)`;
                 `st:(A,C,FFI)wl_state`; `n:num`] WALLOCPAUX_lookup_moves) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `ALOOKUP (ls:(num#num)list) n` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:num` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[option_CASE] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `n IN domain (word_alloc_numset_list_insert (MAP SND (ls':(num#num)list))
                  (ITLIST delete (MAP FST ls') (live:1 spt)))` ASSUME_TAC THENL
   [REWRITE_TAC[word_allocProof_domain_numset_list_insert; domain_FOLDR_delete; IN_UNION;
                IN_DIFF; IN_SET_OF_LIST] THEN
    DISJ1_TAC THEN ASM_REWRITE_TAC[GSYM ALOOKUP_NONE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `SOME (v:(A)word_loc)`)) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `strong_locals_rel I
      (domain (word_alloc_numset_list_insert (MAP SND (ls':(num#num)list))
        (ITLIST delete (MAP FST ls') (live:1 spt))))
      (wl_state_locals (st:(A,C,FFI)wl_state)) t` THEN
  REWRITE_TAC[strong_locals_rel_def; I_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let WALLOCPAUX_rd_Inst = prove
 (`!i live nlive lt (st:(A,C,FFI)wl_state). WALLOCPAUX_rd_Q st (wl_Inst i) live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN
  UNDISCH_TAC `wl_evaluate (wl_Inst i,st:(A,C,FFI)wl_state) = (res,rst)` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  MP_TAC(ISPEC `wl_inst (i:(A)inst) (st:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `s1:(A,C,FFI)wl_state`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  REWRITE_TAC[option_CASE; PAIR_EQ] THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP WALLOCPAUX_inst_store) THEN
  UNDISCH_TAC `remove_dead (wl_Inst i) live nlive (lt:(1 spt#1 spt)list) =
               (prog':(A)wl_prog,livein,nlivein)` THEN
  REWRITE_TAC[remove_dead_def] THEN
  ASM_CASES_TAC `remove_dead_inst (i:(A)inst) live` THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
               check (fun th -> is_eq(concl th) && rhs(concl th) = v)))
    [`prog':(A)wl_prog`; `livein:1 spt`; `nlivein:store_name list`] THEN
  REWRITE_TAC[option_CASE] THENL
   [MP_TAC(ISPECL [`i:(A)inst`; `live:1 spt`; `st:(A,C,FFI)wl_state`; `s1:(A,C,FFI)wl_state`]
      WALLOCPAUX_inst_dead) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `L:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`t:((A)word_loc)spt`; `tstore:(store_name,(A)word_loc)fmap`] THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
    UNDISCH_TAC `strong_locals_rel I (domain (live:1 spt))
                   (wl_state_locals (st:(A,C,FFI)wl_state)) t` THEN
    REWRITE_TAC[strong_locals_rel_def; I_THM] THEN ASM_MESON_TAC[];
    MP_TAC(ISPECL [`i:(A)inst`; `live:1 spt`; `st:(A,C,FFI)wl_state`; `s1:(A,C,FFI)wl_state`;
                   `t:((A)word_loc)spt`; `tstore:(store_name,(A)word_loc)fmap`]
      WALLOCPAUX_inst_live) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`t1:((A)word_loc)spt`; `tstore:(store_name,(A)word_loc)fmap`] THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[option_CASE]]);;

let WALLOCPAUX_rd_Get = prove
 (`!nm sn live nlive lt (st:(A,C,FFI)wl_state).
       WALLOCPAUX_rd_Q st (wl_Get nm sn) live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN
  ASM_CASES_TAC `lookup nm (live:1 spt) = NONE` THEN
  GVS[remove_dead_def; get_live_def; wl_evaluate_def; option_case_eq; pair_case_eq;
      COND_CASE_EQ; wl_set_var_def; wl_get_store_def] THENL
   [MATCH_MP_TAC strong_locals_rel_insert_notin THEN ASM_REWRITE_TAC[GSYM lookup_NONE_domain];
    ALL_TAC] THEN
  SUBGOAL_THEN `FLOOKUP (tstore:(store_name,(A)word_loc)fmap) sn = SOME (a:(A)word_loc)`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`FILTER (\s. ~(sn = s)) (nlive:store_name list)`;
                   `wl_state_store (st:(A,C,FFI)wl_state)`;
                   `tstore:(store_name,(A)word_loc)fmap`; `sn:store_name`]
       live_store_rel_FLOOKUP_store) THEN
    ASM_REWRITE_TAC[IN_SET_OF_LIST; MEM_FILTER];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`insert nm (a:(A)word_loc) t`; `tstore:(store_name,(A)word_loc)fmap`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    MATCH_MP_TAC strong_locals_rel_I_insert_insert THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC live_store_rel_less THEN
    EXISTS_TAC `FILTER (\s. ~(sn = s)) (nlive:store_name list)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_FILTER] THEN MESON_TAC[]]);;

let WALLOCPAUX_rd_OpCurrHeap = prove
 (`!bop nm src live nlive lt (st:(A,C,FFI)wl_state).
       WALLOCPAUX_rd_Q st (wl_OpCurrHeap bop nm src) live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN
  ASM_CASES_TAC `lookup nm (live:1 spt) = NONE` THEN
  GVS[remove_dead_def; get_live_def; wl_evaluate_def; option_case_eq; pair_case_eq;
      COND_CASE_EQ; wl_set_var_def] THENL
   [MATCH_MP_TAC strong_locals_rel_insert_notin THEN ASM_REWRITE_TAC[GSYM lookup_NONE_domain];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `wl_word_exp (wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore)
                    (st:(A,C,FFI)wl_state)))
       (wl_Op bop [wl_Var src; Lookup CurrHeap]) = SOME (a:(A)word_loc)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC strong_locals_rel_I_word_exp THEN
    MAP_EVERY EXISTS_TAC [`delete nm (live:1 spt)`;
                          `FILTER (\s. ~(CurrHeap = s)) (nlive:store_name list)`] THEN
    ASM_REWRITE_TAC[] THEN
    SIMP[get_live_exp_def; big_union_def; nlive_store_def; domain_union; domain_insert;
         domain_delete; IN_SET_OF_LIST; MEM_FILTER] THEN
    MATCH_MP_TAC strong_locals_rel_subset THEN
    EXISTS_TAC `src INSERT (domain (live:1 spt) DELETE nm)` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`insert nm (a:(A)word_loc) t`; `tstore:(store_name,(A)word_loc)fmap`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    MATCH_MP_TAC strong_locals_rel_I_insert_insert THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC strong_locals_rel_subset THEN
    EXISTS_TAC `src INSERT (domain (live:1 spt) DELETE nm)` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC live_store_rel_less THEN
    EXISTS_TAC `FILTER (\s. ~(CurrHeap = s)) (nlive:store_name list)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_FILTER] THEN MESON_TAC[]]);;

let WALLOCPAUX_rd_LocValue = prove
 (`!r l1 live nlive lt (st:(A,C,FFI)wl_state).
       WALLOCPAUX_rd_Q st (wl_LocValue r l1) live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN
  ASM_CASES_TAC `lookup r (live:1 spt) = NONE` THEN
  GVS[remove_dead_def; get_live_def; wl_evaluate_def; option_case_eq; pair_case_eq;
      COND_CASE_EQ; wl_set_var_def] THENL
   [MATCH_MP_TAC strong_locals_rel_insert_notin THEN ASM_REWRITE_TAC[GSYM lookup_NONE_domain];
    MATCH_MP_TAC strong_locals_rel_I_insert_insert THEN ASM_REWRITE_TAC[]]);;

let WALLOCPAUX_rd_Set = prove
 (`!sn e live nlive lt (st:(A,C,FFI)wl_state).
       WALLOCPAUX_rd_Q st (wl_Set sn e) live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN
  SUBGOAL_THEN `?r. e = (wl_Var r:(A)wl_exp)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `flat_exp_conventions (wl_Set sn (e:(A)wl_exp))` THEN
    CASES_ON `e:(A)wl_exp` THEN SIMP[flat_exp_conventions_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `e:(A)wl_exp`)) THEN
  ASM_CASES_TAC `MEM (sn:store_name) nlive` THEN
  GVS[remove_dead_def; get_live_def; wl_evaluate_def; option_case_eq; pair_case_eq;
      COND_CASE_EQ; wl_set_store_def; wl_word_exp_def] THENL
   [UNDISCH_TAC `live_store_rel nlivein (wl_state_store (st:(A,C,FFI)wl_state)) tstore` THEN
    REWRITE_TAC[live_store_rel_def; FLOOKUP_UPDATE; IN_SET_OF_LIST] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`t:((A)word_loc)spt`;
                        `(tstore:(store_name,(A)word_loc)fmap) |+ (sn,a)`] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `a:(A)word_loc` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC strong_locals_rel_I_get_var THEN
    EXISTS_TAC `domain (live:1 spt)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC strong_locals_rel_subset THEN
    EXISTS_TAC `r INSERT domain (live:1 spt)` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    UNDISCH_TAC `live_store_rel (CONS sn nlive) (wl_state_store (st:(A,C,FFI)wl_state)) tstore` THEN
    REWRITE_TAC[live_store_rel_def; FLOOKUP_UPDATE; IN_SET_OF_LIST; MEM] THEN MESON_TAC[]]);;

let WALLOCPAUX_rd_Seq = prove
 (`!s1 s2 live nlive lt.
       (!st:(A,C,FFI)wl_state. WALLOCPAUX_rd_Q st s2 live nlive lt) /\
       (!s2' s2live s2nlive.
            remove_dead s2 live nlive lt = (s2',s2live,s2nlive)
            ==> (!st:(A,C,FFI)wl_state. WALLOCPAUX_rd_Q st s1 s2live s2nlive lt))
       ==> (!st:(A,C,FFI)wl_state. WALLOCPAUX_rd_Q st (wl_Seq s1 s2) live nlive lt)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih2") (LABEL_TAC "ih1")) THEN
  GEN_TAC THEN REWRITE_TAC[WALLOCPAUX_rd_Q_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[remove_dead_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `remove_dead s2 live nlive (lt:(1 spt#1 spt)list):(A)wl_prog#1 spt#store_name list`
    [`s2':(A)wl_prog`; `s2live:1 spt`; `s2nlive:store_name list`] THEN
  REWRITE_TAC[pair_CASE] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `remove_dead s1 s2live s2nlive (lt:(1 spt#1 spt)list):(A)wl_prog#1 spt#store_name list`
    [`s1':(A)wl_prog`; `s1live:1 spt`; `s1nlive:store_name list`] THEN
  REWRITE_TAC[pair_CASE; PAIR_EQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[flat_exp_conventions_def] THEN STRIP_TAC THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
               check (fun th -> is_eq(concl th) && rhs(concl th) = v)))
    [`livein:1 spt`; `nlivein:store_name list`] THEN
  UNDISCH_TAC `wl_evaluate (wl_Seq s1 s2,st:(A,C,FFI)wl_state) = (res,rst)` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (s1,st:(A,C,FFI)wl_state)`
    [`r1:((A)wl_result)option`; `st1:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(r1 = SOME (wl_Error:(A)wl_result))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(if r1 = NONE then wl_evaluate (s2,st1)
                  else (r1:((A)wl_result)option,st1:(A,C,FFI)wl_state)) = (res,rst)` THEN
    ASM_REWRITE_TAC[option_DISTINCT; PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`s2':(A)wl_prog`; `s2live:1 spt`; `s2nlive:store_name list`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[WALLOCPAUX_rd_Q_def] o SPEC `st:(A,C,FFI)wl_state`) THEN
  DISCH_THEN(MP_TAC o SPECL [`s1':(A)wl_prog`; `s1live:1 spt`; `s1nlive:store_name list`;
    `t:((A)word_loc)spt`; `tstore:(store_name,(A)word_loc)fmap`;
    `r1:((A)wl_result)option`; `st1:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:((A)word_loc)spt` (X_CHOOSE_THEN
    `tstore1:(store_name,(A)word_loc)fmap` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> is_eq(concl th) && rhs(concl th) = `prog':(A)wl_prog`)) THEN
  ASM_CASES_TAC `r1:((A)wl_result)option = NONE` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> lhs(concl th) = `r1:((A)wl_result)option`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_CASE]) THEN
    REMOVE_THEN "ih2" (MP_TAC o REWRITE_RULE[WALLOCPAUX_rd_Q_def] o
                        SPEC `st1:(A,C,FFI)wl_state`) THEN
    DISCH_THEN(MP_TAC o SPECL [`s2':(A)wl_prog`; `s2live:1 spt`; `s2nlive:store_name list`;
      `t1:((A)word_loc)spt`; `tstore1:(store_name,(A)word_loc)fmap`;
      `res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t2:((A)word_loc)spt` (X_CHOOSE_THEN
      `tstore2:(store_name,(A)word_loc)fmap` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`t2:((A)word_loc)spt`; `tstore2:(store_name,(A)word_loc)fmap`] THEN
    ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THENL
     [UNDISCH_TAC `wl_evaluate (s1',wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore)
                     (st:(A,C,FFI)wl_state))) =
                   (NONE,wl_state_locals_fupd (K t1) (wl_state_store_fupd (K tstore1) st1))` THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN REWRITE_TAC[PAIR_EQ] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    COND_CASES_TAC THENL
     [UNDISCH_TAC `wl_evaluate (s2',wl_state_locals_fupd (K t1) (wl_state_store_fupd (K tstore1)
                     (st1:(A,C,FFI)wl_state))) =
                   (res,wl_state_locals_fupd (K t2) (wl_state_store_fupd (K tstore2) rst))` THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WALLOCPAUX_seq_NONE th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `r1:((A)wl_result)option` (cases "option")) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:(A)wl_result` SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_CASE]) THEN
  UNDISCH_TAC `(if SOME (x:(A)wl_result) = NONE then wl_evaluate (s2,st1:(A,C,FFI)wl_state)
                else (SOME x,st1)) = (res,rst)` THEN
  REWRITE_TAC[GSYM (distinctness "option"); PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  MAP_EVERY EXISTS_TAC [`t1:((A)word_loc)spt`; `tstore1:(store_name,(A)word_loc)fmap`] THEN
  ASM_REWRITE_TAC[option_CASE] THEN
  COND_CASES_TAC THENL
   [UNDISCH_TAC `wl_evaluate (s1',wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore)
                   (st:(A,C,FFI)wl_state))) =
                 (SOME (x:(A)wl_result),
                  wl_state_locals_fupd (K t1) (wl_state_store_fupd (K tstore1) st1))` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    REWRITE_TAC[PAIR_EQ; distinctness "option"];
    ALL_TAC] THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WALLOCPAUX_seq_SOME th]));;

let WALLOCPAUX_rd_MustTerminate = prove
 (`!s1 live nlive lt.
       (!st:(A,C,FFI)wl_state. WALLOCPAUX_rd_Q st s1 live nlive lt)
       ==> (!st:(A,C,FFI)wl_state. WALLOCPAUX_rd_Q st (MustTerminate s1) live nlive lt)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_rd_Q_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[remove_dead_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC
    `remove_dead s1 live nlive (lt:(1 spt#1 spt)list):(A)wl_prog#1 spt#store_name list`
    [`s1':(A)wl_prog`; `s1live:1 spt`; `s1nlive:store_name list`] THEN
  REWRITE_TAC[pair_CASE; PAIR_EQ; flat_exp_conventions_def] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
               check (fun th -> is_eq(concl th) && rhs(concl th) = v)))
    [`prog':(A)wl_prog`; `livein:1 spt`; `nlivein:store_name list`] THEN
  UNDISCH_TAC `wl_evaluate (MustTerminate s1,st:(A,C,FFI)wl_state) = (res,rst)` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  COND_CASES_TAC THENL [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC
    `wl_evaluate (s1,wl_state_clock_fupd (K (MustTerminate_limit (:A)))
       (wl_state_termdep_fupd (K (wl_state_termdep st - 1)) (st:(A,C,FFI)wl_state)))`
    [`r1:((A)wl_result)option`; `st1:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN
  COND_CASES_TAC THENL [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REMOVE_THEN "ih" (MP_TAC o REWRITE_RULE[WALLOCPAUX_rd_Q_def] o
    SPEC `wl_state_clock_fupd (K (MustTerminate_limit (:A)))
       (wl_state_termdep_fupd (K (wl_state_termdep st - 1)) (st:(A,C,FFI)wl_state))`) THEN
  DISCH_THEN(MP_TAC o SPECL [`s1':(A)wl_prog`; `s1live:1 spt`; `s1nlive:store_name list`;
    `t:((A)word_loc)spt`; `tstore:(store_name,(A)word_loc)fmap`;
    `r1:((A)wl_result)option`; `st1:(A,C,FFI)wl_state`]) THEN
  ANTS_TAC THENL [SIMP[] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:((A)word_loc)spt` (X_CHOOSE_THEN
    `tstore1:(store_name,(A)word_loc)fmap` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`t1:((A)word_loc)spt`; `tstore1:(store_name,(A)word_loc)fmap`] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      can (term_match [] `wl_evaluate (s1',x:(A,C,FFI)wl_state)`) (lhs(concl th)))) THEN
    SIMP[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[pair_CASE] THEN SIMP[];
    POP_ASSUM MP_TAC THEN SIMP[]]);;

let WALLOCPAUX_rd_If = prove
 (`!cmp r1 ri e2 e3 live nlive lt.
       (!st:(A,C,FFI)wl_state. WALLOCPAUX_rd_Q st e2 live nlive lt) /\
       (!e2' e2_live e2_nlive.
            remove_dead e2 live nlive lt = (e2',e2_live,e2_nlive)
            ==> (!st:(A,C,FFI)wl_state. WALLOCPAUX_rd_Q st e3 live nlive lt))
       ==> (!st:(A,C,FFI)wl_state. WALLOCPAUX_rd_Q st (wl_If cmp r1 ri e2 e3) live nlive lt)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih2") (LABEL_TAC "ih3")) THEN
  GEN_TAC THEN REWRITE_TAC[WALLOCPAUX_rd_Q_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[remove_dead_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC
    `remove_dead e2 live nlive (lt:(1 spt#1 spt)list):(A)wl_prog#1 spt#store_name list`
    [`e2':(A)wl_prog`; `e2_live:1 spt`; `e2_nlive:store_name list`] THEN
  REWRITE_TAC[pair_CASE] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC
    `remove_dead e3 live nlive (lt:(1 spt#1 spt)list):(A)wl_prog#1 spt#store_name list`
    [`e3':(A)wl_prog`; `e3_live:1 spt`; `e3_nlive:store_name list`] THEN
  REWRITE_TAC[pair_CASE; PAIR_EQ; flat_exp_conventions_def] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REMOVE_THEN "ih3" (MP_TAC o SPECL [`e2':(A)wl_prog`; `e2_live:1 spt`;
                                     `e2_nlive:store_name list`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ih3") THEN
  STRIP_TAC THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
               check (fun th -> is_eq(concl th) && rhs(concl th) = v)))
    [`prog':(A)wl_prog`; `livein:1 spt`; `nlivein:store_name list`] THEN
  SUBGOAL_THEN
   `strong_locals_rel I (domain (e2_live:1 spt)) (wl_state_locals (st:(A,C,FFI)wl_state)) t /\
    strong_locals_rel I (domain (e3_live:1 spt)) (wl_state_locals st) t /\
    (!v. wl_get_var r1 st = SOME v ==>
         wl_get_var r1 (wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore) st)) =
         SOME v) /\
    (!v. wl_get_var_imm ri st = SOME v ==>
         wl_get_var_imm ri (wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore) st)) =
         SOME v)`
    STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "strong_locals_rel"
      with Failure _ -> false)) THEN
    STRUCT_CASES_TAC (ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN
    SIMP[wl_get_var_imm_def; wl_get_var_def; strong_locals_rel_def; I_THM; domain_insert;
         domain_union; IN_INSERT; IN_UNION] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `live_store_rel e2_nlive (wl_state_store (st:(A,C,FFI)wl_state)) tstore /\
                live_store_rel e3_nlive (wl_state_store st) tstore`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC live_store_rel_less THEN
    EXISTS_TAC `FILTER (\s. MEM s e3_nlive) (e2_nlive:store_name list)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_FILTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `wl_evaluate (wl_If cmp r1 ri e2 e3,st:(A,C,FFI)wl_state) = (res,rst)` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  MP_TAC(ISPEC `wl_get_var r1 (st:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `x:(A)word_loc` (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THENL
   [SIMP[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `wl_get_var_imm ri (st:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `y:(A)word_loc` (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THENL
   [SIMP[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[pair_CASE; option_CASE] THEN
  MP_TAC(ISPEC `wl_word_cmp cmp (x:(A)word_loc) y` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `b:bool` (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THENL
   [SIMP[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SIMP[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `wl_get_var r1 (wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore)
      (st:(A,C,FFI)wl_state))) = SOME x /\
    wl_get_var_imm ri (wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore) st)) =
      SOME y`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `b:bool` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [REMOVE_THEN "ih2" (MP_TAC o REWRITE_RULE[WALLOCPAUX_rd_Q_def] o
                        SPEC `st:(A,C,FFI)wl_state`) THEN
    DISCH_THEN(MP_TAC o SPECL [`e2':(A)wl_prog`; `e2_live:1 spt`; `e2_nlive:store_name list`;
      `t:((A)word_loc)spt`; `tstore:(store_name,(A)word_loc)fmap`;
      `res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`]);
    REMOVE_THEN "ih3" (MP_TAC o REWRITE_RULE[WALLOCPAUX_rd_Q_def] o
                        SPEC `st:(A,C,FFI)wl_state`) THEN
    DISCH_THEN(MP_TAC o SPECL [`e3':(A)wl_prog`; `e3_live:1 spt`; `e3_nlive:store_name list`;
      `t:((A)word_loc)spt`; `tstore:(store_name,(A)word_loc)fmap`;
      `res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`])] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:((A)word_loc)spt` (X_CHOOSE_THEN
    `tstore2:(store_name,(A)word_loc)fmap` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`t2:((A)word_loc)spt`; `tstore2:(store_name,(A)word_loc)fmap`] THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN
  TRY(POP_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[pair_CASE; option_CASE]);;

(* helpers for the Call case: push_env does not store the handler program; *)
(* the callee state does not depend on the caller's locals                  *)

let WALLOCPAUX_push_env_handler = prove
 (CASE_TERM
  `!envs (h:(num#(A)wl_prog#num#num)option) (f:(A)wl_prog->(A)wl_prog)
    (s:(A,C,FFI)wl_state).
     wl_push_env envs (match h with NONE -> NONE | SOME (a,p,b,c) -> SOME (a,f p,b,c)) s =
     wl_push_env envs h s`,
  GEN_TAC THEN REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  SIMP[wl_push_env_def]);;

let WALLOCPAUX_call_env_push_locals = prove
 (`!args ss envs (h:(num#(A)wl_prog#num#num)option) t (s:(A,C,FFI)wl_state).
     wl_call_env args ss (wl_push_env envs h (wl_dec_clock (wl_state_locals_fupd (K t) s))) =
     wl_call_env args ss (wl_push_env envs h (wl_dec_clock s)) /\
     wl_state_stack_max
       (wl_call_env args ss (wl_push_env envs h (wl_state_locals_fupd (K t) s))) =
     wl_state_stack_max (wl_call_env args ss (wl_push_env envs h s))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `wl_dec_clock (wl_state_locals_fupd (K t) (s:(A,C,FFI)wl_state)) =
                wl_state_locals_fupd (K t) (wl_dec_clock s)` SUBST1_TAC THENL
   [REWRITE_TAC[wl_dec_clock_def] THEN SIMP[]; ALL_TAC] THEN
  REWRITE_TAC[WALLOCPAUX_push_env_locals; wl_call_env_def] THEN SIMP[]);;

let WALLOCPAUX_rd_CallSome = prove
 (`!v cutsets ret_handler l1 l2 dest args h live nlive lt.
       (!st:(A,C,FFI)wl_state. WALLOCPAUX_rd_Q st ret_handler live nlive lt) /\
       (!ret_handler' rl v' l1' l2' prog.
            remove_dead ret_handler live nlive lt = (ret_handler',rl) /\
            h = SOME (v',prog,l1',l2')
            ==> (!st:(A,C,FFI)wl_state. WALLOCPAUX_rd_Q st prog live nlive lt))
       ==> (!st:(A,C,FFI)wl_state.
                WALLOCPAUX_rd_Q st
                (wl_Call (SOME (v,cutsets,ret_handler,l1,l2)) dest args h)
                live
                nlive
                lt)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihr") (LABEL_TAC "ihh")) THEN
  GEN_TAC THEN REWRITE_TAC[WALLOCPAUX_rd_Q_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[remove_dead_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC
    `remove_dead ret_handler live nlive (lt:(1 spt#1 spt)list):(A)wl_prog#1 spt#store_name list`
    [`rh':(A)wl_prog`; `rl:1 spt#store_name list`] THEN
  REWRITE_TAC[pair_CASE; PAIR_EQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  STRIP_TAC THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
               check (fun th -> is_eq(concl th) && rhs(concl th) = v)))
    [`prog':(A)wl_prog`; `livein:1 spt`; `nlivein:store_name list`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o REWRITE_RULE[live_store_rel_NIL] o
    check (fun th -> can (term_match [] `live_store_rel [] (x:(store_name,(A)word_loc)fmap) y`)
                         (concl th))) THEN
  REWRITE_TAC[with_same_store] THEN
  UNDISCH_TAC `wl_evaluate (wl_Call (SOME (v,cutsets,ret_handler,l1,l2)) dest args h,
                            st:(A,C,FFI)wl_state) = (res,rst)` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[add_ret_loc_def; wl_state_INFO.ri_accfupds; K_THM; option_CASE; pair_CASE] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MP_TAC(ISPEC `wl_get_vars args (st:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `xs:((A)word_loc)list`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  REWRITE_TAC[option_CASE] THENL [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wl_get_vars args (wl_state_locals_fupd (K t) (st:(A,C,FFI)wl_state)) =
                SOME xs` SUBST1_TAC THENL
   [MATCH_MP_TAC strong_locals_rel_I_get_vars' THEN
    EXISTS_TAC `domain (union (union (FST (cutsets:1 spt#1 spt)) (SND cutsets))
                  (word_alloc_numset_list_insert args LN))` THEN
    ASM_REWRITE_TAC[domain_union; word_allocProof_domain_numset_list_insert; IN_UNION;
                    IN_SET_OF_LIST] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[option_CASE] THEN
  ASM_CASES_TAC `bad_dest_args (dest:num option) (args:num list)` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `wl_find_code (dest:num option) (CONS (wl_Loc l1 l2) (xs:((A)word_loc)list)) (wl_state_code st)
                  (wl_state_stack_size (st:(A,C,FFI)wl_state))` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN
    `fc:((A)word_loc)list#(A)wl_prog#num option` SUBST1_TAC)) THEN
  REWRITE_TAC[option_CASE] THENL [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  WALLOCPAUX_TUPLE_TAC `fc:((A)word_loc)list#(A)wl_prog#num option`
    [`args1:((A)word_loc)list`; `prog1:(A)wl_prog`; `ss:num option`] THEN
  REWRITE_TAC[pair_CASE] THEN
  ASM_CASES_TAC `domain (FST (cutsets:1 spt#1 spt)) = {} \/ ~ALL_DISTINCT (v:num list)` THEN
  ASM_REWRITE_TAC[] THENL [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `cut_envs cutsets (wl_state_locals (st:(A,C,FFI)wl_state))` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN
    `envs:((A)word_loc)spt#((A)word_loc)spt` (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  REWRITE_TAC[option_CASE] THENL [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `cut_envs cutsets t = SOME (envs:((A)word_loc)spt#((A)word_loc)spt)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC strong_locals_rel_I_cut_envs THEN EXISTS_TAC `st:(A,C,FFI)wl_state` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC strong_locals_rel_subset THEN
    EXISTS_TAC `domain (union (union (FST (cutsets:1 spt#1 spt)) (SND cutsets))
                  (word_alloc_numset_list_insert args LN))` THEN
    ASM_REWRITE_TAC[domain_union] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[option_CASE; WALLOCPAUX_push_env_handler; WALLOCPAUX_call_env_push_locals] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_exp_conventions_def; option_CASE; pair_CASE]) THEN
  ASM_CASES_TAC `wl_state_clock (st:(A,C,FFI)wl_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`wl_state_locals (rst:(A,C,FFI)wl_state)`;
                          `wl_state_store (rst:(A,C,FFI)wl_state)`] THEN
    REWRITE_TAC[WALLOCPAUX_rd_concl_refl; word_allocProof_with_same_locals; with_same_store] THEN
    MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST1_TAC o SYM o
                 check (fun th -> is_eq(concl th) && rhs(concl th) = v)))
      [`res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`] THEN
    REWRITE_TAC[PAIR_EQ; wl_flush_state_def] THEN SIMP[];
    ALL_TAC] THEN
  WALLOCPAUX_TUPLE_TAC
    `wl_evaluate (prog1,wl_call_env args1 ss (wl_push_env envs h (wl_dec_clock
       (st:(A,C,FFI)wl_state))))`
    [`r2:((A)wl_result)option`; `s2:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPEC `r2:((A)wl_result)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `r:(A)wl_result` SUBST1_TAC)) THEN
  REWRITE_TAC[option_CASE] THENL [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  STRUCT_CASES_TAC (ISPEC `r:(A)wl_result` (cases "wl_result")) THEN
  REWRITE_TAC[WALLOCPAUX_wl_result_CASE] THEN
  TRY(REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
      MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
                   check (fun th -> is_eq(concl th) && rhs(concl th) = v)))
        [`res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`] THEN
      FIRST [FIRST_X_ASSUM(CONTR_TAC o REWRITE_RULE[] o
               check (fun th -> concl th = `~(SOME (wl_Error:(A)wl_result) = SOME wl_Error)`));
             MAP_EVERY EXISTS_TAC [`wl_state_locals (s2:(A,C,FFI)wl_state)`;
                                   `wl_state_store (s2:(A,C,FFI)wl_state)`] THEN
             REWRITE_TAC[WALLOCPAUX_rd_concl_refl; word_allocProof_with_same_locals;
                         with_same_store]] THEN NO_TAC) THENL
   [COND_CASES_TAC THENL
     [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `wl_pop_env (s2:(A,C,FFI)wl_state)` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `s1:(A,C,FFI)wl_state`
      SUBST1_TAC)) THEN
    REWRITE_TAC[option_CASE] THENL [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THENL [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]] THEN
    DISCH_TAC THEN
    USE_THEN "ihr" (MP_TAC o REWRITE_RULE[WALLOCPAUX_rd_Q_def] o
      SPEC `wl_set_vars v a1 (s1:(A,C,FFI)wl_state)`) THEN
    DISCH_THEN(MP_TAC o SPECL [`rh':(A)wl_prog`; `FST (rl:1 spt#store_name list)`;
      `SND (rl:1 spt#store_name list)`;
      `wl_state_locals (wl_set_vars v a1 (s1:(A,C,FFI)wl_state))`;
      `wl_state_store (wl_set_vars v a1 (s1:(A,C,FFI)wl_state))`;
      `res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`]) THEN
    ASM_REWRITE_TAC[WALLOCPAUX_strong_locals_rel_I_refl; live_store_rel_refl;
                    word_allocProof_with_same_locals; with_same_store; PAIR];
    MP_TAC(ISPEC `h:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `hh:num#(A)wl_prog#num#num`
      SUBST_ALL_TAC)) THEN
    REWRITE_TAC[option_CASE] THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
      MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
                   check (fun th -> is_eq(concl th) && rhs(concl th) = v)))
        [`res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`] THEN
      MAP_EVERY EXISTS_TAC [`wl_state_locals (s2:(A,C,FFI)wl_state)`;
                            `wl_state_store (s2:(A,C,FFI)wl_state)`] THEN
      REWRITE_TAC[WALLOCPAUX_rd_concl_refl; word_allocProof_with_same_locals;
                  with_same_store];
      ALL_TAC] THEN
    WALLOCPAUX_TUPLE_TAC `hh:num#(A)wl_prog#num#num`
      [`hn:num`; `hp:(A)wl_prog`; `hl1:num`; `hl2:num`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_CASE; pair_CASE]) THEN
    REWRITE_TAC[option_CASE; pair_CASE] THEN
    COND_CASES_TAC THENL [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THENL [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]] THEN
    DISCH_TAC THEN
    USE_THEN "ihh" (MP_TAC o SPECL [`rh':(A)wl_prog`; `rl:1 spt#store_name list`;
      `hn:num`; `hl1:num`; `hl2:num`; `hp:(A)wl_prog`]) THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[WALLOCPAUX_rd_Q_def] o
      SPEC `wl_set_var hn a1 (s2:(A,C,FFI)wl_state)`) THEN
    DISCH_THEN(MP_TAC o SPECL
      [`FST (remove_dead (hp:(A)wl_prog) live nlive (lt:(1 spt#1 spt)list))`;
       `FST (SND (remove_dead (hp:(A)wl_prog) live nlive (lt:(1 spt#1 spt)list)))`;
       `SND (SND (remove_dead (hp:(A)wl_prog) live nlive (lt:(1 spt#1 spt)list)))`;
       `wl_state_locals (wl_set_var hn a1 (s2:(A,C,FFI)wl_state))`;
       `wl_state_store (wl_set_var hn a1 (s2:(A,C,FFI)wl_state))`;
       `res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`]) THEN
    ASM_REWRITE_TAC[WALLOCPAUX_strong_locals_rel_I_refl; live_store_rel_refl;
                    word_allocProof_with_same_locals; with_same_store; PAIR]]);;

let WALLOCPAUX_rd_CallNone = prove
 (`!dst args hdl live nlive lt (st:(A,C,FFI)wl_state).
       WALLOCPAUX_rd_Q st (wl_Call NONE dst args hdl) live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN
  GVS[remove_dead_def; get_live_def; wl_evaluate_def; option_case_eq; pair_case_eq;
      case_eq "word_loc"] THEN
  SUBGOAL_THEN `wl_get_vars args (wl_state_locals_fupd (K t) (st:(A,C,FFI)wl_state)) = SOME a`
    ASSUME_TAC THENL
   [MATCH_MP_TAC strong_locals_rel_I_get_vars' THEN
    EXISTS_TAC `domain (word_alloc_numset_list_insert args (LN:1 spt))` THEN
    ASM_REWRITE_TAC[word_allocProof_domain_numset_list_insert; IN_UNION; IN_SET_OF_LIST] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`wl_state_locals (rst:(A,C,FFI)wl_state)`;
                        `wl_state_store (rst:(A,C,FFI)wl_state)`] THEN
  REWRITE_TAC[WALLOCPAUX_rd_concl_refl; word_allocProof_with_same_locals; with_same_store] THEN
  ASM_REWRITE_TAC[option_INJ; UNWIND_THM1; WALLOCPAUX_call_env_locals] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  EVERY_CASE_TAC THEN SIMP[] THEN MESON_TAC[]);;

let WALLOCPAUX_rd_Alloc = prove
 (`!n nms live nlive lt (st:(A,C,FFI)wl_state).
       WALLOCPAUX_rd_Q st (wl_Alloc n nms) live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN
  GVS[remove_dead_def; get_live_def; wl_evaluate_def; option_case_eq; pair_case_eq;
      case_eq "word_loc"] THEN
  IMP_RES_TAC strong_locals_rel_I_get_var' THEN
  SUBGOAL_THEN `cut_envs nms t = cut_envs nms (wl_state_locals (st:(A,C,FFI)wl_state))`
    ASSUME_TAC THENL
   [CASES_ON `cut_envs nms (wl_state_locals (st:(A,C,FFI)wl_state))` THENL
     [GVS[wl_alloc_def];
      MATCH_MP_TAC strong_locals_rel_I_cut_envs THEN EXISTS_TAC `st:(A,C,FFI)wl_state` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC strong_locals_rel_subset THEN
      EXISTS_TAC `n INSERT (domain (FST (nms:1 spt#1 spt)) UNION domain (SND nms))` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`wl_state_locals (rst:(A,C,FFI)wl_state)`;
                        `wl_state_store (rst:(A,C,FFI)wl_state)`] THEN
  REWRITE_TAC[WALLOCPAUX_rd_concl_refl; word_allocProof_with_same_locals; with_same_store] THEN
  ASM_SIMP_TAC[WALLOCPAUX_alloc_locals] THEN ASM_MESON_TAC[]);;

let WALLOCPAUX_rd_Raise = prove
 (`!n live nlive lt (st:(A,C,FFI)wl_state). WALLOCPAUX_rd_Q st (wl_Raise n) live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN
  GVS[remove_dead_def; get_live_def; wl_evaluate_def; option_case_eq; pair_case_eq] THEN
  REWRITE_TAC[WALLOCPAUX_jump_exc_locals] THEN ASM_MESON_TAC[strong_locals_rel_I_get_var']);;

let WALLOCPAUX_rd_Return = prove
 (`!n ms live nlive lt (st:(A,C,FFI)wl_state).
       WALLOCPAUX_rd_Q st (wl_Return n ms) live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN
  GVS[remove_dead_def; get_live_def; wl_evaluate_def; option_case_eq; pair_case_eq;
      case_eq "word_loc"] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[strong_locals_rel_I_get_var'];
    MATCH_MP_TAC strong_locals_rel_I_get_vars' THEN
    EXISTS_TAC `n INSERT domain (word_alloc_numset_list_insert ms (live:1 spt))` THEN
    ASM_REWRITE_TAC[word_allocProof_domain_numset_list_insert; IN_INSERT; IN_UNION;
                    IN_SET_OF_LIST] THEN
    MESON_TAC[]]);;

let WALLOCPAUX_rd_Loop = prove
 (`!names body exit_names live nlive lt.
       (!lt' (st:(A,C,FFI)wl_state). WALLOCPAUX_rd_Q st body names [] lt')
       ==> (!st:(A,C,FFI)wl_state.
                WALLOCPAUX_rd_Q st (wl_Loop names body exit_names) live nlive lt)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_rd_Q_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[remove_dead_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC
    `remove_dead body names [] (CONS (names,exit_names) (lt:(1 spt#1 spt)list))
       :(A)wl_prog#1 spt#store_name list`
    [`body':(A)wl_prog`; `bl:1 spt`; `bnl:store_name list`] THEN
  REWRITE_TAC[pair_CASE; PAIR_EQ; flat_exp_conventions_def] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
               check (fun th -> is_eq(concl th) && rhs(concl th) = v)))
    [`prog':(A)wl_prog`; `livein:1 spt`; `nlivein:store_name list`] THEN
  MP_TAC(ISPECL [`st:(A,C,FFI)wl_state`; `t:((A)word_loc)spt`;
    `tstore:(store_name,(A)word_loc)fmap`; `names:1 spt`; `body:(A)wl_prog`;
    `exit_names:1 spt`; `live:1 spt`; `nlive:store_name list`; `lt:(1 spt#1 spt)list`;
    `wl_Loop names body' exit_names:(A)wl_prog`; `names:1 spt`; `[]:store_name list`;
    `res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`]
    evaluate_remove_dead_Loop_helper) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[remove_dead_def; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[pair_CASE] THEN
    REPEAT STRIP_TAC THEN
    USE_THEN "ih" (MP_TAC o REWRITE_RULE[WALLOCPAUX_rd_Q_def] o
      SPECL [`CONS (names,exit_names) (lt:(1 spt#1 spt)list)`; `st':(A,C,FFI)wl_state`]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`livein':1 spt`; `nlivein':store_name list`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[]]);;

let WALLOCPAUX_rd_Break = prove
 (`!n live nlive lt (st:(A,C,FFI)wl_state). WALLOCPAUX_rd_Q st (wl_Break n) live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN GVS[remove_dead_def; get_live_def; wl_evaluate_def] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`oEL n (lt:(1 spt#1 spt)list)`, `x:(1 spt#1 spt)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN SIMP[]);;

let WALLOCPAUX_rd_Continue = prove
 (`!n live nlive lt (st:(A,C,FFI)wl_state). WALLOCPAUX_rd_Q st (wl_Continue n) live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN GVS[remove_dead_def; get_live_def; wl_evaluate_def] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`oEL n (lt:(1 spt#1 spt)list)`, `x:(1 spt#1 spt)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN SIMP[]);;

let WALLOCPAUX_rd_Skip = prove
 (`!live nlive lt (st:(A,C,FFI)wl_state). WALLOCPAUX_rd_Q st wl_Skip live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN GVS[remove_dead_def; get_live_def; wl_evaluate_def]);;

let WALLOCPAUX_rd_Assign = prove
 (`!v8 v9 live nlive lt (st:(A,C,FFI)wl_state).
       WALLOCPAUX_rd_Q st (wl_Assign v8 v9) live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN ASM_MESON_TAC[flat_exp_conventions_def]);;

let WALLOCPAUX_rd_Store = prove
 (`!v14 v15 live nlive lt (st:(A,C,FFI)wl_state).
       WALLOCPAUX_rd_Q st (wl_Store v14 v15) live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN ASM_MESON_TAC[flat_exp_conventions_def]);;

let WALLOCPAUX_rd_StoreConsts = prove
 (`!v33 v34 v35 v36 v37 live nlive lt (st:(A,C,FFI)wl_state).
       WALLOCPAUX_rd_Q st (wl_StoreConsts v33 v34 v35 v36 v37) live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN
  GVS[remove_dead_def; get_live_def; wl_evaluate_def; option_case_eq; pair_case_eq;
      case_eq "word_loc"; COND_CASE_EQ; wl_set_var_def; wl_unset_var_def; LET_DEF;
      LET_END_DEF] THEN
  SUBGOAL_THEN
    `wl_get_var v35 (wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore)
       (st:(A,C,FFI)wl_state))) = SOME (wl_Word a) /\
     wl_get_var v36 (wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore) st)) =
       SOME (wl_Word a')`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WALLOCPAUX_get_var_I THEN
    EXISTS_TAC `v35 INSERT v36 INSERT (domain (live:1 spt) DELETE v34 DELETE v33)` THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`insert v35 (wl_Word (word_add a (word_mul bytes_in_word (word (LENGTH (v37:(bool#(A)word)list))))))
      (insert v36 (wl_Word a') (delete v33 (delete v34 (t:((A)word_loc)spt))))`;
    `tstore:(store_name,(A)word_loc)fmap`] THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  UNDISCH_TAC `strong_locals_rel I (v35 INSERT v36 INSERT (domain (live:1 spt) DELETE v34 DELETE v33))
                 (wl_state_locals (st:(A,C,FFI)wl_state)) t` THEN
  REWRITE_TAC[strong_locals_rel_def; I_THM; lookup_insert; lookup_delete; IN_INSERT;
              IN_DELETE] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`n:num`; `v:(A)word_loc`] THEN
  ASM_CASES_TAC `n:num = v35` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n:num = v36` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n:num = v33` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  ASM_CASES_TAC `n:num = v34` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let WALLOCPAUX_rd_Tick = prove
 (`!live nlive lt (st:(A,C,FFI)wl_state). WALLOCPAUX_rd_Q st wl_Tick live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN
  ASM_CASES_TAC `wl_state_clock (st:(A,C,FFI)wl_state) = 0` THEN
  GVS[remove_dead_def; get_live_def; wl_evaluate_def; wl_flush_state_def; wl_dec_clock_def;
      wl_state_component_equality]);;

let WALLOCPAUX_rd_Install = prove
 (`!v48 v49 v50 v51 v52 live nlive lt (st:(A,C,FFI)wl_state).
       WALLOCPAUX_rd_Q st (wl_Install v48 v49 v50 v51 v52) live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN
  GVS[remove_dead_def; get_live_def; wl_evaluate_def; option_case_eq; pair_case_eq;
      case_eq "word_loc"; list_case_eq; COND_CASE_EQ; list_insert_def; wl_get_var_def;
      LET_DEF; LET_END_DEF] THEN
  WALLOCPAUX_TRANSFER_TAC THEN WALLOCPAUX_TRANSFER_CUT_TAC THEN GVS[] THEN
  MAP_EVERY EXISTS_TAC [`insert v48 (wl_Loc (x:num) 0) (a:((A)word_loc)spt)`;
                        `tstore:(store_name,(A)word_loc)fmap`] THEN
  ASM_REWRITE_TAC[WALLOCPAUX_strong_locals_rel_I_refl]);;

let WALLOCPAUX_rd_CodeBufferWrite = prove
 (`!v53 v54 live nlive lt (st:(A,C,FFI)wl_state).
       WALLOCPAUX_rd_Q st (wl_CodeBufferWrite v53 v54) live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN
  GVS[remove_dead_def; get_live_def; wl_evaluate_def; option_case_eq; pair_case_eq;
      case_eq "word_loc"; list_insert_def] THEN
  MAP_EVERY EXISTS_TAC [`t:((A)word_loc)spt`; `tstore:(store_name,(A)word_loc)fmap`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[WALLOCPAUX_get_var_I; IN_INSERT];
    MATCH_MP_TAC strong_locals_rel_subset THEN
    EXISTS_TAC `v54 INSERT v53 INSERT domain (live:1 spt)` THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[]]);;

let WALLOCPAUX_rd_DataBufferWrite = prove
 (`!v55 v56 live nlive lt (st:(A,C,FFI)wl_state).
       WALLOCPAUX_rd_Q st (wl_DataBufferWrite v55 v56) live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN
  GVS[remove_dead_def; get_live_def; wl_evaluate_def; option_case_eq; pair_case_eq;
      case_eq "word_loc"; list_insert_def] THEN
  MAP_EVERY EXISTS_TAC [`t:((A)word_loc)spt`; `tstore:(store_name,(A)word_loc)fmap`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[WALLOCPAUX_get_var_I; IN_INSERT];
    MATCH_MP_TAC strong_locals_rel_subset THEN
    EXISTS_TAC `v56 INSERT v55 INSERT domain (live:1 spt)` THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[]]);;

let WALLOCPAUX_rd_FFI = prove
 (`!v57 v58 v59 v60 v61 v62 live nlive lt (st:(A,C,FFI)wl_state).
       WALLOCPAUX_rd_Q st (wl_FFI v57 v58 v59 v60 v61 v62) live nlive lt`,
  WALLOCPAUX_RD_OPEN_TAC THEN
  GVS[remove_dead_def; get_live_def; wl_evaluate_def; option_case_eq; pair_case_eq;
      case_eq "word_loc"; case_eq "ffi_result"; list_case_eq; COND_CASE_EQ; wl_get_var_def;
      LET_DEF; LET_END_DEF] THEN
  WALLOCPAUX_TRANSFER_TAC THEN WALLOCPAUX_TRANSFER_CUT_TAC THEN GVS[] THEN
  TRY(REWRITE_TAC[wl_flush_state_def] THEN SIMP[] THEN NO_TAC) THEN
  MAP_EVERY EXISTS_TAC [`a:((A)word_loc)spt`; `tstore:(store_name,(A)word_loc)fmap`] THEN
  ASM_REWRITE_TAC[WALLOCPAUX_strong_locals_rel_I_refl]);;

let WALLOCPAUX_rd_ShareInst = prove
 (`!v63 v64 v65 live nlive lt (st:(A,C,FFI)wl_state).
       WALLOCPAUX_rd_Q st (ShareInst v63 v64 v65) live nlive lt`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `v63:memop` (cases "memop")) THEN
  WALLOCPAUX_RD_OPEN_TAC THEN
  FIRST_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o MATCH_MP WALLOCPAUX_flat_ShareInst) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `v65:(A)wl_exp`)) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[wl_evaluate_def; remove_dead_def]) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  GVS[get_live_def; get_live_exp_def; big_union_def;
      wl_word_exp_def; the_words_def; wl_get_var_def; share_inst_def; WALLOCPAUX_sh_mem_set_var_cases;
      wl_sh_mem_store_def; wl_sh_mem_load_def; wl_sh_mem_store_byte_def;
      wl_sh_mem_store16_def; wl_sh_mem_store32_def; wl_sh_mem_load_byte_def;
      wl_sh_mem_load16_def; wl_sh_mem_load32_def;
      option_case_eq; pair_case_eq; case_eq "word_loc"; case_eq "ffi_result";
      COND_CASE_EQ; wl_set_var_def; LET_DEF; LET_END_DEF] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  WALLOCPAUX_TRANSFER_TAC THEN
  GVS[wl_word_exp_def; the_words_def; wl_get_var_def; share_inst_def; WALLOCPAUX_sh_mem_set_var_cases;
      wl_sh_mem_store_def; wl_sh_mem_load_def; wl_sh_mem_store_byte_def;
      wl_sh_mem_store16_def; wl_sh_mem_store32_def; wl_sh_mem_load_byte_def;
      wl_sh_mem_load16_def; wl_sh_mem_load32_def; wl_set_var_def] THEN
  TRY(REWRITE_TAC[wl_flush_state_def] THEN SIMP[] THEN NO_TAC) THEN
  WALLOCPAUX_SLR_FINISH_TAC);;

(* HOL4 line 3900 *)
let evaluate_remove_dead = prove
 (CASE_TERM
  `!(prog:(A)wl_prog) live nlive lt prog' livein nlivein (st:(A,C,FFI)wl_state)
    t tstore res rst.
     strong_locals_rel I (domain livein) (wl_state_locals st) t /\
     live_store_rel nlivein (wl_state_store st) tstore /\
     wl_evaluate (prog,st) = (res,rst) /\
     flat_exp_conventions prog /\
     remove_dead prog live nlive lt = (prog',livein,nlivein) /\
     ~(res = SOME wl_Error)
     ==> ?t' tstore'.
           wl_evaluate (prog',wl_state_locals_fupd (K t) (wl_state_store_fupd (K tstore) st)) =
           (res,wl_state_locals_fupd (K t') (wl_state_store_fupd (K tstore') rst)) /\
           (match res with
              NONE ->
                strong_locals_rel I (domain live) (wl_state_locals rst) t' /\
                live_store_rel nlive (wl_state_store rst) tstore'
            | SOME (wordSem_Break n) ->
                wl_state_store rst = tstore' /\
                (match oEL n lt with
                   SOME (_,exit_names) ->
                     strong_locals_rel I (domain exit_names) (wl_state_locals rst) t'
                 | NONE -> T)
            | SOME (wordSem_Continue n) ->
                wl_state_store rst = tstore' /\
                (match oEL n lt with
                   SOME (names,_) ->
                     strong_locals_rel I (domain names) (wl_state_locals rst) t'
                 | NONE -> T)
            | SOME _ -> wl_state_locals rst = t' /\ wl_state_store rst = tstore')`,
  SUBGOAL_THEN
    `!prog live nlive lt (st:(A,C,FFI)wl_state). WALLOCPAUX_rd_Q st prog live nlive lt`
    MP_TAC THENL
   [MATCH_MP_TAC remove_dead_ind THEN REPEAT CONJ_TAC THENL
     (map MATCH_ACCEPT_TAC
       [WALLOCPAUX_rd_Move; WALLOCPAUX_rd_Inst; WALLOCPAUX_rd_Get; WALLOCPAUX_rd_OpCurrHeap;
        WALLOCPAUX_rd_LocValue; WALLOCPAUX_rd_Set; WALLOCPAUX_rd_Seq;
        WALLOCPAUX_rd_MustTerminate; WALLOCPAUX_rd_If; WALLOCPAUX_rd_CallSome;
        WALLOCPAUX_rd_CallNone; WALLOCPAUX_rd_Alloc; WALLOCPAUX_rd_Raise;
        WALLOCPAUX_rd_Return; WALLOCPAUX_rd_Loop; WALLOCPAUX_rd_Break;
        WALLOCPAUX_rd_Continue; WALLOCPAUX_rd_Skip; WALLOCPAUX_rd_Assign;
        WALLOCPAUX_rd_Store; WALLOCPAUX_rd_StoreConsts; WALLOCPAUX_rd_Tick;
        WALLOCPAUX_rd_Install; WALLOCPAUX_rd_CodeBufferWrite;
        WALLOCPAUX_rd_DataBufferWrite; WALLOCPAUX_rd_FFI; WALLOCPAUX_rd_ShareInst]);
    ALL_TAC] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`prog:(A)wl_prog`; `live:1 spt`; `nlive:store_name list`;
                               `lt:(1 spt#1 spt)list`; `st:(A,C,FFI)wl_state`]) THEN
  REWRITE_TAC[WALLOCPAUX_rd_Q_def] THEN DISCH_THEN(ACCEPT_TAC o SPEC_ALL));;

(* HOL4 line 4473 *)
let evaluate_remove_dead_prog = prove
 (CASE_TERM
  `!(prog:(A)wl_prog) (st:(A,C,FFI)wl_state) rst res.
     flat_exp_conventions prog /\
     wl_evaluate (prog,st) = (res,rst) /\
     ~(res = SOME wl_Error)
     ==> ?t'. wl_evaluate (remove_dead_prog prog,st) =
              (res,wl_state_locals_fupd (K t') rst) /\
              (match res with
                 NONE -> T
               | SOME (wordSem_Break _) -> T
               | SOME (wordSem_Continue _) -> T
               | SOME _ -> wl_state_locals rst = t')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[remove_dead_prog_def] THEN
  WALLOCPAUX_TUPLE_TAC
    `remove_dead (prog:(A)wl_prog) LN [] []:(A)wl_prog#1 spt#store_name list`
    [`p':(A)wl_prog`; `li:1 spt`; `nli:store_name list`] THEN
  REWRITE_TAC[FST] THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`; `LN:1 spt`; `[]:store_name list`;
    `[]:(1 spt#1 spt)list`; `p':(A)wl_prog`; `li:1 spt`; `nli:store_name list`;
    `st:(A,C,FFI)wl_state`; `wl_state_locals (st:(A,C,FFI)wl_state)`;
    `wl_state_store (st:(A,C,FFI)wl_state)`; `res:((A)wl_result)option`;
    `rst:(A,C,FFI)wl_state`] evaluate_remove_dead) THEN
  ASM_REWRITE_TAC[WALLOCPAUX_strong_locals_rel_I_refl; live_store_rel_refl;
                  word_allocProof_with_same_locals; with_same_store] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:((A)word_loc)spt` (X_CHOOSE_THEN
    `ts1:(store_name,(A)word_loc)fmap` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `ts1 = wl_state_store (rst:(A,C,FFI)wl_state)` SUBST_ALL_TAC THENL
   [POP_ASSUM MP_TAC THEN
    SPEC_TAC(`res:((A)wl_result)option`, `r:((A)wl_result)option`) THEN
    REWRITE_TAC[FORALL_OPTION_THM] THEN CONJ_TAC THENL
     [SIMP[live_store_rel_NIL];
      GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `a:(A)wl_result` (cases "wl_result")) THEN
      SIMP[]];
    ALL_TAC] THEN
  EXISTS_TAC `t1:((A)word_loc)spt` THEN
  ASM_REWRITE_TAC[with_same_store] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`res:((A)wl_result)option`, `r:((A)wl_result)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM] THEN CONJ_TAC THENL
   [SIMP[];
    GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `a:(A)wl_result` (cases "wl_result")) THEN
    SIMP[]]);;

(* HOL4 line 4506: val size_tac2 (ML) *)

(* HOL4 line 4510 *)
let ssa_locals_rel_def = cake_def
  `ssa_locals_rel na (ssa:num spt) (st_locs:A spt) (cst_locs:A spt) <=>
     (!x y. lookup x ssa = SOME y ==> y IN domain cst_locs) /\
     (!x y. lookup x st_locs = SOME y
            ==> x IN domain ssa /\
                lookup (THE (lookup x ssa)) cst_locs = SOME y /\
                (is_alloc_var x ==> x < na))`;;

(* HOL4 line 4523 *)
let ssa_map_ok_def = cake_def
  `ssa_map_ok na (ssa:num spt) <=>
     !x y. lookup x ssa = SOME y ==> ~is_phy_var y /\ y < na`;;

(* helper: is_alloc_var is preserved by adding 4 (HOL4 is_alloc_var_add, used *)
(* here before it is stated) *)

let WALLOCPAUX_is_alloc_var_add4 = prove
 (`!n. is_alloc_var n ==> is_alloc_var (n + 4)`,
  GEN_TAC THEN REWRITE_TAC[is_alloc_var_def] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `n + 4 = 1 * 4 + n`] THEN REWRITE_TAC[MOD_MULT_ADD]);;

(* HOL4 line 4529 *)
let list_next_var_rename_lemma_1 = prove
 (CASE_TERM
  `!ls (ssa:num spt) na ls' ssa' na'.
     list_next_var_rename ls ssa na = (ls',ssa',na')
     ==> let len = LENGTH ls in
           ALL_DISTINCT ls' /\
           ls' = MAP (\x. 4 * x + na) (COUNT_LIST len) /\
           na' = na + 4 * len`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[list_next_var_rename_def; next_var_rename_def; LENGTH; COUNT_LIST_DEF; MAP;
              ALL_DISTINCT; LET_DEF; LET_END_DEF; PAIR_EQ; pair_CASE] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[ALL_DISTINCT] THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename t (insert h na ssa) (na + 4)`
    [`ys:num list`; `s2:num spt`; `n2:num`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`insert h na (ssa:num spt)`; `na + 4`; `ys:num list`;
                                `s2:num spt`; `n2:num`]) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; pair_CASE; PAIR_EQ] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[ALL_DISTINCT; MAP_MAP_o; o_DEF; MEM_MAP; CONS_11] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[ARITH_RULE `~(na = 4 * x + na + 4)`];
    ARITH_TAC;
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN ARITH_TAC;
    ARITH_TAC]);;

(* HOL4 line 4561 *)
let list_next_var_rename_lemma_2 = prove
 (CASE_TERM
  `!ls (ssa:num spt) na.
     ALL_DISTINCT ls
     ==> let (ls',ssa',na') = list_next_var_rename ls ssa na in
           ls' = MAP (\x. THE (lookup x ssa')) ls /\
           domain ssa' = domain ssa UNION set_of_list ls /\
           (!x. ~MEM x ls ==> lookup x ssa' = lookup x ssa) /\
           (!x. MEM x ls ==> ?y. lookup x ssa' = SOME y)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[list_next_var_rename_def; next_var_rename_def; LET_DEF; LET_END_DEF;
              pair_CASE; ALL_DISTINCT; MAP; set_of_list; MEM; UNION_EMPTY] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`insert h na (ssa:num spt)`; `na + 4`]) THEN
  ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename t (insert h na ssa) (na + 4)`
    [`ys:num list`; `s2:num spt`; `n2:num`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lookup h (s2:num spt) = SOME na` ASSUME_TAC THENL
   [ASM_SIMP_TAC[lookup_insert]; ALL_TAC] THEN
  ASM_REWRITE_TAC[THE_DEF; CONS_11; domain_insert] THEN
  REPEAT CONJ_TAC THENL
   [SET_TAC[];
    REWRITE_TAC[DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[lookup_insert];
    ASM_MESON_TAC[]]);;

(* HOL4 line 4579 *)
let list_next_var_rename_lemma_2' = prove
 (`!ls (ssa:num spt) na ls' ssa' na'.
     list_next_var_rename ls ssa na = (ls',ssa',na')
     ==> ALL_DISTINCT ls
     ==> ls' = MAP (\x. THE (lookup x ssa')) ls /\
         domain ssa' = domain ssa UNION set_of_list ls /\
         (!x. ~MEM x ls ==> lookup x ssa' = lookup x ssa) /\
         (!x. MEM x ls ==> ?y. lookup x ssa' = SOME y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ls:num list`; `ssa:num spt`; `na:num`] list_next_var_rename_lemma_2) THEN
  ASM_REWRITE_TAC[pair_CASE]);;

(* HOL4 line 4594: val exists_tac (ML) *)

(* HOL4 line 4598 *)
let ssa_locals_rel_get_var = prove
 (`!na ssa (st:(A,C,FFI)wl_state) (cst:(A,C,FFI)wl_state) n x.
     ssa_locals_rel na ssa (wl_state_locals st) (wl_state_locals cst) /\
     wl_get_var n st = SOME x
     ==> wl_get_var (option_lookup ssa n) cst = SOME x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_get_var_def; ssa_locals_rel_def; option_lookup_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:(A)word_loc`]) THEN
  ASM_REWRITE_TAC[domain_lookup] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[option_CASE] THEN
  FIRST_X_ASSUM(MP_TAC o check (can (find_term ((=) `THE:(num)option->num`)) o concl)) THEN
  ASM_REWRITE_TAC[THE_DEF]);;

(* HOL4 line 4610 *)
let ssa_locals_rel_get_vars = prove
 (`!ls y na ssa (st:(A,C,FFI)wl_state) (cst:(A,C,FFI)wl_state).
     ssa_locals_rel na ssa (wl_state_locals st) (wl_state_locals cst) /\
     wl_get_vars ls st = SOME y
     ==> wl_get_vars (MAP (option_lookup ssa) ls) cst = SOME y`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wl_get_vars_def; MAP] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[option_case_eq; option_DISTINCT; option_INJ] THEN STRIP_TAC THEN
  EXISTS_TAC `a:(A)word_loc` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[ssa_locals_rel_get_var]; ALL_TAC] THEN
  EXISTS_TAC `a':((A)word_loc)list` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 4624 *)
let ssa_map_ok_extend = prove
 (`!na ssa h.
     ssa_map_ok na ssa /\ ~is_phy_var na ==> ssa_map_ok (na + 4) (insert h na ssa)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ssa_map_ok_def; lookup_insert] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ] THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `y:num`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[ARITH_RULE `y < na ==> y < na + 4`]]);;

(* HOL4 line 4636 *)
let merge_moves_frame = prove
 (CASE_TERM
  `!ls na ssaL ssaR.
     is_alloc_var na
     ==> let (moveL,moveR,na',ssaL',ssaR') = word_alloc_merge_moves ls ssaL ssaR na in
           is_alloc_var na' /\
           na <= na' /\
           (ssa_map_ok na ssaL ==> ssa_map_ok na' ssaL') /\
           (ssa_map_ok na ssaR ==> ssa_map_ok na' ssaR')`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[word_alloc_merge_moves_def; pair_CASE; LE_REFL] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`na:num`; `ssaL:num spt`; `ssaR:num spt`]) THEN
  ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `word_alloc_merge_moves t ssaL ssaR na`
    [`mL:(num#num)list`; `mR:(num#num)list`; `n1:num`; `sL:num spt`; `sR:num spt`] THEN
  REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  STRIP_TAC THEN
  CASES_ON `lookup h (sL:num spt)` THEN CASES_ON `lookup h (sR:num spt)` THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[WALLOCPAUX_is_alloc_var_add4];
    ASM_ARITH_TAC;
    ASM_MESON_TAC[ssa_map_ok_extend; convention_partitions];
    ASM_MESON_TAC[ssa_map_ok_extend; convention_partitions]]);;

(* HOL4 line 4667 *)
let merge_moves_fst = prove
 (CASE_TERM
  `!ls na (ssaL:num spt) (ssaR:num spt).
     let (moveL,moveR,na',ssaL',ssaR') = word_alloc_merge_moves ls ssaL ssaR na in
       na <= na' /\
       ALL (\x. x < na' /\ x >= na) (MAP FST moveL) /\
       ALL (\x. x < na' /\ x >= na) (MAP FST moveR)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[word_alloc_merge_moves_def; pair_CASE; LE_REFL; MAP; ALL] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`na:num`; `ssaL:num spt`; `ssaR:num spt`]) THEN
  WALLOCPAUX_TUPLE_TAC `word_alloc_merge_moves t ssaL ssaR na`
    [`mL:(num#num)list`; `mR:(num#num)list`; `n1:num`; `sL:num spt`; `sR:num spt`] THEN
  REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  STRIP_TAC THEN
  CASES_ON `lookup h (sL:num spt)` THEN CASES_ON `lookup h (sR:num spt)` THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[pair_CASE; MAP; ALL; FST] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  REPEAT STRIP_TAC THEN TRY(ASM_ARITH_TAC) THEN RES_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 4687 *)
let merge_moves_frame2 = prove
 (CASE_TERM
  `!ls na (ssaL:num spt) (ssaR:num spt).
     let (moveL,moveR,na',ssaL',ssaR') = word_alloc_merge_moves ls ssaL ssaR na in
       domain ssaL' = domain ssaL /\
       domain ssaR' = domain ssaR /\
       !x. MEM x ls /\ x IN domain (inter ssaL ssaR) ==> lookup x ssaL' = lookup x ssaR'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[word_alloc_merge_moves_def; pair_CASE; MEM] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`na:num`; `ssaL:num spt`; `ssaR:num spt`]) THEN
  WALLOCPAUX_TUPLE_TAC `word_alloc_merge_moves t ssaL ssaR na`
    [`mL:(num#num)list`; `mR:(num#num)list`; `n1:num`; `sL:num spt`; `sR:num spt`] THEN
  REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  STRIP_TAC THEN
  CASES_ON `lookup h (sL:num spt)` THEN CASES_ON `lookup h (sR:num spt)` THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[pair_CASE; domain_insert; lookup_insert; domain_inter; IN_INTER] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[domain_inter; IN_INTER]) THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC(SET_RULE `(h:num) IN s ==> h INSERT s = s`) THEN
      ASM_MESON_TAC[domain_lookup]) THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
  ASM_MESON_TAC[domain_lookup; lookup_NONE_domain; option_DISTINCT]);;

(* HOL4 line 4720 *)
let merge_moves_frame3 = prove
 (CASE_TERM
  `!ls na (ssaL:num spt) (ssaR:num spt).
     let (moveL,moveR,na',ssaL',ssaR') = word_alloc_merge_moves ls ssaL ssaR na in
       !x. ~MEM x ls \/ ~(x IN domain (inter ssaL ssaR))
           ==> lookup x ssaL' = lookup x ssaL /\ lookup x ssaR' = lookup x ssaR`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[word_alloc_merge_moves_def; pair_CASE; MEM] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`na:num`; `ssaL:num spt`; `ssaR:num spt`]) THEN
  MP_TAC(ISPECL [`t:num list`; `na:num`; `ssaL:num spt`; `ssaR:num spt`]
    merge_moves_frame2) THEN
  WALLOCPAUX_TUPLE_TAC `word_alloc_merge_moves t ssaL ssaR na`
    [`mL:(num#num)list`; `mR:(num#num)list`; `n1:num`; `sL:num spt`; `sR:num spt`] THEN
  REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT STRIP_TAC THEN
  CASES_ON `lookup h (sL:num spt)` THEN CASES_ON `lookup h (sR:num spt)` THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[pair_CASE; lookup_insert] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[domain_inter; IN_INTER; DE_MORGAN_THM]) THEN
  REWRITE_TAC[domain_inter; IN_INTER; DE_MORGAN_THM] THEN X_GEN_TAC `x:num` THEN
  ASM_CASES_TAC `x:num = h` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  TRY(FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `ssaR:num spt`)) (concl th) &&
        is_disj(fst(dest_imp(snd(dest_forall(concl th)))))))) THEN
  ASM_MESON_TAC[domain_lookup; lookup_NONE_domain; option_DISTINCT]);;

(* HOL4 line 4748 *)
let mov_eval_head = prove
 (`!p moves (st:(A,C,FFI)wl_state) rst x y.
     wl_evaluate (wl_Move p moves,st) = (NONE,rst) /\
     y IN domain (wl_state_locals st) /\
     ~MEM y (MAP FST moves) /\
     ~MEM x (MAP FST moves)
     ==> wl_evaluate (wl_Move p (CONS (x,y) moves),st) =
         (NONE,wl_state_locals_fupd
                 (K (insert x (THE (lookup y (wl_state_locals st))) (wl_state_locals rst)))
                 rst)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[MAP; ALL_DISTINCT; FST; SND; wl_get_vars_def; wl_get_var_def] THEN
  ASM_CASES_TAC `ALL_DISTINCT (MAP FST (moves:(num#num)list))` THEN
  ASM_REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN
  CASES_ON `wl_get_vars (MAP SND (moves:(num#num)list)) (st:(A,C,FFI)wl_state)` THEN
  ASM_REWRITE_TAC[option_CASE; PAIR_EQ; option_DISTINCT] THEN
  REWRITE_TAC[domain_lookup] THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE; THE_DEF] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_var o rhs o concl)) THEN
  REWRITE_TAC[wl_set_vars_def; alist_insert_def] THEN SIMP[]);;

(* HOL4 line 4763 *)
let merge_moves_correctL = prove
 (CASE_TERM
  `!ls na ssaL ssaR (stL:(A,C,FFI)wl_state) (cstL:(A,C,FFI)wl_state) pri.
     is_alloc_var na /\
     ALL_DISTINCT ls /\
     ssa_map_ok na ssaL
     ==> let (moveL,moveR,na',ssaL',ssaR') = word_alloc_merge_moves ls ssaL ssaR na in
         (ssa_locals_rel na ssaL (wl_state_locals stL) (wl_state_locals cstL)
          ==> let (resL,rcstL) = wl_evaluate (wl_Move pri moveL,cstL) in
                resL = NONE /\
                (!x. ~MEM x ls ==> lookup x ssaL' = lookup x ssaL) /\
                (!x y. x < na /\ lookup x (wl_state_locals cstL) = SOME y
                       ==> lookup x (wl_state_locals rcstL) = SOME y) /\
                ssa_locals_rel na' ssaL' (wl_state_locals stL) (wl_state_locals rcstL) /\
                word_state_eq_rel cstL rcstL)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[word_alloc_merge_moves_def; pair_CASE; MEM; ALL_DISTINCT] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    REWRITE_TAC[MAP; ALL_DISTINCT; wl_get_vars_def; option_CASE; pair_CASE] THEN
    REWRITE_TAC[wl_set_vars_def; alist_insert_def; word_allocProof_with_same_locals] THEN
    ASM_REWRITE_TAC[word_state_eq_rel_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`na:num`; `ssaL:num spt`; `ssaR:num spt`;
    `stL:(A,C,FFI)wl_state`; `cstL:(A,C,FFI)wl_state`; `pri:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:num list`; `na:num`; `ssaL:num spt`; `ssaR:num spt`]
    merge_moves_frame) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:num list`; `na:num`; `ssaL:num spt`; `ssaR:num spt`]
    merge_moves_fst) THEN
  MP_TAC(ISPECL [`t:num list`; `na:num`; `ssaL:num spt`; `ssaR:num spt`]
    merge_moves_frame3) THEN
  WALLOCPAUX_TUPLE_TAC `word_alloc_merge_moves t ssaL ssaR na`
    [`mL:(num#num)list`; `mR:(num#num)list`; `n1:num`; `sL:num spt`; `sR:num spt`] THEN
  REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT DISCH_TAC THEN
  CASES_ON `lookup h (sL:num spt)` THEN CASES_ON `lookup h (sR:num spt)` THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[pair_CASE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (wl_Move pri mL,cstL:(A,C,FFI)wl_state)`
    [`r0:((A)wl_result)option`; `rc:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THENL
   (replicate (ASM_REWRITE_TAC[DE_MORGAN_THM] THEN ASM_MESON_TAC[]) 4 @ [ALL_TAC]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  SUBGOAL_THEN `lookup h (ssaL:num spt) = SOME a` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `a < na /\ ~is_phy_var a` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ssa_map_ok_def]; ALL_TAC] THEN
  SUBGOAL_THEN `a IN domain (wl_state_locals (cstL:(A,C,FFI)wl_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[ssa_locals_rel_def]; ALL_TAC] THEN
  SUBGOAL_THEN `~MEM a (MAP FST (mL:(num#num)list))` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\x. x < n1 /\ x >= na) (MAP FST (mL:(num#num)list))` THEN
    UNDISCH_TAC `a < na` THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    MESON_TAC[ARITH_RULE `a < na ==> ~(a >= na)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `~MEM n1 (MAP FST (mL:(num#num)list))` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\x. x < n1 /\ x >= na) (MAP FST (mL:(num#num)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[LT_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`pri:num`; `mL:(num#num)list`; `cstL:(A,C,FFI)wl_state`;
                 `rc:(A,C,FFI)wl_state`; `n1:num`; `a:num`] mov_eval_head) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[pair_CASE] THEN
  SIMP[lookup_insert] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN SUBGOAL_THEN `~(x:num = n1)` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `x < na` THEN UNDISCH_TAC `na <= n1` THEN ARITH_TAC;
    ALL_TAC;
    UNDISCH_TAC `word_state_eq_rel (cstL:(A,C,FFI)wl_state) rc` THEN
    REWRITE_TAC[word_state_eq_rel_def] THEN SIMP[]] THEN
  REWRITE_TAC[ssa_locals_rel_def; lookup_insert; domain_insert; IN_INSERT] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
     [MESON_TAC[]; ASM_MESON_TAC[ssa_locals_rel_def]];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `x IN domain (sL:num spt) /\
                lookup (THE (lookup x sL)) (wl_state_locals (rc:(A,C,FFI)wl_state)) =
                SOME y /\
                (is_alloc_var x ==> x < n1)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ssa_locals_rel_def]; ALL_TAC] THEN
  ASM_CASES_TAC `x:num = h` THEN ASM_REWRITE_TAC[THE_DEF] THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `lookup a (wl_state_locals (cstL:(A,C,FFI)wl_state)) = SOME y`
        (fun th -> REWRITE_TAC[th; THE_DEF]) THEN
      UNDISCH_TAC `ssa_locals_rel na ssaL (wl_state_locals (stL:(A,C,FFI)wl_state))
                     (wl_state_locals (cstL:(A,C,FFI)wl_state))` THEN
      REWRITE_TAC[ssa_locals_rel_def] THEN
      DISCH_THEN(MP_TAC o SPECL [`h:num`; `y:(A)word_loc`] o CONJUNCT2) THEN
      ASM_MESON_TAC[THE_DEF];
      UNDISCH_TAC `is_alloc_var x ==> x < n1` THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[ARITH_RULE `h < n1 ==> h < n1 + 4`]];
    SUBGOAL_THEN `~(THE (lookup x (sL:num spt)) = n1)` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `x IN domain (sL:num spt)` THEN
      UNDISCH_TAC `ssa_map_ok n1 (sL:num spt)` THEN
      REWRITE_TAC[ssa_map_ok_def; domain_lookup] THEN DISCH_TAC THEN
      DISCH_THEN(X_CHOOSE_TAC `z:num`) THEN ASM_REWRITE_TAC[THE_DEF] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `z:num`]) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[LT_REFL];
      UNDISCH_TAC `is_alloc_var x ==> x < n1` THEN
      MESON_TAC[ARITH_RULE `x < n1 ==> x < n1 + 4`]]]);;

(* HOL4 line 4840 *)
let merge_moves_correctR = prove
 (CASE_TERM
  `!ls na ssaL ssaR (stR:(A,C,FFI)wl_state) (cstR:(A,C,FFI)wl_state) pri.
     is_alloc_var na /\
     ALL_DISTINCT ls /\
     ssa_map_ok na ssaR
     ==> let (moveL,moveR,na',ssaL',ssaR') = word_alloc_merge_moves ls ssaL ssaR na in
         (ssa_locals_rel na ssaR (wl_state_locals stR) (wl_state_locals cstR)
          ==> let (resR,rcstR) = wl_evaluate (wl_Move pri moveR,cstR) in
                resR = NONE /\
                (!x. ~MEM x ls ==> lookup x ssaR' = lookup x ssaR) /\
                (!x y. x < na /\ lookup x (wl_state_locals cstR) = SOME y
                       ==> lookup x (wl_state_locals rcstR) = SOME y) /\
                ssa_locals_rel na' ssaR' (wl_state_locals stR) (wl_state_locals rcstR) /\
                word_state_eq_rel cstR rcstR)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[word_alloc_merge_moves_def; pair_CASE; MEM; ALL_DISTINCT] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    REWRITE_TAC[MAP; ALL_DISTINCT; wl_get_vars_def; option_CASE; pair_CASE] THEN
    REWRITE_TAC[wl_set_vars_def; alist_insert_def; word_allocProof_with_same_locals] THEN
    ASM_REWRITE_TAC[word_state_eq_rel_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`na:num`; `ssaL:num spt`; `ssaR:num spt`;
    `stR:(A,C,FFI)wl_state`; `cstR:(A,C,FFI)wl_state`; `pri:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:num list`; `na:num`; `ssaL:num spt`; `ssaR:num spt`]
    merge_moves_frame) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:num list`; `na:num`; `ssaL:num spt`; `ssaR:num spt`]
    merge_moves_fst) THEN
  MP_TAC(ISPECL [`t:num list`; `na:num`; `ssaL:num spt`; `ssaR:num spt`]
    merge_moves_frame3) THEN
  WALLOCPAUX_TUPLE_TAC `word_alloc_merge_moves t ssaL ssaR na`
    [`mL:(num#num)list`; `mR:(num#num)list`; `n1:num`; `sL:num spt`; `sR:num spt`] THEN
  REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT DISCH_TAC THEN
  CASES_ON `lookup h (sL:num spt)` THEN CASES_ON `lookup h (sR:num spt)` THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[pair_CASE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (wl_Move pri mR,cstR:(A,C,FFI)wl_state)`
    [`r0:((A)wl_result)option`; `rc:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THENL
   (replicate (ASM_REWRITE_TAC[DE_MORGAN_THM] THEN ASM_MESON_TAC[]) 4 @ [ALL_TAC]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  SUBGOAL_THEN `lookup h (ssaR:num spt) = SOME a'` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `a' < na /\ ~is_phy_var a'` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ssa_map_ok_def]; ALL_TAC] THEN
  SUBGOAL_THEN `a' IN domain (wl_state_locals (cstR:(A,C,FFI)wl_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[ssa_locals_rel_def]; ALL_TAC] THEN
  SUBGOAL_THEN `~MEM a' (MAP FST (mR:(num#num)list))` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\x. x < n1 /\ x >= na) (MAP FST (mR:(num#num)list))` THEN
    UNDISCH_TAC `a' < na` THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    MESON_TAC[ARITH_RULE `a < na ==> ~(a >= na)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `~MEM n1 (MAP FST (mR:(num#num)list))` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\x. x < n1 /\ x >= na) (MAP FST (mR:(num#num)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[LT_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`pri:num`; `mR:(num#num)list`; `cstR:(A,C,FFI)wl_state`;
                 `rc:(A,C,FFI)wl_state`; `n1:num`; `a':num`] mov_eval_head) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[pair_CASE] THEN
  SIMP[lookup_insert] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN SUBGOAL_THEN `~(x:num = n1)` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `x < na` THEN UNDISCH_TAC `na <= n1` THEN ARITH_TAC;
    ALL_TAC;
    UNDISCH_TAC `word_state_eq_rel (cstR:(A,C,FFI)wl_state) rc` THEN
    REWRITE_TAC[word_state_eq_rel_def] THEN SIMP[]] THEN
  REWRITE_TAC[ssa_locals_rel_def; lookup_insert; domain_insert; IN_INSERT] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
     [MESON_TAC[]; ASM_MESON_TAC[ssa_locals_rel_def]];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `x IN domain (sR:num spt) /\
                lookup (THE (lookup x sR)) (wl_state_locals (rc:(A,C,FFI)wl_state)) =
                SOME y /\
                (is_alloc_var x ==> x < n1)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ssa_locals_rel_def]; ALL_TAC] THEN
  ASM_CASES_TAC `x:num = h` THEN ASM_REWRITE_TAC[THE_DEF] THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `lookup a' (wl_state_locals (cstR:(A,C,FFI)wl_state)) = SOME y`
        (fun th -> REWRITE_TAC[th; THE_DEF]) THEN
      UNDISCH_TAC `ssa_locals_rel na ssaR (wl_state_locals (stR:(A,C,FFI)wl_state))
                     (wl_state_locals (cstR:(A,C,FFI)wl_state))` THEN
      REWRITE_TAC[ssa_locals_rel_def] THEN
      DISCH_THEN(MP_TAC o SPECL [`h:num`; `y:(A)word_loc`] o CONJUNCT2) THEN
      ASM_MESON_TAC[THE_DEF];
      UNDISCH_TAC `is_alloc_var x ==> x < n1` THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[ARITH_RULE `h < n1 ==> h < n1 + 4`]];
    SUBGOAL_THEN `~(THE (lookup x (sR:num spt)) = n1)` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `x IN domain (sR:num spt)` THEN
      UNDISCH_TAC `ssa_map_ok n1 (sR:num spt)` THEN
      REWRITE_TAC[ssa_map_ok_def; domain_lookup] THEN DISCH_TAC THEN
      DISCH_THEN(X_CHOOSE_TAC `z:num`) THEN ASM_REWRITE_TAC[THE_DEF] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `z:num`]) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[LT_REFL];
      UNDISCH_TAC `is_alloc_var x ==> x < n1` THEN
      MESON_TAC[ARITH_RULE `x < n1 ==> x < n1 + 4`]]]);;

(* HOL4 line 4917 *)
let fake_moves_frame = prove
 (CASE_TERM
  `!prio ls na ssaL ssaR.
     is_alloc_var na
     ==> let (moveL:(A)wl_prog,moveR:(A)wl_prog,na',ssaL',ssaR') =
             fake_moves prio ls ssaL ssaR na in
           is_alloc_var na' /\
           na <= na' /\
           (ssa_map_ok na ssaL ==> ssa_map_ok na' ssaL') /\
           (ssa_map_ok na ssaR ==> ssa_map_ok na' ssaR')`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[fake_moves_def; pair_CASE; LE_REFL] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`na:num`; `ssaL:num spt`; `ssaR:num spt`]) THEN
  ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC
    `fake_moves prio t ssaL ssaR na:(A)wl_prog#(A)wl_prog#num#num spt#num spt`
    [`mL:(A)wl_prog`; `mR:(A)wl_prog`; `n1:num`; `sL:num spt`; `sR:num spt`] THEN
  REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  STRIP_TAC THEN
  CASES_ON `lookup h (sL:num spt)` THEN CASES_ON `lookup h (sR:num spt)` THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN REPEAT CONJ_TAC THENL
   (map (fun _ -> FIRST [ASM_MESON_TAC[WALLOCPAUX_is_alloc_var_add4]; ASM_ARITH_TAC;
                         ASM_MESON_TAC[ssa_map_ok_extend; convention_partitions]])
        (1--8)));;

(* helper: lookup_NONE_domain with quantified variables *)

let WALLOCPAUX_lookup_NONE = prove
 (`!k (t:A spt). lookup k t = NONE <=> ~(k IN domain t)`,
  REWRITE_TAC[lookup_NONE_domain]);;

(* HOL4 line 4948 *)
let fake_moves_frame2 = prove
 (CASE_TERM
  `!prio ls na (ssaL:num spt) (ssaR:num spt).
     let (moveL:(A)wl_prog,moveR:(A)wl_prog,na',ssaL',ssaR') =
         fake_moves prio ls ssaL ssaR na in
       domain ssaL' =
         domain ssaL UNION (set_of_list ls INTER (domain ssaR UNION domain ssaL)) /\
       domain ssaR' =
         domain ssaR UNION (set_of_list ls INTER (domain ssaR UNION domain ssaL)) /\
       !x. MEM x ls /\ ~(x IN domain (inter ssaL ssaR)) ==> lookup x ssaL' = lookup x ssaR'`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[fake_moves_def; pair_CASE; set_of_list; MEM; INTER_EMPTY; UNION_EMPTY] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`na:num`; `ssaL:num spt`; `ssaR:num spt`]) THEN
  WALLOCPAUX_TUPLE_TAC
    `fake_moves prio t ssaL ssaR na:(A)wl_prog#(A)wl_prog#num#num spt#num spt`
    [`mL:(A)wl_prog`; `mR:(A)wl_prog`; `n1:num`; `sL:num spt`; `sR:num spt`] THEN
  REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  STRIP_TAC THEN
  CASES_ON `lookup h (sL:num spt)` THEN CASES_ON `lookup h (sR:num spt)` THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EXTENSION; domain_inter; IN_UNION; IN_INTER;
                              IN_SET_OF_LIST]) THEN
  REWRITE_TAC[EXTENSION; domain_insert; domain_inter; IN_INSERT; IN_UNION; IN_INTER;
              IN_SET_OF_LIST; lookup_insert] THEN
  MP_TAC(ISPECL [`h:num`; `sL:num spt`] WALLOCPAUX_lookup_NONE) THEN
  MP_TAC(ISPECL [`h:num`; `sR:num spt`] WALLOCPAUX_lookup_NONE) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN REPEAT DISCH_TAC THEN
  REPEAT CONJ_TAC THEN TRY(X_GEN_TAC `x:num` THEN ASM_CASES_TAC `x:num = h`) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 4968 *)
let fake_moves_frame3 = prove
 (CASE_TERM
  `!prio ls na (ssaL:num spt) (ssaR:num spt).
     let (moveL:(A)wl_prog,moveR:(A)wl_prog,na',ssaL',ssaR') =
         fake_moves prio ls ssaL ssaR na in
       !x. ~MEM x ls \/ x IN domain (inter ssaL ssaR)
           ==> lookup x ssaL' = lookup x ssaL /\ lookup x ssaR' = lookup x ssaR`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[fake_moves_def; pair_CASE; MEM] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`na:num`; `ssaL:num spt`; `ssaR:num spt`]) THEN
  MP_TAC(ISPECL [`prio:((1,1)sum)option`; `t:num list`; `na:num`; `ssaL:num spt`;
                 `ssaR:num spt`] (INST_TYPE [`:A`,`:A`] fake_moves_frame2)) THEN
  WALLOCPAUX_TUPLE_TAC
    `fake_moves prio t ssaL ssaR na:(A)wl_prog#(A)wl_prog#num#num spt#num spt`
    [`mL:(A)wl_prog`; `mR:(A)wl_prog`; `n1:num`; `sL:num spt`; `sR:num spt`] THEN
  REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT STRIP_TAC THEN
  CASES_ON `lookup h (sL:num spt)` THEN CASES_ON `lookup h (sR:num spt)` THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; lookup_insert] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EXTENSION; domain_inter; IN_UNION; IN_INTER;
                              IN_SET_OF_LIST; DE_MORGAN_THM]) THEN
  REWRITE_TAC[domain_inter; IN_INTER; DE_MORGAN_THM] THEN
  MP_TAC(ISPECL [`h:num`; `sL:num spt`] WALLOCPAUX_lookup_NONE) THEN
  MP_TAC(ISPECL [`h:num`; `sR:num spt`] WALLOCPAUX_lookup_NONE) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `x:num` THEN ASM_CASES_TAC `x:num = h` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* helpers: a fake move, a one-element move                                 *)

let WALLOCPAUX_evaluate_fake_move = prove
 (`!v (s:(A,C,FFI)wl_state).
     wl_evaluate (fake_move v:(A)wl_prog,s) = (NONE,wl_set_var v (wl_Word (word 0)) s)`,
  REWRITE_TAC[fake_move_def] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[wl_inst_def; wl_assign_def; wl_word_exp_def] THEN SIMP[]);;

let WALLOCPAUX_evaluate_Move1 = prove
 (`!p x y (s:(A,C,FFI)wl_state).
     y IN domain (wl_state_locals s)
     ==> wl_evaluate (wl_Move p [(x,y)]:(A)wl_prog,s) =
         (NONE,wl_state_locals_fupd
                 (K (insert x (THE (lookup y (wl_state_locals s))) (wl_state_locals s))) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[domain_lookup] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[MAP; ALL_DISTINCT; MEM; wl_get_vars_def; wl_get_var_def] THEN
  ASM_REWRITE_TAC[option_CASE; THE_DEF] THEN
  REWRITE_TAC[wl_set_vars_def; alist_insert_def]);;

(* HOL4 line 4994 *)
let fake_moves_correctL = prove
 (CASE_TERM
  `!prio ls na ssaL ssaR (stL:(A,C,FFI)wl_state) (cstL:(A,C,FFI)wl_state).
     is_alloc_var na /\
     ALL_DISTINCT ls /\
     ssa_map_ok na ssaL
     ==> let (moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR na in
         (ssa_locals_rel na ssaL (wl_state_locals stL) (wl_state_locals cstL)
          ==> let (resL,rcstL) = wl_evaluate (moveL,cstL) in
                resL = NONE /\
                (!x. ~MEM x ls ==> lookup x ssaL' = lookup x ssaL) /\
                (!x y. x < na /\ lookup x (wl_state_locals cstL) = SOME y
                       ==> lookup x (wl_state_locals rcstL) = SOME y) /\
                ssa_locals_rel na' ssaL' (wl_state_locals stL) (wl_state_locals rcstL) /\
                word_state_eq_rel cstL rcstL)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[fake_moves_def; pair_CASE; MEM; ALL_DISTINCT] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN REWRITE_TAC[pair_CASE] THEN
    ASM_REWRITE_TAC[word_state_eq_rel_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`na:num`; `ssaL:num spt`; `ssaR:num spt`;
    `stL:(A,C,FFI)wl_state`; `cstL:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`prio:((1,1)sum)option`; `t:num list`; `na:num`; `ssaL:num spt`;
                 `ssaR:num spt`] (INST_TYPE [`:A`,`:A`] fake_moves_frame)) THEN
  ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC
    `fake_moves prio t ssaL ssaR na:(A)wl_prog#(A)wl_prog#num#num spt#num spt`
    [`mL:(A)wl_prog`; `mR:(A)wl_prog`; `n1:num`; `sL:num spt`; `sR:num spt`] THEN
  REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT DISCH_TAC THEN
  CASES_ON `lookup h (sL:num spt)` THEN CASES_ON `lookup h (sR:num spt)` THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (mL:(A)wl_prog,cstL:(A,C,FFI)wl_state)`
    [`r0:((A)wl_result)option`; `rc:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[DE_MORGAN_THM] THEN ASM_MESON_TAC[];
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    MP_TAC(ISPECL [`mL:(A)wl_prog`; `fake_move n1:(A)wl_prog`; `cstL:(A,C,FFI)wl_state`;
                   `rc:(A,C,FFI)wl_state`] WALLOCPAUX_seq_NONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[WALLOCPAUX_evaluate_fake_move; pair_CASE; wl_set_var_def] THEN
    SIMP[lookup_insert] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      REPEAT STRIP_TAC THEN SUBGOAL_THEN `~(x:num = n1)` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `x < na` THEN UNDISCH_TAC `na <= n1` THEN ARITH_TAC;
      ALL_TAC;
      UNDISCH_TAC `word_state_eq_rel (cstL:(A,C,FFI)wl_state) rc` THEN
      REWRITE_TAC[word_state_eq_rel_def] THEN SIMP[]] THEN
    REWRITE_TAC[ssa_locals_rel_def; lookup_insert; domain_insert; IN_INSERT] THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
       [MESON_TAC[]; ASM_MESON_TAC[ssa_locals_rel_def]];
      ALL_TAC] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `x IN domain (sL:num spt) /\
                  lookup (THE (lookup x sL)) (wl_state_locals (rc:(A,C,FFI)wl_state)) =
                  SOME y /\
                  (is_alloc_var x ==> x < n1)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[ssa_locals_rel_def]; ALL_TAC] THEN
    ASM_CASES_TAC `x:num = h` THENL
     [ASM_MESON_TAC[domain_lookup; option_DISTINCT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[THE_DEF] THEN SUBGOAL_THEN `~(THE (lookup x (sL:num spt)) = n1)` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `x IN domain (sL:num spt)` THEN
        UNDISCH_TAC `ssa_map_ok n1 (sL:num spt)` THEN
        REWRITE_TAC[ssa_map_ok_def; domain_lookup] THEN DISCH_TAC THEN
        DISCH_THEN(X_CHOOSE_TAC `z:num`) THEN ASM_REWRITE_TAC[THE_DEF] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `z:num`]) THEN ASM_REWRITE_TAC[] THEN
        MESON_TAC[LT_REFL];
        UNDISCH_TAC `is_alloc_var x ==> x < n1` THEN
        MESON_TAC[ARITH_RULE `x < n1 ==> x < n1 + 4`]];
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    SUBGOAL_THEN `a IN domain (wl_state_locals (rc:(A,C,FFI)wl_state))` ASSUME_TAC THENL
     [ASM_MESON_TAC[ssa_locals_rel_def]; ALL_TAC] THEN
    MP_TAC(ISPECL [`mL:(A)wl_prog`; `wl_Move (priority prio T) [(n1,a)]:(A)wl_prog`;
                   `cstL:(A,C,FFI)wl_state`; `rc:(A,C,FFI)wl_state`] WALLOCPAUX_seq_NONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[WALLOCPAUX_evaluate_Move1] THEN REWRITE_TAC[pair_CASE] THEN
    SIMP[lookup_insert] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      REPEAT STRIP_TAC THEN SUBGOAL_THEN `~(x:num = n1)` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `x < na` THEN UNDISCH_TAC `na <= n1` THEN ARITH_TAC;
      ALL_TAC;
      UNDISCH_TAC `word_state_eq_rel (cstL:(A,C,FFI)wl_state) rc` THEN
      REWRITE_TAC[word_state_eq_rel_def] THEN SIMP[]] THEN
    REWRITE_TAC[ssa_locals_rel_def; lookup_insert; domain_insert; IN_INSERT] THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
       [MESON_TAC[]; ASM_MESON_TAC[ssa_locals_rel_def]];
      ALL_TAC] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `x IN domain (sL:num spt) /\
                  lookup (THE (lookup x sL)) (wl_state_locals (rc:(A,C,FFI)wl_state)) =
                  SOME y /\
                  (is_alloc_var x ==> x < n1)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[ssa_locals_rel_def]; ALL_TAC] THEN
    ASM_CASES_TAC `x:num = h` THEN ASM_REWRITE_TAC[THE_DEF] THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `lookup a (wl_state_locals (rc:(A,C,FFI)wl_state)) = SOME y`
          (fun th -> REWRITE_TAC[th; THE_DEF]) THEN
        ASM_MESON_TAC[THE_DEF];
        UNDISCH_TAC `is_alloc_var x ==> x < n1` THEN ASM_REWRITE_TAC[] THEN
        MESON_TAC[ARITH_RULE `h < n1 ==> h < n1 + 4`]];
      SUBGOAL_THEN `~(THE (lookup x (sL:num spt)) = n1)` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `x IN domain (sL:num spt)` THEN
        UNDISCH_TAC `ssa_map_ok n1 (sL:num spt)` THEN
        REWRITE_TAC[ssa_map_ok_def; domain_lookup] THEN DISCH_TAC THEN
        DISCH_THEN(X_CHOOSE_TAC `z:num`) THEN ASM_REWRITE_TAC[THE_DEF] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `z:num`]) THEN ASM_REWRITE_TAC[] THEN
        MESON_TAC[LT_REFL];
        UNDISCH_TAC `is_alloc_var x ==> x < n1` THEN
        MESON_TAC[ARITH_RULE `x < n1 ==> x < n1 + 4`]]];
    ASM_REWRITE_TAC[DE_MORGAN_THM] THEN ASM_MESON_TAC[]]);;

(* HOL4 line 5089 *)
let fake_moves_correctR = prove
 (CASE_TERM
  `!prio ls na ssaL ssaR (stR:(A,C,FFI)wl_state) (cstR:(A,C,FFI)wl_state).
     is_alloc_var na /\
     ALL_DISTINCT ls /\
     ssa_map_ok na ssaR
     ==> let (moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR na in
         (ssa_locals_rel na ssaR (wl_state_locals stR) (wl_state_locals cstR)
          ==> let (resR,rcstR) = wl_evaluate (moveR,cstR) in
                resR = NONE /\
                (!x. ~MEM x ls ==> lookup x ssaR' = lookup x ssaR) /\
                (!x y. x < na /\ lookup x (wl_state_locals cstR) = SOME y
                       ==> lookup x (wl_state_locals rcstR) = SOME y) /\
                ssa_locals_rel na' ssaR' (wl_state_locals stR) (wl_state_locals rcstR) /\
                word_state_eq_rel cstR rcstR)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[fake_moves_def; pair_CASE; MEM; ALL_DISTINCT] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN REWRITE_TAC[pair_CASE] THEN
    ASM_REWRITE_TAC[word_state_eq_rel_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`na:num`; `ssaL:num spt`; `ssaR:num spt`;
    `stR:(A,C,FFI)wl_state`; `cstR:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`prio:((1,1)sum)option`; `t:num list`; `na:num`; `ssaL:num spt`;
                 `ssaR:num spt`] (INST_TYPE [`:A`,`:A`] fake_moves_frame)) THEN
  ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC
    `fake_moves prio t ssaL ssaR na:(A)wl_prog#(A)wl_prog#num#num spt#num spt`
    [`mL:(A)wl_prog`; `mR:(A)wl_prog`; `n1:num`; `sL:num spt`; `sR:num spt`] THEN
  REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT DISCH_TAC THEN
  CASES_ON `lookup h (sL:num spt)` THEN CASES_ON `lookup h (sR:num spt)` THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (mR:(A)wl_prog,cstR:(A,C,FFI)wl_state)`
    [`r0:((A)wl_result)option`; `rc:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[DE_MORGAN_THM] THEN ASM_MESON_TAC[];
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    SUBGOAL_THEN `a IN domain (wl_state_locals (rc:(A,C,FFI)wl_state))` ASSUME_TAC THENL
     [ASM_MESON_TAC[ssa_locals_rel_def]; ALL_TAC] THEN
    MP_TAC(ISPECL [`mR:(A)wl_prog`; `wl_Move (priority prio F) [(n1,a)]:(A)wl_prog`;
                   `cstR:(A,C,FFI)wl_state`; `rc:(A,C,FFI)wl_state`] WALLOCPAUX_seq_NONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[WALLOCPAUX_evaluate_Move1] THEN REWRITE_TAC[pair_CASE] THEN
    SIMP[lookup_insert] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      REPEAT STRIP_TAC THEN SUBGOAL_THEN `~(x:num = n1)` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `x < na` THEN UNDISCH_TAC `na <= n1` THEN ARITH_TAC;
      ALL_TAC;
      UNDISCH_TAC `word_state_eq_rel (cstR:(A,C,FFI)wl_state) rc` THEN
      REWRITE_TAC[word_state_eq_rel_def] THEN SIMP[]] THEN
    REWRITE_TAC[ssa_locals_rel_def; lookup_insert; domain_insert; IN_INSERT] THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
       [MESON_TAC[]; ASM_MESON_TAC[ssa_locals_rel_def]];
      ALL_TAC] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `x IN domain (sR:num spt) /\
                  lookup (THE (lookup x sR)) (wl_state_locals (rc:(A,C,FFI)wl_state)) =
                  SOME y /\
                  (is_alloc_var x ==> x < n1)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[ssa_locals_rel_def]; ALL_TAC] THEN
    ASM_CASES_TAC `x:num = h` THEN ASM_REWRITE_TAC[THE_DEF] THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `lookup a (wl_state_locals (rc:(A,C,FFI)wl_state)) = SOME y`
          (fun th -> REWRITE_TAC[th; THE_DEF]) THEN
        ASM_MESON_TAC[THE_DEF];
        UNDISCH_TAC `is_alloc_var x ==> x < n1` THEN ASM_REWRITE_TAC[] THEN
        MESON_TAC[ARITH_RULE `h < n1 ==> h < n1 + 4`]];
      SUBGOAL_THEN `~(THE (lookup x (sR:num spt)) = n1)` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `x IN domain (sR:num spt)` THEN
        UNDISCH_TAC `ssa_map_ok n1 (sR:num spt)` THEN
        REWRITE_TAC[ssa_map_ok_def; domain_lookup] THEN DISCH_TAC THEN
        DISCH_THEN(X_CHOOSE_TAC `z:num`) THEN ASM_REWRITE_TAC[THE_DEF] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `z:num`]) THEN ASM_REWRITE_TAC[] THEN
        MESON_TAC[LT_REFL];
        UNDISCH_TAC `is_alloc_var x ==> x < n1` THEN
        MESON_TAC[ARITH_RULE `x < n1 ==> x < n1 + 4`]]];
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    MP_TAC(ISPECL [`mR:(A)wl_prog`; `fake_move n1:(A)wl_prog`; `cstR:(A,C,FFI)wl_state`;
                   `rc:(A,C,FFI)wl_state`] WALLOCPAUX_seq_NONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[WALLOCPAUX_evaluate_fake_move; pair_CASE; wl_set_var_def] THEN
    SIMP[lookup_insert] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      REPEAT STRIP_TAC THEN SUBGOAL_THEN `~(x:num = n1)` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `x < na` THEN UNDISCH_TAC `na <= n1` THEN ARITH_TAC;
      ALL_TAC;
      UNDISCH_TAC `word_state_eq_rel (cstR:(A,C,FFI)wl_state) rc` THEN
      REWRITE_TAC[word_state_eq_rel_def] THEN SIMP[]] THEN
    REWRITE_TAC[ssa_locals_rel_def; lookup_insert; domain_insert; IN_INSERT] THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
       [MESON_TAC[]; ASM_MESON_TAC[ssa_locals_rel_def]];
      ALL_TAC] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `x IN domain (sR:num spt) /\
                  lookup (THE (lookup x sR)) (wl_state_locals (rc:(A,C,FFI)wl_state)) =
                  SOME y /\
                  (is_alloc_var x ==> x < n1)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[ssa_locals_rel_def]; ALL_TAC] THEN
    ASM_CASES_TAC `x:num = h` THENL
     [ASM_MESON_TAC[domain_lookup; option_DISTINCT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[THE_DEF] THEN SUBGOAL_THEN `~(THE (lookup x (sR:num spt)) = n1)` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `x IN domain (sR:num spt)` THEN
        UNDISCH_TAC `ssa_map_ok n1 (sR:num spt)` THEN
        REWRITE_TAC[ssa_map_ok_def; domain_lookup] THEN DISCH_TAC THEN
        DISCH_THEN(X_CHOOSE_TAC `z:num`) THEN ASM_REWRITE_TAC[THE_DEF] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `z:num`]) THEN ASM_REWRITE_TAC[] THEN
        MESON_TAC[LT_REFL];
        UNDISCH_TAC `is_alloc_var x ==> x < n1` THEN
        MESON_TAC[ARITH_RULE `x < n1 ==> x < n1 + 4`]];
    ASM_REWRITE_TAC[DE_MORGAN_THM] THEN ASM_MESON_TAC[]]);;

(* HOL4 line 5186 *)
let ssa_eq_rel_swap = prove
 (`!na ssaR (st:(A,C,FFI)wl_state) (cst:(A,C,FFI)wl_state) ssaL.
     ssa_locals_rel na ssaR (wl_state_locals st) (wl_state_locals cst) /\
     domain ssaL = domain ssaR /\
     (!x. lookup x ssaL = lookup x ssaR)
     ==> ssa_locals_rel na ssaL (wl_state_locals st) (wl_state_locals cst)`,
  REWRITE_TAC[ssa_locals_rel_def] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 5195 *)
let ssa_locals_rel_more = prove
 (`!na ssa (stlocs:A spt) cstlocs na'.
     ssa_locals_rel na ssa stlocs cstlocs /\ na <= na'
     ==> ssa_locals_rel na' ssa stlocs cstlocs`,
  REWRITE_TAC[ssa_locals_rel_def] THEN MESON_TAC[LTE_TRANS]);;

(* HOL4 line 5205 *)
let ssa_map_ok_more = prove
 (`!na ssa na'. ssa_map_ok na ssa /\ na <= na' ==> ssa_map_ok na' ssa`,
  REWRITE_TAC[ssa_map_ok_def] THEN MESON_TAC[LTE_TRANS]);;

(* HOL4 line 5215 *)
let get_var_ignore = prove
 (`!x (cst:(A,C,FFI)wl_state) y ls a.
     wl_get_var x cst = SOME y /\
     ~MEM x ls /\
     LENGTH ls = LENGTH a
     ==> wl_get_var x (wl_set_vars ls a cst) = SOME y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_get_var_def; wl_set_vars_def] THEN STRIP_TAC THEN
  SIMP[] THEN ASM_SIMP_TAC[lookup_alist_insert] THEN
  SUBGOAL_THEN `ALOOKUP (ZIP (ls:num list) (a:((A)word_loc)list)) x = NONE`
    SUBST1_TAC THENL [ASM_SIMP_TAC[ALOOKUP_ZIP_FAIL]; ASM_REWRITE_TAC[option_CASE]]);;

(* helper: word_state_eq_rel is transitive *)

let WALLOCPAUX_word_state_eq_rel_trans = prove
 (`!(s:(A,C,FFI)wl_state) t u.
     word_state_eq_rel s t /\ word_state_eq_rel t u ==> word_state_eq_rel s u`,
  REWRITE_TAC[word_state_eq_rel_def] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 5227 *)
let fix_inconsistencies_correctL = prove
 (CASE_TERM
  `!prio na ssaL ssaR.
     is_alloc_var na /\
     ssa_map_ok na ssaL
     ==> let (moveL:(A)wl_prog,moveR:(A)wl_prog,na',ssaU) =
             fix_inconsistencies prio ssaL ssaR na in
         (!(stL:(A,B,C)wl_state) (cstL:(A,B,C)wl_state).
            ssa_locals_rel na ssaL (wl_state_locals stL) (wl_state_locals cstL)
            ==> let (resL,rcstL) = wl_evaluate (moveL,cstL) in
                  resL = NONE /\
                  ssa_locals_rel na' ssaU (wl_state_locals stL) (wl_state_locals rcstL) /\
                  word_state_eq_rel cstL rcstL)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[fix_inconsistencies_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ABBREV_TAC `vu = MAP FST (toAList (union (ssaL:num spt) ssaR))` THEN
  SUBGOAL_THEN `ALL_DISTINCT (vu:num list)` ASSUME_TAC THENL
   [EXPAND_TAC "vu" THEN REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList]; ALL_TAC] THEN
  MP_TAC(ISPECL [`vu:num list`; `na:num`; `ssaL:num spt`; `ssaR:num spt`]
    merge_moves_frame) THEN ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `word_alloc_merge_moves vu ssaL ssaR na`
    [`mL:(num#num)list`; `mR:(num#num)list`; `n1:num`; `sL:num spt`; `sR:num spt`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  WALLOCPAUX_TUPLE_TAC
    `fake_moves prio vu sL sR n1:(A)wl_prog#(A)wl_prog#num#num spt#num spt`
    [`fL:(A)wl_prog`; `fR:(A)wl_prog`; `n2:num`; `tL:num spt`; `tR:num spt`] THEN
  REWRITE_TAC[pair_CASE] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`vu:num list`; `na:num`; `ssaL:num spt`; `ssaR:num spt`;
                 `stL:(A,B,C)wl_state`; `cstL:(A,B,C)wl_state`; `priority prio T`]
    merge_moves_correctL) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_TUPLE_TAC
    `wl_evaluate (wl_Move (priority prio T) mL:(A)wl_prog,cstL:(A,B,C)wl_state)`
    [`r1:((A)wl_result)option`; `c1:(A,B,C)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`prio:((1,1)sum)option`; `vu:num list`; `n1:num`; `sL:num spt`;
                 `sR:num spt`; `stL:(A,B,C)wl_state`; `c1:(A,B,C)wl_state`]
    fake_moves_correctL) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (fL:(A)wl_prog,c1:(A,B,C)wl_state)`
    [`r2:((A)wl_result)option`; `c2:(A,B,C)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`wl_Move (priority prio T) mL:(A)wl_prog`; `fL:(A)wl_prog`;
                 `cstL:(A,B,C)wl_state`; `c1:(A,B,C)wl_state`] WALLOCPAUX_seq_NONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN
  ASM_MESON_TAC[WALLOCPAUX_word_state_eq_rel_trans]);;

(* HOL4 line 5262 *)
let fix_inconsistencies_correctR = prove
 (CASE_TERM
  `!na ssaL ssaR prio.
     is_alloc_var na /\
     ssa_map_ok na ssaR
     ==> let (moveL:(A)wl_prog,moveR:(A)wl_prog,na',ssaU) =
             fix_inconsistencies prio ssaL ssaR na in
         (!(stR:(A,B,C)wl_state) (cstR:(A,B,C)wl_state).
            ssa_locals_rel na ssaR (wl_state_locals stR) (wl_state_locals cstR)
            ==> let (resR,rcstR) = wl_evaluate (moveR,cstR) in
                  resR = NONE /\
                  ssa_locals_rel na' ssaU (wl_state_locals stR) (wl_state_locals rcstR) /\
                  word_state_eq_rel cstR rcstR)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[fix_inconsistencies_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ABBREV_TAC `vu = MAP FST (toAList (union (ssaL:num spt) ssaR))` THEN
  SUBGOAL_THEN `ALL_DISTINCT (vu:num list)` ASSUME_TAC THENL
   [EXPAND_TAC "vu" THEN REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. MEM x vu <=> x IN domain (ssaL:num spt) \/ x IN domain (ssaR:num spt)`
    ASSUME_TAC THENL
   [EXPAND_TAC "vu" THEN REWRITE_TAC[toAList_domain; domain_union; IN_UNION]; ALL_TAC] THEN
  MP_TAC(ISPECL [`vu:num list`; `na:num`; `ssaL:num spt`; `ssaR:num spt`]
    merge_moves_frame) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`vu:num list`; `na:num`; `ssaL:num spt`; `ssaR:num spt`]
    merge_moves_frame2) THEN
  MP_TAC(ISPECL [`vu:num list`; `na:num`; `ssaL:num spt`; `ssaR:num spt`]
    merge_moves_frame3) THEN
  WALLOCPAUX_TUPLE_TAC `word_alloc_merge_moves vu ssaL ssaR na`
    [`mL:(num#num)list`; `mR:(num#num)list`; `n1:num`; `sL:num spt`; `sR:num spt`] THEN
  REWRITE_TAC[pair_CASE] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`prio:((1,1)sum)option`; `vu:num list`; `n1:num`; `sL:num spt`;
                 `sR:num spt`] (INST_TYPE [`:A`,`:A`] fake_moves_frame2)) THEN
  MP_TAC(ISPECL [`prio:((1,1)sum)option`; `vu:num list`; `n1:num`; `sL:num spt`;
                 `sR:num spt`] (INST_TYPE [`:A`,`:A`] fake_moves_frame3)) THEN
  WALLOCPAUX_TUPLE_TAC
    `fake_moves prio vu sL sR n1:(A)wl_prog#(A)wl_prog#num#num spt#num spt`
    [`fL:(A)wl_prog`; `fR:(A)wl_prog`; `n2:num`; `tL:num spt`; `tR:num spt`] THEN
  REWRITE_TAC[pair_CASE] THEN REPEAT DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`vu:num list`; `na:num`; `ssaL:num spt`; `ssaR:num spt`;
                 `stR:(A,B,C)wl_state`; `cstR:(A,B,C)wl_state`; `priority prio F`]
    merge_moves_correctR) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_TUPLE_TAC
    `wl_evaluate (wl_Move (priority prio F) mR:(A)wl_prog,cstR:(A,B,C)wl_state)`
    [`r1:((A)wl_result)option`; `c1:(A,B,C)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`prio:((1,1)sum)option`; `vu:num list`; `n1:num`; `sL:num spt`;
                 `sR:num spt`; `stR:(A,B,C)wl_state`; `c1:(A,B,C)wl_state`]
    fake_moves_correctR) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (fR:(A)wl_prog,c1:(A,B,C)wl_state)`
    [`r2:((A)wl_result)option`; `c2:(A,B,C)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`wl_Move (priority prio F) mR:(A)wl_prog`; `fR:(A)wl_prog`;
                 `cstR:(A,B,C)wl_state`; `c1:(A,B,C)wl_state`] WALLOCPAUX_seq_NONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[WALLOCPAUX_word_state_eq_rel_trans]] THEN
  MATCH_MP_TAC ssa_eq_rel_swap THEN EXISTS_TAC `tR:num spt` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_SET_OF_LIST] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:num` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[domain_inter; IN_INTER; DE_MORGAN_THM]) THEN
  ASM_CASES_TAC `x IN domain (ssaL:num spt) \/ x IN domain (ssaR:num spt)` THENL
   [ALL_TAC; ASM_MESON_TAC[lookup_NONE_domain]] THEN
  ASM_CASES_TAC `x IN domain (sL:num spt) /\ x IN domain (sR:num spt)` THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 5318: fun use_ALOOKUP_ALL_DISTINCT_MEM (ML tactic) *)

(* helpers: lookups in alist_insert away from and at the inserted keys *)

let WALLOCPAUX_lookup_alist_insert_notin = prove
 (`!ks vs (t:A spt) z.
     LENGTH ks = LENGTH vs /\ ~MEM z ks ==> lookup z (alist_insert ks vs t) = lookup z t`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[lookup_alist_insert] THEN
  SUBGOAL_THEN `ALOOKUP (ZIP (ks:num list) (vs:A list)) z = NONE` SUBST1_TAC THENL
   [ASM_SIMP_TAC[ALOOKUP_ZIP_FAIL]; REWRITE_TAC[option_CASE]]);;

let WALLOCPAUX_lookup_alist_insert_EL = prove
 (`!ks vs (t:A spt) k.
     ALL_DISTINCT ks /\ LENGTH ks = LENGTH vs /\ k < LENGTH ks
     ==> lookup (EL k ks) (alist_insert ks vs t) = SOME (EL k vs)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[lookup_alist_insert] THEN
  SUBGOAL_THEN `ALOOKUP (ZIP (ks:num list) (vs:A list)) (EL k ks) = SOME (EL k vs)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_SIMP_TAC[MAP_FST_ZIP; MEM_ZIP] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[option_CASE]]);;

(* the facts about list_next_var_rename that the move lemmas below use: the  *)
(* new names are at least na (and not physical when na is not), one per     *)
(* renamed variable                                                          *)

let WALLOCPAUX_LNVR_FACTS_TAC : tactic =
  MP_TAC(ISPECL [`ls:num list`; `ssa:num spt`; `na:num`] list_next_var_rename_lemma_2) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ls:num list`; `ssa:num spt`; `na:num`] list_next_var_rename_lemma_1) THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename ls ssa na`
    [`nls:num list`; `ssa1:num spt`; `na1:num`] THEN
  REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(MP_TAC o SPECL [`nls:num list`; `ssa1:num spt`; `na1:num`]) THEN
  REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z. MEM z nls ==> na <= z /\ (~is_phy_var na ==> ~is_phy_var z)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `nls:num list` &&
                             can (find_term ((=) `COUNT_LIST`)) (concl th)
                          then REWRITE_TAC[th] else failwith "") THEN
    REWRITE_TAC[MEM_MAP; is_phy_var_def] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THENL
     [ARITH_TAC;
      UNDISCH_TAC `z MOD 2 = 0` THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[ARITH_RULE `4 * x + na = (2 * x) * 2 + na`] THEN
      ASM_REWRITE_TAC[MOD_MULT_ADD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (nls:num list) = LENGTH (ls:num list) /\
                (!k. k < LENGTH ls ==> THE (lookup (EL k ls) ssa1) = EL k nls) /\
                (!x. MEM x ls ==> MEM (THE (lookup x ssa1)) nls)`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `nls:num list` &&
                             can (find_term ((=) `ssa1:num spt`)) (concl th)
                          then REWRITE_TAC[th] else failwith "") THEN
    SIMP_TAC[LENGTH_MAP; EL_MAP; MEM_MAP] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
           lhs(concl th) = `nls:num list`)));;

(* HOL4 line 5327 *)
let list_next_var_rename_move_preserve = prove
 (CASE_TERM
  `!(st:(A,C,FFI)wl_state) ssa na ls cst.
     ssa_locals_rel na ssa (wl_state_locals st) (wl_state_locals cst) /\
     set_of_list ls SUBSET domain (wl_state_locals st) /\
     ALL_DISTINCT ls /\
     ssa_map_ok na ssa /\
     word_state_eq_rel st cst
     ==> let (mov,ssa',na') = list_next_var_rename_move ssa na ls in
         let (res,rcst) = wl_evaluate (mov,cst) in
           res = NONE /\
           ssa_locals_rel na' ssa' (wl_state_locals st) (wl_state_locals rcst) /\
           word_state_eq_rel st rcst /\
           (~is_phy_var na
            ==> !w. is_phy_var w
                    ==> lookup w (wl_state_locals rcst) = lookup w (wl_state_locals cst)) /\
           (!x y. lookup x (wl_state_locals st) = SOME y
                  ==> lookup (THE (lookup x ssa)) (wl_state_locals rcst) = SOME y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[list_next_var_rename_move_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_LNVR_FACTS_TAC THEN
  ABBREV_TAC `vs = MAP (\x. THE (lookup x (wl_state_locals (st:(A,C,FFI)wl_state)))) ls` THEN
  SUBGOAL_THEN `wl_get_vars ls (st:(A,C,FFI)wl_state) = SOME vs` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ls:num list`; `st:(A,C,FFI)wl_state`] word_allocProof_get_vars_eq) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_get_vars (MAP (option_lookup ssa) ls) (cst:(A,C,FFI)wl_state) = SOME vs`
    ASSUME_TAC THENL [ASM_MESON_TAC[ssa_locals_rel_get_vars]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (vs:((A)word_loc)list) = LENGTH (ls:num list)` ASSUME_TAC THENL
   [EXPAND_TAC "vs" THEN REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP; LENGTH_MAP] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  REWRITE_TAC[wl_set_vars_def] THEN SIMP[] THEN
  SUBGOAL_THEN `!x y. lookup x (wl_state_locals (st:(A,C,FFI)wl_state)) = SOME y
                     ==> lookup (THE (lookup x ssa))
                           (alist_insert nls vs (wl_state_locals (cst:(A,C,FFI)wl_state))) =
                         SOME y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `x IN domain (ssa:num spt) /\
                  lookup (THE (lookup x ssa)) (wl_state_locals (cst:(A,C,FFI)wl_state)) =
                  SOME y` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[ssa_locals_rel_def]; ALL_TAC] THEN
    SUBGOAL_THEN `THE (lookup x (ssa:num spt)) < na` ASSUME_TAC THENL
     [UNDISCH_TAC `x IN domain (ssa:num spt)` THEN REWRITE_TAC[domain_lookup] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[THE_DEF] THEN ASM_MESON_TAC[ssa_map_ok_def];
      ALL_TAC] THEN
    SUBGOAL_THEN `~MEM (THE (lookup x (ssa:num spt))) nls` ASSUME_TAC THENL
     [ASM_MESON_TAC[NOT_LE]; ALL_TAC] THEN
    ASM_SIMP_TAC[WALLOCPAUX_lookup_alist_insert_notin];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `word_state_eq_rel (st:(A,C,FFI)wl_state) cst` THEN
    REWRITE_TAC[word_state_eq_rel_def] THEN SIMP[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC WALLOCPAUX_lookup_alist_insert_notin THEN
    ASM_MESON_TAC[]] THEN
  REWRITE_TAC[ssa_locals_rel_def] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:num`; `z:num`] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[domain_alist_insert; IN_UNION; IN_SET_OF_LIST] THEN
    ASM_CASES_TAC `MEM (x:num) ls` THENL
     [DISJ2_TAC THEN SUBGOAL_THEN `z = THE (lookup x (ssa1:num spt))` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[THE_DEF]; ASM_MESON_TAC[]];
      DISJ1_TAC THEN ASM_MESON_TAC[ssa_locals_rel_def]];
    MAP_EVERY X_GEN_TAC [`x:num`; `y:(A)word_loc`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `x IN domain (ssa:num spt) /\ (is_alloc_var x ==> x < na)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ssa_locals_rel_def]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[IN_UNION];
      ASM_CASES_TAC `MEM (x:num) ls` THENL
       [SUBGOAL_THEN `?k. k < LENGTH (ls:num list) /\ x = EL k ls` STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[MEM_EXISTS_EL]; ALL_TAC] THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[] THEN
        MP_TAC(ISPECL [`nls:num list`; `vs:((A)word_loc)list`;
                       `wl_state_locals (cst:(A,C,FFI)wl_state)`; `k:num`]
          WALLOCPAUX_lookup_alist_insert_EL) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        EXPAND_TAC "vs" THEN ASM_SIMP_TAC[EL_MAP; THE_DEF];
        ASM_SIMP_TAC[]];
      ASM_MESON_TAC[ARITH_RULE `x < na ==> x < na + 4 * l`]]]);;

(* HOL4 line 5434 *)
let option_lookup_subset_helper = prove
 (`!ssa (cst_locs:A spt) ls.
     (!x y. lookup x ssa = SOME y ==> y IN domain cst_locs) /\
     set_of_list ls SUBSET domain ssa
     ==> set_of_list (MAP (option_lookup ssa) ls) SUBSET domain cst_locs`,
  REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_MAP] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (is_var o lhs o concl)) THEN
  SUBGOAL_THEN `x' IN domain (ssa:num spt)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[domain_lookup]) THEN
  DISCH_THEN(X_CHOOSE_TAC `z:num`) THEN
  ASM_REWRITE_TAC[option_lookup_def; option_CASE] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `x':num` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 5448 *)
let list_next_var_rename_move_preserve_weak = prove
 (CASE_TERM
  `!(st:(A,C,FFI)wl_state) ssa na ls cst.
     ssa_locals_rel na ssa (wl_state_locals st) (wl_state_locals cst) /\
     set_of_list ls SUBSET domain ssa /\
     ALL_DISTINCT ls /\
     ssa_map_ok na ssa /\
     word_state_eq_rel st cst
     ==> let (mov,ssa',na') = list_next_var_rename_move ssa na ls in
         let (res,rcst) = wl_evaluate (mov,cst) in
           res = NONE /\
           ssa_locals_rel na' ssa' (wl_state_locals st) (wl_state_locals rcst) /\
           word_state_eq_rel st rcst`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[list_next_var_rename_move_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_LNVR_FACTS_TAC THEN
  ABBREV_TAC `cls = MAP (option_lookup ssa) (ls:num list)` THEN
  SUBGOAL_THEN `set_of_list cls SUBSET domain (wl_state_locals (cst:(A,C,FFI)wl_state))`
    ASSUME_TAC THENL
   [EXPAND_TAC "cls" THEN MATCH_MP_TAC option_lookup_subset_helper THEN
    ASM_MESON_TAC[ssa_locals_rel_def];
    ALL_TAC] THEN
  ABBREV_TAC `vs = MAP (\x. THE (lookup x (wl_state_locals (cst:(A,C,FFI)wl_state)))) cls` THEN
  SUBGOAL_THEN `wl_get_vars cls (cst:(A,C,FFI)wl_state) = SOME vs` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cls:num list`; `cst:(A,C,FFI)wl_state`] word_allocProof_get_vars_eq) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (vs:((A)word_loc)list) = LENGTH (ls:num list) /\
                LENGTH (cls:num list) = LENGTH ls` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["vs"; "cls"] THEN REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  REWRITE_TAC[wl_set_vars_def] THEN SIMP[] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `word_state_eq_rel (st:(A,C,FFI)wl_state) cst` THEN
    REWRITE_TAC[word_state_eq_rel_def] THEN SIMP[]] THEN
  REWRITE_TAC[ssa_locals_rel_def] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:num`; `z:num`] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[domain_alist_insert; IN_UNION; IN_SET_OF_LIST] THEN
    ASM_CASES_TAC `MEM (x:num) ls` THENL
     [DISJ2_TAC THEN SUBGOAL_THEN `z = THE (lookup x (ssa1:num spt))` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[THE_DEF]; ASM_MESON_TAC[]];
      DISJ1_TAC THEN ASM_MESON_TAC[ssa_locals_rel_def]];
    MAP_EVERY X_GEN_TAC [`x:num`; `y:(A)word_loc`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `x IN domain (ssa:num spt) /\
                  lookup (THE (lookup x ssa)) (wl_state_locals (cst:(A,C,FFI)wl_state)) =
                  SOME y /\
                  (is_alloc_var x ==> x < na)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ssa_locals_rel_def]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[IN_UNION];
      ASM_CASES_TAC `MEM (x:num) ls` THENL
       [SUBGOAL_THEN `?k. k < LENGTH (ls:num list) /\ x = EL k ls` STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[MEM_EXISTS_EL]; ALL_TAC] THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[] THEN
        MP_TAC(ISPECL [`nls:num list`; `vs:((A)word_loc)list`;
                       `wl_state_locals (cst:(A,C,FFI)wl_state)`; `k:num`]
          WALLOCPAUX_lookup_alist_insert_EL) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        MAP_EVERY EXPAND_TAC ["vs"; "cls"] THEN
        ASM_SIMP_TAC[EL_MAP; LENGTH_MAP] THEN
        UNDISCH_TAC `EL k ls IN domain (ssa:num spt)` THEN
        REWRITE_TAC[domain_lookup] THEN STRIP_TAC THEN
        UNDISCH_TAC `lookup (THE (lookup (EL k ls) ssa))
                       (wl_state_locals (cst:(A,C,FFI)wl_state)) = SOME y` THEN
        ASM_REWRITE_TAC[option_lookup_def; option_CASE; THE_DEF] THEN
        SIMP_TAC[THE_DEF];
        SUBGOAL_THEN `THE (lookup x (ssa:num spt)) < na` ASSUME_TAC THENL
         [UNDISCH_TAC `x IN domain (ssa:num spt)` THEN REWRITE_TAC[domain_lookup] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[THE_DEF] THEN ASM_MESON_TAC[ssa_map_ok_def];
          ALL_TAC] THEN
        SUBGOAL_THEN `~MEM (THE (lookup x (ssa:num spt))) nls` ASSUME_TAC THENL
         [ASM_MESON_TAC[NOT_LE]; ALL_TAC] THEN
        ASM_SIMP_TAC[WALLOCPAUX_lookup_alist_insert_notin]];
      ASM_MESON_TAC[ARITH_RULE `x < na ==> x < na + 4 * l`]]]);;

(* HOL4 line 5525 *)
let get_vars_list_insert_eq_gen = prove
 (`!(st:(A,C,FFI)wl_state) ls x locs a b.
     LENGTH ls = LENGTH x /\ ALL_DISTINCT ls /\
     LENGTH a = LENGTH b /\ (!e. MEM e ls ==> ~MEM e a)
     ==> wl_get_vars ls (wl_state_locals_fupd (K (alist_insert (APPEND a ls) (APPEND b x) locs)) st) =
         SOME x`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[alist_insert_append] THEN
  MP_TAC(ISPECL [`ls:num list`;
    `wl_state_locals_fupd (K (alist_insert a b (alist_insert ls x (locs:((A)word_loc)spt))))
       (st:(A,C,FFI)wl_state)`] word_allocProof_get_vars_eq) THEN
  ANTS_TAC THENL
   [SIMP[] THEN ASM_SIMP_TAC[domain_alist_insert] THEN SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  REWRITE_TAC[LIST_EQ] THEN ASM_REWRITE_TAC[LENGTH_MAP] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `k < LENGTH (ls:num list)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP] THEN SIMP[] THEN
  SUBGOAL_THEN `~MEM (EL k ls) (a:num list)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[MEM_EL]; ALL_TAC] THEN
  ASM_SIMP_TAC[WALLOCPAUX_lookup_alist_insert_notin; WALLOCPAUX_lookup_alist_insert_EL; THE_DEF]);;

(* HOL4 line 5546 *)
let get_vars_set_vars_eq = prove
 (`!(cst:(A,C,FFI)wl_state) ls x.
     ALL_DISTINCT ls /\ LENGTH x = LENGTH ls
     ==> wl_get_vars ls (wl_set_vars ls x cst) = SOME x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_set_vars_def] THEN
  MP_TAC(ISPECL [`cst:(A,C,FFI)wl_state`; `ls:num list`; `x:((A)word_loc)list`;
    `wl_state_locals (cst:(A,C,FFI)wl_state)`; `[]:num list`; `[]:((A)word_loc)list`]
    get_vars_list_insert_eq_gen) THEN
  REWRITE_TAC[APPEND; MEM; LENGTH] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 5557 *)
let ssa_locals_rel_ignore_set_var = prove
 (`!na ssa (st:(A,C,FFI)wl_state) (cst:(A,C,FFI)wl_state) v a.
     ssa_map_ok na ssa /\
     ssa_locals_rel na ssa (wl_state_locals st) (wl_state_locals cst) /\
     is_phy_var v
     ==> ssa_locals_rel na ssa (wl_state_locals st) (wl_state_locals (wl_set_var v a cst))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ssa_locals_rel_def; ssa_map_ok_def; wl_set_var_def] THEN
  SIMP[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[domain_insert; IN_INSERT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `y:(A)word_loc`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `k IN domain (ssa:num spt) /\
                lookup (THE (lookup k ssa)) (wl_state_locals (cst:(A,C,FFI)wl_state)) = SOME y /\
                (is_alloc_var k ==> k < na)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[lookup_insert] THEN
  UNDISCH_TAC `k IN domain (ssa:num spt)` THEN REWRITE_TAC[domain_lookup] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:num`) THEN ASM_REWRITE_TAC[THE_DEF] THEN
  ASM_CASES_TAC `z:num = v` THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]]);;

(* HOL4 line 5573 *)
let ssa_locals_rel_ignore_insert = prove
 (`!na ssa (stloc:A spt) cstloc v a.
     ssa_map_ok na ssa /\
     ssa_locals_rel na ssa stloc cstloc /\
     is_phy_var v
     ==> ssa_locals_rel na ssa stloc (insert v a cstloc)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ssa_locals_rel_def; ssa_map_ok_def] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[domain_insert; IN_INSERT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `y:A`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `k IN domain (ssa:num spt) /\
                lookup (THE (lookup k ssa)) (cstloc:A spt) = SOME y /\
                (is_alloc_var k ==> k < na)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[lookup_insert] THEN
  UNDISCH_TAC `k IN domain (ssa:num spt)` THEN REWRITE_TAC[domain_lookup] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:num`) THEN ASM_REWRITE_TAC[THE_DEF] THEN
  ASM_CASES_TAC `z:num = v` THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]]);;

(* HOL4 line 5590 *)
let ssa_locals_rel_ignore_list_insert = prove
 (`!na ssa (st:(A,C,FFI)wl_state) (cst:(A,C,FFI)wl_state) ls x.
     ssa_map_ok na ssa /\
     ssa_locals_rel na ssa (wl_state_locals st) (wl_state_locals cst) /\
     ALL is_phy_var ls /\
     LENGTH ls = LENGTH x
     ==> ssa_locals_rel na ssa (wl_state_locals st) (alist_insert ls x (wl_state_locals cst))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ssa_locals_rel_def; ssa_map_ok_def] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[domain_alist_insert; IN_UNION] THEN
  (* since HOL Light 2828953 ASM_SIMP_TAC proves the first conjunct itself *)
  TRY (CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `y:(A)word_loc`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `k IN domain (ssa:num spt) /\
                lookup (THE (lookup k ssa)) (wl_state_locals (cst:(A,C,FFI)wl_state)) = SOME y /\
                (is_alloc_var k ==> k < na)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `k IN domain (ssa:num spt)` THEN REWRITE_TAC[domain_lookup] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:num`) THEN
  SUBGOAL_THEN `~MEM (z:num) ls` ASSUME_TAC THENL
   [ASM_MESON_TAC[ALL_MEM]; ALL_TAC] THEN
  ASM_SIMP_TAC[WALLOCPAUX_lookup_alist_insert_notin; THE_DEF] THEN
  ASM_MESON_TAC[THE_DEF]);;

(* HOL4 line 5611 *)
let ssa_locals_rel_set_var = prove
 (`!na ssa (stl:A spt) cstl n w.
     ssa_locals_rel na ssa stl cstl /\
     ssa_map_ok na ssa /\
     n < na
     ==> ssa_locals_rel (na + 4) (insert n na ssa) (insert n w stl) (insert na w cstl)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ssa_locals_rel_def; ssa_map_ok_def] THEN
  STRIP_TAC THEN REWRITE_TAC[lookup_insert; domain_insert; IN_INSERT] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:num`; `y:num`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
     [MESON_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `y:A`] THEN
  ASM_CASES_TAC `k:num = n` THEN ASM_REWRITE_TAC[option_INJ; THE_DEF] THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[ARITH_RULE `n < na ==> n < na + 4`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `k IN domain (ssa:num spt) /\
                lookup (THE (lookup k ssa)) (cstl:A spt) = SOME y /\
                (is_alloc_var k ==> k < na)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `k IN domain (ssa:num spt)` THEN REWRITE_TAC[domain_lookup] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:num`) THEN
  SUBGOAL_THEN `z < na` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[THE_DEF] THEN
  SUBGOAL_THEN `~(z:num = na)` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `z < na` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[ARITH_RULE `k < na ==> k < na + 4`]);;

(* HOL4 line 5639 *)
let ssa_locals_rel_insert = prove
 (`!na ssa (stloc:A spt) cstloc n w.
     ssa_locals_rel na ssa stloc cstloc /\
     ssa_map_ok na ssa /\
     n < na
     ==> ssa_locals_rel (na + 4) (insert n na ssa) (insert n w stloc) (insert na w cstloc)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ssa_locals_rel_def; ssa_map_ok_def] THEN
  STRIP_TAC THEN REWRITE_TAC[lookup_insert; domain_insert; IN_INSERT] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:num`; `y:num`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
     [MESON_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `y:A`] THEN
  ASM_CASES_TAC `k:num = n` THEN ASM_REWRITE_TAC[option_INJ; THE_DEF] THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[ARITH_RULE `n < na ==> n < na + 4`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `k IN domain (ssa:num spt) /\
                lookup (THE (lookup k ssa)) (cstloc:A spt) = SOME y /\
                (is_alloc_var k ==> k < na)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `k IN domain (ssa:num spt)` THEN REWRITE_TAC[domain_lookup] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:num`) THEN
  SUBGOAL_THEN `z < na` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[THE_DEF] THEN
  SUBGOAL_THEN `~(z:num = na)` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `z < na` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[ARITH_RULE `k < na ==> k < na + 4`]);;

(* HOL4 line 5667: val is_phy_var_tac (ML) *)

(* HOL4 line 5673 *)
let ssa_locals_rel_list_next_var_rename = prove
 (`!xs ssa na (stloc:A spt) cstloc ys ssa' na' ls.
     list_next_var_rename xs ssa na = (ys,ssa',na') /\
     ssa_locals_rel na ssa stloc cstloc /\
     ssa_map_ok na ssa /\
     LENGTH xs = LENGTH ls /\
     ALL (\x. x < na) xs /\
     ALL_DISTINCT xs /\
     ~is_phy_var na
     ==> ssa_locals_rel na' ssa' (alist_insert xs ls stloc) (alist_insert ys ls cstloc)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[list_next_var_rename_def; PAIR_EQ; LENGTH] THEN
    STRIP_TAC THEN
    MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
                 check (fun th -> is_eq(concl th) && rhs(concl th) = v)))
      [`ys:num list`; `ssa':num spt`; `na':num`] THEN
    SUBGOAL_THEN `ls:A list = []` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[alist_insert_def];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`ssa:num spt`; `na:num`; `stloc:A spt`; `cstloc:A spt`;
                       `ys:num list`; `ssa':num spt`; `na':num`; `ls:A list`] THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `l:A` (X_CHOOSE_THEN `ls1:A list` SUBST1_TAC))
    (ISPEC `ls:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC] THEN
  REWRITE_TAC[list_next_var_rename_def; next_var_rename_def; LET_DEF; LET_END_DEF; pair_CASE] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename t (insert h na (ssa:num spt)) (na + 4)`
    [`ys0:num list`; `ssa0:num spt`; `na0:num`] THEN
  REWRITE_TAC[pair_CASE; PAIR_EQ; SUC_INJ; ALL; ALL_DISTINCT; alist_insert_def] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  STRIP_TAC THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
               check (fun th -> is_eq(concl th) && rhs(concl th) = v)))
    [`ys:num list`; `ssa':num spt`; `na':num`] THEN
  REWRITE_TAC[alist_insert_def] THEN
  SUBGOAL_THEN `~MEM na (ys0:num list)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:num list`; `insert h na (ssa:num spt)`; `na + 4`; `ys0:num list`;
                   `ssa0:num spt`; `na0:num`] list_next_var_rename_lemma_1) THEN
    ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[MEM_MAP] THEN
    MESON_TAC[ARITH_RULE `!x. ~(na = 4 * x + na + 4)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `insert h (l:A) (alist_insert t ls1 stloc) =
                  alist_insert t ls1 (insert h l stloc) /\
                insert na (l:A) (alist_insert ys0 ls1 cstloc) =
                  alist_insert ys0 ls1 (insert na l cstloc)`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC alist_insert_pull_insert THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ssa_locals_rel (na + 4) (insert h na ssa) (insert h (l:A) stloc)
                  (insert na l cstloc)` ASSUME_TAC THENL
   [MATCH_MP_TAC ssa_locals_rel_insert THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ssa_map_ok (na + 4) (insert h na ssa)` ASSUME_TAC THENL
   [MATCH_MP_TAC ssa_map_ok_extend THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\x. x < na + 4) t` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\x. x < na) t` THEN MATCH_MP_TAC MONO_ALL THEN
    REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~is_phy_var (na + 4)` ASSUME_TAC THENL
   [UNDISCH_TAC `~is_phy_var na` THEN REWRITE_TAC[is_phy_var_def] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `na + 4 = 2 * 2 + na`] THEN REWRITE_TAC[MOD_MULT_ADD];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`insert h na (ssa:num spt)`; `na + 4`; `insert h (l:A) stloc`;
     `insert na (l:A) cstloc`; `ys0:num list`; `ssa0:num spt`; `na0:num`; `ls1:A list`]) THEN
  ASM_REWRITE_TAC[]);;
