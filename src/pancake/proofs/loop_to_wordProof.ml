(* ========================================================================= *)
(* loop_to_wordProof: port of HOL4 pancake/proofs/loop_to_wordProofScript.sml *)
(* (CakeML v3479).                                                           *)
(* Correctness proof for loop_to_word.                                       *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says (loop_to_wordProof_locals_rel,              *)
(*   loop_to_wordProof_state_rel, loop_to_wordProof_compile_correct, ...);   *)
(*   local helpers that are not HOL4 theorems are PL2WAUX_.                  *)
(* - compile_correct: HOL4 states the conclusion of loopSem's evaluate_ind   *)
(*   for its predicate goal and proves the cases in suspend/Resume blocks.   *)
(*   Here PL2WAUX_goal is that predicate, PL2WAUX_case C the case of the     *)
(*   statement constructor C, each Resume block (with its sub-blocks) is     *)
(*   the theorem PL2WAUX_compile_correct_C, and compile_correct is assembled *)
(*   from them, quantified over prog and s (HOL4: !v v1. goal (v,v1)).       *)
(* - The find_code reasoning that HOL4 repeats for tail calls and calls      *)
(*   that return is the helper PL2WAUX_find_code.                            *)
(* - state_rel_imp_semantics is proved more directly than in HOL4:          *)
(*   compile_correct relates the two runs at the same clock, so the two     *)
(*   semantics agree clock by clock (no evaluate_add_clock reasoning).       *)
(* - s.f is loop_state_f s or wl_state_f s, s with f := v is                 *)
(*   ..._f_fupd (K v) s; set is set_of_list; EVERY is ALL; isEmpty t is     *)
(*   t = LN; UNIV is (:num); extract_labels is wordConvs_extract_labels.     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/backend_common.ml";;
needs "pancake/semantics/loopSem.ml";;
needs "pancake/semantics/loopProps.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "pancake/pan_common.ml";;
needs "pancake/semantics/pan_commonProps.ml";;
needs "pancake/loop_to_word.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4 temp_delsimps lift_disj_eq, lift_imp_disj, fromAList_def,           *)
(* domain_union, domain_inter, domain_difference, domain_map, map_def,     *)
(* lookup_rwts, insert_notEmpty, isEmpty_union: the kit has no file-local  *)
(* deletion (cake_del_simps acts everywhere), so the proofs here live with *)
(* the sptree rewrites of the kit's simpset.                                *)

(* HOL4: locals_rel_def *)

let loop_to_wordProof_locals_rel_def = cake_def
  `loop_to_wordProof_locals_rel ctxt (l1:(A)spt) (l2:(A)spt) <=>
     INJ (loop_to_word_find_var ctxt) (domain ctxt) (:num) /\
     (!n m. lookup n ctxt = SOME m ==> ~(m = 0) /\ EVEN m) /\
     !n v. lookup n l1 = SOME v ==>
           ?m. lookup n ctxt = SOME m /\ lookup m l2 = SOME v`;;

(* HOL4: globals_rel_def *)

let loop_to_wordProof_globals_rel_def = cake_def
  `loop_to_wordProof_globals_rel (g1:(5 word,A)fmap) (g2:(store_name,A)fmap) <=>
     !n v. FLOOKUP g1 n = SOME v ==> FLOOKUP g2 (Temp n) = SOME v`;;

(* HOL4: code_rel_def *)

let loop_to_wordProof_code_rel_def = cake_def
  `loop_to_wordProof_code_rel (s_code:(num list # (A)loop_prog)spt)
                              (t_code:(num # (A)wl_prog)spt) <=>
     !name params body.
       lookup name s_code = SOME (params,body) ==>
       lookup name t_code =
         SOME (LENGTH params + 1,loop_to_word_comp_func name params body) /\
       ALL_DISTINCT params`;;

(* HOL4: state_rel_def *)

let loop_to_wordProof_state_rel_def = cake_def
  `loop_to_wordProof_state_rel (s:(A,FFI)loop_state) (t:(A,C,FFI)wl_state) <=>
     ?len.
       wl_state_memory t = loop_state_memory s /\
       wl_state_mdomain t = loop_state_mdomain s /\
       wl_state_sh_mdomain t = loop_state_sh_mdomain s /\
       wl_state_clock t = loop_state_clock s /\
       wl_state_be t = loop_state_be s /\
       wl_state_ffi t = loop_state_ffi s /\
       ALOOKUP (fmap_to_alist (wl_state_store t)) CurrHeap =
         SOME (wl_Word (loop_state_base_addr s)) /\
       ALOOKUP (fmap_to_alist (wl_state_store t)) HeapLength = SOME (wl_Word len) /\
       loop_state_top_addr s = word_add (loop_state_base_addr s) (word_mul (word 2) len) /\
       loop_to_wordProof_globals_rel (loop_state_globals s) (wl_state_store t) /\
       loop_to_wordProof_code_rel (loop_state_code s) (wl_state_code t)`;;

(* HOL4: val goal (the predicate of the induction on loopSem's evaluate)   *)

let PL2WAUX_goal = CASE_TERM
 `\(prog:(A)loop_prog,s:(A,FFI)loop_state).
    !res s1 (t:(A,C,FFI)wl_state) ctxt retv l.
      loop_evaluate (prog,s) = (res,s1) /\ ~(res = SOME loop_Error) /\
      loop_to_wordProof_state_rel s t /\
      loop_to_wordProof_locals_rel ctxt (loop_state_locals s) (wl_state_locals t) /\
      lookup 0 (wl_state_locals t) = SOME retv /\
      good_dimindex(:A) /\
      ~(isWord retv) /\
      domain (acc_vars prog LN) SUBSET domain ctxt
      ==> ?t1 res1.
            wl_evaluate (FST (loop_to_word_comp ctxt prog l),t) = (res1,t1) /\
            wl_state_ffi t1 = loop_state_ffi s1 /\
            match res with
              NONE ->
                loop_to_wordProof_state_rel s1 t1 /\ res1 = NONE /\
                lookup 0 (wl_state_locals t1) = SOME retv /\
                loop_to_wordProof_locals_rel ctxt (loop_state_locals s1)
                  (wl_state_locals t1) /\
                wl_state_stack t1 = wl_state_stack t /\
                wl_state_handler t1 = wl_state_handler t
            | SOME (loop_Result v) ->
                loop_to_wordProof_state_rel s1 t1 /\
                res1 = SOME (wl_Result retv v) /\
                wl_state_stack t1 = wl_state_stack t /\
                wl_state_handler t1 = wl_state_handler t
            | SOME (loop_Exception v) ->
                loop_to_wordProof_state_rel s1 t1 /\
                (~(res1 = SOME wl_Error) ==> ?u1 u2. res1 = SOME (wl_Exception u1 u2)) /\
                (!r l1 l2.
                   wl_jump_exc (wl_state_stack_fupd (K (wl_state_stack t))
                                 (wl_state_handler_fupd (K (wl_state_handler t)) t1)) =
                     SOME (r,l1,l2)
                   ==> res1 = SOME (wl_Exception (wl_Loc l1 l2) v) /\ r = t1)
            | SOME (loopSem_Break n) ->
                loop_to_wordProof_state_rel s1 t1 /\ res1 = SOME (wordSem_Break n) /\
                lookup 0 (wl_state_locals t1) = SOME retv /\
                loop_to_wordProof_locals_rel ctxt (loop_state_locals s1)
                  (wl_state_locals t1) /\
                wl_state_stack t1 = wl_state_stack t /\
                wl_state_handler t1 = wl_state_handler t
            | SOME (loopSem_Continue n) ->
                loop_to_wordProof_state_rel s1 t1 /\ res1 = SOME (wordSem_Continue n) /\
                lookup 0 (wl_state_locals t1) = SOME retv /\
                loop_to_wordProof_locals_rel ctxt (loop_state_locals s1)
                  (wl_state_locals t1) /\
                wl_state_stack t1 = wl_state_stack t /\
                wl_state_handler t1 = wl_state_handler t
            | SOME loop_TimeOut -> res1 = SOME wl_TimeOut
            | SOME (loop_FinalFFI f) -> res1 = SOME (wl_FinalFFI f)
            | _ -> F`;;

(* HOL4: val ind_thm *)

let PL2WAUX_ind_thm =
  REWRITE_RULE[] (CONV_RULE (DEPTH_CONV GEN_BETA_CONV)
                    (ISPEC PL2WAUX_goal loop_evaluate_ind));;

(* the case of the induction for the statement constructor c (HOL4's      *)
(* suspend/Resume blocks of compile_correct are the theorems              *)
(* PL2WAUX_compile_correct_C, each proving one case)                      *)

let PL2WAUX_case c =
  let is_case cj =
    let b = snd(strip_forall cj) in
    let b = if is_imp b && is_forall(rand b) then snd(strip_forall(rand b))
            else b in
    let ev = hd(conjuncts(lhand b)) in
    let prog = fst(dest_pair(rand(lhs ev))) in
    name_of(fst(strip_comb prog)) = c in
  find is_case (conjuncts(lhand(concl PL2WAUX_ind_thm)));;

(* HOL4: locals_rel_intro *)

let loop_to_wordProof_locals_rel_intro = prove
 (`loop_to_wordProof_locals_rel ctxt (l1:(A)spt) l2 ==>
     INJ (loop_to_word_find_var ctxt) (domain ctxt) (:num) /\
     (!n m. lookup n ctxt = SOME m ==> ~(m = 0) /\ EVEN m) /\
     !n v. lookup n l1 = SOME v ==>
           ?m. lookup n ctxt = SOME m /\ lookup m l2 = SOME v`,
  REWRITE_TAC[loop_to_wordProof_locals_rel_def]);;

(* HOL4: globals_rel_intro *)

let loop_to_wordProof_globals_rel_intro = prove
 (`loop_to_wordProof_globals_rel (g1:(5 word,A)fmap) g2 ==>
     !n v. FLOOKUP g1 n = SOME v ==> FLOOKUP g2 (Temp n) = SOME v`,
  REWRITE_TAC[loop_to_wordProof_globals_rel_def]);;

(* HOL4: code_rel_intro *)

let loop_to_wordProof_code_rel_intro = prove
 (`loop_to_wordProof_code_rel (s_code:(num list # (A)loop_prog)spt) t_code ==>
     !name params body.
       lookup name s_code = SOME (params,body) ==>
       lookup name t_code =
         SOME (LENGTH params + 1,loop_to_word_comp_func name params body) /\
       ALL_DISTINCT params`,
  REWRITE_TAC[loop_to_wordProof_code_rel_def]);;

(* HOL4: state_rel_intro *)

let loop_to_wordProof_state_rel_intro = prove
 (`loop_to_wordProof_state_rel (s:(A,FFI)loop_state) (t:(A,C,FFI)wl_state) ==>
     wl_state_memory t = loop_state_memory s /\
     wl_state_mdomain t = loop_state_mdomain s /\
     wl_state_clock t = loop_state_clock s /\
     wl_state_be t = loop_state_be s /\
     wl_state_ffi t = loop_state_ffi s /\
     ALOOKUP (fmap_to_alist (wl_state_store t)) CurrHeap =
       SOME (wl_Word (loop_state_base_addr s)) /\
     loop_to_wordProof_globals_rel (loop_state_globals s) (wl_state_store t) /\
     loop_to_wordProof_code_rel (loop_state_code s) (wl_state_code t)`,
  REWRITE_TAC[loop_to_wordProof_state_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let find_var_neq_0 = prove
 (`v IN domain ctxt /\ loop_to_wordProof_locals_rel ctxt (lcl:(A)spt) lcl' ==>
     ~(loop_to_word_find_var ctxt v = 0)`,
  REWRITE_TAC[loop_to_wordProof_locals_rel_def; loop_to_word_find_var_def;
              domain_lookup] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE] THEN ASM_MESON_TAC[]);;

let find_var_neq_0_ctxt = prove
 (`(!n m. lookup n ctxt = SOME m ==> ~(m = 0) /\ EVEN m) /\ v IN domain ctxt ==>
     ~(loop_to_word_find_var ctxt v = 0)`,
  REWRITE_TAC[loop_to_word_find_var_def; domain_lookup] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE] THEN ASM_MESON_TAC[]);;

let find_var_neq_odd = prove
 (`(!n m. lookup n ctxt = SOME m ==> ~(m = 0) /\ EVEN m) /\ ~EVEN k ==>
     ~(loop_to_word_find_var ctxt v = k)`,
  REWRITE_TAC[loop_to_word_find_var_def] THEN STRIP_TAC THEN
  QCASES_ON "lookup v ctxt" THEN ASM_REWRITE_TAC[option_CASE] THEN
  ASM_MESON_TAC[EVEN]);;

(* the variable a key is mapped to (used for MESON steps below) *)

let PL2WAUX_find_var_lookup = prove
 (`!ctxt n m. lookup n ctxt = SOME m ==> loop_to_word_find_var ctxt n = m`,
  SIMP_TAC[loop_to_word_find_var_def; option_CASE]);;

let locals_rel_insert = prove
 (`loop_to_wordProof_locals_rel ctxt (lcl:(A)spt) lcl' /\ v IN domain ctxt ==>
     loop_to_wordProof_locals_rel ctxt (insert v w lcl)
       (insert (loop_to_word_find_var ctxt v) w lcl')`,
  REWRITE_TAC[loop_to_wordProof_locals_rel_def; lookup_insert] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `x:A`] THEN
  ASM_CASES_TAC `n:num = v` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `m:num` o REWRITE_RULE[domain_lookup]) THEN
    EXISTS_TAC `m:num` THEN ASM_SIMP_TAC[PL2WAUX_find_var_lookup];
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:A`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(m = loop_to_word_find_var ctxt v)`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[INJ; domain_lookup; PL2WAUX_find_var_lookup]]);;

let locals_rel_insert_unmapped = prove
 (`loop_to_wordProof_locals_rel ctxt (lcl:(A)spt) lcl' /\
   (!n. n IN domain ctxt ==> ~(loop_to_word_find_var ctxt n = k)) ==>
   loop_to_wordProof_locals_rel ctxt lcl (insert k x lcl')`,
  REWRITE_TAC[loop_to_wordProof_locals_rel_def; lookup_insert] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `y:A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(m:num = k)` (fun th -> ASM_REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[domain_lookup; PL2WAUX_find_var_lookup]);;

(* HOL4: locals_rel_alist_insert *)

let loop_to_wordProof_locals_rel_alist_insert = prove
 (`!vs ws (lcl:(A)spt) lcl'.
     loop_to_wordProof_locals_rel ctxt lcl lcl' /\ set_of_list vs SUBSET domain ctxt
     ==> loop_to_wordProof_locals_rel ctxt (alist_insert vs ws lcl)
           (alist_insert (MAP (loop_to_word_find_var ctxt) vs) ws lcl')`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[alist_insert_def; MAP] THENL
   [SIMP_TAC[]; ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[alist_insert_def] THENL
   [SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[set_of_list; INSERT_SUBSET] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC locals_rel_insert THEN ASM_SIMP_TAC[]);;

let locals_rel_ALL_DISTINCT_MAP = prove
 (`loop_to_wordProof_locals_rel ctxt (lcl:(A)spt) lcl' /\
   set_of_list xs SUBSET domain ctxt /\ ALL_DISTINCT xs ==>
   ALL_DISTINCT (MAP (loop_to_word_find_var ctxt) xs)`,
  REWRITE_TAC[loop_to_wordProof_locals_rel_def; INJ; SUBSET; IN_SET_OF_LIST] THEN
  STRIP_TAC THEN MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN ASM_MESON_TAC[]);;

let locals_rel_alist_insert_toAList = prove
 (`!vs ws (lcl:(A)spt) env.
     loop_to_wordProof_locals_rel ctxt lcl env /\ set_of_list vs SUBSET domain ctxt
     ==> loop_to_wordProof_locals_rel ctxt (alist_insert vs ws lcl)
           (alist_insert (MAP (loop_to_word_find_var ctxt) vs) ws
              (fromAList (toAList env)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC loop_to_wordProof_locals_rel_alist_insert THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_to_wordProof_locals_rel_def]) THEN
  ASM_REWRITE_TAC[loop_to_wordProof_locals_rel_def; lookup_fromAList_toAList]);;

(* HOL4: locals_rel_get_var *)

let loop_to_wordProof_locals_rel_get_var = prove
 (`loop_to_wordProof_locals_rel ctxt l (wl_state_locals (t:(A,C,FFI)wl_state)) /\
   lookup n l = SOME w
   ==> wl_get_var (loop_to_word_find_var ctxt n) t = SOME w`,
  REWRITE_TAC[loop_to_wordProof_locals_rel_def; wl_get_var_def] THEN
  ASM_MESON_TAC[PL2WAUX_find_var_lookup]);;

(* HOL4: locals_rel_get_vars *)

let loop_to_wordProof_locals_rel_get_vars = prove
 (`!argvars argvals.
     loop_to_wordProof_locals_rel ctxt (loop_state_locals (s:(A,FFI)loop_state))
       (wl_state_locals (t:(A,C,FFI)wl_state)) /\
     get_vars argvars s = SOME argvals
     ==> wl_get_vars (MAP (loop_to_word_find_var ctxt) argvars) t = SOME argvals /\
         LENGTH argvals = LENGTH argvars`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[get_vars_def; wl_get_vars_def; MAP] THENL
   [MESON_TAC[LENGTH; option_INJ]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN GVS_ASM[option_case_eq] THEN
  IMP_RES_TAC loop_to_wordProof_locals_rel_get_var THEN RES_TAC THEN
  ASM_REWRITE_TAC[option_CASE; LENGTH]);;

(* HOL4: state_rel_IMP [local] *)

let loop_to_wordProof_state_rel_IMP = prove
 (`loop_to_wordProof_state_rel (s:(A,FFI)loop_state) (t:(A,C,FFI)wl_state) ==>
     wl_state_clock t = loop_state_clock s`,
  REWRITE_TAC[loop_to_wordProof_state_rel_def] THEN MESON_TAC[]);;

let set_fromNumSet = prove
 (`set_of_list (fromNumSet t) = domain t`,
  REWRITE_TAC[fromNumSet_def; EXTENSION; IN_SET_OF_LIST; MEM_MAP;
              EXISTS_PAIR_THM; MEM_toAList; domain_lookup] THEN
  MESON_TAC[]);;

let domain_toNumSet = prove
 (`domain (toNumSet ps) = set_of_list ps`,
  SPEC_TAC(`ps:num list`,`ps:num list`) THEN
  LIST_INDUCT_TAC THEN FS[toNumSet_def; set_of_list]);;

let domain_make_ctxt = prove
 (`!n ps l. domain (make_ctxt n ps l) = domain l UNION set_of_list ps`,
  QINDUCT_ON "ps" THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[make_ctxt_def; set_of_list; UNION_EMPTY; domain_insert] THEN
  SET_TAC[]);;

let make_ctxt_inj = prove
 (`!xs l n.
     (!x y v. lookup x l = SOME v /\ lookup y l = SOME v ==> x = y /\ v < n) ==>
     (!x y v. lookup x (make_ctxt n xs l) = SOME v /\
              lookup y (make_ctxt n xs l) = SOME v ==> x = y)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[make_ctxt_def] THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o SPECL [`insert h n (l:num spt)`; `n + 2`]) THEN
  REWRITE_TAC[lookup_insert] THEN REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
  ASM_MESON_TAC[ARITH_RULE `n < n + 2`; LT_REFL;
                ARITH_RULE `v < n ==> v < n + 2`]);;

(* HOL4: make_ctxt_APPEND [local] *)

let make_ctxt_APPEND = prove
 (`!xs ys n l.
     make_ctxt n (APPEND xs ys) l =
     make_ctxt (n + 2 * LENGTH xs) ys (make_ctxt n xs l)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[make_ctxt_def; APPEND; LENGTH; MULT_CLAUSES; ADD_CLAUSES;
                  ADD_ASSOC]);;

(* HOL4: make_ctxt_NOT_MEM [local] *)

let make_ctxt_NOT_MEM = prove
 (`!xs n l x. ~MEM x xs ==> lookup x (make_ctxt n xs l) = lookup x l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[make_ctxt_def; MEM; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[lookup_insert]);;

let lookup_EL_make_ctxt = prove
 (`!params k n l.
     k < LENGTH params /\ ALL_DISTINCT params ==>
     lookup (EL k params) (make_ctxt n params l) = SOME (2 * k + n)`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; LT]; ALL_TAC] THEN
  REWRITE_TAC[LENGTH; ALL_DISTINCT; make_ctxt_def] THEN
  INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; LT_0; LT_SUC] THEN
  REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[make_ctxt_NOT_MEM; lookup_insert] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES];
    ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN ARITH_TAC]);;

let lookup_make_ctxt_range = prove
 (`!xs m l n y.
     lookup n (make_ctxt m xs l) = SOME y ==> lookup n l = SOME y \/ m <= y`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[make_ctxt_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m + 2`; `insert h m (l:num spt)`; `n:num`; `y:num`]) THEN
  ASM_REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_INJ] THEN
  MESON_TAC[ARITH_RULE `m + 2 <= y ==> m <= y`; LE_REFL]);;

let lookup_make_ctxt_EVEN = prove
 (`!xs m l n y.
     EVEN m /\ (!k v. lookup k l = SOME v ==> EVEN v) /\
     lookup n (make_ctxt m xs l) = SOME y ==> EVEN y`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[make_ctxt_def] THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m + 2`; `insert h m (l:num spt)`; `n:num`; `y:num`]) THEN
  ASM_REWRITE_TAC[EVEN_ADD; ARITH_EVEN; lookup_insert] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_INJ] THEN ASM_MESON_TAC[]);;

let locals_rel_make_ctxt = prove
 (`ALL_DISTINCT params /\ DISJOINT (set_of_list params) (set_of_list xs) /\
   LENGTH params = LENGTH (l:A list) ==>
   loop_to_wordProof_locals_rel (make_ctxt 2 (APPEND params xs) LN)
     (fromAList (ZIP params l)) (fromList2 (CONS retv l))`,
  REWRITE_TAC[loop_to_wordProof_locals_rel_def] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[INJ; IN_UNIV; domain_lookup] THEN
    MP_TAC(ISPECL [`APPEND (params:num list) xs`; `LN:num spt`; `2`] make_ctxt_inj) THEN
    REWRITE_TAC[lookup_def; option_DISTINCT] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `vx:num`)
                 (CONJUNCTS_THEN2 (X_CHOOSE_TAC `vy:num`) MP_TAC)) THEN
    ASM_SIMP_TAC[PL2WAUX_find_var_lookup] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP lookup_make_ctxt_range) THEN
      REWRITE_TAC[lookup_def; option_DISTINCT] THEN ARITH_TAC;
      MATCH_MP_TAC lookup_make_ctxt_EVEN THEN
      MAP_EVERY EXISTS_TAC [`APPEND (params:num list) xs`; `2`; `LN:num spt`; `n:num`] THEN
      ASM_REWRITE_TAC[lookup_def; option_DISTINCT; ARITH_EVEN]];
    MAP_EVERY X_GEN_TAC [`n:num`; `v:A`] THEN
    REWRITE_TAC[lookup_fromAList] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    ASM_SIMP_TAC[MEM_ZIP; PAIR_EQ; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~MEM (EL k params:num) xs` ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[IN_DISJOINT; IN_SET_OF_LIST]) THEN
      ASM_MESON_TAC[MEM_EL];
      ALL_TAC] THEN
    ASM_SIMP_TAC[make_ctxt_APPEND; make_ctxt_NOT_MEM; lookup_EL_make_ctxt] THEN
    REWRITE_TAC[option_INJ; UNWIND_THM1] THEN
    REWRITE_TAC[lookup_fromList2; EVEN_ADD; EVEN_DOUBLE; ARITH_EVEN] THEN
    SUBGOAL_THEN `(2 * k + 2) DIV 2 = SUC k` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 * k + 2 = 2 * SUC k`] THEN
      SIMP_TAC[DIV_MULT; ARITH_EQ];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[lookup_fromList; LENGTH; LT_SUC; EL; TL]]);;

let domain_mk_new_cutset_not_empty = prove
 (`~(domain (mk_new_cutset ctxt x1) = {})`,
  REWRITE_TAC[mk_new_cutset_def; domain_insert; NOT_INSERT_EMPTY]);;

(* the domain of a new cutset *)

let PL2WAUX_domain_mk_new_cutset = prove
 (`domain (mk_new_cutset ctxt x1) =
     0 INSERT IMAGE (loop_to_word_find_var ctxt) (domain x1)`,
  REWRITE_TAC[mk_new_cutset_def; domain_insert; domain_toNumSet; SET_OF_LIST_MAP;
              set_fromNumSet]);;

let cut_env_mk_new_cutset = prove
 (`loop_to_wordProof_locals_rel ctxt l1 (l2:(A)spt) /\ domain x1 SUBSET domain l1 /\
   lookup 0 l2 = SOME y ==>
   ?env1. wl_cut_env (mk_new_cutset ctxt x1,LN) l2 = SOME env1 /\
          loop_to_wordProof_locals_rel ctxt (sptree_inter l1 x1) env1`,
  STRIP_TAC THEN
  SUBGOAL_THEN `domain (mk_new_cutset ctxt x1) SUBSET domain (l2:(A)spt)` ASSUME_TAC THENL
   [REWRITE_TAC[PL2WAUX_domain_mk_new_cutset; INSERT_SUBSET] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; domain_lookup] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `v:num` THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[loop_to_wordProof_locals_rel_def; SUBSET; domain_lookup]) THEN
    ASM_MESON_TAC[PL2WAUX_find_var_lookup];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[wl_cut_env_def; cut_envs_def; cut_names_def; domain_def; EMPTY_SUBSET] THEN
  SIMP[] THEN
  UNDISCH_TAC `loop_to_wordProof_locals_rel ctxt l1 (l2:(A)spt)` THEN
  REWRITE_TAC[loop_to_wordProof_locals_rel_def; lookup_inter_alt;
              PL2WAUX_domain_mk_new_cutset; IN_INSERT; IN_IMAGE] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `v:A`] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `m:num` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?x. m = loop_to_word_find_var ctxt x /\ x IN domain (x1:num_set)`
    (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[PL2WAUX_find_var_lookup]);;

let env_to_list_IMP = prove
 (`env_to_list (env1:((A)word_loc)spt) (wl_state_permute (t:(A,C,FFI)wl_state)) =
     (l,permute) ==>
     domain (fromAList l) = domain env1 /\
     !x. lookup x (fromAList l) = lookup x env1`,
  DISCH_THEN(MP_TAC o MATCH_MP env_to_list_lookup_equiv) THEN
  SIMP_TAC[EXTENSION; domain_lookup; lookup_fromAList]);;

let cut_env_LN_IMP = prove
 (`wl_cut_env (s,LN) l = SOME (env:(A)spt) ==> cut_envs (s,LN) l = SOME (env,LN)`,
  REWRITE_TAC[wl_cut_env_def; cut_envs_def; cut_names_def] THEN
  COND_CASES_TAC THEN SIMP[]);;

let env_to_list_LN_IMP = prove
 (`env_to_list (LN:((A)word_loc)spt) l = (x,p) ==> x = []`,
  DISCH_THEN(MP_TAC o CONJUNCT2 o MATCH_MP env_to_list_lookup_equiv) THEN
  REWRITE_TAC[lookup_def; option_DISTINCT] THEN
  STRUCT_CASES_TAC(ISPEC `x:(num#(A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[MEM] THEN MESON_TAC[PAIR]);;

let cut_env_mk_new_cutset_IMP = prove
 (`wl_cut_env (mk_new_cutset ctxt x1,LN) l1 = SOME (l2:(A)spt) ==>
     lookup 0 l2 = lookup 0 l1`,
  REWRITE_TAC[wl_cut_env_def; cut_envs_def; cut_names_def] THEN
  COND_CASES_TAC THEN SIMP[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[lookup_inter_alt; PL2WAUX_domain_mk_new_cutset; IN_INSERT]);;

(* HOL4: LASTN_ADD_CONS [local] *)

let LASTN_ADD_CONS = prove
 (`~(LENGTH xs <= n) ==> LASTN (n + 1) (CONS (x:A) xs) = LASTN (n + 1) xs`,
  DISCH_TAC THEN MATCH_MP_TAC LASTN_TL THEN ASM_ARITH_TAC);;

(* HOL4: word_sh_SOME_MOD_dimword [local] *)

let word_sh_SOME_MOD_dimword = prove
 (`good_dimindex (:A) /\ word_sh sh (w:A word) n = SOME z ==>
     n MOD dimword (:A) = n`,
  REWRITE_TAC[word_sh_def; good_dimindex_def; dimword_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LE; GE; NOT_LT]) THEN
  STRIP_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

(* the arguments of an Op: each one that evaluates is compiled correctly *)

let PL2WAUX_the_words_comp_exp = prove
 (`!l (s:(A,FFI)loop_state) (ts:(A,C,FFI)wl_state) ctxt.
     (!a v. MEM a l /\ loop_eval s a = SOME v
            ==> wl_word_exp ts (comp_exp ctxt a) = SOME v)
     ==> !ws. the_words (MAP (loop_eval s) l) = SOME ws
              ==> the_words (MAP (wl_word_exp ts) (MAP (comp_exp ctxt) l)) = SOME ws`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; the_words_def; MEM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  QBY "!ws. the_words (MAP (loop_eval s) t) = SOME ws ==>
            the_words (MAP (wl_word_exp ts) (MAP (comp_exp ctxt) t)) = SOME ws"
    (ASM_MESON_TAC[]) THEN
  GVS_ASM[option_case_eq; case_eq "word_loc"; pair_case_eq] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:(A)loop_exp`) THEN
  ASM_REWRITE_TAC[option_INJ; FORALL_UNWIND_THM1] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

(* HOL4: comp_exp_preserves_eval *)

let loop_to_wordProof_comp_exp_preserves_eval = prove
 (`!s (e:(A)loop_exp) v (t:(A,C,FFI)wl_state) ctxt.
     loop_eval s e = SOME v /\ good_dimindex(:A) /\
     loop_to_wordProof_state_rel s t /\
     loop_to_wordProof_locals_rel ctxt (loop_state_locals s) (wl_state_locals t)
     ==> wl_word_exp t (comp_exp ctxt e) = SOME v`,
  MATCH_MP_TAC loop_eval_ind THEN
  REWRITE_TAC[loop_eval_def; comp_exp_def; wl_word_exp_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT CONJ_TAC THENL
   [(* Const *)
    MESON_TAC[];
    (* Var *)
    MESON_TAC[loop_to_wordProof_locals_rel_get_var];
    (* Lookup *)
    REWRITE_TAC[wl_get_store_def; loop_to_wordProof_state_rel_def;
                loop_to_wordProof_globals_rel_def] THEN MESON_TAC[];
    (* Load *)
    REPEAT STRIP_TAC THEN GVS_ASM[option_case_eq; case_eq "word_loc"] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:(A,C,FFI)wl_state`; `ctxt:num spt`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SIMP[] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[loop_to_wordProof_state_rel_def; wl_mem_load_def; loop_mem_load_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    (* Op *)
    REPEAT STRIP_TAC THEN GVS_ASM[option_case_eq] THEN
    MP_TAC(ISPECL [`wexps:((A)loop_exp)list`; `s:(A,FFI)loop_state`;
                   `t:(A,C,FFI)wl_state`; `ctxt:num spt`] PL2WAUX_the_words_comp_exp) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(SUBST1_TAC o MATCH_MP th)) THEN
    ASM_REWRITE_TAC[option_CASE; OPTION_MAP_DEF];
    (* Shift *)
    REPEAT STRIP_TAC THEN GVS_ASM[option_case_eq; case_eq "word_loc"] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPECL [`t:(A,C,FFI)wl_state`; `ctxt:num spt`]) THEN
           ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC) THEN
    SIMP[] THEN ASM_REWRITE_TAC[];
    (* BaseAddr *)
    REWRITE_TAC[wl_get_store_def; loop_to_wordProof_state_rel_def; ALOOKUP_EQ_FLOOKUP] THEN
    MESON_TAC[];
    (* TopAddr: the shift by one is the multiplication by two *)
    REWRITE_TAC[wl_get_store_def; loop_to_wordProof_state_rel_def; ALOOKUP_EQ_FLOOKUP] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[MAP; the_words_def] THEN SIMP[] THEN
    ASM_REWRITE_TAC[wl_word_exp_def; wl_get_store_def] THEN
    SIMP[word_sh_def; VAL_WORD_1; word_op_def] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[good_dimindex_def]) THEN
    SUBGOAL_THEN `~(1 >= dimindex(:A))` (fun th -> REWRITE_TAC[th]) THENL
     [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC; ALL_TAC] THEN
    SIMP[ITLIST; WORD_ADD_0; WORD_MUL_LSL; EXP_1] THEN
    ASM_MESON_TAC[option_INJ]]);;

(* HOL4: evaluate_tick_unfold [local] *)

let evaluate_tick_unfold = prove
 (`wl_evaluate (wl_Tick:(A)wl_prog,(s:(A,C,FFI)wl_state)) =
     if wl_state_clock s = 0 then (SOME wl_TimeOut,wl_flush_state T s)
     else (NONE,wl_dec_clock s)`,
  REWRITE_TAC[wl_evaluate_def]);;

(* HOL4: evaluate_tick_loop_tick_unfold [local] *)

let evaluate_tick_loop_tick_unfold = prove
 (`~(wl_state_clock (t1:(A,C,FFI)wl_state) = 0) ==>
   wl_evaluate (wl_Seq wl_Tick (wl_Seq (wl_Loop names body exit_names) wl_Tick),t1) =
   (\(res',s1).
      if res' = NONE then
        if wl_state_clock s1 = 0 then (SOME wl_TimeOut,wl_flush_state T s1)
        else (NONE,wl_state_clock_fupd (K (wl_state_clock s1 - 1)) s1)
      else (res',s1))
   (wl_evaluate (wl_Loop names body exit_names,
                 wl_state_clock_fupd (K (wl_state_clock t1 - 1)) t1))`,
  DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [wl_evaluate_def] THEN
  ASM_REWRITE_TAC[evaluate_tick_unfold] THEN SIMP[] THEN
  GEN_REWRITE_TAC LAND_CONV [wl_evaluate_def] THEN
  REWRITE_TAC[evaluate_tick_unfold; wl_dec_clock_def] THEN
  SPEC_TAC(`wl_evaluate (wl_Loop names body exit_names,
              wl_state_clock_fupd (K (wl_state_clock t1 - 1)) (t1:(A,C,FFI)wl_state))`,
           `p:((A)wl_result)option # (A,C,FFI)wl_state`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP[]);;

(* ------------------------------------------------------------------------- *)
(* The cases of compile_correct (HOL4 Resume blocks).                        *)
(* ------------------------------------------------------------------------- *)

(* HOL4: Resume compile_correct[Skip] *)

let PL2WAUX_compile_correct_Skip = prove
 (PL2WAUX_case "loop_Skip",
  REPEAT STRIP_TAC THEN
  GVS[loop_evaluate_def; loop_to_word_comp_def; wl_evaluate_def] THEN
  FS[loop_to_wordProof_state_rel_def]);;

(* HOL4: Resume compile_correct[Fail] *)

let PL2WAUX_compile_correct_Fail = prove
 (PL2WAUX_case "loop_Fail",
  REPEAT STRIP_TAC THEN
  GVS[loop_evaluate_def; loop_to_word_comp_def; wl_evaluate_def]);;

(* HOL4: Resume compile_correct[Tick] *)

let PL2WAUX_compile_correct_Tick = prove
 (PL2WAUX_case "loop_Tick",
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wl_state_clock (t:(A,C,FFI)wl_state) = loop_state_clock (s:(A,FFI)loop_state)`
    ASSUME_TAC THENL [ASM_MESON_TAC[loop_to_wordProof_state_rel_IMP]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_evaluate_def]) THEN
  ASM_REWRITE_TAC[loop_to_word_comp_def; wl_evaluate_def] THEN
  COND_CASES_TAC THEN GVS[] THEN
  FS[loop_to_wordProof_state_rel_def; wl_flush_state_def; loop_dec_clock_def;
     wl_dec_clock_def]);;

(* HOL4: Resume compile_correct[Continue] *)

let PL2WAUX_compile_correct_Continue = prove
 (PL2WAUX_case "loop_Continue",
  REPEAT STRIP_TAC THEN
  GVS[loop_evaluate_def; loop_to_word_comp_def; wl_evaluate_def] THEN
  FS[loop_to_wordProof_state_rel_def]);;

(* HOL4: Resume compile_correct[Break] *)

let PL2WAUX_compile_correct_Break = prove
 (PL2WAUX_case "loop_Break",
  REPEAT STRIP_TAC THEN
  GVS[loop_evaluate_def; loop_to_word_comp_def; wl_evaluate_def] THEN
  FS[loop_to_wordProof_state_rel_def]);;

(* HOL4: Resume compile_correct[Loop], with the cases Loop_bodyNONE,       *)
(* Loop_Exception, Loop_Break and Loop_Continue as the branches below      *)

let PL2WAUX_compile_correct_Loop = prove
 (PL2WAUX_case "loop_Loop",
  (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
     RULE_ASSUM_TAC(REWRITE_RULE[acc_vars_def]) THEN
     QBY "wl_state_clock t = loop_state_clock s" (FS[loop_to_wordProof_state_rel_def]) THEN
     QBY "wl_state_ffi t = loop_state_ffi s" (FS[loop_to_wordProof_state_rel_def]) THEN
     REWRITE_TAC[loop_to_word_comp_def] THEN
     PAIR_CASES_ON `loop_to_word_comp ctxt (body:(A)loop_prog) l` THEN SIMP[] THEN
     RENAME1 "loop_to_word_comp ctxt body l = (wbody,lb1,lb2)" THEN
     QPAT_X_ASSUM "loop_evaluate (loop_Loop _ _ _,_) = _" MP_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [loop_evaluate_def] THEN
     REWRITE_TAC[cut_res_def; cut_state_def] THEN
     COND_CASES_TAC THENL [ALL_TAC; SIMP[] THEN ASM_MESON_TAC[]] THEN
     SIMP[] THEN COND_CASES_TAC THENL
      [SIMP[] THEN STRIP_TAC THEN GVS[] THEN
       ONCE_REWRITE_TAC[wl_evaluate_def] THEN
       ASM_REWRITE_TAC[evaluate_tick_unfold] THEN SIMP[wl_flush_state_def];
       ALL_TAC]) THEN
  (SUBGOAL_THEN
      `cut_res (live_in:num_set) (NONE:((A)loop_result)option,s:(A,FFI)loop_state) =
       (NONE,loop_dec_clock (loop_state_locals_fupd
                               (K (sptree_inter (loop_state_locals s) live_in)) s))`
      ASSUME_TAC THENL
      [REWRITE_TAC[cut_res_def; cut_state_def] THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
       ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_conj(concl th) &&
                                            is_forall(lhand(concl th)))) THEN
     ASM_REWRITE_TAC[PAIR_EQ] THEN
     REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1] THEN
     DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC) THEN
  (SIMP[] THEN
     DRULE_ALL cut_env_mk_new_cutset THEN STRIP_TAC THEN
     DRULE cut_env_mk_new_cutset_IMP THEN DISCH_TAC THEN
     QBY "~(wl_state_clock t = 0)" (ASM_REWRITE_TAC[]) THEN
     ASM_SIMP_TAC[evaluate_tick_loop_tick_unfold] THEN
     GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV o BINDER_CONV o LAND_CONV o LAND_CONV o RAND_CONV)
       [wl_evaluate_def] THEN
     SIMP[wl_cut_state_def] THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
     PAIR_CASES_ON `loop_evaluate (body:(A)loop_prog,
                      loop_dec_clock (loop_state_locals_fupd
                        (K (sptree_inter (loop_state_locals s) (live_in:num_set))) (s:(A,FFI)loop_state)))` THEN
     RENAME1 "loop_evaluate _ = (resb,sb)" THEN SIMP[] THEN DISCH_TAC) THEN
  (QBY "~(resb = SOME loop_Error)" (DISCH_TAC THEN GVS[loop_exit_loop_def]) THEN
     RULE_ASSUM_TAC(fun th ->
       if can (find_term (fun t -> t = `resb:((A)loop_result)option,sb:(A,FFI)loop_state`))
              (concl th)
       then REWRITE_RULE[PAIR_EQ; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1] th
       else th)) THEN
  (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_neg(lhand(concl th)))) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(MP_TAC o SPEC `wl_state_locals_fupd (K (env1:((A)word_loc)spt))
                                (wl_state_clock_fupd (K (loop_state_clock (s:(A,FFI)loop_state) - 1))
                                   (t:(A,C,FFI)wl_state))`) THEN
     ANTS_TAC THENL [FS[loop_to_wordProof_state_rel_def; loop_dec_clock_def]; ALL_TAC] THEN
     DISCH_THEN(MP_TAC o SPEC `ctxt:num spt`) THEN
     ANTS_TAC THENL [SIMP[loop_dec_clock_def] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     DISCH_THEN(MP_TAC o SPEC `retv:(A)word_loc`) THEN
     SIMP[] THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN(MP_TAC o SPEC `l:num#num`) THEN ASM_REWRITE_TAC[FST] THEN STRIP_TAC) THEN
  (QCASES_ON "resb" THENL
      [ALL_TAC; RENAME1 "loop_evaluate _ = (SOME rb,sb)" THEN QCASES_ON "rb"] THEN
     GVS[loop_exit_loop_def; wl_cont_loop_def; wl_exit_loop_def]) THENL
   [(* the body returns NONE *)
    QBY "wl_state_clock t1 = loop_state_clock sb" (FS[loop_to_wordProof_state_rel_def]) THEN
      ASM_CASES_TAC `loop_state_clock (sb:(A,FFI)loop_state) = 0` THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT] THEN
        QPAT_X_ASSUM "loop_evaluate (loop_Loop _ _ _,sb) = _" MP_TAC THEN
        ONCE_REWRITE_TAC[loop_evaluate_def] THEN REWRITE_TAC[cut_res_def; cut_state_def] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN GVS[];
        FIRST_X_ASSUM(MP_TAC o SPEC `t1:(A,C,FFI)wl_state` o check (is_forall o concl)) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPEC `ctxt:num spt`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPEC `retv:(A)word_loc`) THEN ASM_REWRITE_TAC[acc_vars_def] THEN
        DISCH_THEN(MP_TAC o SPEC `l:num#num`) THEN
        ASM_REWRITE_TAC[loop_to_word_comp_def] THEN SIMP[] THEN
        ASM_SIMP_TAC[evaluate_tick_loop_tick_unfold] THEN
        REWRITE_TAC[wl_STOP_def; wl_dec_clock_def] THEN ASM_REWRITE_TAC[]];
    (* Exception *)
    ASM_CASES_TAC `res1 = SOME (wl_Error:(A)wl_result)` THENL
       [GVS[wl_cont_loop_def; wl_exit_loop_def];
        RES_TAC THEN GVS[wl_cont_loop_def; wl_exit_loop_def]];
    (* Break *)
    ASM_CASES_TAC `a' = 0` THENL [ALL_TAC; GVS[]] THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
      REWRITE_TAC[] THEN
      ASM_CASES_TAC `domain (live_out:num_set) SUBSET domain (loop_state_locals (sb:(A,FFI)loop_state))`
      THENL [ALL_TAC; GVS[]] THEN
      SUBGOAL_THEN
       `?env2. wl_cut_env (mk_new_cutset ctxt live_out,LN)
                 (wl_state_locals (t1:(A,C,FFI)wl_state)) = SOME env2 /\
               loop_to_wordProof_locals_rel ctxt
                 (sptree_inter (loop_state_locals (sb:(A,FFI)loop_state)) live_out) env2`
        STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC (GEN_ALL cut_env_mk_new_cutset) THEN EXISTS_TAC `retv:(A)word_loc` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP cut_env_mk_new_cutset_IMP) THEN
      QBY "wl_state_clock t1 = loop_state_clock sb" (FS[loop_to_wordProof_state_rel_def]) THEN
      ASM_REWRITE_TAC[] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `loop_state_clock (sb:(A,FFI)loop_state) = 0` THEN
      GVS[wl_flush_state_def] THEN
      FS[loop_dec_clock_def; loop_to_wordProof_state_rel_def];
    (* Continue *)
    (ASM_CASES_TAC `a' = 0` THENL [ALL_TAC; GVS[]] THEN
           FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
           REWRITE_TAC[wl_cont_loop_def] THEN
           FIRST_X_ASSUM(fun th ->
             if is_forall(concl th) &&
                can (find_term ((=) `loop_Loop live_in body live_out:(A)loop_prog`)) (concl th)
             then MP_TAC(SPECL [`res:((A)loop_result)option`; `s1:(A,FFI)loop_state`] th)
             else failwith "") THEN
           ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
        (QBY "wl_state_clock t1 = loop_state_clock sb" (FS[loop_to_wordProof_state_rel_def]) THEN
           ASM_CASES_TAC `loop_state_clock (sb:(A,FFI)loop_state) = 0` THENL
            [ASM_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT] THEN
             QPAT_X_ASSUM "loop_evaluate (loop_Loop _ _ _,sb) = _" MP_TAC THEN
             ONCE_REWRITE_TAC[loop_evaluate_def] THEN REWRITE_TAC[cut_res_def; cut_state_def] THEN
             COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN GVS[];
             FIRST_X_ASSUM(MP_TAC o SPEC `t1:(A,C,FFI)wl_state` o check (is_forall o concl)) THEN
             ASM_REWRITE_TAC[] THEN
             DISCH_THEN(MP_TAC o SPEC `ctxt:num spt`) THEN ASM_REWRITE_TAC[] THEN
             DISCH_THEN(MP_TAC o SPEC `retv:(A)word_loc`) THEN ASM_REWRITE_TAC[acc_vars_def] THEN
             DISCH_THEN(MP_TAC o SPEC `l:num#num`) THEN
             ASM_REWRITE_TAC[loop_to_word_comp_def] THEN SIMP[] THEN
             ASM_SIMP_TAC[evaluate_tick_loop_tick_unfold] THEN
             REWRITE_TAC[wl_STOP_def; wl_dec_clock_def] THEN ASM_REWRITE_TAC[]])]);;

(* HOL4: Resume compile_correct[Mark] *)

let PL2WAUX_compile_correct_Mark = prove
 (PL2WAUX_case "Mark",
  REPEAT GEN_TAC THEN
  REWRITE_TAC[loop_evaluate_def; loop_to_word_comp_def; acc_vars_def]);;

(* HOL4: Resume compile_correct[Return] *)

let PL2WAUX_compile_correct_Return = prove
 (PL2WAUX_case "loop_Return",
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_evaluate_def]) THEN
  QCASES_ON "get_vars ns s" THEN GVS[] THEN
  DRULE_ALL loop_to_wordProof_locals_rel_get_vars THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[loop_to_word_comp_def; wl_evaluate_def; wl_get_var_def] THEN
  QCASES_ON "retv" THEN FS[isWord_def] THEN
  FS[wl_flush_state_def; loop_to_wordProof_state_rel_def; call_env_def]);;

(* HOL4: Resume compile_correct[Raise] *)

let PL2WAUX_compile_correct_Raise = prove
 (PL2WAUX_case "loop_Raise",
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_evaluate_def]) THEN
  QCASES_ON "lookup n (loop_state_locals s)" THEN GVS[] THEN
  IMP_RES_TAC loop_to_wordProof_locals_rel_get_var THEN
  ASM_REWRITE_TAC[loop_to_word_comp_def; wl_evaluate_def] THEN
  QCASES_ON "wl_jump_exc t" THENL
   [FS[RECORD_SELFID_ss; loop_to_wordProof_state_rel_def; call_env_def];
    ALL_TAC] THEN
  RENAME1 "wl_jump_exc t = SOME x" THEN PAIR_CASES_ON `x:(A,C,FFI)wl_state#num#num` THEN
  SIMP[] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[wl_jump_exc_def] THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  DISCH_TAC THEN GVS(all_case_eqs()) THEN
  FS[loop_to_wordProof_state_rel_def; call_env_def]);;

(* HOL4: Resume compile_correct[Seq] *)

let PL2WAUX_compile_correct_Seq = prove
 (PL2WAUX_case "loop_Seq",
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_evaluate_def]) THEN
  PAIRARG_TAC THEN REWRITE_TAC[loop_to_word_comp_def] THEN
  REPEAT(PAIRARG_TAC THEN ASM_REWRITE_TAC[]) THEN
  QPAT_X_ASSUM "domain (acc_vars _ LN) SUBSET domain ctxt"
    (STRIP_ASSUME_TAC o REWRITE_RULE[UNION_SUBSET] o ONCE_REWRITE_RULE[acc_vars_acc] o
     REWRITE_RULE[acc_vars_def]) THEN
  REWRITE_TAC[FST; wl_evaluate_def] THEN
  FIRST_X_ASSUM(QSPECL_THEN ["res'"; "s1'"; "t"; "ctxt"; "retv"; "l"] MP_TAC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; PAIR_EQ]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  QPAT_X_ASSUM "wl_evaluate (wp,t) = _" (fun th -> REWRITE_TAC[th]) THEN SIMP[] THEN
  QCASES_ON "res'" THEN FS[] THENL
   [FIRST_X_ASSUM(QSPECL_THEN ["res"; "s1"; "t1"; "ctxt"; "retv"; "l'"] MP_TAC) THEN
    ASM_REWRITE_TAC[FST] THEN DISCH_THEN ACCEPT_TAC;
    GVS[] THEN QCASES_ON "a" THEN FS[] THEN COND_CASES_TAC THEN GVS[]]);;

(* HOL4: Resume compile_correct[Assign] *)

let PL2WAUX_compile_correct_Assign = prove
 (PL2WAUX_case "loop_Assign",
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_evaluate_def]) THEN
  QCASES_ON "loop_eval s exp" THEN GVS[] THEN
  IMP_RES_TAC loop_to_wordProof_comp_exp_preserves_eval THEN
  ASM_REWRITE_TAC[loop_to_word_comp_def; wl_evaluate_def] THEN SIMP[] THEN
  FS[loop_set_var_def; wl_set_var_def] THEN
  QPAT_X_ASSUM "domain (acc_vars _ LN) SUBSET _"
    (STRIP_ASSUME_TAC o REWRITE_RULE[acc_vars_def; domain_insert; domain_def; INSERT_SUBSET]) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[loop_to_wordProof_state_rel_intro]; ALL_TAC] THEN
  CONJ_TAC THENL [FS[loop_to_wordProof_state_rel_def]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[find_var_neq_0];
    MATCH_MP_TAC locals_rel_insert THEN ASM_REWRITE_TAC[]]);;

(* HOL4: Resume compile_correct[Primitive] *)

let PL2WAUX_compile_correct_Primitive = prove
 (PL2WAUX_case "loop_Primitive",
  (REPEAT STRIP_TAC THEN
     RULE_ASSUM_TAC(REWRITE_RULE[loop_evaluate_def]) THEN
     QCASES_ON "get_vars rhss s" THEN GVS[] THEN
     QCASES_ON "pop" THEN RULE_ASSUM_TAC(REWRITE_RULE[loop_primop_def]) THEN
     GVS_ASM(all_case_eqs())) THEN
  (DRULE_ALL loop_to_wordProof_locals_rel_get_vars THEN STRIP_TAC THEN
     GVS_ASM[LENGTH_EQ_NUM_compute; ALL; isWord_exists]) THEN
  (FIRST_X_ASSUM(MP_TAC o SYM o check (fun th -> is_eq(concl th) && is_numeral(lhs(concl th)))) THEN
     DISCH_TAC THEN GVS_ASM[LENGTH_EQ_NUM_compute] THEN
     RENAME_TAC ["loop_Primitive [res_var; co_var] panLang_AddCarry [li; ri; ci]";
                 "get_vars _ s = SOME [wl_Word lw; wl_Word rw; wl_Word cw]"]) THEN
  (QPAT_X_ASSUM "domain (acc_vars _ LN) SUBSET _"
       (MP_TAC o REWRITE_RULE[acc_vars_def; list_insert_def; domain_insert; domain_def;
                              INSERT_SUBSET; EMPTY_SUBSET]) THEN STRIP_TAC THEN
     RULE_ASSUM_TAC(REWRITE_RULE[wl_get_vars_def]) THEN GVS_ASM(all_case_eqs()) THEN
     SUBGOAL_THEN `~(loop_to_word_find_var ctxt res_var = 0) /\
                   ~(loop_to_word_find_var ctxt co_var = 0)` STRIP_ASSUME_TAC THENL
      [ASM_MESON_TAC[find_var_neq_0]; ALL_TAC] THEN
     SUBGOAL_THEN `!n. ~(loop_to_word_find_var ctxt n = 1) /\
                       ~(loop_to_word_find_var ctxt n = 3)` ASSUME_TAC THENL
      [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC find_var_neq_odd THEN
       RULE_ASSUM_TAC(REWRITE_RULE[loop_to_wordProof_locals_rel_def]) THEN
       ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
       ALL_TAC] THEN
     ASM_REWRITE_TAC[loop_to_word_comp_def; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[LET_DEF; LET_END_DEF; EL; HD; TL; FST; ONE; TWO] THEN
     CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[GSYM ONE; GSYM TWO]) THEN
  (SIMP[] THEN RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def; theWord_def]) THEN
     FIRST_ASSUM(fun th -> if is_forall(concl th) then
                             ASSUME_TAC(ONCE_REWRITE_RULE[EQ_SYM_EQ] th) else NO_TAC) THEN
     ASM_REWRITE_TAC[wl_evaluate_def; wl_word_exp_def; wl_get_var_def; wl_set_var_def;
                     wl_inst_def; wl_get_vars_def] THEN
     SIMP[lookup_insert] THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN SIMP[]) THEN
  (REWRITE_TAC[set_vars_def; alist_insert_def] THEN SIMP[] THEN
     CONJ_TAC THENL [ASM_MESON_TAC[loop_to_wordProof_state_rel_intro]; ALL_TAC] THEN
     CONJ_TAC THENL [FS[loop_to_wordProof_state_rel_def]; ALL_TAC] THEN
     REPEAT(MATCH_MP_TAC locals_rel_insert THEN ASM_REWRITE_TAC[]) THEN
     REPEAT(MATCH_MP_TAC locals_rel_insert_unmapped THEN ASM_REWRITE_TAC[])));;

(* HOL4: Resume compile_correct[LocValue] *)

let PL2WAUX_compile_correct_LocValue = prove
 (PL2WAUX_case "LocValue",
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_evaluate_def]) THEN
  QPAT_X_ASSUM "domain (acc_vars _ LN) SUBSET _"
    (STRIP_ASSUME_TAC o REWRITE_RULE[acc_vars_def; domain_insert; domain_def; INSERT_SUBSET]) THEN
  GVS_ASM[COND_CASE_EQ] THEN
  QBY "l1 IN domain (wl_state_code t)"
   (FIRST_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                 CONJUNCT2 o CONJUNCT2 o MATCH_MP loop_to_wordProof_state_rel_intro) THEN
    REWRITE_TAC[loop_to_wordProof_code_rel_def] THEN
    UNDISCH_TAC `l1 IN domain (loop_state_code (s:(A,FFI)loop_state))` THEN
    REWRITE_TAC[domain_lookup] THEN MESON_TAC[PAIR]) THEN
  ASM_REWRITE_TAC[loop_to_word_comp_def; wl_evaluate_def] THEN SIMP[] THEN
  FS[loop_set_var_def; wl_set_var_def] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[loop_to_wordProof_state_rel_intro]; ALL_TAC] THEN
  CONJ_TAC THENL [FS[loop_to_wordProof_state_rel_def]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[find_var_neq_0];
    MATCH_MP_TAC locals_rel_insert THEN ASM_REWRITE_TAC[]]);;

(* HOL4: Resume compile_correct[Store] *)

let PL2WAUX_compile_correct_Store = prove
 (PL2WAUX_case "loop_Store",
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_evaluate_def]) THEN
  GVS_ASM[option_case_eq; case_eq "word_loc"; pair_case_eq] THEN
  IMP_RES_TAC loop_to_wordProof_comp_exp_preserves_eval THEN
  IMP_RES_TAC loop_to_wordProof_locals_rel_get_var THEN
  IMP_RES_TAC loop_to_wordProof_state_rel_intro THEN
  ASM_REWRITE_TAC[loop_to_word_comp_def; wl_evaluate_def] THEN SIMP[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_mem_store_def]) THEN
  GVS_ASM[COND_CASE_EQ] THEN ASM_REWRITE_TAC[wl_mem_store_def] THEN SIMP[] THEN
  FS[loop_to_wordProof_state_rel_def]);;

(* HOL4: Resume compile_correct[Store32] *)

let PL2WAUX_compile_correct_Store32 = prove
 (PL2WAUX_case "loop_Store32",
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_evaluate_def]) THEN
  GVS_ASM[option_case_eq; case_eq "word_loc"; pair_case_eq] THEN
  IMP_RES_TAC loop_to_wordProof_locals_rel_get_var THEN
  IMP_RES_TAC loop_to_wordProof_state_rel_intro THEN
  ASM_REWRITE_TAC[loop_to_word_comp_def; wl_evaluate_def; wl_inst_def; wl_word_exp_def;
                  MAP; the_words_def] THEN
  SIMP[word_op_def; ITLIST; WORD_ADD_0] THEN
  FS[loop_to_wordProof_state_rel_def]);;

(* HOL4: Resume compile_correct[StoreByte] *)

let PL2WAUX_compile_correct_StoreByte = prove
 (PL2WAUX_case "loop_StoreByte",
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_evaluate_def]) THEN
  GVS_ASM[option_case_eq; case_eq "word_loc"; pair_case_eq] THEN
  IMP_RES_TAC loop_to_wordProof_locals_rel_get_var THEN
  IMP_RES_TAC loop_to_wordProof_state_rel_intro THEN
  ASM_REWRITE_TAC[loop_to_word_comp_def; wl_evaluate_def; wl_inst_def; wl_word_exp_def;
                  MAP; the_words_def] THEN
  SIMP[word_op_def; ITLIST; WORD_ADD_0] THEN
  FS[loop_to_wordProof_state_rel_def]);;

(* HOL4: Resume compile_correct[Load32] *)

let PL2WAUX_compile_correct_Load32 = prove
 (PL2WAUX_case "loop_Load32",
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_evaluate_def]) THEN
  QPAT_X_ASSUM "domain (acc_vars _ LN) SUBSET _"
    (STRIP_ASSUME_TAC o REWRITE_RULE[acc_vars_def; domain_insert; domain_def; INSERT_SUBSET]) THEN
  GVS_ASM[option_case_eq; case_eq "word_loc"; pair_case_eq] THEN
  IMP_RES_TAC loop_to_wordProof_locals_rel_get_var THEN
  IMP_RES_TAC loop_to_wordProof_state_rel_intro THEN
  ASM_REWRITE_TAC[loop_to_word_comp_def; wl_evaluate_def; wl_inst_def; wl_word_exp_def;
                  MAP; the_words_def] THEN
  SIMP[word_op_def; ITLIST; WORD_ADD_0] THEN
  FS[loop_set_var_def; wl_set_var_def] THEN
  CONJ_TAC THENL [FS[loop_to_wordProof_state_rel_def]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[find_var_neq_0];
    MATCH_MP_TAC locals_rel_insert THEN ASM_REWRITE_TAC[]]);;

(* HOL4: Resume compile_correct[LoadByte] *)

let PL2WAUX_compile_correct_LoadByte = prove
 (PL2WAUX_case "loop_LoadByte",
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_evaluate_def]) THEN
  QPAT_X_ASSUM "domain (acc_vars _ LN) SUBSET _"
    (STRIP_ASSUME_TAC o REWRITE_RULE[acc_vars_def; domain_insert; domain_def; INSERT_SUBSET]) THEN
  GVS_ASM[option_case_eq; case_eq "word_loc"; pair_case_eq] THEN
  IMP_RES_TAC loop_to_wordProof_locals_rel_get_var THEN
  IMP_RES_TAC loop_to_wordProof_state_rel_intro THEN
  ASM_REWRITE_TAC[loop_to_word_comp_def; wl_evaluate_def; wl_inst_def; wl_word_exp_def;
                  MAP; the_words_def] THEN
  SIMP[word_op_def; ITLIST; WORD_ADD_0] THEN
  FS[loop_set_var_def; wl_set_var_def] THEN
  CONJ_TAC THENL [FS[loop_to_wordProof_state_rel_def]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[find_var_neq_0];
    MATCH_MP_TAC locals_rel_insert THEN ASM_REWRITE_TAC[]]);;

(* HOL4: Resume compile_correct[SetGlobal] *)

let PL2WAUX_compile_correct_SetGlobal = prove
 (PL2WAUX_case "loop_SetGlobal",
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_evaluate_def]) THEN
  GVS_ASM[option_case_eq] THEN
  IMP_RES_TAC loop_to_wordProof_comp_exp_preserves_eval THEN
  ASM_REWRITE_TAC[loop_to_word_comp_def; wl_evaluate_def] THEN SIMP[] THEN
  REWRITE_TAC[loop_set_globals_def; wl_set_store_def] THEN SIMP[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[loop_to_wordProof_state_rel_intro]; ALL_TAC] THEN
  UNDISCH_TAC `loop_to_wordProof_state_rel (s:(A,FFI)loop_state) (t:(A,C,FFI)wl_state)` THEN
  REWRITE_TAC[loop_to_wordProof_state_rel_def; loop_to_wordProof_globals_rel_def;
              ALOOKUP_EQ_FLOOKUP] THEN
  STRIP_TAC THEN EXISTS_TAC `len:A word` THEN
  SIMP[FLOOKUP_UPDATE] THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

(* HOL4: acc_vars_acc' [local] *)

let acc_vars_acc' =
  GEN `p:(A)loop_prog`
   (SPECL [`p:(A)loop_prog`; `acc_vars (q:(A)loop_prog) LN`] acc_vars_acc);;

(* the immediate operand of an If is compiled correctly *)

let PL2WAUX_get_var_imm = prove
 (`!ri v. loop_to_wordProof_locals_rel ctxt (loop_state_locals (s:(A,FFI)loop_state))
            (wl_state_locals (t:(A,C,FFI)wl_state)) /\
          get_var_imm ri s = SOME v
          ==> wl_get_var_imm (find_reg_imm ctxt ri) t = SOME v`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN
  REWRITE_TAC[get_var_imm_def; wl_get_var_imm_def; find_reg_imm_def] THEN
  MESON_TAC[loop_to_wordProof_locals_rel_get_var]);;

(* cutting the source locals keeps the relation *)

let PL2WAUX_locals_rel_inter = prove
 (`loop_to_wordProof_locals_rel ctxt (l1:(A)spt) l2 ==>
   loop_to_wordProof_locals_rel ctxt (sptree_inter l1 (x:(B)spt)) l2`,
  REWRITE_TAC[loop_to_wordProof_locals_rel_def; lookup_inter_alt] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]);;

(* HOL4: Resume compile_correct[If] *)

let PL2WAUX_compile_correct_If = prove
 (PL2WAUX_case "loop_If",
  (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
     RULE_ASSUM_TAC(REWRITE_RULE[acc_vars_def; acc_vars_acc'; UNION_SUBSET]) THEN
     QPAT_X_ASSUM "loop_evaluate (loop_If _ _ _ _ _ _,_) = _" MP_TAC THEN
     ONCE_REWRITE_TAC[loop_evaluate_def] THEN DISCH_TAC THEN
     GVS_ASM(all_case_eqs())) THEN
  (RENAME1 "lookup r1 (loop_state_locals s) = SOME (wl_Word x)" THEN
     RENAME1 "get_var_imm ri s = SOME (wl_Word y)" THEN
     REWRITE_TAC[loop_to_word_comp_def] THEN
     PAIR_CASES_ON `loop_to_word_comp ctxt (c1:(A)loop_prog) l` THEN SIMP[] THEN
     RENAME1 "loop_to_word_comp ctxt c1 l = (wp,lp1,lp2)" THEN
     PAIR_CASES_ON `loop_to_word_comp ctxt (c2:(A)loop_prog) (lp1,lp2)` THEN SIMP[] THEN
     RENAME1 "loop_to_word_comp ctxt c2 (lp1,lp2) = (wq,lq1,lq2)" THEN
     IMP_RES_TAC loop_to_wordProof_locals_rel_get_var THEN
     IMP_RES_TAC PL2WAUX_get_var_imm THEN
     REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
     ASM_CASES_TAC `asm_word_cmp cmp (x:A word) y` THEN ASM_REWRITE_TAC[]) THENL
   [(* the first branch *)
    (POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
           PAIR_CASES_ON `loop_evaluate (c1:(A)loop_prog, s:(A,FFI)loop_state)` THEN
           RENAME1 "loop_evaluate (c1,s) = (resb,sb)" THEN
           QBY "~(resb = SOME loop_Error)" (DISCH_TAC THEN GVS[cut_res_def]) THEN
           FIRST_X_ASSUM(QSPECL_THEN ["resb"; "sb"; "t"; "ctxt"; "retv"; "l"] MP_TAC) THEN
           ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
           QCASES_ON "resb" THENL [ALL_TAC; RENAME1 "cut_res live_out (SOME rb,sb) = _" THEN QCASES_ON "rb"] THEN
           GVS[cut_res_def]) THENL
         [(* NONE *)
          QBY "wl_state_clock t1 = loop_state_clock sb" (FS[loop_to_wordProof_state_rel_def]) THEN
            FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=)
              `cut_state (live_out:num_set) (sb:(A,FFI)loop_state)`)) (concl th))) THEN
            REWRITE_TAC[cut_state_def] THEN
            COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
            ASM_CASES_TAC `loop_state_clock (sb:(A,FFI)loop_state) = 0` THEN
            ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN GVS[wl_flush_state_def] THEN
            ASM_SIMP_TAC[PL2WAUX_locals_rel_inter; wl_dec_clock_def] THEN
            FS[loop_dec_clock_def; wl_dec_clock_def; loop_to_wordProof_state_rel_def] THEN
            MATCH_MP_TAC PL2WAUX_locals_rel_inter THEN ASM_REWRITE_TAC[];
          (* Exception *)
          ASM_CASES_TAC `res1 = SOME (wl_Error:(A)wl_result)` THENL
             [GVS[]; RES_TAC THEN GVS[]]];
    (* the second branch *)
    (POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
           PAIR_CASES_ON `loop_evaluate (c2:(A)loop_prog, s:(A,FFI)loop_state)` THEN
           RENAME1 "loop_evaluate (c2,s) = (resb,sb)" THEN
           QBY "~(resb = SOME loop_Error)" (DISCH_TAC THEN GVS[cut_res_def]) THEN
           FIRST_X_ASSUM(QSPECL_THEN ["resb"; "sb"; "t"; "ctxt"; "retv"; "(lp1,lp2)"] MP_TAC) THEN
           ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
           QCASES_ON "resb" THENL [ALL_TAC; RENAME1 "cut_res live_out (SOME rb,sb) = _" THEN QCASES_ON "rb"] THEN
           GVS[cut_res_def]) THENL
         [(* NONE *)
          QBY "wl_state_clock t1 = loop_state_clock sb" (FS[loop_to_wordProof_state_rel_def]) THEN
            FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=)
              `cut_state (live_out:num_set) (sb:(A,FFI)loop_state)`)) (concl th))) THEN
            REWRITE_TAC[cut_state_def] THEN
            COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
            ASM_CASES_TAC `loop_state_clock (sb:(A,FFI)loop_state) = 0` THEN
            ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN GVS[wl_flush_state_def] THEN
            ASM_SIMP_TAC[PL2WAUX_locals_rel_inter; wl_dec_clock_def] THEN
            FS[loop_dec_clock_def; wl_dec_clock_def; loop_to_wordProof_state_rel_def] THEN
            MATCH_MP_TAC PL2WAUX_locals_rel_inter THEN ASM_REWRITE_TAC[];
          (* Exception *)
          ASM_CASES_TAC `res1 = SOME (wl_Error:(A)wl_result)` THENL
             [GVS[]; RES_TAC THEN GVS[]]]]);;

(* a branch where loopLang's result is an error, which is excluded *)

let PL2WAUX_ERROR_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  UNDISCH_TAC `~(res = SOME (loop_Error:(A)loop_result))` THEN ASM_REWRITE_TAC[];;

(* the compiled code of a called function: HOL4 proves this inline, once  *)
(* for tail calls and once for calls that return                           *)

let PL2WAUX_comp_func_ctxt = prove
 (`!params (args:((A)word_loc)list) v (body:(A)loop_prog).
     ALL_DISTINCT params /\ LENGTH params = LENGTH args
     ==> loop_to_wordProof_locals_rel
           (make_ctxt 2 (APPEND params (fromNumSet (difference (acc_vars body LN)
                                                     (toNumSet params)))) LN)
           (fromAList (ZIP params args)) (fromList2 (CONS v args)) /\
         domain (acc_vars body LN) SUBSET
         domain (make_ctxt 2 (APPEND params (fromNumSet (difference (acc_vars body LN)
                                                          (toNumSet params)))) LN)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC locals_rel_make_ctxt THEN
    ASM_REWRITE_TAC[set_fromNumSet; IN_DISJOINT; domain_difference; domain_toNumSet] THEN
    SET_TAC[];
    REWRITE_TAC[domain_make_ctxt; set_fromNumSet; domain_difference; domain_toNumSet;
                SET_OF_LIST_APPEND; domain_def] THEN SET_TAC[]]);;

let PL2WAUX_find_code = prove
 (`!dest argvals new_env (new_code:(A)loop_prog) (v:(A)word_loc) (t:(A,C,FFI)wl_state) s_code.
     loop_to_wordProof_code_rel s_code (wl_state_code t) /\
     find_code dest argvals s_code = SOME (new_env,new_code)
     ==> ?args1 prog1 ss1 ctxt1 l1.
           wl_find_code dest (CONS v argvals) (wl_state_code t) (wl_state_stack_size t) =
             SOME (args1,prog1,ss1) /\
           FST (loop_to_word_comp ctxt1 new_code l1) = prog1 /\
           lookup 0 (fromList2 args1) = SOME v /\
           loop_to_wordProof_locals_rel ctxt1 new_env (fromList2 args1) /\
           domain (acc_vars new_code LN) SUBSET domain ctxt1`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `dest:num option` (cases "option")) THEN
  REWRITE_TAC[find_code_def; wl_find_code_def; loop_to_wordProof_code_rel_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN GVS_ASM(all_case_eqs()) THEN
  RES_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THENL
   [(* NONE: the label is the last argument *)
    ASM_REWRITE_TAC[LAST; BUTLAST] THEN SIMP[] THEN
    REWRITE_TAC[ARITH_RULE `SUC (n + 1) = (n + 1) + 1`] THEN
    SIMP[loop_to_word_comp_func_def; LET_DEF; LET_END_DEF] THEN
    MAP_EVERY EXISTS_TAC
     [`make_ctxt 2 (APPEND x (fromNumSet (difference (acc_vars (new_code:(A)loop_prog) LN)
                                            (toNumSet x)))) LN`; `(a0:num,2)`] THEN
    REWRITE_TAC[lookup_fromList2; EVEN; ARITH_RULE `0 DIV 2 = 0`; lookup_fromList;
                LENGTH; LT_0; EL; HD] THEN
    MATCH_MP_TAC PL2WAUX_comp_func_ctxt THEN ASM_SIMP_TAC[LENGTH_FRONT] THEN ASM_ARITH_TAC;
    (* SOME p *)
    REWRITE_TAC[loop_to_word_comp_func_def; LET_DEF; LET_END_DEF; ADD1] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    MAP_EVERY EXISTS_TAC
     [`make_ctxt 2 (APPEND x (fromNumSet (difference (acc_vars (new_code:(A)loop_prog) LN)
                                            (toNumSet x)))) LN`; `(a:num,2)`] THEN
    REWRITE_TAC[lookup_fromList2; EVEN; ARITH_RULE `0 DIV 2 = 0`; lookup_fromList;
                LENGTH; LT_0; EL; HD] THEN
    MATCH_MP_TAC PL2WAUX_comp_func_ctxt THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* the frame pushed for a call whose second cutset is empty *)

let PL2WAUX_push_env_LN = prove
 (CASE_TERM
  `!(env1:((A)word_loc)spt) (b:(num#(A)wl_prog#num#num)option) (s:(A,C,FFI)wl_state).
     wl_state_stack (wl_push_env (env1,LN) b s) =
       CONS (StackFrame (wl_state_locals_size s) (toAList env1) []
               (match b with NONE -> NONE
                           | SOME (w,h,l1,l2) -> SOME (wl_state_handler s,l1,l2)))
            (wl_state_stack s) /\
     wl_state_handler (wl_push_env (env1,LN) b s) =
       (match b with NONE -> wl_state_handler s
                   | SOME _ -> LENGTH (wl_state_stack s))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `b:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
  TRY(PAIR_CASES_ON `a:num#(A)wl_prog#num#num`) THEN
  REWRITE_TAC[wl_push_env_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  PAIR_CASES_ON `env_to_list (LN:((A)word_loc)spt) (wl_state_permute (s:(A,C,FFI)wl_state))` THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP env_to_list_LN_IMP) THEN SIMP[]);;

(* the return values never overwrite variable 0 *)

let PL2WAUX_lookup_0_alist_insert = prove
 (`!ns (vs:A list) t.
     (!n. MEM n ns ==> ~(loop_to_word_find_var ctxt n = 0)) /\ LENGTH ns = LENGTH vs
     ==> lookup 0 (alist_insert (MAP (loop_to_word_find_var ctxt) ns) vs t) = lookup 0 t`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `vs:A list` list_CASES) THEN
  REWRITE_TAC[MAP; alist_insert_def; LENGTH; NOT_SUC; SUC_INJ; MEM; NOT_CONS_NIL] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[lookup_insert] THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]]);;

(* an exception handler found below a pushed frame is found with it too *)

let PL2WAUX_jump_exc_push = prove
 (`!(s:(A,C,FFI)wl_state) stk h fr x.
     wl_jump_exc (wl_state_stack_fupd (K stk) (wl_state_handler_fupd (K h) s)) = SOME x
     ==> wl_jump_exc (wl_state_stack_fupd (K (CONS fr stk))
                        (wl_state_handler_fupd (K h) s)) = SOME x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_jump_exc_def] THEN SIMP[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `LASTN (h + 1) (CONS (fr:(A)stack_frame) stk) = LASTN (h + 1) stk`
    SUBST1_TAC THENL
   [MATCH_MP_TAC LASTN_ADD_CONS THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* PAIR_CASES_ON the first loop_evaluate (p,_) of the goal or assumptions *)

let PL2WAUX_EVAL_CASES_TAC (p:term) : tactic = fun (asl,w as g) ->
  let is_ev t =
    try let f,args = strip_comb t in
        fst(dest_const f) = "loop_evaluate" && fst(dest_pair(hd args)) = p
    with Failure _ -> false in
  let tm = find_term is_ev (list_mk_conj(w :: map (concl o snd) asl)) in
  PAIR_CASES_ON tm g;;

(* HOL4: Resume compile_correct[Call], with the cases Call_TailCall,         *)
(* Call_NOhandler and Call_SOMEhandler as the branches below              *)

let PL2WAUX_compile_correct_Call = prove
 (PL2WAUX_case "loop_Call",
  (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
     QPAT_X_ASSUM "loop_evaluate (loop_Call _ _ _ _,_) = _" MP_TAC THEN
     ONCE_REWRITE_TAC[loop_evaluate_def] THEN
     QCASES_ON "get_vars argvars s" THEN SIMP[] THEN TRY(PL2WAUX_ERROR_TAC THEN NO_TAC) THEN
     RENAME1 "get_vars argvars s = SOME argvals" THEN
     QCASES_ON "find_code dest argvals (loop_state_code s)" THEN SIMP[] THEN
     TRY(PL2WAUX_ERROR_TAC THEN NO_TAC) THEN
     RENAME1 "find_code dest argvals (loop_state_code s) = SOME fc" THEN
     PAIR_CASES_ON `fc:((A)word_loc)spt#(A)loop_prog` THEN
     RENAME1 "find_code dest argvals (loop_state_code s) = SOME (new_env,new_code)" THEN
     SIMP[] THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (is_conj o concl)) THEN ASM_REWRITE_TAC[] THEN
     SIMP[] THEN STRIP_TAC) THEN
  (DRULE_ALL loop_to_wordProof_locals_rel_get_vars THEN STRIP_TAC THEN
     SUBGOAL_THEN `~bad_dest_args (dest:num option) (MAP (loop_to_word_find_var ctxt) argvars)`
       ASSUME_TAC THENL
      [REWRITE_TAC[bad_dest_args_def; MAP_EQ_NIL] THEN STRIP_TAC THEN
       UNDISCH_TAC `find_code dest argvals (loop_state_code (s:(A,FFI)loop_state)) =
                    SOME (new_env,new_code:(A)loop_prog)` THEN
       ASM_REWRITE_TAC[find_code_def] THEN
       SUBGOAL_THEN `argvals:((A)word_loc)list = []` SUBST1_TAC THENL
        [ASM_MESON_TAC[LENGTH_EQ_NIL]; REWRITE_TAC[option_DISTINCT]];
       ALL_TAC] THEN
     REWRITE_TAC[loop_to_word_comp_def; LET_DEF; LET_END_DEF] THEN
     CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
     QCASES_ON "ret" THEN SIMP[]) THENL
   [(* tail call *)
    (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
          rand(concl th) = `res:((A)loop_result)option,s1:(A,FFI)loop_state`)) THEN
       SIMP[] THEN
       ASM_CASES_TAC `handler:(num#(A)loop_prog#(A)loop_prog#num_set)option = NONE` THEN
       ASM_REWRITE_TAC[] THEN TRY(PL2WAUX_ERROR_TAC THEN NO_TAC) THEN
       MP_TAC(ISPECL [`dest:num option`; `argvals:((A)word_loc)list`;
                      `new_env:((A)word_loc)spt`; `new_code:(A)loop_prog`; `retv:(A)word_loc`;
                      `t:(A,C,FFI)wl_state`; `loop_state_code (s:(A,FFI)loop_state)`]
                     PL2WAUX_find_code) THEN
       ANTS_TAC THENL [ASM_MESON_TAC[loop_to_wordProof_state_rel_intro]; ALL_TAC] THEN
       STRIP_TAC THEN
       ASM_REWRITE_TAC[wl_evaluate_def; wl_get_vars_def; wl_get_var_def] THEN SIMP[] THEN
       ASM_REWRITE_TAC[] THEN SIMP[add_ret_loc_def; bad_dest_args_def] THEN ASM_REWRITE_TAC[] THEN
       SIMP[]) THEN
    (QBY "wl_state_clock t = loop_state_clock s" (FS[loop_to_wordProof_state_rel_def]) THEN
       ASM_REWRITE_TAC[] THEN
       ASM_CASES_TAC `loop_state_clock (s:(A,FFI)loop_state) = 0` THEN ASM_REWRITE_TAC[] THENL
        [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN GVS[wl_flush_state_def] THEN
         FS[loop_to_wordProof_state_rel_def];
         ALL_TAC] THEN
       PAIR_CASES_ON `loop_evaluate (new_code:(A)loop_prog,
                        loop_state_locals_fupd (K (new_env:((A)word_loc)spt))
                          (loop_dec_clock (s:(A,FFI)loop_state)))` THEN
       RENAME1 "loop_evaluate _ = (rb,sb)" THEN SIMP[] THEN DISCH_TAC THEN
       SUBGOAL_THEN `~(rb = SOME (loop_Error:(A)loop_result))` ASSUME_TAC THENL
        [DISCH_TAC THEN UNDISCH_TAC `~(res = SOME (loop_Error:(A)loop_result))` THEN GVS[];
         ALL_TAC] THEN
       FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
         can (find_term ((=) `loop_dec_clock (s:(A,FFI)loop_state)`)) (concl th))) THEN
       ASM_REWRITE_TAC[] THEN
       DISCH_THEN(MP_TAC o SPECL [`rb:((A)loop_result)option`; `sb:(A,FFI)loop_state`;
         `wl_call_env args1 ss1 (wl_dec_clock (t:(A,C,FFI)wl_state))`; `ctxt1:num spt`;
         `retv:(A)word_loc`; `l1:num#num`]) THEN
       ASM_REWRITE_TAC[] THEN
       ANTS_TAC THENL
        [REWRITE_TAC[wl_call_env_def; wl_dec_clock_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
         FS[loop_to_wordProof_state_rel_def; loop_dec_clock_def];
         ALL_TAC] THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[]) THEN
    (QCASES_ON "rb" THENL [ALL_TAC; RENAME1 "loop_evaluate _ = (SOME rr,sb)" THEN QCASES_ON "rr"] THEN
       GVS[wl_call_env_def; wl_dec_clock_def] THEN
       TRY(PL2WAUX_ERROR_TAC THEN NO_TAC)) THEN
    (ASM_CASES_TAC `res1 = SOME (wl_Error:(A)wl_result)` THENL
        [GVS[]; RES_TAC THEN GVS[]]);
    (* a call that returns *)
    (RENAME1 "loop_Call (SOME rt) dest argvars handler" THEN
       PAIR_CASES_ON `rt:num list#num_set` THEN
       RENAME1 "loop_Call (SOME (ns,live)) dest argvars handler" THEN
       PAIR_CASES_ON `l:num#num` THEN
       FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
          rand(concl th) = `res:((A)loop_result)option,s1:(A,FFI)loop_state`)) THEN
       SIMP[] THEN
       ASM_CASES_TAC `ALL_DISTINCT (ns:num list)` THEN ASM_REWRITE_TAC[] THEN
       TRY(PL2WAUX_ERROR_TAC THEN NO_TAC) THEN
       REWRITE_TAC[cut_res_def; cut_state_def] THEN SIMP[] THEN
       ASM_CASES_TAC `domain (live:num_set) SUBSET domain (loop_state_locals (s:(A,FFI)loop_state))` THEN
       ASM_REWRITE_TAC[] THEN SIMP[] THEN TRY(PL2WAUX_ERROR_TAC THEN NO_TAC)) THEN
    (QBY "wl_state_clock t = loop_state_clock s" (FS[loop_to_wordProof_state_rel_def]) THEN
       DRULE_ALL cut_env_mk_new_cutset THEN STRIP_TAC THEN
       FIRST_ASSUM(ASSUME_TAC o MATCH_MP cut_env_LN_IMP) THEN
       FIRST_ASSUM(ASSUME_TAC o MATCH_MP cut_env_mk_new_cutset_IMP) THEN
       MP_TAC(ISPECL [`dest:num option`; `argvals:((A)word_loc)list`;
                      `new_env:((A)word_loc)spt`; `new_code:(A)loop_prog`; `wl_Loc l0 l1:(A)word_loc`;
                      `t:(A,C,FFI)wl_state`; `loop_state_code (s:(A,FFI)loop_state)`]
                     PL2WAUX_find_code) THEN
       ANTS_TAC THENL [ASM_MESON_TAC[loop_to_wordProof_state_rel_intro]; ALL_TAC] THEN
       STRIP_TAC THEN SIMP[] THEN
       QCASES_ON "handler" THEN SIMP[]) THENL
     [(* no exception handler *)
      (SUBGOAL_THEN `set_of_list ns SUBSET domain (ctxt:num spt)` ASSUME_TAC THENL
          [QPAT_X_ASSUM "domain (acc_vars (loop_Call _ _ _ _) LN) SUBSET _" MP_TAC THEN
           REWRITE_TAC[acc_vars_def; LET_DEF; LET_END_DEF] THEN SIMP[] THEN
           REWRITE_TAC[SUBSET; domain_list_insert; IN_SET_OF_LIST; domain_def; NOT_IN_EMPTY] THEN
           MESON_TAC[];
           ALL_TAC] THEN
         SUBGOAL_THEN `ALL_DISTINCT (MAP (loop_to_word_find_var ctxt) ns)` ASSUME_TAC THENL
          [MATCH_MP_TAC (INST_TYPE [`:(A)word_loc`,`:A`] (GEN_ALL locals_rel_ALL_DISTINCT_MAP)) THEN
           MAP_EVERY EXISTS_TAC [`loop_state_locals (s:(A,FFI)loop_state)`;
                                 `wl_state_locals (t:(A,C,FFI)wl_state)`] THEN
           ASM_REWRITE_TAC[];
           ALL_TAC] THEN
         ASM_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
         ASM_REWRITE_TAC[add_ret_loc_def; domain_mk_new_cutset_not_empty] THEN SIMP[] THEN
         ASM_REWRITE_TAC[] THEN SIMP[]) THEN
      (QBY "wl_state_ffi t = loop_state_ffi s" (FS[loop_to_wordProof_state_rel_def]) THEN
         ASM_CASES_TAC `loop_state_clock (s:(A,FFI)loop_state) = 0` THEN ASM_REWRITE_TAC[] THENL
          [SIMP[] THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN GVS[wl_flush_state_def];
           ALL_TAC] THEN
         SIMP[] THEN
         PAIR_CASES_ON `loop_evaluate (new_code:(A)loop_prog,
                          loop_state_locals_fupd (K (new_env:((A)word_loc)spt))
                           (loop_dec_clock (loop_state_locals_fupd
                             (K (sptree_inter (loop_state_locals s) (live:num_set))) (s:(A,FFI)loop_state))))` THEN
         RENAME1 "loop_evaluate _ = (rb,st)" THEN SIMP[] THEN DISCH_TAC THEN
         SUBGOAL_THEN `~(rb = SOME (loop_Error:(A)loop_result))` ASSUME_TAC THENL
          [DISCH_TAC THEN UNDISCH_TAC `~(res = SOME (loop_Error:(A)loop_result))` THEN GVS[];
           ALL_TAC] THEN
         FIRST_X_ASSUM(MP_TAC o SPECL [`ns:num list`; `live:num_set`;
           `loop_dec_clock (loop_state_locals_fupd (K (sptree_inter (loop_state_locals s) (live:num_set)))
                             (s:(A,FFI)loop_state))`] o
           check (fun th -> try fst(dest_var(fst(dest_forall(concl th)))) = "ns'"
                            with Failure _ -> false)) THEN
         ASM_REWRITE_TAC[cut_res_def; cut_state_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
         SIMP[] THEN
         DISCH_THEN(MP_TAC o SPECL [
           `wl_call_env args1 ss1 (wl_push_env (env1,LN) NONE (wl_dec_clock (t:(A,C,FFI)wl_state)))`;
           `ctxt1:num spt`; `wl_Loc l0 l1:(A)word_loc`; `l1':num#num`]) THEN
         ASM_REWRITE_TAC[isWord_def] THEN ANTS_TAC THENL
          [REWRITE_TAC[wl_call_env_def; wl_push_env_def; LET_DEF; LET_END_DEF] THEN
           CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
           PAIR_CASES_ON `env_to_list (LN:((A)word_loc)spt)
                            (wl_state_permute (wl_dec_clock (t:(A,C,FFI)wl_state)))` THEN
           SIMP[] THEN ASM_REWRITE_TAC[] THEN
           FS[loop_to_wordProof_state_rel_def; loop_dec_clock_def; wl_dec_clock_def];
           ALL_TAC] THEN
         STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[]) THEN
      (QCASES_ON "rb" THENL [ALL_TAC; RENAME1 "loop_evaluate _ = (SOME rr,st)" THEN QCASES_ON "rr"] THEN
         GVS[] THEN TRY(PL2WAUX_ERROR_TAC THEN NO_TAC)) THENL
       [(* the callee returns *)
        (RENAME1 "loop_evaluate _ = (SOME (loop_Result retvs),st)" THEN
           ASM_CASES_TAC `LENGTH (retvs:((A)word_loc)list) = LENGTH (ns:num list)` THEN
           GVS[] THEN TRY(PL2WAUX_ERROR_TAC THEN NO_TAC) THEN
           RULE_ASSUM_TAC(REWRITE_RULE[PL2WAUX_push_env_LN; wl_dec_clock_def]) THEN
           ASM_REWRITE_TAC[wl_pop_env_def] THEN SIMP[]) THEN
        (REWRITE_TAC[domain_fromAList_toAList; wl_evaluate_def] THEN
           SIMP[wl_set_vars_def; set_vars_def; loop_dec_clock_def] THEN
           SUBGOAL_THEN `!n. MEM n ns ==> ~(loop_to_word_find_var ctxt n = 0)` ASSUME_TAC THENL
            [RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_SET_OF_LIST]) THEN
             ASM_MESON_TAC[find_var_neq_0];
             ALL_TAC] THEN
           REPEAT CONJ_TAC THENL
            [FS[loop_to_wordProof_state_rel_def];
             ASM_SIMP_TAC[PL2WAUX_lookup_0_alist_insert; lookup_fromAList_toAList];
             MATCH_MP_TAC locals_rel_alist_insert_toAList THEN ASM_REWRITE_TAC[]]);
        (* the callee raises an exception *)
        (RENAME1 "loop_evaluate _ = (SOME (loop_Exception exn),st)" THEN
           ASM_CASES_TAC `res1 = SOME (wl_Error:(A)wl_result)` THENL [ALL_TAC; RES_TAC] THEN
           GVS[] THEN
           (CONJ_TAC THENL [FS[loop_to_wordProof_state_rel_def]; ALL_TAC] THEN
            RULE_ASSUM_TAC(REWRITE_RULE[PL2WAUX_push_env_LN; wl_dec_clock_def]) THEN
            RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
            ASM_MESON_TAC[PL2WAUX_jump_exc_push]))];
      (* an exception handler *)
      (RENAME1 "loop_Call (SOME (ns,live)) dest argvars (SOME hd)" THEN
         PAIR_CASES_ON `hd:num#(A)loop_prog#(A)loop_prog#num_set` THEN
         RENAME1 "loop_Call (SOME (ns,live)) dest argvars (SOME (hn,hp1,hp2,hlive))" THEN
         SIMP[] THEN
         PAIR_CASES_ON `loop_to_word_comp ctxt (hp1:(A)loop_prog) (l0,l1 + 1)` THEN
         RENAME1 "loop_to_word_comp ctxt hp1 (l0,l1 + 1) = (wp1,la,lb)" THEN SIMP[] THEN
         PAIR_CASES_ON `loop_to_word_comp ctxt (hp2:(A)loop_prog) (la,lb)` THEN
         RENAME1 "loop_to_word_comp ctxt hp2 (la,lb) = (wp2,lc,ld)" THEN SIMP[] THEN
         QPAT_X_ASSUM "domain (acc_vars (loop_Call _ _ _ _) LN) SUBSET _" (MP_TAC o
           REWRITE_RULE[acc_vars_def; LET_DEF; LET_END_DEF]) THEN SIMP[] THEN
         ONCE_REWRITE_TAC[acc_vars_acc] THEN ONCE_REWRITE_TAC[acc_vars_acc] THEN
         REWRITE_TAC[UNION_SUBSET; domain_insert; INSERT_SUBSET] THEN STRIP_TAC THEN
         SUBGOAL_THEN `set_of_list ns SUBSET domain (ctxt:num spt)` ASSUME_TAC THENL
          [UNDISCH_TAC `domain (list_insert ns LN) SUBSET domain (ctxt:num spt)` THEN
           REWRITE_TAC[SUBSET; domain_list_insert; IN_SET_OF_LIST; domain_def; NOT_IN_EMPTY] THEN
           MESON_TAC[];
           ALL_TAC] THEN
         SUBGOAL_THEN `ALL_DISTINCT (MAP (loop_to_word_find_var ctxt) ns)` ASSUME_TAC THENL
          [MATCH_MP_TAC (INST_TYPE [`:(A)word_loc`,`:A`] (GEN_ALL locals_rel_ALL_DISTINCT_MAP)) THEN
           MAP_EVERY EXISTS_TAC [`loop_state_locals (s:(A,FFI)loop_state)`;
                                 `wl_state_locals (t:(A,C,FFI)wl_state)`] THEN
           ASM_REWRITE_TAC[];
           ALL_TAC]) THEN
      (ASM_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
         ASM_REWRITE_TAC[add_ret_loc_def; domain_mk_new_cutset_not_empty] THEN SIMP[] THEN
         ASM_REWRITE_TAC[] THEN SIMP[] THEN
         QBY "wl_state_ffi t = loop_state_ffi s" (FS[loop_to_wordProof_state_rel_def]) THEN
         ASM_CASES_TAC `loop_state_clock (s:(A,FFI)loop_state) = 0` THEN ASM_REWRITE_TAC[] THENL
          [SIMP[] THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN GVS[wl_flush_state_def];
           ALL_TAC] THEN
         SIMP[] THEN
         PAIR_CASES_ON `loop_evaluate (new_code:(A)loop_prog,
                          loop_state_locals_fupd (K (new_env:((A)word_loc)spt))
                           (loop_dec_clock (loop_state_locals_fupd
                             (K (sptree_inter (loop_state_locals s) (live:num_set))) (s:(A,FFI)loop_state))))` THEN
         RENAME1 "loop_evaluate _ = (rb,st)" THEN SIMP[] THEN DISCH_TAC THEN
         SUBGOAL_THEN `~(rb = SOME (loop_Error:(A)loop_result))` ASSUME_TAC THENL
          [DISCH_TAC THEN UNDISCH_TAC `~(res = SOME (loop_Error:(A)loop_result))` THEN GVS[];
           ALL_TAC]) THEN
      (FIRST_X_ASSUM(MP_TAC o SPECL [`ns:num list`; `live:num_set`;
           `loop_dec_clock (loop_state_locals_fupd (K (sptree_inter (loop_state_locals s) (live:num_set)))
                             (s:(A,FFI)loop_state))`] o
           check (fun th -> try let vs,_ = strip_forall(concl th) in
                                fst(dest_var(hd vs)) = "ns'" && length vs = 3
                            with Failure _ -> false)) THEN
         ASM_REWRITE_TAC[cut_res_def; cut_state_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
         SIMP[] THEN
         DISCH_THEN(MP_TAC o SPECL [
           `wl_call_env args1 ss1 (wl_push_env (env1,LN)
              (SOME (loop_to_word_find_var ctxt hn,wp1,lc,ld)) (wl_dec_clock (t:(A,C,FFI)wl_state)))`;
           `ctxt1:num spt`; `wl_Loc l0 l1:(A)word_loc`; `l1':num#num`]) THEN
         ASM_REWRITE_TAC[isWord_def] THEN ANTS_TAC THENL
          [REWRITE_TAC[wl_call_env_def; wl_push_env_def; LET_DEF; LET_END_DEF] THEN
           CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
           PAIR_CASES_ON `env_to_list (LN:((A)word_loc)spt)
                            (wl_state_permute (wl_dec_clock (t:(A,C,FFI)wl_state)))` THEN
           SIMP[] THEN ASM_REWRITE_TAC[] THEN
           FS[loop_to_wordProof_state_rel_def; loop_dec_clock_def; wl_dec_clock_def];
           ALL_TAC] THEN
         STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[]) THEN
      (QCASES_ON "rb" THENL [ALL_TAC; RENAME1 "loop_evaluate _ = (SOME rr,st)" THEN QCASES_ON "rr"] THEN
         GVS[] THEN TRY(PL2WAUX_ERROR_TAC THEN NO_TAC)) THENL
       [(* the callee returns: the return handler runs *)
        (RENAME1 "loop_evaluate _ = (SOME (loop_Result retvs),st)" THEN
           ASM_CASES_TAC `LENGTH (retvs:((A)word_loc)list) = LENGTH (ns:num list)` THEN
           GVS[] THEN TRY(PL2WAUX_ERROR_TAC THEN NO_TAC) THEN
           RULE_ASSUM_TAC(REWRITE_RULE[PL2WAUX_push_env_LN; wl_dec_clock_def]) THEN
           RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
           ASM_REWRITE_TAC[wl_pop_env_def] THEN SIMP[] THEN
           REWRITE_TAC[domain_fromAList_toAList]) THEN
        (PL2WAUX_EVAL_CASES_TAC `hp2:(A)loop_prog` THEN
           RENAME1 "loop_evaluate (hp2,_) = (rh,sh)" THEN
           SUBGOAL_THEN `~(rh = SOME (loop_Error:(A)loop_result))` ASSUME_TAC THENL
            [DISCH_TAC THEN UNDISCH_TAC `~(res = SOME (loop_Error:(A)loop_result))` THEN
             GVS[cut_res_def];
             ALL_TAC] THEN
           FIRST_X_ASSUM(MP_TAC o SPECL [`retvs:((A)word_loc)list`;
             `loop_dec_clock (loop_state_locals_fupd (K (sptree_inter (loop_state_locals s) (live:num_set)))
                               (s:(A,FFI)loop_state))`; `st:(A,FFI)loop_state`] o
             check (fun th -> try let vs,_ = strip_forall(concl th) in
                                  map (fst o dest_var) vs = ["retvs"; "s'"; "st"]
                              with Failure _ -> false)) THEN
           ASM_REWRITE_TAC[cut_res_def; cut_state_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
           SIMP[]) THEN
        (DISCH_THEN(MP_TAC o SPECL [
             `wl_set_vars (MAP (loop_to_word_find_var ctxt) ns) retvs
               (wl_state_locals_fupd (K (fromAList (toAList (env1:((A)word_loc)spt))))
               (wl_state_locals_size_fupd (K (wl_state_locals_size (t:(A,C,FFI)wl_state)))
               (wl_state_stack_fupd (K (wl_state_stack t))
               (wl_state_handler_fupd (K (wl_state_handler t)) (t1:(A,C,FFI)wl_state)))))`;
             `ctxt:num spt`; `retv:(A)word_loc`; `(la:num,lb:num)`]) THEN
           ASM_REWRITE_TAC[] THEN
           SUBGOAL_THEN `!n. MEM n ns ==> ~(loop_to_word_find_var ctxt n = 0)` ASSUME_TAC THENL
            [RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_SET_OF_LIST]) THEN
             ASM_MESON_TAC[find_var_neq_0];
             ALL_TAC] THEN
           ANTS_TAC THENL
            [REWRITE_TAC[set_vars_def; wl_set_vars_def; loop_dec_clock_def] THEN SIMP[] THEN
             ASM_SIMP_TAC[PL2WAUX_lookup_0_alist_insert; lookup_fromAList_toAList] THEN
             CONJ_TAC THENL
              [FS[loop_to_wordProof_state_rel_def];
               MATCH_MP_TAC locals_rel_alist_insert_toAList THEN ASM_REWRITE_TAC[]];
             ALL_TAC] THEN
           STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[]) THEN
        (QCASES_ON "rh" THENL [ALL_TAC; RENAME1 "loop_evaluate _ = (SOME rh2,sh)" THEN QCASES_ON "rh2"] THEN
           GVS[cut_res_def] THEN TRY(PL2WAUX_ERROR_TAC THEN NO_TAC)) THENL
        [(* the result of the handler is NONE *)
         QBY "wl_state_clock t1' = loop_state_clock sh" (FS[loop_to_wordProof_state_rel_def]) THEN
           FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=)
             `cut_state (hlive:num_set) (sh:(A,FFI)loop_state)`)) (concl th))) THEN
           REWRITE_TAC[cut_state_def] THEN
           COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
           ASM_CASES_TAC `loop_state_clock (sh:(A,FFI)loop_state) = 0` THEN
           ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN GVS[wl_flush_state_def] THEN
           ASM_SIMP_TAC[PL2WAUX_locals_rel_inter; wl_dec_clock_def] THEN
           FS[loop_dec_clock_def; wl_dec_clock_def; loop_to_wordProof_state_rel_def] THEN
           MATCH_MP_TAC PL2WAUX_locals_rel_inter THEN ASM_REWRITE_TAC[];
         (* an exception *)
         ASM_CASES_TAC `res1' = SOME (wl_Error:(A)wl_result)` THENL
            [GVS[]; RES_TAC THEN GVS[]]];
        (* the callee raises: the exception handler runs *)
        (RENAME1 "loop_evaluate _ = (SOME (loop_Exception exn),st)" THEN
           RULE_ASSUM_TAC(REWRITE_RULE[PL2WAUX_push_env_LN; wl_dec_clock_def; wl_call_env_def]) THEN
           RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
           FIRST_X_ASSUM(fun th ->
             if is_forall(concl th) &&
                can (find_term (fun t -> try fst(dest_const t) = "wl_jump_exc" with Failure _ -> false))
                    (concl th)
             then MP_TAC(CAKE_SIMP_RULE[] (REWRITE_RULE[RICHAUX_LASTN_CONS]
                    (CAKE_SIMP_RULE[] (REWRITE_RULE[wl_jump_exc_def; LENGTH; ARITH_RULE `n < SUC n`] th))))
             else NO_TAC)) THEN
        (DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (fun th ->
             MAP_EVERY (fun f -> ASSUME_TAC(SYM(CAKE_SIMP_RULE[] (AP_TERM f th))))
               [`wl_state_locals:(A,C,FFI)wl_state->((A)word_loc)spt`;
                `wl_state_stack:(A,C,FFI)wl_state->((A)stack_frame)list`;
                `wl_state_handler:(A,C,FFI)wl_state->num`])) THEN
           ASM_REWRITE_TAC[domain_fromAList_toAList] THEN SIMP[] THEN
           PL2WAUX_EVAL_CASES_TAC `hp1:(A)loop_prog` THEN
           RENAME1 "loop_evaluate (hp1,_) = (rh,sh)" THEN
           SUBGOAL_THEN `~(rh = SOME (loop_Error:(A)loop_result))` ASSUME_TAC THENL
            [DISCH_TAC THEN UNDISCH_TAC `~(res = SOME (loop_Error:(A)loop_result))` THEN
             GVS[cut_res_def];
             ALL_TAC]) THEN
        (FIRST_X_ASSUM(MP_TAC o SPECL [`exn:(A)word_loc`;
             `loop_dec_clock (loop_state_locals_fupd (K (sptree_inter (loop_state_locals s) (live:num_set)))
                               (s:(A,FFI)loop_state))`; `st:(A,FFI)loop_state`] o
             check (fun th -> try let vs,_ = strip_forall(concl th) in
                                  map (fst o dest_var) vs = ["exn"; "s'"; "st"]
                              with Failure _ -> false)) THEN
           ASM_REWRITE_TAC[cut_res_def; cut_state_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
           SIMP[] THEN
           DISCH_THEN(MP_TAC o SPECL [
             `wl_set_var (loop_to_word_find_var ctxt hn) exn (t1:(A,C,FFI)wl_state)`;
             `ctxt:num spt`; `retv:(A)word_loc`; `(l0:num,l1 + 1)`]) THEN
           ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
            [REWRITE_TAC[loop_set_var_def; wl_set_var_def; loop_dec_clock_def] THEN SIMP[] THEN
             ASM_REWRITE_TAC[lookup_insert] THEN
             SUBGOAL_THEN `~(0 = loop_to_word_find_var ctxt hn)` (fun th -> REWRITE_TAC[th]) THENL
              [ASM_MESON_TAC[find_var_neq_0]; ALL_TAC] THEN
             ASM_REWRITE_TAC[lookup_fromAList_toAList] THEN
             CONJ_TAC THENL
              [FS[loop_to_wordProof_state_rel_def];
               MATCH_MP_TAC locals_rel_insert THEN ASM_REWRITE_TAC[] THEN
               UNDISCH_TAC `loop_to_wordProof_locals_rel ctxt
                              (sptree_inter (loop_state_locals (s:(A,FFI)loop_state)) (live:num_set)) env1` THEN
               REWRITE_TAC[loop_to_wordProof_locals_rel_def; lookup_fromAList_toAList]];
             ALL_TAC] THEN
           STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[]) THEN
        (QCASES_ON "rh" THENL [ALL_TAC; RENAME1 "loop_evaluate _ = (SOME rh2,sh)" THEN QCASES_ON "rh2"] THEN
           GVS[cut_res_def] THEN TRY(PL2WAUX_ERROR_TAC THEN NO_TAC)) THENL
        [(* the result of the handler is NONE *)
         QBY "wl_state_clock t1' = loop_state_clock sh" (FS[loop_to_wordProof_state_rel_def]) THEN
           FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=)
             `cut_state (hlive:num_set) (sh:(A,FFI)loop_state)`)) (concl th))) THEN
           REWRITE_TAC[cut_state_def] THEN
           COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
           ASM_CASES_TAC `loop_state_clock (sh:(A,FFI)loop_state) = 0` THEN
           ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN GVS[wl_flush_state_def] THEN
           ASM_SIMP_TAC[PL2WAUX_locals_rel_inter; wl_dec_clock_def] THEN
           FS[loop_dec_clock_def; wl_dec_clock_def; loop_to_wordProof_state_rel_def] THEN
           MATCH_MP_TAC PL2WAUX_locals_rel_inter THEN ASM_REWRITE_TAC[];
         (* an exception *)
         ASM_CASES_TAC `res1' = SOME (wl_Error:(A)wl_result)` THENL
            [GVS[]; RES_TAC THEN GVS[]]]]]]);;

(* HOL4: Resume compile_correct[FFI] *)

let PL2WAUX_compile_correct_FFI = prove
 (PL2WAUX_case "loop_FFI",
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_evaluate_def; cut_state_def]) THEN
  GVS_ASM(all_case_eqs()) THEN
  IMP_RES_TAC loop_to_wordProof_locals_rel_get_var THEN
  IMP_RES_TAC loop_to_wordProof_state_rel_intro THEN
  DRULE_ALL cut_env_mk_new_cutset THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP cut_env_mk_new_cutset_IMP) THEN
  ASM_REWRITE_TAC[loop_to_word_comp_def] THEN SIMP[] THEN
  ASM_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
  FS[loop_to_wordProof_state_rel_def; call_env_def]);;

(* HOL4: Resume compile_correct[Arith] *)

let PL2WAUX_compile_correct_Arith = prove
 (PL2WAUX_case "loop_Arith",
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_evaluate_def]) THEN
  QCASES_ON "loop_arith s arith" THEN GVS[] THEN
  QCASES_ON "arith" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[acc_vars_def; loop_arith_def]) THEN
  GVS_ASM(all_case_eqs()) THEN
  IMP_RES_TAC loop_to_wordProof_locals_rel_get_var THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  ASM_REWRITE_TAC[loop_to_word_comp_def; wl_evaluate_def; wl_inst_def; wl_get_vars_def;
                  wl_get_var_def] THEN
  SIMP[] THEN ASM_REWRITE_TAC[] THEN SIMP[loop_set_var_def; wl_set_var_def] THEN
  ASM_REWRITE_TAC[wl_evaluate_def; wl_inst_def; wl_get_vars_def; wl_get_var_def] THEN
  SIMP[] THEN ASM_REWRITE_TAC[] THEN SIMP[wl_set_var_def] THEN
  (REPEAT CONJ_TAC THENL
    [ASM_MESON_TAC[loop_to_wordProof_state_rel_intro];
     FS[loop_to_wordProof_state_rel_def];
     REWRITE_TAC[lookup_insert] THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[find_var_neq_0];
     REPEAT(MATCH_MP_TAC locals_rel_insert THEN ASM_REWRITE_TAC[])]));;

(* HOL4: TAKE_1_word_to_bytes (in HOL4 just before Resume compile_correct[ShMem]) *)

let TAKE_1_word_to_bytes = prove
 (`good_dimindex(:A) ==>
   TAKE 1 (word_to_bytes (w:A word) F) = [get_byte (word 0) w F]`,
  SUBGOAL_THEN `!n. TAKE 1 (word_to_bytes_aux (SUC n) (w:A word) F) =
                    [get_byte (word 0) w F]` ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[word_to_bytes_aux_def; APPEND] THEN
      REWRITE_TAC[num_CONV `1`; TAKE];
      ONCE_REWRITE_TAC[word_to_bytes_aux_def] THEN
      POP_ASSUM MP_TAC THEN
      SPEC_TAC(`word_to_bytes_aux (SUC n) (w:A word) F`,`l:byte list`) THEN
      LIST_INDUCT_TAC THEN
      REWRITE_TAC[APPEND; num_CONV `1`; TAKE; CONJUNCT1 TAKE_DEF; NOT_CONS_NIL]];
    REWRITE_TAC[good_dimindex_def; word_to_bytes_def] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[ARITH_RULE `4 = SUC 3 /\ 8 = SUC 7`]]);;

(* HOL4: Resume compile_correct[ShMem] *)

(* the end of each shared memory case *)

let PL2WAUX_SHMEM_FINISH_TAC =
  REWRITE_TAC[loop_set_var_def; wl_set_var_def; call_env_def; wl_flush_state_def] THEN
  SIMP[] THEN REPEAT CONJ_TAC THEN
  FIRST [FS[loop_to_wordProof_state_rel_def] THEN NO_TAC;
         REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
         ASM_MESON_TAC[find_var_neq_0];
         MATCH_MP_TAC locals_rel_insert THEN ASM_REWRITE_TAC[];
         ASM_REWRITE_TAC[]];;

let PL2WAUX_compile_correct_ShMem = prove
 (PL2WAUX_case "loop_ShMem",
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_evaluate_def]) THEN
  QPAT_X_ASSUM "domain (acc_vars _ LN) SUBSET _"
    (STRIP_ASSUME_TAC o REWRITE_RULE[acc_vars_def; domain_insert; domain_def; INSERT_SUBSET;
                                     EMPTY_SUBSET]) THEN
  GVS_ASM(all_case_eqs()) THEN
  IMP_RES_TAC loop_to_wordProof_comp_exp_preserves_eval THEN
  ASM_REWRITE_TAC[loop_to_word_comp_def; wl_evaluate_def] THEN SIMP[] THEN
  QCASES_ON "op" THEN RULE_ASSUM_TAC(REWRITE_RULE[is_load_def]) THEN GVS_ASM[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_sh_mem_op_def; loop_sh_mem_load_def;
                              loop_sh_mem_store_def]) THEN
  IMP_RES_TAC loop_to_wordProof_locals_rel_get_var THEN
  QBY "wl_state_sh_mdomain t = loop_state_sh_mdomain s" (FS[loop_to_wordProof_state_rel_def]) THEN
  QBY "wl_state_ffi t = loop_state_ffi s" (FS[loop_to_wordProof_state_rel_def]) THEN
  FIRST_ASSUM(fun th -> if concl th = `good_dimindex(:A)`
    then RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP TAKE_1_word_to_bytes th; APPEND])
    else NO_TAC) THEN
  GVS_ASM(all_case_eqs()) THEN
  ASM_REWRITE_TAC[share_inst_def; wl_sh_mem_load_def; wl_sh_mem_load_byte_def;
    wl_sh_mem_load16_def; wl_sh_mem_load32_def; wl_sh_mem_store_def;
    wl_sh_mem_store_byte_def; wl_sh_mem_store16_def; wl_sh_mem_store32_def] THEN
  SIMP[sh_mem_set_var_def] THEN ASM_SIMP_TAC[TAKE_1_word_to_bytes] THEN
  PL2WAUX_SHMEM_FINISH_TAC);;

(* HOL4: Finalise compile_correct.  HOL4 states the conclusion of its      *)
(* induction theorem, !v v1. goal (v,v1); here it is split into prog and s. *)

let loop_to_wordProof_compile_correct =
  let cases = [PL2WAUX_compile_correct_Skip; PL2WAUX_compile_correct_Fail;
    PL2WAUX_compile_correct_Tick; PL2WAUX_compile_correct_Continue;
    PL2WAUX_compile_correct_Break; PL2WAUX_compile_correct_Loop;
    PL2WAUX_compile_correct_Mark; PL2WAUX_compile_correct_Return;
    PL2WAUX_compile_correct_Raise; PL2WAUX_compile_correct_Seq;
    PL2WAUX_compile_correct_Assign; PL2WAUX_compile_correct_Primitive;
    PL2WAUX_compile_correct_LocValue; PL2WAUX_compile_correct_Store;
    PL2WAUX_compile_correct_Store32; PL2WAUX_compile_correct_StoreByte;
    PL2WAUX_compile_correct_Load32; PL2WAUX_compile_correct_LoadByte;
    PL2WAUX_compile_correct_SetGlobal; PL2WAUX_compile_correct_If;
    PL2WAUX_compile_correct_Call; PL2WAUX_compile_correct_FFI;
    PL2WAUX_compile_correct_Arith; PL2WAUX_compile_correct_ShMem] in
  let th = MP PL2WAUX_ind_thm
             (end_itlist CONJ
                (map (fun cj -> find (fun th -> aconv (concl th) cj) cases)
                     (conjuncts(lhand(concl PL2WAUX_ind_thm))))) in
  GENL [`prog:(A)loop_prog`; `s:(A,FFI)loop_state`]
    (CONV_RULE GEN_BETA_CONV (SPEC `(prog:(A)loop_prog,s:(A,FFI)loop_state)` th));;

let state_rel_with_clock = prove
 (`loop_to_wordProof_state_rel (s:(A,FFI)loop_state) (t:(A,C,FFI)wl_state) ==>
   loop_to_wordProof_state_rel (loop_state_clock_fupd (K k) s) (wl_state_clock_fupd (K k) t)`,
  RW[] THEN FS[loop_to_wordProof_state_rel_def]);;

let locals_rel_mk_ctxt_ln = prove
 (`0 < n /\ EVEN n ==> loop_to_wordProof_locals_rel (make_ctxt n xs LN) (LN:(A)spt) lc`,
  REWRITE_TAC[loop_to_wordProof_locals_rel_def; lookup_def; option_DISTINCT] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[INJ; IN_UNIV; domain_lookup] THEN
    MP_TAC(ISPECL [`xs:num list`; `LN:num spt`; `n:num`] make_ctxt_inj) THEN
    REWRITE_TAC[lookup_def; option_DISTINCT] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `vx:num`)
                 (CONJUNCTS_THEN2 (X_CHOOSE_TAC `vy:num`) MP_TAC)) THEN
    ASM_SIMP_TAC[PL2WAUX_find_var_lookup] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`k:num`; `m:num`] THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP lookup_make_ctxt_range) THEN
      REWRITE_TAC[lookup_def; option_DISTINCT] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC lookup_make_ctxt_EVEN THEN
      MAP_EVERY EXISTS_TAC [`xs:num list`; `n:num`; `LN:num spt`; `k:num`] THEN
      ASM_REWRITE_TAC[lookup_def; option_DISTINCT]]]);;

(* ------------------------------------------------------------------------- *)
(* HOL4: state_rel_imp_semantics.  compile_correct relates the two runs of   *)
(* the program of semantics_def at the same clock (state_rel keeps the       *)
(* clocks equal), so the two semantics agree clock by clock: the failure     *)
(* conditions are both false, the terminating behaviours are the same, and   *)
(* the io-event chains of the divergent case are the same sets (HOL4 goes    *)
(* through equiv_lprefix_chain and evaluate_add_clock_io_events_mono; with  *)
(* equal clocks that is not needed).  The ctxt given to compile_correct is   *)
(* LN (HOL4 uses the one of comp_func; any ctxt with locals_rel ctxt LN _    *)
(* works, since the program of semantics_def assigns no variable).           *)
(* ------------------------------------------------------------------------- *)

(* compile_correct at a program p and a state s *)

let PL2WAUX_compile_correct_at p s =
  ISPECL [p; s] loop_to_wordProof_compile_correct;;

(* the run of the program of semantics_def at clock k *)

let PL2WAUX_semantics_run = prove
 (CASE_TERM
  `!(s:(A,FFI)loop_state) (t:(A,C,FFI)wl_state) start k r s1.
     loop_to_wordProof_state_rel s t /\ loop_state_locals s = LN /\ good_dimindex(:A) /\
     lookup 0 (wl_state_locals t) = SOME (wl_Loc 1 0) /\
     loop_evaluate (loop_Call NONE (SOME start) [] NONE,loop_state_clock_fupd (K k) s) =
       (r,s1) /\
     ~(r = SOME loop_Error)
     ==> ?r1 t1.
           wl_evaluate (wl_Call NONE (SOME start) [0] NONE,wl_state_clock_fupd (K k) t) =
             (r1,t1) /\
           wl_state_ffi t1 = loop_state_ffi s1 /\
           (match r with
              SOME (loop_Result v) -> r1 = SOME (wl_Result (wl_Loc 1 0) v)
            | SOME loop_TimeOut -> r1 = SOME wl_TimeOut
            | SOME (loop_FinalFFI f) -> r1 = SOME (wl_FinalFFI f)
            | _ -> T)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(PL2WAUX_compile_correct_at `loop_Call NONE (SOME start) [] NONE:(A)loop_prog`
                                    `loop_state_clock_fupd (K k) (s:(A,FFI)loop_state)`) THEN
  DISCH_THEN(MP_TAC o SPECL [`r:((A)loop_result)option`; `s1:(A,FFI)loop_state`;
     `wl_state_clock_fupd (K k) (t:(A,C,FFI)wl_state)`; `LN:num spt`;
     `wl_Loc 1 0:(A)word_loc`; `(0,0):num#num`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[state_rel_with_clock] THEN SIMP[isWord_def; acc_vars_def; SUBSET_REFL] THEN
    ASM_REWRITE_TAC[loop_to_wordProof_locals_rel_def; lookup_def; domain_def; INJ;
                    NOT_IN_EMPTY; option_DISTINCT];
    ALL_TAC] THEN
  REWRITE_TAC[loop_to_word_comp_def; MAP; LET_DEF; LET_END_DEF] THEN SIMP[] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`res1:((A)wl_result)option`; `t1:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[] THEN
  QCASES_ON "r" THEN FS[] THEN QCASES_ON "a" THEN FS[]);;

(* two semantics are equal when their parts are *)

let PL2WAUX_semantics_cong = prove
 (CASE_TERM
  `!c1 c2 (P1:behaviour->bool) P2 d1 d2.
     (c1 <=> c2) /\ (!res. P1 res <=> P2 res) /\ d1 = d2
     ==> (if c1 then Fail else
            match (some) P1 with NONE -> Diverge d1 | SOME res -> res) =
         (if c2 then Fail else
            match (some) P2 with NONE -> Diverge d2 | SOME res -> res)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `P1:behaviour->bool = P2` SUBST1_TAC THEN
  ASM_REWRITE_TAC[FUN_EQ_THM]);;

(* HOL4: state_rel_imp_semantics *)

let loop_to_wordProof_state_rel_imp_semantics = prove
 (`!(s:(A,FFI)loop_state) (t:(A,C,FFI)wl_state) start.
     loop_to_wordProof_state_rel s t /\
     loop_state_locals s = LN /\ good_dimindex(:A) /\
     lookup 0 (wl_state_locals t) = SOME (wl_Loc 1 0) /\
     (?prog:(A)loop_prog. lookup start (loop_state_code s) = SOME ([],prog)) /\
     ~(loop_semantics s start = Fail)
     ==> wl_semantics t start = loop_semantics s start`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* every run of s ends in TimeOut, FinalFFI or Result (it is not Fail) *)
  SUBGOAL_THEN
   `!k r (s1:(A,FFI)loop_state).
      loop_evaluate (loop_Call NONE (SOME start) [] NONE,loop_state_clock_fupd (K k) s) =
      (r,s1)
      ==> r = SOME loop_TimeOut \/ (?f. r = SOME (loop_FinalFFI f)) \/
          (?v. r = SOME (loop_Result v))`
   (LABEL_TAC "oks") THENL
   [UNDISCH_TAC `~(loop_semantics (s:(A,FFI)loop_state) start = Fail)` THEN
    REWRITE_TAC[loop_semantics_def; LET_DEF; LET_END_DEF] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[FST] THEN QCASES_ON "r" THEN SIMP[] THEN QCASES_ON "a" THEN SIMP[];
    ALL_TAC] THEN
  (* the two runs at each clock *)
  SUBGOAL_THEN
   `!k. ?r (s1:(A,FFI)loop_state) r1 (t1:(A,C,FFI)wl_state).
      loop_evaluate (loop_Call NONE (SOME start) [] NONE,loop_state_clock_fupd (K k) s) =
      (r,s1) /\
      wl_evaluate (wl_Call NONE (SOME start) [0] NONE,wl_state_clock_fupd (K k) t) =
      (r1,t1) /\
      wl_state_ffi t1 = loop_state_ffi s1 /\
      (r = SOME loop_TimeOut /\ r1 = SOME wl_TimeOut \/
       (?f. r = SOME (loop_FinalFFI f) /\ r1 = SOME (wl_FinalFFI f)) \/
       (?v. r = SOME (loop_Result v) /\ r1 = SOME (wl_Result (wl_Loc 1 0) v)))`
   (LABEL_TAC "both") THENL
   [X_GEN_TAC `k:num` THEN
    MP_TAC(ISPEC `loop_evaluate (loop_Call NONE (SOME start) [] NONE:(A)loop_prog,
                                 loop_state_clock_fupd (K k) (s:(A,FFI)loop_state))`
           PAIR_SURJECTIVE) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:((A)loop_result)option`; `s1:(A,FFI)loop_state`] THEN
    DISCH_THEN(LABEL_TAC "evr") THEN
    USE_THEN "oks" (fun oks -> USE_THEN "evr" (LABEL_TAC "rok" o MATCH_MP oks)) THEN
    MP_TAC(SPECL [`s:(A,FFI)loop_state`; `t:(A,C,FFI)wl_state`; `start:num`; `k:num`;
                  `r:((A)loop_result)option`; `s1:(A,FFI)loop_state`]
                 PL2WAUX_semantics_run) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      USE_THEN "rok" (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[option_INJ; distinctness "loop_result"];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:((A)wl_result)option`
      (X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`r:((A)loop_result)option`; `s1:(A,FFI)loop_state`;
                          `r1:((A)wl_result)option`; `t1:(A,C,FFI)wl_state`] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "rok" (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN FS[];
    ALL_TAC] THEN
  REWRITE_TAC[loop_semantics_def; wl_semantics_def; LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC PL2WAUX_semantics_cong THEN REPEAT CONJ_TAC THENL
   [(* neither semantics fails *)
    MATCH_MP_TAC(TAUT `~p /\ ~q ==> (p <=> q)`) THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `k:num` THEN
    USE_THEN "both" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[FST] THEN SIMP[];
    (* the same terminating behaviours, clock by clock *)
    X_GEN_TAC `res:behaviour` THEN BETA_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    USE_THEN "both" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN SIMP[];
    (* the same io-event chains *)
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    USE_THEN "both" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[SND]]);;

(* the function names are kept by compile_prog *)

let PL2WAUX_MAP_FST_compile_prog = prove
 (`!prog:(num # num list # (A)loop_prog)list.
     MAP FST (loop_to_word_compile_prog prog) = MAP FST prog`,
  REWRITE_TAC[loop_to_word_compile_prog_def] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP] THEN
  SPEC_TAC(`h:num # num list # (A)loop_prog`,`h:num # num list # (A)loop_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP[]);;

(* HOL4: first_compile_prog_all_distinct *)

let loop_to_wordProof_first_compile_prog_all_distinct = prove
 (`!prog:(num # num list # (A)loop_prog)list.
     ALL_DISTINCT (MAP FST prog) ==>
     ALL_DISTINCT (MAP FST (loop_to_word_compile_prog prog))`,
  REWRITE_TAC[PL2WAUX_MAP_FST_compile_prog]);;

let first_compile_all_distinct = prove
 (`!prog:(num # num list # (A)loop_prog)list.
     ALL_DISTINCT (MAP FST prog) ==>
     ALL_DISTINCT (MAP FST (loop_to_word_compile prog))`,
  REWRITE_TAC[loop_to_word_compile_def] THEN
  MATCH_ACCEPT_TAC loop_to_wordProof_first_compile_prog_all_distinct);;

let mem_prog_mem_compile_prog = prove
 (`!prog name params (body:(A)loop_prog).
     MEM (name,params,body) prog ==>
     MEM (name,LENGTH params + 1,loop_to_word_comp_func name params body)
         (loop_to_word_compile_prog prog)`,
  REWRITE_TAC[loop_to_word_compile_prog_def; MEM_MAP] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `(name,params,body):num # num list # (A)loop_prog` THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

let lookup_prog_some_lookup_compile_prog = prove
 (`!prog name params (body:(A)loop_prog).
     lookup name (fromAList prog) = SOME (params,body) ==>
     lookup name (fromAList (loop_to_word_compile_prog prog)) =
     SOME (LENGTH params + 1,loop_to_word_comp_func name params body)`,
  REWRITE_TAC[loop_to_word_compile_prog_def] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; fromAList_def; lookup_def; option_DISTINCT] THEN
  SPEC_TAC(`h:num # num list # (A)loop_prog`,`h:num # num list # (A)loop_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP[fromAList_def; lookup_insert] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[option_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* no_install/no_alloc/no_mt lemmas *)

let loop_to_word_comp_not_created = prove
 (CASE_TERM
  `(!x:(A)wl_prog.
      (match x with ShareInst _ _ _ -> T | wl_Call _ _ _ _ -> T
                  | wl_LocValue _ _ -> T | _ -> F) ==> P x) ==>
   !ctxt (prog:(A)loop_prog) l wprog l2.
     loop_to_word_comp ctxt prog l = (wprog,l2) ==>
     not_created_subprogs P wprog`,
  DISCH_TAC THEN REC_IND_TAC loop_to_word_comp_ind THEN
  RW[loop_to_word_comp_def] THEN
  GVS[not_created_subprogs_def] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN
  GVS(all_case_eqs()) THEN
  GVS[not_created_subprogs_def] THEN
  EVERY_CASE_TAC THEN FS[]);;

let loop_to_word_comp_func_not_created = prove
 (CASE_TERM
  `(!x:(A)wl_prog.
      (match x with ShareInst _ _ _ -> T | wl_Call _ _ _ _ -> T
                  | wl_LocValue _ _ -> T | _ -> F) ==> P x) ==>
   !(body:(A)loop_prog) name params.
     not_created_subprogs P (loop_to_word_comp_func name params body)`,
  DISCH_THEN(MP_TAC o MATCH_MP loop_to_word_comp_not_created) THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[loop_to_word_comp_func_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MESON_TAC[PAIR]);;

let loop_to_word_compile_not_created = prove
 (CASE_TERM
  `!pan_prog:(num # num list # (A)loop_prog)list.
     (!x:(A)wl_prog.
        (match x with ShareInst _ _ _ -> T | wl_Call _ _ _ _ -> T
                    | wl_LocValue _ _ -> T | _ -> F) ==> P x) ==>
     ALL (not_created_subprogs P)
       (MAP (SND o SND) (loop_to_word_compile_prog pan_prog))`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[loop_to_word_compile_prog_def; MAP; ALL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_to_word_compile_prog_def]) THEN
  DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  SPEC_TAC(`h:num # num list # (A)loop_prog`,`h:num # num list # (A)loop_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP[o_THM] THEN
  ASM_SIMP_TAC[loop_to_word_comp_func_not_created]);;

(* HOL4: loop_to_word_compile_not_created_MEM [local] *)

let loop_to_word_compile_not_created_MEM = prove
 (CASE_TERM
  `MEM (a,b,(p:(A)wl_prog)) (loop_to_word_compile_prog
                               (pan_prog:(num # num list # (A)loop_prog)list)) ==>
   (!x:(A)wl_prog.
      (match x with ShareInst _ _ _ -> T | wl_Call _ _ _ _ -> T
                  | wl_LocValue _ _ -> T | _ -> F) ==> P x) ==>
   not_created_subprogs P p`,
  REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pan_prog:(num # num list # (A)loop_prog)list` o
                MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
                  (REWRITE_RULE[IMP_CONJ] loop_to_word_compile_not_created))) THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN DISCH_THEN MATCH_MP_TAC THEN
  EXISTS_TAC `(a,b,p):num # num # (A)wl_prog` THEN ASM_REWRITE_TAC[o_THM]);;

let loop_compile_no_install_code = prove
 (`no_install_code
     (fromAList (loop_to_word_compile (prog:(num # num list # (A)loop_prog)list)))`,
  REWRITE_TAC[loop_to_word_compile_def; no_install_code_def;
              wordConvs_no_install_subprogs_def; lookup_fromAList] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP loop_to_word_compile_not_created_MEM) THEN
  GEN_TAC THEN
  ASM_CASES_TAC `x:(A)wl_prog = wl_Install 0 0 0 0 (LN,LN)` THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

let loop_compile_no_alloc_code = prove
 (`no_alloc_code
     (fromAList (loop_to_word_compile (prog:(num # num list # (A)loop_prog)list)))`,
  REWRITE_TAC[loop_to_word_compile_def; no_alloc_code_def;
              no_alloc_subprogs_def; lookup_fromAList] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP loop_to_word_compile_not_created_MEM) THEN
  GEN_TAC THEN
  ASM_CASES_TAC `x:(A)wl_prog = wl_Alloc 0 (LN,LN)` THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

let loop_compile_no_mt_code = prove
 (`no_mt_code
     (fromAList (loop_to_word_compile (prog:(num # num list # (A)loop_prog)list)))`,
  REWRITE_TAC[loop_to_word_compile_def; no_mt_code_def;
              no_mt_subprogs_def; lookup_fromAList] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP loop_to_word_compile_not_created_MEM) THEN
  GEN_TAC THEN
  ASM_CASES_TAC `x:(A)wl_prog = MustTerminate wl_Skip` THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

(* loop_to_word good_handlers *)

let comp_l_invariant = prove
 (`!ctxt (prog:(A)loop_prog) l prog' l'.
     loop_to_word_comp ctxt prog l = (prog',l') ==> FST l' = FST l`,
  REC_IND_TAC loop_to_word_comp_ind THEN RW[loop_to_word_comp_def] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN GVS(all_case_eqs()) THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN GVS[]);;

let good_handlers_comp = prove
 (`!ctxt (prog:(A)loop_prog) l.
     good_handlers (FST l) (FST (loop_to_word_comp ctxt prog l))`,
  REC_IND_TAC loop_to_word_comp_ind THEN RW[good_handlers_def; loop_to_word_comp_def] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN
  REPEAT(TOP_CASE_TAC THEN GVS[]) THEN
  IMP_RES_TAC comp_l_invariant THEN RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN
  ASM_MESON_TAC[]);;

let loop_to_word_good_handlers = prove
 (`loop_to_word_compile_prog (prog:(num # num list # (A)loop_prog)list) = prog' ==>
   ALL (\(n,m,pp). good_handlers n pp) prog'`,
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SPEC_TAC(`prog:(num # num list # (A)loop_prog)list`,
           `prog:(num # num list # (A)loop_prog)list`) THEN
  REWRITE_TAC[loop_to_word_compile_prog_def] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; ALL] THEN
  SPEC_TAC(`h:num # num list # (A)loop_prog`,`h:num # num list # (A)loop_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP[loop_to_word_comp_func_def] THEN
  REWRITE_TAC[REWRITE_RULE[FORALL_PAIR_THM; FST] good_handlers_comp]);;

(* lab_pres for loop_to_word *)

let loop_to_word_comp_SND_LE = prove
 (`!ctxt (prog:(A)loop_prog) l p r.
     loop_to_word_comp ctxt prog l = (p,r) ==> SND l <= SND r`,
  REC_IND_TAC loop_to_word_comp_ind THEN RW[loop_to_word_comp_def] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN GVS(all_case_eqs()) THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN GVS[] THEN ASM_ARITH_TAC);;

let loop_to_word_comp_extract_labels_len = prove
 (`!ctxt (prog:(A)loop_prog) l p r.
     loop_to_word_comp ctxt prog l = (p,r) ==>
     LENGTH (wordConvs_extract_labels p) = SND r - SND l`,
  REC_IND_TAC loop_to_word_comp_ind THEN RW[loop_to_word_comp_def] THEN
  FS[wordConvs_extract_labels_def] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN GVS(all_case_eqs()) THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN
  GVS[wordConvs_extract_labels_def; LENGTH_APPEND; LENGTH] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN
  IMP_RES_TAC loop_to_word_comp_SND_LE THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN FS[LENGTH; LENGTH_APPEND] THEN
  ASM_ARITH_TAC);;

let loop_to_word_comp_extract_labels = prove
 (`!ctxt (prog:(A)loop_prog) l p l'.
     loop_to_word_comp ctxt prog l = (p,l') ==>
     ALL (\(q,r). q = FST l /\ SND l <= r /\ r < SND l')
         (wordConvs_extract_labels p)`,
  REC_IND_TAC loop_to_word_comp_ind THEN RW[loop_to_word_comp_def] THEN
  FS[wordConvs_extract_labels_def] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN GVS(all_case_eqs()) THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN GVS[wordConvs_extract_labels_def] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN
  IMP_RES_TAC loop_to_word_comp_SND_LE THEN IMP_RES_TAC comp_l_invariant THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV GEN_BETA_CONV) o
                 REWRITE_RULE[GSYM ALL_MEM; FORALL_PAIR_THM]) THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_ARITH_TAC);;

let loop_to_word_comp_ALL_DISTINCT = prove
 (`!ctxt (prog:(A)loop_prog) l p r.
     loop_to_word_comp ctxt prog l = (p,r) ==>
     ALL_DISTINCT (wordConvs_extract_labels p)`,
  REC_IND_TAC loop_to_word_comp_ind THEN RW[loop_to_word_comp_def] THEN
  FS[wordConvs_extract_labels_def] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN GVS(all_case_eqs()) THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN GVS[wordConvs_extract_labels_def] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN
  IMP_RES_TAC loop_to_word_comp_extract_labels THEN
  IMP_RES_TAC loop_to_word_comp_SND_LE THEN IMP_RES_TAC comp_l_invariant THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV GEN_BETA_CONV) o
                 REWRITE_RULE[GSYM ALL_MEM; FORALL_PAIR_THM]) THEN
  ASM_REWRITE_TAC[ALL_DISTINCT_APPEND; FORALL_PAIR_THM; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_ARITH_TAC);;

let loop_to_word_comp_func_lab_pres = prove
 (`loop_to_word_comp_func n' params (body:(A)loop_prog) = p ==>
   (!n. n < LENGTH (wordConvs_extract_labels p) ==>
        (\(l1,l2). l1 = n' /\ ~(l2 = 0) /\ ~(l2 = 1))
        (EL n (wordConvs_extract_labels p))) /\
   ALL_DISTINCT (wordConvs_extract_labels p)`,
  REWRITE_TAC[loop_to_word_comp_func_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_GOALSUB_ABBREV_TAC "FST cmp" THEN
  PAIR_CASES_ON `cmp:(A)wl_prog#num#num` THEN REWRITE_TAC[FST] THEN
  IMP_RES_TAC loop_to_word_comp_extract_labels THEN
  IMP_RES_TAC loop_to_word_comp_ALL_DISTINCT THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND; EVERY_EL]) THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`EL n (wordConvs_extract_labels (cmp0:(A)wl_prog))`,`x:num#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  ARITH_TAC);;

let loop_to_word_compile_prog_lab_pres = prove
 (`loop_to_word_compile_prog (prog:(num # num list # (A)loop_prog)list) = prog' ==>
   ALL (\(n,m,p).
          let labs = wordConvs_extract_labels p in
          ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) labs /\
          ALL_DISTINCT labs) prog'`,
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SPEC_TAC(`prog:(num # num list # (A)loop_prog)list`,
           `prog:(num # num list # (A)loop_prog)list`) THEN
  REWRITE_TAC[loop_to_word_compile_prog_def] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; ALL] THEN
  SPEC_TAC(`h:num # num list # (A)loop_prog`,`h:num # num list # (A)loop_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[EVERY_EL] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(GEN_ALL loop_to_word_comp_func_lab_pres) THEN MESON_TAC[]);;

(* first_name offset *)

let loop_to_word_compile_prog_FST_eq = prove
 (`loop_to_word_compile_prog (prog:(num # num list # (A)loop_prog)list) = prog' ==>
   MAP FST prog' = MAP FST prog`,
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[PL2WAUX_MAP_FST_compile_prog]);;

let loop_to_word_compile_prog_lab_min = prove
 (`loop_to_word_compile_prog (prog:(num # num list # (A)loop_prog)list) = prog' /\
   ALL (\p. x <= FST p) prog ==>
   ALL (\p. x <= FST p) prog'`,
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP loop_to_word_compile_prog_FST_eq) THEN
  POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC[GSYM (REWRITE_RULE[o_DEF] (ISPEC `\n:num. x <= n` (GSYM ALL_MAP)))] THEN
  REWRITE_TAC[GSYM o_DEF] THEN
  ONCE_REWRITE_TAC[GSYM ALL_MAP] THEN SIMP_TAC[]);;

let loop_to_word_compile_lab_min = prove
 (`loop_to_word_compile (prog:(num # num list # (A)loop_prog)list) = prog' /\
   ALL (\p. x <= FST p) prog ==>
   ALL (\p. x <= FST p) prog'`,
  REWRITE_TAC[loop_to_word_compile_def; loop_to_word_compile_prog_lab_min]);;

(* inst_ok_less *)

let full_imp_inst_ok_less = prove
 (`!c (prog:(A)wl_prog). full_inst_ok_less c prog ==> every_inst (inst_ok_less c) prog`,
  REC_IND_TAC full_inst_ok_less_ind THEN
  RW[full_inst_ok_less_def; every_inst_def] THEN
  REPEAT(TOP_CASE_TAC THEN FS[]) THEN REWRITE_TAC[inst_ok_less_def]);;

(* HOL4 notes that this definition belongs in loopProps *)

let loop_inst_ok_def = cake_def
  `(loop_inst_ok (c:(A)asm_config) (loop_Arith (LDiv r1 r2 r3):(B)loop_prog) <=>
      asm_config_ISA c IN {ARMv8, MIPS, RISC_V}) /\
   (loop_inst_ok c (loop_Arith (LLongMul r1 r2 r3 r4)) <=>
      (asm_config_ISA c = ARMv7 ==> ~(r1 = r2)) /\
      (asm_config_ISA c = ARMv8 \/ asm_config_ISA c = RISC_V \/ asm_config_ISA c = Ag32
       ==> ~(r1 = r3) /\ ~(r1 = r4))) /\
   (loop_inst_ok c (loop_Arith (LLongDiv r1 r2 r3 r4 r5)) <=>
      asm_config_ISA c = x86_64) /\
   (loop_inst_ok c (_:(B)loop_prog) <=> T)`;;

(* distinct variables, the first one mapped, get distinct names *)

let PL2WAUX_find_var_inj = prove
 (`INJ (loop_to_word_find_var ctxt) (domain ctxt) (:num) /\
   (!n m. lookup n ctxt = SOME m ==> ~(m = 0) /\ EVEN m) /\
   x IN domain ctxt /\ ~(x = y)
   ==> ~(loop_to_word_find_var ctxt x = loop_to_word_find_var ctxt y)`,
  STRIP_TAC THEN ASM_CASES_TAC `y IN domain (ctxt:num spt)` THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[INJ]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[domain_lookup]) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `m:num`) THEN
  ASM_SIMP_TAC[PL2WAUX_find_var_lookup] THEN
  REWRITE_TAC[loop_to_word_find_var_def] THEN
  QCASES_ON "lookup y ctxt" THEN ASM_MESON_TAC[option_CASE]);;

(* the induction hypotheses of a statement with subprograms: the accumulated *)
(* variables of each subprogram are in the context                         *)

let PL2WAUX_EVERY_INST_REC_TAC =
  REPEAT(TOP_CASE_TAC THEN FS[]) THEN FS[every_inst_def] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN
  TRY(QPAT_X_ASSUM "domain (acc_vars _ _) SUBSET _"
       (STRIP_ASSUME_TAC o REWRITE_RULE[UNION_SUBSET] o ONCE_REWRITE_RULE[acc_vars_acc] o
        ONCE_REWRITE_RULE[acc_vars_acc])) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN ASM_REWRITE_TAC[FST] THEN
  SIMP_TAC[];;

let loop_to_word_comp_every_inst_ok_less = prove
 (`!ctxt (prog:(A)loop_prog) l.
     asm_offset_ok 0 (asm_config_byte_offset c) (word 0) /\
     asm_offset_ok 0 (asm_config_addr_offset c) (word 0) /\
     every_prog (loop_inst_ok c) prog /\
     domain (acc_vars prog LN) SUBSET domain ctxt /\
     INJ (loop_to_word_find_var ctxt) (domain ctxt) (:num) /\
     (!n m. lookup n ctxt = SOME m ==> ~(m = 0) /\ EVEN m)
     ==> every_inst (inst_ok_less c) (FST (loop_to_word_comp ctxt prog l))`,
  REC_IND_TAC loop_to_word_comp_ind THEN
  RW[loop_to_word_comp_def; every_inst_def; every_prog_def; loop_inst_ok_def;
     acc_vars_def] THENL
   [(* Primitive: the scratch registers 1 and 3 are odd *)
    QCASES_ON "pop" THEN SIMP[every_inst_def; inst_ok_less_def] THEN
    DISCH_TAC THEN CONV_TAC(RAND_CONV SYM_CONV) THEN MATCH_MP_TAC find_var_neq_odd THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    QCASES_ON "pop" THEN SIMP[every_inst_def];
    (* Arith *)
    QCASES_ON "arith" THEN
    FS[loop_inst_ok_def; every_inst_def; inst_ok_less_def; domain_insert; domain_def;
       INSERT_SUBSET; EMPTY_SUBSET] THEN
    REPEAT STRIP_TAC THEN RES_TAC THEN ASM_MESON_TAC[PL2WAUX_find_var_inj];
    (* Load32, LoadByte, Store32, StoreByte *)
    FS[inst_ok_less_def];
    FS[inst_ok_less_def];
    FS[inst_ok_less_def];
    FS[inst_ok_less_def];
    (* Seq, If, Loop, Call *)
    PL2WAUX_EVERY_INST_REC_TAC;
    PL2WAUX_EVERY_INST_REC_TAC;
    PL2WAUX_EVERY_INST_REC_TAC;
    PL2WAUX_EVERY_INST_REC_TAC]);;

let loop_to_word_comp_func_every_inst_ok_less = prove
 (`loop_to_word_comp_func n params (body:(A)loop_prog) = p /\
   every_prog (loop_inst_ok c) body /\
   asm_offset_ok 0 (asm_config_addr_offset c) (word 0) /\
   asm_offset_ok 0 (asm_config_byte_offset c) (word 0) ==>
   every_inst (inst_ok_less c) p`,
  REWRITE_TAC[loop_to_word_comp_func_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC loop_to_word_comp_every_inst_ok_less THEN ASM_REWRITE_TAC[] THEN
  MATCH_GOALSUB_ABBREV_TAC "make_ctxt 2 lista LN" THEN
  SUBGOAL_THEN
   `loop_to_wordProof_locals_rel (make_ctxt 2 lista LN) (LN:((A)word_loc)spt) LN`
   (STRIP_ASSUME_TAC o MATCH_MP loop_to_wordProof_locals_rel_intro) THENL
   [MATCH_MP_TAC locals_rel_mk_ctxt_ln THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "lista" THEN
  REWRITE_TAC[domain_make_ctxt; set_fromNumSet; domain_difference; domain_toNumSet;
              SET_OF_LIST_APPEND; domain_def] THEN
  SET_TAC[]);;

let loop_to_word_compile_prog_every_inst_ok_less = prove
 (`loop_to_word_compile_prog (lprog:(num # num list # (A)loop_prog)list) = wprog0 /\
   asm_offset_ok 0 (asm_config_byte_offset c) (word 0) /\
   asm_offset_ok 0 (asm_config_addr_offset c) (word 0) /\
   ALL (\(n,params,body). every_prog (loop_inst_ok c) body) lprog
   ==> ALL (\(n,m,p). every_inst (inst_ok_less c) p) wprog0`,
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`lprog:(num # num list # (A)loop_prog)list`,
           `lprog:(num # num list # (A)loop_prog)list`) THEN
  REWRITE_TAC[loop_to_word_compile_prog_def] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; ALL] THEN
  SPEC_TAC(`h:num # num list # (A)loop_prog`,`h:num # num list # (A)loop_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP[] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC(GEN_ALL loop_to_word_comp_func_every_inst_ok_less) THEN
  ASM_MESON_TAC[]);;

let loop_to_word_every_inst_ok_less = prove
 (`loop_to_word_compile (lprog:(num # num list # (A)loop_prog)list) = wprog0 /\
   asm_offset_ok 0 (asm_config_byte_offset c) (word 0) /\
   asm_offset_ok 0 (asm_config_addr_offset c) (word 0) /\
   ALL (\(n,params,body). every_prog (loop_inst_ok c) body) lprog
   ==> ALL (\(n,m,p). every_inst (inst_ok_less c) p) wprog0`,
  REWRITE_TAC[loop_to_word_compile_def; loop_to_word_compile_prog_every_inst_ok_less]);;
