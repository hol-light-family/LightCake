(* ========================================================================= *)
(* word_elimProof: port of HOL4 compiler/backend/proofs/                     *)
(* word_elimProofScript.sml (CakeML v3479).                                  *)
(* Correctness proof for word_elim.                                          *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The names of wordLang, wordSem and wordProps are those of their files  *)
(*   (wl_evaluate, wl_get_var, wl_state_locals, ...): HOL4 s.f is           *)
(*   wl_state_f s, s with f := v is wl_state_f_fupd (K v) s.  HOL4 get_store,*)
(*   get_stack and code_rel of this theory are word_elimProof_get_store,    *)
(*   word_elimProof_get_stack and word_elimProof_code_rel (names.tsv);      *)
(*   HOL4 no_install is wordConvs_no_install; () is one; SET_TO_LIST is     *)
(*   list_of_set; BIGUNION (set l) is UNIONS (set_of_list l).                *)
(* - HOL4 unused quantified variables keep their own type variables (the e *)
(*   of get_num_wordloc_alist_thm, the l1 l2 of word_state_rel_pop_env, the *)
(*   r of word_removal_thm); free variables of HOL4 statements stay free    *)
(*   (lsz of get_stack_hd_thm, n of stack_list_rearrange_lemma, mem of      *)
(*   FINITE_mdom_mem).  The variable memory of get_memory_update is mem     *)
(*   (memory is a constant of another file).                                *)
(* - word_removal_lemma is proved by induction with wl_evaluate_ind (HOL4   *)
(*   recInduct evaluate_ind, with its suspend/Resume cases), one local      *)
(*   tactic per clause of evaluate.  The proof uses that related states     *)
(*   differ only in their code (WELIMAUX_word_state_rel_code): a statement  *)
(*   that does not look at the code runs in the same way on both, and the   *)
(*   locations of its result come from a safety lemma about the source      *)
(*   semantics alone (WELIMAUX_safe_...).  WELIMAUX_ names are local        *)
(*   helpers.                                                                *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mllist.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_elim.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "hol4/spt_closure.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Analysis lemmas                                                           *)
(* ------------------------------------------------------------------------- *)

let lookup_analyse_word_code = prove
 (`!code n (arity:B) (prog:(A)wl_prog).
     ALOOKUP code n = SOME (arity,prog)
     ==> lookup n (analyse_word_code code) = SOME (find_word_ref prog)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_DEF; option_DISTINCT] THEN
  SPEC_TAC(`h:num#B#(A)wl_prog`,`h:num#B#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; analyse_word_code_def; lookup_insert] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP[option_INJ; PAIR_EQ]);;

let remove_word_code_thm = prove
 (`!n (reachable:1 spt) (l:(num#B)list).
     ALL_DISTINCT (MAP FST l)
     ==> !v. n IN domain reachable /\ MEM (n,v) l <=>
             MEM (n,v) (remove_word_code reachable l)`,
  REWRITE_TAC[remove_word_code_def; MEM_FILTER; domain_lookup;
              IS_SOME_EXISTS; FST] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Definitions                                                               *)
(* ------------------------------------------------------------------------- *)

(* HOL4 type word_loc = Word (A word) | Loc num num *)

let dest_word_loc_def = cake_def
  `(dest_word_loc (wl_Loc n (_:num)) = SOME n) /\
   (dest_word_loc (_:(A)word_loc) = NONE)`;;

let dest_result_loc_def = cake_def
  `(dest_result_loc (SOME (wl_Result (w:(A)word_loc) ns)) =
      UNIONS (set_of_list (MAP (\x. match dest_word_loc x with
                                      NONE -> {}
                                    | SOME x -> {x}) ns))) /\
   (dest_result_loc (SOME (wl_Exception (w:(A)word_loc) (wl_Loc n n0))) = {n}) /\
   (dest_result_loc (_:((A)wl_result)option) = {})`;;

(* locals : ((A)word_loc)spt *)

let get_locals_def = cake_def
  `(get_locals (LN:((A)word_loc)spt) = LN:1 spt) /\
   (get_locals (LS a) =
      match dest_word_loc a with SOME n -> insert n one LN | NONE -> LN) /\
   (get_locals (BN t1 t2) = union (get_locals t1) (get_locals t2)) /\
   (get_locals (BS t1 a t2) =
      let t = union (get_locals t1) (get_locals t2) in
      match dest_word_loc a with SOME n -> insert n one t | NONE -> t)`;;

let domain_get_locals_lookup = prove
 (`!n (t:((A)word_loc)spt).
     n IN domain (get_locals t) <=> ?k n1. lookup k t = SOME (wl_Loc n n1)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC spt_INDUCT THEN
  REWRITE_TAC[get_locals_def; SPTAUX_EXISTS_lookup; LET_DEF; LET_END_DEF] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[domain_def; NOT_IN_EMPTY];
    GEN_TAC THEN
    DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
      (ISPEC `a:(A)word_loc` (cases "word_loc"));
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC);
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
      (ISPEC `a1:(A)word_loc` (cases "word_loc"))] THEN
  ASM_REWRITE_TAC[dest_word_loc_def; option_CASE; domain_union; domain_insert;
    domain_def; IN_UNION; IN_INSERT; NOT_IN_EMPTY; injectivity "word_loc";
    distinctness "word_loc"] THEN
  MESON_TAC[]);;

let get_locals_insert_Loc = prove
 (`!k n1 n0 (locals:((A)word_loc)spt).
     domain (get_locals (insert k (wl_Loc n1 n0) locals)) SUBSET
     domain (get_locals locals) UNION {n1}`,
  REWRITE_TAC[SUBSET; IN_UNION; IN_SING; domain_get_locals_lookup;
              lookup_insert] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `k':num` MP_TAC) THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN MESON_TAC[]);;

let get_locals_insert = prove
 (CASE_TERM
  `!k (v:(A)word_loc) locals.
     domain (get_locals (insert k v locals)) SUBSET
     domain (get_locals locals) UNION
     (match dest_word_loc v with NONE -> {} | SOME n -> {n})`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
    (ISPEC `v:(A)word_loc` (cases "word_loc")) THEN
  REWRITE_TAC[dest_word_loc_def; option_CASE; get_locals_insert_Loc] THEN
  REWRITE_TAC[SUBSET; IN_UNION; NOT_IN_EMPTY; domain_get_locals_lookup;
              lookup_insert] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `k':num` MP_TAC) THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; distinctness "word_loc"] THEN MESON_TAC[]);;

(* the locations of a list of values, as a num_set (a helper of the        *)
(* get_store, get_num_wordloc_alist and get_memory lemmas)                 *)

let WELIMAUX_MEM_locs = prove
 (`!(l:((A)word_loc)list) n.
     MEM n (MAP THE (FILTER IS_SOME (MAP dest_word_loc l))) <=>
     ?n1. MEM (wl_Loc n n1) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; FILTER; MEM] THEN
  DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
    (ISPEC `h:(A)word_loc` (cases "word_loc")) THEN
  ASM_REWRITE_TAC[dest_word_loc_def; IS_SOME_DEF; MAP; MEM; THE_DEF;
                  injectivity "word_loc"; distinctness "word_loc"] THEN
  MESON_TAC[]);;

let WELIMAUX_domain_locs = prove
 (`!(l:((A)word_loc)list) n.
     n IN domain (FOLDL (\acc loc. insert loc one acc) (LN:1 spt)
                        (MAP THE (FILTER IS_SOME (MAP dest_word_loc l)))) <=>
     ?n1. MEM (wl_Loc n n1) l`,
  REWRITE_TAC[domain_nat_set_from_list; domain_def; UNION_EMPTY;
              IN_SET_OF_LIST; WELIMAUX_MEM_locs]);;

(* TODO fix conflict with get_store in WordSem *)

(* store : (store_name,(A)word_loc)fmap *)

let word_elimProof_get_store_def = cake_def
  `word_elimProof_get_store (st:(store_name,(A)word_loc)fmap) =
     let locSet = list_of_set (FRANGE st) in
     let locList = MAP THE (FILTER IS_SOME (MAP dest_word_loc locSet)) in
     FOLDL (\acc loc. insert loc one acc) (LN:1 spt) locList`;;

let domain_get_store = prove
 (`!n (store:(store_name,(A)word_loc)fmap).
     n IN domain (word_elimProof_get_store store) <=>
     ?k n1. FLOOKUP store k = SOME (wl_Loc n n1)`,
  REWRITE_TAC[word_elimProof_get_store_def; LET_DEF; LET_END_DEF;
              WELIMAUX_domain_locs] THEN
  SIMP_TAC[MEM_LIST_OF_SET; FINITE_FRANGE; IN_FRANGE_FLOOKUP] THEN
  MESON_TAC[]);;

let get_store_update = prove
 (CASE_TERM
  `!(store:(store_name,(A)word_loc)fmap) k v.
     domain (word_elimProof_get_store (store |+ (k,v))) SUBSET
     domain (word_elimProof_get_store store) UNION
     (match dest_word_loc v with NONE -> {} | SOME n -> {n})`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SUBSET; IN_UNION; domain_get_store; FLOOKUP_UPDATE] THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(X_CHOOSE_THEN `k':store_name` MP_TAC) THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
   [DISCH_THEN(X_CHOOSE_THEN `n1:num` SUBST1_TAC) THEN
    REWRITE_TAC[dest_word_loc_def; option_CASE; IN_SING];
    MESON_TAC[]]);;

let get_num_wordloc_alist_def = cake_def
  `get_num_wordloc_alist (l:(num#(A)word_loc)list) =
     let locs = MAP THE (FILTER IS_SOME (MAP (dest_word_loc o SND) l)) in
     FOLDL (\acc loc. insert loc one acc) (LN:1 spt) locs`;;

let get_num_wordloc_alist_thm = prove
 (`!n (e:B) (l:(num#(A)word_loc)list).
     (?n0. MEM (wl_Loc n n0) (MAP SND l)) <=>
     n IN domain (get_num_wordloc_alist l)`,
  REWRITE_TAC[get_num_wordloc_alist_def; LET_DEF; LET_END_DEF; MAP_o;
              WELIMAUX_domain_locs]);;

let get_num_wordloc_alist_get_locals = prove
 (`!e:(num#(A)word_loc)list.
     domain (get_locals (fromAList e)) SUBSET domain (get_num_wordloc_alist e)`,
  REWRITE_TAC[SUBSET; domain_get_locals_lookup; lookup_fromAList;
              GSYM get_num_wordloc_alist_thm; MEM_MAP] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `n1:num`
    (ASSUME_TAC o MATCH_MP ALOOKUP_MEM))) THEN
  MAP_EVERY EXISTS_TAC [`n1:num`; `(k:num,wl_Loc x n1:(A)word_loc)`] THEN
  ASM_REWRITE_TAC[]);;

let get_locals_union_subset = prove
 (`!A (B:((A)word_loc)spt).
     domain (get_locals (union A B)) SUBSET
     domain (union (get_locals A) (get_locals B))`,
  REWRITE_TAC[SUBSET; domain_union; IN_UNION; domain_get_locals_lookup;
              lookup_union] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `n1:num`
    MP_TAC)) THEN
  CASES_ON `lookup k (A:((A)word_loc)spt)` THEN
  REWRITE_TAC[option_CASE; option_INJ] THEN ASM_MESON_TAC[]);;

(* stack : ((A)stack_frame)list *)

let word_elimProof_get_stack_def = cake_def
  `(word_elimProof_get_stack ([]:((A)stack_frame)list) = LN:1 spt) /\
   (word_elimProof_get_stack (CONS (StackFrame lsz e0 e _) xs) =
      union (union (get_num_wordloc_alist e0) (get_num_wordloc_alist e))
            (word_elimProof_get_stack xs))`;;

let word_elimProof_get_stack_ind = cake_ind "word_elimProof_get_stack";;

let get_stack_hd_thm = prove
 (`!stack dr (l0:(num#(A)word_loc)list) l opt t.
     domain (word_elimProof_get_stack stack) SUBSET dr /\
     stack = CONS (StackFrame (lsz:num option) l l0 opt) t
     ==> domain (get_locals (union (fromAList l0) (fromAList l))) SUBSET dr /\
         domain (word_elimProof_get_stack t) SUBSET dr`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST1_TAC) THEN
  REWRITE_TAC[word_elimProof_get_stack_def; domain_union] THEN
  MP_TAC(ISPECL [`fromAList (l0:(num#(A)word_loc)list)`;
                 `fromAList (l:(num#(A)word_loc)list)`] get_locals_union_subset) THEN
  MP_TAC(ISPEC `l0:(num#(A)word_loc)list` get_num_wordloc_alist_get_locals) THEN
  MP_TAC(ISPEC `l:(num#(A)word_loc)list` get_num_wordloc_alist_get_locals) THEN
  REWRITE_TAC[domain_union] THEN SET_TAC[]);;

let get_stack_LASTN = prove
 (`!(stack:((A)stack_frame)list) n.
     domain (word_elimProof_get_stack (LASTN n stack)) SUBSET
     domain (word_elimProof_get_stack stack)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LASTN_ALT; SUBSET_REFL] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[SUBSET_REFL] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `domain (word_elimProof_get_stack (t:((A)stack_frame)list))` THEN
  ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC (ISPEC `h:(A)stack_frame` (cases "stack_frame")) THEN
  REWRITE_TAC[word_elimProof_get_stack_def; domain_union] THEN SET_TAC[]);;

let get_stack_CONS = prove
 (`!(h:(A)stack_frame) t.
     domain (word_elimProof_get_stack [h]) SUBSET
     domain (word_elimProof_get_stack (CONS h t)) /\
     domain (word_elimProof_get_stack t) SUBSET
     domain (word_elimProof_get_stack (CONS h t))`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `h:(A)stack_frame` (cases "stack_frame")) THEN
  REWRITE_TAC[word_elimProof_get_stack_def; domain_union; domain_def] THEN
  SET_TAC[]);;

let get_stack_enc_stack = prove
 (CASE_TERM
  `!(stack:((A)stack_frame)list) (reachable:B spt).
     domain (word_elimProof_get_stack stack) SUBSET domain reachable
     ==> !e. MEM e (wl_enc_stack stack)
             ==> (match dest_word_loc e with NONE -> {} | SOME n -> {n}) SUBSET
                 domain reachable`,
  MATCH_MP_TAC word_elimProof_get_stack_ind THEN
  REWRITE_TAC[wl_enc_stack_def; MEM; word_elimProof_get_stack_def;
              domain_union; UNION_SUBSET; MEM_APPEND] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `w:(A)word_loc` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN (CASE_TERM `!w:(A)word_loc. MEM w (MAP SND (e:(num#(A)word_loc)list))
    ==> (match dest_word_loc w with NONE -> {} | SOME n -> {n}) SUBSET
        domain (reachable:B spt)`) (fun th -> ASM_MESON_TAC[th]) THEN
  X_GEN_TAC `v:(A)word_loc` THEN
  DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
    (ISPEC `v:(A)word_loc` (cases "word_loc")) THEN
  REWRITE_TAC[dest_word_loc_def; option_CASE; EMPTY_SUBSET; SING_SUBSET] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `a0 IN domain (get_num_wordloc_alist (e:(num#(A)word_loc)list))`
    MP_TAC THENL
   [REWRITE_TAC[GSYM get_num_wordloc_alist_thm] THEN
    ASM_MESON_TAC[];
    ASM SET_TAC[]]);;

let WELIMAUX_dec_stack_step = prove
 (`!(xs:((A)word_loc)list) n l0 l handler st (reachable:B spt) new_stack.
     (~(LENGTH xs < LENGTH l)
      ==> !(reachable:B spt) new_stack.
            (!n n0. MEM (wl_Loc n n0) (DROP (LENGTH l) xs)
                    ==> n IN domain reachable) /\
            domain (word_elimProof_get_stack st) SUBSET domain reachable /\
            wl_dec_stack (DROP (LENGTH l) xs) st = SOME new_stack
            ==> domain (word_elimProof_get_stack new_stack) SUBSET
                domain reachable) /\
     (!n n0. MEM (wl_Loc n n0) xs ==> n IN domain reachable) /\
     domain (word_elimProof_get_stack (CONS (StackFrame n l0 l handler) st))
       SUBSET domain reachable /\
     wl_dec_stack xs (CONS (StackFrame n l0 l handler) st) = SOME new_stack
     ==> domain (word_elimProof_get_stack new_stack) SUBSET domain reachable`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IL2AUX_dec_stack_cons] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `wl_dec_stack (DROP (LENGTH (l:(num#(A)word_loc)list))
                           (xs:((A)word_loc)list)) (st:((A)stack_frame)list)` THEN
  ASM_REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN
  REWRITE_TAC[word_elimProof_get_stack_def; domain_union; UNION_SUBSET] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `domain (word_elimProof_get_stack (a:((A)stack_frame)list)) SUBSET
                domain (reachable:B spt)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM_DROP_IMP]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  ASM_REWRITE_TAC[word_elimProof_get_stack_def; domain_union; UNION_SUBSET] THEN
  REWRITE_TAC[SUBSET; GSYM get_num_wordloc_alist_thm] THEN
  SUBGOAL_THEN `MAP SND (ZIP (MAP FST (l:(num#(A)word_loc)list))
                     (TAKE (LENGTH l) (xs:((A)word_loc)list))) =
                TAKE (LENGTH l) xs` SUBST1_TAC THENL
   [MATCH_MP_TAC MAP_SND_ZIP THEN REWRITE_TAC[LENGTH_MAP] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC LENGTH_TAKE THEN ASM_ARITH_TAC;
    ASM_MESON_TAC[MEM_TAKE]]);;

let get_stack_dec_stack = prove
 (`!(locs:((A)word_loc)list) stack (reachable:B spt) new_stack.
     (!n n0. MEM (wl_Loc n n0) locs ==> n IN domain reachable) /\
     domain (word_elimProof_get_stack stack) SUBSET domain reachable /\
     wl_dec_stack locs stack = SOME new_stack
     ==> domain (word_elimProof_get_stack new_stack) SUBSET domain reachable`,
  MATCH_MP_TAC wl_dec_stack_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[wl_dec_stack_def; option_INJ] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[word_elimProof_get_stack_def; domain_def; EMPTY_SUBSET];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC (ISPECL [`[]:((A)word_loc)list`; `n:num option`;
      `l0:(num#(A)word_loc)list`; `l:(num#(A)word_loc)list`;
      `handler:(num#num#num)option`; `st:((A)stack_frame)list`;
      `reachable:B spt`; `new_stack:((A)stack_frame)list`]
      WELIMAUX_dec_stack_step) THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC (ISPECL [`CONS (v2:(A)word_loc) v3`; `n:num option`;
      `l0:(num#(A)word_loc)list`; `l:(num#(A)word_loc)list`;
      `handler:(num#num#num)option`; `st:((A)stack_frame)list`;
      `reachable:B spt`; `new_stack:((A)stack_frame)list`]
      WELIMAUX_dec_stack_step) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[wl_dec_stack_def; option_DISTINCT]]);;

(* memory : A word -> (A)word_loc *)

let get_memory_def = cake_def
  `get_memory (mem:A word->(A)word_loc) (mdom:A word->bool) =
     let locSet = list_of_set (IMAGE mem mdom) in
     let locList = MAP THE (FILTER IS_SOME (MAP dest_word_loc locSet)) in
     FOLDL (\acc loc. insert loc one acc) (LN:1 spt) locList`;;

let FINITE_mdom_mem = prove
 (`!mdom. FINITE mdom ==> FINITE {(mem:A->B) x | x IN mdom}`,
  SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE]);;

let domain_get_memory = prove
 (`!(mem:A word->(A)word_loc) (mdom:A word->bool) n.
     n IN domain (get_memory mem mdom) <=>
     ?k n1. k IN mdom /\ mem k = wl_Loc n n1`,
  REWRITE_TAC[get_memory_def; LET_DEF; LET_END_DEF; WELIMAUX_domain_locs] THEN
  SIMP_TAC[MEM_LIST_OF_SET; FINITE_IMAGE; WORD_FINITE; IN_IMAGE] THEN
  MESON_TAC[]);;

let get_memory_update = prove
 (CASE_TERM
  `!k (v:(A)word_loc) (mem:A word->(A)word_loc) (mdomain:A word->bool).
     domain (get_memory ((k =+ v) mem) mdomain) SUBSET
     domain (get_memory mem mdomain) UNION
     (match dest_word_loc v with NONE -> {} | SOME n -> {n})`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SUBSET; IN_UNION; domain_get_memory; APPLY_UPDATE_THM] THEN
  X_GEN_TAC `n:num` THEN
  DISCH_THEN(X_CHOOSE_THEN `k':A word` (X_CHOOSE_THEN `n1:num` MP_TAC)) THEN
  COND_CASES_TAC THENL
   [DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    REWRITE_TAC[dest_word_loc_def; option_CASE; IN_SING];
    MESON_TAC[]]);;

let find_loc_state_def = cake_def
  `find_loc_state (s:(A,C,FFI)wl_state) =
     let loc = get_locals (wl_state_locals s) in
     let sto = word_elimProof_get_store (wl_state_store s) in
     let sta = word_elimProof_get_stack (wl_state_stack s) in
     let mem = get_memory (wl_state_memory s) (wl_state_mdomain s) in
     union (union loc sto) (union sta mem)`;;

let domain_find_loc_state = prove
 (`!s:(A,C,FFI)wl_state.
     domain (find_loc_state s) =
     ((domain (get_locals (wl_state_locals s)) UNION
       domain (word_elimProof_get_store (wl_state_store s))) UNION
      domain (word_elimProof_get_stack (wl_state_stack s))) UNION
     domain (get_memory (wl_state_memory s) (wl_state_mdomain s))`,
  REWRITE_TAC[find_loc_state_def; LET_DEF; LET_END_DEF; domain_union;
              UNION_ASSOC]);;

let word_elimProof_code_rel_def = cake_def
  `word_elimProof_code_rel (reachable:1 spt) (s_code:(num#(A)wl_prog)spt)
                           (t_code:(num#(A)wl_prog)spt) <=>
     !n. n IN domain reachable ==> lookup n s_code = lookup n t_code`;;

let code_closed_def = cake_def
  `code_closed (reachable:B spt) (c1:(C#(A)wl_prog)spt) <=>
     ?code1. c1 = fromAList code1 /\
             !n m. n IN domain reachable /\
                   is_reachable (analyse_word_code code1) n m
                   ==> m IN domain reachable`;;

let gc_no_new_locs_def = cake_def
  `gc_no_new_locs (g:((A)word_loc)list#(A word->(A)word_loc)#(A word->bool)#
                     (store_name,(A)word_loc)fmap->
                     (((A)word_loc)list#(A word->(A)word_loc)#
                      (store_name,(A)word_loc)fmap)option) <=>
     !sta mem mdom sto wl mem1 sto1 sta1.
       g (wl_enc_stack sta, mem, mdom, sto) = SOME (wl, mem1, sto1) /\
       wl_dec_stack wl sta = SOME sta1
       ==> domain (word_elimProof_get_stack sta1) SUBSET
           domain (word_elimProof_get_stack sta) /\
           domain (get_memory mem1 mdom) SUBSET domain (get_memory mem mdom) /\
           domain (word_elimProof_get_store sto1) SUBSET
           domain (word_elimProof_get_store sto)`;;

let word_state_rel_def = cake_def
  `word_state_rel (reachable:1 spt) (t:(A,C,FFI)wl_state) (s:(A,C,FFI)wl_state) <=>
     wl_state_locals s = wl_state_locals t /\
     wl_state_fp_regs s = wl_state_fp_regs t /\
     wl_state_store s = wl_state_store t /\
     wl_state_stack s = wl_state_stack t /\
     wl_state_memory s = wl_state_memory t /\
     wl_state_mdomain s = wl_state_mdomain t /\
     wl_state_sh_mdomain s = wl_state_sh_mdomain t /\
     wl_state_permute s = wl_state_permute t /\
     wl_state_compile s = wl_state_compile t /\
     wl_state_compile_oracle s = wl_state_compile_oracle t /\
     wl_state_code_buffer s = wl_state_code_buffer t /\
     wl_state_data_buffer s = wl_state_data_buffer t /\
     wl_state_gc_fun s = wl_state_gc_fun t /\
     wl_state_handler s = wl_state_handler t /\
     wl_state_clock s = wl_state_clock t /\
     wl_state_termdep s = wl_state_termdep t /\
     wl_state_be s = wl_state_be t /\
     wl_state_ffi s = wl_state_ffi t /\
     wl_state_locals_size s = wl_state_locals_size t /\
     wl_state_stack_max s = wl_state_stack_max t /\
     wl_state_stack_limit s = wl_state_stack_limit t /\
     wl_state_stack_size s = wl_state_stack_size t /\
     word_elimProof_code_rel reachable (wl_state_code s) (wl_state_code t) /\
     domain (find_loc_state t) SUBSET domain reachable`;;

(* ------------------------------------------------------------------------- *)
(* Other lemmas                                                              *)
(* ------------------------------------------------------------------------- *)

let ALOOKUP_ZIP_SUCCESS = prove
 (`!(x:A list) (y:B list) k v.
     LENGTH x = LENGTH y ==> ALOOKUP (ZIP x y) k = SOME v ==> MEM v y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  ASM_SIMP_TAC[MEM_ZIP; PAIR_EQ] THEN ASM_MESON_TAC[MEM_EL]);;

let get_vars_locals = prove
 (`!args (s:(A,C,FFI)wl_state) x y.
     wl_get_vars args s = SOME x /\ MEM y x
     ==> ?n. lookup n (wl_state_locals s) = SOME y`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wl_get_vars_def; option_INJ] THEN
  REPEAT GEN_TAC THEN TRY (CASES_ON `wl_get_var h (s:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[option_CASE; option_DISTINCT] THEN
    CASES_ON `wl_get_vars t (s:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def])) THEN
  DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th) THEN SUBST1_TAC(SYM(CONJUNCT1 th))) THEN
  REWRITE_TAC[MEM] THEN STRIP_TAC THENL
   [EXISTS_TAC `h:num` THEN ASM_REWRITE_TAC[]; ASM_MESON_TAC[]]);;

let get_vars_get_locals = prove
 (`!args (s:(A,C,FFI)wl_state) x n n1.
     wl_get_vars args s = SOME x /\ MEM (wl_Loc n n1) x
     ==> n IN domain (get_locals (wl_state_locals s))`,
  REWRITE_TAC[domain_get_locals_lookup] THEN MESON_TAC[get_vars_locals]);;

let get_locals_fromList2 = prove
 (`!args (s:(A,C,FFI)wl_state) x t.
     wl_get_vars args s = SOME x /\ ~(x = []) /\ t = fromList2 x
     ==> domain (get_locals t) SUBSET domain (get_locals (wl_state_locals s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET] THEN
  X_GEN_TAC `a:num` THEN REWRITE_TAC[domain_get_locals_lookup] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_TAC `n1:num`)) THEN
  SUBGOAL_THEN `MEM (wl_Loc a n1:(A)word_loc) x` ASSUME_TAC THENL
   [REWRITE_TAC[ISPECL [`wl_Loc a n1:(A)word_loc`; `x:((A)word_loc)list`]
                  fromList2_value] THEN ASM_MESON_TAC[];
    REWRITE_TAC[GSYM domain_get_locals_lookup] THEN
    ASM_MESON_TAC[get_vars_get_locals]]);;

let get_locals_fromList2_extension = prove
 (`!x (y:(A)word_loc) ys.
     x IN domain (get_locals (fromList2 ys))
     ==> x IN domain (get_locals (fromList2 (APPEND ys [y])))`,
  REWRITE_TAC[domain_get_locals_lookup] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_TAC `n1:num`)) THEN
  SUBGOAL_THEN `MEM (wl_Loc x n1:(A)word_loc) (APPEND ys [y])` MP_TAC THENL
   [REWRITE_TAC[MEM_APPEND] THEN DISJ1_TAC THEN
    REWRITE_TAC[ISPECL [`wl_Loc x n1:(A)word_loc`; `ys:((A)word_loc)list`]
                  fromList2_value] THEN ASM_MESON_TAC[];
    REWRITE_TAC[ISPECL [`wl_Loc x n1:(A)word_loc`; `APPEND ys [y:(A)word_loc]`]
                  fromList2_value] THEN MESON_TAC[]]);;

let get_locals_fromList2_FRONT = prove
 (`!args (s:(A,C,FFI)wl_state) x xf t.
     wl_get_vars args s = SOME x /\ ~(x = []) /\ xf = BUTLAST x /\
     t = fromList2 xf
     ==> domain (get_locals t) SUBSET domain (get_locals (wl_state_locals s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `domain (get_locals (fromList2 (x:((A)word_loc)list)))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[SUBSET] THEN X_GEN_TAC `a:num` THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV o
      RAND_CONV o RAND_CONV) [GSYM(MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
    REWRITE_TAC[get_locals_fromList2_extension];
    MATCH_MP_TAC get_locals_fromList2 THEN ASM_MESON_TAC[]]);;

let get_memory_write_bytearray_lemma = prove
 (`!(mem:A word->(A)word_loc) mdom (reachable:B spt) c r be.
     domain (get_memory mem mdom) SUBSET domain reachable
     ==> domain (get_memory (write_bytearray c r mem mdom be) mdom) SUBSET
         domain reachable`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[write_bytearray_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`word_add c (word 1):A word`; `be:bool`]) THEN
  ASM_REWRITE_TAC[mem_store_byte_aux_def] THEN
  CASES_ON `write_bytearray (word_add c (word 1)) t (mem:A word->(A)word_loc)
              mdom be (byte_align c)` THEN
  REWRITE_TAC[case_def "word_loc"] THEN ASM_REWRITE_TAC[option_CASE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_CASE] THEN DISCH_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC (CASE_TERM `domain (get_memory (write_bytearray (word_add c (word 1)) t
     (mem:A word->(A)word_loc) mdom be) mdom) UNION
     (match dest_word_loc (wl_Word (set_byte c h a be):(A)word_loc) with
        NONE -> {} | SOME n -> {n})`) THEN
  REWRITE_TAC[get_memory_update] THEN
  ASM_REWRITE_TAC[dest_word_loc_def; option_CASE; UNION_EMPTY]);;

let stack_list_rearrange_lemma = prove
 (`!(s:(A,C,FFI)wl_state) dr (locs:D spt) opt lsz.
     domain (get_locals (wl_state_locals s)) SUBSET dr /\
     domain (word_elimProof_get_stack (wl_state_stack s)) SUBSET dr
     ==> domain (word_elimProof_get_stack
           (CONS (StackFrame lsz (toAList (inter (wl_state_locals s) (n:B spt)))
                    (list_rearrange (wl_state_permute s 0)
                       (sort key_val_compare
                          (toAList (inter (wl_state_locals s) locs)))) opt)
                 (wl_state_stack s))) SUBSET dr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[word_elimProof_get_stack_def; domain_union; UNION_SUBSET] THEN
  REWRITE_TAC[SUBSET; GSYM get_num_wordloc_alist_thm; MEM_MAP;
              mem_list_rearrange; sort_MEM; EXISTS_PAIR_THM; MEM_toAList;
              lookup_inter_alt] THEN
  SUBGOAL_THEN `!k a n0. lookup k (wl_state_locals (s:(A,C,FFI)wl_state)) =
                          SOME (wl_Loc a n0) ==> a IN dr` ASSUME_TAC THENL
   [UNDISCH_TAC `domain (get_locals (wl_state_locals (s:(A,C,FFI)wl_state)))
                 SUBSET dr` THEN
    REWRITE_TAC[SUBSET; domain_get_locals_lookup] THEN MESON_TAC[];
    REWRITE_TAC[COND_CASE_EQ; option_DISTINCT] THEN ASM_MESON_TAC[]]);;

let remove_word_code_thm_FST = prove
 (`!n (reachable:1 spt) (l:(num#B)list).
     ALL_DISTINCT (MAP FST l)
     ==> (n IN domain reachable /\ MEM n (MAP FST l) <=>
          MEM n (MAP FST (remove_word_code reachable l)))`,
  REWRITE_TAC[remove_word_code_def; MEM_MAP; MEM_FILTER; domain_lookup;
              IS_SOME_EXISTS] THEN
  MESON_TAC[]);;

let remove_word_code_MAP_FST_lemma = prove
 (`!(reachable:1 spt) (l:(num#num#(A)wl_prog)list).
     MAP FST (FILTER (\x. IS_SOME (lookup (FST x) reachable)) l) =
     FILTER (\x. IS_SOME (lookup x reachable)) (MAP FST l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; MAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP]);;

(* ------------------------------------------------------------------------- *)
(* Word state rel                                                            *)
(* ------------------------------------------------------------------------- *)

(* the related states differ only in their code *)

let WELIMAUX_word_state_rel_code = prove
 (`!reachable (s:(A,C,FFI)wl_state) t.
     word_state_rel reachable s t
     ==> t = wl_state_code_fupd (K (wl_state_code t)) s`,
  REWRITE_TAC[word_state_rel_def; wl_state_component_equality] THEN
  REPEAT STRIP_TAC THEN SIMP[]);;

let word_state_rel_get_var = prove
 (`word_state_rel reachable (s:(A,C,FFI)wl_state) t
   ==> wl_get_var v t = wl_get_var v s`,
  SIMP[word_state_rel_def; wl_get_var_def]);;

let word_state_rel_get_store = prove
 (`word_state_rel reachable (s:(A,C,FFI)wl_state) t
   ==> wl_get_store v t = wl_get_store v s`,
  SIMP[word_state_rel_def; wl_get_store_def]);;

let word_state_rel_get_vars = prove
 (`word_state_rel reachable (s:(A,C,FFI)wl_state) t
   ==> wl_get_vars vs t = wl_get_vars vs s`,
  DISCH_TAC THEN SPEC_TAC(`vs:num list`,`vs:num list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[wl_get_vars_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP word_state_rel_get_var th]));;

let WELIMAUX_fls_set_var = prove
 (CASE_TERM
  `!n (v:(A)word_loc) (s:(A,C,FFI)wl_state).
     domain (find_loc_state (wl_set_var n v s)) SUBSET
     domain (find_loc_state s) UNION
     (match dest_word_loc v with NONE -> {} | SOME n -> {n})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[domain_find_loc_state; wl_set_var_def] THEN
  SIMP[] THEN
  MP_TAC(ISPECL [`n:num`; `v:(A)word_loc`; `wl_state_locals (s:(A,C,FFI)wl_state)`]
         get_locals_insert) THEN
  SET_TAC[]);;

let word_state_rel_set_var = prove
 (CASE_TERM
  `word_state_rel reachable (s:(A,C,FFI)wl_state) t /\
   (match dest_word_loc v with NONE -> {} | SOME n -> {n}) SUBSET
   domain reachable
   ==> word_state_rel reachable (wl_set_var n v s) (wl_set_var n v t)`,
  STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `v:(A)word_loc`; `s:(A,C,FFI)wl_state`]
         WELIMAUX_fls_set_var) THEN
  UNDISCH_TAC `word_state_rel reachable (s:(A,C,FFI)wl_state) t` THEN
  REWRITE_TAC[word_state_rel_def] THEN SIMP[wl_set_var_def] THEN
  REPEAT STRIP_TAC THEN ASM SET_TAC[]);;

(* TODO maybe depreciate? *)

let word_state_rel_set_var_word = prove
 (`word_state_rel reachable (s:(A,C,FFI)wl_state) t
   ==> word_state_rel reachable (wl_set_var n (wl_Word w) s)
                                (wl_set_var n (wl_Word w) t)`,
  DISCH_TAC THEN MATCH_MP_TAC word_state_rel_set_var THEN
  ASM_REWRITE_TAC[dest_word_loc_def; option_CASE; EMPTY_SUBSET]);;

let WELIMAUX_set_vars_nil = prove
 (`!(s:(A,C,FFI)wl_state) xs. wl_set_vars [] xs s = s`,
  REWRITE_TAC[wl_set_vars_def; alist_insert_def; wl_state_component_equality] THEN
  SIMP[]);;

let WELIMAUX_set_vars_cons = prove
 (`!v vs (x:(A)word_loc) xs (s:(A,C,FFI)wl_state).
     wl_set_vars (CONS v vs) (CONS x xs) s = wl_set_var v x (wl_set_vars vs xs s)`,
  REWRITE_TAC[wl_set_vars_def; wl_set_var_def; alist_insert_def] THEN SIMP[]);;

(* TODO add assum to prove it *)

let word_state_rel_set_vars = prove
 (CASE_TERM
  `word_state_rel reachable (s:(A,C,FFI)wl_state) t /\
   UNIONS (set_of_list
     (MAP (\x'. match dest_word_loc x' with NONE -> {} | SOME x -> {x})
          (l:((A)word_loc)list))) SUBSET domain reachable /\
   LENGTH (l0:num list) = LENGTH l
   ==> word_state_rel reachable (wl_set_vars l0 l s) (wl_set_vars l0 l t)`,
  SPEC_TAC(`l:((A)word_loc)list`,`l:((A)word_loc)list`) THEN
  SPEC_TAC(`l0:num list`,`l0:num list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; WELIMAUX_set_vars_nil] THEN
  REWRITE_TAC[WELIMAUX_set_vars_cons; MAP; set_of_list; UNIONS_INSERT;
              UNION_SUBSET] THEN
  STRIP_TAC THEN MATCH_MP_TAC word_state_rel_set_var THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* This can be strengthened to an equality *)

let word_state_rel_set_fp_var = prove
 (`word_state_rel reachable (s:(A,C,FFI)wl_state) t
   ==> word_state_rel reachable (wl_set_fp_var n v s) (wl_set_fp_var n v t)`,
  REWRITE_TAC[word_state_rel_def; wl_set_fp_var_def; domain_find_loc_state] THEN
  SIMP[]);;

let word_state_rel_word_exp = prove
 (`!(s1:(A,C,FFI)wl_state) exp s2 reachable.
     word_state_rel reachable s1 s2 ==> wl_word_exp s2 exp = wl_word_exp s1 exp`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP WELIMAUX_word_state_rel_code) THEN
  REWRITE_TAC[wl_word_exp_with_const]);;

let word_state_rel_mem_load = prove
 (`word_state_rel reachable (s:(A,C,FFI)wl_state) t
   ==> wl_mem_load addr t = wl_mem_load addr s`,
  SIMP[word_state_rel_def; wl_mem_load_def]);;

let word_state_rel_mem_load_32 = prove
 (`word_state_rel reachable (s:(A,C,FFI)wl_state) t
   ==> mem_load_32 (wl_state_memory s) (wl_state_mdomain s) (wl_state_be s) c =
       mem_load_32 (wl_state_memory t) (wl_state_mdomain t) (wl_state_be t) c`,
  SIMP[word_state_rel_def]);;

let word_state_rel_get_fp_var = prove
 (`word_state_rel reachable (s:(A,C,FFI)wl_state) t
   ==> wl_get_fp_var v s = wl_get_fp_var v t`,
  SIMP[word_state_rel_def; wl_get_fp_var_def]);;

let word_state_rel_assign_NONE = prove
 (`!reg exp (s:(A,C,FFI)wl_state) reachable t.
     word_state_rel reachable s t
     ==> (wl_assign reg exp s = NONE <=> wl_assign reg exp t = NONE)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP WELIMAUX_word_state_rel_code) THEN
  REWRITE_TAC[wl_assign_with_const; OPTION_MAP_EQ_NONE]);;

let word_state_rel_inst_NONE = prove
 (`!reachable (s:(A,C,FFI)wl_state) t i.
     word_state_rel reachable s t
     ==> (wl_inst i s = NONE <=> wl_inst i t = NONE)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP WELIMAUX_word_state_rel_code) THEN
  REWRITE_TAC[wl_inst_with_const; OPTION_MAP_EQ_NONE]);;

(* a state with the same code and fewer locations is related to its copy *)
(* with the code of t                                                     *)

let WELIMAUX_word_state_rel_step = prove
 (`!reachable (s:(A,C,FFI)wl_state) t (s1:(A,C,FFI)wl_state).
     word_state_rel reachable s t /\ wl_state_code s1 = wl_state_code s /\
     domain (find_loc_state s1) SUBSET domain (find_loc_state s)
     ==> word_state_rel reachable s1
           (wl_state_code_fupd (K (wl_state_code t)) s1)`,
  REWRITE_TAC[word_state_rel_def] THEN REPEAT STRIP_TAC THEN SIMP[] THEN
  ASM_MESON_TAC[SUBSET_TRANS]);;

let WELIMAUX_word_exp_fls = prove
 (`!(s:(A,C,FFI)wl_state) exp n n1.
     wl_word_exp s exp = SOME (wl_Loc n n1) ==> n IN domain (find_loc_state s)`,
  GEN_TAC THEN X_GEN_TAC `e:(A)wl_exp` THEN
  STRUCT_CASES_TAC (ISPEC `e:(A)wl_exp` (CONJUNCT1 (cases "wl_exp"))) THEN
  REWRITE_TAC[wl_word_exp_def; option_INJ; distinctness "word_loc";
              domain_find_loc_state; IN_UNION] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[option_case_eq; case_eq "word_loc"; OPTION_MAP_EQ_SOME;
     option_DISTINCT; option_INJ; distinctness "word_loc"; injectivity "word_loc";
     wl_get_var_def; wl_get_store_def; wl_mem_load_def; COND_CASE_EQ] THEN
  REWRITE_TAC[domain_get_locals_lookup; domain_get_store; domain_get_memory] THEN
  MESON_TAC[]);;

(* steps of a state that add no location to find_loc_state *)

let WELIMAUX_fls_set_var_word = prove
 (`!(s:(A,C,FFI)wl_state) (s1:(A,C,FFI)wl_state) n w.
     domain (find_loc_state s1) SUBSET domain (find_loc_state s)
     ==> domain (find_loc_state (wl_set_var n (wl_Word w) s1)) SUBSET
         domain (find_loc_state s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `domain (find_loc_state (s1:(A,C,FFI)wl_state))` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`n:num`; `wl_Word w:(A)word_loc`; `s1:(A,C,FFI)wl_state`]
         WELIMAUX_fls_set_var) THEN
  REWRITE_TAC[dest_word_loc_def; option_CASE; UNION_EMPTY]);;

let WELIMAUX_fls_set_fp_var = prove
 (`!(s:(A,C,FFI)wl_state) (s1:(A,C,FFI)wl_state) n v.
     domain (find_loc_state s1) SUBSET domain (find_loc_state s)
     ==> domain (find_loc_state (wl_set_fp_var n v s1)) SUBSET
         domain (find_loc_state s)`,
  REWRITE_TAC[domain_find_loc_state; wl_set_fp_var_def] THEN SIMP[]);;

let WELIMAUX_fls_set_var_loc = prove
 (`!(s:(A,C,FFI)wl_state) n v.
     (!a n1. v = wl_Loc a n1 ==> a IN domain (find_loc_state s))
     ==> domain (find_loc_state (wl_set_var n v s)) SUBSET
         domain (find_loc_state s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `v:(A)word_loc`; `s:(A,C,FFI)wl_state`]
         WELIMAUX_fls_set_var) THEN
  DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    (ISPEC `v:(A)word_loc` (cases "word_loc")) THEN
  REWRITE_TAC[dest_word_loc_def; option_CASE; UNION_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a0:num`; `a1:num`]) THEN
  REWRITE_TAC[] THEN SET_TAC[]);;

let WELIMAUX_fls_memory_word = prove
 (`!(s:(A,C,FFI)wl_state) a w.
     domain (find_loc_state
       (wl_state_memory_fupd (K ((a =+ wl_Word w) (wl_state_memory s))) s))
     SUBSET domain (find_loc_state s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[domain_find_loc_state] THEN SIMP[] THEN
  MP_TAC(ISPECL [`a:A word`; `wl_Word w:(A)word_loc`;
                 `wl_state_memory (s:(A,C,FFI)wl_state)`;
                 `wl_state_mdomain (s:(A,C,FFI)wl_state)`] get_memory_update) THEN
  REWRITE_TAC[dest_word_loc_def; option_CASE; UNION_EMPTY] THEN SET_TAC[]);;

let WELIMAUX_mem_store_byte_aux_word = prove
 (`!(m:A word->(A)word_loc) dm be a b m'.
     mem_store_byte_aux m dm be a b = SOME m' ==> ?x w. m' = (x =+ wl_Word w) m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mem_store_byte_aux_def] THEN
  CASES_ON `(m:A word->(A)word_loc) (byte_align a)` THEN
  REWRITE_TAC[case_def "word_loc"; option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

let WELIMAUX_mem_store_32_word = prove
 (`!(m:A word->(A)word_loc) dm be a hw m'.
     mem_store_32 m dm be a hw = SOME m' ==> ?x w. m' = (x =+ wl_Word w) m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mem_store_32_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `(m:A word->(A)word_loc) (byte_align a)` THEN
  REWRITE_TAC[case_def "word_loc"; option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[option_INJ] THEN
  MESON_TAC[]);;

let WELIMAUX_assign_fls = prove
 (`!reg exp (s:(A,C,FFI)wl_state) s1.
     wl_assign reg exp s = SOME s1
     ==> domain (find_loc_state s1) SUBSET domain (find_loc_state s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_assign_def] THEN
  CASES_ON `wl_word_exp (s:(A,C,FFI)wl_state) exp` THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC WELIMAUX_fls_set_var_loc THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_MESON_TAC[WELIMAUX_word_exp_fls]);;

let word_state_rel_assign_SOME = prove
 (`word_state_rel reachable (s:(A,C,FFI)wl_state) t
   ==> (wl_assign reg exp s = SOME s1 /\ wl_assign reg exp t = SOME t1
        ==> word_state_rel reachable s1 t1)`,
  DISCH_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP WELIMAUX_word_state_rel_code th]) THEN
  REWRITE_TAC[wl_assign_with_const] THEN STRIP_TAC THEN
  UNDISCH_TAC `OPTION_MAP (\s:(A,C,FFI)wl_state.
                 wl_state_code_fupd (K (wl_state_code (t:(A,C,FFI)wl_state))) s)
               (wl_assign reg exp s) = SOME t1` THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC WELIMAUX_word_state_rel_step THEN
  EXISTS_TAC `s:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[assign_const_full; WELIMAUX_assign_fls]);;

let WELIMAUX_get_var_fls = prove
 (`!r (s:(A,C,FFI)wl_state) n n1.
     wl_get_var r s = SOME (wl_Loc n n1) ==> n IN domain (find_loc_state s)`,
  REWRITE_TAC[wl_get_var_def; domain_find_loc_state; IN_UNION;
              domain_get_locals_lookup] THEN MESON_TAC[]);;

let WELIMAUX_mem_load_fls = prove
 (`!a (s:(A,C,FFI)wl_state) n n1.
     wl_mem_load a s = SOME (wl_Loc n n1) ==> n IN domain (find_loc_state s)`,
  REWRITE_TAC[wl_mem_load_def; COND_CASE_EQ; option_DISTINCT; option_INJ;
              domain_find_loc_state; IN_UNION; domain_get_memory] THEN
  MESON_TAC[]);;

let WELIMAUX_mem_store_fls = prove
 (`!a (w:(A)word_loc) (s:(A,C,FFI)wl_state) s1.
     wl_mem_store a w s = SOME s1
     ==> (!n n1. w = wl_Loc n n1 ==> n IN domain (find_loc_state s))
     ==> domain (find_loc_state s1) SUBSET domain (find_loc_state s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_mem_store_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    (ISPEC `w:(A)word_loc` (cases "word_loc")) THEN
  REWRITE_TAC[WELIMAUX_fls_memory_word; injectivity "word_loc";
              distinctness "word_loc"] THEN
  DISCH_THEN(MP_TAC o SPECL [`a0:num`; `a1:num`]) THEN REWRITE_TAC[] THEN
  REWRITE_TAC[domain_find_loc_state] THEN SIMP[] THEN
  MP_TAC(ISPECL [`a:A word`; `wl_Loc a0 a1:(A)word_loc`;
                 `wl_state_memory (s:(A,C,FFI)wl_state)`;
                 `wl_state_mdomain (s:(A,C,FFI)wl_state)`] get_memory_update) THEN
  REWRITE_TAC[dest_word_loc_def; option_CASE] THEN SET_TAC[]);;

let WELIMAUX_mem_store_byte_fls = prove
 (`!(s:(A,C,FFI)wl_state) be a b m'.
     mem_store_byte_aux (wl_state_memory s) (wl_state_mdomain s) be a b = SOME m'
     ==> domain (find_loc_state (wl_state_memory_fupd (K m') s)) SUBSET
         domain (find_loc_state s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A word` (X_CHOOSE_THEN `w:A word` SUBST1_TAC) o
             MATCH_MP WELIMAUX_mem_store_byte_aux_word) THEN
  REWRITE_TAC[WELIMAUX_fls_memory_word]);;

let WELIMAUX_mem_store_32_fls = prove
 (`!(s:(A,C,FFI)wl_state) be a hw m'.
     mem_store_32 (wl_state_memory s) (wl_state_mdomain s) be a hw = SOME m'
     ==> domain (find_loc_state (wl_state_memory_fupd (K m') s)) SUBSET
         domain (find_loc_state s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A word` (X_CHOOSE_THEN `w:A word` SUBST1_TAC) o
             MATCH_MP WELIMAUX_mem_store_32_word) THEN
  REWRITE_TAC[WELIMAUX_fls_memory_word]);;

let WELIMAUX_INST_FLS_TAC : tactic =
  FIRST
   [REPEAT (MATCH_MP_TAC WELIMAUX_fls_set_var_word ORELSE
            MATCH_MP_TAC WELIMAUX_fls_set_fp_var) THEN
    REWRITE_TAC[SUBSET_REFL] THEN NO_TAC;
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP WELIMAUX_assign_fls);
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP WELIMAUX_mem_store_byte_fls);
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP WELIMAUX_mem_store_32_fls);
    MATCH_MP_TAC WELIMAUX_fls_set_var_loc THEN
    ASM_MESON_TAC[WELIMAUX_mem_load_fls] THEN NO_TAC;
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WELIMAUX_mem_store_fls) THEN
    ASM_MESON_TAC[WELIMAUX_get_var_fls]];;

let WELIMAUX_inst_fls = prove
 (`!i (s:(A,C,FFI)wl_state) s1.
     wl_inst i s = SOME s1
     ==> domain (find_loc_state s1) SUBSET domain (find_loc_state s)`,
  GEN_TAC THEN IL2AUX_INST_SPLIT_TAC THEN REPEAT GEN_TAC THEN
  SIMP[wl_inst_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  EVERY_CASE_TAC THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN
  DISCH_THEN(fun th -> if is_var(rhs(concl th)) then SUBST1_TAC(SYM th)
                       else ASSUME_TAC th) THEN
  WELIMAUX_INST_FLS_TAC);;

let word_state_rel_inst_SOME = prove
 (`!reachable (s:(A,C,FFI)wl_state) t i s1 t1.
     word_state_rel reachable s t
     ==> (wl_inst i s = SOME s1 /\ wl_inst i t = SOME t1
          ==> word_state_rel reachable s1 t1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP WELIMAUX_word_state_rel_code th]) THEN
  REWRITE_TAC[wl_inst_with_const] THEN STRIP_TAC THEN
  UNDISCH_TAC `OPTION_MAP (\s:(A,C,FFI)wl_state.
                 wl_state_code_fupd (K (wl_state_code (t:(A,C,FFI)wl_state))) s)
               (wl_inst i s) = SOME t1` THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC WELIMAUX_word_state_rel_step THEN
  EXISTS_TAC `s:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[inst_const_full; WELIMAUX_inst_fls]);;

let WELIMAUX_frame_lemma = prove
 (`!stack lsz (l:(num#(A)word_loc)list) l0 opt t.
     stack = CONS (StackFrame lsz l l0 opt) t
     ==> domain (get_locals (union (fromAList l0) (fromAList l))) SUBSET
         domain (word_elimProof_get_stack stack) /\
         domain (word_elimProof_get_stack t) SUBSET
         domain (word_elimProof_get_stack stack)`,
  MESON_TAC[get_stack_hd_thm; SUBSET_REFL]);;

let WELIMAUX_pop_env_fls = prove
 (`!(s:(A,C,FFI)wl_state) s1.
     wl_pop_env s = SOME s1
     ==> domain (find_loc_state s1) SUBSET domain (find_loc_state s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_pop_env_def] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WELIMAUX_frame_lemma) THEN
  REWRITE_TAC[domain_find_loc_state] THEN SIMP[] THEN SET_TAC[]);;

let word_state_rel_pop_env_NONE = prove
 (`!reachable (s:(A,C,FFI)wl_state) t.
     word_state_rel reachable s t
     ==> (wl_pop_env s = NONE <=> wl_pop_env t = NONE)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP WELIMAUX_word_state_rel_code) THEN
  REWRITE_TAC[wl_pop_env_with_const; OPTION_MAP_EQ_NONE]);;

let word_state_rel_pop_env = prove
 (`!reachable (s:(A,C,FFI)wl_state) t s1 (l1:B) (l2:D).
     word_state_rel reachable s t
     ==> wl_pop_env s = SOME s1
     ==> ?t1. wl_pop_env t = SOME t1 /\ word_state_rel reachable s1 t1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP WELIMAUX_word_state_rel_code th]) THEN
  ASM_REWRITE_TAC[wl_pop_env_with_const; OPTION_MAP_DEF; option_INJ] THEN
  REWRITE_TAC[UNWIND_THM1] THEN
  MATCH_MP_TAC WELIMAUX_word_state_rel_step THEN
  EXISTS_TAC `s:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[wl_pop_env_const; WELIMAUX_pop_env_fls]);;

let WELIMAUX_jump_exc_fls = prove
 (`!(s:(A,C,FFI)wl_state) s1 l1 l2.
     wl_jump_exc s = SOME (s1,l1,l2)
     ==> domain (find_loc_state s1) SUBSET domain (find_loc_state s) /\
         wl_state_code s1 = wl_state_code s /\
         !c. wl_jump_exc (wl_state_code_fupd (K c) s) =
             SOME (wl_state_code_fupd (K c) s1,l1,l2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_jump_exc_def] THEN SIMP[] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN SIMP[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WELIMAUX_frame_lemma) THEN
  MP_TAC(ISPECL [`wl_state_stack (s:(A,C,FFI)wl_state)`;
                 `wl_state_handler (s:(A,C,FFI)wl_state) + 1`] get_stack_LASTN) THEN
  REWRITE_TAC[domain_find_loc_state] THEN SIMP[] THEN SET_TAC[]);;

let word_state_rel_jump_exc = prove
 (`!reachable (s:(A,C,FFI)wl_state) t s1 l1 l2.
     word_state_rel reachable s t
     ==> wl_jump_exc s = SOME (s1,l1,l2)
     ==> ?t1. wl_jump_exc t = SOME (t1,l1,l2) /\ word_state_rel reachable s1 t1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_jump_exc_fls) THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP WELIMAUX_word_state_rel_code th]) THEN
  ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN REWRITE_TAC[UNWIND_THM1] THEN
  MATCH_MP_TAC WELIMAUX_word_state_rel_step THEN
  EXISTS_TAC `s:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[]);;

let WELIMAUX_gc_fls = prove
 (`!(s:(A,C,FFI)wl_state) s1.
     gc_no_new_locs (wl_state_gc_fun s) /\ wl_gc s = SOME s1
     ==> domain (find_loc_state s1) SUBSET domain (find_loc_state s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_gc_def; LET_DEF; LET_END_DEF] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  REWRITE_TAC[gc_no_new_locs_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> FIRST_ASSUM(MP_TAC o
      MATCH_MP (REWRITE_RULE[IMP_CONJ] th))) (SUBST1_TAC o SYM)) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[domain_find_loc_state] THEN SIMP[] THEN SET_TAC[]);;

let word_state_rel_gc = prove
 (`!reachable (s:(A,C,FFI)wl_state) t s1.
     word_state_rel reachable s t /\ gc_no_new_locs (wl_state_gc_fun s)
     ==> wl_gc s = SOME s1
     ==> ?t1. wl_gc t = SOME t1 /\ word_state_rel reachable s1 t1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP WELIMAUX_word_state_rel_code th]) THEN
  ASM_REWRITE_TAC[wl_gc_with_const; OPTION_MAP_DEF; option_INJ] THEN
  REWRITE_TAC[UNWIND_THM1] THEN
  MATCH_MP_TAC WELIMAUX_word_state_rel_step THEN
  EXISTS_TAC `s:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[IL2AUX_gc_all; WELIMAUX_gc_fls]);;

let WELIMAUX_push_frame = prove
 (`!(s:(A,C,FFI)wl_state) (n:B spt) (locs:D spt) opt lsz.
     domain (word_elimProof_get_stack
       (CONS (StackFrame lsz (toAList (inter (wl_state_locals s) n))
                (list_rearrange (wl_state_permute s 0)
                   (sort key_val_compare
                      (toAList (inter (wl_state_locals s) locs)))) opt)
             (wl_state_stack s))) SUBSET domain (find_loc_state s)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC (GEN `n:B spt` stack_list_rearrange_lemma) THEN
  REWRITE_TAC[domain_find_loc_state] THEN SET_TAC[]);;

let WELIMAUX_push_env_fls = prove
 (`!names envs h (s:(A,C,FFI)wl_state).
     cut_envs names (wl_state_locals s) = SOME envs
     ==> domain (find_loc_state (wl_push_env envs h s)) SUBSET
         domain (find_loc_state s) /\
         wl_state_gc_fun (wl_push_env envs h s) = wl_state_gc_fun s /\
         wl_state_code (wl_push_env envs h s) = wl_state_code s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_envs_def; cut_names_def] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SPEC_TAC(`h:(num#(A)wl_prog#num#num)option`,`h:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def; env_to_list_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[domain_find_loc_state] THEN SIMP[] THEN
  REWRITE_TAC[GSYM domain_find_loc_state; WELIMAUX_push_frame] THEN
  REWRITE_TAC[domain_find_loc_state] THEN SET_TAC[]);;

let WELIMAUX_fls_set_store_word = prove
 (`!v w (s:(A,C,FFI)wl_state).
     domain (find_loc_state (wl_set_store v (wl_Word w) s)) SUBSET
     domain (find_loc_state s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[domain_find_loc_state; wl_set_store_def] THEN
  SIMP[] THEN
  MP_TAC(ISPECL [`wl_state_store (s:(A,C,FFI)wl_state)`; `v:store_name`;
                 `wl_Word w:(A)word_loc`] get_store_update) THEN
  REWRITE_TAC[dest_word_loc_def; option_CASE; UNION_EMPTY] THEN SET_TAC[]);;

let WELIMAUX_fls_flush = prove
 (`!b (s:(A,C,FFI)wl_state).
     domain (find_loc_state (wl_flush_state b s)) SUBSET
     domain (find_loc_state s)`,
  MATCH_MP_TAC bool_INDUCT THEN
  REWRITE_TAC[domain_find_loc_state; wl_flush_state_def] THEN SIMP[] THEN
  REWRITE_TAC[get_locals_def; word_elimProof_get_stack_def; domain_def;
    word_elimProof_get_store_def; LET_DEF; LET_END_DEF; FRANGE_FEMPTY;
    LIST_OF_SET_EMPTY; MAP; FILTER; FOLDL] THEN
  SET_TAC[]);;

let WELIMAUX_fls_flush_sub = prove
 (`!b (x:(A,C,FFI)wl_state) t.
     domain (find_loc_state x) SUBSET t
     ==> domain (find_loc_state (wl_flush_state b x)) SUBSET t`,
  MESON_TAC[WELIMAUX_fls_flush; SUBSET_TRANS]);;

let WELIMAUX_alloc_chain = prove
 (`!names envs (s:(A,C,FFI)wl_state) c s2 s3.
     gc_no_new_locs (wl_state_gc_fun s) /\
     cut_envs names (wl_state_locals s) = SOME envs /\
     wl_gc (wl_push_env envs NONE (wl_set_store AllocSize (wl_Word c) s)) = SOME s2 /\
     wl_pop_env s2 = SOME s3
     ==> domain (find_loc_state s3) SUBSET domain (find_loc_state s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`names:cutsets`; `envs:((A)word_loc)spt#((A)word_loc)spt`;
                 `NONE:(num#(A)wl_prog#num#num)option`;
                 `wl_set_store AllocSize (wl_Word c) (s:(A,C,FFI)wl_state)`]
         WELIMAUX_push_env_fls) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[wl_set_store_def] THEN SIMP[]; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`wl_push_env envs NONE (wl_set_store AllocSize (wl_Word c)
                    (s:(A,C,FFI)wl_state))`; `s2:(A,C,FFI)wl_state`]
         WELIMAUX_gc_fls) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[wl_set_store_def] THEN SIMP[] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s2:(A,C,FFI)wl_state`; `s3:(A,C,FFI)wl_state`]
         WELIMAUX_pop_env_fls) THEN
  MP_TAC(ISPECL [`AllocSize`; `c:A word`; `s:(A,C,FFI)wl_state`]
         WELIMAUX_fls_set_store_word) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_TRANS]);;

let WELIMAUX_alloc_fls = prove
 (`!c names (s:(A,C,FFI)wl_state) res s1.
     gc_no_new_locs (wl_state_gc_fun s) /\ wl_alloc c names s = (res,s1) /\
     ~(res = SOME wl_Error)
     ==> domain (find_loc_state s1) SUBSET domain (find_loc_state s) /\
         (res = NONE \/ res = SOME NotEnoughSpace)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_alloc_def] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ; option_INJ; option_DISTINCT;
    distinctness "wl_result"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; distinctness "wl_result"]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN ASM_REWRITE_TAC[] THEN
  TRY (MATCH_MP_TAC WELIMAUX_fls_flush_sub) THEN
  MATCH_MP_TAC WELIMAUX_alloc_chain THEN ASM_MESON_TAC[]);;

let word_state_rel_alloc = prove
 (`!reachable (s:(A,C,FFI)wl_state) t res c n s1.
     word_state_rel reachable s t /\ ~(res = SOME wl_Error) /\
     gc_no_new_locs (wl_state_gc_fun s)
     ==> wl_alloc c n s = (res,s1)
     ==> ?t1. wl_alloc c n t = (res,t1) /\ word_state_rel reachable s1 t1 /\
              dest_result_loc res SUBSET domain reachable`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:A word`; `n:cutsets`; `s:(A,C,FFI)wl_state`;
                 `res:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`]
         WELIMAUX_alloc_fls) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP WELIMAUX_word_state_rel_code th]) THEN
  ASM_REWRITE_TAC[wl_alloc_with_const; PAIR_MAP_THM; I_THM; PAIR_EQ] THEN
  REWRITE_TAC[UNWIND_THM1] THEN
  ASM_REWRITE_TAC[dest_result_loc_def; EMPTY_SUBSET] THEN
  MATCH_MP_TAC WELIMAUX_word_state_rel_step THEN
  EXISTS_TAC `s:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[wl_alloc_const]);;

let const_writes_eq_Loc = prove
 (`!words (a:A word) c m k l1 l2.
     const_writes a c words m k = wl_Loc l1 l2 ==> m k = wl_Loc l1 l2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[const_writes_def] THEN
  SPEC_TAC(`h:bool#A word`,`h:bool#A word`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; const_writes_def] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[APPLY_UPDATE_THM] THEN COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "word_loc"]);;

(* TODO move *)

let push_env_def2 = prove
 (CASE_TERM
  `wl_push_env env handler (s:(A,C,FFI)wl_state) =
     let l0 = toAList (FST env) in
     let (l,permute) = env_to_list (SND env) (wl_state_permute s) in
     let handler = (match handler with
                      NONE -> NONE
                    | SOME (w,h,l1,l2) -> SOME (wl_state_handler s,l1,l2)) in
     let stack = CONS (StackFrame (wl_state_locals_size s) l0 l handler)
                      (wl_state_stack s) in
       wl_state_stack_fupd (K stack)
        (wl_state_stack_max_fupd
           (K (OPTION_MAP2 MAX (wl_state_stack_max s) (wl_stack_size stack)))
         (wl_state_permute_fupd (K permute)
          (wl_state_handler_fupd
             (K (match handler with
                   NONE -> wl_state_handler s
                 | SOME x -> LENGTH (wl_state_stack s))) s)))`,
  SPEC_TAC(`handler:(num#(A)wl_prog#num#num)option`,
           `handler:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def;
              env_to_list_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[] THEN
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;

(* ------------------------------------------------------------------------- *)
(* Main lemmas                                                               *)
(* ------------------------------------------------------------------------- *)

(* HOL4 [local] *)

let get_locals_inter_subset = prove
 (`domain (get_locals (inter (a:((A)word_loc)spt) (b:B spt))) SUBSET
   domain (get_locals a)`,
  REWRITE_TAC[SUBSET; domain_get_locals_lookup; lookup_inter_alt] THEN
  REWRITE_TAC[COND_CASE_EQ; option_DISTINCT] THEN MESON_TAC[]);;

(* the evaluation of a statement that does not look at the code commutes  *)
(* with replacing the code (helpers of word_removal_lemma)                 *)

let WELIMAUX_flush_code = prove
 (`!b c (s:(A,C,FFI)wl_state).
     wl_flush_state b (wl_state_code_fupd (K c) s) =
     wl_state_code_fupd (K c) (wl_flush_state b s)`,
  MATCH_MP_TAC bool_INDUCT THEN REWRITE_TAC[wl_flush_state_def] THEN SIMP[]);;

let WELIMAUX_jump_exc_code = prove
 (CASE_TERM
  `!c (s:(A,C,FFI)wl_state).
     wl_jump_exc (wl_state_code_fupd (K c) s) =
     match wl_jump_exc s with
       NONE -> NONE
     | SOME (s1,l1,l2) -> SOME (wl_state_code_fupd (K c) s1,l1,l2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_jump_exc_def] THEN SIMP[] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[]));;

let WELIMAUX_sh_mem_set_var_code = prove
 (`!r v c (s:(A,C,FFI)wl_state).
     sh_mem_set_var r v (wl_state_code_fupd (K c) s) =
     (I ## wl_state_code_fupd (K c)) (sh_mem_set_var r v s):((A)wl_result)option#(A,C,FFI)wl_state`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `r:((FFI)ffi_result)option` (cases "option")) THEN
  TRY (STRUCT_CASES_TAC (ISPEC `a:(FFI)ffi_result` (cases "ffi_result"))) THEN
  SIMP[sh_mem_set_var_def; WELIMAUX_flush_code; PAIR_MAP_THM; I_THM]);;

let WELIMAUX_share_inst_code = prove
 (`!op v ad c (s:(A,C,FFI)wl_state).
     share_inst op v ad (wl_state_code_fupd (K c) s) =
     (I ## wl_state_code_fupd (K c)) (share_inst op v ad s):((A)wl_result)option#(A,C,FFI)wl_state`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  REWRITE_TAC[share_inst_def; wl_sh_mem_load_def; wl_sh_mem_load_byte_def;
    wl_sh_mem_load16_def; wl_sh_mem_load32_def; wl_sh_mem_store_def;
    wl_sh_mem_store_byte_def; wl_sh_mem_store16_def; wl_sh_mem_store32_def;
    wl_get_var_def] THEN
  SIMP[WELIMAUX_sh_mem_set_var_code] THEN REPEAT (TOP_CASE_TAC THEN
    SIMP[sh_mem_set_var_def; WELIMAUX_flush_code; WELIMAUX_sh_mem_set_var_code;
         PAIR_MAP_THM; I_THM]));;

let WELIMAUX_code_eta = prove
 (`!c. (\s:(A,C,FFI)wl_state. wl_state_code_fupd (K c) s) = wl_state_code_fupd (K c)`,
  REWRITE_TAC[ETA_AX]);;

let WELIMAUX_EVAL_CODE_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN
  SIMP[WELIMAUX_flush_code; WELIMAUX_share_inst_code; WELIMAUX_jump_exc_code;
       PAIR_MAP_THM; I_THM; WELIMAUX_code_eta; wl_dec_clock_def] THEN
  REPEAT (TOP_CASE_TAC THEN
    FS[WELIMAUX_flush_code; WELIMAUX_share_inst_code; WELIMAUX_jump_exc_code;
       PAIR_MAP_THM; I_THM; WELIMAUX_code_eta; wl_dec_clock_def]);;

(* the statements that do not depend on the code: every one but Call,     *)
(* LocValue, Install and the compound ones                                 *)

let WELIMAUX_evaluate_code =
  let tmpl = `!c (s:(A,C,FFI)wl_state).
     wl_evaluate (p:(A)wl_prog, wl_state_code_fupd (K c) s) =
     (I ## wl_state_code_fupd (K c)) (wl_evaluate (p, s))` in
  let stmt pat = list_mk_forall(frees pat, vsubst [pat,`p:(A)wl_prog`] tmpl) in
  let pats =
    [`wl_Skip:(A)wl_prog`; `wl_Alloc n names:(A)wl_prog`;
     `wl_StoreConsts t1 t2 addr offset words:(A)wl_prog`;
     `wl_Move pri moves:(A)wl_prog`; `wl_Inst i:(A)wl_prog`;
     `wl_Assign v exp:(A)wl_prog`; `wl_Get v name:(A)wl_prog`;
     `wl_Set v exp:(A)wl_prog`; `wl_OpCurrHeap b dst src:(A)wl_prog`;
     `wl_Store exp v:(A)wl_prog`; `wl_Tick:(A)wl_prog`;
     `wl_Return n ms:(A)wl_prog`; `wl_Raise n:(A)wl_prog`;
     `wl_Break k:(A)wl_prog`; `wl_Continue k:(A)wl_prog`;
     `wl_CodeBufferWrite r1 r2:(A)wl_prog`; `wl_DataBufferWrite r1 r2:(A)wl_prog`;
     `wl_FFI ffi_index ptr1 len1 ptr2 len2 names:(A)wl_prog`;
     `ShareInst op v exp:(A)wl_prog`] in
  end_itlist CONJ (map (fun pat -> prove(stmt pat, WELIMAUX_EVAL_CODE_TAC)) pats);;

(* more steps that add no location to find_loc_state *)

let WELIMAUX_get_store_fls = prove
 (`!name (s:(A,C,FFI)wl_state) n n1.
     wl_get_store name s = SOME (wl_Loc n n1) ==> n IN domain (find_loc_state s)`,
  REWRITE_TAC[wl_get_store_def; domain_find_loc_state; IN_UNION;
              domain_get_store] THEN MESON_TAC[]);;

let WELIMAUX_fls_unset_var = prove
 (`!v (s:(A,C,FFI)wl_state) t.
     domain (find_loc_state s) SUBSET t
     ==> domain (find_loc_state (wl_unset_var v s)) SUBSET t`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUBSET_TRANS) THEN
  SUBGOAL_THEN `domain (get_locals (delete v (wl_state_locals (s:(A,C,FFI)wl_state))))
                SUBSET domain (get_locals (wl_state_locals s))` MP_TAC THENL
   [REWRITE_TAC[SUBSET; domain_get_locals_lookup; lookup_delete] THEN
    REWRITE_TAC[COND_CASE_EQ; option_DISTINCT] THEN MESON_TAC[];
    REWRITE_TAC[domain_find_loc_state; wl_unset_var_def] THEN SIMP[] THEN
    SET_TAC[]]);;

let WELIMAUX_fls_const_writes = prove
 (`!a off words (s:(A,C,FFI)wl_state).
     domain (find_loc_state (wl_state_memory_fupd
       (K (const_writes a off words (wl_state_memory s))) s)) SUBSET
     domain (find_loc_state s)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `domain (get_memory (const_writes a off words
                  (wl_state_memory (s:(A,C,FFI)wl_state))) (wl_state_mdomain s))
                SUBSET domain (get_memory (wl_state_memory s) (wl_state_mdomain s))`
    MP_TAC THENL
   [REWRITE_TAC[SUBSET; domain_get_memory] THEN MESON_TAC[const_writes_eq_Loc];
    REWRITE_TAC[domain_find_loc_state] THEN SIMP[] THEN SET_TAC[]]);;

let WELIMAUX_fls_set_vars = prove
 (`!ks vs (s:(A,C,FFI)wl_state).
     (!n n1. MEM (wl_Loc n n1) vs ==> n IN domain (find_loc_state s))
     ==> domain (find_loc_state (wl_set_vars ks vs s)) SUBSET
         domain (find_loc_state s)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[WELIMAUX_set_vars_nil; SUBSET_REFL] THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[wl_set_vars_def; alist_insert_def] THEN
    REWRITE_TAC[domain_find_loc_state] THEN SIMP[] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[WELIMAUX_set_vars_cons; MEM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC (CASE_TERM `domain (find_loc_state (wl_set_vars t t' (s:(A,C,FFI)wl_state)))
    UNION (match dest_word_loc (h':(A)word_loc) with NONE -> {} | SOME n -> {n})`) THEN
  REWRITE_TAC[WELIMAUX_fls_set_var] THEN
  REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    (ISPEC `h':(A)word_loc` (cases "word_loc")) THEN
  REWRITE_TAC[dest_word_loc_def; option_CASE; EMPTY_SUBSET; SING_SUBSET] THEN
  ASM_MESON_TAC[]);;

let WELIMAUX_fls_set_store = prove
 (`!v (w:(A)word_loc) (s:(A,C,FFI)wl_state).
     (!n n1. w = wl_Loc n n1 ==> n IN domain (find_loc_state s))
     ==> domain (find_loc_state (wl_set_store v w s)) SUBSET
         domain (find_loc_state s)`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    (ISPEC `w:(A)word_loc` (cases "word_loc")) THEN
  REWRITE_TAC[WELIMAUX_fls_set_store_word; injectivity "word_loc"] THEN
  DISCH_THEN(MP_TAC o SPECL [`a0:num`; `a1:num`]) THEN REWRITE_TAC[] THEN
  REWRITE_TAC[domain_find_loc_state; wl_set_store_def] THEN SIMP[] THEN
  MP_TAC(ISPECL [`wl_state_store (s:(A,C,FFI)wl_state)`; `v:store_name`;
                 `wl_Loc a0 a1:(A)word_loc`] get_store_update) THEN
  REWRITE_TAC[dest_word_loc_def; option_CASE] THEN SET_TAC[]);;

(* location safety of the statements that do not depend on the code: the *)
(* locations of the result and of the final state are reachable           *)

let WELIMAUX_safe_stmt =
  let tmpl = `!(s:(A,C,FFI)wl_state) result new_state (reachable:1 spt).
     wl_evaluate (p:(A)wl_prog, s) = (result,new_state) /\
     ~(result = SOME wl_Error) /\
     domain (find_loc_state s) SUBSET domain reachable /\
     gc_no_new_locs (wl_state_gc_fun s) /\
     domain (find_word_ref p) SUBSET domain reachable
     ==> domain (find_loc_state new_state) SUBSET domain reachable /\
         dest_result_loc result SUBSET domain reachable` in
  fun pat -> list_mk_forall(frees pat, vsubst [pat,`p:(A)wl_prog`] tmpl);;

let WELIMAUX_SAFE_PRE_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[wl_case_eq_thms; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; injectivity "word_loc";
    distinctness "wl_result"; distinctness "option"]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  ASM_REWRITE_TAC[dest_result_loc_def; EMPTY_SUBSET];;

(* close domain (find_loc_state X) SUBSET domain reachable through        *)
(* domain (find_loc_state s) SUBSET domain reachable                       *)

let WELIMAUX_VIA_S_TAC : tactic =
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `domain (find_loc_state (s:(A,C,FFI)wl_state))` THEN
  ASM_REWRITE_TAC[];;

let WELIMAUX_safe_Skip = prove
 (WELIMAUX_safe_stmt `wl_Skip:(A)wl_prog`, WELIMAUX_SAFE_PRE_TAC);;

let WELIMAUX_safe_Alloc = prove
 (WELIMAUX_safe_stmt `wl_Alloc n names:(A)wl_prog`,
  WELIMAUX_SAFE_PRE_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WELIMAUX_alloc_fls o
    CONJ (ASSUME `gc_no_new_locs (wl_state_gc_fun (s:(A,C,FFI)wl_state))`) o
    C CONJ (ASSUME `~(result = SOME (wl_Error:(A)wl_result))`) o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_alloc"
                     with Failure _ -> false)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[dest_result_loc_def; EMPTY_SUBSET] THEN
  ASM_MESON_TAC[SUBSET_TRANS]);;

let WELIMAUX_safe_StoreConsts = prove
 (WELIMAUX_safe_stmt `wl_StoreConsts t1 t2 addr offset words:(A)wl_prog`,
  WELIMAUX_SAFE_PRE_TAC THEN WELIMAUX_VIA_S_TAC THEN
  REPEAT (MATCH_MP_TAC WELIMAUX_fls_set_var_word ORELSE
          MATCH_MP_TAC WELIMAUX_fls_unset_var) THEN
  REWRITE_TAC[WELIMAUX_fls_const_writes]);;

let WELIMAUX_safe_Move = prove
 (WELIMAUX_safe_stmt `wl_Move pri moves:(A)wl_prog`,
  WELIMAUX_SAFE_PRE_TAC THEN WELIMAUX_VIA_S_TAC THEN
  MATCH_MP_TAC WELIMAUX_fls_set_vars THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[domain_find_loc_state; IN_UNION] THEN
  ASM_MESON_TAC[get_vars_get_locals]);;

let WELIMAUX_safe_Inst = prove
 (WELIMAUX_safe_stmt `wl_Inst i:(A)wl_prog`,
  WELIMAUX_SAFE_PRE_TAC THEN WELIMAUX_VIA_S_TAC THEN
  ASM_MESON_TAC[WELIMAUX_inst_fls]);;

let WELIMAUX_safe_Assign = prove
 (WELIMAUX_safe_stmt `wl_Assign v exp:(A)wl_prog`,
  WELIMAUX_SAFE_PRE_TAC THEN WELIMAUX_VIA_S_TAC THEN
  MATCH_MP_TAC WELIMAUX_fls_set_var_loc THEN
  ASM_MESON_TAC[WELIMAUX_word_exp_fls]);;

let WELIMAUX_safe_Get = prove
 (WELIMAUX_safe_stmt `wl_Get v name:(A)wl_prog`,
  WELIMAUX_SAFE_PRE_TAC THEN WELIMAUX_VIA_S_TAC THEN
  MATCH_MP_TAC WELIMAUX_fls_set_var_loc THEN
  ASM_MESON_TAC[WELIMAUX_get_store_fls]);;

let WELIMAUX_safe_Set = prove
 (WELIMAUX_safe_stmt `wl_Set v exp:(A)wl_prog`,
  WELIMAUX_SAFE_PRE_TAC THEN WELIMAUX_VIA_S_TAC THEN
  MATCH_MP_TAC WELIMAUX_fls_set_store THEN
  ASM_MESON_TAC[WELIMAUX_word_exp_fls]);;

let WELIMAUX_safe_OpCurrHeap = prove
 (WELIMAUX_safe_stmt `wl_OpCurrHeap b dst src:(A)wl_prog`,
  WELIMAUX_SAFE_PRE_TAC THEN WELIMAUX_VIA_S_TAC THEN
  MATCH_MP_TAC WELIMAUX_fls_set_var_loc THEN
  ASM_MESON_TAC[WELIMAUX_word_exp_fls]);;

let WELIMAUX_safe_Store = prove
 (WELIMAUX_safe_stmt `wl_Store exp v:(A)wl_prog`,
  WELIMAUX_SAFE_PRE_TAC THEN WELIMAUX_VIA_S_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WELIMAUX_mem_store_fls) THEN
  ASM_MESON_TAC[WELIMAUX_get_var_fls]);;

let WELIMAUX_safe_Tick = prove
 (WELIMAUX_safe_stmt `wl_Tick:(A)wl_prog`,
  WELIMAUX_SAFE_PRE_TAC THEN TRY (MATCH_MP_TAC WELIMAUX_fls_flush_sub) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[domain_find_loc_state; UNION_SUBSET]) THEN
  REWRITE_TAC[domain_find_loc_state; wl_dec_clock_def] THEN SIMP[]);;

let WELIMAUX_locs_subset = prove
 (CASE_TERM
  `!(l:((A)word_loc)list) t.
     (!n n1. MEM (wl_Loc n n1) l ==> n IN t)
     ==> UNIONS (set_of_list (MAP (\x. match dest_word_loc x with
                                         NONE -> {}
                                       | SOME x -> {x}) l)) SUBSET t`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; set_of_list; UNIONS_0; UNIONS_INSERT; EMPTY_SUBSET;
              UNION_SUBSET; MEM] THEN
  REPEAT STRIP_TAC THENL
   [DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      (ISPEC `h:(A)word_loc` (cases "word_loc")) THEN
    REWRITE_TAC[dest_word_loc_def; option_CASE; EMPTY_SUBSET; SING_SUBSET] THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let WELIMAUX_safe_Return = prove
 (WELIMAUX_safe_stmt `wl_Return n ms:(A)wl_prog`,
  WELIMAUX_SAFE_PRE_TAC THENL
   [MATCH_MP_TAC WELIMAUX_fls_flush_sub THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WELIMAUX_locs_subset THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
      check (fun th -> can (find_term ((=) `find_loc_state:(A,C,FFI)wl_state->1 spt`))
                           (concl th))) THEN
    REWRITE_TAC[domain_find_loc_state; IN_UNION] THEN
    ASM_MESON_TAC[get_vars_get_locals]]);;

let WELIMAUX_safe_Raise = prove
 (WELIMAUX_safe_stmt `wl_Raise n:(A)wl_prog`,
  WELIMAUX_SAFE_PRE_TAC THENL
   [WELIMAUX_VIA_S_TAC THEN ASM_MESON_TAC[WELIMAUX_jump_exc_fls];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb
      (lhs(concl th))))) = "wl_get_var" with Failure _ -> false)) THEN
    SPEC_TAC(`a:(A)word_loc`,`a:(A)word_loc`) THEN
    MATCH_MP_TAC word_loc_INDUCT THEN
    REWRITE_TAC[dest_result_loc_def; EMPTY_SUBSET; SING_SUBSET] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
      check (fun th -> can (find_term ((=) `find_loc_state:(A,C,FFI)wl_state->1 spt`))
                           (concl th))) THEN
    ASM_MESON_TAC[WELIMAUX_get_var_fls]]);;

let WELIMAUX_safe_Break = prove
 (WELIMAUX_safe_stmt `wl_Break k:(A)wl_prog`, WELIMAUX_SAFE_PRE_TAC);;

let WELIMAUX_safe_Continue = prove
 (WELIMAUX_safe_stmt `wl_Continue k:(A)wl_prog`, WELIMAUX_SAFE_PRE_TAC);;

let WELIMAUX_safe_CodeBufferWrite = prove
 (WELIMAUX_safe_stmt `wl_CodeBufferWrite r1 r2:(A)wl_prog`,
  WELIMAUX_SAFE_PRE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[domain_find_loc_state; UNION_SUBSET]) THEN
  REWRITE_TAC[domain_find_loc_state] THEN SIMP[]);;

let WELIMAUX_safe_DataBufferWrite = prove
 (WELIMAUX_safe_stmt `wl_DataBufferWrite r1 r2:(A)wl_prog`,
  WELIMAUX_SAFE_PRE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[domain_find_loc_state; UNION_SUBSET]) THEN
  REWRITE_TAC[domain_find_loc_state] THEN SIMP[]);;

let WELIMAUX_cut_env_locals = prove
 (`!names (L:((A)word_loc)spt) env.
     wl_cut_env names L = SOME env
     ==> domain (get_locals env) SUBSET domain (get_locals L)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_cut_env_def; cut_envs_def; cut_names_def] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `domain (union (get_locals (inter (L:((A)word_loc)spt) (SND (names:cutsets))))
                            (get_locals (inter L (FST names))))` THEN
  REWRITE_TAC[get_locals_union_subset; domain_union; UNION_SUBSET;
              get_locals_inter_subset]);;

let WELIMAUX_safe_FFI = prove
 (WELIMAUX_safe_stmt `wl_FFI ffi_index ptr1 len1 ptr2 len2 names:(A)wl_prog`,
  WELIMAUX_SAFE_PRE_TAC THENL
   [ALL_TAC; MATCH_MP_TAC WELIMAUX_fls_flush_sub THEN ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP WELIMAUX_cut_env_locals o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
                         "wl_cut_env" with Failure _ -> false)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[domain_find_loc_state; UNION_SUBSET]) THEN
  REWRITE_TAC[domain_find_loc_state] THEN SIMP[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS];
    MATCH_MP_TAC get_memory_write_bytearray_lemma THEN ASM_REWRITE_TAC[]]);;

let WELIMAUX_sh_mem_set_var_fls = prove
 (`!r v (s:(A,C,FFI)wl_state) (res:((A)wl_result)option) s1.
     sh_mem_set_var r v s = (res,s1) /\ ~(res = SOME wl_Error)
     ==> domain (find_loc_state s1) SUBSET domain (find_loc_state s) /\
         dest_result_loc res = {}`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `r:((FFI)ffi_result)option` (cases "option")) THEN
  TRY (STRUCT_CASES_TAC (ISPEC `a:(FFI)ffi_result` (cases "ffi_result"))) THEN
  REWRITE_TAC[sh_mem_set_var_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[dest_result_loc_def; WELIMAUX_fls_flush] THEN
  MATCH_MP_TAC WELIMAUX_fls_set_var_word THEN
  REWRITE_TAC[domain_find_loc_state] THEN SIMP[] THEN SET_TAC[]);;

let WELIMAUX_share_inst_fls = prove
 (`!op v ad (s:(A,C,FFI)wl_state) (res:((A)wl_result)option) s1.
     share_inst op v ad s = (res,s1) /\ ~(res = SOME wl_Error)
     ==> domain (find_loc_state s1) SUBSET domain (find_loc_state s) /\
         dest_result_loc res = {}`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  REWRITE_TAC[share_inst_def; WELIMAUX_sh_mem_set_var_fls] THEN
  REWRITE_TAC[wl_sh_mem_store_def; wl_sh_mem_store_byte_def;
    wl_sh_mem_store16_def; wl_sh_mem_store32_def] THEN
  REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[PAIR_EQ]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[dest_result_loc_def; WELIMAUX_fls_flush] THEN
  REWRITE_TAC[domain_find_loc_state] THEN SIMP[] THEN SET_TAC[]);;

let WELIMAUX_safe_ShareInst = prove
 (WELIMAUX_safe_stmt `ShareInst op v exp:(A)wl_prog`,
  WELIMAUX_SAFE_PRE_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP WELIMAUX_share_inst_fls o
    C CONJ (ASSUME `~(result = SOME (wl_Error:(A)wl_result))`) o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
                         "share_inst" with Failure _ -> false)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[EMPTY_SUBSET] THEN
  ASM_MESON_TAC[SUBSET_TRANS]);;

(* the parts of word_state_rel used by the main lemma *)

let WELIMAUX_word_state_rel_fls = prove
 (`!reachable (s:(A,C,FFI)wl_state) t.
     word_state_rel reachable s t
     ==> domain (find_loc_state s) SUBSET domain reachable /\
         word_elimProof_code_rel reachable (wl_state_code t) (wl_state_code s)`,
  SIMP[word_state_rel_def]);;

let WELIMAUX_rel_fupd = prove
 (`!reachable (s:(A,C,FFI)wl_state) c.
     word_elimProof_code_rel reachable c (wl_state_code s) /\
     domain (find_loc_state s) SUBSET domain reachable
     ==> word_state_rel reachable s (wl_state_code_fupd (K c) s)`,
  SIMP[word_state_rel_def]);;

let WELIMAUX_is_eval_eq th =
  try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_evaluate"
  with Failure _ -> false;;

(* a statement that does not depend on the code: the related state runs  *)
(* the same way, the locations come from the safety lemma                 *)

let WELIMAUX_SIMPLE_TAC (safe:thm) : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_word_state_rel_fls) THEN
  SUBGOAL_THEN `wl_state_code (s:(A,C,FFI)wl_state) =
                wl_state_code (new_state:(A,C,FFI)wl_state)` ASSUME_TAC THENL
   [MATCH_MP_TAC no_install_evaluate_const_code THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `reachable:1 spt` o
              MATCH_MP (REWRITE_RULE[IMP_CONJ] safe) o check WELIMAUX_is_eval_eq) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> SUBST1_TAC (MATCH_MP WELIMAUX_word_state_rel_code th)) THEN
  REWRITE_TAC[WELIMAUX_evaluate_code] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[check WELIMAUX_is_eval_eq th]) THEN
  ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM; PAIR_EQ; UNWIND_THM1] THEN
  MATCH_MP_TAC WELIMAUX_rel_fupd THEN ASM_MESON_TAC[];;

let WELIMAUX_rel_clock_termdep = prove
 (`!reachable (s:(A,C,FFI)wl_state) t c d.
     word_state_rel reachable s t
     ==> word_state_rel reachable (wl_state_clock_fupd (K c) (wl_state_termdep_fupd (K d) s))
                                  (wl_state_clock_fupd (K c) (wl_state_termdep_fupd (K d) t))`,
  REWRITE_TAC[word_state_rel_def; domain_find_loc_state] THEN SIMP[]);;

let WELIMAUX_rel_fields = prove
 (`!reachable (s:(A,C,FFI)wl_state) t.
     word_state_rel reachable s t
     ==> wl_state_locals t = wl_state_locals s /\
         wl_state_fp_regs t = wl_state_fp_regs s /\
         wl_state_store t = wl_state_store s /\
         wl_state_stack t = wl_state_stack s /\
         wl_state_memory t = wl_state_memory s /\
         wl_state_mdomain t = wl_state_mdomain s /\
         wl_state_sh_mdomain t = wl_state_sh_mdomain s /\
         wl_state_permute t = wl_state_permute s /\
         wl_state_compile t = wl_state_compile s /\
         wl_state_compile_oracle t = wl_state_compile_oracle s /\
         wl_state_code_buffer t = wl_state_code_buffer s /\
         wl_state_data_buffer t = wl_state_data_buffer s /\
         wl_state_gc_fun t = wl_state_gc_fun s /\
         wl_state_handler t = wl_state_handler s /\
         wl_state_clock t = wl_state_clock s /\
         wl_state_termdep t = wl_state_termdep s /\
         wl_state_be t = wl_state_be s /\
         wl_state_ffi t = wl_state_ffi s /\
         wl_state_locals_size t = wl_state_locals_size s /\
         wl_state_stack_max t = wl_state_stack_max s /\
         wl_state_stack_limit t = wl_state_stack_limit s /\
         wl_state_stack_size t = wl_state_stack_size s`,
  SIMP[word_state_rel_def]);;

let WELIMAUX_MT_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_rel_fields o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "word_state_rel"
                     with Failure _ -> false)) THEN
  UNDISCH_TAC `wl_evaluate (MustTerminate p,s:(A,C,FFI)wl_state) = result,new_state` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "ih" (MP_TAC o C MATCH_MP
    (ASSUME `~(wl_state_termdep (s:(A,C,FFI)wl_state) = 0)`)) THEN
  CASES_ON `wl_evaluate (p, wl_state_clock_fupd (K (MustTerminate_limit (:A)))
             (wl_state_termdep_fupd (K (wl_state_termdep (s:(A,C,FFI)wl_state) - 1)) s))` THEN
  REWRITE_TAC[pair_CASE] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`result:((A)wl_result)option`; `y:(A,C,FFI)wl_state`;
     `reachable:1 spt`;
     `wl_state_clock_fupd (K (MustTerminate_limit (:A)))
        (wl_state_termdep_fupd (K (wl_state_termdep (s:(A,C,FFI)wl_state) - 1))
           (removed_state:(A,C,FFI)wl_state))`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wordConvs_no_install_def; find_word_ref_def]) THEN
    ASM_SIMP_TAC[WELIMAUX_rel_clock_termdep] THEN SIMP[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE; PAIR_EQ; UNWIND_THM1] THEN
  MATCH_MP_TAC WELIMAUX_rel_clock_termdep THEN ASM_REWRITE_TAC[];;

let WELIMAUX_SEQ_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wordConvs_no_install_def; find_word_ref_def;
                              domain_union; UNION_SUBSET]) THEN
  UNDISCH_TAC `wl_evaluate (wl_Seq c1 c2,s:(A,C,FFI)wl_state) = result,new_state` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  CASES_ON `wl_evaluate (c1:(A)wl_prog,s:(A,C,FFI)wl_state)` THEN
  REWRITE_TAC[pair_CASE] THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN DISCH_TAC THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`NONE:((A)wl_result)option`; `y:(A,C,FFI)wl_state`;
      `reachable:1 spt`; `removed_state:(A,C,FFI)wl_state`]) THEN
    ASM_REWRITE_TAC[option_DISTINCT] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "ih2" (MP_TAC o SPEC `y:(A,C,FFI)wl_state`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`result:((A)wl_result)option`; `new_state:(A,C,FFI)wl_state`;
      `reachable:1 spt`; `t1:(A,C,FFI)wl_state`]) THEN
    ASM_REWRITE_TAC[pair_CASE] THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`c1:(A)wl_prog`; `s:(A,C,FFI)wl_state`; `NONE:((A)wl_result)option`;
                     `y:(A,C,FFI)wl_state`] wl_evaluate_consts) THEN
      MP_TAC(ISPECL [`c1:(A)wl_prog`; `s:(A,C,FFI)wl_state`; `NONE:((A)wl_result)option`;
                     `y:(A,C,FFI)wl_state`] no_install_evaluate_const_code) THEN
      MP_TAC(ISPECL [`c1:(A)wl_prog`; `removed_state:(A,C,FFI)wl_state`;
                     `NONE:((A)wl_result)option`; `t1:(A,C,FFI)wl_state`]
                    no_install_evaluate_const_code) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
      REWRITE_TAC[]];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`result:((A)wl_result)option`;
      `new_state:(A,C,FFI)wl_state`; `reachable:1 spt`;
      `removed_state:(A,C,FFI)wl_state`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t1:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[pair_CASE]];;

let WELIMAUX_IF_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wordConvs_no_install_def; find_word_ref_def;
                              domain_union; UNION_SUBSET]) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  SUBGOAL_THEN `wl_get_var r1 (removed_state:(A,C,FFI)wl_state) =
                wl_get_var r1 (s:(A,C,FFI)wl_state) /\
                wl_get_var_imm ri (removed_state:(A,C,FFI)wl_state) =
                wl_get_var_imm ri s`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP WELIMAUX_word_state_rel_code th]) THEN
    SIMP[];
    ALL_TAC] THEN
  UNDISCH_TAC `wl_evaluate (wl_If cmp r1 ri c1 c2,s:(A,C,FFI)wl_state) =
               result,new_state` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  (* the NONE cases are closed by the rewriting *)
  CASES_ON `wl_get_var r1 (s:(A,C,FFI)wl_state)` THEN
  ASM_REWRITE_TAC[pair_CASE; option_CASE; PAIR_EQ] THEN
  CASES_ON `wl_get_var_imm ri (s:(A,C,FFI)wl_state)` THEN
  ASM_REWRITE_TAC[pair_CASE; option_CASE; PAIR_EQ] THEN
  CASES_ON `wl_word_cmp cmp (a:(A)word_loc) (a':(A)word_loc)` THEN
  ASM_REWRITE_TAC[pair_CASE; option_CASE; PAIR_EQ] THEN
  TRY (STRIP_TAC THEN ASM_MESON_TAC[]);;

let WELIMAUX_rel_dec_clock = prove
 (`!reachable (s:(A,C,FFI)wl_state) t.
     word_state_rel reachable s t
     ==> word_state_rel reachable (wl_dec_clock s) (wl_dec_clock t)`,
  REWRITE_TAC[word_state_rel_def; wl_dec_clock_def; domain_find_loc_state] THEN
  SIMP[]);;

let WELIMAUX_rel_flush = prove
 (`!reachable (s:(A,C,FFI)wl_state) t b.
     word_state_rel reachable s t
     ==> word_state_rel reachable (wl_flush_state b s) (wl_flush_state b t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP WELIMAUX_word_state_rel_code) THEN
  REWRITE_TAC[WELIMAUX_flush_code] THEN MATCH_MP_TAC WELIMAUX_rel_fupd THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_word_state_rel_fls) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[flush_state_const] THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[WELIMAUX_fls_flush_sub]]);;

let WELIMAUX_cut_state_rel = prove
 (`!reachable (s:(A,C,FFI)wl_state) t names s'.
     word_state_rel reachable s t /\ wl_cut_state names s = SOME s'
     ==> ?t'. wl_cut_state names t = SOME t' /\ word_state_rel reachable s' t' /\
              domain (find_loc_state s') SUBSET domain (find_loc_state s) /\
              wl_state_code s' = wl_state_code s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `domain (find_loc_state (s':(A,C,FFI)wl_state)) SUBSET
                domain (find_loc_state (s:(A,C,FFI)wl_state)) /\
                wl_state_code s' = wl_state_code s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `wl_cut_state names (s:(A,C,FFI)wl_state) = SOME s'` THEN
    REWRITE_TAC[wl_cut_state_def] THEN
    CASES_ON `wl_cut_env names (wl_state_locals (s:(A,C,FFI)wl_state))` THEN
    REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP WELIMAUX_cut_env_locals) THEN
    REWRITE_TAC[domain_find_loc_state] THEN SIMP[] THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP WELIMAUX_word_state_rel_code) THEN
  ASM_REWRITE_TAC[cut_state_with_const; OPTION_MAP_DEF; option_INJ] THEN
  REWRITE_TAC[UNWIND_THM1] THEN
  MATCH_MP_TAC WELIMAUX_rel_fupd THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_word_state_rel_fls) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `domain (find_loc_state (s:(A,C,FFI)wl_state))` THEN ASM_REWRITE_TAC[]);;

let WELIMAUX_dest_exit_loop = prove
 (`!res:((A)wl_result)option.
     dest_result_loc (wl_exit_loop res) SUBSET dest_result_loc res`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `res:((A)wl_result)option` (cases "option")) THEN
  TRY (STRUCT_CASES_TAC (ISPEC `a:(A)wl_result` (cases "wl_result"))) THEN
  REWRITE_TAC[wl_exit_loop_def; dest_result_loc_def; SUBSET_REFL; EMPTY_SUBSET]);;

let WELIMAUX_INSTALL_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wordConvs_no_install_def]) THEN
  FIRST_ASSUM CONTR_TAC;;

let WELIMAUX_LOCVALUE_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_word_state_rel_fls) THEN
  UNDISCH_TAC `wl_evaluate (wl_LocValue r l1,s:(A,C,FFI)wl_state) = result,new_state` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [ALL_TAC; STRIP_TAC THEN ASM_MESON_TAC[]] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[find_word_ref_def; domain_insert; domain_def;
                              INSERT_SUBSET]) THEN
  SUBGOAL_THEN `l1 IN domain (wl_state_code (removed_state:(A,C,FFI)wl_state))`
    ASSUME_TAC THENL
   [UNDISCH_TAC `l1 IN domain (wl_state_code (s:(A,C,FFI)wl_state))` THEN
    REWRITE_TAC[domain_lookup] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[word_elimProof_code_rel_def]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[PAIR_EQ; UNWIND_THM1; dest_result_loc_def; EMPTY_SUBSET] THEN
  MATCH_MP_TAC word_state_rel_set_var THEN
  ASM_REWRITE_TAC[dest_word_loc_def; option_CASE; SING_SUBSET];;

let WELIMAUX_cut_state_consts = prove
 (`!names (s:(A,C,FFI)wl_state) s1.
     wl_cut_state names s = SOME s1
     ==> wl_state_code s1 = wl_state_code s /\
         wl_state_gc_fun s1 = wl_state_gc_fun s /\
         wl_state_clock s1 = wl_state_clock s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_cut_state_def] THEN
  CASES_ON `wl_cut_env names (wl_state_locals (s:(A,C,FFI)wl_state))` THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[]);;

let WELIMAUX_LOOP_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihL") (LABEL_TAC "ihB")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wordConvs_no_install_def; find_word_ref_def]) THEN
  UNDISCH_TAC `wl_evaluate (wl_Loop names c exit_names,s:(A,C,FFI)wl_state) =
               result,new_state` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  CASES_ON `wl_cut_state (names,LN) (s:(A,C,FFI)wl_state)` THEN
  REWRITE_TAC[option_CASE] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`reachable:1 spt`; `s:(A,C,FFI)wl_state`;
                 `removed_state:(A,C,FFI)wl_state`; `(names,LN):cutsets`;
                 `a:(A,C,FFI)wl_state`] WELIMAUX_cut_state_rel) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[option_CASE] THEN
  CASES_ON `wl_evaluate (c:(A)wl_prog, a:(A,C,FFI)wl_state)` THEN
  REWRITE_TAC[pair_CASE] THEN
  ASM_CASES_TAC `x = SOME (wl_Error:(A)wl_result)` THENL
   [ASM_REWRITE_TAC[wl_cont_loop_def; wl_exit_loop_def; option_INJ;
                    distinctness "wl_result"; PAIR_EQ] THEN
    STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_cut_state_consts o
    check (fun th -> concl th = `wl_cut_state (names,LN) (removed_state:(A,C,FFI)wl_state) =
                                 SOME t'`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_cut_state_consts o
    check (fun th -> concl th = `wl_cut_state (names,LN) (s:(A,C,FFI)wl_state) = SOME a`)) THEN
  REMOVE_THEN "ihB" (MP_TAC o SPEC `a:(A,C,FFI)wl_state`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:((A)wl_result)option`; `y:(A,C,FFI)wl_state`;
    `reachable:1 spt`; `t':(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_rel_fields o
    check (fun th -> concl th = `word_state_rel reachable (y:(A,C,FFI)wl_state) t1`)) THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [COND_CASES_TAC THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      EXISTS_TAC `wl_flush_state T (t1:(A,C,FFI)wl_state)` THEN
      ASM_SIMP_TAC[WELIMAUX_rel_flush; dest_result_loc_def; EMPTY_SUBSET];
      ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN
    REMOVE_THEN "ihL" (MP_TAC o SPECL [`a:(A,C,FFI)wl_state`; `x:((A)wl_result)option`;
                                       `y:(A,C,FFI)wl_state`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`result:((A)wl_result)option`;
      `new_state:(A,C,FFI)wl_state`; `reachable:1 spt`;
      `wl_dec_clock (t1:(A,C,FFI)wl_state)`]) THEN
    REWRITE_TAC[wl_STOP_def; wordConvs_no_install_def; find_word_ref_def] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wl_STOP_def]) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[WELIMAUX_rel_dec_clock] THEN REWRITE_TAC[wl_dec_clock_def] THEN
      SIMP[] THEN
      MP_TAC(ISPECL [`c:(A)wl_prog`; `a:(A,C,FFI)wl_state`; `x:((A)wl_result)option`;
                     `y:(A,C,FFI)wl_state`] wl_evaluate_consts) THEN
      MP_TAC(ISPECL [`c:(A)wl_prog`; `a:(A,C,FFI)wl_state`; `x:((A)wl_result)option`;
                     `y:(A,C,FFI)wl_state`] no_install_evaluate_const_code) THEN
      MP_TAC(ISPECL [`c:(A)wl_prog`; `t':(A,C,FFI)wl_state`; `x:((A)wl_result)option`;
                     `t1:(A,C,FFI)wl_state`] no_install_evaluate_const_code) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [CASES_ON `wl_cut_state (exit_names,LN) (y:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[option_CASE; PAIR_EQ] THENL
     [STRIP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    MP_TAC(ISPECL [`reachable:1 spt`; `y:(A,C,FFI)wl_state`; `t1:(A,C,FFI)wl_state`;
                   `(exit_names,LN):cutsets`; `new_state:(A,C,FFI)wl_state`]
           WELIMAUX_cut_state_rel) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t2:(A,C,FFI)wl_state` THEN
    ASM_REWRITE_TAC[option_CASE; dest_result_loc_def; EMPTY_SUBSET];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    EXISTS_TAC `t1:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[WELIMAUX_dest_exit_loop; SUBSET_TRANS]];;

(* helpers of the Call case *)

let WELIMAUX_find_code_eq = prove
 (`!dest (args:((A)word_loc)list) (c1:(num#B)spt) c2 (ss:(L)spt).
     (!n. dest = SOME n ==> lookup n c1 = lookup n c2) /\
     (!n m. dest = NONE /\ MEM (wl_Loc n m) args ==> lookup n c1 = lookup n c2)
     ==> wl_find_code dest args c1 ss = wl_find_code dest args c2 ss`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `dest:num option` (cases "option")) THEN
  REWRITE_TAC[wl_find_code_def; option_DISTINCT; option_INJ] THEN
  REPEAT STRIP_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CASES_ON `LAST (args:((A)word_loc)list)` THEN
    REWRITE_TAC[case_def "word_loc"] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `lookup a0 (c1:(num#B)spt) = lookup a0 c2`
      (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `a1:num` THEN
    ASM_MESON_TAC[MEM_LAST_NOT_NIL];
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[REWRITE_RULE[] (SPEC `a:num` th)])]);;

let WELIMAUX_find_code_info = prove
 (`!dest (args:((A)word_loc)list) (code:(num#B)spt) (ss:(L)spt) args1 prog ss1.
     wl_find_code dest args code ss = SOME (args1,prog,ss1)
     ==> (?n a. lookup n code = SOME (a,prog) /\
                (dest = SOME n \/ (dest = NONE /\ ?m. MEM (wl_Loc n m) args))) /\
         (!x. MEM x args1 ==> MEM x args)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `dest:num option` (cases "option")) THEN
  REWRITE_TAC[wl_find_code_def; option_DISTINCT; option_INJ] THEN
  REPEAT GEN_TAC THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MEM_LAST_NOT_NIL; MEM_FRONT; APPEND_BUTLAST_LAST; MEM_APPEND]);;

let WELIMAUX_code_closed_lookup = prove
 (`!reachable (c:(num#(A)wl_prog)spt) n a p.
     code_closed reachable c /\ n IN domain reachable /\ lookup n c = SOME (a,p)
     ==> domain (find_word_ref p) SUBSET domain (reachable:B spt)`,
  REWRITE_TAC[code_closed_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var (lhs (concl th)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lookup_fromAList]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP lookup_analyse_word_code) THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[is_reachable_def] THEN MATCH_MP_TAC RTC_SINGLE THEN
  REWRITE_TAC[is_adjacent_def] THEN EXISTS_TAC `find_word_ref (p:(A)wl_prog)` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `m IN domain (find_word_ref (p:(A)wl_prog))` THEN
  REWRITE_TAC[domain_lookup] THEN MESON_TAC[one]);;

let WELIMAUX_rel_call_env = prove
 (`!reachable (s:(A,C,FFI)wl_state) t args1 ss.
     word_state_rel reachable s t /\
     (!n m. MEM (wl_Loc n m) args1 ==> n IN domain reachable)
     ==> word_state_rel reachable (wl_call_env args1 ss s) (wl_call_env args1 ss t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_word_state_rel_fls) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP WELIMAUX_word_state_rel_code) THEN
  REWRITE_TAC[wl_call_env_with_const] THEN MATCH_MP_TAC WELIMAUX_rel_fupd THEN
  REWRITE_TAC[wl_call_env_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `domain (find_loc_state (s:(A,C,FFI)wl_state)) SUBSET domain (reachable:1 spt)` THEN
  REWRITE_TAC[domain_find_loc_state] THEN SIMP[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; domain_get_locals_lookup] THEN
  X_GEN_TAC `x:num` THEN DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_TAC `n1:num`)) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `n1:num` THEN
  REWRITE_TAC[ISPECL [`wl_Loc x n1:(A)word_loc`; `args1:((A)word_loc)list`]
                fromList2_value] THEN
  ASM_MESON_TAC[]);;

let WELIMAUX_rel_push_env = prove
 (`!reachable (s:(A,C,FFI)wl_state) t names envs h.
     word_state_rel reachable s t /\ cut_envs names (wl_state_locals s) = SOME envs
     ==> word_state_rel reachable (wl_push_env envs h s) (wl_push_env envs h t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_word_state_rel_fls) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_push_env_fls) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP WELIMAUX_word_state_rel_code) THEN
  REWRITE_TAC[wl_push_env_with_const] THEN MATCH_MP_TAC WELIMAUX_rel_fupd THEN
  ASM_MESON_TAC[SUBSET_TRANS]);;

let WELIMAUX_rel_flush_stack = prove
 (`!reachable (s:(A,C,FFI)wl_state) t m.
     word_state_rel reachable s t
     ==> word_state_rel reachable
           (wl_flush_state T (wl_state_stack_fupd (K []) (wl_state_stack_max_fupd (K m) s)))
           (wl_flush_state T (wl_state_stack_fupd (K []) (wl_state_stack_max_fupd (K m) t)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_word_state_rel_fls) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_rel_fields) THEN
  UNDISCH_TAC `domain (find_loc_state (s:(A,C,FFI)wl_state)) SUBSET domain (reachable:1 spt)` THEN
  UNDISCH_TAC `word_elimProof_code_rel (reachable:1 spt) (wl_state_code (t:(A,C,FFI)wl_state))
                 (wl_state_code (s:(A,C,FFI)wl_state))` THEN
  REWRITE_TAC[word_state_rel_def; wl_flush_state_def; domain_find_loc_state] THEN
  SIMP[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[get_locals_def; word_elimProof_get_stack_def; domain_def;
    word_elimProof_get_store_def; LET_DEF; LET_END_DEF; FRANGE_FEMPTY;
    LIST_OF_SET_EMPTY; MAP; FILTER; FOLDL; EMPTY_SUBSET]);;

(* the parts of the Call case: references and no_install of a call *)

let WELIMAUX_find_word_ref_call = prove
 (`!(ret:(num list#cutsets#(A)wl_prog#num#num)option) dest args handler (r:1 spt).
     domain (find_word_ref (wl_Call ret dest args handler)) SUBSET domain r <=>
     (!n. dest = SOME n ==> n IN domain r) /\
     (!n names rh l1 l2. ret = SOME (n,names,rh,l1,l2)
                         ==> l1 IN domain r /\ domain (find_word_ref rh) SUBSET domain r) /\
     (!n h l1 l2. handler = SOME (n,h,l1,l2) ==> domain (find_word_ref h) SUBSET domain r)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[find_word_ref_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[domain_union; UNION_SUBSET; domain_insert; INSERT_SUBSET; domain_def;
    EMPTY_SUBSET; option_DISTINCT; option_INJ; PAIR_EQ] THEN
  MESON_TAC[]);;

let WELIMAUX_no_install_call = prove
 (`!(ret:(num list#cutsets#(A)wl_prog#num#num)option) dest args handler.
     wordConvs_no_install (wl_Call ret dest args handler) <=>
     (!n names rh l1 l2. ret = SOME (n,names,rh,l1,l2) ==> wordConvs_no_install rh) /\
     (!n h l1 l2. handler = SOME (n,h,l1,l2) ==> wordConvs_no_install h)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[wordConvs_no_install_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "wl_prog"; option_DISTINCT; option_INJ; PAIR_EQ] THEN
  MESON_TAC[]);;

let WELIMAUX_MEM_add_ret_loc = prove
 (`!(ret:(B#C#D#num#num)option) (xs:((A)word_loc)list) y.
     MEM y (add_ret_loc ret xs) <=>
     MEM y xs \/ ?n names rh l1 l2. ret = SOME (n,names,rh,l1,l2) /\ y = wl_Loc l1 l2`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; add_ret_loc_def; MEM;
              option_DISTINCT; option_INJ; PAIR_EQ] THEN
  MESON_TAC[]);;

let WELIMAUX_call_locs = prove
 (`!reachable (s:(A,C,FFI)wl_state) t
      (ret:(num list#cutsets#(A)wl_prog#num#num)option) dest args
      (handler:(num#(A)wl_prog#num#num)option) xs.
     word_state_rel reachable s t /\ wl_get_vars args s = SOME xs /\
     domain (find_word_ref (wl_Call ret dest args handler)) SUBSET domain reachable
     ==> !n m. MEM (wl_Loc n m) (add_ret_loc ret xs) ==> n IN domain reachable`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WELIMAUX_find_word_ref_call] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_word_state_rel_fls) THEN
  SUBGOAL_THEN `!n m. MEM (wl_Loc n m:(A)word_loc) xs ==> n IN domain (reachable:1 spt)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
      check (fun th -> can (find_term ((=) `find_loc_state:(A,C,FFI)wl_state->1 spt`))
                           (concl th))) THEN
    REWRITE_TAC[domain_find_loc_state; IN_UNION] THEN
    DISJ1_TAC THEN DISJ1_TAC THEN DISJ1_TAC THEN
    MATCH_MP_TAC get_vars_get_locals THEN
    MAP_EVERY EXISTS_TAC [`args:num list`; `xs:((A)word_loc)list`; `m:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[WELIMAUX_MEM_add_ret_loc] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "word_loc"]) THEN
  ASM_MESON_TAC[]);;

let WELIMAUX_call_find_code = prove
 (`!reachable (s:(A,C,FFI)wl_state) t
      (ret:(num list#cutsets#(A)wl_prog#num#num)option) dest args
      (handler:(num#(A)wl_prog#num#num)option) xs.
     word_state_rel reachable s t /\ wl_get_vars args s = SOME xs /\
     domain (find_word_ref (wl_Call ret dest args handler)) SUBSET domain reachable
     ==> wl_find_code dest (add_ret_loc ret xs) (wl_state_code t)
                      (wl_state_stack_size t) =
         wl_find_code dest (add_ret_loc ret xs) (wl_state_code s)
                      (wl_state_stack_size s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP WELIMAUX_call_locs) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_word_state_rel_fls) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_rel_fields) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WELIMAUX_find_word_ref_call]) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WELIMAUX_find_code_eq THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_elimProof_code_rel_def]) THEN
  ASM_MESON_TAC[]);;

let WELIMAUX_call_prog = prove
 (`!reachable (s:(A,C,FFI)wl_state) t
      (ret:(num list#cutsets#(A)wl_prog#num#num)option) dest args
      (handler:(num#(A)wl_prog#num#num)option) xs args1 prog ss.
     word_state_rel reachable s t /\ wl_get_vars args s = SOME xs /\
     domain (find_word_ref (wl_Call ret dest args handler)) SUBSET domain reachable /\
     code_closed reachable (wl_state_code s) /\ no_install_code (wl_state_code s) /\
     wl_find_code dest (add_ret_loc ret xs) (wl_state_code s) (wl_state_stack_size s) =
       SOME (args1,prog,ss)
     ==> domain (find_word_ref prog) SUBSET domain reachable /\
         wordConvs_no_install prog /\
         (!n m. MEM (wl_Loc n m) args1 ==> n IN domain reachable)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`reachable:1 spt`; `s:(A,C,FFI)wl_state`; `t:(A,C,FFI)wl_state`;
    `ret:(num list#cutsets#(A)wl_prog#num#num)option`; `dest:num option`;
    `args:num list`; `handler:(num#(A)wl_prog#num#num)option`;
    `xs:((A)word_loc)list`] WELIMAUX_call_locs) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WELIMAUX_find_code_info o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
                         "wl_find_code" with Failure _ -> false)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `a:num`
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) ASSUME_TAC) THEN
  SUBGOAL_THEN `n IN domain (reachable:1 spt)` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[WELIMAUX_find_word_ref_call]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC WELIMAUX_code_closed_lookup THEN
    MAP_EVERY EXISTS_TAC [`wl_state_code (s:(A,C,FFI)wl_state)`; `n:num`; `a:num`] THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[no_install_code_def];
    ASM_MESON_TAC[]]);;

let WELIMAUX_handler_cases = prove
 (`!handler:(num#(A)wl_prog#num#num)option.
     handler = NONE \/ ?n h l1 l2. handler = SOME (n,h,l1,l2)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; option_DISTINCT; option_INJ;
              PAIR_EQ] THEN MESON_TAC[]);;

let WELIMAUX_stack_max_push_call = prove
 (`!reachable (s:(A,C,FFI)wl_state) t args1 ss envs h.
     word_state_rel reachable s t
     ==> wl_state_stack_max (wl_call_env args1 ss (wl_push_env envs h t)) =
         wl_state_stack_max (wl_call_env args1 ss (wl_push_env envs h s))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP WELIMAUX_word_state_rel_code) THEN
  REWRITE_TAC[wl_push_env_with_const; wl_call_env_with_const] THEN SIMP[]);;

let WELIMAUX_rel_call_push = prove
 (`!reachable (s:(A,C,FFI)wl_state) t args1 ss names envs h.
     word_state_rel reachable s t /\
     cut_envs names (wl_state_locals s) = SOME envs /\
     (!n m. MEM (wl_Loc n m) args1 ==> n IN domain reachable)
     ==> word_state_rel reachable
           (wl_call_env args1 ss (wl_push_env envs h (wl_dec_clock s)))
           (wl_call_env args1 ss (wl_push_env envs h (wl_dec_clock t))) /\
         wl_state_code (wl_call_env args1 ss (wl_push_env envs h (wl_dec_clock s))) =
         wl_state_code s /\
         wl_state_code (wl_call_env args1 ss (wl_push_env envs h (wl_dec_clock t))) =
         wl_state_code t /\
         wl_state_gc_fun (wl_call_env args1 ss (wl_push_env envs h (wl_dec_clock s))) =
         wl_state_gc_fun s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:(A,C,FFI)wl_state.
                  cut_envs names (wl_state_locals x) = SOME envs
                  ==> wl_state_code (wl_call_env args1 ss (wl_push_env envs h
                         (wl_dec_clock x))) = wl_state_code x /\
                      wl_state_gc_fun (wl_call_env args1 ss (wl_push_env envs h
                         (wl_dec_clock x))) = wl_state_gc_fun x`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`names:cutsets`; `envs:((A)word_loc)spt#((A)word_loc)spt`;
                   `h:(num#(A)wl_prog#num#num)option`;
                   `wl_dec_clock (x:(A,C,FFI)wl_state)`] WELIMAUX_push_env_fls) THEN
    REWRITE_TAC[wl_dec_clock_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
    SIMP[wl_call_env_def];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_rel_fields) THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC WELIMAUX_rel_call_env THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC WELIMAUX_rel_push_env THEN EXISTS_TAC `names:cutsets` THEN
  ASM_SIMP_TAC[WELIMAUX_rel_dec_clock] THEN REWRITE_TAC[wl_dec_clock_def] THEN
  SIMP[] THEN ASM_REWRITE_TAC[]);;

let WELIMAUX_call_ret_facts = prove
 (`!n names (rh:(A)wl_prog) l1 l2 dest args handler (r:1 spt).
     domain (find_word_ref (wl_Call (SOME (n,names,rh,l1,l2)) dest args handler))
       SUBSET domain r
     ==> wordConvs_no_install (wl_Call (SOME (n,names,rh,l1,l2)) dest args handler)
     ==> domain (find_word_ref rh) SUBSET domain r /\ wordConvs_no_install rh`,
  REWRITE_TAC[WELIMAUX_find_word_ref_call; WELIMAUX_no_install_call] THEN
  MESON_TAC[]);;

let WELIMAUX_call_handler_facts = prove
 (`!(ret:(num list#cutsets#(A)wl_prog#num#num)option) dest args n (h:(A)wl_prog)
    l1 l2 (r:1 spt).
     domain (find_word_ref (wl_Call ret dest args (SOME (n,h,l1,l2))))
       SUBSET domain r
     ==> wordConvs_no_install (wl_Call ret dest args (SOME (n,h,l1,l2)))
     ==> domain (find_word_ref h) SUBSET domain r /\ wordConvs_no_install h`,
  REWRITE_TAC[WELIMAUX_find_word_ref_call; WELIMAUX_no_install_call] THEN
  MESON_TAC[]);;

let WELIMAUX_ERR_TAC : tactic =
  (* the term is parsed once (a parse per assumption cost seconds a call) *)
  let err_tm = `~(SOME (wl_Error:(A)wl_result) = SOME wl_Error)` in
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_ASSUM(fun th ->
    if concl th = err_tm then CONTR_TAC (REWRITE_RULE[] th) else NO_TAC);;

(* the Call case of word_removal_lemma *)

let WELIMAUX_CALL_PRE_TAC : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let l = CONJUNCTS th in
    LABEL_TAC "ih1" (el 0 l) THEN LABEL_TAC "ih2" (el 1 l) THEN
    LABEL_TAC "ih3" (el 2 l) THEN LABEL_TAC "ih4" (el 3 l)) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_word_state_rel_fls) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP word_state_rel_get_vars o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "word_state_rel"
                     with Failure _ -> false)) THEN
  UNDISCH_TAC `wl_evaluate (wl_Call ret dest args handler,s:(A,C,FFI)wl_state) =
               result,new_state` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `wl_get_vars args (s:(A,C,FFI)wl_state)` THEN
  REWRITE_TAC[option_CASE] THENL [WELIMAUX_ERR_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL [WELIMAUX_ERR_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`reachable:1 spt`; `s:(A,C,FFI)wl_state`;
    `removed_state:(A,C,FFI)wl_state`;
    `ret:(num list#cutsets#(A)wl_prog#num#num)option`; `dest:num option`;
    `args:num list`; `handler:(num#(A)wl_prog#num#num)option`;
    `a:((A)word_loc)list`] WELIMAUX_call_find_code) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CASES_ON `wl_find_code dest (add_ret_loc (ret:(num list#cutsets#(A)wl_prog#num#num)option)
              (a:((A)word_loc)list))
              (wl_state_code (s:(A,C,FFI)wl_state)) (wl_state_stack_size s)` THEN
  REWRITE_TAC[option_CASE] THENL [WELIMAUX_ERR_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?args1 prog ss. (a':((A)word_loc)list#(A)wl_prog#num option) =
                                (args1,prog,ss)`
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL
   [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPECL [`reachable:1 spt`; `s:(A,C,FFI)wl_state`;
    `removed_state:(A,C,FFI)wl_state`;
    `ret:(num list#cutsets#(A)wl_prog#num#num)option`; `dest:num option`;
    `args:num list`; `handler:(num#(A)wl_prog#num#num)option`;
    `a:((A)word_loc)list`; `args1:((A)word_loc)list`; `prog:(A)wl_prog`;
    `ss:num option`] WELIMAUX_call_prog) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_rel_fields o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "word_state_rel"
                     with Failure _ -> false));;

let WELIMAUX_CALL_TAIL_TAC : tactic =
  REWRITE_TAC[option_CASE] THEN
  SUBGOAL_THEN `wl_state_clock (removed_state:(A,C,FFI)wl_state) =
                wl_state_clock (s:(A,C,FFI)wl_state)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THENL [ALL_TAC; WELIMAUX_ERR_TAC] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    EXISTS_TAC `wl_flush_state T (removed_state:(A,C,FFI)wl_state)` THEN
    ASM_SIMP_TAC[WELIMAUX_rel_flush; dest_result_loc_def; EMPTY_SUBSET];
    ALL_TAC] THEN
  CASES_ON `wl_evaluate (prog:(A)wl_prog,
              wl_call_env (args1:((A)word_loc)list) (ss:num option)
                (wl_dec_clock (s:(A,C,FFI)wl_state)))` THEN
  REWRITE_TAC[pair_CASE] THEN
  COND_CASES_TAC THENL [WELIMAUX_ERR_TAC; ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`a:((A)word_loc)list`; `prog:(A)wl_prog`;
     `args1:((A)word_loc)list`; `ss:num option`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`result:((A)wl_result)option`;
    `new_state:(A,C,FFI)wl_state`; `reachable:1 spt`;
    `wl_call_env args1 ss (wl_dec_clock (removed_state:(A,C,FFI)wl_state))`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC WELIMAUX_rel_call_env THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC WELIMAUX_rel_dec_clock THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[wl_call_env_def; wl_dec_clock_def] THEN SIMP[] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t1:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[pair_CASE];;

let WELIMAUX_CALL_RET1_TAC : tactic =
  FIRST_ASSUM(MP_TAC o MATCH_MP WELIMAUX_call_ret_facts) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  REWRITE_TAC[option_CASE; pair_CASE] THEN
  SUBGOAL_THEN `wl_state_clock (removed_state:(A,C,FFI)wl_state) =
                wl_state_clock (s:(A,C,FFI)wl_state) /\
                wl_state_locals removed_state = wl_state_locals s`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THENL [WELIMAUX_ERR_TAC; ALL_TAC] THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th; option_CASE] THEN WELIMAUX_ERR_TAC)
    (X_CHOOSE_THEN `envs:((A)word_loc)spt#((A)word_loc)spt` ASSUME_TAC)
    (ISPEC `cut_envs names (wl_state_locals (s:(A,C,FFI)wl_state))` (cases "option")) THEN
  ASM_REWRITE_TAC[option_CASE] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WELIMAUX_stack_max_push_call th]) THEN
    REWRITE_TAC[PAIR_EQ; UNWIND_THM1; dest_result_loc_def; EMPTY_SUBSET] THEN
    MATCH_MP_TAC WELIMAUX_rel_flush_stack THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `wl_evaluate (prog:(A)wl_prog, wl_call_env (args1:((A)word_loc)list)
           (ss:num option) (wl_push_env (envs:((A)word_loc)spt#((A)word_loc)spt)
              handler (wl_dec_clock (s:(A,C,FFI)wl_state))))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:((A)wl_result)option`
    (X_CHOOSE_THEN `y:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  ASM_CASES_TAC `x = SOME (wl_Error:(A)wl_result)` THENL
   [ASM_REWRITE_TAC[option_CASE; case_def "wl_result"] THEN WELIMAUX_ERR_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "ih4" (MP_TAC o SPECL [`a:((A)word_loc)list`; `rh:(A)wl_prog`; `l1:num`;
     `l2:num`; `n:num list`; `names:cutsets`; `prog:(A)wl_prog`;
     `args1:((A)word_loc)list`; `ss:num option`;
     `envs:((A)word_loc)spt#((A)word_loc)spt`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:((A)wl_result)option`; `y:(A,C,FFI)wl_state`;
    `reachable:1 spt`;
    `wl_call_env args1 ss (wl_push_env envs handler
       (wl_dec_clock (removed_state:(A,C,FFI)wl_state)))`]) THEN
  MP_TAC(ISPECL [`reachable:1 spt`; `s:(A,C,FFI)wl_state`;
    `removed_state:(A,C,FFI)wl_state`; `args1:((A)word_loc)list`; `ss:num option`;
    `names:cutsets`; `envs:((A)word_loc)spt#((A)word_loc)spt`;
    `handler:(num#(A)wl_prog#num#num)option`] WELIMAUX_rel_call_push) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_rel_fields o
    check (fun th -> concl th = `word_state_rel reachable (y:(A,C,FFI)wl_state) t2`)) THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`;
    `wl_call_env args1 ss (wl_push_env envs handler (wl_dec_clock (s:(A,C,FFI)wl_state)))`;
    `x:((A)wl_result)option`; `y:(A,C,FFI)wl_state`] wl_evaluate_consts) THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`;
    `wl_call_env args1 ss (wl_push_env envs handler (wl_dec_clock (s:(A,C,FFI)wl_state)))`;
    `x:((A)wl_result)option`; `y:(A,C,FFI)wl_state`] no_install_evaluate_const_code) THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`;
    `wl_call_env args1 ss (wl_push_env envs handler
       (wl_dec_clock (removed_state:(A,C,FFI)wl_state)))`;
    `x:((A)wl_result)option`; `t2:(A,C,FFI)wl_state`]
    no_install_evaluate_const_code) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `r:(A)wl_result` SUBST_ALL_TAC)
    (ISPEC `x:((A)wl_result)option` (cases "option")) THEN
  REWRITE_TAC[option_CASE] THENL [WELIMAUX_ERR_TAC; ALL_TAC] THEN
  REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    (ISPEC `r:(A)wl_result` (cases "wl_result")) THEN
  REWRITE_TAC[case_def "wl_result"] THEN
  TRY (WELIMAUX_ERR_TAC THEN NO_TAC) THEN
  TRY (REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
       EXISTS_TAC `t2:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN NO_TAC);;

(* the code and gc_fun of the states after the call body, for the IHs *)

let WELIMAUX_CODES_TAC (sts:term list) : tactic =
  MAP_EVERY (fun t -> MP_TAC (ASSUME t)) sts THEN
  MAP_EVERY (fun t -> MP_TAC (ASSUME t))
    [`gc_no_new_locs (wl_state_gc_fun (s:(A,C,FFI)wl_state))`;
     `no_install_code (wl_state_code (s:(A,C,FFI)wl_state))`;
     `no_install_code (wl_state_code (removed_state:(A,C,FFI)wl_state))`;
     `code_closed (reachable:1 spt) (wl_state_code (s:(A,C,FFI)wl_state))`] THEN
  MESON_TAC[];;

let WELIMAUX_CALL_RESULT_TAC : tactic =
  COND_CASES_TAC THENL [WELIMAUX_ERR_TAC; ALL_TAC] THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th; option_CASE] THEN WELIMAUX_ERR_TAC)
    (X_CHOOSE_THEN `s1:(A,C,FFI)wl_state` ASSUME_TAC)
    (ISPEC `wl_pop_env (y:(A,C,FFI)wl_state)` (cases "option")) THEN
  ASM_REWRITE_TAC[option_CASE] THEN
  MP_TAC(ISPECL [`reachable:1 spt`; `y:(A,C,FFI)wl_state`; `t2:(A,C,FFI)wl_state`;
                 `s1:(A,C,FFI)wl_state`; `0`; `0`] word_state_rel_pop_env) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[option_CASE] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WELIMAUX_rel_fields o
    check (fun th -> concl th = `word_state_rel reachable (s1:(A,C,FFI)wl_state) t1`)) THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL [ALL_TAC; WELIMAUX_ERR_TAC] THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(MATCH_MP pop_env_code_gc_fun_clock
    (ASSUME `wl_pop_env (y:(A,C,FFI)wl_state) = SOME s1`)) THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN
  MP_TAC(MATCH_MP pop_env_code_gc_fun_clock
    (ASSUME `wl_pop_env (t2:(A,C,FFI)wl_state) = SOME t1`)) THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "ih2" (MP_TAC o SPECL [`a:((A)word_loc)list`; `names:cutsets`;
     `prog:(A)wl_prog`; `args1:((A)word_loc)list`; `ss:num option`;
     `a0:(A)word_loc`; `l1:num`; `l2:num`; `y:(A,C,FFI)wl_state`;
     `envs:((A)word_loc)spt#((A)word_loc)spt`; `rh:(A)wl_prog`; `n:num list`;
     `a1:((A)word_loc)list`; `s1:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`result:((A)wl_result)option`;
    `new_state:(A,C,FFI)wl_state`; `reachable:1 spt`;
    `wl_set_vars n a1 (t1:(A,C,FFI)wl_state)`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC word_state_rel_set_vars THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `dest_result_loc (SOME (wl_Result (a0:(A)word_loc) a1)) SUBSET
                     domain (reachable:1 spt)` THEN
        REWRITE_TAC[dest_result_loc_def];
        FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
          `~(~(a0 = wl_Loc l1 l2:(A)word_loc) \/
             ~(LENGTH (a1:((A)word_loc)list) = LENGTH (n:num list)))`)) THEN
        MESON_TAC[]];
      REWRITE_TAC[wl_set_vars_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
      WELIMAUX_CODES_TAC
       [`wl_state_gc_fun (s:(A,C,FFI)wl_state) = wl_state_gc_fun (y:(A,C,FFI)wl_state)`;
        `wl_state_gc_fun (y:(A,C,FFI)wl_state) = wl_state_gc_fun (s1:(A,C,FFI)wl_state)`;
        `wl_state_code (s:(A,C,FFI)wl_state) = wl_state_code (y:(A,C,FFI)wl_state)`;
        `wl_state_code (y:(A,C,FFI)wl_state) = wl_state_code (s1:(A,C,FFI)wl_state)`;
        `wl_state_code (removed_state:(A,C,FFI)wl_state) =
         wl_state_code (t2:(A,C,FFI)wl_state)`;
        `wl_state_code (t2:(A,C,FFI)wl_state) = wl_state_code (t1:(A,C,FFI)wl_state)`]];
    REWRITE_TAC[]];;

let WELIMAUX_CALL_EXC_TAC : tactic =
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `hn:num` (X_CHOOSE_THEN `hh:(A)wl_prog`
      (X_CHOOSE_THEN `hl1:num` (X_CHOOSE_THEN `hl2:num` SUBST_ALL_TAC))))
    (ISPEC `handler:(num#(A)wl_prog#num#num)option` WELIMAUX_handler_cases) THEN
  REWRITE_TAC[option_CASE; pair_CASE] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    EXISTS_TAC `t2:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WELIMAUX_call_handler_facts) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  COND_CASES_TAC THENL [WELIMAUX_ERR_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL [ALL_TAC; WELIMAUX_ERR_TAC] THEN DISCH_TAC THEN
  REMOVE_THEN "ih3" (MP_TAC o SPECL [`a:((A)word_loc)list`; `rh:(A)wl_prog`;
     `l1:num`; `l2:num`; `n:num list`; `names:cutsets`; `prog:(A)wl_prog`;
     `args1:((A)word_loc)list`; `ss:num option`; `a0:(A)word_loc`; `hl1:num`;
     `hl2:num`; `envs:((A)word_loc)spt#((A)word_loc)spt`; `hh:(A)wl_prog`;
     `hn:num`; `a1:(A)word_loc`; `y:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`result:((A)wl_result)option`;
    `new_state:(A,C,FFI)wl_state`; `reachable:1 spt`;
    `wl_set_var hn a1 (t2:(A,C,FFI)wl_state)`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC word_state_rel_set_var THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `dest_result_loc (SOME (wl_Exception (a0:(A)word_loc) a1)) SUBSET
                   domain (reachable:1 spt)` THEN
      SPEC_TAC(`a1:(A)word_loc`,`a1:(A)word_loc`) THEN
      MATCH_MP_TAC word_loc_INDUCT THEN
      REWRITE_TAC[dest_result_loc_def; dest_word_loc_def; option_CASE; EMPTY_SUBSET];
      REWRITE_TAC[wl_set_var_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
      WELIMAUX_CODES_TAC
       [`wl_state_gc_fun (s:(A,C,FFI)wl_state) = wl_state_gc_fun (y:(A,C,FFI)wl_state)`;
        `wl_state_code (s:(A,C,FFI)wl_state) = wl_state_code (y:(A,C,FFI)wl_state)`;
        `wl_state_code (removed_state:(A,C,FFI)wl_state) =
         wl_state_code (t2:(A,C,FFI)wl_state)`]];
    REWRITE_TAC[]];;

let WELIMAUX_CALL_TAC : tactic =
  WELIMAUX_CALL_PRE_TAC THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    (ISPEC `ret:(num list#cutsets#(A)wl_prog#num#num)option` IL2AUX_ret_cases) THENL
   [WELIMAUX_CALL_TAIL_TAC;
    WELIMAUX_CALL_RET1_TAC THENL [WELIMAUX_CALL_RESULT_TAC; WELIMAUX_CALL_EXC_TAC]];;

let word_removal_lemma = prove
 (`!program (state:(A,C,FFI)wl_state) result new_state reachable removed_state.
     wl_evaluate (program,state) = (result,new_state) /\
     ~(result = SOME wl_Error) /\ word_state_rel reachable state removed_state /\
     gc_no_new_locs (wl_state_gc_fun state) /\
     wordConvs_no_install program /\ no_install_code (wl_state_code state) /\
     no_install_code (wl_state_code removed_state) /\
     domain (find_word_ref program) SUBSET domain reachable /\
     code_closed reachable (wl_state_code state)
     ==> ?s. wl_evaluate (program,removed_state) = (result,s) /\
             word_state_rel reachable new_state s /\
             dest_result_loc result SUBSET domain reachable`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THENL
   (map WELIMAUX_SIMPLE_TAC
      [WELIMAUX_safe_Skip; WELIMAUX_safe_Alloc; WELIMAUX_safe_StoreConsts;
       WELIMAUX_safe_Move; WELIMAUX_safe_Inst; WELIMAUX_safe_Assign;
       WELIMAUX_safe_Get; WELIMAUX_safe_Set; WELIMAUX_safe_OpCurrHeap;
       WELIMAUX_safe_Store; WELIMAUX_safe_Tick] @
    [WELIMAUX_MT_TAC; WELIMAUX_SEQ_TAC] @
    map WELIMAUX_SIMPLE_TAC
      [WELIMAUX_safe_Return; WELIMAUX_safe_Raise; WELIMAUX_safe_Break;
       WELIMAUX_safe_Continue] @
    [WELIMAUX_IF_TAC; WELIMAUX_LOOP_TAC; WELIMAUX_LOCVALUE_TAC; WELIMAUX_INSTALL_TAC] @
    map WELIMAUX_SIMPLE_TAC
      [WELIMAUX_safe_CodeBufferWrite; WELIMAUX_safe_DataBufferWrite;
       WELIMAUX_safe_FFI; WELIMAUX_safe_ShareInst] @
    [WELIMAUX_CALL_TAC]));;

(* ------------------------------------------------------------------------- *)
(* word_removal_thm                                                          *)
(* ------------------------------------------------------------------------- *)

let WELIMAUX_ALOOKUP_remove = prove
 (`!(reachable:B spt) (l:(num#C)list) k.
     ALOOKUP (remove_word_code reachable l) k =
     if IS_SOME (lookup k reachable) then ALOOKUP l k else NONE`,
  GEN_TAC THEN REWRITE_TAC[remove_word_code_def] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[FILTER; ALOOKUP_DEF; COND_ID] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ALOOKUP_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let word_removal_thm = prove
 (`!start (state:(A,C,FFI)wl_state) result new_state (r:B) reachable code1.
     wl_evaluate (wl_Call NONE (SOME start) [0] NONE, state) = (result,new_state) /\
     ~(result = SOME wl_Error) /\ wl_state_code state = fromAList code1 /\
     domain (find_loc_state state) SUBSET domain reachable /\
     gc_no_new_locs (wl_state_gc_fun state) /\
     reachable = closure_spt (insert start one LN) (analyse_word_code code1) /\
     ALL_DISTINCT (MAP FST code1) /\ no_install_code (wl_state_code state)
     ==> ?s. wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
               wl_state_code_fupd (K (fromAList (remove_word_code reachable code1)))
                 state) = (result,s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`;
    `state:(A,C,FFI)wl_state`; `result:((A)wl_result)option`;
    `new_state:(A,C,FFI)wl_state`; `reachable:1 spt`;
    `wl_state_code_fupd (K (fromAList (remove_word_code (reachable:1 spt)
       (code1:(num#num#(A)wl_prog)list)))) (state:(A,C,FFI)wl_state)`]
    word_removal_lemma) THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`analyse_word_code (code1:(num#num#(A)wl_prog)list)`;
                 `insert start one (LN:1 spt)`] closure_spt_thm) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th)))) THEN
  DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [(* word_state_rel *)
    REWRITE_TAC[word_state_rel_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[word_elimProof_code_rel_def; lookup_fromAList;
                WELIMAUX_ALOOKUP_remove] THEN
    SIMP_TAC[domain_lookup; IS_SOME_EXISTS];
    (* no_install *)
    REWRITE_TAC[wordConvs_no_install_def; distinctness "wl_prog"] THEN
    CASE_REWRITE_TAC[];
    (* no_install_code *)
    UNDISCH_TAC `no_install_code (wl_state_code (state:(A,C,FFI)wl_state))` THEN
    ASM_REWRITE_TAC[] THEN SIMP[] THEN
    REWRITE_TAC[no_install_code_def; lookup_fromAList; WELIMAUX_ALOOKUP_remove] THEN
    MESON_TAC[option_DISTINCT];
    (* find_word_ref *)
    ASM_REWRITE_TAC[find_word_ref_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[domain_union; domain_insert; domain_def; UNION_EMPTY;
                SING_SUBSET; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    MESON_TAC[is_reachable_def; RTC_REFL];
    (* code_closed *)
    REWRITE_TAC[code_closed_def] THEN EXISTS_TAC `code1:(num#num#(A)wl_prog)list` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    MESON_TAC[is_reachable_def; RTC_TRANS]]);;
