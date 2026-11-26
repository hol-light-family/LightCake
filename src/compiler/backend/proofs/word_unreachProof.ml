(* ========================================================================= *)
(* word_unreachProof: port of HOL4 compiler/backend/proofs/                  *)
(* word_unreachProofScript.sml (CakeML v3479).                               *)
(* Correctness proof for word_unreach.                                       *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The names of wordLang, wordSem, wordProps and word_unreach are those of *)
(*   their files (wl_evaluate, wl_Seq, word_unreach_merge_moves, ...): HOL4  *)
(*   s.f is wl_state_f s, s with f := v is wl_state_f_fupd (K v) s.          *)
(* - copy_vars is word_unreachProof_copy_vars (doc/names.tsv).               *)
(* - evaluate_Loop_body_eq comes before evaluate_Seq_assoc_right_lemma,     *)
(*   whose Loop case (HOL4 suspend/Resume) uses it.                          *)
(* - WPROOF1AUX_WU_ names are local helpers.                                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/word_unreach.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;

type_invention_error := true;;

(* -- proofs about semantics -- *)

(* HOL4: evaluate_Skip_Seq *)

let word_unreachProof_evaluate_Skip_Seq = prove
 (`wl_evaluate (wl_Seq wl_Skip p,s:(A,C,FFI)wl_state) = wl_evaluate (p,s)`,
  SIMP[wl_evaluate_def]);;

(* HOL4: evaluate_Seq_Skip *)

let word_unreachProof_evaluate_Seq_Skip = prove
 (`!p1 (s:(A,C,FFI)wl_state).
     wl_evaluate (wl_Seq p1 wl_Skip,s) = wl_evaluate (p1,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN PAIRARG_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4: evaluate_Seq_assoc *)

let word_unreachProof_evaluate_Seq_assoc = prove
 (`wl_evaluate (wl_Seq p1 (wl_Seq p2 p3), s:(A,C,FFI)wl_state) =
   wl_evaluate (wl_Seq (wl_Seq p1 p2) p3, s)`,
  REWRITE_TAC[wl_evaluate_def] THEN
  MP_TAC(ISPEC `wl_evaluate (p1:(A)wl_prog,s:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r1:((A)wl_result)option`; `t1:(A,C,FFI)wl_state`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[pair_CASE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPEC `wl_evaluate (p2:(A)wl_prog,t1:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r2:((A)wl_result)option`; `t2:(A,C,FFI)wl_state`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[pair_CASE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[pair_CASE]);;

let ALL_DISTINCT_merge_moves = prove
 (`ALL_DISTINCT (MAP FST (word_unreach_merge_moves l1 l2))`,
  REWRITE_TAC[word_unreach_merge_moves_def; LET_DEF; LET_END_DEF] THEN
  MATCH_ACCEPT_TAC(GEN_ALL(REWRITE_RULE[ALL_DISTINCT; APPEND_NIL]
    (ISPECL [`ls:(num#num)list`; `[]:num list`] anub_all_distinct_keys))));;

(* HOL4: copy_vars_def *)

let word_unreachProof_copy_vars_def = cake_def
  `(word_unreachProof_copy_vars [] (from:(A)spt) (to:(A)spt) = to) /\
   (word_unreachProof_copy_vars (CONS (l,r) rest) from to =
      insert l (THE (lookup r from)) (word_unreachProof_copy_vars rest from to))`;;

let copy_vars_append = prove
 (`!xs ys (from:(A)spt) to.
     word_unreachProof_copy_vars (APPEND xs ys) from to =
     word_unreachProof_copy_vars xs from (word_unreachProof_copy_vars ys from to)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; word_unreachProof_copy_vars_def] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  ASM_REWRITE_TAC[word_unreachProof_copy_vars_def]);;

let WPROOF1AUX_WU_alist_insert_copy_vars = prove
 (`!moves x (t:((A)word_loc)spt) (s:(A,C,FFI)wl_state).
     wl_get_vars (MAP SND moves) s = SOME x ==>
     alist_insert (MAP FST moves) x t =
     word_unreachProof_copy_vars moves (wl_state_locals s) t`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP; wl_get_vars_def; option_INJ] THEN REPEAT STRIP_TAC THEN
    RVEQ_TAC THEN REWRITE_TAC[alist_insert_def; word_unreachProof_copy_vars_def];
    ALL_TAC] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN
  REWRITE_TAC[MAP; wl_get_vars_def] THEN REPEAT GEN_TAC THEN
  CASES_ON `wl_get_var b (s:(A,C,FFI)wl_state)` THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `wl_get_vars (MAP SND (t:(num#num)list)) (s:(A,C,FFI)wl_state)` THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[alist_insert_def; word_unreachProof_copy_vars_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  SIMP[]);;

let evaluate_Move = prove
 (CASE_TERM
  `wl_evaluate (wl_Move pri moves,s:(A,C,FFI)wl_state) =
   if ALL_DISTINCT (MAP FST moves) then
     match wl_get_vars (MAP SND moves) s with
       NONE -> (SOME wl_Error,s)
     | SOME l -> (NONE, wl_state_locals_fupd
                          (combin_K (word_unreachProof_copy_vars moves (wl_state_locals s)
                                (wl_state_locals s))) s)
   else (SOME wl_Error,s)`,
  REWRITE_TAC[wl_evaluate_def] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  CASES_ON `wl_get_vars (MAP SND (moves:(num#num)list)) (s:(A,C,FFI)wl_state)` THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_set_vars_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF1AUX_WU_alist_insert_copy_vars th]));;

let copy_vars_MEM_acc = prove
 (`!xs acc n (w:A).
     MEM n acc ==>
     insert n w (word_unreachProof_copy_vars (anub xs acc) s t) =
     insert n w (word_unreachProof_copy_vars (anub xs (FILTER (\x. ~(n = x)) acc)) s t)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[anub_def] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `v:num`] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[anub_def; MEM_FILTER] THEN
  ASM_CASES_TAC `n:num = k` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_REWRITE_TAC[word_unreachProof_copy_vars_def; insert_shadow] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `MEM (k:num) acc`)]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (k:num) (FILTER (\x. ~(k = x)) acc)`;
                                  `k:num`; `w:A`]) THEN
    REWRITE_TAC[MEM; FILTER; FILTER_FILTER] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[word_unreachProof_copy_vars_def] THEN
  ASM_SIMP_TAC[insert_swap] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (k:num) acc`; `n:num`; `w:A`]) THEN
  ASM_REWRITE_TAC[MEM; FILTER]);;

let copy_vars_anub = prove
 (`word_unreachProof_copy_vars (anub xs []) =
   (word_unreachProof_copy_vars xs:(A)spt->(A)spt->(A)spt)`,
  SPEC_TAC(`xs:(num#num)list`,`xs:(num#num)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[anub_def; MEM] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `v:num`] THEN
  REWRITE_TAC[anub_def; MEM; FUN_EQ_THM; word_unreachProof_copy_vars_def] THEN
  MAP_EVERY X_GEN_TAC [`s:(A)spt`; `t0:(A)spt`] THEN
  MP_TAC(ISPECL [`t:(num#num)list`; `[k:num]`; `k:num`; `THE (lookup v (s:(A)spt))`]
    (INST [`s:(A)spt`,`s:(A)spt`; `t0:(A)spt`,`t:(A)spt`] copy_vars_MEM_acc)) THEN
  REWRITE_TAC[MEM; FILTER] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

let lookup_copy_vars_ignore = prove
 (`!l1 h1 (x:(A)spt) y.
     ALOOKUP l1 h1 = NONE ==>
     lookup h1 (word_unreachProof_copy_vars l1 x y) = lookup h1 y`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[word_unreachProof_copy_vars_def] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[ALOOKUP_DEF; word_unreachProof_copy_vars_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  ASM_SIMP_TAC[lookup_insert]);;

let lookup_copy_vars = prove
 (`!l1 h1 y (s:(A)spt) t z.
     ALOOKUP l1 h1 = SOME y /\
     lookup h1 (word_unreachProof_copy_vars l1 s t) = SOME z ==>
     THE (lookup y s) = z`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_DEF; option_DISTINCT] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[ALOOKUP_DEF; word_unreachProof_copy_vars_def; lookup_insert] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
  ASM_MESON_TAC[]);;

(* HOL4 [local] *)

let get_vars_IS_SOME_lookup = prove
 (`!xs (s:(A,C,FFI)wl_state).
     (?ws. wl_get_vars xs s = SOME ws) <=>
     ALL (\x. IS_SOME (lookup x (wl_state_locals s))) xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wl_get_vars_def; ALL; option_INJ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[wl_get_var_def] THEN
  CASES_ON `lookup h (wl_state_locals (s:(A,C,FFI)wl_state))` THEN
  CAKE_REWRITE_TAC[IS_SOME_DEF] THEN REWRITE_TAC[option_DISTINCT] THEN
  FIRST_X_ASSUM(fun th -> if is_forall (concl th) then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  CASES_ON `wl_get_vars t (s:(A,C,FFI)wl_state)` THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let IMP_EVERY_MAP_SND_anub = prove
 (`!xs acc (p:B->bool).
     ALL p (MAP SND xs) ==> ALL p (MAP SND (anub (xs:(A#B)list) acc))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[anub_def; MAP; ALL] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[anub_def; MAP; ALL; SND] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[MAP; ALL]);;

(* the moves of merge_moves that come from l2 *)

let WPROOF1AUX_WU_copy_vars_l2 = prove
 (CASE_TERM
  `!l2 (l1:(num#num)list) (L:(A)spt) t.
     ALL (\y. IS_SOME (lookup y (word_unreachProof_copy_vars l1 L L))) (MAP SND l2) ==>
     word_unreachProof_copy_vars
       (MAP (\p. match p with
                   (x,y) -> (match ALOOKUP l1 y with
                               NONE -> (x,y)
                             | SOME v -> (x,v))) l2) L t =
     word_unreachProof_copy_vars l2 (word_unreachProof_copy_vars l1 L L) t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; word_unreachProof_copy_vars_def] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`; `l1:(num#num)list`; `L:(A)spt`; `t0:(A)spt`] THEN
  REWRITE_TAC[MAP; ALL; SND; pair_CASE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l1:(num#num)list`; `L:(A)spt`; `t0:(A)spt`] o
                check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CASES_ON `ALOOKUP (l1:(num#num)list) y` THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[word_unreachProof_copy_vars_def] THENL
   [ASM_SIMP_TAC[lookup_copy_vars_ignore];
    AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `IS_SOME (lookup y (word_unreachProof_copy_vars (l1:(num#num)list) L
                                      (L:(A)spt)))` THEN
    CASES_ON `lookup y (word_unreachProof_copy_vars (l1:(num#num)list) L (L:(A)spt))` THEN
    REWRITE_TAC[IS_SOME_DEF; THE_DEF] THEN
    MATCH_MP_TAC lookup_copy_vars THEN ASM_MESON_TAC[]]);;

let WPROOF1AUX_WU_merge_moves_reads = prove
 (`!l1 l2 (L:(A)spt).
     ALL (\x. IS_SOME (lookup x L)) (MAP SND l1) /\
     ALL (\y. IS_SOME (lookup y (word_unreachProof_copy_vars l1 L L))) (MAP SND l2) ==>
     ALL (\x. IS_SOME (lookup x L)) (MAP SND (word_unreach_merge_moves l1 l2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_unreach_merge_moves_def; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN MATCH_MP_TAC IMP_EVERY_MAP_SND_anub THEN
  ASM_REWRITE_TAC[MAP_APPEND; ALL_APPEND] THEN
  UNDISCH_TAC `ALL (\y. IS_SOME (lookup y (word_unreachProof_copy_vars l1 L (L:(A)spt))))
                   (MAP SND (l2:(num#num)list))` THEN
  SPEC_TAC(`l2:(num#num)list`,`l2:(num#num)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN REWRITE_TAC[pair_CASE; SND] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  CASES_ON `ALOOKUP (l1:(num#num)list) y` THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[SND] THENL
   [UNDISCH_TAC `IS_SOME (lookup y (word_unreachProof_copy_vars l1 L (L:(A)spt)))` THEN
    ASM_SIMP_TAC[lookup_copy_vars_ignore];
    UNDISCH_TAC `ALL (\x. IS_SOME (lookup x (L:(A)spt))) (MAP SND (l1:(num#num)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `(y:num,a:num)` THEN REWRITE_TAC[SND] THEN
    MATCH_MP_TAC ALOOKUP_MEM THEN ASM_REWRITE_TAC[]]);;


let WPROOF1AUX_WU_is_eval_eq th =
  let c = concl th in
  is_eq c && (let l = lhs c in is_comb l && is_const (rator l) &&
                               fst(dest_const(rator l)) = "wl_evaluate");;

(* case split on the first subterm of the goal whose head is the constant  *)
(* named c and which has no bound variables                                 *)

let WPROOF1AUX_WU_CASES_HEAD_TAC (c:string) : tactic = fun (asl,w as g) ->
  let fvs = frees w in
  let ok t = let h,_ = strip_comb t in
             is_const h && fst(dest_const h) = c &&
             subset (frees t) (fvs @ freesl (map (concl o snd) asl)) in
  let t = find_term ok w in
  (CASES_ON t THEN CAKE_REWRITE_TAC[]) g;;


(* the clause of wl_evaluate_def for the constructor named c *)

let WPROOF1AUX_WU_eval_clause (c:string) =
  find (fun th -> let l = lhs (snd (strip_forall (concl th))) in
                  let p = fst (dest_pair (rand l)) in
                  fst (dest_const (fst (strip_comb p))) = c)
       (CONJUNCTS wl_evaluate_def);;

let merge_moves_Skip = prove
 (`!l1 l2 (s:(A,C,FFI)wl_state) res s1.
     wl_evaluate (wl_Seq (wl_Move n1 l1) (wl_Move n2 l2),s) = (res,s1) /\
     ~(res = SOME wl_Error) ==>
     wl_evaluate (wl_Move m (word_unreach_merge_moves l1 l2),s) = (res,s1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WPROOF1AUX_WU_eval_clause "wl_Seq"; evaluate_Move] THEN
  ASM_CASES_TAC `ALL_DISTINCT (MAP FST (l1:(num#num)list))` THEN
  ASM_REWRITE_TAC[pair_CASE; option_DISTINCT; PAIR_EQ] THENL
   [ALL_TAC; MESON_TAC[]] THEN
  CASES_ON `wl_get_vars (MAP SND (l1:(num#num)list)) (s:(A,C,FFI)wl_state)` THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[pair_CASE; PAIR_EQ] THENL [MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `ALL_DISTINCT (MAP FST (l2:(num#num)list))` THEN
  ASM_REWRITE_TAC[PAIR_EQ] THENL [ALL_TAC; MESON_TAC[]] THEN
  WPROOF1AUX_WU_CASES_HEAD_TAC "wl_get_vars" THEN REWRITE_TAC[PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[ALL_DISTINCT_merge_moves] THEN
  SUBGOAL_THEN
   `ALL (\x. IS_SOME (lookup x (wl_state_locals (s:(A,C,FFI)wl_state))))
        (MAP SND (l1:(num#num)list)) /\
    ALL (\y. IS_SOME (lookup y (word_unreachProof_copy_vars l1 (wl_state_locals s)
                                   (wl_state_locals s))))
        (MAP SND (l2:(num#num)list))`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`MAP SND (l1:(num#num)list)`; `s:(A,C,FFI)wl_state`]
                    get_vars_IS_SOME_lookup) THEN ASM_MESON_TAC[];
      MP_TAC(ISPECL [`MAP SND (l2:(num#num)list)`;
                     `wl_state_locals_fupd (combin_K (word_unreachProof_copy_vars l1
                        (wl_state_locals s) (wl_state_locals s))) (s:(A,C,FFI)wl_state)`]
                    get_vars_IS_SOME_lookup) THEN
      SIMP[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`MAP SND (word_unreach_merge_moves l1 l2)`; `s:(A,C,FFI)wl_state`]
                get_vars_IS_SOME_lookup) THEN
  ASM_SIMP_TAC[WPROOF1AUX_WU_merge_moves_reads] THEN
  DISCH_THEN(X_CHOOSE_THEN `ws:((A)word_loc)list` SUBST1_TAC) THEN
  CAKE_REWRITE_TAC[] THEN SIMP[] THEN
  REWRITE_TAC[word_unreach_merge_moves_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[copy_vars_anub; copy_vars_append] THEN
  MATCH_MP_TAC WPROOF1AUX_WU_copy_vars_l2 THEN ASM_REWRITE_TAC[]);;

let merge_moves_thm = prove
 (`!p l1 l2 (s:(A,C,FFI)wl_state) res s1.
     wl_evaluate (wl_Seq (wl_Move n1 l1) (wl_Seq (wl_Move n2 l2) p),s) = (res,s1) /\
     ~(res = SOME wl_Error) ==>
     wl_evaluate (wl_Seq (wl_Move m (word_unreach_merge_moves l1 l2)) p,s) = (res,s1)`,
  REWRITE_TAC[word_unreachProof_evaluate_Seq_assoc] THEN
  ONCE_REWRITE_TAC[WPROOF1AUX_WU_eval_clause "wl_Seq"] THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `wl_evaluate (wl_Seq (wl_Move n1 l1) (wl_Move n2 l2),s:(A,C,FFI)wl_state)`
               PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res2:((A)wl_result)option`
    (X_CHOOSE_THEN `s2:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(res2 = SOME (wl_Error:(A)wl_result))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
    ASM_REWRITE_TAC[option_DISTINCT; PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`l1:(num#num)list`; `l2:(num#num)list`; `s:(A,C,FFI)wl_state`;
                `res2:((A)wl_result)option`; `s2:(A,C,FFI)wl_state`]
               (INST [`m:num`,`m:num`] merge_moves_Skip)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[pair_CASE]);;

let WPROOF1AUX_WU_dest_Seq_Move = prove
 (`!p:(A)wl_prog n l rest.
     dest_Seq_Move p = SOME (n,l,rest) <=>
     (p = wl_Move n l /\ rest = wl_Skip) \/ p = wl_Seq (wl_Move n l) rest`,
  GEN_TAC THEN CASES_ON `p:(A)wl_prog` THEN REWRITE_TAC[dest_Seq_Move_def] THEN
  CAKE_REWRITE_TAC[] THEN TRY(CASES_ON `a0:(A)wl_prog` THEN
                              REWRITE_TAC[dest_Seq_Move_def] THEN CAKE_REWRITE_TAC[]) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN MESON_TAC[]);;

let WPROOF1AUX_WU_seq_not_none = prove
 (`!p1 p2 (s:(A,C,FFI)wl_state).
     ~(FST (wl_evaluate (p1, s)) = NONE) ==>
     wl_evaluate (wl_Seq p1 p2, s) = wl_evaluate (p1, s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[WPROOF1AUX_WU_eval_clause "wl_Seq"] THEN
  MP_TAC(ISPEC `wl_evaluate (p1:(A)wl_prog, s:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE; FST] THEN SIMP_TAC[]);;

(* the evaluations of Raise, Return, Break and Continue never return NONE: *)
(* Seq of such a program is the program                                     *)

let WPROOF1AUX_WU_NOT_NONE_TAC : tactic = fun (asl,w as g) ->
  let ev = lhs (lhand (lhand w)) in
  let p1 = rand (rator (fst (dest_pair (rand ev)))) in
  let tm = vsubst [p1, `pp:(A)wl_prog`]
             `~(FST (wl_evaluate (pp:(A)wl_prog, s:(A,C,FFI)wl_state)) = NONE)` in
  (SUBGOAL_THEN tm (fun th -> REWRITE_TAC[MATCH_MP WPROOF1AUX_WU_seq_not_none th]) THENL
    [ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
     REPEAT (TOP_CASE_TAC THEN SIMP[]) THEN NO_TAC;
     STRIP_TAC THEN ASM_REWRITE_TAC[]]) g;;

let evaluate_SimpSeq = prove
 (`wl_evaluate (wl_Seq p1 p2,s:(A,C,FFI)wl_state) = (res,s1) /\ ~(res = SOME wl_Error) ==>
   wl_evaluate (SimpSeq p1 p2,s) = (res,s1)`,
  REWRITE_TAC[SimpSeq_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[word_unreachProof_evaluate_Seq_Skip] THEN MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `p1:(A)wl_prog` THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[word_unreachProof_evaluate_Skip_Seq] THEN
  TRY(STRIP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(WPROOF1AUX_WU_NOT_NONE_TAC THEN NO_TAC) THEN
  (* Move *)
  CASES_ON `dest_Seq_Move (p2:(A)wl_prog)` THEN CAKE_REWRITE_TAC[] THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `a:num#(num#num)list#(A)wl_prog` BASICAUX_TUPLE3) THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:num` (X_CHOOSE_THEN `l2:(num#num)list`
    (X_CHOOSE_THEN `rest:(A)wl_prog` SUBST_ALL_TAC))) THEN
  CAKE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[WPROOF1AUX_WU_dest_Seq_Move]) THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN
    MATCH_MP_TAC (INST [`a0:num`,`n1:num`; `n2:num`,`n2:num`] merge_moves_Skip) THEN
    ASM_REWRITE_TAC[];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
     [MATCH_MP_TAC (INST [`a0:num`,`n1:num`; `n2:num`,`n2:num`] merge_moves_Skip) THEN
      ONCE_REWRITE_TAC[GSYM word_unreachProof_evaluate_Seq_Skip] THEN
      ASM_REWRITE_TAC[GSYM word_unreachProof_evaluate_Seq_assoc];
      MATCH_MP_TAC (INST [`a0:num`,`n1:num`; `n2:num`,`n2:num`] merge_moves_thm) THEN
      ASM_REWRITE_TAC[]]]);;

(* HOL4 [local] *)

let push_env_handler = prove
 (CASE_TERM
  `wl_push_env x' (match handler with
                     NONE -> NONE
                   | SOME (y1,q2,y2,y3) -> SOME (y1,Seq_assoc_right q2 wl_Skip,y2,y3))
                  (wl_dec_clock (s:(A,C,FFI)wl_state)) =
   wl_push_env x' handler (wl_dec_clock s)`,
  CASES_ON `handler:(num#(A)wl_prog#num#num)option` THEN CAKE_REWRITE_TAC[] THEN
  SPEC_TAC(`a:num#(A)wl_prog#num#num`,`a:num#(A)wl_prog#num#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_push_env_def]);;

(* HOL4 [local] *)

let evaluate_Loop_body_eq = prove
 (`(!(s:(A,C,FFI)wl_state) res s1.
      wl_evaluate (p1:(A)wl_prog, s) = (res, s1) /\ ~(res = SOME wl_Error) ==>
      wl_evaluate (p2:(A)wl_prog, s) = (res, s1)) ==>
   !(s:(A,C,FFI)wl_state) res s1.
      wl_evaluate (wl_Loop names p1 exit_names, s) = (res, s1) /\
      ~(res = SOME wl_Error) ==>
      wl_evaluate (wl_Loop names p2 exit_names, s) = (res, s1)`,
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!n (s:(A,C,FFI)wl_state) res s1. wl_state_clock s = n ==>
      wl_evaluate (wl_Loop names p1 exit_names, s) = (res, s1) /\
      ~(res = SOME wl_Error) ==>
      wl_evaluate (wl_Loop names p2 exit_names, s) = (res, s1)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`s:(A,C,FFI)wl_state`; `res:((A)wl_result)option`;
                       `s1:(A,C,FFI)wl_state`] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[WPROOF1AUX_WU_eval_clause "wl_Loop"] THEN
  CASES_ON `wl_cut_state (names,LN) (s:(A,C,FFI)wl_state)` THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THENL [MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `wl_evaluate (p1:(A)wl_prog,a:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)wl_result)option` (X_CHOOSE_THEN `t:(A,C,FFI)wl_state`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(r = SOME (wl_Error:(A)wl_result))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
    SIMP[wl_cont_loop_def; wl_exit_loop_def; PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_evaluate (p2:(A)wl_prog,a:(A,C,FFI)wl_state) = (r,t)` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[pair_CASE] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_STOP_def] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `wl_state_clock (wl_dec_clock (t:(A,C,FFI)wl_state))` o
                check (is_forall o concl)) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `wl_state_clock (a:(A,C,FFI)wl_state) = wl_state_clock (s:(A,C,FFI)wl_state)`
      ASSUME_TAC THENL
     [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP cut_state_const) THEN ASM_REWRITE_TAC[] THEN
      SIMP[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP wl_evaluate_clock o
                check (fun th -> concl th = `wl_evaluate (p1:(A)wl_prog,a:(A,C,FFI)wl_state) =
                                             (r,t)`)) THEN
    REWRITE_TAC[wl_dec_clock_def] THEN SIMP[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`wl_dec_clock (t:(A,C,FFI)wl_state)`;
                             `res:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[]);;

let WPROOF1AUX_WU_SKIP_TAC : tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_unreach_Seq_assoc_right_def; word_unreachProof_evaluate_Skip_Seq] THEN
  MESON_TAC[];;

let WPROOF1AUX_WU_SEQ_TAC : tactic =
  MAP_EVERY X_GEN_TAC [`q1:(A)wl_prog`; `q2:(A)wl_prog`; `acc:(A)wl_prog`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[word_unreach_Seq_assoc_right_def] THEN
  USE_THEN "ih1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `wl_evaluate (wl_Seq (wl_Seq q1 q2) acc,s:(A,C,FFI)wl_state) = res,s1` THEN
  REWRITE_TAC[GSYM word_unreachProof_evaluate_Seq_assoc] THEN
  ONCE_REWRITE_TAC[WPROOF1AUX_WU_eval_clause "wl_Seq"] THEN
  MP_TAC(ISPEC `wl_evaluate (q1:(A)wl_prog,s:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)wl_result)option` (X_CHOOSE_THEN `t:(A,C,FFI)wl_state`
    SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  DISCH_TAC THEN USE_THEN "ih2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];;

let WPROOF1AUX_WU_seq_cong = prove
 (`!p q acc (s:(A,C,FFI)wl_state).
     wl_evaluate (p, s) = wl_evaluate (q, s) ==>
     wl_evaluate (wl_Seq p acc, s) = wl_evaluate (wl_Seq q acc, s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[WPROOF1AUX_WU_eval_clause "wl_Seq"] THEN
  ASM_REWRITE_TAC[]);;

let WPROOF1AUX_WU_seq_not_error = prove
 (`!p acc (s:(A,C,FFI)wl_state) res s1.
     wl_evaluate (wl_Seq p acc, s) = (res, s1) /\ ~(res = SOME wl_Error) ==>
     ~(FST (wl_evaluate (p, s)) = SOME wl_Error)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[WPROOF1AUX_WU_eval_clause "wl_Seq"] THEN
  MP_TAC(ISPEC `wl_evaluate (p:(A)wl_prog,s:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)wl_result)option` (X_CHOOSE_THEN `t:(A,C,FFI)wl_state`
    SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE; FST] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_DISTINCT; PAIR_EQ] THEN MESON_TAC[]);;

let WPROOF1AUX_WU_ih_use = prove
 (`!q q'.
     (!(s:(A,C,FFI)wl_state) res s1.
        wl_evaluate (wl_Seq q wl_Skip, s) = (res, s1) /\ ~(res = SOME wl_Error) ==>
        wl_evaluate (q', s) = (res, s1)) ==>
     !(s:(A,C,FFI)wl_state). ~(FST (wl_evaluate (q, s)) = SOME wl_Error) ==>
         wl_evaluate (q', s) = wl_evaluate (q, s)`,
  REWRITE_TAC[word_unreachProof_evaluate_Seq_Skip] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `wl_evaluate (q:(A)wl_prog,s:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)wl_result)option` (X_CHOOSE_THEN `t:(A,C,FFI)wl_state`
    (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[]);;

(* the shape of the If, MustTerminate and Loop cases: SimpSeq of the       *)
(* transformed program, whose evaluation is the original one              *)

let WPROOF1AUX_WU_SIMPSEQ_CONG_TAC : tactic =
  REWRITE_TAC[word_unreach_Seq_assoc_right_def] THEN CAKE_REWRITE_TAC[] THEN
  MATCH_MP_TAC evaluate_SimpSeq THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> if WPROOF1AUX_WU_is_eval_eq th then
    (ASSUME_TAC(MATCH_MP WPROOF1AUX_WU_seq_not_error (CONJ th
       (ASSUME `~(res = SOME (wl_Error:(A)wl_result))`))) THEN
     MP_TAC th) else NO_TAC) THEN
  MATCH_MP_TAC(MESON[] `(a:B) = b ==> b = c ==> a = c`) THEN
  MATCH_MP_TAC WPROOF1AUX_WU_seq_cong;;

let WPROOF1AUX_WU_IF_TAC : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP WPROOF1AUX_WU_ih_use)) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN WPROOF1AUX_WU_SIMPSEQ_CONG_TAC THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[WPROOF1AUX_WU_eval_clause "wl_If"] THEN
  REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[FST]) THEN ASM_SIMP_TAC[];;

(* split the first evaluation wl_evaluate (p,X) of the goal (no bound        *)
(* variables) into the pair (r,t), keeping the equation                     *)

let WPROOF1AUX_WU_EVAL_SPLIT_TAC (p:term) (r:term) (t:term) : tactic = fun (asl,w as g) ->
  let fvs = frees w @ freesl (map (concl o snd) asl) in
  let ok tm = is_comb tm && is_const (rator tm) &&
              fst(dest_const(rator tm)) = "wl_evaluate" &&
              fst(dest_pair(rand tm)) = p && subset (frees tm) fvs in
  let tm = find_term ok w in
  (MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
   X_GEN_TAC r THEN X_GEN_TAC t THEN DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE]) g;;

(* with an assumption wl_evaluate (q,S) = (r,t), ~(r = SOME wl_Error) and an *)
(* induction hypothesis from WPROOF1AUX_WU_ih_use for q, rewrite the        *)
(* evaluation of the transformed q at S                                      *)

let WPROOF1AUX_WU_IH_RW_TAC (q:term) : tactic =
  FIRST_ASSUM(fun th ->
    if WPROOF1AUX_WU_is_eval_eq th && fst(dest_pair(rand(lhs(concl th)))) = q then
      let st = snd(dest_pair(rand(lhs(concl th)))) in
      let r = fst(dest_pair(rhs(concl th))) in
      let nerr = ASSUME (mk_neg(mk_eq(r, `SOME (wl_Error:(A)wl_result)`))) in
      FIRST_ASSUM(fun ih ->
        if is_forall (concl ih) &&
           can (find_term (fun t -> t = q)) (concl ih) then
          MP_TAC(SPEC st ih) THEN REWRITE_TAC[th; FST; nerr] THEN
          DISCH_THEN SUBST1_TAC
        else NO_TAC)
    else NO_TAC);;

let WPROOF1AUX_WU_MT_TAC : tactic =
  MAP_EVERY X_GEN_TAC [`q:(A)wl_prog`; `acc:(A)wl_prog`] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP WPROOF1AUX_WU_ih_use) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN WPROOF1AUX_WU_SIMPSEQ_CONG_TAC THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[WPROOF1AUX_WU_eval_clause "MustTerminate"] THEN
  COND_CASES_TAC THEN REWRITE_TAC[FST] THEN
  WPROOF1AUX_WU_EVAL_SPLIT_TAC `q:(A)wl_prog` `r:((A)wl_result)option`
    `t:(A,C,FFI)wl_state` THEN
  ASM_CASES_TAC `r = SOME (wl_Error:(A)wl_result)` THENL
   [ASM_REWRITE_TAC[option_INJ] THEN SIMP[]; ALL_TAC] THEN
  DISCH_TAC THEN WPROOF1AUX_WU_IH_RW_TAC `q:(A)wl_prog` THEN REWRITE_TAC[pair_CASE];;

let WPROOF1AUX_WU_LOOP_TAC : tactic =
  MAP_EVERY X_GEN_TAC [`names:(1)spt`; `body:(A)wl_prog`; `exit_names:(1)spt`;
                       `acc:(A)wl_prog`] THEN
  REWRITE_TAC[word_unreachProof_evaluate_Seq_Skip] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (INST [`names:(1)spt`,`names:(1)spt`;
                                          `exit_names:(1)spt`,`exit_names:(1)spt`]
                                         evaluate_Loop_body_eq)) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN WPROOF1AUX_WU_SIMPSEQ_CONG_TAC THEN
  POP_ASSUM MP_TAC THEN
  MP_TAC(ISPEC `wl_evaluate (wl_Loop names body exit_names,s:(A,C,FFI)wl_state)`
               PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)wl_result)option` (X_CHOOSE_THEN `t:(A,C,FFI)wl_state`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN ASM_REWRITE_TAC[];;

let WPROOF1AUX_WU_push_env_some = prove
 (`wl_push_env envs (SOME (n, Seq_assoc_right p wl_Skip, l1, l2)) (s:(A,C,FFI)wl_state) =
   wl_push_env envs (SOME (n,p,l1,l2)) s`,
  REWRITE_TAC[wl_push_env_def]);;

let WPROOF1AUX_WU_CALL0_TAC : tactic =
  MAP_EVERY X_GEN_TAC [`ret_prog:(num list#cutsets#(A)wl_prog#num#num)option`;
                       `dest:num option`; `args:num list`;
                       `handler:(num#(A)wl_prog#num#num)option`; `acc:(A)wl_prog`] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
   (X_CHOOSE_THEN `rv:num list#cutsets#(A)wl_prog#num#num` SUBST_ALL_TAC)
   (ISPEC `ret_prog:(num list#cutsets#(A)wl_prog#num#num)option` (cases "option")) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
   (X_CHOOSE_THEN `hv:num#(A)wl_prog#num#num` SUBST_ALL_TAC)
   (ISPEC `handler:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
  TRY(MP_TAC(ISPEC `rv:num list#cutsets#(A)wl_prog#num#num` BASICAUX_TUPLE5) THEN
      DISCH_THEN(X_CHOOSE_THEN `x1:num list` (X_CHOOSE_THEN `x2:cutsets`
        (X_CHOOSE_THEN `q1:(A)wl_prog` (X_CHOOSE_THEN `x3:num`
          (X_CHOOSE_THEN `x4:num` SUBST_ALL_TAC)))))) THEN
  TRY(MP_TAC(ISPEC `hv:num#(A)wl_prog#num#num` BASICAUX_TUPLE4) THEN
      DISCH_THEN(X_CHOOSE_THEN `y1:num` (X_CHOOSE_THEN `q2:(A)wl_prog`
        (X_CHOOSE_THEN `y2:num` (X_CHOOSE_THEN `y3:num` SUBST_ALL_TAC))))) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; LEFT_FORALL_IMP_THM; EXISTS_REFL; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IMP_CONJ; FORALL_UNWIND_THM2] THEN
  ALL_TAC;;

let WPROOF1AUX_WU_bfr = prove
 (`!r:((W)wl_result)option. ~wl_bad_fun_return r ==> ~(r = NONE)`,
  GEN_TAC THEN CASES_ON `r:((W)wl_result)option` THEN
  REWRITE_TAC[wl_bad_fun_return_def; option_DISTINCT]);;

(* a call without a return: Seq_assoc_right drops acc, the call never     *)
(* returns NONE                                                             *)

let WPROOF1AUX_WU_CALL_NONE_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[word_unreach_Seq_assoc_right_def] THEN CAKE_REWRITE_TAC[] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_WU_is_eval_eq) THEN
  MATCH_MP_TAC(MESON[] `(a:B) = b ==> a = c ==> b = c`) THEN
  MATCH_MP_TAC WPROOF1AUX_WU_seq_not_none THEN
  ONCE_REWRITE_TAC[WPROOF1AUX_WU_eval_clause "wl_Call"] THEN SIMP[] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[]) THEN ASM_MESON_TAC[WPROOF1AUX_WU_bfr];;


let WPROOF1AUX_WU_CALL_SOME_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN WPROOF1AUX_WU_SIMPSEQ_CONG_TAC THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[WPROOF1AUX_WU_eval_clause "wl_Call"] THEN
  SIMP[add_ret_loc_def; WPROOF1AUX_WU_push_env_some] THEN
  REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[FST]) THEN ASM_SIMP_TAC[];;

let WPROOF1AUX_WU_CALL_SOME1_TAC : tactic =
  DISCH_THEN(ASSUME_TAC o MATCH_MP WPROOF1AUX_WU_ih_use o
             REWRITE_RULE[GSYM IMP_CONJ] o
             SPECL [`x1:num list`; `x2:cutsets`; `x3:num`; `x4:num`; `q1:(A)wl_prog`]) THEN
  WPROOF1AUX_WU_CALL_SOME_TAC;;

let WPROOF1AUX_WU_CALL_SOME2_TAC : tactic =
  DISCH_THEN(ASSUME_TAC o MATCH_MP WPROOF1AUX_WU_ih_use o
             REWRITE_RULE[GSYM IMP_CONJ] o
             SPECL [`x1:num list`; `x2:cutsets`; `x3:num`; `x4:num`; `q1:(A)wl_prog`]) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP WPROOF1AUX_WU_ih_use o
             REWRITE_RULE[GSYM IMP_CONJ] o
             SPECL [`x1:num list`; `x2:cutsets`; `q1:(A)wl_prog`; `x3:num`; `x4:num`;
                    `y1:num`; `y2:num`; `y3:num`; `q2:(A)wl_prog`]) THEN
  WPROOF1AUX_WU_CALL_SOME_TAC;;



let WPROOF1AUX_WU_CALL_TAC : tactic =
  WPROOF1AUX_WU_CALL0_TAC THENL
   [WPROOF1AUX_WU_CALL_NONE_TAC; WPROOF1AUX_WU_CALL_NONE_TAC;
    WPROOF1AUX_WU_CALL_SOME1_TAC; WPROOF1AUX_WU_CALL_SOME2_TAC];;

(* the other constructors: Seq_assoc_right p1 acc = SimpSeq p1 acc *)

let WPROOF1AUX_WU_SIMPSEQ_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[word_unreach_Seq_assoc_right_def] THEN
  REWRITE_TAC[evaluate_SimpSeq];;

let evaluate_Seq_assoc_right_lemma = prove
 (`!p1 p2 (s:(A,C,FFI)wl_state) res s1.
     wl_evaluate (wl_Seq p1 p2,s) = (res,s1) /\ ~(res = SOME wl_Error) ==>
     wl_evaluate (Seq_assoc_right p1 p2,s) = (res,s1)`,
  MATCH_MP_TAC word_unreach_Seq_assoc_right_ind THEN REPEAT CONJ_TAC THENL
   ([WPROOF1AUX_WU_SKIP_TAC; WPROOF1AUX_WU_SEQ_TAC; WPROOF1AUX_WU_IF_TAC;
     WPROOF1AUX_WU_MT_TAC; WPROOF1AUX_WU_CALL_TAC; WPROOF1AUX_WU_LOOP_TAC] @
    replicate WPROOF1AUX_WU_SIMPSEQ_TAC 20));;

let evaluate_remove_unreach = prove
 (`!p (s:(A,C,FFI)wl_state) res s1.
     wl_evaluate (p,s) = (res,s1) /\ ~(res = SOME wl_Error) ==>
     wl_evaluate (remove_unreach p,s) = (res,s1)`,
  REWRITE_TAC[remove_unreach_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC evaluate_Seq_assoc_right_lemma THEN
  ASM_REWRITE_TAC[word_unreachProof_evaluate_Seq_Skip]);;
