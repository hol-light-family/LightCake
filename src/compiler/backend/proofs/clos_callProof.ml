(* ========================================================================= *)
(* clos_callProof: port of HOL4 compiler/backend/proofs/clos_callProofScript *)
(* .sml (CakeML v3479).  Correctness proof for clos_call.                    *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/clos_call.ml";;
needs "compiler/backend/db_vars.ml";;

type_invention_error := true;;

(* HOL4: v_size_lemma [local] *)
let clos_callProof_v_size_lemma = prove
 (`!(v:clos_v) vl. MEM v vl ==> clos_v_size v < list_size clos_v_size vl`,
  MESON_TAC[MEM_LIST_SIZE]);;

let code_locs_GENLIST_Var = prove
 (`!n t i. code_locs (GENLIST_Var t i n) = []`,
  INDUCT_TAC THEN ONCE_REWRITE_TAC[GENLIST_Var_def] THEN
  ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; code_locs_append; code_locs_def; APPEND]);;
let _ = cake_add_simps [code_locs_GENLIST_Var];;

let fv_GENLIST_Var_tra = prove
 (`!n tra i. clos_fv v (GENLIST_Var tra i n) <=> v < n`,
  INDUCT_TAC THEN ONCE_REWRITE_TAC[GENLIST_Var_def] THEN
  ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; fv_append; clos_fv_def; LT] THEN
  MESON_TAC[]);;

let evaluate_GENLIST_Var_tra = prove
 (`!n tr i.
     clos_evaluate (GENLIST_Var tr i n,env,(s:(C,FFI)clos_state)) =
     if n <= LENGTH env then (Rval (TAKE n env),s)
     else (Rerr (Rabort Rtype_error),s)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GENLIST_Var_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; clos_evaluate_def; LE_0; TAKE_0] THEN
  ASM_REWRITE_TAC[clos_evaluate_append] THEN
  ASM_CASES_TAC `n <= LENGTH (env:clos_v list)` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[clos_evaluate_def] THENL
   [ASM_CASES_TAC `n < LENGTH (env:clos_v list)` THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THENL
     [REWRITE_TAC[ADD1] THEN
      ASM_SIMP_TAC[ARITH_RULE `n < m ==> n + 1 <= m`; TAKE_EL_SNOC; SNOC_APPEND];
      ASM_SIMP_TAC[ARITH_RULE `~(n < m) ==> ~(SUC n <= m)`]];
    ASM_SIMP_TAC[ARITH_RULE `~(n <= m) ==> ~(SUC n <= m)`]]);;

(* HOL4 ML binding evaluate_add_clock *)
let CLOSCALLPAUX_evaluate_add_clock = prove
 (`!es env (s:(C,FFI)clos_state) r s' extra.
     clos_evaluate (es,env,s) = (r,s') ==>
     ~(r = Rerr (Rabort Rtimeout_error)) ==>
     clos_evaluate (es,env,clos_state_clock_fupd (K (clos_state_clock s + extra)) s) =
     (r,clos_state_clock_fupd (K (clos_state_clock s' + extra)) s')`,
  MESON_TAC[clos_evaluate_add_to_clock]);;

let is_Recclosure_def = cake_def
  `(is_Recclosure (clos_Recclosure _ _ _ _ _) <=> T) /\
   (is_Recclosure _ <=> F)`;;
let _ = cake_add_simps [is_Recclosure_def];;

let every_refv_def = cake_def
  `(every_refv (P:A->bool) (clos_ValueArray vs) <=> ALL P vs) /\
   (every_refv P (clos_Thunk m v) <=> P v) /\
   (every_refv P _ <=> T)`;;
let _ = cake_add_simps [every_refv_def];;

(* HOL4 [local] *)
let IMP_EXISTS_IFF = prove
 (`!xs. (!x:A. MEM x xs ==> (P x <=> Q x)) ==> (EX P xs <=> EX Q xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[EX; MEM] THEN ASM_MESON_TAC[]);;

(* correctness of free *)

(* local helpers: the induction theorems of the kit give hypotheses of the *)
(* form !c l. f x = (c,l) ==> P (HOL4's contexts), which hold trivially   *)
let CLOSCALLPAUX_FORALL_PAIR_EQ_IMP = prove
 (`(!(f:A#B) Q. (!c l. f = (c,l) ==> Q) <=> Q) /\
   (!(f:A#B) (g:C#D) Q. (!c1 l1 c2 l2. f = (c1,l1) /\ g = (c2,l2) ==> Q) <=> Q)`,
  MESON_TAC[PAIR]);;

(* the facts free_LENGTH and free_SING of every assumption free xs = (c,l) *)
let CLOSCALLPAUX_FREE_FACTS_TAC : tactic =
  ASSUM_LIST (fun ths -> EVERY (map (fun th ->
    let c = concl th in
    if is_eq c && is_comb(lhs c) && rator(lhs c) = `clos_call_free`
    then ASSUME_TAC (MATCH_MP free_LENGTH th) THEN
         (fun g -> try STRIP_ASSUME_TAC (MATCH_MP free_SING th) g
                   with Failure _ -> ALL_TAC g)
    else ALL_TAC) ths));;

let free_thm = prove
 (CASE_TERM
  `!xs. let (ys,l) = clos_call_free xs in
          !n. (clos_fv n ys <=> has_var n l) /\ (clos_fv n xs <=> has_var n l)`,
  MATCH_MP_TAC clos_call_free_ind THEN
  REWRITE_TAC[CLOSCALLPAUX_FORALL_PAIR_EQ_IMP] THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[clos_call_free_def] THEN
  REPEAT PAIRARG_TAC THEN CLOSCALLPAUX_FREE_FACTS_TAC THEN
  GVS[clos_fv_def; has_var_def; HD] THEN
  (* Letrec *)
  REWRITE_TAC[EX_MAP; o_DEF] THEN GEN_TAC THEN CONJ_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC IMP_EXISTS_IFF THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `z:clos_exp`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `z:clos_exp`]) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `clos_call_free [z]` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:clos_exp list`
    (X_CHOOSE_THEN `l:db_var_set` ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP free_SING) THEN
  ASM_REWRITE_TAC[] THEN SIMP[HD; fv1_intro; ADD_ASSOC]);;

(* correctness of free *)

(* value relation *)

let subg_def = cake_def
  `subg (g0:A spt # (B # C) list) g1 <=>
     subspt (FST g0) (FST g1) /\
     (!k v. ALOOKUP (SND g0) k = SOME v ==> ALOOKUP (SND g1) k = SOME v) /\
     ALL_DISTINCT (MAP FST (SND g1))`;;

let subg_refl = prove
 (`!g:A spt # (B # C) list. ALL_DISTINCT (MAP FST (SND g)) ==> subg g g`,
  RW[subg_def; subspt_refl]);;

let subg_trans = prove
 (`!g1 g2 g3:A spt # (B # C) list. subg g1 g2 /\ subg g2 g3 ==> subg g1 g3`,
  RW[subg_def] THEN ASM_MESON_TAC[subspt_trans]);;

let wfg'_def = cake_def
  `wfg' (g:A spt # (num # B) list) <=>
     set_of_list (MAP FST (SND g)) SUBSET IMAGE SUC (domain (FST g))`;;

let wfg_def = cake_def
  `wfg (g:A spt # (num # B) list) <=>
     set_of_list (MAP FST (SND g)) = IMAGE SUC (domain (FST g)) /\
     ALL_DISTINCT (MAP FST (SND g))`;;

let make_g_def = cake_def
  `make_g (d:A spt) (code:(num,B)fmap) =
     if IMAGE SUC (domain d) SUBSET FDOM code then
       SOME (d, MAP (\k. (FST k + 1, THE (FLOOKUP code (FST k + 1)))) (toAList d))
     else NONE`;;

(* HOL4 [local] *)
let ALL_DISTINCT_MAP_FST_ADD1 = prove
 (`!xs:(num # A) list.
     ALL_DISTINCT (MAP (\k. FST k + 1) xs) <=> ALL_DISTINCT (MAP FST xs)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ALL_DISTINCT] THEN
  REWRITE_TAC[MEM_MAP; EQ_ADD_RCANCEL]);;

let make_g_wfg = prove
 (`make_g (d:A spt) (code:(num,B)fmap) = SOME g ==> wfg g`,
  RW[make_g_def; wfg_def] THEN
  REWRITE_TAC[MAP_MAP_o; o_DEF; ALL_DISTINCT_MAP_FST_ADD1;
              ALL_DISTINCT_MAP_FST_toAList] THEN
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_MAP; IN_IMAGE; EXISTS_PAIR_THM;
              MEM_toAList; domain_lookup; FST; ADD1] THEN
  MESON_TAC[]);;

let make_g_subg = prove
 (`make_g (cfg:A spt) (FEMPTY |++ (aux:(num # B) list)) = SOME new /\ wfg (cfg,aux)
   ==> subg (cfg,aux) new`,
  REWRITE_TAC[make_g_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) MP_TAC) THEN
  REWRITE_TAC[wfg_def; subg_def; FST; SND; subspt_refl; MAP_MAP_o; o_DEF] THEN
  REWRITE_TAC[ALL_DISTINCT_MAP_FST_ADD1; ALL_DISTINCT_MAP_FST_toAList] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN
  REWRITE_TAC[MAP_MAP_o; o_DEF; ALL_DISTINCT_MAP_FST_ADD1;
              ALL_DISTINCT_MAP_FST_toAList] THEN
  SUBGOAL_THEN `FLOOKUP (FEMPTY |++ (aux:(num # B) list)) k = SOME v` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP
      FUPDATE_LIST_ALL_DISTINCT_REVERSE th)]) THEN
    MATCH_MP_TAC FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `k IN IMAGE SUC (domain (cfg:A spt))` MP_TAC THENL
   [UNDISCH_TAC `set_of_list (MAP FST (aux:(num # B) list)) =
                 IMAGE SUC (domain (cfg:A spt))` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_SET_OF_LIST; MEM_MAP; EXISTS_PAIR_THM; FST] THEN
    ASM_MESON_TAC[ALOOKUP_MEM];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; domain_lookup] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_TAC `x:A`))) THEN
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; FST; PAIR_EQ] THEN
  MAP_EVERY EXISTS_TAC [`j:num`; `x:A`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD1]) THEN
  ASM_REWRITE_TAC[MEM_toAList; ADD1; THE_DEF]);;

let make_g_make_g_eq = prove
 (`!x1 (x2:(num,B)fmap) y1 y2 (g0:A spt # (num # B) list) g1.
     FST g0 = FST g1 /\ subg g0 g1 /\
     make_g x1 x2 = SOME g0 /\ make_g y1 y2 = SOME g1 ==> g0 = g1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wfg (g0:A spt # (num # B) list) /\ wfg (g1:A spt # (num # B) list)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[make_g_wfg]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[make_g_def]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o lhs o concl))) THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  REPEAT(DISCH_THEN(SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o rhs o concl)) THEN
  REWRITE_TAC[PAIR_EQ] THEN MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:A`] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[subg_def; wfg_def; FST; SND]) THEN
  POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!f:(num,B)fmap.
       ALL_DISTINCT (MAP FST (MAP (\k. FST k + 1,THE (FLOOKUP f (FST k + 1)))
                                  (toAList (y1:A spt)))) ==>
       ALOOKUP (MAP (\k. FST k + 1,THE (FLOOKUP f (FST k + 1))) (toAList y1)) (a + 1) =
       SOME (THE (FLOOKUP f (a + 1)))` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN
    ASM_REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; PAIR_EQ; FST] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[option_INJ]]);;

let make_g_IMP_subg = prove
 (`make_g (r0:num_set) (code:(num,B)fmap) = SOME g0 /\
   DISJOINT (FDOM code) (set_of_list (MAP FST (progs1:(num # B) list))) /\
   ALL_DISTINCT (MAP FST progs1) /\
   make_g r1 (code |++ progs1) = SOME g1 /\ subspt r0 r1 /\
   set_of_list (MAP FST progs1) SUBSET IMAGE SUC (domain r1) ==>
   subg (r1,APPEND progs1 (SND g0)) g1`,
  STRIP_TAC THEN
  SUBGOAL_THEN `wfg (g1:num_set # (num # B) list)` MP_TAC THENL
   [ASM_MESON_TAC[make_g_wfg]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[make_g_def]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o lhs o concl))) THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  REPEAT(DISCH_THEN(SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[wfg_def; subg_def; FST; SND; subspt_refl] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ALOOKUP_APPEND] THEN REPEAT GEN_TAC THEN
  CASES_ON `ALOOKUP (progs1:(num#B)list) k` THEN CASE_REWRITE_TAC[option_INJ] THEN
  DISCH_TAC THEN MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[] THENL
   [(* the key is in SND g0 *)
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; FST; PAIR_EQ; MEM_toAList] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `x:1` STRIP_ASSUME_TAC)) THEN
    RVEQ_TAC THEN MAP_EVERY EXISTS_TAC [`j:num`; `x:1`] THEN
    SUBGOAL_THEN `FLOOKUP ((code:(num,B)fmap) |++ progs1) (j + 1) = FLOOKUP code (j + 1)`
      SUBST1_TAC THENL
     [ASM_SIMP_TAC[flookup_fupdate_list; alookup_distinct_reverse] THEN
      CASE_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN ASM_MESON_TAC[subspt_lookup];
    (* the key is in progs1 *)
    RVEQ_TAC THEN
    SUBGOAL_THEN `FLOOKUP ((code:(num,B)fmap) |++ progs1) k = SOME v` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM(MATCH_MP FUPDATE_LIST_ALL_DISTINCT_REVERSE
        (ASSUME `ALL_DISTINCT (MAP FST (progs1:(num#B)list))`))] THEN
      MATCH_MP_TAC FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `k IN IMAGE SUC (domain (r1:num_set))` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
        check (fun th -> concl th =
          `set_of_list (MAP FST (progs1:(num#B)list)) SUBSET
           IMAGE SUC (domain (r1:num_set))`)) THEN
      REWRITE_TAC[IN_SET_OF_LIST] THEN
      MATCH_MP_TAC(MESON[ALOOKUP_NONE; option_DISTINCT]
        `ALOOKUP (l:(num#B)list) k = SOME v ==> MEM k (MAP FST l)`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; domain_lookup] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_TAC `x:1`))) THEN
    REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; FST; PAIR_EQ] THEN
    MAP_EVERY EXISTS_TAC [`j:num`; `x:1`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD1]) THEN
    ASM_REWRITE_TAC[MEM_toAList; ADD1; THE_DEF]]);;

let recclosure_wf_def = cake_def
  `recclosure_wf loc (fns:(num # clos_exp) list) <=>
     every_Fn_SOME (MAP SND fns) /\
     every_Fn_vs_NONE (MAP SND fns) /\
     DISJOINT (set_of_list (list_of_seq (\i. 2 * i + loc) (LENGTH fns)))
              (set_of_list (code_locs (MAP SND fns))) /\
     ALL_DISTINCT (code_locs (MAP SND fns))`;;

let code_includes_def = cake_def
  `code_includes (al:(A # B) list) code <=>
     !k v. ALOOKUP al k = SOME v ==> FLOOKUP code k = SOME v`;;

let recclosure_rel_def = cake_def
  `recclosure_rel (g:num_set # (num # num # clos_exp) list) (l:num->bool)
                  (code:(num,num # clos_exp)fmap) loc
                  (fns1:(num # clos_exp) list) fns2 <=>
   ?g0.
     recclosure_wf loc fns1 /\
     wfg g0 /\
     DISJOINT (IMAGE SUC (set_of_list (code_locs (MAP SND fns1))))
              (set_of_list (MAP FST (SND g0))) /\
     DISJOINT (set_of_list (list_of_seq (\i. 2 * i + loc + 1) (LENGTH fns1)))
              (set_of_list (MAP FST (SND g0))) /\
     (let (es,new_g) = clos_call_calls (MAP SND fns1)
                         (insert_each loc (LENGTH fns1) g0) in
      if ALL2 (\np p. match np with
                        (n,_) -> !v. has_var v (SND (clos_call_free [p])) ==> v < n)
              fns1 es
      then
        (?tra n. fns2 = calls_list tra n loc fns1) /\
        subg (clos_call_code_list loc (ZIP (MAP FST fns1) es) new_g) g /\
        set_of_list (code_locs (MAP SND fns1)) DIFF domain (FST new_g) SUBSET l /\
        code_includes (SND (clos_call_code_list loc (ZIP (MAP FST fns1) es) new_g))
                      code
      else
        let (es,new_g) = clos_call_calls (MAP SND fns1) g0 in
          fns2 = ZIP (MAP FST fns1) es /\
          subg new_g g /\
          set_of_list (code_locs (MAP SND fns1)) DIFF domain (FST new_g) SUBSET l /\
          set_of_list (list_of_seq (\i. 2 * i + loc) (LENGTH fns1)) SUBSET l /\
          code_includes (SND new_g) code)`;;

let clos_callProof_env_rel_def = cake_def
  `clos_callProof_env_rel (R:A->B->bool) env1 env2 a (es:(num # clos_exp) list) <=>
     if LENGTH env1 = LENGTH env2 then ALL2 R env1 env2 else
     !x. EX (\p. match p with (n,p) -> clos_fv1 (n + a + x) p) es ==>
         x < LENGTH env1 /\ x < LENGTH env2 /\ R (EL x env1) (EL x env2)`;;

(* HOL4 [mono] *)
let clos_callProof_env_rel_mono = prove
 (`(!x y. MEM x env1 /\ MEM y env2 /\ (R:A->B->bool) x y ==> R' x y) ==>
   clos_callProof_env_rel R env1 env2 a es ==>
   clos_callProof_env_rel R' env1 env2 a es`,
  REWRITE_TAC[clos_callProof_env_rel_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[LIST_REL_EL_EQN] THEN ASM_MESON_TAC[MEM_EL];
    ASM_MESON_TAC[MEM_EL]]);;

(* HOL4 [defncong] *)
let env_rel_cong = prove
 (`(!x y. MEM x env1 /\ MEM y env2 ==> ((R:A->B->bool) x y <=> R' x y)) ==>
   (clos_callProof_env_rel R env1 env2 a es <=>
    clos_callProof_env_rel R' env1 env2 a es)`,
  REWRITE_TAC[clos_callProof_env_rel_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[LIST_REL_EL_EQN] THEN ASM_MESON_TAC[MEM_EL];
    ASM_MESON_TAC[MEM_EL]]);;

(* v_rel recurses through LIST_REL (ALL2) and env_rel.  The definition uses  *)
(* the admissibility rules below (HOL4's congruence rules LIST_REL_CONG and *)
(* env_rel_cong: a recursive call under ALL2 R l1 l2 or env_rel R e1 e2 a es *)
(* gets the context MEM y l1 /\ MEM z l2), registered for this definition   *)
(* only.                                                                     *)

let CLOSCALLPAUX_ADMISSIBLE_env_rel = prove
 (`!(<<) (p:(A->B)->P->bool) (s:P->A) (h:(A->B)->P->C->D->bool) e1 e2 n es.
        admissible(<<) p s e1 /\ admissible(<<) p s e2 /\
        admissible(<<) p s n /\ admissible(<<) p s es /\
        admissible (<<) (\f (y,z,x). p f x /\ MEM y (e1 f x) /\ MEM z (e2 f x))
                        (\(y,z,x). s x) (\f (y,z,x). h f x y z)
        ==> admissible (<<) p s
              (\f x. clos_callProof_env_rel (h f x) (e1 f x) (e2 f x) (n f x) (es f x))`,
  REWRITE_TAC[admissible; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(e1:(A->B)->P->C list) g a = e1 f a /\
                (e2:(A->B)->P->D list) g a = e2 f a /\
                (n:(A->B)->P->num) g a = n f a /\
                (es:(A->B)->P->(num # clos_exp) list) g a = es f a`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC env_rel_cong THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let clos_callProof_v_rel_def =
  let saved = !cake_admissible_rules in
  cake_register_admissible "ALL2" LISTAUX_ADMISSIBLE_ALL2;
  cake_register_admissible "clos_callProof_env_rel" CLOSCALLPAUX_ADMISSIBLE_env_rel;
  let th = try cake_def_wf
    `MEASURE (\x:(num_set # (num # num # clos_exp) list) # (num->bool) #
                 (num,num # clos_exp)fmap # clos_v # clos_v.
                clos_v_size (FST (SND (SND (SND x)))))`
    TERM_TAC
    `(clos_callProof_v_rel g l code (clos_Number i) v <=> v = clos_Number i) /\
     (clos_callProof_v_rel g l code (clos_Word64 w) v <=> v = clos_Word64 w) /\
     (clos_callProof_v_rel g l code (clos_Block n vs) v <=>
        ?vs'. v = clos_Block n vs' /\ ALL2 (clos_callProof_v_rel g l code) vs vs') /\
     (clos_callProof_v_rel g l code (ByteVector ws) v <=> v = ByteVector ws) /\
     (clos_callProof_v_rel g l code (clos_RefPtr b n) v <=> v = clos_RefPtr b n) /\
     (clos_callProof_v_rel g l code (clos_Closure loco vs1 env1 n bod1) v <=>
        ?loc vs2 env2 bod2.
          recclosure_rel g l code loc [(n,bod1)] [(n,bod2)] /\
          v = clos_Closure (SOME loc) vs2 env2 n bod2 /\ loco = SOME loc /\
          ALL2 (clos_callProof_v_rel g l code) vs1 vs2 /\
          clos_callProof_env_rel (clos_callProof_v_rel g l code) env1 env2 0
                                 [(n,bod2)]) /\
     (clos_callProof_v_rel g l code (clos_Recclosure loco vs1 env1 fns1 j) v <=>
        ?loc vs2 env2 fns2.
          recclosure_rel g l code loc fns1 fns2 /\
          v = clos_Recclosure (SOME loc) vs2 env2 fns2 j /\ loco = SOME loc /\
          ALL2 (clos_callProof_v_rel g l code) vs1 vs2 /\
          clos_callProof_env_rel (clos_callProof_v_rel g l code) env1 env2
                                 (LENGTH fns2) fns2)`
    with e -> (cake_admissible_rules := saved; raise e) in
  cake_admissible_rules := saved; th;;

let clos_callProof_v_rel_ind = cake_ind "clos_callProof_v_rel";;

(* HOL4's wfv_def has nested patterns and a catch-all clause; defined by  *)
(* clauses, the kit takes over 15 minutes on it (the completed clauses),   *)
(* so wfv is defined by one match (seconds) and HOL4's clauses wfv_def and *)
(* induction theorem wfv_ind are proved from it.                          *)

let CLOSCALLPAUX_wfv_match_def = cake_def_wf
  `MEASURE (\x:(num_set # (num # num # clos_exp) list) # (num->bool) #
               (num,num # clos_exp)fmap # clos_v.
              clos_v_size (SND (SND (SND x))))`
  TERM_TAC
  `wfv g l code v <=>
     match v with
       clos_Closure NONE _ _ _ _ -> F
     | clos_Recclosure NONE _ _ _ _ -> F
     | clos_Closure (SOME loc) vs env n bod ->
         ALL (wfv g l code) vs /\ ALL (wfv g l code) env /\
         (?fns2. recclosure_rel g l code loc [(n,bod)] fns2)
     | clos_Recclosure (SOME loc) vs env fns i ->
         ALL (wfv g l code) vs /\ ALL (wfv g l code) env /\
         (?fns2. recclosure_rel g l code loc fns fns2)
     | clos_Block _ vs -> ALL (wfv g l code) vs
     | _ -> T`;;

let wfv_def = prove
 (`(!g l code v0 v1 v2 v3. wfv g l code (clos_Closure NONE v0 v1 v2 v3) <=> F) /\
   (!g l code v0 v1 v2 v3. wfv g l code (clos_Recclosure NONE v0 v1 v2 v3) <=> F) /\
   (!g l code loc vs env n bod.
      wfv g l code (clos_Closure (SOME loc) vs env n bod) <=>
      ALL (wfv g l code) vs /\ ALL (wfv g l code) env /\
      (?fns2. recclosure_rel g l code loc [(n,bod)] fns2)) /\
   (!g l code loc vs env fns i.
      wfv g l code (clos_Recclosure (SOME loc) vs env fns i) <=>
      ALL (wfv g l code) vs /\ ALL (wfv g l code) env /\
      (?fns2. recclosure_rel g l code loc fns fns2)) /\
   (!g l code v vs. wfv g l code (clos_Block v vs) <=> ALL (wfv g l code) vs) /\
   (!g l code i. wfv g l code (clos_Number i) <=> T) /\
   (!g l code w. wfv g l code (clos_Word64 w) <=> T) /\
   (!g l code bs. wfv g l code (ByteVector bs) <=> T) /\
   (!g l code b n. wfv g l code (clos_RefPtr b n) <=> T)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [CLOSCALLPAUX_wfv_match_def] THEN CASE_REWRITE_TAC[]);;
let _ = cake_add_simps [wfv_def];;

let wfv_ind = prove
 (`!P:(num_set # (num # num # clos_exp) list)->(num->bool)->
      (num,num # clos_exp)fmap->clos_v->bool.
     (!g l code v0 v1 v2 v3. P g l code (clos_Closure NONE v0 v1 v2 v3)) /\
     (!g l code v0 v1 v2 v3. P g l code (clos_Recclosure NONE v0 v1 v2 v3)) /\
     (!g l code loc vs env n bod.
        (!a. MEM a env ==> P g l code a) /\ (!a. MEM a vs ==> P g l code a)
        ==> P g l code (clos_Closure (SOME loc) vs env n bod)) /\
     (!g l code loc vs env fns i.
        (!a. MEM a env ==> P g l code a) /\ (!a. MEM a vs ==> P g l code a)
        ==> P g l code (clos_Recclosure (SOME loc) vs env fns i)) /\
     (!g l code v vs. (!a. MEM a vs ==> P g l code a)
        ==> P g l code (clos_Block v vs)) /\
     (!g l code i. P g l code (clos_Number i)) /\
     (!g l code w. P g l code (clos_Word64 w)) /\
     (!g l code bs. P g l code (ByteVector bs)) /\
     (!g l code b n. P g l code (clos_RefPtr b n))
     ==> !g l code v. P g l code v`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  SPEC_TAC(`v:clos_v`,`v:clos_v`) THEN MATCH_MP_TAC v_ind THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `o':num option` option_nchotomy) THEN ASM_MESON_TAC[]);;

let wfv_state_def = cake_def
  `wfv_state g l code (s:(A,FFI)clos_state) <=>
     ALL (OPTION_ALL (wfv g l code)) (clos_state_globals s) /\
     FEVERY (every_refv (wfv g l code) o SND) (clos_state_refs s) /\
     clos_state_code s = FEMPTY`;;

(* HOL4 types calls_state and abs_calls_state: abbreviations *)
new_type_abbrev("calls_state",`:num_set # (num # num # clos_exp) list`);;
new_type_abbrev("abs_calls_state",`:num_set`);;

let clos_callProof_state_rel_def = cake_def
  `clos_callProof_state_rel g l (s:(abs_calls_state # C,FFI)clos_state)
                            (t:(C,FFI)clos_state) <=>
     clos_state_ffi s = clos_state_ffi t /\
     clos_state_clock s = clos_state_clock t /\
     clos_state_max_app s = clos_state_max_app t /\
     ALL2 (OPTREL (clos_callProof_v_rel g l (clos_state_code t)))
          (clos_state_globals s) (clos_state_globals t) /\
     fmap_rel (clos_ref_rel (clos_callProof_v_rel g l (clos_state_code t)))
              (clos_state_refs s) (clos_state_refs t) /\
     clos_state_code s = FEMPTY`;;

let clos_callProof_state_rel_max_app = prove
 (`clos_callProof_state_rel g l (s:(abs_calls_state # C,FFI)clos_state) t
   ==> clos_state_max_app s = clos_state_max_app t`,
  SIMP_TAC[clos_callProof_state_rel_def]);;

let clos_callProof_state_rel_clock = prove
 (`clos_callProof_state_rel g l (s:(abs_calls_state # C,FFI)clos_state) t
   ==> clos_state_clock s = clos_state_clock t`,
  SIMP_TAC[clos_callProof_state_rel_def]);;

let clos_callProof_state_rel_with_clock = prove
 (`clos_callProof_state_rel g l (s:(abs_calls_state # C,FFI)clos_state) t
   ==> clos_callProof_state_rel g l (clos_state_clock_fupd (K k) s)
                                    (clos_state_clock_fupd (K k) t)`,
  SIMP[clos_callProof_state_rel_def]);;

let state_rel_flookup_refs = prove
 (`clos_callProof_state_rel g l (s:(abs_calls_state # C,FFI)clos_state) t /\
   FLOOKUP (clos_state_refs s) k = SOME v
   ==> ?v'. FLOOKUP (clos_state_refs t) k = SOME v' /\
            clos_ref_rel (clos_callProof_v_rel g l (clos_state_code t)) v v'`,
  REWRITE_TAC[clos_callProof_state_rel_def; fmap_rel_OPTREL_FLOOKUP] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  ASM_REWRITE_TAC[OPTREL_def; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

(* syntactic properties of compiler *)

let FST_code_list = prove
 (`!loc fns (g:B # (num # num # A) list).
     FST (clos_call_code_list loc fns g) = FST g`,
  MATCH_MP_TAC clos_call_code_list_ind THEN
  REWRITE_TAC[clos_call_code_list_def; FST]);;
let _ = cake_add_simps [FST_code_list];;

let SND_insert_each = prove
 (`!p n (g:num_set # A). SND (insert_each p n g) = SND g`,
  MATCH_MP_TAC insert_each_ind THEN REWRITE_TAC[insert_each_def; SND]);;
let _ = cake_add_simps [SND_insert_each];;

let CLOSCALLPAUX_calls_list_MAPi = prove
 (`!fns:(num # A) list loc n.
     calls_list t n loc fns =
     MAPi (\i p. (FST p, clos_Call t 0 (loc + 2 * i + 1) (GENLIST_Var t 1 (FST p))))
          fns`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[calls_list_def; MAPi_DEF] THEN
  CASES_ON `h:num # A` THEN
  ASM_REWRITE_TAC[calls_list_def; MAPi_DEF; CONS_11; FST; MULT_CLAUSES; ADD_CLAUSES] THEN
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PAIR_EQ; injectivity "clos_exp"] THEN ARITH_TAC);;

let calls_list_MAPi = prove
 (`!loc (tra:tra) n.
     calls_list t n loc =
     MAPi (\i (p:num # A).
             (FST p, clos_Call t 0 (loc + 2 * i + 1) (GENLIST_Var t 1 (FST p))))`,
  REWRITE_TAC[FUN_EQ_THM; CLOSCALLPAUX_calls_list_MAPi]);;

let calls_list_length = prove
 (`LENGTH (calls_list t n p (fns:(num # A) list)) = LENGTH fns`,
  REWRITE_TAC[calls_list_MAPi; LENGTH_MAPi]);;
let _ = cake_add_simps [calls_list_length];;

let domain_FST_insert_each = prove
 (`!p n (g:num_set # A).
     domain (FST (insert_each p n g)) =
     set_of_list (list_of_seq (\i. 2 * i + p) n) UNION domain (FST g)`,
  MATCH_MP_TAC insert_each_ind THEN
  REWRITE_TAC[insert_each_def; LIST_OF_SEQ; set_of_list; UNION_EMPTY] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[domain_insert; FST; o_DEF] THEN
  SUBGOAL_THEN `(\x. 2 * SUC x + p) = (\i. 2 * i + p + 2)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN SET_TAC[]);;

let SND_code_list_change = prove
 (`!loc fns (g:B # (num # num # A) list) (g':B # (num # num # A) list).
     SND g = SND g' ==>
     SND (clos_call_code_list loc fns g) = SND (clos_call_code_list loc fns g')`,
  MATCH_MP_TAC clos_call_code_list_ind THEN REWRITE_TAC[clos_call_code_list_def] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?a b. g' = (a:B,b:(num # num # A) list)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[SND]) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[clos_call_code_list_def] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[SND]);;

let MAP_FST_code_list = prove
 (`!loc fns (g:B # (num # num # A) list).
     MAP FST (SND (clos_call_code_list loc fns g)) =
     APPEND (REVERSE (list_of_seq (\i. loc + i * 2 + 1) (LENGTH fns)))
            (MAP FST (SND g))`,
  MATCH_MP_TAC clos_call_code_list_ind THEN
  REWRITE_TAC[clos_call_code_list_def; LENGTH; LIST_OF_SEQ; REVERSE; APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SND; MAP; GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[o_DEF; MULT_CLAUSES; ADD_CLAUSES] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ARITH_TAC);;

let SND_code_list_ZIP = prove
 (`!loc fns (g:B # (num # num # A) list).
     SND (clos_call_code_list loc fns g) =
     APPEND (REVERSE (ZIP (list_of_seq ((+) (loc + 1) o ( * ) 2) (LENGTH fns)) fns))
            (SND g)`,
  MATCH_MP_TAC clos_call_code_list_ind THEN
  REWRITE_TAC[clos_call_code_list_def; LENGTH; LIST_OF_SEQ; ZIP; REVERSE; APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SND; GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[o_DEF; MULT_CLAUSES; ADD_CLAUSES; HD; TL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ARITH_TAC);;

(* HOL4 DEEP_INTRO_TAC some_intro: Q (some P) from the two cases of some_intro *)
let CLOSCALLPAUX_SOME_INTRO_TAC : tactic = fun (asl,w) ->
  let t = find_term (fun t -> is_comb t && is_const (rator t) &&
                              fst(dest_const(rator t)) = "some") w in
  let ety = hd(snd(dest_type(type_of t))) in
  let y = genvar (type_of t) in
  let q = mk_abs(y, subst [y,t] w) in
  let th = PINST [ety,`:A`] [rand t,`P:A->bool`; q,`Q:A option->bool`] some_intro in
  MATCH_MP_TAC (BETA_RULE th) (asl,w);;

let ALOOKUP_code_list = prove
 (CASE_TERM
  `!loc fns (g:B # (num # num # A) list) k.
     ALOOKUP (SND (clos_call_code_list loc fns g)) k =
     match (some i. i < LENGTH fns /\ k = loc + 2 * i + 1) with
       SOME i -> SOME (EL i fns)
     | NONE -> ALOOKUP (SND g) k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SND_code_list_ZIP; ALOOKUP_APPEND] THEN
  SUBGOAL_THEN
   `ALL_DISTINCT (MAP FST (ZIP (list_of_seq ((+) (loc + 1) o ( * ) 2) (LENGTH fns))
                               (fns:(num # A) list)))`
   ASSUME_TAC THENL
   [SIMP_TAC[MAP_ZIP; LENGTH_LIST_OF_SEQ; ALL_DISTINCT_GENLIST; o_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[alookup_distinct_reverse] THEN
  CLOSCALLPAUX_SOME_INTRO_TAC THEN CASE_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `ALOOKUP (ZIP (list_of_seq ((+) (loc + 1) o ( * ) 2) (LENGTH fns))
                   (fns:(num # A) list)) k = SOME (EL i fns)` SUBST1_TAC THENL
     [MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN
      ASM_SIMP_TAC[MEM_ZIP; LENGTH_LIST_OF_SEQ] THEN
      EXISTS_TAC `i:num` THEN
      ASM_SIMP_TAC[LENGTH_ZIP; LENGTH_LIST_OF_SEQ; EL_ZIP; EL_LIST_OF_SEQ; o_THM;
                   PAIR_EQ] THEN
      ARITH_TAC;
      CASE_REWRITE_TAC[]];
    DISCH_TAC THEN
    SUBGOAL_THEN
     `ALOOKUP (ZIP (list_of_seq ((+) (loc + 1) o ( * ) 2) (LENGTH fns))
                   (fns:(num # A) list)) k = NONE` SUBST1_TAC THENL
     [REWRITE_TAC[ALOOKUP_NONE] THEN
      SIMP_TAC[MAP_ZIP; LENGTH_LIST_OF_SEQ; MEM_GENLIST; o_THM] THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `m:num` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ARITH_TAC;
      CASE_REWRITE_TAC[]]]);;

let insert_each_subspt = prove
 (`!p n (g:num_set # A). subspt (FST g) (FST (insert_each p n g))`,
  MATCH_MP_TAC insert_each_ind THEN REWRITE_TAC[insert_each_def; subspt_refl] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC) THEN REWRITE_TAC[FST] THEN
  MATCH_MP_TAC(MESON[subspt_trans]
    `subspt (a:1 spt) b ==> subspt b c ==> subspt a c`) THEN
  REWRITE_TAC[subspt_lookup; lookup_insert] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[one]);;

let code_list_IS_SUFFIX = prove
 (`!loc fns (g:B # (num # num # A) list).
     IS_SUFFIX (SND (clos_call_code_list loc fns g)) (SND g)`,
  REWRITE_TAC[SND_code_list_ZIP; IS_SUFFIX_APPEND] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Local proof tools for the inductions over clos_call_calls.               *)
(* ------------------------------------------------------------------------- *)

(* HOL4 ho_match_mp_tac calls_ind \\ rw[calls_def] \\ rpt(pairarg_tac \\ fs[]): *)
(* the statement is !xs g0 ys g. clos_call_calls xs g0 = (ys,g) ==> ...        *)
let CLOSCALLPAUX_is_calls_eq th =
  let c = concl th in
  is_eq c &&
  (let h,_ = strip_comb (lhs c) in is_const h && fst(dest_const h) = "clos_call_calls");;

let CLOSCALLPAUX_CALLS_IND_TAC : tactic =
  MATCH_MP_TAC clos_call_calls_ind THEN REPEAT CONJ_TAC THEN
  REPEAT (GEN_TAC ORELSE DISCH_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check CLOSCALLPAUX_is_calls_eq) THEN
  REWRITE_TAC[clos_call_calls_def] THEN
  REPEAT (IL1AUX_PAIRARG_TAC THEN GVS[]) THEN REPEAT STRIP_TAC THEN GVS[];;

(* every implicational assumption (an induction hypothesis) resolved with   *)
(* the other assumptions, as far as possible (HOL4 res_tac, deeper)          *)
let CLOSCALLPAUX_IH_TAC : tactic = fun (asl,w as gl) ->
  let ths = map snd asl in
  let is_imp_th th = is_imp (snd(strip_forall(concl th))) in
  let facts = filter (fun th -> not (is_imp_th th)) ths in
  let ihs = filter is_imp_th ths in
  let rec go depth th =
    if not (is_imp_th th) then [th] else if depth = 0 then [] else
    let th = REWRITE_RULE[IMP_CONJ] th in
    flat (map (fun f -> try go (depth-1) (MATCH_MP th f) with Failure _ -> []) facts) in
  let news = flat (map (go 6) ihs) in
  MAP_EVERY ASSUME_TAC news gl;;

let CLOSCALLPAUX_SPLIT_ASM_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;

(* f applied to every assumption, the results added *)
let CLOSCALLPAUX_ADD_FACTS_TAC (f:thm->thm) : tactic =
  ASSUM_LIST (fun ths ->
    MAP_EVERY (fun th -> try ASSUME_TAC (f th) with Failure _ -> ALL_TAC) ths);;

(* set reasoning: the SUBSET / DISJOINT / IN / set-equation assumptions are *)
(* moved into the goal, the set-valued atoms (IMAGE f s, set_of_list l,     *)
(* domain t) are generalized to variables, every universal fact is         *)
(* instantiated at the elements that occur and MESON decides the remaining *)
(* ground problem (SET_TAC and TAUT are too slow on these goals)           *)
let CLOSCALLPAUX_is_set_atom t =
  (try let h,args = strip_comb t in
       is_const h && mem (fst(dest_const h)) ["IMAGE"; "set_of_list"; "domain"]
   with Failure _ -> false) && not (is_var t);;

let rec CLOSCALLPAUX_term_size t =
  if is_comb t then CLOSCALLPAUX_term_size (rator t) + CLOSCALLPAUX_term_size (rand t)
  else if is_abs t then 1 + CLOSCALLPAUX_term_size (body t) else 1;;

let CLOSCALLPAUX_ABS_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_binary "SUBSET" c || is_binary "IN" c || is_binary "DISJOINT" c ||
       (is_neg c && is_binary "IN" (rand c)) ||
       (is_eq c && type_of (lhs c) = `:num->bool`)
    then MP_TAC th else NO_TAC)) THEN
  (fun (asl,w) ->
     let rec maximal t =
       if CLOSCALLPAUX_is_set_atom t then [t]
       else if is_comb t then maximal (rator t) @ maximal (rand t)
       else if is_abs t then (try maximal (body t) with Failure _ -> [])
       else [] in
     let ts = setify (filter (fun t -> subset (frees t) (frees w)) (maximal w)) in
     let ts = sort (fun a b -> CLOSCALLPAUX_term_size a > CLOSCALLPAUX_term_size b) ts in
     MAP_EVERY (fun t -> SPEC_TAC(t, genvar (type_of t))) ts (asl,w));;

let CLOSCALLPAUX_SET_PROP_TAC : tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_INSERT; NOT_IN_EMPTY; IN_INTER; IN_DIFF; IN_DISJOINT;
              NOT_EXISTS_THM; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN
  (fun (asl,w) ->
     let ground = w :: filter (fun t -> not (is_forall t)) (map (concl o snd) asl) in
     let els = setify (flat (map (fun t -> map lhand (find_terms (is_binary "IN") t))
                                 ground)) in
     let fv = frees w @ freesl (map (concl o snd) asl) in
     let els = filter (fun e -> subset (frees e) fv) els in
     let inst th =
       if is_forall (concl th) then
         let v = fst(dest_forall (concl th)) in
         mapfilter (fun e -> if type_of e = type_of v then SPEC e th else failwith "")
                   els
       else [th] in
     let ths = map (REWRITE_RULE[]) (flat (map (inst o snd) asl)) in
     (REWRITE_TAC[] THEN MESON_TAC ths) ([],w));;

let CLOSCALLPAUX_ABS_PROP_TAC = CLOSCALLPAUX_ABS_TAC THEN CLOSCALLPAUX_SET_PROP_TAC;;

(* facts about the steps of clos_call_calls *)
let CLOSCALLPAUX_subspt_IMAGE_SUC = prove
 (`!t1 t2:num_set. subspt t1 t2 ==> IMAGE SUC (domain t1) SUBSET IMAGE SUC (domain t2)`,
  SIMP_TAC[subspt_domain; IMAGE_SUBSET]);;

let CLOSCALLPAUX_code_list_keys_eq = prove
 (`!loc n. set_of_list (REVERSE (list_of_seq (\i. loc + i * 2 + 1) n)) =
           IMAGE SUC (set_of_list (list_of_seq (\i. 2 * i + loc) n))`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_REVERSE; MEM_GENLIST; IN_IMAGE] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `2 * m + loc` THEN CONJ_TAC THENL [ARITH_TAC; ASM_MESON_TAC[]];
    EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)

let calls_subspt = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g.
     clos_call_calls xs g0 = (ys,g) ==> subspt (FST g0) (FST g)`,
  CLOSCALLPAUX_CALLS_IND_TAC THEN EVERY_CASE_TAC THEN GVS[subspt_refl] THEN
  ASM_MESON_TAC[subspt_trans; insert_each_subspt; FST_code_list]);;

(* the preprocessing of the set facts of a calls step *)
let CLOSCALLPAUX_CALLS_FACTS_TAC : tactic =
  CLOSCALLPAUX_IH_TAC THEN
  IMP_RES_TAC calls_subspt THEN IMP_RES_TAC calls_length THEN
  CLOSCALLPAUX_ADD_FACTS_TAC (MATCH_MP CLOSCALLPAUX_subspt_IMAGE_SUC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[subspt_domain]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST_code_list; MAP_FST_code_list;
    SND_insert_each; domain_FST_insert_each; LENGTH_MAP; SET_OF_LIST_APPEND;
    LISTAUX_LENGTH_ZIP; CLOSCALLPAUX_code_list_keys_eq; IMAGE_UNION; UNION_SUBSET;
    LISTAUX_list_of_seq_1; set_of_list; BETA_THM;
    ARITH_RULE `2 * 0 + loc = loc`]) THEN
  CLOSCALLPAUX_SPLIT_ASM_TAC;;

(* HOL4 proves calls_IS_SUFFIX after calls_code_subset; it is used here *)
let calls_IS_SUFFIX = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g.
     clos_call_calls xs g0 = (ys,g) ==> IS_SUFFIX (SND g) (SND g0)`,
  CLOSCALLPAUX_CALLS_IND_TAC THEN EVERY_CASE_TAC THEN GVS[IS_SUFFIX_REFL] THEN
  ASM_MESON_TAC[IS_SUFFIX_TRANS; IS_SUFFIX_CONS; code_list_IS_SUFFIX;
                SND_insert_each; IS_SUFFIX_REFL]);;

let CLOSCALLPAUX_calls_new_keys = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g.
     clos_call_calls xs g0 = (ys,g) ==>
     set_of_list (MAP FST (SND g)) SUBSET
       IMAGE SUC (domain (FST g)) UNION set_of_list (MAP FST (SND g0))`,
  CLOSCALLPAUX_CALLS_IND_TAC THEN EVERY_CASE_TAC THEN GVS[] THEN
  CLOSCALLPAUX_CALLS_FACTS_TAC THEN
  REWRITE_TAC[GSYM ADD1; SUC_INJ; UNWIND_THM1] THEN
  CLOSCALLPAUX_ABS_PROP_TAC);;

let calls_code_subset = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g.
     clos_call_calls xs g0 = (ys,g) ==>
     IMAGE SUC (domain (FST g0)) SUBSET IMAGE SUC (domain (FST g)) /\
     set_of_list (MAP FST (SND g0)) SUBSET set_of_list (MAP FST (SND g)) /\
     set_of_list (MAP FST (SND g)) SUBSET
       IMAGE SUC (domain (FST g)) UNION set_of_list (MAP FST (SND g0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[calls_subspt; CLOSCALLPAUX_subspt_IMAGE_SUC];
    FIRST_ASSUM(MP_TAC o MATCH_MP calls_IS_SUFFIX) THEN
    REWRITE_TAC[IS_SUFFIX_APPEND] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[MAP_APPEND; SET_OF_LIST_APPEND] THEN SET_TAC[];
    ASM_MESON_TAC[CLOSCALLPAUX_calls_new_keys]]);;

(* more local tools: the induction over clos_call_calls with the further    *)
(* hypotheses of the statement left in the goal (statements are curried     *)
(* with IMP_CONJ first), the unwinding and resolution of the induction     *)
(* hypotheses, and backward chaining through them                          *)

let CLOSCALLPAUX_DISCH_TO_CALLS : tactic =
  let rec go (asl,w as g) =
    if is_forall w then (GEN_TAC THEN go) g
    else if is_imp w then
      if CLOSCALLPAUX_is_calls_eq (ASSUME (lhand w)) then DISCH_TAC g
      else (DISCH_TAC THEN go) g
    else ALL_TAC g in
  go;;

let CLOSCALLPAUX_CALLS_IND2_TAC : tactic =
  MATCH_MP_TAC clos_call_calls_ind THEN REPEAT CONJ_TAC THEN
  CLOSCALLPAUX_DISCH_TO_CALLS THEN
  FIRST_X_ASSUM(MP_TAC o check CLOSCALLPAUX_is_calls_eq) THEN
  REWRITE_TAC[clos_call_calls_def; LET_DEF; LET_END_DEF] THEN
  REPEAT IL1AUX_PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  EVERY_CASE_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  CLOSCALLPAUX_SPLIT_ASM_TAC THEN RVEQ_TAC;;

let CLOSCALLPAUX_UNWIND_IH_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1;
                              FORALL_UNWIND_THM2]) THEN
  CLOSCALLPAUX_SPLIT_ASM_TAC;;

(* each induction hypothesis resolved with the calls equations among the   *)
(* assumptions (and with assumptions equal to its ground antecedents); the *)
(* partly resolved implications are added uncurried                        *)
let CLOSCALLPAUX_IH_CALLS_TAC : tactic = fun (asl,w as gl) ->
  let ths = map snd asl in
  let is_imp_th th = is_imp (snd(strip_forall(concl th))) in
  let eqs = filter CLOSCALLPAUX_is_calls_eq ths in
  let ihs = filter is_imp_th ths in
  let rec resolve depth th =
    let th = REWRITE_RULE[IMP_CONJ] th in
    let vs,body = strip_forall (concl th) in
    if depth = 0 || not (is_imp body) then [th] else
    let a = lhand body in
    let cands =
      if CLOSCALLPAUX_is_calls_eq (ASSUME a) then eqs
      else if not (exists (fun v -> vfree_in v a) vs)
      then filter (fun f -> aconv (concl f) a) ths else [] in
    let rs = mapfilter (fun f -> MATCH_MP th f) cands in
    if rs = [] then [th] else flat (map (resolve (depth-1)) rs) in
  let news = flat (map (fun ih -> resolve 6 ih) ihs) in
  let news = map (fun th -> if is_imp_th th then REWRITE_RULE[GSYM IMP_CONJ] th else th)
                 news in
  let rec dedup acc l = match l with
      [] -> rev acc
    | th::t -> if exists (fun th' -> aconv (concl th') (concl th)) (acc @ ths)
               then dedup acc t else dedup (th::acc) t in
  MAP_EVERY ASSUME_TAC (dedup [] news) gl;;

let CLOSCALLPAUX_DISJOINT_IMAGE_SUC = prove
 (`!s t. DISJOINT s t ==> DISJOINT (IMAGE SUC s) (IMAGE SUC t)`,
  REWRITE_TAC[DISJOINT] THEN SIMP_TAC[GSYM IMAGE_INTER_INJ; SUC_INJ; IMAGE_CLAUSES]);;

let CLOSCALLPAUX_GENLIST_LOC = prove
 (`(!loc m. list_of_seq (\n. loc + 2 * n) m = list_of_seq (\i. 2 * i + loc) m) /\
   (!m. list_of_seq (\n. 2 * n) m = list_of_seq (\i. 2 * i + 0) m)`,
  REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ARITH_TAC);;

let CLOSCALLPAUX_AD_RW = [SND; MAP; ALL_DISTINCT; ADD1; MAP_FST_code_list;
  ALL_DISTINCT_APPEND'; ALL_DISTINCT_REVERSE; SET_OF_LIST_APPEND; SND_insert_each;
  CLOSCALLPAUX_code_list_keys_eq; GSYM IN_SET_OF_LIST; IMAGE_UNION; DISJOINT_UNION;
  set_of_list; IMAGE_CLAUSES; CLOSCALLPAUX_GENLIST_LOC; FST_code_list;
  LISTAUX_LENGTH_ZIP; LENGTH_MAP];;

let CLOSCALLPAUX_is_set_goal w =
  is_binary "SUBSET" w || is_binary "DISJOINT" w || is_binary "IN" w ||
  (is_neg w && is_binary "IN" (rand w));;

let rec CLOSCALLPAUX_BACKCHAIN_TAC n : tactic = fun (asl,w as gl) ->
  (CASE_REWRITE_TAC CLOSCALLPAUX_AD_RW THEN REPEAT CONJ_TAC THEN
   (fun (asl,w as gl) ->
     FIRST [FIRST_ASSUM ACCEPT_TAC;
            (if CLOSCALLPAUX_is_set_goal w then CLOSCALLPAUX_ABS_PROP_TAC else NO_TAC);
            (REWRITE_TAC[ALL_DISTINCT_GENLIST] THEN BETA_TAC THEN ARITH_TAC);
            (if n > 0 then
               FIRST_ASSUM(fun ih ->
                 if is_imp(concl ih) then
                   MATCH_MP_TAC ih THEN CLOSCALLPAUX_BACKCHAIN_TAC (n-1)
                 else NO_TAC)
             else NO_TAC)] gl)) gl;;

(* ------------------------------------------------------------------------- *)

let calls_add_SUC_code_locs = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g.
     clos_call_calls xs g0 = (ys,g) ==>
     set_of_list (MAP FST (SND g)) SUBSET
     set_of_list (MAP FST (SND g0)) UNION IMAGE SUC (set_of_list (code_locs xs))`,
  CLOSCALLPAUX_CALLS_IND_TAC THEN EVERY_CASE_TAC THEN GVS[code_locs_def] THEN
  CLOSCALLPAUX_CALLS_FACTS_TAC THEN
  REWRITE_TAC[SET_OF_LIST_APPEND; set_of_list; IMAGE_UNION; IMAGE_CLAUSES;
              CLOSCALLPAUX_GENLIST_LOC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SET_OF_LIST_APPEND; set_of_list; IMAGE_UNION;
                              IMAGE_CLAUSES; CLOSCALLPAUX_GENLIST_LOC]) THEN
  REWRITE_TAC[GSYM ADD1; SUC_INJ; UNWIND_THM1] THEN CLOSCALLPAUX_ABS_PROP_TAC);;

(* the facts of a calls step for the distinctness of the code table keys *)
let CLOSCALLPAUX_AD_PRE_TAC : tactic =
  CLOSCALLPAUX_UNWIND_IH_TAC THEN REPEAT DISCH_TAC THEN
  IMP_RES_TAC calls_add_SUC_code_locs THEN CLOSCALLPAUX_IH_CALLS_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE
    (code_locs_def :: LET_DEF :: LET_END_DEF :: CLOSCALLPAUX_AD_RW)) THEN
  CLOSCALLPAUX_SPLIT_ASM_TAC THEN
  CLOSCALLPAUX_ADD_FACTS_TAC (fun th ->
    if is_binary "DISJOINT" (concl th) && not (is_comb (lhand (concl th)) &&
       is_comb (rator (lhand (concl th))) &&
       rator (rator (lhand (concl th))) = `IMAGE:(num->num)->(num->bool)->num->bool`)
    then REWRITE_RULE[IMAGE_CLAUSES; ADD1] (MATCH_MP CLOSCALLPAUX_DISJOINT_IMAGE_SUC th)
    else failwith "") THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM IMP_CONJ]);;

let calls_ALL_DISTINCT = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g.
     clos_call_calls xs g0 = (ys,g) /\ ALL_DISTINCT (MAP FST (SND g0)) /\
     ALL_DISTINCT (code_locs xs) /\
     DISJOINT (IMAGE SUC (set_of_list (code_locs xs))) (set_of_list (MAP FST (SND g0)))
     ==> ALL_DISTINCT (MAP FST (SND g))`,
  REWRITE_TAC[IMP_CONJ] THEN CLOSCALLPAUX_CALLS_IND2_TAC THEN
  CLOSCALLPAUX_AD_PRE_TAC THEN CLOSCALLPAUX_BACKCHAIN_TAC 4);;

let compile_ALL_DISTINCT = prove
 (`clos_call_compile do_call x = (y,g,aux) /\ ALL_DISTINCT (code_locs x)
   ==> ALL_DISTINCT (MAP FST aux)`,
  BOOL_CASES_TAC `do_call:bool` THEN REWRITE_TAC[clos_call_compile_def] THENL
   [IL1AUX_PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MP_TAC(SPECL [`x:clos_exp list`; `(LN,[]):num_set # (num # num # clos_exp) list`]
                 calls_ALL_DISTINCT) THEN
    DISCH_THEN(MP_TAC o SPECL [`y:clos_exp list`;
                               `(g,aux):num_set # (num # num # clos_exp) list`]) THEN
    ASM_REWRITE_TAC[SND; MAP; ALL_DISTINCT; set_of_list; DISJOINT_EMPTY];
    REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[MAP; ALL_DISTINCT]]);;

let calls_subg = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g.
     clos_call_calls xs g0 = (ys,g) /\
     ALL_DISTINCT (MAP FST (SND g0)) /\
     ALL_DISTINCT (code_locs xs) /\
     DISJOINT (IMAGE SUC (set_of_list (code_locs xs))) (set_of_list (MAP FST (SND g0)))
     ==> subg g0 g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[subg_def] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (SND (g:num_set # (num # num # clos_exp) list)))`
    ASSUME_TAC THENL [ASM_MESON_TAC[calls_ALL_DISTINCT]; ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[calls_subspt]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP calls_IS_SUFFIX) THEN
  REWRITE_TAC[IS_SUFFIX_APPEND] THEN
  DISCH_THEN(X_CHOOSE_TAC `l:(num # num # clos_exp) list`) THEN
  UNDISCH_TAC `ALL_DISTINCT (MAP FST (SND (g:num_set # (num # num # clos_exp) list)))` THEN
  ASM_REWRITE_TAC[ALOOKUP_APPEND; MAP_APPEND; ALL_DISTINCT_APPEND] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ALOOKUP (l:(num # num # clos_exp) list) k = NONE`
    (fun th -> ASM_REWRITE_TAC[th] THEN CASE_REWRITE_TAC[]) THEN
  REWRITE_TAC[ALOOKUP_NONE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  DISCH_TAC THEN REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `(k:num,v:num # clos_exp)` THEN
  ASM_REWRITE_TAC[]);;

let calls_domain = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g.
     clos_call_calls xs g0 = (ys,g) ==>
     domain (FST g) SUBSET domain (FST g0) UNION IMAGE PRE (set_of_list (MAP FST (SND g)))`,
  let CLOSCALLPAUX_IS_SUFFIX_PRE = prove
   (`!l1 l2:(num # A) list. IS_SUFFIX l1 l2 ==>
       IMAGE PRE (set_of_list (MAP FST l2)) SUBSET IMAGE PRE (set_of_list (MAP FST l1))`,
    REWRITE_TAC[IS_SUFFIX_APPEND] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[MAP_APPEND; SET_OF_LIST_APPEND; IMAGE_UNION] THEN SET_TAC[])
  and CLOSCALLPAUX_keys_PRE = prove
   (`!loc n. IMAGE PRE (set_of_list (REVERSE (list_of_seq (\i. loc + i * 2 + 1) n))) =
             set_of_list (list_of_seq (\i. 2 * i + loc) n)`,
    REWRITE_TAC[CLOSCALLPAUX_code_list_keys_eq; GSYM IMAGE_o] THEN
    REWRITE_TAC[o_DEF; PRE; IMAGE_ID]) in
  CLOSCALLPAUX_CALLS_IND_TAC THEN EVERY_CASE_TAC THEN GVS[] THEN
  CLOSCALLPAUX_IH_TAC THEN IMP_RES_TAC calls_IS_SUFFIX THEN
  CLOSCALLPAUX_ADD_FACTS_TAC (MATCH_MP CLOSCALLPAUX_IS_SUFFIX_PRE) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST_code_list; MAP_FST_code_list; SND_insert_each;
    domain_FST_insert_each; SET_OF_LIST_APPEND; IMAGE_UNION; CLOSCALLPAUX_keys_PRE;
    LISTAUX_list_of_seq_1; set_of_list; IMAGE_CLAUSES;
    ARITH_RULE `!n. PRE (n + 1) = n`; LISTAUX_LENGTH_ZIP; LENGTH_MAP;
    BETA_THM; ARITH_RULE `2 * 0 + loc = loc`; UNION_SUBSET]) THEN
  CLOSCALLPAUX_SPLIT_ASM_TAC THEN
  REWRITE_TAC[FST; SND; MAP; set_of_list; IMAGE_CLAUSES;
              ARITH_RULE `!n. PRE (n + 1) = n`; FST_code_list] THEN
  CLOSCALLPAUX_ABS_PROP_TAC);;

let calls_domain_locs = prove
 (`!xs (g:num_set # (num # num # clos_exp) list) ys g2.
     clos_call_calls xs g = (ys,g2) ==>
     domain (FST g2) SUBSET domain (FST g) UNION set_of_list (code_locs xs)`,
  CLOSCALLPAUX_CALLS_IND_TAC THEN EVERY_CASE_TAC THEN GVS[code_locs_def] THEN
  CLOSCALLPAUX_IH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST_code_list; domain_FST_insert_each; SET_OF_LIST_APPEND;
    LISTAUX_list_of_seq_1; set_of_list; CLOSCALLPAUX_GENLIST_LOC;
    BETA_THM; ARITH_RULE `2 * 0 + loc = loc`; UNION_SUBSET]) THEN
  CLOSCALLPAUX_SPLIT_ASM_TAC THEN
  REWRITE_TAC[FST; SND; SET_OF_LIST_APPEND; set_of_list; CLOSCALLPAUX_GENLIST_LOC;
              FST_code_list] THEN
  CLOSCALLPAUX_ABS_PROP_TAC);;

let wfg'_insert_each = prove
 (`!n (g:num_set # (num # A) list) loc. wfg' g ==> wfg' (insert_each loc n g)`,
  REWRITE_TAC[wfg'_def; SND_insert_each; domain_FST_insert_each] THEN SET_TAC[]);;

let wfg'_code_list = prove
 (`!ls (g:num_set # (num # num # A) list) loc.
     wfg' g /\ set_of_list (list_of_seq (\i. loc + 2 * i) (LENGTH ls)) SUBSET domain (FST g)
     ==> wfg' (clos_call_code_list loc ls g)`,
  REWRITE_TAC[wfg'_def; MAP_FST_code_list; FST_code_list; SET_OF_LIST_APPEND;
              CLOSCALLPAUX_code_list_keys_eq; CLOSCALLPAUX_GENLIST_LOC; UNION_SUBSET] THEN
  MESON_TAC[IMAGE_SUBSET]);;

let CLOSCALLPAUX_db_to_set_LN = prove
 (`!d. db_to_set d = LN <=> !n. ~has_var n d`,
  GEN_TAC THEN MP_TAC(ISPECL [`db_to_set d`; `LN:num_set`] spt_eq_thm) THEN
  REWRITE_TAC[wf_db_to_set; sptree_wf_def] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[lookup_def; lookup_db_to_set] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `lookup x (db_to_set d)` option_nchotomy) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[one]);;

let closed_Fn = prove
 (`clos_call_closed (Fn t loco vs args e) <=>
   !v. has_var v (SND (clos_call_free [e])) ==> v < args`,
  REWRITE_TAC[clos_call_closed_def; clos_call_free_def; LET_DEF; LET_END_DEF] THEN
  IL1AUX_PAIRARG_TAC THEN REWRITE_TAC[SND; CLOSCALLPAUX_db_to_set_LN; has_var_def] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `v - args`) THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `v < args` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `v - args + args = v` (fun th -> ASM_REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `n + args`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let closed_Fn_fv = prove
 (`clos_call_closed (Fn t loco vs args e) <=> !v. clos_fv v [e] ==> v < args`,
  REWRITE_TAC[closed_Fn] THEN MP_TAC(SPEC `[e:clos_exp]` free_thm) THEN
  IL1AUX_PAIRARG_TAC THEN ASM_REWRITE_TAC[SND] THEN SIMP_TAC[]);;

(* local tools: the facts of a calls step for wfg', and backward chaining  *)
(* through the induction hypotheses and some given rules                    *)
let CLOSCALLPAUX_wfg'_CONS = prove
 (`!(g:num_set # (num # A) list) loc v.
     wfg' g /\ loc IN domain (FST g) ==> wfg' (FST g, CONS (loc + 1,v) (SND g))`,
  REWRITE_TAC[wfg'_def; MAP; set_of_list; INSERT_SUBSET; FST; SND; IN_IMAGE; ADD1] THEN
  MESON_TAC[]);;

let rec CLOSCALLPAUX_BACKCHAIN_RULES_TAC rules n : tactic = fun (asl,w as gl) ->
  (CASE_REWRITE_TAC CLOSCALLPAUX_AD_RW THEN REPEAT CONJ_TAC THEN
   (fun (asl,w as gl) ->
     FIRST [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM CONTR_TAC;
            (if CLOSCALLPAUX_is_set_goal w then CLOSCALLPAUX_ABS_PROP_TAC else NO_TAC);
            (REWRITE_TAC[ALL_DISTINCT_GENLIST] THEN BETA_TAC THEN ARITH_TAC);
            (if n > 0 then
               FIRST (map (fun ih -> if is_imp(snd(strip_forall(concl ih))) then
                   MATCH_MP_TAC ih THEN CLOSCALLPAUX_BACKCHAIN_RULES_TAC rules (n-1)
                 else NO_TAC) (map snd asl @ rules))
             else NO_TAC)] gl)) gl;;

let CLOSCALLPAUX_WFG_PRE_TAC : tactic =
  CLOSCALLPAUX_UNWIND_IH_TAC THEN REPEAT DISCH_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[every_Fn_SOME_def; IS_SOME_DEF]) THEN
  CLOSCALLPAUX_SPLIT_ASM_TAC THEN
  CLOSCALLPAUX_IH_CALLS_TAC THEN CLOSCALLPAUX_IH_CALLS_TAC THEN
  CLOSCALLPAUX_IH_CALLS_TAC THEN
  IMP_RES_TAC calls_subspt THEN IMP_RES_TAC calls_length THEN
  RULE_ASSUM_TAC(REWRITE_RULE[subspt_domain; FST_code_list; domain_FST_insert_each;
    LISTAUX_list_of_seq_1; set_of_list; BETA_THM; ARITH_RULE `2 * 0 + loc = loc`;
    UNION_SUBSET; LENGTH_MAP; LISTAUX_LENGTH_ZIP]) THEN
  CLOSCALLPAUX_SPLIT_ASM_TAC;;

let calls_wfg' = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g.
     clos_call_calls xs g0 = (ys,g) /\ every_Fn_SOME xs /\ wfg' g0 ==> wfg' g`,
  REWRITE_TAC[IMP_CONJ] THEN CLOSCALLPAUX_CALLS_IND2_TAC THEN CLOSCALLPAUX_WFG_PRE_TAC THEN
  CLOSCALLPAUX_BACKCHAIN_RULES_TAC
    [wfg'_insert_each; wfg'_code_list; CLOSCALLPAUX_wfg'_CONS] 4);;

let calls_wfg = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g.
     clos_call_calls xs g0 = (ys,g) /\
     ALL_DISTINCT (code_locs xs) /\
     DISJOINT (IMAGE SUC (set_of_list (code_locs xs))) (set_of_list (MAP FST (SND g0))) /\
     every_Fn_SOME xs /\ wfg g0
     ==> wfg g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wfg' (g0:num_set # (num # num # clos_exp) list)` ASSUME_TAC THENL
   [UNDISCH_TAC `wfg (g0:num_set # (num # num # clos_exp) list)` THEN
    SIMP_TAC[wfg_def; wfg'_def; SUBSET_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `wfg' (g:num_set # (num # num # clos_exp) list)` MP_TAC THENL
   [ASM_MESON_TAC[calls_wfg']; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP calls_domain) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP calls_IS_SUFFIX) THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (SND (g:num_set # (num # num # clos_exp) list)))`
    MP_TAC THENL
   [MATCH_MP_TAC calls_ALL_DISTINCT THEN
    MAP_EVERY EXISTS_TAC [`xs:clos_exp list`; `g0:num_set # (num # num # clos_exp) list`;
                          `ys:clos_exp list`] THEN
    ASM_MESON_TAC[wfg_def]; ALL_TAC] THEN
  UNDISCH_TAC `wfg (g0:num_set # (num # num # clos_exp) list)` THEN
  UNDISCH_TAC `domain (FST (g:num_set # (num # num # clos_exp) list)) SUBSET
    domain (FST (g0:num_set # (num # num # clos_exp) list)) UNION
    IMAGE PRE (set_of_list (MAP FST (SND g)))` THEN
  REWRITE_TAC[wfg_def; wfg'_def; IS_SUFFIX_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [UNDISCH_TAC `set_of_list (MAP FST (SND (g:num_set # (num # num # clos_exp) list)))
                 SUBSET IMAGE SUC (domain (FST g))` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o REWRITE_RULE[SUBSET] o
    check (fun th -> is_binary "SUBSET" (concl th) &&
                     can (find_term ((=) `PRE`)) (concl th))) THEN
  ASM_REWRITE_TAC[IN_UNION; IN_IMAGE] THEN STRIP_TAC THENL
   [REWRITE_TAC[MAP_APPEND; SET_OF_LIST_APPEND; IN_UNION] THEN DISJ2_TAC THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:num` THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o SPEC `x':num` o REWRITE_RULE[SUBSET] o
      check (fun th -> is_binary "SUBSET" (concl th) &&
                       can (find_term ((=) `SUC`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[PRE]]);;

(* local helpers for calls_fv1_subset *)
let CLOSCALLPAUX_ALL2_fv = prove
 (`!xs ys. ALL2 (\x y. !v. clos_fv1 v y ==> clos_fv1 v x) xs ys ==> !n. clos_fv n ys ==> clos_fv n xs`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:clos_exp list` list_CASES) THEN
  REWRITE_TAC[ALL2; clos_fv_def; fv_cons] THEN ASM_MESON_TAC[]);;

let CLOSCALLPAUX_EX_calls_list = prove
 (CASE_TERM `!fns (t:tra) i loc n m.
     ~EX (\p. match p with (a,b) -> clos_fv1 ((n + a) + m) b)
         (calls_list t i loc (fns:(num#A)list))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[calls_list_def; EX] THEN
  CASES_ON `h:num#A` THEN
  ASM_REWRITE_TAC[calls_list_def; EX] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM fv1_intro; clos_fv_def; fv_GENLIST_Var_tra] THEN ARITH_TAC);;

let CLOSCALLPAUX_EX_ZIP_fv = prove
 (CASE_TERM `!fns ys n m.
     ALL2 (\x y. !v. clos_fv1 v y ==> clos_fv1 v x) (MAP SND fns) ys ==>
     EX (\p. match p with (a,b) -> clos_fv1 ((n + a) + m) b) (ZIP (MAP FST fns) ys) ==>
     EX (\p. match p with (a,b) -> clos_fv1 ((n + a) + m) b) (fns:(num # clos_exp) list)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ZIP; EX] THEN
  CASES_ON `h:num # clos_exp` THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:clos_exp list` list_CASES) THEN
  REWRITE_TAC[ALL2; MAP; ZIP_def; EX; FST; SND] THEN CASE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let CLOSCALLPAUX_FV1_FIN_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THEN
  CLOSCALLPAUX_ADD_FACTS_TAC (MATCH_MP CLOSCALLPAUX_ALL2_fv) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
  REWRITE_TAC[fv1_thm; HD; fv1_intro] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[fv1_thm; HD; fv1_intro]) THEN
  REWRITE_TAC[GSYM fv1_intro; clos_fv_def; fv_append; fv_GENLIST_Var_tra; SNOC_APPEND;
              LENGTH_APPEND; LENGTH; ARITH_RULE `!x y. x + y < y <=> F`;
              ARITH_RULE `!x y z. x + y + z < y <=> F`;
              ARITH_RULE `!x y. x + y + SUC 0 < y <=> F`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM fv1_intro; clos_fv_def; fv_append]) THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[];;

let CLOSCALLPAUX_FV1_LETREC_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THEN
  REWRITE_TAC[fv1_thm; HD; calls_list_length; LISTAUX_LENGTH_ZIP; LENGTH_MAP;
              CLOSCALLPAUX_EX_calls_list] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN REPEAT STRIP_TAC THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun (a,e) ->
     try ASSUME_TAC (MATCH_MP (MATCH_MP CLOSCALLPAUX_EX_ZIP_fv a) e)
     with Failure _ -> ALL_TAC)
     (allpairs (fun a e -> (a,e)) ths ths)) THEN
  ASM_MESON_TAC[];;

let calls_fv1_subset = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g.
     clos_call_calls xs g0 = (ys,g) ==>
     ALL2 (\x y. flip clos_fv1 y SUBSET flip clos_fv1 x) xs ys`,
  CLOSCALLPAUX_CALLS_IND_TAC THEN EVERY_CASE_TAC THEN GVS[] THEN
  CLOSCALLPAUX_IH_TAC THEN IMP_RES_TAC calls_length THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_EQ_NUM_compute]) THEN
  CLOSCALLPAUX_SPLIT_ASM_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL2; SUBSET; IN; C_THM]) THEN
  REWRITE_TAC[ALL2; SUBSET; IN; C_THM] THEN
  (fun (asl,w as g) ->
     if can (find_term (fun t -> is_const t && fst(dest_const t) = "clos_Letrec")) w
     then CLOSCALLPAUX_FV1_LETREC_TAC g else CLOSCALLPAUX_FV1_FIN_TAC g));;

let calls_fv_imp = prove
 (`clos_call_calls xs (g0:num_set # (num # num # clos_exp) list) = (ys,g) /\ clos_fv v ys
   ==> clos_fv v xs`,
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP calls_fv1_subset) THEN
  REWRITE_TAC[SUBSET; IN; C_THM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CLOSCALLPAUX_ALL2_fv) THEN ASM_MESON_TAC[]);;

let FST_insert_each_same = prove
 (`!p n (g0:num_set # A) (g0':num_set # A).
     FST g0 = FST g0' ==> FST (insert_each p n g0) = FST (insert_each p n g0')`,
  MATCH_MP_TAC insert_each_ind THEN REWRITE_TAC[insert_each_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?a b. g0' = (a:num_set,b:A)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[insert_each_def] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[FST]);;

let code_list_replace_SND = prove
 (`!loc fns (g0:B # (num # num # A) list) g g0' ls.
     clos_call_code_list loc fns g0 = g /\ FST g0 = FST g0' /\
     SND g = APPEND ls (SND g0)
     ==> clos_call_code_list loc fns g0' = (FST g, APPEND ls (SND g0'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> is_eq (concl th) && is_var (rhs (concl th)))) THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM PAIR] THEN
  REWRITE_TAC[PAIR_EQ; FST_code_list; SND_code_list_ZIP] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SND_code_list_ZIP; APPEND_RCANCEL]) THEN
  ASM_REWRITE_TAC[APPEND_RCANCEL]);;

(* local helper: clos_call_calls only puts entries in front of SND g, and   *)
(* only FST g decides anything (HOL4's calls_acc_0, calls_replace_SND and   *)
(* calls_acc below follow from it)                                          *)
let CLOSCALLPAUX_insert_each_APPEND = prove
 (`!p n (g:num_set # (B list)) l.
     insert_each p n (FST g, APPEND (SND g) l) =
     (FST (insert_each p n g), APPEND (SND (insert_each p n g)) l)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM PAIR] THEN
  REWRITE_TAC[PAIR_EQ; SND_insert_each; SND] THEN
  MATCH_MP_TAC FST_insert_each_same THEN REWRITE_TAC[FST]);;

let CLOSCALLPAUX_code_list_APPEND = prove
 (`!loc fns (g:B # (num # num # A) list) l.
     clos_call_code_list loc fns (FST g, APPEND (SND g) l) =
     (FST (clos_call_code_list loc fns g),
      APPEND (SND (clos_call_code_list loc fns g)) l)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM PAIR] THEN
  REWRITE_TAC[PAIR_EQ; FST_code_list; SND_code_list_ZIP; FST; SND; APPEND_ASSOC]);;

let CLOSCALLPAUX_ACC_STEP_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[CLOSCALLPAUX_insert_each_APPEND;
    CLOSCALLPAUX_code_list_APPEND; FST; SND]) THEN
  (fun (asl,w as gl) ->
     let ths = map snd asl in
     let is_ih th = let vs,b = strip_forall (concl th) in
                    vs <> [] && is_eq b && CLOSCALLPAUX_is_calls_eq (ASSUME b) in
     let ihs = filter is_ih ths in
     RULE_ASSUM_TAC(fun th -> if CLOSCALLPAUX_is_calls_eq th then REWRITE_RULE ihs th
                              else th) gl) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN CLOSCALLPAUX_SPLIT_ASM_TAC THEN RVEQ_TAC;;

let CLOSCALLPAUX_calls_APPEND = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g.
     clos_call_calls xs g0 = (ys,g) ==>
     !l. clos_call_calls xs (FST g0, APPEND (SND g0) l) =
         (ys, (FST g, APPEND (SND g) l))`,
  CLOSCALLPAUX_CALLS_IND_TAC THEN EVERY_CASE_TAC THEN GVS[] THEN CLOSCALLPAUX_IH_TAC THEN
  CLOSCALLPAUX_ACC_STEP_TAC THEN CLOSCALLPAUX_ACC_STEP_TAC THEN CLOSCALLPAUX_ACC_STEP_TAC THEN
  ASM_REWRITE_TAC[] THEN GVS[]);;

let calls_replace_SND = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g g0' ls.
     clos_call_calls xs g0 = (ys,g) /\ FST g0 = FST g0' /\ SND g = APPEND ls (SND g0)
     ==> clos_call_calls xs g0' = (ys,(FST g,APPEND ls (SND g0')))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `clos_call_calls xs (FST (g0:num_set # (num # num # clos_exp) list),[])`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ys0:clos_exp list` (X_CHOOSE_THEN
    `h:num_set # (num # num # clos_exp) list` ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[FST; SND; APPEND] o
    MATCH_MP CLOSCALLPAUX_calls_APPEND) THEN
  SUBGOAL_THEN `g0' = (FST (g0:num_set # (num # num # clos_exp) list),
                       SND (g0':num_set # (num # num # clos_exp) list))` SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM PAIR] THEN ASM_REWRITE_TAC[PAIR_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `ys0:clos_exp list = ys /\
                FST (h:num_set # (num # num # clos_exp) list) =
                FST (g:num_set # (num # num # clos_exp) list) /\ SND h = ls`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `SND (g0:num_set # (num # num # clos_exp) list)` o
      check (is_forall o concl)) THEN
    REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `SND (g:num_set # (num # num # clos_exp) list) =
                 APPEND ls (SND (g0:num_set # (num # num # clos_exp) list))` THEN
    ASM_REWRITE_TAC[SND; FST; APPEND_RCANCEL] THEN MESON_TAC[];
    ASM_REWRITE_TAC[]]);;

let insert_each'_def = cake_def_wf
  `MEASURE (\x:(num # A) list # num # num # (num_set # (num # A) list).
              FST (SND (SND x)))`
  TERM_TAC
  `(insert_each' (gt:(num # A) list) p 0 (g:num_set # (num # A) list) = g) /\
   (insert_each' gt p (SUC n) (g1,g2) =
      insert_each' gt (p + 2) n
        (insert p one g1, CONS (p + 1,THE (ALOOKUP gt (p + 1))) g2))`;;

let insert_each'_ind = cake_ind "insert_each'";;

let wfg_insert_each' = prove
 (`!gt p n (g:num_set # (num # A) list).
     wfg g /\ DISJOINT (set_of_list (list_of_seq (\i. p + 2 * i) n)) (domain (FST g))
     ==> wfg (insert_each' gt p n g)`,
  MATCH_MP_TAC insert_each'_ind THEN REWRITE_TAC[insert_each'_def] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wfg_def; FST; SND; IN_DISJOINT; IN_SET_OF_LIST;
                              MEM_GENLIST]) THEN
  REWRITE_TAC[wfg_def; FST; SND; MAP; set_of_list; domain_insert; IMAGE_CLAUSES;
              ALL_DISTINCT; IN_DISJOINT; IN_SET_OF_LIST; MEM_GENLIST; IN_INSERT] THEN
  ASM_REWRITE_TAC[GSYM IN_SET_OF_LIST; ADD1; IN_IMAGE] THEN
  REWRITE_TAC[NOT_EXISTS_THM; EQ_ADD_RCANCEL] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `0` THEN ASM_ARITH_TAC;
    UNDISCH_TAC `x = p:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `SUC m` THEN ASM_REWRITE_TAC[LT_SUC] THEN
    ARITH_TAC]);;

let FST_insert_each' = prove
 (`!gt p n (g:num_set # (num # A) list).
     FST (insert_each' gt p n g) = FST (insert_each p n g)`,
  MATCH_MP_TAC insert_each'_ind THEN REWRITE_TAC[insert_each'_def; insert_each_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FST_insert_each_same THEN REWRITE_TAC[FST]);;

let MAP_FST_insert_each' = prove
 (`!gt p n (g:num_set # (num # A) list).
     MAP FST (SND (insert_each' gt p n g)) =
     APPEND (REVERSE (list_of_seq (\i. p + i * 2 + 1) n)) (MAP FST (SND g))`,
  MATCH_MP_TAC insert_each'_ind THEN
  REWRITE_TAC[insert_each'_def; LIST_OF_SEQ; REVERSE; APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SND; MAP; GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[o_DEF; MULT_CLAUSES; ADD_CLAUSES] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ARITH_TAC);;

let SND_insert_each' = prove
 (`!gt p n (g:num_set # (num # A) list).
     SND (insert_each' gt p n g) =
     APPEND (REVERSE (list_of_seq (\i. (2 * i + p + 1, THE (ALOOKUP gt (2 * i + p + 1))))
                                  n))
            (SND g)`,
  MATCH_MP_TAC insert_each'_ind THEN
  REWRITE_TAC[insert_each'_def; LIST_OF_SEQ; REVERSE; APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SND; GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[o_DEF; MULT_CLAUSES; ADD_CLAUSES] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  SUBGOAL_THEN `(2 + 2 * x) + p + 1 = 2 * x + (p + 2) + 1` SUBST1_TAC THENL
   [ARITH_TAC; REWRITE_TAC[]]);;

let calls_el_sing = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g i.
     clos_call_calls xs g0 = (ys,g) /\
     i < LENGTH xs /\
     ALL_DISTINCT (MAP FST (SND g0)) /\
     ALL_DISTINCT (code_locs xs) /\
     DISJOINT (IMAGE SUC (set_of_list (code_locs xs))) (set_of_list (MAP FST (SND g0))) /\
     wfg g0 /\ every_Fn_SOME xs
     ==> ?ga gb.
           clos_call_calls [EL i xs] ga = ([EL i ys],gb) /\
           subg g0 ga /\ subg ga gb /\ subg gb g /\ wfg ga /\ wfg gb /\
           DISJOINT (IMAGE SUC (set_of_list (code_locs [EL i xs])))
                    (set_of_list (MAP FST (SND ga))) /\
           set_of_list (MAP FST (SND ga)) SUBSET
             set_of_list (MAP FST (SND g0)) UNION
             IMAGE SUC (set_of_list (code_locs (TAKE i xs))) /\
           set_of_list (code_locs [EL i xs]) DIFF domain (FST gb) SUBSET
             set_of_list (code_locs xs) DIFF domain (FST g)`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; LT]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN STRUCT_CASES_TAC (ISPEC `t:clos_exp list` list_CASES) THEN
  DISCH_TAC THENL
   [(* a single expression: i = 0 *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `i = 0` SUBST_ALL_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP calls_sing) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[EL; HD; TAKE_DEF; code_locs_def; set_of_list; IMAGE_CLAUSES; UNION_EMPTY;
                SUBSET_REFL] THEN
    MAP_EVERY EXISTS_TAC [`g0:num_set # (num # num # clos_exp) list`;
                          `g:num_set # (num # num # clos_exp) list`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    SUBGOAL_THEN `ALL_DISTINCT (MAP FST (SND (g:num_set # (num # num # clos_exp) list)))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC calls_ALL_DISTINCT THEN
      MAP_EVERY EXISTS_TAC [`[h:clos_exp]`; `g0:num_set # (num # num # clos_exp) list`;
                            `[y:clos_exp]`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[subg_refl] THEN CONJ_TAC THENL
     [MATCH_MP_TAC calls_subg THEN
      MAP_EVERY EXISTS_TAC [`[h:clos_exp]`; `[y:clos_exp]`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC calls_wfg THEN
      MAP_EVERY EXISTS_TAC [`[h:clos_exp]`; `g0:num_set # (num # num # clos_exp) list`;
                            `[y:clos_exp]`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* at least two expressions *)
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check CLOSCALLPAUX_is_calls_eq) THEN
  ONCE_REWRITE_TAC[clos_call_calls_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT IL1AUX_PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP calls_sing o check (fun th ->
    CLOSCALLPAUX_is_calls_eq th && rand(rator(lhs(concl th))) = `[h:clos_exp]`)) THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN
   `ALL_DISTINCT (code_locs [h]) /\ ALL_DISTINCT (code_locs (CONS h' t')) /\
    DISJOINT (set_of_list (code_locs [h])) (set_of_list (code_locs (CONS h' t'))) /\
    DISJOINT (IMAGE SUC (set_of_list (code_locs [h])))
             (set_of_list (MAP FST (SND (g0:num_set # (num # num # clos_exp) list)))) /\
    DISJOINT (IMAGE SUC (set_of_list (code_locs (CONS h' t'))))
             (set_of_list (MAP FST (SND g0))) /\
    every_Fn_SOME [h] /\ every_Fn_SOME (CONS h' t')`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ALL_DISTINCT (code_locs (CONS h (CONS h' t')))` THEN
    UNDISCH_TAC `DISJOINT (IMAGE SUC (set_of_list (code_locs (CONS h (CONS h' t')))))
                   (set_of_list (MAP FST (SND (g0:num_set # (num # num # clos_exp) list))))` THEN
    UNDISCH_TAC `every_Fn_SOME (CONS h (CONS h' t'))` THEN
    REWRITE_TAC[code_locs_def; every_Fn_SOME_def; LET_DEF; LET_END_DEF;
                ALL_DISTINCT_APPEND'; SET_OF_LIST_APPEND; IMAGE_UNION; DISJOINT_UNION] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL_DISTINCT (MAP FST (SND (g':num_set # (num # num # clos_exp) list))) /\ wfg g' /\
    subg (g0:num_set # (num # num # clos_exp) list) g' /\
    set_of_list (MAP FST (SND g')) SUBSET
      set_of_list (MAP FST (SND g0)) UNION IMAGE SUC (set_of_list (code_locs [h]))`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC calls_ALL_DISTINCT THEN
      MAP_EVERY EXISTS_TAC [`[h:clos_exp]`; `g0:num_set # (num # num # clos_exp) list`;
                            `[y:clos_exp]`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC calls_wfg THEN
      MAP_EVERY EXISTS_TAC [`[h:clos_exp]`; `g0:num_set # (num # num # clos_exp) list`;
                            `[y:clos_exp]`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC calls_subg THEN
      MAP_EVERY EXISTS_TAC [`[h:clos_exp]`; `[y:clos_exp]`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC calls_add_SUC_code_locs THEN
      MAP_EVERY EXISTS_TAC [`[y:clos_exp]`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE SUC (set_of_list (code_locs (CONS h' t'))))
                  (set_of_list (MAP FST (SND (g':num_set # (num # num # clos_exp) list))))`
   ASSUME_TAC THENL
   [MP_TAC(ISPECL [`set_of_list (code_locs [h])`; `set_of_list (code_locs (CONS h' t'))`]
      CLOSCALLPAUX_DISJOINT_IMAGE_SUC) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `set_of_list (MAP FST (SND (g':num_set # (num # num # clos_exp) list))) SUBSET
      set_of_list (MAP FST (SND (g0:num_set # (num # num # clos_exp) list))) UNION
      IMAGE SUC (set_of_list (code_locs [h]))` THEN
    UNDISCH_TAC `DISJOINT (IMAGE SUC (set_of_list (code_locs (CONS h' t'))))
                  (set_of_list (MAP FST (SND (g0:num_set # (num # num # clos_exp) list))))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL_DISTINCT (MAP FST (SND (g:num_set # (num # num # clos_exp) list))) /\ wfg g /\
    subg (g':num_set # (num # num # clos_exp) list) g`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC calls_ALL_DISTINCT THEN
      MAP_EVERY EXISTS_TAC [`CONS (h':clos_exp) t'`;
                            `g':num_set # (num # num # clos_exp) list`;
                            `e2':clos_exp list`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC calls_wfg THEN
      MAP_EVERY EXISTS_TAC [`CONS (h':clos_exp) t'`;
                            `g':num_set # (num # num # clos_exp) list`;
                            `e2':clos_exp list`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC calls_subg THEN
      MAP_EVERY EXISTS_TAC [`CONS (h':clos_exp) t'`; `e2':clos_exp list`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CASES_ON `i:num` THENL
   [(* the first expression *)
    REWRITE_TAC[EL; HD; APPEND; TAKE_DEF; code_locs_def; set_of_list; IMAGE_CLAUSES;
                UNION_EMPTY; SUBSET_REFL] THEN
    MAP_EVERY EXISTS_TAC [`g0:num_set # (num # num # clos_exp) list`;
                          `g':num_set # (num # num # clos_exp) list`] THEN
    ASM_SIMP_TAC[subg_refl] THEN
    REWRITE_TAC[SUBSET_REFL; LET_DEF; LET_END_DEF; SET_OF_LIST_APPEND] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION] THEN X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `SUC x IN set_of_list (MAP FST (SND (g:num_set # (num # num # clos_exp) list)))`
      MP_TAC THENL
     [UNDISCH_TAC `wfg (g:num_set # (num # num # clos_exp) list)` THEN
      REWRITE_TAC[wfg_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `x:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`CONS (h':clos_exp) t'`; `g':num_set # (num # num # clos_exp) list`;
                  `e2':clos_exp list`; `g:num_set # (num # num # clos_exp) list`]
           calls_add_SUC_code_locs) THEN
    ASM_REWRITE_TAC[SUBSET; IN_UNION] THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
    UNDISCH_TAC `wfg (g':num_set # (num # num # clos_exp) list)` THEN
    REWRITE_TAC[wfg_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_IMAGE; SUC_INJ] THEN
    REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM] THEN CONJ_TAC THEN X_GEN_TAC `z:num` THENL
     [ASM_MESON_TAC[];
      UNDISCH_TAC `DISJOINT (set_of_list (code_locs [h]))
                            (set_of_list (code_locs (CONS h' t')))` THEN
      REWRITE_TAC[IN_DISJOINT] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* a later expression *)
  FIRST_X_ASSUM(MP_TAC o SPECL [`g':num_set # (num # num # clos_exp) list`;
    `e2':clos_exp list`; `g:num_set # (num # num # clos_exp) list`; `n:num`] o
    check (is_forall o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; LT_SUC]) THEN ASM_REWRITE_TAC[LENGTH] THEN
  DISCH_THEN(X_CHOOSE_THEN `ga:num_set # (num # num # clos_exp) list`
    (X_CHOOSE_THEN `gb:num_set # (num # num # clos_exp) list` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`ga:num_set # (num # num # clos_exp) list`;
                        `gb:num_set # (num # num # clos_exp) list`] THEN
  REWRITE_TAC[EL; TL; APPEND] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC subg_trans THEN
    EXISTS_TAC `g':num_set # (num # num # clos_exp) list` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONJUNCT2 TAKE] THEN
  ONCE_REWRITE_TAC[code_locs_cons] THEN
  REWRITE_TAC[code_locs_def; APPEND_NIL] THEN
  REWRITE_TAC[SET_OF_LIST_APPEND; IMAGE_UNION] THEN
  UNDISCH_TAC `set_of_list (MAP FST (SND (g':num_set # (num # num # clos_exp) list))) SUBSET
    set_of_list (MAP FST (SND (g0:num_set # (num # num # clos_exp) list))) UNION
    IMAGE SUC (set_of_list (code_locs [h]))` THEN
  UNDISCH_TAC `set_of_list (MAP FST (SND (ga:num_set # (num # num # clos_exp) list))) SUBSET
    set_of_list (MAP FST (SND (g':num_set # (num # num # clos_exp) list))) UNION
    IMAGE SUC (set_of_list (code_locs (TAKE n (CONS h' t'))))` THEN
  UNDISCH_TAC `set_of_list (code_locs [EL n (CONS h' t')]) DIFF
    domain (FST (gb:num_set # (num # num # clos_exp) list)) SUBSET
    set_of_list (code_locs (CONS h' t')) DIFF
    domain (FST (g:num_set # (num # num # clos_exp) list))` THEN
  SET_TAC[]);;

(* HOL4's pairmaparg_tac (an ML tactic) is not needed here *)

let insert_each_pair_arg = prove
 (`insert_each x y (p,q:A) = (FST (insert_each x y (p,q':A)), q)`,
  GEN_REWRITE_TAC LAND_CONV [GSYM PAIR] THEN
  REWRITE_TAC[PAIR_EQ; SND_insert_each; SND] THEN
  MATCH_MP_TAC FST_insert_each_same THEN REWRITE_TAC[FST]);;

(* HOL4 [local] *)
let calls_acc_0 = prove
 (`!xs (tmp:num_set # (num # num # clos_exp) list) x r.
     APPEND x r = SND tmp ==>
     clos_call_calls xs tmp =
     ((I:clos_exp list->clos_exp list) ## (I:num_set->num_set) ## flip APPEND r)
       (clos_call_calls xs (FST tmp, x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `clos_call_calls xs (FST (tmp:num_set # (num # num # clos_exp) list), x)`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ys:clos_exp list` (X_CHOOSE_THEN
    `h:num_set # (num # num # clos_exp) list` ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `r:(num # num # clos_exp) list` o REWRITE_RULE[FST; SND] o
    MATCH_MP CLOSCALLPAUX_calls_APPEND) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[GSYM(ISPEC `h:num_set # (num # num # clos_exp) list` PAIR)] THEN
  REWRITE_TAC[PAIR_MAP_THM; I_THM; C_THM; FST; SND]);;

let calls_acc = prove
 (`!xs d old res d1 aux.
     clos_call_calls xs (d,[]) = (res,d1,aux) ==>
     clos_call_calls xs (d,old) = (res,d1,APPEND aux old)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `old:(num # num # clos_exp) list` o
    REWRITE_RULE[FST; SND; APPEND] o MATCH_MP CLOSCALLPAUX_calls_APPEND) THEN
  REWRITE_TAC[]);;

(* properties of value relation *)

(* local helpers *)
let CLOSCALLPAUX_ALL2_EXISTS = prove
 (`!(R:A->B->bool) l. (!x. MEM x l ==> ?y. R x y) ==> ?l'. ALL2 R l l'`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THENL
   [EXISTS_TAC `[]:B list` THEN REWRITE_TAC[ALL2]; ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `l':B list`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:A`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `y:B`) THEN EXISTS_TAC `CONS (y:B) l'` THEN
  ASM_REWRITE_TAC[ALL2]);;

let CLOSCALLPAUX_ALL2_env_rel = prove
 (`!(R:A->B->bool) env1 env2 a es.
     ALL2 R env1 env2 ==> clos_callProof_env_rel R env1 env2 a es`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  ASM_REWRITE_TAC[clos_callProof_env_rel_def]);;

let CLOSCALLPAUX_MAP_FST_calls_list = prove
 (`!fns:(num # A) list t i loc. MAP FST (calls_list t i loc fns) = MAP FST fns`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[calls_list_def; MAP] THEN
  CASES_ON `h:num # A` THEN ASM_REWRITE_TAC[calls_list_def; MAP; FST]);;

let CLOSCALLPAUX_recclosure_rel_MAP_FST = prove
 (`recclosure_rel g l code loc fns1 fns2 ==> MAP FST fns2 = MAP FST fns1`,
  REWRITE_TAC[recclosure_rel_def; LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN REPEAT IL1AUX_PAIRARG_TAC THEN COND_CASES_TAC THEN
  REPEAT IL1AUX_PAIRARG_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[CLOSCALLPAUX_MAP_FST_calls_list] THEN
  IMP_RES_TAC calls_length THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN
  ASM_SIMP_TAC[MAP_ZIP; LENGTH_MAP]);;

let CLOSCALLPAUX_MAP_FST_SING = prove
 (`!(l:(A # B) list) n. MAP FST l = [n] ==> ?b. l = [(n,b)]`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11; MAP_EQ_NIL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `SND (h:A # B)` THEN
  ASM_MESON_TAC[PAIR]);;

let v_rel_exists = prove
 (`!v1. wfv g l code v1 ==> ?v2. clos_callProof_v_rel g l code v1 v2`,
  let ALL2_TAC =
    MP_TAC(ISPECL [`clos_callProof_v_rel g l code`; `l':clos_v list`]
      CLOSCALLPAUX_ALL2_EXISTS) THEN
    MP_TAC(ISPECL [`clos_callProof_v_rel g l code`; `l0:clos_v list`]
      CLOSCALLPAUX_ALL2_EXISTS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `env2:clos_v list`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `vs2:clos_v list`) in
  MATCH_MP_TAC v_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wfv_def; clos_callProof_v_rel_def; GSYM ALL_MEM] THEN
  TRY (MESON_TAC[]) THENL
   [(* Block *)
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`clos_callProof_v_rel g l code`; `l':clos_v list`]
       CLOSCALLPAUX_ALL2_EXISTS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `vs':clos_v list`) THEN
    MAP_EVERY EXISTS_TAC [`clos_Block n vs'`; `vs':clos_v list`] THEN ASM_REWRITE_TAC[];
    (* Closure *)
    STRUCT_CASES_TAC(ISPEC `o':num option` option_nchotomy) THEN
    REWRITE_TAC[wfv_def; option_INJ; option_DISTINCT; GSYM ALL_MEM] THEN
    STRIP_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CLOSCALLPAUX_recclosure_rel_MAP_FST) THEN
    DISCH_THEN(X_CHOOSE_THEN `b:clos_exp` SUBST_ALL_TAC o
      MATCH_MP CLOSCALLPAUX_MAP_FST_SING o REWRITE_RULE[MAP; FST]) THEN
    ALL2_TAC THEN
    MAP_EVERY EXISTS_TAC [`clos_Closure (SOME x) vs2 env2 n b`; `x:num`;
                          `vs2:clos_v list`; `env2:clos_v list`; `b:clos_exp`] THEN
    ASM_SIMP_TAC[CLOSCALLPAUX_ALL2_env_rel];
    (* Recclosure *)
    STRUCT_CASES_TAC(ISPEC `o':num option` option_nchotomy) THEN
    REWRITE_TAC[wfv_def; option_INJ; option_DISTINCT; GSYM ALL_MEM] THEN
    STRIP_TAC THEN STRIP_TAC THEN ALL2_TAC THEN
    MAP_EVERY EXISTS_TAC [`clos_Recclosure (SOME x) vs2 env2 fns2 n`; `x:num`;
                          `vs2:clos_v list`; `env2:clos_v list`;
                          `fns2:(num # clos_exp) list`] THEN
    ASM_SIMP_TAC[CLOSCALLPAUX_ALL2_env_rel]]);;

(* HOL4 [local] code_includes_SUBMAP comes after subg_insert_each' in HOL4;  *)
(* it is used here                                                          *)
let code_includes_SUBMAP = prove
 (`code_includes (x:(A # B) list) y1 /\ y1 SUBMAP y2 ==> code_includes x y2`,
  REWRITE_TAC[code_includes_def] THEN MESON_TAC[FLOOKUP_SUBMAP]);;

(* local helpers: monotonicity of recclosure_rel and of v_rel *)
let CLOSCALLPAUX_recclosure_rel_mono = GEN_ALL @@ prove
 (`recclosure_rel g l code loc fns1 fns2 /\ subg g g' /\ l SUBSET l' /\
   code SUBMAP code' ==> recclosure_rel g' l' code' loc fns1 fns2`,
  REWRITE_TAC[recclosure_rel_def; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN EXISTS_TAC `g0:num_set # (num # num # clos_exp) list` THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REPEAT IL1AUX_PAIRARG_TAC THEN COND_CASES_TAC THEN REPEAT IL1AUX_PAIRARG_TAC THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [MESON_TAC[];
         (MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l:num->bool` THEN ASM_REWRITE_TAC[]);
         (MATCH_MP_TAC (GEN_ALL code_includes_SUBMAP) THEN
          EXISTS_TAC `code:(num,num # clos_exp)fmap` THEN ASM_REWRITE_TAC[]);
         (MATCH_MP_TAC subg_trans THEN
          EXISTS_TAC `g:num_set # (num # num # clos_exp) list` THEN ASM_REWRITE_TAC[])]);;

let CLOSCALLPAUX_recclosure_rel_SUBMAP = GEN_ALL @@ prove
 (`recclosure_rel g l code loc fns1 fns2 /\ code SUBMAP code'
   ==> recclosure_rel g l code' loc fns1 fns2`,
  REWRITE_TAC[recclosure_rel_def; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN EXISTS_TAC `g0:num_set # (num # num # clos_exp) list` THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REPEAT IL1AUX_PAIRARG_TAC THEN COND_CASES_TAC THEN REPEAT IL1AUX_PAIRARG_TAC THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [MESON_TAC[];
         (MATCH_MP_TAC (GEN_ALL code_includes_SUBMAP) THEN
          EXISTS_TAC `code:(num,num # clos_exp)fmap` THEN ASM_REWRITE_TAC[])]);;

let CLOSCALLPAUX_ALL2_MEM_MONO = prove
 (`!(R:A->B->bool) R' l1 l2.
     (!x y. MEM x l1 /\ MEM y l2 /\ R x y ==> R' x y) /\ ALL2 R l1 l2 ==> ALL2 R' l1 l2`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `l2:B list` list_CASES) THEN
  REWRITE_TAC[ALL2; MEM] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

(* the closure cases of the monotonicity proofs of v_rel *)
let CLOSCALLPAUX_VREL_CLOS_TAC (rrtac:tactic) : tactic =
  MAP_EVERY EXISTS_TAC [`loc:num`; `vs2:clos_v list`; `env2:clos_v list`] THEN
  (fun (asl,w) -> EXISTS_TAC (fst(dest_exists w)) (asl,w)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [rrtac;
    MATCH_MP_TAC CLOSCALLPAUX_ALL2_MEM_MONO THEN
    EXISTS_TAC `clos_callProof_v_rel g l code` THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "clos_callProof_env_rel")) (concl th))) THEN
    MATCH_MP_TAC clos_callProof_env_rel_mono THEN ASM_MESON_TAC[]];;

let CLOSCALLPAUX_VREL_MONO_TAC (rrtac:tactic) : tactic =
  MATCH_MP_TAC clos_callProof_v_rel_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_callProof_v_rel_def] THEN TRY (MESON_TAC[]) THEN
  REPEAT STRIP_TAC THENL
   [EXISTS_TAC `vs':clos_v list` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSCALLPAUX_ALL2_MEM_MONO THEN
    EXISTS_TAC `clos_callProof_v_rel g l code` THEN ASM_MESON_TAC[];
    CLOSCALLPAUX_VREL_CLOS_TAC rrtac;
    CLOSCALLPAUX_VREL_CLOS_TAC rrtac];;

let CLOSCALLPAUX_v_rel_subg = prove
 (`!g l code v1 v2. clos_callProof_v_rel g l code v1 v2 ==>
     !g' l'. subg g g' /\ l SUBSET l' ==> clos_callProof_v_rel g' l' code v1 v2`,
  CLOSCALLPAUX_VREL_MONO_TAC
   (MATCH_MP_TAC CLOSCALLPAUX_recclosure_rel_mono THEN
    MAP_EVERY EXISTS_TAC [`g:num_set # (num # num # clos_exp) list`; `l:num->bool`;
                          `code:(num,num # clos_exp)fmap`] THEN
    ASM_REWRITE_TAC[SUBMAP_REFL]));;

let v_rel_subg = prove
 (`!g l code v1 v2 g' l'.
     clos_callProof_v_rel g l code v1 v2 /\ subg g g' /\ l SUBSET l' ==>
     clos_callProof_v_rel g' l' code v1 v2`,
  MESON_TAC[CLOSCALLPAUX_v_rel_subg]);;

let code_includes_subg = prove
 (`subg (g1:A spt # (B # C) list) g2 ==>
   code_includes (SND g2) code ==> code_includes (SND g1) code`,
  REWRITE_TAC[subg_def; code_includes_def] THEN MESON_TAC[]);;

let code_includes_ALOOKUP = prove
 (`code_includes (al:(A # B) list) code /\ ALOOKUP al loc = SOME r
   ==> FLOOKUP code loc = SOME r`,
  REWRITE_TAC[code_includes_def] THEN MESON_TAC[]);;

let CLOSCALLPAUX_REV_TAKE = prove
 (`!l:A list n. n = LENGTH l ==>
     REVERSE (TAKE n (REVERSE l)) = l /\ REVERSE (DROP n (REVERSE l)) = []`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM LENGTH_REVERSE] THEN
  REWRITE_TAC[TAKE_LENGTH_ID; DROP_LENGTH_NIL; REVERSE_REVERSE; REVERSE]);;

(* rewrite the goal with the reverse of the assumption tm (an equation) *)
let CLOSCALLPAUX_LENGTH_BACK_TAC (tm:term) : tactic =
  FIRST_ASSUM(fun th -> if concl th = tm then REWRITE_TAC[GSYM th] else NO_TAC);;

(* the Closure case of dest_closure_v_rel_lookup *)
let CLOSCALLPAUX_lookup_Closure = prove
 (`!g l code loc loc0 vs1 vs2 env1' env2' k bod1 bod2 env1 env2 x.
     dest_closure max_app (SOME loc) (clos_Closure (SOME loc0) vs1 env1' k bod1) env1 =
       SOME x /\
     recclosure_rel g l code loc0 [(k,bod1)] [(k,bod2)] /\
     ALL2 (clos_callProof_v_rel g l code) vs1 vs2 /\
     ALL2 (clos_callProof_v_rel g l code) env1 env2 /\ ~(loc IN l)
     ==> ?e l1 xs n ls g01 g1 l1' tra.
           x = Full_app e (APPEND env1 l1) [] /\ EL n xs = (LENGTH env1,e) /\
           clos_call_calls (MAP SND xs) g01 = (ls,g1) /\ n < LENGTH ls /\
           subg (clos_call_code_list (loc - 2 * n) (ZIP (MAP FST xs) ls) g1) g /\
           ALOOKUP (SND g) (loc + 1) = SOME (LENGTH env1,EL n ls) /\
           dest_closure max_app (SOME loc) (clos_Closure (SOME loc0) vs2 env2' k bod2) env2 =
             SOME (Full_app (clos_Call tra 0 (loc + 1) (GENLIST_Var tra 1 (LENGTH env1)))
                            (APPEND env2 l1') []) /\
           code_includes (SND (clos_call_code_list (loc - 2 * n) (ZIP (MAP FST xs) ls) g1))
                         code`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dest_closure_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[check_loc_def; option_INJ; LENGTH_EQ_NIL] THEN
  ASM_CASES_TAC `vs1:clos_v list = []` THEN ASM_REWRITE_TAC[option_DISTINCT; LIST_REL_NIL] THEN
  ASM_CASES_TAC `loc0:num = loc` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  ASM_CASES_TAC `k = LENGTH (env1:clos_v list)` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  REWRITE_TAC[LENGTH; ADD_CLAUSES; LT_REFL; SUB_0; APPEND_NIL] THEN
  ASM_CASES_TAC `0 < LENGTH (env1:clos_v list)` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  CLOSCALLPAUX_LENGTH_BACK_TAC
    `LENGTH (env1:clos_v list) = LENGTH (env2:clos_v list)` THEN
  SUBGOAL_THEN `REVERSE (TAKE (LENGTH (env1:clos_v list)) (REVERSE env1)) = env1 /\
                REVERSE (DROP (LENGTH env1) (REVERSE env1)) = [] /\
                REVERSE (TAKE (LENGTH env1) (REVERSE (env2:clos_v list))) = env2 /\
                REVERSE (DROP (LENGTH env1) (REVERSE env2)) = []`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[CLOSCALLPAUX_REV_TAKE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH; SUB_0; ADD_CLAUSES; LT_REFL; APPEND_NIL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rand(concl th) = `x:app_kind`)) THEN
  SIMP_TAC[CLOSCALLPAUX_REV_TAKE; APPEND_NIL] THEN
  SUBGOAL_THEN `0 < LENGTH (env2:clos_v list)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `recclosure_rel g l code loc [LENGTH (env1:clos_v list),(bod1:clos_exp)]
                 [LENGTH env1,(bod2:clos_exp)]` THEN
  REWRITE_TAC[recclosure_rel_def; LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN IL1AUX_PAIRARG_TAC THEN COND_CASES_TAC THENL
   [ALL_TAC;
    IL1AUX_PAIRARG_TAC THEN REWRITE_TAC[LENGTH; ONE; LIST_OF_SEQ; set_of_list] THEN
    REWRITE_TAC[INSERT_SUBSET; MULT_CLAUSES; ADD_CLAUSES] THEN ASM_MESON_TAC[]] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; SND; FST; LENGTH; calls_list_def]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP calls_sing o check CLOSCALLPAUX_is_calls_eq) THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONS_11; PAIR_EQ; ZIP_def; clos_call_code_list_def]) THEN
  CLOSCALLPAUX_SPLIT_ASM_TAC THEN RVEQ_TAC THEN
  CLOSCALLPAUX_LENGTH_BACK_TAC
    `LENGTH (env1:clos_v list) = LENGTH (env2:clos_v list)` THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `LENGTH (env1:clos_v list) = LENGTH (env2:clos_v list)`)) THEN
  MAP_EVERY EXISTS_TAC [`bod1:clos_exp`; `env1':clos_v list`;
    `[LENGTH (env1:clos_v list),(bod1:clos_exp)]`;
    `0`; `[y:clos_exp]`; `insert_each loc (SUC 0) (g0:num_set # (num # num # clos_exp) list)`;
    `new_g':num_set # (num # num # clos_exp) list`; `env2':clos_v list`; `tra:tra`] THEN
  ASM_REWRITE_TAC[MAP; SND; FST; EL; HD; LENGTH; ZIP_def; ARITH_RULE `x - 2 * 0 = x`;
                  ARITH_RULE `0 < SUC 0`] THEN
  UNDISCH_TAC `subg (clos_call_code_list loc [LENGTH (env1:clos_v list),(y:clos_exp)]
                  (new_g':num_set # (num # num # clos_exp) list))
                (g:num_set # (num # num # clos_exp) list)` THEN
  REWRITE_TAC[subg_def] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[ALOOKUP_code_list] THEN
  SUBGOAL_THEN `(some i. i < LENGTH [LENGTH (env1:clos_v list),(y:clos_exp)] /\
                         loc + 1 = loc + 2 * i + 1) = SOME 0`
    SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH; ARITH_RULE `i < SUC 0 /\ x + 1 = x + 2 * i + 1 <=> i = 0`; some_EQ];
    CASE_REWRITE_TAC[EL; HD]]);;

(* the Recclosure case of dest_closure_v_rel_lookup *)
let CLOSCALLPAUX_lookup_Recclosure = prove
 (`!g l code loc loc0 vs1 vs2 env1' env2' fns1 fns2 j env1 env2 x.
     dest_closure max_app (SOME loc) (clos_Recclosure (SOME loc0) vs1 env1' fns1 j) env1 =
       SOME x /\
     recclosure_rel g l code loc0 fns1 fns2 /\
     ALL2 (clos_callProof_v_rel g l code) vs1 vs2 /\
     ALL2 (clos_callProof_v_rel g l code) env1 env2 /\ ~(loc IN l)
     ==> ?e l1 xs n ls g01 g1 l1' tra.
           x = Full_app e (APPEND env1 l1) [] /\ EL n xs = (LENGTH env1,e) /\
           clos_call_calls (MAP SND xs) g01 = (ls,g1) /\ n < LENGTH ls /\
           subg (clos_call_code_list (loc - 2 * n) (ZIP (MAP FST xs) ls) g1) g /\
           ALOOKUP (SND g) (loc + 1) = SOME (LENGTH env1,EL n ls) /\
           dest_closure max_app (SOME loc) (clos_Recclosure (SOME loc0) vs2 env2' fns2 j)
             env2 =
             SOME (Full_app (clos_Call tra 0 (loc + 1) (GENLIST_Var tra 1 (LENGTH env1)))
                            (APPEND env2 l1') []) /\
           code_includes (SND (clos_call_code_list (loc - 2 * n) (ZIP (MAP FST xs) ls) g1))
                         code`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k bod. EL j fns1 = (k:num,bod:clos_exp)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  REWRITE_TAC[dest_closure_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[check_loc_def; OPTION_MAP_DEF; option_INJ; LENGTH_EQ_NIL; GSYM NOT_LT] THEN
  ASM_CASES_TAC `j < LENGTH (fns1:(num # clos_exp) list)` THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN
  ASM_CASES_TAC `vs1:clos_v list = []` THEN ASM_REWRITE_TAC[option_DISTINCT; LIST_REL_NIL] THEN
  ASM_CASES_TAC `loc = 2 * j + loc0` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  ASM_CASES_TAC `k = LENGTH (env1:clos_v list)` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  REWRITE_TAC[LENGTH; ADD_CLAUSES; LT_REFL; SUB_0; APPEND_NIL; LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `0 < LENGTH (env1:clos_v list)` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  RULE_ASSUM_TAC(SIMP_RULE[CLOSCALLPAUX_REV_TAKE; APPEND_NIL; option_INJ]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rand(concl th) = `x:app_kind`)) THEN
  UNDISCH_TAC `recclosure_rel g l code loc0 fns1 fns2` THEN
  REWRITE_TAC[recclosure_rel_def; LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN IL1AUX_PAIRARG_TAC THEN COND_CASES_TAC THENL
   [ALL_TAC;
    IL1AUX_PAIRARG_TAC THEN REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_GENLIST] THEN
    STRIP_TAC THEN UNDISCH_TAC `~(2 * j + loc0 IN l)` THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN EXISTS_TAC `j:num` THEN
                            ASM_REWRITE_TAC[] THEN NO_TAC)] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `LENGTH (env1:clos_v list) = LENGTH (env2:clos_v list)`)) THEN
  SUBGOAL_THEN `EL j (calls_list tra n loc0 (fns1:(num # clos_exp) list)) =
                (LENGTH (env1:clos_v list),
                 clos_Call tra 0 ((2 * j + loc0) + 1) (GENLIST_Var tra 1 (LENGTH env1)))`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[calls_list_MAPi; EL_MAPi] THEN
    REWRITE_TAC[FST; PAIR_EQ; injectivity "clos_exp"] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[calls_list_length; LENGTH; SUB_0; ADD_CLAUSES; LT_REFL; APPEND_NIL] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CLOSCALLPAUX_REV_TAKE; APPEND_NIL; LT_REFL] THEN
  MAP_EVERY EXISTS_TAC [`bod:clos_exp`;
    `APPEND (list_of_seq (clos_Recclosure (SOME loc0) [] env1' fns1) (LENGTH fns1)) env1'`;
    `fns1:(num # clos_exp) list`; `j:num`; `es':clos_exp list`;
    `insert_each loc0 (LENGTH (fns1:(num # clos_exp) list))
       (g0:num_set # (num # num # clos_exp) list)`;
    `new_g':num_set # (num # num # clos_exp) list`;
    `APPEND (list_of_seq (clos_Recclosure (SOME loc0) [] env2'
               (calls_list tra n loc0 (fns1:(num # clos_exp) list))) (LENGTH fns1)) env2'`;
    `tra:tra`] THEN
  REWRITE_TAC[APPEND_ASSOC; ARITH_RULE `(2 * j + loc0) - 2 * j = loc0`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP calls_length o check CLOSCALLPAUX_is_calls_eq) THEN
  REWRITE_TAC[LENGTH_MAP] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `subg (clos_call_code_list loc0
                       (ZIP (MAP FST (fns1:(num # clos_exp) list)) (es':clos_exp list))
                       (new_g':num_set # (num # num # clos_exp) list))
                    (g:num_set # (num # num # clos_exp) list)` THEN
  REWRITE_TAC[subg_def] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[ALOOKUP_code_list] THEN
  SUBGOAL_THEN `(some i. i < LENGTH (ZIP (MAP FST (fns1:(num # clos_exp) list))
                                         (es':clos_exp list)) /\
                         (2 * j + loc0) + 1 = loc0 + 2 * i + 1) = SOME j`
    SUBST1_TAC THENL
   [REWRITE_TAC[LISTAUX_LENGTH_ZIP; LENGTH_MAP] THEN
    SUBGOAL_THEN `!i. i < LENGTH (fns1:(num # clos_exp) list) /\
                      (2 * j + loc0) + 1 = loc0 + 2 * i + 1 <=> i = j`
      (fun th -> REWRITE_TAC[th; some_EQ]) THEN
    X_GEN_TAC `i:num` THEN EQ_TAC THENL
     [ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC];
    CASE_REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[EL_ZIP; LENGTH_MAP; EL_MAP] THEN REWRITE_TAC[FST]);;

let dest_closure_v_rel_lookup = prove
 (`dest_closure max_app (SOME loc) v1 env1 = SOME x /\
   clos_callProof_v_rel g l code v1 v2 /\
   ALL2 (clos_callProof_v_rel g l code) env1 env2 /\
   wfg g /\ loc IN domain (FST g) /\ ~(loc IN l)
   ==> ?e l1 xs n ls g01 g1 l1' tra (i:A).
         x = Full_app e (APPEND env1 l1) [] /\ EL n xs = (LENGTH env1,e) /\
         clos_call_calls (MAP SND xs) g01 = (ls,g1) /\ n < LENGTH ls /\
         subg (clos_call_code_list (loc - 2 * n) (ZIP (MAP FST xs) ls) g1) g /\
         ALOOKUP (SND g) (loc + 1) = SOME (LENGTH env1,EL n ls) /\
         dest_closure max_app (SOME loc) v2 env2 =
           SOME (Full_app (clos_Call tra 0 (loc + 1) (GENLIST_Var tra 1 (LENGTH env1)))
                          (APPEND env2 l1') []) /\
         code_includes (SND (clos_call_code_list (loc - 2 * n) (ZIP (MAP FST xs) ls) g1))
                       code`,
  REWRITE_TAC[EXISTS_SIMP] THEN STRIP_TAC THEN
  UNDISCH_TAC `dest_closure max_app (SOME loc) v1 env1 = SOME x` THEN
  UNDISCH_TAC `clos_callProof_v_rel g l code v1 v2` THEN
  CASES_ON `v1:clos_v` THEN REWRITE_TAC[clos_callProof_v_rel_def] THEN
  TRY (REWRITE_TAC[dest_closure_def] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN NO_TAC) THEN
  STRIP_TAC THEN RVEQ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC CLOSCALLPAUX_lookup_Closure; MATCH_MP_TAC CLOSCALLPAUX_lookup_Recclosure] THEN
  ASM_MESON_TAC[]);;

let CLOSCALLPAUX_TAKE_DROP_APPEND = prove
 (`!(l1:A list) l2 n. LENGTH l1 = n ==>
     TAKE n (APPEND l1 l2) = l1 /\ DROP n (APPEND l1 l2) = l2`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[TAKE_LENGTH_APPEND; DROP_LENGTH_APPEND]);;

let CLOSCALLPAUX_ALL2_REV_TAKE = prove
 (`!(R:A->B->bool) l1 l2 n.
     ALL2 R l1 l2 ==>
     ALL2 R (REVERSE (TAKE n (REVERSE l1))) (REVERSE (TAKE n (REVERSE l2))) /\
     ALL2 R (REVERSE (DROP n (REVERSE l1))) (REVERSE (DROP n (REVERSE l2)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EVERY2_REVERSE THEN
  REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP EVERY2_REVERSE) THEN
  ASM_SIMP_TAC[EVERY2_TAKE; EVERY2_DROP]);;

let CLOSCALLPAUX_env_rel_MEM_MONO = prove
 (`!(R:A->B->bool) e1 e2 a es es'.
     clos_callProof_env_rel R e1 e2 a es /\ (!x. MEM x es' ==> MEM x es)
     ==> clos_callProof_env_rel R e1 e2 a es'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_callProof_env_rel_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN REWRITE_TAC[EXISTS_MEM] THEN
  STRIP_TAC THEN X_GEN_TAC `x:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* the Closure case of dest_closure_v_rel *)
let CLOSCALLPAUX_dest_closure_v_rel_Closure = prove
 (CASE_TERM
  `!g l code loco loc0 vs1 vs2 cenv1 cenv2 k bod1 bod2 env1 env2 x1.
     dest_closure max_app loco (clos_Closure (SOME loc0) vs1 cenv1 k bod1) env1 =
       SOME x1 /\
     recclosure_rel g l code loc0 [(k,bod1)] [(k,bod2)] /\
     ALL2 (clos_callProof_v_rel g l code) vs1 vs2 /\
     clos_callProof_env_rel (clos_callProof_v_rel g l code) cenv1 cenv2 0 [(k,bod2)] /\
     ALL2 (clos_callProof_v_rel g l code) env1 env2
     ==> ?x2. dest_closure max_app loco (clos_Closure (SOME loc0) vs2 cenv2 k bod2) env2 =
                SOME x2 /\
              match x1 with
                Partial_app c1 -> ?c2. x2 = Partial_app c2 /\
                                       clos_callProof_v_rel g l code c1 c2
              | Full_app e1 args1 rest1 ->
                  ?fns1 loc i fns2 args2 rest2 n.
                    x2 = Full_app (SND (EL i fns2)) args2 rest2 /\
                    (let m = if is_Recclosure (clos_Closure (SOME loc0) vs2 cenv2 k bod2)
                             then LENGTH fns2 else 0 in
                     n + m <= LENGTH args1 /\ n + m <= LENGTH args2 /\
                     ALL2 (clos_callProof_v_rel g l code) (TAKE (n + m) args1)
                                                          (TAKE (n + m) args2) /\
                     clos_callProof_env_rel (clos_callProof_v_rel g l code)
                       (DROP (n + m) args1) (DROP (n + m) args2) m [EL i fns2]) /\
                    ALL2 (clos_callProof_v_rel g l code) rest1 rest2 /\
                    recclosure_rel g l code loc fns1 fns2 /\
                    i < LENGTH fns1 /\ EL i fns1 = (n,e1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dest_closure_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[is_Recclosure_def; LET_DEF; LET_END_DEF; ADD_CLAUSES] THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (vs2:clos_v list) = LENGTH (vs1:clos_v list) /\
                LENGTH (env2:clos_v list) = LENGTH (env1:clos_v list)`
    (fun th -> REWRITE_TAC[th] THEN STRIP_ASSUME_TAC th) THENL
   [ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> rand(concl th) = `SOME (x1:app_kind)`)) THEN
  COND_CASES_TAC THENL [POP_ASSUM STRIP_ASSUME_TAC; REWRITE_TAC[option_DISTINCT]] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[UNWIND_THM1] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[UNWIND_THM1] THENL
   [SUBGOAL_THEN `k - LENGTH (vs1:clos_v list) <= LENGTH (env1:clos_v list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (APPEND (REVERSE (TAKE (k - LENGTH vs1) (REVERSE env1)))
                                 (vs1:clos_v list)) = k /\
                  LENGTH (APPEND (REVERSE (TAKE (k - LENGTH vs1) (REVERSE env2)))
                                 (vs2:clos_v list)) = k`
      STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[LENGTH_APPEND; LENGTH_REVERSE; LENGTH_TAKE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`[(k:num),(bod1:clos_exp)]`; `loc0:num`; `0`;
      `[(k:num),(bod2:clos_exp)]`;
      `APPEND (APPEND (REVERSE (TAKE (k - LENGTH (vs1:clos_v list)) (REVERSE env2))) vs2)
              (cenv2:clos_v list)`;
      `REVERSE (DROP (k - LENGTH (vs1:clos_v list)) (REVERSE (env2:clos_v list)))`;
      `k:num`] THEN
    REWRITE_TAC[EL; HD; SND; LENGTH; ARITH_RULE `0 < SUC 0`] THEN
    ASM_SIMP_TAC[CLOSCALLPAUX_TAKE_DROP_APPEND] THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LE_ADD] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EVERY2_APPEND_suff THEN ASM_SIMP_TAC[CLOSCALLPAUX_ALL2_REV_TAKE];
      ASM_SIMP_TAC[CLOSCALLPAUX_ALL2_REV_TAKE]];
    ONCE_REWRITE_TAC[clos_callProof_v_rel_def] THEN
    MAP_EVERY EXISTS_TAC [`loc0:num`; `APPEND env2 vs2:clos_v list`; `cenv2:clos_v list`;
                          `bod2:clos_exp`] THEN
    ASM_SIMP_TAC[EVERY2_APPEND_suff]]);;

(* the Recclosure case of dest_closure_v_rel *)
let CLOSCALLPAUX_dest_closure_v_rel_Recclosure = prove
 (CASE_TERM
  `!g l code loco loc0 vs1 vs2 cenv1 cenv2 fns1 fns2 j env1 env2 x1.
     dest_closure max_app loco (clos_Recclosure (SOME loc0) vs1 cenv1 fns1 j) env1 =
       SOME x1 /\
     recclosure_rel g l code loc0 fns1 fns2 /\
     ALL2 (clos_callProof_v_rel g l code) vs1 vs2 /\
     clos_callProof_env_rel (clos_callProof_v_rel g l code) cenv1 cenv2 (LENGTH fns2) fns2 /\
     ALL2 (clos_callProof_v_rel g l code) env1 env2
     ==> ?x2. dest_closure max_app loco (clos_Recclosure (SOME loc0) vs2 cenv2 fns2 j) env2 =
                SOME x2 /\
              match x1 with
                Partial_app c1 -> ?c2. x2 = Partial_app c2 /\
                                       clos_callProof_v_rel g l code c1 c2
              | Full_app e1 args1 rest1 ->
                  ?fns1 loc i fns2' args2 rest2 n.
                    x2 = Full_app (SND (EL i fns2')) args2 rest2 /\
                    (let m = if is_Recclosure (clos_Recclosure (SOME loc0) vs2 cenv2 fns2 j)
                             then LENGTH fns2' else 0 in
                     n + m <= LENGTH args1 /\ n + m <= LENGTH args2 /\
                     ALL2 (clos_callProof_v_rel g l code) (TAKE (n + m) args1)
                                                          (TAKE (n + m) args2) /\
                     clos_callProof_env_rel (clos_callProof_v_rel g l code)
                       (DROP (n + m) args1) (DROP (n + m) args2) m [EL i fns2']) /\
                    ALL2 (clos_callProof_v_rel g l code) rest1 rest2 /\
                    recclosure_rel g l code loc fns1 fns2' /\
                    i < LENGTH fns1 /\ EL i fns1 = (n,e1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSCALLPAUX_recclosure_rel_MAP_FST) THEN
  SUBGOAL_THEN `LENGTH (fns2:(num # clos_exp) list) = LENGTH (fns1:(num # clos_exp) list) /\
                LENGTH (vs2:clos_v list) = LENGTH (vs1:clos_v list) /\
                LENGTH (env2:clos_v list) = LENGTH (env1:clos_v list)`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_REL_LENGTH; LENGTH_MAP]; ALL_TAC] THEN
  SUBGOAL_THEN `?k bod. EL j fns1 = (k:num,bod:clos_exp)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `?k2 bod2. EL j fns2 = (k2:num,bod2:clos_exp)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_CASES_TAC `j < LENGTH (fns1:(num # clos_exp) list)` THENL
   [ALL_TAC;
    UNDISCH_TAC `dest_closure max_app loco (clos_Recclosure (SOME loc0) vs1 cenv1 fns1 j)
                   env1 = SOME x1` THEN
    ASM_REWRITE_TAC[dest_closure_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM NOT_LT; option_DISTINCT; LET_DEF; LET_END_DEF] THEN
    CASE_REWRITE_TAC[option_DISTINCT]] THEN
  SUBGOAL_THEN `k2:num = k` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `MAP FST (fns2:(num # clos_exp) list) = MAP FST (fns1:(num # clos_exp) list)` THEN
    DISCH_THEN(MP_TAC o AP_TERM `EL j:num list -> num`) THEN
    ASM_SIMP_TAC[EL_MAP] THEN REWRITE_TAC[FST];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> rand(concl th) = `SOME (x1:app_kind)`)) THEN
  SUBGOAL_THEN `~(LENGTH (fns1:(num # clos_exp) list) <= j)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NOT_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[dest_closure_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[is_Recclosure_def; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[option_DISTINCT]; POP_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM])] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[UNWIND_THM1] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[UNWIND_THM1] THENL
   [SUBGOAL_THEN `k - LENGTH (vs1:clos_v list) <= LENGTH (env1:clos_v list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `LENGTH (APPEND (APPEND (REVERSE (TAKE (k - LENGTH vs1) (REVERSE env1)))
                             (vs1:clos_v list))
        (list_of_seq (clos_Recclosure (SOME loc0) [] cenv1 fns1) (LENGTH fns1))) =
      k + LENGTH (fns1:(num # clos_exp) list) /\
      LENGTH (APPEND (APPEND (REVERSE (TAKE (k - LENGTH vs1) (REVERSE env2)))
                             (vs2:clos_v list))
        (list_of_seq (clos_Recclosure (SOME loc0) [] cenv2 fns2) (LENGTH fns1))) =
      k + LENGTH fns1`
      STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[LENGTH_APPEND; LENGTH_REVERSE; LENGTH_TAKE; LENGTH_LIST_OF_SEQ] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`fns1:(num # clos_exp) list`; `loc0:num`; `j:num`;
      `fns2:(num # clos_exp) list`;
      `APPEND (APPEND (APPEND (REVERSE (TAKE (k - LENGTH (vs1:clos_v list)) (REVERSE env2)))
                              vs2)
         (list_of_seq (clos_Recclosure (SOME loc0) [] cenv2 fns2)
                      (LENGTH (fns1:(num # clos_exp) list))))
         (cenv2:clos_v list)`;
      `REVERSE (DROP (k - LENGTH (vs1:clos_v list)) (REVERSE (env2:clos_v list)))`;
      `k:num`] THEN
    ASM_REWRITE_TAC[SND] THEN
    ASM_SIMP_TAC[CLOSCALLPAUX_TAKE_DROP_APPEND] THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LE_ADD] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC EVERY2_APPEND_suff THEN CONJ_TAC THENL
       [MATCH_MP_TAC EVERY2_APPEND_suff THEN ASM_SIMP_TAC[CLOSCALLPAUX_ALL2_REV_TAKE];
        REWRITE_TAC[LIST_REL_GENLIST] THEN REPEAT STRIP_TAC THEN
        ONCE_REWRITE_TAC[clos_callProof_v_rel_def] THEN
        MAP_EVERY EXISTS_TAC [`loc0:num`; `[]:clos_v list`; `cenv2:clos_v list`;
                              `fns2:(num # clos_exp) list`] THEN
        ASM_REWRITE_TAC[ALL2]];
      SUBGOAL_THEN `MEM (k,bod2) (fns2:(num # clos_exp) list)` ASSUME_TAC THENL
       [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          lhs(concl th) = `EL j (fns2:(num # clos_exp) list)`)) THEN
        MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC CLOSCALLPAUX_env_rel_MEM_MONO THEN
      EXISTS_TAC `fns2:(num # clos_exp) list` THEN
      UNDISCH_TAC `clos_callProof_env_rel (clos_callProof_v_rel g l code) cenv1 cenv2
                     (LENGTH (fns2:(num # clos_exp) list)) fns2` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[MEM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[CLOSCALLPAUX_ALL2_REV_TAKE]];
    ONCE_REWRITE_TAC[clos_callProof_v_rel_def] THEN
    MAP_EVERY EXISTS_TAC [`loc0:num`; `APPEND env2 vs2:clos_v list`; `cenv2:clos_v list`;
                          `fns2:(num # clos_exp) list`] THEN
    ASM_SIMP_TAC[EVERY2_APPEND_suff]]);;

let dest_closure_v_rel = prove
 (CASE_TERM
  `dest_closure max_app loco v1 env1 = SOME x1 /\
   clos_callProof_v_rel g l code v1 v2 /\
   ALL2 (clos_callProof_v_rel g l code) env1 env2
   ==> ?x2. dest_closure max_app loco v2 env2 = SOME x2 /\
            match x1 with
              Partial_app c1 -> ?c2. x2 = Partial_app c2 /\ clos_callProof_v_rel g l code c1 c2
            | Full_app e1 args1 rest1 ->
                ?fns1 loc i fns2 args2 rest2 n.
                  x2 = Full_app (SND (EL i fns2)) args2 rest2 /\
                  (let m = if is_Recclosure v2 then LENGTH fns2 else 0 in
                   n + m <= LENGTH args1 /\ n + m <= LENGTH args2 /\
                   ALL2 (clos_callProof_v_rel g l code) (TAKE (n + m) args1)
                                                        (TAKE (n + m) args2) /\
                   clos_callProof_env_rel (clos_callProof_v_rel g l code)
                     (DROP (n + m) args1) (DROP (n + m) args2) m [EL i fns2]) /\
                  ALL2 (clos_callProof_v_rel g l code) rest1 rest2 /\
                  recclosure_rel g l code loc fns1 fns2 /\
                  i < LENGTH fns1 /\ EL i fns1 = (n,e1)`,
  STRIP_TAC THEN
  UNDISCH_TAC `dest_closure max_app loco v1 env1 = SOME x1` THEN
  UNDISCH_TAC `clos_callProof_v_rel g l code v1 v2` THEN
  CASES_ON `v1:clos_v` THEN REWRITE_TAC[clos_callProof_v_rel_def] THEN
  TRY (REWRITE_TAC[dest_closure_def] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN NO_TAC) THEN
  STRIP_TAC THEN RVEQ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC CLOSCALLPAUX_dest_closure_v_rel_Closure;
    MATCH_MP_TAC CLOSCALLPAUX_dest_closure_v_rel_Recclosure] THEN
  ASM_MESON_TAC[]);;

let dest_closure_partial_wfv = prove
 (`dest_closure max_app loco v env = SOME (Partial_app x) /\
   ALL (wfv g l code) env /\ wfv g l code v ==> wfv g l code x`,
  RW[dest_closure_def] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  CASES_ON `v:clos_v` THEN CASE_REWRITE_TAC[] THEN
  REPEAT (IL1AUX_PAIRARG_TAC) THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; injectivity "app_kind";
              distinctness "app_kind"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  STRUCT_CASES_TAC(ISPEC `a0:num option` option_nchotomy) THEN
  REWRITE_TAC[wfv_def; ALL_APPEND] THEN SIMP_TAC[]);;

let dest_closure_full_wfv = prove
 (`dest_closure max_app loco v env = SOME (Full_app e args rest) /\
   wfv g l code v /\ ALL (wfv g l code) env
   ==> ?(ys:A) (g01:B) loc fns1 fns2 i.
         ALL (wfv g l code) args /\ ALL (wfv g l code) rest /\
         recclosure_rel g l code loc fns1 fns2 /\
         SND (EL i fns1) = e /\ i < LENGTH fns1`,
  RW[dest_closure_def] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  CASES_ON `v:clos_v` THEN CASE_REWRITE_TAC[] THEN
  REPEAT (IL1AUX_PAIRARG_TAC) THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; injectivity "app_kind";
              distinctness "app_kind"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  STRUCT_CASES_TAC(ISPEC `a0:num option` option_nchotomy) THEN
  REWRITE_TAC[wfv_def; ALL_APPEND] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`x:num`; `[a3,e]:(num # clos_exp) list`;
                         `fns2:(num # clos_exp) list`; `0`] THEN
    ASM_SIMP_TAC[EVERY_REVERSE; EVERY_TAKE; EVERY_DROP; EL; HD; SND; LENGTH; ARITH];
    MAP_EVERY EXISTS_TAC [`x:num`; `a3:(num # clos_exp) list`;
                          `fns2:(num # clos_exp) list`; `a4:num`] THEN
    ASM_SIMP_TAC[EVERY_REVERSE; EVERY_TAKE; EVERY_DROP; EVERY_GENLIST; wfv_def; ALL; SND] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_ARITH_TAC]]);;

let env_rel_DROP = prove
 (`clos_callProof_env_rel (R:A->B->bool) (DROP x l1) (DROP x l2) x es /\
   ALL2 R (TAKE x l1) (TAKE x l2) /\ x <= LENGTH l1 /\ x <= LENGTH l2
   ==> clos_callProof_env_rel R l1 l2 0 es`,
  REWRITE_TAC[clos_callProof_env_rel_def; LENGTH_DROP] THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (l1:A list) - x = LENGTH (l2:B list) - x <=> LENGTH l1 = LENGTH l2`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `x <= LENGTH (l1:A list)` THEN UNDISCH_TAC `x <= LENGTH (l2:B list)` THEN
    ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  ASM_CASES_TAC `LENGTH (l1:A list) = LENGTH (l2:B list)` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `ALL2 (R:A->B->bool) (APPEND (TAKE x l1) (DROP x l1))
                   (APPEND (TAKE x l2) (DROP x l2))` MP_TAC THENL
     [MATCH_MP_TAC EVERY2_APPEND_suff THEN ASM_REWRITE_TAC[]; REWRITE_TAC[TAKE_DROP]];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i < x` THENL
   [UNDISCH_TAC `ALL2 (R:A->B->bool) (TAKE x l1) (TAKE x l2)` THEN
    ASM_SIMP_TAC[LIST_REL_EL_EQN; LENGTH_TAKE; EL_TAKE] THEN
    DISCH_TAC THEN MAP_EVERY UNDISCH_TAC
      [`i < x:num`; `x <= LENGTH (l1:A list)`; `x <= LENGTH (l2:B list)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i - x:num` o check (is_forall o concl)) THEN
  SUBGOAL_THEN `!n. n + x + (i - x) = n + 0 + i` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `~(i < x:num)` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `i < LENGTH (l1:A list) /\ i < LENGTH (l2:B list)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(i < x:num)`; `i - x < LENGTH (l1:A list) - x`;
                           `i - x < LENGTH (l2:B list) - x`] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(R:A->B->bool) (EL (i - x) (DROP x l1)) (EL (i - x) (DROP x l2))` THEN
  SUBGOAL_THEN `i - x + x = i:num` ASSUME_TAC THENL
   [UNDISCH_TAC `~(i < x:num)` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_DROP]);;

let env_rel_DROP_args = prove
 (`clos_callProof_env_rel (R:A->B->bool) (DROP n l1) (DROP n l2) a [(n,e)] /\
   ALL2 R (TAKE n l1) (TAKE n l2) /\ n <= LENGTH l1 /\ n <= LENGTH l2
   ==> clos_callProof_env_rel R l1 l2 a [(0,e)]`,
  REWRITE_TAC[clos_callProof_env_rel_def; LENGTH_DROP] THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (l1:A list) - n = LENGTH (l2:B list) - n <=> LENGTH l1 = LENGTH l2`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `n <= LENGTH (l1:A list)` THEN UNDISCH_TAC `n <= LENGTH (l2:B list)` THEN
    ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  ASM_CASES_TAC `LENGTH (l1:A list) = LENGTH (l2:B list)` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `ALL2 (R:A->B->bool) (APPEND (TAKE n l1) (DROP n l1))
                   (APPEND (TAKE n l2) (DROP n l2))` MP_TAC THENL
     [MATCH_MP_TAC EVERY2_APPEND_suff THEN ASM_REWRITE_TAC[]; REWRITE_TAC[TAKE_DROP]];
    ALL_TAC] THEN
  REWRITE_TAC[EX] THEN CASE_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i < n` THENL
   [UNDISCH_TAC `ALL2 (R:A->B->bool) (TAKE n l1) (TAKE n l2)` THEN
    ASM_SIMP_TAC[LIST_REL_EL_EQN; LENGTH_TAKE; EL_TAKE] THEN
    DISCH_TAC THEN MAP_EVERY UNDISCH_TAC
      [`i < n:num`; `n <= LENGTH (l1:A list)`; `n <= LENGTH (l2:B list)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i - n:num` o check (is_forall o concl)) THEN
  REWRITE_TAC[EX] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n + a + (i - n) = 0 + a + i` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `~(i < n:num)` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `i < LENGTH (l1:A list) /\ i < LENGTH (l2:B list)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(i < n:num)`; `i - n < LENGTH (l1:A list) - n`;
                           `i - n < LENGTH (l2:B list) - n`] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(R:A->B->bool) (EL (i - n) (DROP n l1)) (EL (i - n) (DROP n l2))` THEN
  SUBGOAL_THEN `i - n + n = i:num` ASSUME_TAC THENL
   [UNDISCH_TAC `~(i < n:num)` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_DROP]);;

(* two blocks with disjoint keys can be swapped in an association list *)
let CLOSCALLPAUX_ALOOKUP_SWAP = prove
 (`!(A:(K # V) list) B C.
     ALL_DISTINCT (MAP FST (APPEND A (APPEND B C)))
     ==> ALOOKUP (APPEND A (APPEND B C)) = ALOOKUP (APPEND B (APPEND A C)) /\
         ALL_DISTINCT (MAP FST (APPEND B (APPEND A C)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MAP_APPEND; ALL_DISTINCT_APPEND; MEM_APPEND] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[FUN_EQ_THM; ALOOKUP_APPEND] THEN X_GEN_TAC `k:K` THEN
  ASM_CASES_TAC `MEM (k:K) (MAP FST (A:(K # V) list))` THENL
   [SUBGOAL_THEN `ALOOKUP (B:(K # V) list) k = NONE` SUBST1_TAC THENL
     [REWRITE_TAC[ALOOKUP_NONE] THEN ASM_MESON_TAC[]; REWRITE_TAC[option_CASE]];
    SUBGOAL_THEN `ALOOKUP (A:(K # V) list) k = NONE` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[ALOOKUP_NONE]; REWRITE_TAC[option_CASE]]] THEN
  STRUCT_CASES_TAC(ISPEC `ALOOKUP (A:(K # V) list) k` option_nchotomy) THEN
  REWRITE_TAC[option_CASE] THEN
  STRUCT_CASES_TAC(ISPEC `ALOOKUP (B:(K # V) list) k` option_nchotomy) THEN
  REWRITE_TAC[option_CASE]);;

let subg_insert_each' = prove
 (`!gb (fns1:(num # B) list) (es:A list) g1.
     subg gb (FST (new_g:C spt # (num # num # A) list),
              APPEND l (SND (insert_each' g1 loc (LENGTH fns1) g))) /\
     SND new_g = APPEND l (SND g) /\ LENGTH fns1 = LENGTH es /\
     wfg g /\
     DISJOINT (set_of_list (list_of_seq (\i. 2 * i + loc + 1) (LENGTH fns1)))
              (IMAGE SUC (domain (FST g))) /\
     DISJOINT (set_of_list (MAP FST l)) (IMAGE SUC (domain (FST g))) /\
     (!i. i < LENGTH fns1
          ==> ALOOKUP g1 (2 * i + loc + 1) = SOME (FST (EL i fns1),EL i es))
     ==> subg (FST new_g, APPEND l (SND (insert_each' g1 loc (LENGTH fns1) g)))
              (clos_call_code_list loc (ZIP (MAP FST fns1) es) new_g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ZIP (list_of_seq ((+) (loc + 1) o ( * ) 2) (LENGTH (ZIP (MAP FST fns1) es)))
        (ZIP (MAP FST (fns1:(num # B) list)) (es:A list)) =
    list_of_seq (\i. (2 * i + loc + 1, THE (ALOOKUP g1 (2 * i + loc + 1))))
                (LENGTH fns1)`
   (LABEL_TAC "zipeq") THENL
   [REWRITE_TAC[LISTAUX_LENGTH_ZIP; LENGTH_MAP] THEN
    W(fun (_,w) -> MP_TAC(ISPECL [rand(lhand w); `(+) (loc + 1) o ( * ) 2`;
                                  `LENGTH (fns1:(num # B) list)`] ZIP_GENLIST1)) THEN
    REWRITE_TAC[LISTAUX_LENGTH_ZIP; LENGTH_MAP] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC GENLIST_CONG THEN REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[THE_DEF] THEN
    SUBGOAL_THEN `m < LENGTH (MAP FST (fns1:(num # B) list))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_ZIP; LENGTH_MAP; EL_MAP; o_THM; PAIR_EQ] THEN
    REWRITE_TAC[GSYM(ASSUME `LENGTH (fns1:(num # B) list) = LENGTH (es:A list)`)] THEN
    ASM_SIMP_TAC[EL_ZIP; LENGTH_MAP; EL_MAP] THEN ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `subg gb (FST (new_g:C spt # (num # num # A) list),
                        APPEND l (SND (insert_each' (g1:(num # num # A) list) loc
                                         (LENGTH (fns1:(num # B) list)) g)))` THEN
  REWRITE_TAC[subg_def; FST_code_list; SND_code_list_ZIP; SND_insert_each'; FST; SND;
              subspt_refl] THEN
  REWRITE_TAC[ASSUME `SND (new_g:C spt # (num # num # A) list) =
                       APPEND l (SND (g:num_set # (num # num # A) list))`] THEN
  USE_THEN "zipeq" (fun th -> REWRITE_TAC[th]) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSCALLPAUX_ALOOKUP_SWAP) THEN
  ASM_REWRITE_TAC[]);;

let CLOSCALLPAUX_v_rel_SUBMAP = prove
 (`!g l code v1 v2. clos_callProof_v_rel g l code v1 v2 ==>
     !code'. code SUBMAP code' ==> clos_callProof_v_rel g l code' v1 v2`,
  CLOSCALLPAUX_VREL_MONO_TAC
   (MATCH_MP_TAC CLOSCALLPAUX_recclosure_rel_SUBMAP THEN
    EXISTS_TAC `code:(num,num # clos_exp)fmap` THEN ASM_REWRITE_TAC[]));;

let wfv_subg = prove
 (`!g l code v g' l' code'.
     wfv g l code v /\ code SUBMAP code' /\ subg g g' /\ l SUBSET l'
     ==> wfv g' l' code' v`,
  MATCH_MP_TAC wfv_ind THEN REWRITE_TAC[wfv_def; GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[CLOSCALLPAUX_recclosure_rel_mono]);;

let wfv_SUBMAP = prove
 (`!g1 l1 code v code1. wfv g1 l1 code v /\ code SUBMAP code1 ==> wfv g1 l1 code1 v`,
  MATCH_MP_TAC wfv_ind THEN REWRITE_TAC[wfv_def; GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[CLOSCALLPAUX_recclosure_rel_SUBMAP]);;

let EVERY_wfv_SUBMAP = prove
 (`ALL (wfv g1 l1 code) env /\ code SUBMAP code1 ==> ALL (wfv g1 l1 code1) env`,
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[wfv_SUBMAP]);;

let EVERY_wfv_subg = prove
 (`ALL (wfv g l code) env /\ code SUBMAP code2 /\ subg g g2 /\ l SUBSET l2
   ==> ALL (wfv g2 l2 code2) env`,
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[wfv_subg]);;

let every_refv_mono = prove
 (`(!x:A. P x ==> P' x) ==> every_refv P v ==> every_refv P' v`,
  STRUCT_CASES_TAC (ISPEC `v:(A)clos_ref` (cases "clos_ref")) THEN
  REWRITE_TAC[every_refv_def; GSYM ALL_MEM] THEN MESON_TAC[]);;

let wfv_state_subg = prove
 (`wfv_state g l code (s:(A,FFI)clos_state) /\ code SUBMAP code2 /\ subg g g2 /\
   l SUBSET l2 ==> wfv_state g2 l2 code2 s`,
  REWRITE_TAC[wfv_state_def; GSYM ALL_MEM; FEVERY_ALL_FLOOKUP; o_THM; SND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[OPTION_ALL_MONO; wfv_subg];
    MATCH_MP_TAC(GEN_ALL(REWRITE_RULE[GSYM IMP_CONJ] every_refv_mono)) THEN
    EXISTS_TAC `wfv g l code` THEN ASM_MESON_TAC[wfv_subg]]);;

let wfv_state_SUBMAP = prove
 (`!g1 l1 code (s:(A,FFI)clos_state) code1.
     wfv_state g1 l1 code s /\ code SUBMAP code1 ==> wfv_state g1 l1 code1 s`,
  REWRITE_TAC[wfv_state_def; GSYM ALL_MEM; FEVERY_ALL_FLOOKUP; o_THM; SND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[OPTION_ALL_MONO; wfv_SUBMAP];
    MATCH_MP_TAC(GEN_ALL(REWRITE_RULE[GSYM IMP_CONJ] every_refv_mono)) THEN
    EXISTS_TAC `wfv g1 l1 code` THEN ASM_MESON_TAC[wfv_SUBMAP]]);;

let v_rel_SUBMAP = prove
 (`!g1 l1 code v1 v2 code1.
     clos_callProof_v_rel g1 l1 code v1 v2 /\ code SUBMAP code1 ==>
     clos_callProof_v_rel g1 l1 code1 v1 v2`,
  MESON_TAC[CLOSCALLPAUX_v_rel_SUBMAP]);;

let v_rel_SUBMAP_subg = prove
 (`clos_callProof_v_rel g l code v1 v2 /\ code SUBMAP code' /\ l SUBSET l' /\ subg g g'
   ==> clos_callProof_v_rel g' l' code' v1 v2`,
  MESON_TAC[v_rel_SUBMAP; v_rel_subg]);;

let LIST_REL_v_rel_SUBMAP = prove
 (`!g1 l1 code v1 v2 code1.
     ALL2 (clos_callProof_v_rel g1 l1 code) v1 v2 /\ code SUBMAP code1 ==>
     ALL2 (clos_callProof_v_rel g1 l1 code1) v1 v2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSCALLPAUX_ALL2_MEM_MONO THEN
  EXISTS_TAC `clos_callProof_v_rel g1 l1 code` THEN ASM_MESON_TAC[v_rel_SUBMAP]);;

let LIST_REL_v_rel_subg = prove
 (`ALL2 (clos_callProof_v_rel g l code) xs ys /\ subg g g2 /\ l SUBSET l2 /\
   code SUBMAP code2 ==> ALL2 (clos_callProof_v_rel g2 l2 code2) xs ys`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSCALLPAUX_ALL2_MEM_MONO THEN
  EXISTS_TAC `clos_callProof_v_rel g l code` THEN ASM_MESON_TAC[v_rel_SUBMAP_subg]);;

let env_rel_SUBMAP = prove
 (`!code code' g1 l1 env1 env2 n vars.
     clos_callProof_env_rel (clos_callProof_v_rel g1 l1 code) env1 env2 n vars /\
     code SUBMAP code' ==>
     clos_callProof_env_rel (clos_callProof_v_rel g1 l1 code') env1 env2 n vars`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
    fst(dest_const t) = "clos_callProof_env_rel")) (concl th))) THEN
  MATCH_MP_TAC clos_callProof_env_rel_mono THEN ASM_MESON_TAC[v_rel_SUBMAP]);;

let env_rel_subg = prove
 (`clos_callProof_env_rel (clos_callProof_v_rel g l code) env1 env2 n vars /\
   subg g g2 /\ l SUBSET l2 /\ code SUBMAP code2 ==>
   clos_callProof_env_rel (clos_callProof_v_rel g2 l2 code2) env1 env2 n vars`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
    fst(dest_const t) = "clos_callProof_env_rel")) (concl th))) THEN
  MATCH_MP_TAC clos_callProof_env_rel_mono THEN ASM_MESON_TAC[v_rel_SUBMAP_subg]);;

(* semantic functions respect relation *)

let clos_callProof_v_rel_Unit = prove
 (`clos_callProof_v_rel g1 l1 code clos_Unit clos_Unit`,
  REWRITE_TAC[clos_Unit_def; clos_callProof_v_rel_def] THEN MESON_TAC[ALL2]);;
let _ = cake_add_simps [clos_callProof_v_rel_Unit];;

let v_to_list_thm = prove
 (`!h h' x. clos_v_to_list h = SOME x /\ clos_callProof_v_rel g1 l1 code h h' ==>
           ?x'. clos_v_to_list h' = SOME x' /\ ALL2 (clos_callProof_v_rel g1 l1 code) x x'`,
  MATCH_MP_TAC clos_v_to_list_ind THEN RW[] THEN FS[clos_v_to_list_def] THEN RW[] THEN
  FS[clos_callProof_v_rel_def; clos_v_to_list_def] THEN RW[] THEN
  EVERY_CASE_TAC THEN FS[] THEN RW[] THEN FS[] THEN RES_TAC THEN FS[] THEN RW[]);;

(* HOL4 [local] *)
let clos_callProof_v_rel_IMP_v_to_bytes_lemma = prove
 (`!x y c g code. clos_callProof_v_rel c g code x y ==>
     !ns:byte list.
       (clos_v_to_list x = SOME (MAP (clos_Number o int_of_num o val) ns) <=>
        clos_v_to_list y = SOME (MAP (clos_Number o int_of_num o val) ns))`,
  MATCH_MP_TAC clos_v_to_list_ind THEN RW[] THEN
  FS[clos_v_to_list_def; clos_callProof_v_rel_def] THEN
  CASES_ON `tag = cons_tag` THEN FS[] THEN RES_TAC THEN FS(all_case_eqs()) THEN
  CASES_ON `ns:byte list` THEN FS[] THEN EQ_TAC THEN RW[] THEN FS[] THEN
  TRY (FS[clos_callProof_v_rel_def] THEN NO_TAC) THEN
  CASES_ON `h:clos_v` THEN FS[clos_callProof_v_rel_def]);;

(* HOL4 [local] *)
let clos_callProof_v_rel_IMP_v_to_words_lemma = prove
 (`!x y c g code. clos_callProof_v_rel c g code x y ==>
     !ns:int64 list.
       (clos_v_to_list x = SOME (MAP clos_Word64 ns) <=>
        clos_v_to_list y = SOME (MAP clos_Word64 ns))`,
  MATCH_MP_TAC clos_v_to_list_ind THEN RW[] THEN
  FS[clos_v_to_list_def; clos_callProof_v_rel_def] THEN
  CASES_ON `tag = cons_tag` THEN FS[] THEN RES_TAC THEN FS(all_case_eqs()) THEN
  CASES_ON `ns:int64 list` THEN FS[] THEN EQ_TAC THEN RW[] THEN FS[] THEN
  TRY (FS[clos_callProof_v_rel_def] THEN NO_TAC) THEN
  CASES_ON `h:clos_v` THEN FS[clos_callProof_v_rel_def]);;

let v_to_bytes_thm = prove
 (`!h h' x. clos_v_to_bytes h = SOME x /\ clos_callProof_v_rel g1 l1 code h h' ==>
            clos_v_to_bytes h' = SOME x`,
  REWRITE_TAC[clos_v_to_bytes_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE
    [MATCH_MP clos_callProof_v_rel_IMP_v_to_bytes_lemma th])) THEN
  ASM_REWRITE_TAC[]);;

let v_to_words_thm = prove
 (`!h h' x. clos_v_to_words h = SOME x /\ clos_callProof_v_rel g1 l1 code h h' ==>
            clos_v_to_words h' = SOME x`,
  REWRITE_TAC[clos_v_to_words_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE
    [MATCH_MP clos_callProof_v_rel_IMP_v_to_words_lemma th])) THEN
  ASM_REWRITE_TAC[]);;

let v_to_list_wfv = prove
 (`!h x. clos_v_to_list h = SOME x /\ wfv g1 l1 code h ==> ALL (wfv g1 l1 code) x`,
  MATCH_MP_TAC clos_v_to_list_ind THEN RW[] THEN FS[clos_v_to_list_def] THEN RW[] THEN
  EVERY_CASE_TAC THEN FS[] THEN RW[] THEN FS[] THEN RES_TAC THEN FS[] THEN RW[]);;

let wfv_Boolv = prove
 (`wfv g1 l1 code (clos_Boolv b) /\ wfv g1 l1 code clos_Unit`,
  CASES_ON `b:bool` THEN REWRITE_TAC[clos_Boolv_def; clos_Unit_def; wfv_def; ALL]);;

let vrel_list_to_v = prove
 (`!xs1 xs2 ys1 ys2.
     ALL2 (clos_callProof_v_rel g l code) xs1 xs2 /\
     ALL2 (clos_callProof_v_rel g l code) ys1 ys2 /\
     clos_callProof_v_rel g l code (clos_list_to_v xs1) (clos_list_to_v xs2) /\
     clos_callProof_v_rel g l code (clos_list_to_v ys1) (clos_list_to_v ys2) ==>
     clos_callProof_v_rel g l code (clos_list_to_v (APPEND xs1 ys1))
                                   (clos_list_to_v (APPEND xs2 ys2))`,
  LIST_INDUCT_TAC THENL [RW[clos_list_to_v_def; APPEND; LIST_REL_NIL]; ALL_TAC] THEN
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `xs2:clos_v list` list_CASES) THEN
  RW[clos_list_to_v_def; APPEND; ALL2] THEN FS[clos_callProof_v_rel_def; ALL2] THEN
  ASM_MESON_TAC[]);;

let vrel_v2l_l2v = prove
 (`!x y xs ys. clos_callProof_v_rel g l code x y /\ clos_v_to_list x = SOME xs /\
               clos_v_to_list y = SOME ys ==>
               clos_callProof_v_rel g l code (clos_list_to_v xs) (clos_list_to_v ys)`,
  MATCH_MP_TAC clos_v_to_list_ind THEN RW[clos_v_to_list_def; clos_callProof_v_rel_def] THEN
  FS[clos_list_to_v_def] THEN RVEQ_TAC THEN FS[clos_v_to_list_def] THEN RVEQ_TAC THEN
  FS(clos_list_to_v_def :: clos_callProof_v_rel_def :: all_case_eqs()) THEN RVEQ_TAC THEN
  FS[clos_list_to_v_def; clos_callProof_v_rel_def] THEN RES_TAC THEN ASM_REWRITE_TAC[]);;
let wfv_v2l_l2v = prove
 (`!x (y:A) xs (ys:B). wfv g l code x /\ clos_v_to_list x = SOME xs ==>
                       wfv g l code (clos_list_to_v xs)`,
  MATCH_MP_TAC clos_v_to_list_ind THEN RW[clos_v_to_list_def; wfv_def] THEN
  FS(clos_list_to_v_def :: all_case_eqs()) THEN RW[clos_list_to_v_def; wfv_def; ALL] THEN
  RES_TAC THEN ASM_REWRITE_TAC[]);;

let wfv_v2l = prove
 (`!x y xs ys.
     wfv g l code x /\ wfv g l code y /\
     clos_v_to_list x = SOME xs /\ clos_v_to_list y = SOME ys ==>
     ?z. wfv g l code z /\ clos_v_to_list z = SOME (APPEND xs ys)`,
  MATCH_MP_TAC clos_v_to_list_ind THEN RW[clos_v_to_list_def] THEN FS[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FS(all_case_eqs()) THEN RVEQ_TAC THEN
  FIRST_ASSUM(fun th -> let c = concl th in
    if is_eq c && lhs c = `clos_v_to_list bt` then
      let t = rand(rhs c) in
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:clos_v`; t; `ys:clos_v list`] o
                    check (is_forall o concl))
    else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:clos_v` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `clos_Block cons_tag [h; z]` THEN
  ASM_REWRITE_TAC[wfv_def; ALL; clos_v_to_list_def] THEN CASE_REWRITE_TAC[APPEND]);;

(* local helpers for do_app_thm *)

let CLOSCALLPAUX_ALL2_EQ_ALL = prove
 (`!(P:A->bool) xs ys. ALL2 (\v1 v2. P v1 /\ v1 = v2) xs ys <=> xs = ys /\ ALL P xs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; ALL; NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]);;

let CLOSCALLPAUX_ALL2_OPTREL_EQ = prove
 (`!(P:A->bool) xs ys.
     ALL2 (OPTREL (\v1 v2. P v1 /\ v1 = v2)) xs ys <=> xs = ys /\ ALL (OPTION_ALL P) xs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; ALL; NOT_CONS_NIL; CONS_11] THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC(ISPEC t option_nchotomy))
    [`h:A option`; `h':A option`] THEN
  REWRITE_TAC[OPTREL_def; OPTION_ALL_def; option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

let CLOSCALLPAUX_simple_val_rel_v_rel = prove
 (`!g l code. clos_simple_val_rel (clos_callProof_v_rel g l code)`,
  REWRITE_TAC[clos_simple_val_rel_def] THEN REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN CASES_ON `x:clos_v` THEN
  REWRITE_TAC[clos_callProof_v_rel_def; injectivity "clos_v"; distinctness "clos_v";
              clos_isClos_def] THEN
  MESON_TAC[]);;

let CLOSCALLPAUX_ref_rel_cases = prove
 (`!(R:A->B->bool) x.
     (!w. clos_ref_rel R x (clos_ByteArray w) <=> x = clos_ByteArray w) /\
     (!w. clos_ref_rel R x (clos_ValueArray w) <=>
          ?w1. x = clos_ValueArray w1 /\ ALL2 R w1 w) /\
     (!m v. clos_ref_rel R x (clos_Thunk m v) <=> ?w. x = clos_Thunk m w /\ R w v)`,
  REPEAT GEN_TAC THEN CASES_ON `x:A clos_ref` THEN
  REWRITE_TAC[clos_ref_rel_def; injectivity "clos_ref"; distinctness "clos_ref"] THEN
  MESON_TAC[]);;

let CLOSCALLPAUX_simple_state_rel_state_rel = prove
 (`!g l code.
     clos_simple_state_rel (clos_callProof_v_rel g l code)
       (\(s:(abs_calls_state # C,FFI)clos_state) (u:(C,FFI)clos_state).
          clos_callProof_state_rel g l s u /\ clos_state_code u = code)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_simple_state_rel_def; clos_callProof_state_rel_def] THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[] THEN
  TRY (MATCH_MP_TAC fmap_rel_FUPDATE_same THEN
       ASM_REWRITE_TAC[clos_ref_rel_def] THEN NO_TAC) THEN
  TRY (RULE_ASSUM_TAC(REWRITE_RULE[fmap_rel_def]) THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[fmap_rel_OPTREL_FLOOKUP]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ptr:num` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[OPTREL_SOME; OPTREL_NONE; CLOSCALLPAUX_ref_rel_cases] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let CLOSCALLPAUX_simple_val_rel_wfv = prove
 (`!g l code. clos_simple_val_rel (\v1 v2. wfv g l code v1 /\ v1 = v2)`,
  REWRITE_TAC[clos_simple_val_rel_def; CLOSCALLPAUX_ALL2_EQ_ALL; ETA_AX] THEN
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[wfv_def; clos_isClos_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wfv_def]) THEN ASM_MESON_TAC[wfv_def]);;

let CLOSCALLPAUX_FEVERY_refv = prove
 (`!(P:clos_v->bool) refs ptr r.
     FEVERY (every_refv P o SND) (refs:(num,clos_v clos_ref)fmap) /\
     FLOOKUP refs ptr = SOME r ==> every_refv P r`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP FEVERY_FLOOKUP o CONJ
    (ASSUME `FEVERY (every_refv (P:clos_v->bool) o SND) (refs:(num,clos_v clos_ref)fmap)`)) THEN
  REWRITE_TAC[o_THM]);;

let CLOSCALLPAUX_simple_state_rel_wfv = prove
 (`!g l code.
     clos_simple_state_rel (\v1 v2. wfv g l code v1 /\ v1 = v2)
       (\(s1:(abs_calls_state # C,FFI)clos_state) s2. wfv_state g l code s1 /\ s1 = s2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_simple_state_rel_def; wfv_state_def; CLOSCALLPAUX_ALL2_EQ_ALL;
              CLOSCALLPAUX_ALL2_OPTREL_EQ; ETA_AX] THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY (MATCH_MP_TAC(CONJUNCT2(SPEC_ALL FEVERY_STRENGTHEN_THM)) THEN
       ASM_REWRITE_TAC[o_THM; every_refv_def] THEN NO_TAC) THEN
  IMP_RES_TAC CLOSCALLPAUX_FEVERY_refv THEN
  RULE_ASSUM_TAC(REWRITE_RULE[every_refv_def]) THEN ASM_MESON_TAC[]);;
let CLOSCALLPAUX_do_app_result_cases = prove
 (`!x:(clos_v # (abs_calls_state # C,FFI)clos_state,clos_v)result.
       (?w s. x = Rval (w,s)) \/ (?v. x = Rerr (Rraise v)) \/
       x = Rerr (Rabort Rtype_error) \/ x = Rerr (Rabort Rtimeout_error) \/
       (?f. x = Rerr (Rabort (Rffi_error f)))`,
  GEN_TAC THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `p:clos_v # (abs_calls_state # C,FFI)clos_state` SUBST1_TAC)
                   (X_CHOOSE_THEN `e:clos_v error_result` SUBST1_TAC)
    (ISPEC `x:(clos_v # (abs_calls_state # C,FFI)clos_state,clos_v)result`
           (cases "result")) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"] THENL
   [MATCH_ACCEPT_TAC PAIR_SURJECTIVE;
    DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:clos_v` SUBST1_TAC)
                     (X_CHOOSE_THEN `ab:abort` SUBST1_TAC)
      (ISPEC `e:clos_v error_result` (cases "error_result")) THEN
    REWRITE_TAC[injectivity "error_result"; distinctness "error_result"] THENL
     [MESON_TAC[];
      STRUCT_CASES_TAC(ISPEC `ab:abort` (cases "abort")) THEN
      REWRITE_TAC[injectivity "abort"; distinctness "abort"] THEN MESON_TAC[]]]);;

let clos_callProof_do_app_thm = prove
 (CASE_TERM
  `match clos_do_app op (REVERSE a) (r:(abs_calls_state # C,FFI)clos_state) with
     Rerr (Rraise _) -> F
   | Rerr (Rabort e) ->
       (e = Rtype_error \/
        (?f. e = Rffi_error f /\
             (ALL2 (clos_callProof_v_rel g2 l2 (clos_state_code (t:(C,FFI)clos_state))) a v /\
              clos_callProof_state_rel g2 l2 r t
              ==> clos_do_app op (REVERSE v) t = Rerr (Rabort (Rffi_error f)))))
   | Rval (w,s) ->
       (wfv_state g2 l2 (clos_state_code t) r /\ ALL (wfv g2 l2 (clos_state_code t)) a
        ==> wfv_state g2 l2 (clos_state_code t) s /\ wfv g2 l2 (clos_state_code t) w) /\
       (ALL2 (clos_callProof_v_rel g2 l2 (clos_state_code t)) a v /\
        clos_callProof_state_rel g2 l2 r t
        ==> ?w' s'. clos_do_app op (REVERSE v) t = Rval (w',s') /\
                    clos_callProof_v_rel g2 l2 (clos_state_code t) w w' /\
                    clos_callProof_state_rel g2 l2 s s')`,
  MP_TAC(ISPECL [`clos_callProof_v_rel g2 l2 (clos_state_code (t:(C,FFI)clos_state))`;
                 `\(s:(abs_calls_state # C,FFI)clos_state) (u:(C,FFI)clos_state).
                     clos_callProof_state_rel g2 l2 s u /\
                     clos_state_code u = clos_state_code (t:(C,FFI)clos_state)`;
                 `r:(abs_calls_state # C,FFI)clos_state`; `t:(C,FFI)clos_state`;
                 `REVERSE (a:clos_v list)`; `REVERSE (v:clos_v list)`; `op:clos_op`]
                simple_val_rel_do_app) THEN
  REWRITE_TAC[CLOSCALLPAUX_simple_val_rel_v_rel; CLOSCALLPAUX_simple_state_rel_state_rel] THEN
  MP_TAC(ISPECL [`\v1 v2. wfv g2 l2 (clos_state_code (t:(C,FFI)clos_state)) v1 /\ v1 = v2`;
                 `\(s1:(abs_calls_state # C,FFI)clos_state) s2.
                     wfv_state g2 l2 (clos_state_code (t:(C,FFI)clos_state)) s1 /\ s1 = s2`;
                 `r:(abs_calls_state # C,FFI)clos_state`; `r:(abs_calls_state # C,FFI)clos_state`;
                 `REVERSE (a:clos_v list)`; `REVERSE (a:clos_v list)`; `op:clos_op`]
                simple_val_rel_do_app) THEN
  REWRITE_TAC[CLOSCALLPAUX_simple_val_rel_wfv; CLOSCALLPAUX_simple_state_rel_wfv] THEN
  REWRITE_TAC[BETA_THM; CLOSCALLPAUX_ALL2_EQ_ALL; EVERY_REVERSE; LIST_REL_REVERSE_EQ] THEN
  MP_TAC(ISPECL [`op:clos_op`; `REVERSE (a:clos_v list)`;
                 `r:(abs_calls_state # C,FFI)clos_state`] CLOSPROPSAUX_do_app_not_Rraise) THEN
  MP_TAC(ISPECL [`op:clos_op`; `REVERSE (a:clos_v list)`;
                 `r:(abs_calls_state # C,FFI)clos_state`] do_app_never_timesout) THEN
  REWRITE_TAC[ETA_AX] THEN
  MP_TAC(ISPEC `clos_do_app op (REVERSE (a:clos_v list)) (r:(abs_calls_state # C,FFI)clos_state)`
           CLOSCALLPAUX_do_app_result_cases) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; injectivity "error_result";
              distinctness "error_result"; injectivity "abort"; distinctness "abort"] THENL
   [MESON_TAC[];
    MESON_TAC[];
    REWRITE_TAC[exc_rel_type_error1; UNWIND_THM1; RIGHT_EXISTS_AND_THM; EXISTS_REFL] THEN
    MESON_TAC[]]);;

let NOT_IN_domain_FST_g = prove
 (`ALL_DISTINCT (APPEND (code_locs xs) (code_locs ys)) ==>
   clos_call_calls ys g' = (e2,g) ==>
   wfg (g':num_set # (num # num # clos_exp) list) ==>
   MEM x (code_locs xs) ==>
   ~(x IN domain (FST g')) ==>
   ~(x IN domain (FST g))`,
  REPEAT DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP calls_domain_locs) THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_SET_OF_LIST] THEN
  DISCH_THEN(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ALL_DISTINCT (APPEND (code_locs xs) (code_locs ys))` THEN
  REWRITE_TAC[ALL_DISTINCT_APPEND] THEN ASM_MESON_TAC[]);;

let clos_callProof_v_rel_Boolv = prove
 (`clos_callProof_v_rel g1 l1 code (clos_Boolv b) v <=> v = clos_Boolv b`,
  REWRITE_TAC[clos_Boolv_def; clos_callProof_v_rel_def; LIST_REL_NIL] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [clos_callProof_v_rel_Boolv];;

(* HOL4 [local] *)
let env_rel_Op_Install = prove
 (`clos_callProof_env_rel (r:A->B->bool) env env2 0 [(0,clos_Op v6 clos_Install e1)] <=>
   clos_callProof_env_rel r env env2 0 (MAP (\x. (0,x)) e1)`,
  REWRITE_TAC[clos_callProof_env_rel_def] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[EX; EX_MAP; o_DEF] THEN CASE_REWRITE_TAC[fv1_thm; ADD_CLAUSES] THEN
  REWRITE_TAC[fv_exists; ETA_AX]);;

let clos_callProof_syntax_ok_def = cake_def
  `clos_callProof_syntax_ok x <=>
     every_Fn_SOME x /\ every_Fn_vs_NONE x /\ ALL_DISTINCT (code_locs x)`;;

let co_ok_def = cake_def_wf
  `MEASURE (\x:(num,num # clos_exp)fmap #
              (num -> (num_set # C) # clos_exp list # A) #
              (num -> num_set # (num # num # clos_exp) list) # num.
              SND (SND (SND x)))`
  TERM_TAC
  `co_ok (code:(num,num # clos_exp)fmap) (co:num -> (num_set # C) # clos_exp list # A)
        (full_gs:num -> num_set # (num # num # clos_exp) list) k <=>
     if k = 0 then T else
       let g = FST (FST (co 0)) in
       let (cfg,exp,aux) = co 0 in
       let (g',exp',aux1) = clos_call_compile_inc g (exp,aux) in
         FST (FST (co 1)) = g' /\
         make_g g code = SOME (full_gs 0) /\
         (!i. subg (full_gs 0) (full_gs i)) /\
         (!x i. MEM x (code_locs exp) /\ ~(x IN domain g') ==>
                ~(x IN domain (FST (FST (co i))))) /\
         DISJOINT (set_of_list (code_locs exp)) (domain g) /\
         DISJOINT (FDOM code) (set_of_list (MAP FST aux1)) /\
         ALL_DISTINCT (MAP FST aux1) /\
         co_ok (code |++ aux1) (shift_seq 1 co) (shift_seq 1 full_gs) (k - 1)`;;

let CLOSCALLPAUX_make_g_FST = prove
 (`make_g (d:A spt) (code:(num,B)fmap) = SOME g ==> FST g = d`,
  REWRITE_TAC[make_g_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[FST]);;

(* unfolding co_ok at a successor *)
let CLOSCALLPAUX_co_ok_SUC = prove
 (`!code (co:num -> (num_set # C) # clos_exp list # A) full_gs k.
     co_ok code co full_gs (k + 1) ==>
     make_g (FST (FST (co 0))) code = SOME (full_gs 0) /\
     ?aux1. co_ok (code |++ aux1) (shift_seq 1 co) (shift_seq 1 full_gs) k`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [co_ok_def] THEN
  REWRITE_TAC[ARITH_RULE `~(k + 1 = 0)`; ADD_SUB; LET_DEF; LET_END_DEF] THEN
  REPEAT IL1AUX_PAIRARG_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN MESON_TAC[]);;

let co_ok_IMP_full_gs_eq_shift_seq = prove
 (`!k code (co:num -> (num_set # C) # clos_exp list # A) (g:D) full_gs.
     co_ok code co full_gs (k + 1)
     ==> FST (FST (shift_seq k co 0)) = FST (full_gs k)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP CLOSCALLPAUX_co_ok_SUC) THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSCALLPAUX_make_g_FST) THEN
    REWRITE_TAC[shift_seq_def; ADD_CLAUSES] THEN MESON_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[ADD1]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`code |++ (aux1:(num # num # clos_exp) list)`;
       `shift_seq 1 (co:num -> (num_set # C) # clos_exp list # A)`;
       `shift_seq 1 (full_gs:num -> num_set # (num # num # clos_exp) list)`]) THEN
    ASM_REWRITE_TAC[ADD1] THEN REWRITE_TAC[shift_seq_def; BETA_THM; ADD_CLAUSES; ADD_AC]]);;

let co_ok_IMP_wfg_full_gs = prove
 (`!k code (co:num -> (num_set # C) # clos_exp list # A) (g:D) full_gs.
     co_ok code co full_gs (k + 1) ==> wfg (full_gs k)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP CLOSCALLPAUX_co_ok_SUC) THENL
   [ASM_MESON_TAC[make_g_wfg];
    RULE_ASSUM_TAC(REWRITE_RULE[ADD1]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`code |++ (aux1:(num # num # clos_exp) list)`;
       `shift_seq 1 (co:num -> (num_set # C) # clos_exp list # A)`;
       `shift_seq 1 (full_gs:num -> num_set # (num # num # clos_exp) list)`]) THEN
    ASM_REWRITE_TAC[ADD1] THEN REWRITE_TAC[shift_seq_def; BETA_THM; ADD_CLAUSES; ADD_AC]]);;

let co_ok_IMP_make_g = prove
 (`!k code (co:num -> (num_set # C) # clos_exp list # A) (g:D) full_gs.
     co_ok code co full_gs (k + 1) ==>
     ?x1 (x2:(num,num # clos_exp)fmap). make_g x1 x2 = SOME (full_gs k)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP CLOSCALLPAUX_co_ok_SUC) THENL
   [ASM_MESON_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[ADD1]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`code |++ (aux1:(num # num # clos_exp) list)`;
       `shift_seq 1 (co:num -> (num_set # C) # clos_exp list # A)`;
       `shift_seq 1 (full_gs:num -> num_set # (num # num # clos_exp) list)`]) THEN
    ASM_REWRITE_TAC[ADD1] THEN REWRITE_TAC[shift_seq_def; BETA_THM; ADD_CLAUSES; ADD_AC]]);;

let code_inv_def = cake_def
  `code_inv (g1_opt:(num_set # (num # num # clos_exp) list)option) (l1:num->bool)
     (s_code:(num,num # clos_exp)fmap)
     (s_cc:(num_set # C) -> clos_exp list # (num # num # clos_exp) list ->
           (D # E # (num_set # C))option)
     (s_co:num -> (num_set # C) # clos_exp list # (num # num # clos_exp) list)
     (t_code:(num,num # clos_exp)fmap)
     (t_cc:C -> clos_exp list # (num # num # clos_exp) list -> (D # E # C)option)
     (t_co:num -> C # clos_exp list # (num # num # clos_exp) list) <=>
     s_code = FEMPTY /\
     s_cc = state_cc clos_call_compile_inc t_cc /\
     t_co = state_co clos_call_compile_inc s_co /\
     (?g aux. wfg (g,aux) /\
        FST (FST (s_co 0)) = g /\
        oracle_monotonic (set_of_list o code_locs o FST o SND) (<) (domain g UNION l1) s_co /\
        t_code = alist_to_fmap aux /\
        (IS_SOME g1_opt ==> g1_opt = SOME (g,aux))) /\
     (!k. let (cfg,exp,aux) = s_co k in clos_callProof_syntax_ok exp /\ aux = [])`;;

let code_inv_k = prove
 (CASE_TERM
  `!k. code_inv g l s_code
         (s_cc:(num_set # C) -> clos_exp list # (num # num # clos_exp) list ->
               (D # E # (num_set # C))option)
         s_co t_code t_cc t_co ==>
       match s_co k with (cfg,exp,aux) -> clos_callProof_syntax_ok exp /\ aux = []`,
  REWRITE_TAC[code_inv_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (is_forall o concl)) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[]);;

let SUBMAP_FUPDATE_LIST = prove
 (`!(f:(A,B)fmap) xs.
     ALL_DISTINCT (MAP FST xs) /\ DISJOINT (FDOM f) (set_of_list (MAP FST xs))
     ==> f SUBMAP (f |++ xs)`,
  REWRITE_TAC[SUBMAP_DEF; FDOM_FUPDATE_LIST; IN_UNION; IN_DISJOINT; IN_SET_OF_LIST] THEN
  MESON_TAC[FUPDATE_LIST_APPLY_NOT_MEM]);;

let includes_state_def = cake_def
  `includes_state (g1:A # B) (s_compile_oracle:num -> (A # C) # D) <=>
     ?k:num. FST (FST (s_compile_oracle k)) = FST g1`;;

let includes_state_EX = prove
 (`includes_state (g1:A # B) (s_co:num -> (A # C) # D # E) ==>
   ?k cfg2 exps aux. s_co k = ((FST g1,cfg2),exps,aux)`,
  REWRITE_TAC[includes_state_def] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `SND (FST ((s_co:num -> (A # C) # D # E) k))`;
                        `FST (SND ((s_co:num -> (A # C) # D # E) k))`;
                        `SND (SND ((s_co:num -> (A # C) # D # E) k))`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[PAIR]);;

let CLOSCALLPAUX_head_is (name:string) (th:thm) =
  try fst(dest_const(fst(strip_comb(concl th)))) = name with Failure _ -> false;;

let CLOSCALLPAUX_ref_rel_mono = prove
 (`!(R:A->B->bool) R' a b.
     (!x y. R x y ==> R' x y) ==> clos_ref_rel R a b ==> clos_ref_rel R' a b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `a:A clos_ref` THEN CASES_ON `b:B clos_ref` THEN
  REWRITE_TAC[clos_ref_rel_def] THEN ASM_MESON_TAC[MONO_ALL2]);;

let code_rel_state_rel_install = prove
 (`code_inv (SOME g1) l1 (clos_state_code r) (clos_state_compile r)
     (clos_state_compile_oracle r) (clos_state_code t) (clos_state_compile t)
     (clos_state_compile_oracle t) /\
   clos_callProof_state_rel g1 l1 (r:(abs_calls_state # C,FFI)clos_state)
     (t:(C,FFI)clos_state) /\
   clos_state_compile r cfg (exps,aux) = SOME (bytes,data,next_cfg) /\
   clos_state_compile_oracle r 0 = (cfg,exps,aux) /\
   clos_state_compile_oracle t 0 = (cfg',progs) /\
   next_cfg = FST (shift_seq 1 (clos_state_compile_oracle r) 0) /\
   DISJOINT l1 (domain (FST g1))
   ==> DISJOINT (FDOM (clos_state_code t)) (set_of_list (MAP FST (SND progs))) /\
       ALL_DISTINCT (MAP FST (SND progs)) /\
       ?exp1 aux1 g2 l2 next_cfg'.
         clos_state_compile t cfg' progs = SOME (bytes,data,next_cfg') /\
         progs = (exp1,aux1) /\
         next_cfg' = FST (shift_seq 1 (clos_state_compile_oracle t) 0) /\
         subg g1 g2 /\ l1 SUBSET l2 /\ DISJOINT l2 (domain (FST g2)) /\
         set_of_list (code_locs exps) DIFF domain (FST g2) SUBSET l2 /\
         clos_call_calls exps g1 = (exp1,g2) /\
         clos_callProof_state_rel g2 l2
           (clos_state_code_fupd (K (clos_state_code r |++ aux))
             (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle r))) r))
           (clos_state_code_fupd (K (clos_state_code t |++ aux1))
             (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle t))) t)) /\
         code_inv (SOME g2) l2 (clos_state_code r |++ aux) (clos_state_compile r)
           (shift_seq 1 (clos_state_compile_oracle r))
           (clos_state_code t |++ aux1) (clos_state_compile t)
           (shift_seq 1 (clos_state_compile_oracle t)) /\
         clos_state_code t SUBMAP (clos_state_code t |++ aux1) /\
         DISJOINT (IMAGE SUC (set_of_list (code_locs exps))) (FDOM (clos_state_code t))`,
  (STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (CLOSCALLPAUX_head_is "code_inv")) THEN
   REWRITE_TAC[code_inv_def; option_INJ; IS_SOME_DEF] THEN STRIP_TAC) THEN
  (FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     lhs (concl th) = `g1:num_set # (num # num # clos_exp) list`)) THEN
   FIRST_ASSUM(MP_TAC o SPEC `0` o check (is_forall o concl)) THEN
   REWRITE_TAC[ASSUME `clos_state_compile_oracle (r:(abs_calls_state # C,FFI)clos_state) 0 =
                       cfg,exps,aux`] THEN
   CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th =
     `aux:(num # num # clos_exp) list = []`)) THEN
   SUBGOAL_THEN `?d (c:C). cfg = (d:num_set,c)` STRIP_ASSUME_TAC THENL
    [MESON_TAC[PAIR]; ALL_TAC] THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     lhs (concl th) = `cfg:num_set # C`)) THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
     `FST (FST (clos_state_compile_oracle (r:(abs_calls_state # C,FFI)clos_state) 0)) = g`)) THEN
   REWRITE_TAC[ASSUME `clos_state_compile_oracle (r:(abs_calls_state # C,FFI)clos_state) 0 =
                       (d,c),exps,[]`; FST] THEN
   DISCH_THEN SUBST_ALL_TAC THEN
   SUBGOAL_THEN `?ea d1 nc. clos_call_calls exps (g,[]) = (ea,d1,nc)` STRIP_ASSUME_TAC THENL
    [MESON_TAC[PAIR]; ALL_TAC]) THEN
  (SUBGOAL_THEN `clos_state_compile_oracle (t:(C,FFI)clos_state) 0 = (c,ea,nc)` ASSUME_TAC THENL
    [REWRITE_TAC[ASSUME `clos_state_compile_oracle (t:(C,FFI)clos_state) =
                   state_co clos_call_compile_inc
                     (clos_state_compile_oracle (r:(abs_calls_state # C,FFI)clos_state))`;
                 state_co_def] THEN
     REWRITE_TAC[ASSUME `clos_state_compile_oracle (r:(abs_calls_state # C,FFI)clos_state) 0 =
                         (g,c),exps,[]`] THEN
     CASE_REWRITE_TAC[clos_call_compile_inc_def; LET_DEF; LET_END_DEF] THEN
     REWRITE_TAC[ASSUME `clos_call_calls exps (g,[]) = ea,d1,nc`] THEN CASE_REWRITE_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
     `clos_state_compile_oracle (t:(C,FFI)clos_state) 0 = cfg',progs`)) THEN
   REWRITE_TAC[ASSUME `clos_state_compile_oracle (t:(C,FFI)clos_state) 0 = (c,ea,nc)`;
               PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM))) THEN
  (SUBGOAL_THEN `?cfg1. clos_state_compile (t:(C,FFI)clos_state) c (ea,nc) =
                        SOME (bytes,data,cfg1) /\ (next_cfg:num_set # C) = (d1,cfg1)`
     STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `clos_state_compile (r:(abs_calls_state # C,FFI)clos_state) (g,c) (exps,[]) =
                  SOME (bytes,data,next_cfg)` THEN
     REWRITE_TAC[ASSUME `clos_state_compile (r:(abs_calls_state # C,FFI)clos_state) =
                   state_cc clos_call_compile_inc (clos_state_compile (t:(C,FFI)clos_state))`;
                 state_cc_def] THEN
     CASE_REWRITE_TAC[clos_call_compile_inc_def; LET_DEF; LET_END_DEF] THEN
     REWRITE_TAC[ASSUME `clos_call_calls exps (g,[]) = ea,d1,nc`] THEN CASE_REWRITE_TAC[] THEN
     STRUCT_CASES_TAC(ISPEC `clos_state_compile (t:(C,FFI)clos_state) c (ea,nc)`
                        option_nchotomy) THEN
     CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
     SUBGOAL_THEN `?b1 d2 c2. (x:byte list # int64 list # C) = (b1,d2,c2)` STRIP_ASSUME_TAC THENL
      [MESON_TAC[PAIR]; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_INJ; PAIR_EQ] THEN MESON_TAC[];
     ALL_TAC]) THEN
  (FIRST_ASSUM(ASSUME_TAC o MATCH_MP calls_acc o check CLOSCALLPAUX_is_calls_eq) THEN
   FIRST_ASSUM(ASSUME_TAC o SPEC `aux':(num # num # clos_exp) list` o check (is_forall o concl) o
     check (fun th -> can (find_term ((=) `clos_call_calls`)) (concl th))) THEN
   SUBGOAL_THEN `DISJOINT (domain (g:num_set) UNION l1) (set_of_list (code_locs exps))` ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[oracle_monotonic_def] o
                 check (CLOSCALLPAUX_head_is "oracle_monotonic")) THEN
     DISCH_THEN(MP_TAC o SPEC `0`) THEN
     REWRITE_TAC[ASSUME `clos_state_compile_oracle (r:(abs_calls_state # C,FFI)clos_state) 0 =
                         (g,c),exps,[]`; o_THM; FST; SND; IN_DISJOINT] THEN
     MESON_TAC[LT_REFL];
     ALL_TAC] THEN
   UNDISCH_TAC `clos_callProof_syntax_ok exps` THEN REWRITE_TAC[clos_callProof_syntax_ok_def] THEN
   STRIP_TAC THEN
   UNDISCH_TAC `wfg (g:num_set,aux':(num # num # clos_exp) list)` THEN
   REWRITE_TAC[wfg_def; FST; SND] THEN STRIP_TAC) THEN
  (SUBGOAL_THEN `set_of_list (MAP FST (nc:(num # num # clos_exp) list)) SUBSET
                 IMAGE SUC (set_of_list (code_locs exps))` ASSUME_TAC THENL
    [MP_TAC(ISPECL [`exps:clos_exp list`; `(g:num_set,[]:(num # num # clos_exp) list)`;
                    `ea:clos_exp list`; `(d1:num_set,nc:(num # num # clos_exp) list)`]
                   calls_add_SUC_code_locs) THEN
     ASM_REWRITE_TAC[SND; MAP; set_of_list; UNION_EMPTY];
     ALL_TAC] THEN
   SUBGOAL_THEN `DISJOINT (IMAGE SUC (set_of_list (code_locs exps))) (IMAGE SUC (domain (g:num_set)))`
     ASSUME_TAC THENL
    [MATCH_MP_TAC CLOSCALLPAUX_DISJOINT_IMAGE_SUC THEN ASM SET_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `ALL_DISTINCT (MAP FST (nc:(num # num # clos_exp) list))` ASSUME_TAC THENL
    [MP_TAC(ISPECL [`exps:clos_exp list`; `(g:num_set,[]:(num # num # clos_exp) list)`;
                    `ea:clos_exp list`; `(d1:num_set,nc:(num # num # clos_exp) list)`]
                   calls_ALL_DISTINCT) THEN
     ASM_REWRITE_TAC[SND; MAP; ALL_DISTINCT; set_of_list; DISJOINT_EMPTY];
     ALL_TAC] THEN
   SUBGOAL_THEN `subg (g:num_set,aux':(num # num # clos_exp) list) (d1,APPEND nc aux')`
     ASSUME_TAC THENL
    [MATCH_MP_TAC calls_subg THEN
     MAP_EVERY EXISTS_TAC [`exps:clos_exp list`; `ea:clos_exp list`] THEN
     ASM_REWRITE_TAC[SND];
     ALL_TAC] THEN
   SUBGOAL_THEN `wfg (d1:num_set,APPEND nc (aux':(num # num # clos_exp) list))` ASSUME_TAC THENL
    [MATCH_MP_TAC calls_wfg THEN
     MAP_EVERY EXISTS_TAC [`exps:clos_exp list`; `(g:num_set,aux':(num # num # clos_exp) list)`;
                           `ea:clos_exp list`] THEN
     ASM_REWRITE_TAC[SND; wfg_def; FST];
     ALL_TAC] THEN
   SUBGOAL_THEN `domain (d1:num_set) SUBSET domain (g:num_set) UNION set_of_list (code_locs exps)`
     ASSUME_TAC THENL
    [MP_TAC(ISPECL [`exps:clos_exp list`; `(g:num_set,[]:(num # num # clos_exp) list)`;
                    `ea:clos_exp list`; `(d1:num_set,nc:(num # num # clos_exp) list)`]
                   calls_domain_locs) THEN
     ASM_REWRITE_TAC[FST];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `FDOM (clos_state_code (t:(C,FFI)clos_state)) = IMAGE SUC (domain (g:num_set))`
     ASSUME_TAC THENL
    [ASM_REWRITE_TAC[FDOM_alist_to_fmap]; ALL_TAC] THEN
   SUBGOAL_THEN `DISJOINT (FDOM (clos_state_code (t:(C,FFI)clos_state)))
                          (set_of_list (MAP FST (nc:(num # num # clos_exp) list)))`
     ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     MAP_EVERY (fun t -> MP_TAC (ASSUME t))
      [`set_of_list (MAP FST (nc:(num # num # clos_exp) list)) SUBSET
        IMAGE SUC (set_of_list (code_locs exps))`;
       `DISJOINT (IMAGE SUC (set_of_list (code_locs exps))) (IMAGE SUC (domain (g:num_set)))`] THEN
     SET_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `clos_state_code (t:(C,FFI)clos_state) SUBMAP clos_state_code t |++ nc`
     ASSUME_TAC THENL
    [MATCH_MP_TAC SUBMAP_FUPDATE_LIST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[]) THEN
  (SUBGOAL_THEN `?pr. clos_state_compile_oracle (r:(abs_calls_state # C,FFI)clos_state) 1 =
                      ((d1,cfg1),pr)` STRIP_ASSUME_TAC THENL
    [EXISTS_TAC `SND (clos_state_compile_oracle (r:(abs_calls_state # C,FFI)clos_state) 1)` THEN
     MP_TAC(ASSUME `(next_cfg:num_set # C) = FST (shift_seq 1
                       (clos_state_compile_oracle (r:(abs_calls_state # C,FFI)clos_state)) 0)`) THEN
     REWRITE_TAC[ASSUME `(next_cfg:num_set # C) = d1,cfg1`; shift_seq_def; ADD_CLAUSES] THEN
     DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PAIR];
     ALL_TAC] THEN
   SUBGOAL_THEN `shift_seq 1 (state_co clos_call_compile_inc
                   (clos_state_compile_oracle (r:(abs_calls_state # C,FFI)clos_state))) =
                 state_co clos_call_compile_inc (shift_seq 1 (clos_state_compile_oracle r))`
     ASSUME_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; shift_seq_def; state_co_def]; ALL_TAC] THEN
   SUBGOAL_THEN `FST (shift_seq 1 (state_co clos_call_compile_inc
                   (clos_state_compile_oracle (r:(abs_calls_state # C,FFI)clos_state))) 0) =
                 cfg1` ASSUME_TAC THENL
    [REWRITE_TAC[shift_seq_def; state_co_def; ADD_CLAUSES] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
     STRUCT_CASES_TAC(ISPEC `clos_call_compile_inc d1 (pr:clos_exp list # (num # num # clos_exp) list)`
                        PAIR_SURJECTIVE) THEN
     CASE_REWRITE_TAC[FST];
     ALL_TAC] THEN
   SUBGOAL_THEN `FST (FST (shift_seq 1 (clos_state_compile_oracle
                   (r:(abs_calls_state # C,FFI)clos_state)) 0)) = d1` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[shift_seq_def; ADD_CLAUSES; FST]; ALL_TAC] THEN
   SUBGOAL_THEN `alist_to_fmap aux' |++ nc =
                 alist_to_fmap (APPEND nc (aux':(num # num # clos_exp) list))` ASSUME_TAC THENL
    [ASM_SIMP_TAC[FUPDATE_LIST_alist_to_fmap; ALL_DISTINCT_alist_to_fmap_REVERSE;
                  alist_to_fmap_APPEND];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
    `oracle_monotonic ((set_of_list o code_locs o FST o SND):
        (num_set # C) # clos_exp list # (num # num # clos_exp) list -> num -> bool) (<)
       (domain (d1:num_set) UNION (l1 UNION (set_of_list (code_locs exps) DIFF domain d1)))
       (shift_seq 1 (clos_state_compile_oracle (r:(abs_calls_state # C,FFI)clos_state)))`
     ASSUME_TAC THENL
    [MATCH_MP_TAC (GEN_ALL oracle_monotonic_shift_seq) THEN
     EXISTS_TAC `domain (g:num_set) UNION l1` THEN
     ASM_REWRITE_TAC[ARITH_RULE `1 > 0`; SUB_REFL; o_THM; FST; SND] THEN
     MP_TAC(ASSUME `domain (d1:num_set) SUBSET domain (g:num_set) UNION
                    set_of_list (code_locs exps)`) THEN SET_TAC[];
     ALL_TAC]) THEN
  (SUBGOAL_THEN (CASE_TERM
    `!k. match shift_seq 1 (clos_state_compile_oracle (r:(abs_calls_state # C,FFI)clos_state)) k
         with (cfg,exp,aux) ->
           (every_Fn_SOME exp /\ every_Fn_vs_NONE exp /\ ALL_DISTINCT (code_locs exp)) /\
           aux = []`)
     ASSUME_TAC THENL
    [X_GEN_TAC `k:num` THEN
     FIRST_ASSUM(MP_TAC o SPEC `k + 1` o check (fun th -> is_forall (concl th) &&
       can (find_term ((=) `clos_callProof_syntax_ok`)) (concl th))) THEN
     REWRITE_TAC[shift_seq_def; clos_callProof_syntax_ok_def];
     ALL_TAC] THEN
   SUBGOAL_THEN `DISJOINT (l1 UNION (set_of_list (code_locs exps) DIFF domain d1))
                          (domain (d1:num_set))` ASSUME_TAC THENL
    [MAP_EVERY (fun t -> MP_TAC (ASSUME t))
      [`domain (d1:num_set) SUBSET domain (g:num_set) UNION set_of_list (code_locs exps)`;
       `DISJOINT l1 (domain (FST (g:num_set,aux':(num # num # clos_exp) list)))`;
       `DISJOINT (domain (g:num_set) UNION l1) (set_of_list (code_locs exps))`] THEN
     REWRITE_TAC[FST] THEN SET_TAC[];
     ALL_TAC]) THEN
  (MAP_EVERY EXISTS_TAC [`ea:clos_exp list`; `nc:(num # num # clos_exp) list`;
     `(d1:num_set, APPEND nc (aux':(num # num # clos_exp) list))`;
     `(l1:num->bool) UNION (set_of_list (code_locs exps) DIFF domain (d1:num_set))`;
     `cfg1:C`] THEN
   ASM_REWRITE_TAC[FST; SND; FUPDATE_LIST_THM; SUBSET_UNION; PAIR_EQ]) THEN
  (SUBGOAL_THEN `alist_to_fmap aux' SUBMAP
                 alist_to_fmap (APPEND nc (aux':(num # num # clos_exp) list))` ASSUME_TAC THENL
    [MP_TAC(ASSUME `clos_state_code (t:(C,FFI)clos_state) SUBMAP clos_state_code t |++ nc`) THEN
     REWRITE_TAC[ASSUME `clos_state_code (t:(C,FFI)clos_state) = alist_to_fmap aux'`;
                 ASSUME `alist_to_fmap aux' |++ nc =
                         alist_to_fmap (APPEND nc (aux':(num # num # clos_exp) list))`];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[]) THEN
  (CONJ_TAC THENL
    [ALL_TAC;
     MAP_EVERY EXISTS_TAC [`d1:num_set`; `APPEND nc (aux':(num # num # clos_exp) list)`] THEN
     ASM_REWRITE_TAC[] THEN
     MP_TAC(ASSUME `wfg (d1:num_set,APPEND nc (aux':(num # num # clos_exp) list))`) THEN
     REWRITE_TAC[wfg_def; FST; SND]] THEN
   UNDISCH_TAC `clos_callProof_state_rel (g:num_set,aux':(num # num # clos_exp) list) l1
                  (r:(abs_calls_state # C,FFI)clos_state) (t:(C,FFI)clos_state)` THEN
   REWRITE_TAC[clos_callProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[]) THEN
  (SUBGOAL_THEN `!v1 v2. clos_callProof_v_rel (g,aux') l1 (clos_state_code (t:(C,FFI)clos_state)) v1 v2
                 ==> clos_callProof_v_rel (d1,APPEND nc aux')
                       (l1 UNION (set_of_list (code_locs exps) DIFF domain d1))
                       (alist_to_fmap (APPEND nc aux')) v1 v2` ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN MATCH_MP_TAC (GEN_ALL v_rel_SUBMAP_subg) THEN
     MAP_EVERY EXISTS_TAC [`clos_state_code (t:(C,FFI)clos_state)`; `l1:num->bool`;
                           `(g:num_set,aux':(num # num # clos_exp) list)`] THEN
     ASM_REWRITE_TAC[SUBSET_UNION];
     ALL_TAC] THEN
   CONJ_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (CLOSCALLPAUX_head_is "ALL2")) THEN
     MATCH_MP_TAC MONO_ALL2 THEN REPEAT GEN_TAC THEN MATCH_MP_TAC OPTREL_MONO THEN
     ASM_REWRITE_TAC[];
     FIRST_X_ASSUM(MP_TAC o check (CLOSCALLPAUX_head_is "fmap_rel")) THEN
     MATCH_MP_TAC fmap_rel_mono THEN REPEAT GEN_TAC THEN
     MATCH_MP_TAC CLOSCALLPAUX_ref_rel_mono THEN ASM_REWRITE_TAC[]]));;

let fv_GENLIST_Var_alt = prove
 (`!n i tra. clos_fv v (GENLIST_Var tra i n) <=> v < n`,
  REWRITE_TAC[fv_GENLIST_Var_tra]);;

let env_rel_env_exists = prove
 (`!vars:(num # clos_exp) list.
     ALL (wfv g1 l1 code) env ==>
     ?env5. clos_callProof_env_rel (clos_callProof_v_rel g1 l1 code) env env5 0 vars /\
            LENGTH env5 = LENGTH env`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`clos_callProof_v_rel g1 l1 code`; `env:clos_v list`]
                CLOSCALLPAUX_ALL2_EXISTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[v_rel_exists; ALL_MEM]; ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `l':clos_v list` THEN
  ASM_SIMP_TAC[CLOSCALLPAUX_ALL2_env_rel] THEN ASM_MESON_TAC[LIST_REL_LENGTH]);;

let evaluate_includes_state = prove
 (`!xs env (s:(A # C,FFI)clos_state) res s1 (g1:A # B).
     includes_state g1 (clos_state_compile_oracle s1) /\
     clos_evaluate (xs,env,s) = (res,s1) ==>
     includes_state g1 (clos_state_compile_oracle s)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP clos_evaluate_code) THEN STRIP_TAC THEN
  UNDISCH_TAC `includes_state (g1:A # B) (clos_state_compile_oracle (s1:(A # C,FFI)clos_state))` THEN
  ASM_REWRITE_TAC[includes_state_def; shift_seq_def; BETA_THM] THEN
  STRIP_TAC THEN EXISTS_TAC `k + n:num` THEN ASM_REWRITE_TAC[]);;

let evaluate_app_includes_state = prove
 (`!(xs:D) (env:E) (s:(A # C,FFI)clos_state) res s1 (g1:A # B).
     includes_state g1 (clos_state_compile_oracle s1) /\
     evaluate_app loco x vs s = (res,s1) ==>
     includes_state g1 (clos_state_compile_oracle s)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP evaluate_app_code) THEN STRIP_TAC THEN
  UNDISCH_TAC `includes_state (g1:A # B) (clos_state_compile_oracle (s1:(A # C,FFI)clos_state))` THEN
  ASM_REWRITE_TAC[includes_state_def; shift_seq_def; BETA_THM] THEN
  STRIP_TAC THEN EXISTS_TAC `k + n:num` THEN ASM_REWRITE_TAC[]);;

let evaluate_app_mono = prove
 (`evaluate_app x y z (s1:(C,FFI)clos_state) = (vs,s2)
   ==> clos_state_code s1 SUBMAP clos_state_code s2`,
  DISCH_THEN(MP_TAC o MATCH_MP evaluate_app_code) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBMAP_FUPDATE_LIST THEN ASM_REWRITE_TAC[]);;

let CLOSCALLPAUX_calls_pure = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g.
     clos_call_calls xs g0 = (ys,g) ==> ALL pure xs ==> ALL pure ys`,
  CLOSCALLPAUX_CALLS_IND2_TAC THEN CLOSCALLPAUX_UNWIND_IH_TAC THEN
  CLOSCALLPAUX_IH_CALLS_TAC THEN
  CLOSCALLPAUX_ADD_FACTS_TAC (fun th ->
    if CLOSCALLPAUX_is_calls_eq th then MATCH_MP calls_sing th else failwith "") THEN
  REPEAT (FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o check (fun th ->
    is_exists (concl th) && is_eq (snd(dest_exists(concl th))) &&
    is_var (lhs (snd(dest_exists(concl th))))))) THEN
  REWRITE_TAC[HD; ALL; pure_def; ALL_APPEND] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HD; ALL; pure_def; ALL_APPEND]) THEN
  ASM_MESON_TAC[]);;

let calls_pure = prove
 (`!xs (g:num_set # (num # num # clos_exp) list) es g1.
     ALL pure xs /\ clos_call_calls xs g = (es,g1) ==> ALL pure es`,
  MESON_TAC[CLOSCALLPAUX_calls_pure]);;

let calls_pure_sing = prove
 (`pure x1 /\ clos_call_calls [x1] (g:num_set # (num # num # clos_exp) list) = ([e1],g1)
   ==> pure e1`,
  MESON_TAC[calls_pure; ALL]);;

let wfg_subg_refl = prove
 (`wfg (g:A spt # (num # B) list) ==> subg g g`,
  SIMP_TAC[wfg_def; subg_refl]);;

let wfg_subg_EX_helper = prove
 (`wfg (g:A spt # (num # B) list) /\ P g ==> ?g2. subg g g2 /\ P g2`,
  MESON_TAC[wfg_subg_refl]);;

(* HOL4 SET_TO_LIST is list_of_set *)
let mk_code_g_def = cake_def
  `mk_code_g (code:(num,B)fmap) =
     (list_to_num_set (MAP PRE (list_of_set (FDOM code))), fmap_to_alist code)`;;

let pure_correct_eq = prove
 (CASE_TERM
  `pure e /\ clos_evaluate ([e],env,(s:(C,FFI)clos_state)) = (res,s') ==>
   match res with
     Rval vs -> s' = s /\ LENGTH vs = 1
   | Rerr (Rraise _) -> F
   | Rerr (Rabort a) -> a = Rtype_error`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`e:clos_exp`; `env:clos_v list`; `s:(C,FFI)clos_state`] pure_correct) THEN
  ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `res:(clos_v list,clos_v)result` (cases "result")) THEN
  CASE_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `a:clos_v error_result` (cases "error_result")) THEN
  CASE_REWRITE_TAC[]);;

(* HOL4 [local] *)
let clos_callProof_state_rel_opt_rel_refs = prove
 (`(clos_callProof_state_rel g l (s1:(abs_calls_state # C,FFI)clos_state)
      (s2:(C,FFI)clos_state) /\
    FLOOKUP (clos_state_refs s1) n = r1
    ==> ?r2. FLOOKUP (clos_state_refs s2) n = r2 /\
             OPTREL (clos_ref_rel (clos_callProof_v_rel g l (clos_state_code s2))) r1 r2) /\
   (clos_callProof_state_rel g l s1 s2 /\ FLOOKUP (clos_state_refs s2) n = r2
    ==> ?r1. FLOOKUP (clos_state_refs s1) n = r1 /\
             OPTREL (clos_ref_rel (clos_callProof_v_rel g l (clos_state_code s2))) r1 r2)`,
  REWRITE_TAC[clos_callProof_state_rel_def; fmap_rel_OPTREL_FLOOKUP] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[UNWIND_THM1] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* calls_correct: the two induction predicates (local abbreviations), the    *)
(* cases of the induction (one lemma per case of clos_evaluate_ind) and     *)
(* the theorem.                                                             *)
(* ------------------------------------------------------------------------- *)

let CLOSCALLPAUX_cc_P_def = cake_def
  `CLOSCALLPAUX_cc_P (xs,env1,(s0:(abs_calls_state # C,FFI)clos_state)) <=>
     !(g0:num_set # (num # num # clos_exp) list) g env2 (t0:(C,FFI)clos_state) ys res s l l1 g1.
       clos_evaluate (xs,env1,s0) = (res,s) /\
       ~(res = Rerr (Rabort Rtype_error)) /\
       clos_call_calls xs g0 = (ys,g) /\
       code_inv (SOME g1) l1 (clos_state_code s0) (clos_state_compile s0)
         (clos_state_compile_oracle s0) (clos_state_code t0) (clos_state_compile t0)
         (clos_state_compile_oracle t0) /\
       every_Fn_SOME xs /\ every_Fn_vs_NONE xs /\
       ALL (wfv g1 l1 (clos_state_code t0)) env1 /\
       wfv_state g1 l1 (clos_state_code t0) s0 /\ wfg g0 /\
       ALL_DISTINCT (code_locs xs) /\
       DISJOINT (IMAGE SUC (set_of_list (code_locs xs))) (set_of_list (MAP FST (SND g0))) /\
       l = set_of_list (code_locs xs) DIFF domain (FST g) /\
       subg g g1 /\ l SUBSET l1 /\ DISJOINT l1 (domain (FST g1)) /\ wfg g1 /\
       clos_callProof_env_rel (clos_callProof_v_rel g1 l1 (clos_state_code t0)) env1 env2 0
         (MAP (\x. (0,x)) ys) /\
       clos_callProof_state_rel g1 l1 s0 t0 /\ code_includes (SND g) (clos_state_code t0)
       ==>
       ?ck res' t g2 l2.
         code_inv (SOME g2) l2 (clos_state_code s) (clos_state_compile s)
           (clos_state_compile_oracle s) (clos_state_code t) (clos_state_compile t)
           (clos_state_compile_oracle t) /\
         wfv_state g2 l2 (clos_state_code t) s /\
         subg g1 g2 /\ wfg g2 /\ l1 SUBSET l2 /\ DISJOINT l2 (domain (FST g2)) /\
         every_result (ALL (wfv g2 l2 (clos_state_code t))) (wfv g2 l2 (clos_state_code t)) res /\
         clos_evaluate (ys,env2,clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) =
           (res',t) /\
         clos_callProof_state_rel g2 l2 s t /\
         result_rel (ALL2 (clos_callProof_v_rel g2 l2 (clos_state_code t)))
           (clos_callProof_v_rel g2 l2 (clos_state_code t)) res res'`;;

let CLOSCALLPAUX_cc_Q_def = cake_def
  `CLOSCALLPAUX_cc_Q loco f args (s0:(abs_calls_state # C,FFI)clos_state) <=>
     !g l (t0:(C,FFI)clos_state) res s f' args'.
       evaluate_app loco f args s0 = (res,s) /\
       ~(res = Rerr (Rabort Rtype_error)) /\
       code_inv (SOME g) l (clos_state_code s0) (clos_state_compile s0)
         (clos_state_compile_oracle s0) (clos_state_code t0) (clos_state_compile t0)
         (clos_state_compile_oracle t0) /\
       wfv g l (clos_state_code t0) f /\ ALL (wfv g l (clos_state_code t0)) args /\
       wfv_state g l (clos_state_code t0) s0 /\
       wfg g /\ DISJOINT l (domain (FST g)) /\
       clos_callProof_v_rel g l (clos_state_code t0) f f' /\
       ALL2 (clos_callProof_v_rel g l (clos_state_code t0)) args args' /\
       clos_callProof_state_rel g l s0 t0
       ==>
       ?ck res' t g2 l2.
         code_inv (SOME g2) l2 (clos_state_code s) (clos_state_compile s)
           (clos_state_compile_oracle s) (clos_state_code t) (clos_state_compile t)
           (clos_state_compile_oracle t) /\
         wfv_state g2 l2 (clos_state_code t) s /\
         every_result (ALL (wfv g2 l2 (clos_state_code t))) (wfv g2 l2 (clos_state_code t)) res /\
         evaluate_app loco f' args' (clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) =
           (res',t) /\
         clos_callProof_state_rel g2 l2 s t /\
         subg g g2 /\ wfg g2 /\ l SUBSET l2 /\ DISJOINT l2 (domain (FST g2)) /\
         result_rel (ALL2 (clos_callProof_v_rel g2 l2 (clos_state_code t)))
           (clos_callProof_v_rel g2 l2 (clos_state_code t)) res res'`;;

let CLOSCALLPAUX_cc_ind =
  let th = ISPECL [`CLOSCALLPAUX_cc_P:clos_exp list # clos_v list #
                      (abs_calls_state # C,FFI)clos_state -> bool`;
                   `CLOSCALLPAUX_cc_Q:num option -> clos_v -> clos_v list ->
                      (abs_calls_state # C,FFI)clos_state -> bool`] clos_evaluate_ind in
  th;;

let CLOSCALLPAUX_cc_case n = el n (conjuncts (lhand (concl CLOSCALLPAUX_cc_ind)));;

(* case [] *)
let CLOSCALLPAUX_cc_NIL = prove
 (CLOSCALLPAUX_cc_case 0,
  REWRITE_TAC[CLOSCALLPAUX_cc_P_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_evaluate_def; clos_call_calls_def; PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`0`; `Rval []:(clos_v list,clos_v)result`; `t0:(C,FFI)clos_state`;
                        `g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock; clos_evaluate_def; SUBSET_REFL;
                  every_result_def; ALL; result_rel_def; ALL2] THEN
  ASM_SIMP_TAC[wfg_subg_refl]);;

(* case evaluate_app with no arguments *)
let CLOSCALLPAUX_cc_app_NIL = prove
 (CLOSCALLPAUX_cc_case 13,
  REWRITE_TAC[CLOSCALLPAUX_cc_Q_def; clos_evaluate_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_NIL]) THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`0`; `Rval [f']:(clos_v list,clos_v)result`; `t0:(C,FFI)clos_state`;
                        `g:num_set # (num # num # clos_exp) list`; `l:num->bool`] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock; clos_evaluate_def; SUBSET_REFL;
                  every_result_def; ALL; result_rel_def; ALL2] THEN
  ASM_SIMP_TAC[wfg_subg_refl]);;

(* case Var *)
let CLOSCALLPAUX_cc_Var = prove
 (CLOSCALLPAUX_cc_case 2,
  REWRITE_TAC[CLOSCALLPAUX_cc_P_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_evaluate_def; clos_call_calls_def; PAIR_EQ] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL [ALL_TAC; MESON_TAC[]] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `n < LENGTH (env2:clos_v list) /\
                clos_callProof_v_rel g1 l1 (clos_state_code (t0:(C,FFI)clos_state))
                  (EL n env) (EL n env2)` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (CLOSCALLPAUX_head_is "clos_callProof_env_rel")) THEN
    REWRITE_TAC[clos_callProof_env_rel_def; MAP; EX] THEN CASE_REWRITE_TAC[fv1_thm] THEN
    COND_CASES_TAC THEN REWRITE_TAC[LIST_REL_EL_EQN; ADD_CLAUSES] THENL
     [ASM_MESON_TAC[]; DISCH_THEN(MP_TAC o SPEC `n:num`) THEN MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`0`; `Rval [EL n env2]:(clos_v list,clos_v)result`;
    `t0:(C,FFI)clos_state`; `g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock; clos_evaluate_def; SUBSET_REFL;
                  every_result_def; ALL; result_rel_def; ALL2] THEN
  ASM_SIMP_TAC[wfg_subg_refl] THEN
  ASM_MESON_TAC[ALL_MEM; MEM_EL]);;
let CLOSCALLPAUX_env_rel_MAP0 = prove
 (`!(R:clos_v->clos_v->bool) e1 e2 ys.
     clos_callProof_env_rel R e1 e2 0 (MAP (\x. (0,x)) ys) <=>
     if LENGTH e1 = LENGTH e2 then ALL2 R e1 e2 else
     !x. clos_fv x ys ==> x < LENGTH e1 /\ x < LENGTH e2 /\ R (EL x e1) (EL x e2)`,
  REWRITE_TAC[clos_callProof_env_rel_def; EX_MAP; o_DEF] THEN
  CASE_REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC[fv_exists; ETA_AX]);;

let CLOSCALLPAUX_env_rel_MAP0_mono = prove
 (`!(R:clos_v->clos_v->bool) e1 e2 ys ys'.
     (!x. clos_fv x ys' ==> clos_fv x ys) /\
     clos_callProof_env_rel R e1 e2 0 (MAP (\x. (0,x)) ys)
     ==> clos_callProof_env_rel R e1 e2 0 (MAP (\x. (0,x)) ys')`,
  REWRITE_TAC[CLOSCALLPAUX_env_rel_MAP0] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN MESON_TAC[]);;

(* clean-up of result_rel / every_result / singleton facts among the assumptions *)
let CLOSCALLPAUX_RES_CLEAN_TAC : tactic =
  REPEAT (CHANGED_TAC
    (RULE_ASSUM_TAC(REWRITE_RULE[CONS_11; LIST_REL_CONS1; LIST_REL_NIL; ALL; HD;
       every_result_def; every_error_result_def; result_rel_def; exc_rel_def;
       result_rel_Rval; result_rel_Rerr1]) THEN
     CLOSCALLPAUX_SPLIT_ASM_TAC THEN
     REPEAT (FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
     RVEQ_TAC));;

(* case Raise *)
let CLOSCALLPAUX_cc_Raise = prove
 (CLOSCALLPAUX_cc_case 5,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSCALLPAUX_cc_P_def] THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?r1 s1. clos_evaluate ([x1],env,(s:(abs_calls_state # C,FFI)clos_state)) =
                        (r1,s1)` STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[clos_evaluate_def; clos_call_calls_def; LET_DEF; LET_END_DEF] THEN
  IL1AUX_PAIRARG_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP calls_sing o check CLOSCALLPAUX_is_calls_eq) THEN
  RVEQ_TAC THEN REWRITE_TAC[HD; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[code_locs_def; every_Fn_SOME_def; every_Fn_vs_NONE_def]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`g0:num_set # (num # num # clos_exp) list`;
    `g:num_set # (num # num # clos_exp) list`; `env2:clos_v list`; `t0:(C,FFI)clos_state`;
    `[y:clos_exp]`; `r1:(clos_v list,clos_v)result`;
    `s1:(abs_calls_state # C,FFI)clos_state`;
    `set_of_list (code_locs [x1]) DIFF domain (FST (g:num_set # (num # num # clos_exp) list))`;
    `l1:num->bool`; `g1:num_set # (num # num # clos_exp) list`] o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC CLOSCALLPAUX_env_rel_MAP0_mono THEN
      EXISTS_TAC `[clos_Raise x y]` THEN ASM_REWRITE_TAC[clos_fv_def]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`ck:num`;
    CASE_TERM `match (res':(clos_v list,clos_v)result) with
                 Rval vs -> (Rerr (Rraise (HD vs)):(clos_v list,clos_v)result)
               | Rerr e -> Rerr e`;
    `t:(C,FFI)clos_state`; `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`] THEN
  REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `r1:(clos_v list,clos_v)result` THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ; result_rel_Rval; result_rel_Rerr1]) THEN
  CLOSCALLPAUX_SPLIT_ASM_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl)) THEN RVEQ_TAC THEN
  CASE_REWRITE_TAC[] THEN
  CLOSCALLPAUX_ADD_FACTS_TAC (MATCH_MP clos_evaluate_SING) THEN
  CLOSCALLPAUX_RES_CLEAN_TAC THEN
  ASM_REWRITE_TAC[HD; every_result_def; every_error_result_def; result_rel_def;
                  exc_rel_def; ALL]);;

let CLOSCALLPAUX_CHOOSE_NAMES (vs:term list) : thm_tactic =
  itlist (fun v ttac -> X_CHOOSE_THEN v ttac) vs STRIP_ASSUME_TAC;;

let CLOSCALLPAUX_IH_NAMES =
  [`ck:num`; `res1:(clos_v list,clos_v)result`; `t:(C,FFI)clos_state`;
   `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`];;

let CLOSCALLPAUX_dec_clock_add = prove
 (`!n ck (t0:(C,FFI)clos_state).
     n <= clos_state_clock t0 ==>
     clos_dec_clock n (clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) =
     clos_state_clock_fupd (K (clos_state_clock (clos_dec_clock n t0) + ck))
       (clos_dec_clock n t0)`,
  REWRITE_TAC[clos_dec_clock_def; clos_state_component_equality;
              clos_state_INFO.ri_accfupds; K_THM] THEN ARITH_TAC);;

let CLOSCALLPAUX_wfv_state_dec_clock = prove
 (`!g l code n (s:(A,FFI)clos_state).
     wfv_state g l code (clos_dec_clock n s) <=> wfv_state g l code s`,
  REWRITE_TAC[wfv_state_def; clos_dec_clock_def; clos_state_INFO.ri_accfupds]);;

let CLOSCALLPAUX_state_rel_dec_clock = prove
 (`!g l n (s:(abs_calls_state # C,FFI)clos_state) (t:(C,FFI)clos_state).
     clos_callProof_state_rel g l s t ==>
     clos_callProof_state_rel g l (clos_dec_clock n s) (clos_dec_clock n t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[clos_dec_clock_def] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP clos_callProof_state_rel_clock) THEN
  MATCH_MP_TAC clos_callProof_state_rel_with_clock THEN ASM_REWRITE_TAC[]);;

(* case Tick *)
let CLOSCALLPAUX_cc_Tick = prove
 (CLOSCALLPAUX_cc_case 11,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSCALLPAUX_cc_P_def] THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_evaluate_def; clos_call_calls_def; LET_DEF; LET_END_DEF] THEN
  IL1AUX_PAIRARG_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP calls_sing o check CLOSCALLPAUX_is_calls_eq) THEN
  RVEQ_TAC THEN REWRITE_TAC[HD; PAIR_EQ] THEN
  COND_CASES_TAC THEN STRIP_TAC THEN RVEQ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN CLOSCALLPAUX_SPLIT_ASM_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`0`; `Rerr (Rabort Rtimeout_error):(clos_v list,clos_v)result`;
      `t0:(C,FFI)clos_state`; `g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`] THEN
    REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock] THEN
    SUBGOAL_THEN `clos_state_clock (t0:(C,FFI)clos_state) = 0` ASSUME_TAC THENL
     [ASM_MESON_TAC[clos_callProof_state_rel_clock]; ALL_TAC] THEN
    ASM_REWRITE_TAC[clos_evaluate_def; SUBSET_REFL;
                    every_result_def; every_error_result_def; result_rel_def; exc_rel_def] THEN
    ASM_SIMP_TAC[wfg_subg_refl];
    RULE_ASSUM_TAC(REWRITE_RULE[code_locs_def; every_Fn_SOME_def; every_Fn_vs_NONE_def]) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`g0:num_set # (num # num # clos_exp) list`;
      `g:num_set # (num # num # clos_exp) list`; `env2:clos_v list`;
      `clos_dec_clock 1 (t0:(C,FFI)clos_state)`;
      `[y:clos_exp]`; `res:(clos_v list,clos_v)result`;
      `s':(abs_calls_state # C,FFI)clos_state`;
      `set_of_list (code_locs [x]) DIFF domain (FST (g:num_set # (num # num # clos_exp) list))`;
      `l1:num->bool`; `g1:num_set # (num # num # clos_exp) list`]) THEN
    ASM_SIMP_TAC[clos_dec_clock_code; dec_clock_compile_oracle; dec_clock_compile;
                 CLOSCALLPAUX_wfv_state_dec_clock; CLOSCALLPAUX_state_rel_dec_clock] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC CLOSCALLPAUX_env_rel_MAP0_mono THEN
      EXISTS_TAC `[clos_Tick x' y]` THEN ASM_REWRITE_TAC[clos_fv_def];
      ALL_TAC] THEN
    DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES CLOSCALLPAUX_IH_NAMES) THEN
    MAP_EVERY EXISTS_TAC CLOSCALLPAUX_IH_NAMES THEN
    ASM_REWRITE_TAC[clos_evaluate_def; clos_state_INFO.ri_accfupds; K_THM] THEN
    SUBGOAL_THEN `~(clos_state_clock (t0:(C,FFI)clos_state) = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[clos_callProof_state_rel_clock]; ALL_TAC] THEN
    ASM_SIMP_TAC[CLOSCALLPAUX_dec_clock_add; ARITH_RULE `~(c = 0) ==> 1 <= c`;
                 ARITH_RULE `~(c = 0) ==> ~(c + ck = 0)`]]);;

(* case Call: the source code table is empty, so a source call fails *)
let CLOSCALLPAUX_cc_Call = prove
 (CLOSCALLPAUX_cc_case 12,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSCALLPAUX_cc_P_def] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?r1 s2. clos_evaluate (xs,env,(s1:(abs_calls_state # C,FFI)clos_state)) =
                        (r1,s2)` STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[clos_evaluate_def; clos_call_calls_def; LET_DEF; LET_END_DEF] THEN
  IL1AUX_PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[code_locs_def; every_Fn_SOME_def; every_Fn_vs_NONE_def]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`g0:num_set # (num # num # clos_exp) list`;
    `g:num_set # (num # num # clos_exp) list`; `env2:clos_v list`; `t0:(C,FFI)clos_state`;
    `xs':clos_exp list`; `r1:(clos_v list,clos_v)result`;
    `s2:(abs_calls_state # C,FFI)clos_state`;
    `set_of_list (code_locs xs) DIFF domain (FST (g:num_set # (num # num # clos_exp) list))`;
    `l1:num->bool`; `g1:num_set # (num # num # clos_exp) list`] o
    check (fun th -> let vs,b = strip_forall (concl th) in length vs = 10)) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC CLOSCALLPAUX_env_rel_MAP0_mono THEN
      EXISTS_TAC `[clos_Call x ticks dest xs']` THEN ASM_REWRITE_TAC[clos_fv_def]];
    ALL_TAC] THEN
  DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES CLOSCALLPAUX_IH_NAMES) THEN
  SUBGOAL_THEN `clos_state_code (s2:(abs_calls_state # C,FFI)clos_state) = FEMPTY`
    ASSUME_TAC THENL [ASM_MESON_TAC[clos_callProof_state_rel_def]; ALL_TAC] THEN
  CASES_ON `r1:(clos_v list,clos_v)result` THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[clos_find_code_def; FLOOKUP_EMPTY]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN CLOSCALLPAUX_SPLIT_ASM_TAC THEN RVEQ_TAC THENL
   [RULE_ASSUM_TAC(CASE_REWRITE_RULE[ASSUME `clos_state_code
       (s2:(abs_calls_state # C,FFI)clos_state) = FEMPTY`; FLOOKUP_EMPTY]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN CLOSCALLPAUX_SPLIT_ASM_TAC THEN RVEQ_TAC THEN
    ASM_MESON_TAC[];
    MAP_EVERY EXISTS_TAC CLOSCALLPAUX_IH_NAMES THEN
    ASM_REWRITE_TAC[clos_evaluate_def] THEN
    CLOSCALLPAUX_RES_CLEAN_TAC THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[every_result_def; result_rel_def]]);;

(* glue for the sequential cases of calls_correct *)

(* two consecutive calls *)
let CLOSCALLPAUX_calls_chain = prove
 (`!xs ys (g0:num_set # (num # num # clos_exp) list) g' g e1 e2.
     clos_call_calls xs g0 = (e1,g') /\ clos_call_calls ys g' = (e2,g) /\
     wfg g0 /\ ALL_DISTINCT (APPEND (code_locs xs) (code_locs ys)) /\
     DISJOINT (IMAGE SUC (set_of_list (APPEND (code_locs xs) (code_locs ys))))
              (set_of_list (MAP FST (SND g0))) /\
     every_Fn_SOME xs /\ every_Fn_SOME ys
     ==> wfg g' /\ wfg g /\ subg g0 g' /\ subg g' g /\
         DISJOINT (IMAGE SUC (set_of_list (code_locs ys))) (set_of_list (MAP FST (SND g'))) /\
         (!x. MEM x (code_locs xs) /\ ~(x IN domain (FST g')) ==> ~(x IN domain (FST g)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ALL_DISTINCT_APPEND; SET_OF_LIST_APPEND; IMAGE_UNION; DISJOINT_UNION] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `wfg (g':num_set # (num # num # clos_exp) list)` ASSUME_TAC THENL
   [MATCH_MP_TAC calls_wfg THEN
    MAP_EVERY EXISTS_TAC [`xs:clos_exp list`; `g0:num_set # (num # num # clos_exp) list`;
                          `e1:clos_exp list`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE SUC (set_of_list (code_locs ys)))
                         (set_of_list (MAP FST (SND (g':num_set # (num # num # clos_exp) list))))`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`xs:clos_exp list`; `g0:num_set # (num # num # clos_exp) list`;
                   `e1:clos_exp list`; `g':num_set # (num # num # clos_exp) list`]
                  calls_add_SUC_code_locs) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ASSUME `DISJOINT (IMAGE SUC (set_of_list (code_locs ys)))
                     (set_of_list (MAP FST (SND (g0:num_set # (num # num # clos_exp) list))))`) THEN
    SUBGOAL_THEN `DISJOINT (IMAGE SUC (set_of_list (code_locs ys)))
                           (IMAGE SUC (set_of_list (code_locs xs)))` MP_TAC THENL
     [MATCH_MP_TAC CLOSCALLPAUX_DISJOINT_IMAGE_SUC THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_SET_OF_LIST; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC calls_wfg THEN
    MAP_EVERY EXISTS_TAC [`ys:clos_exp list`; `g':num_set # (num # num # clos_exp) list`;
                          `e2:clos_exp list`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC calls_subg THEN
    MAP_EVERY EXISTS_TAC [`xs:clos_exp list`; `e1:clos_exp list`] THEN
    ASM_MESON_TAC[wfg_def];
    MATCH_MP_TAC calls_subg THEN
    MAP_EVERY EXISTS_TAC [`ys:clos_exp list`; `e2:clos_exp list`] THEN
    ASM_MESON_TAC[wfg_def];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`ys:clos_exp list`; `g':num_set # (num # num # clos_exp) list`;
                   `e2:clos_exp list`; `g:num_set # (num # num # clos_exp) list`]
                  calls_domain_locs) THEN
    ASM_REWRITE_TAC[SUBSET; IN_UNION; IN_SET_OF_LIST] THEN
    DISCH_THEN(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let CLOSCALLPAUX_result_rel_mono = prove
 (`!g l code g' l' code' (r:(clos_v list,clos_v)result) r'.
     result_rel (ALL2 (clos_callProof_v_rel g l code)) (clos_callProof_v_rel g l code) r r' /\
     subg g g' /\ l SUBSET l' /\ code SUBMAP code'
     ==> result_rel (ALL2 (clos_callProof_v_rel g' l' code')) (clos_callProof_v_rel g' l' code')
           r r'`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:(clos_v list,clos_v)result` (cases "result")) THEN
  STRUCT_CASES_TAC(ISPEC `r':(clos_v list,clos_v)result` (cases "result")) THEN
  REWRITE_TAC[result_rel_def] THENL
   [MESON_TAC[LIST_REL_v_rel_subg];
    STRUCT_CASES_TAC(ISPEC `a:clos_v error_result` (cases "error_result")) THEN
    STRUCT_CASES_TAC(ISPEC `a':clos_v error_result` (cases "error_result")) THEN
    REWRITE_TAC[exc_rel_def] THEN MESON_TAC[v_rel_SUBMAP_subg]]);;

let CLOSCALLPAUX_every_result_mono = prove
 (`!g l code g' l' code' (r:(clos_v list,clos_v)result).
     every_result (ALL (wfv g l code)) (wfv g l code) r /\
     subg g g' /\ l SUBSET l' /\ code SUBMAP code'
     ==> every_result (ALL (wfv g' l' code')) (wfv g' l' code') r`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:(clos_v list,clos_v)result` (cases "result")) THEN
  REWRITE_TAC[every_result_def] THENL
   [MESON_TAC[EVERY_wfv_subg];
    STRUCT_CASES_TAC(ISPEC `a:clos_v error_result` (cases "error_result")) THEN
    REWRITE_TAC[every_error_result_def] THEN MESON_TAC[wfv_subg]]);;

let CLOSCALLPAUX_clock_add_add = prove
 (`!a b (t0:(C,FFI)clos_state).
     clos_state_clock_fupd (K (clos_state_clock (clos_state_clock_fupd
         (K (clos_state_clock t0 + a)) t0) + b))
       (clos_state_clock_fupd (K (clos_state_clock t0 + a)) t0) =
     clos_state_clock_fupd (K (clos_state_clock t0 + (a + b))) t0`,
  REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM] THEN
  ARITH_TAC);;

(* adding clock to a successful (or non-timeout) evaluation *)
let CLOSCALLPAUX_evaluate_add_clock_res = prove
 (`!xs env (t0:(C,FFI)clos_state) ck r t ck'.
     clos_evaluate (xs,env,clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) = (r,t) /\
     ~(r = Rerr (Rabort Rtimeout_error))
     ==> clos_evaluate (xs,env,clos_state_clock_fupd (K (clos_state_clock t0 + (ck + ck'))) t0) =
         (r,clos_state_clock_fupd (K (clos_state_clock t + ck')) t)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSCALLPAUX_evaluate_add_clock) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `ck':num`) THEN
  REWRITE_TAC[CLOSCALLPAUX_clock_add_add]);;

(* case: at least two expressions *)
let CLOSCALLPAUX_cc_CONS = prove
 (CLOSCALLPAUX_cc_case 1,
  (REPEAT GEN_TAC THEN REWRITE_TAC[CLOSCALLPAUX_cc_P_def] THEN STRIP_TAC THEN
   REPEAT GEN_TAC THEN
   SUBGOAL_THEN `?r1 s1. clos_evaluate ([x],env,(s:(abs_calls_state # C,FFI)clos_state)) =
                         (r1,s1)` STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN ONCE_REWRITE_TAC[clos_call_calls_def] THEN
   ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   REPEAT IL1AUX_PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP calls_sing o
     check (fun th -> CLOSCALLPAUX_is_calls_eq th &&
                      (try length (dest_list (rand (lhand (concl th)))) = 1 with _ -> false) ||
                      (try length (dest_list (lhand (lhs (concl th)))) = 1 with _ -> false))) THEN
   RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[code_locs_def; every_Fn_SOME_def; every_Fn_vs_NONE_def]) THEN
   CLOSCALLPAUX_SPLIT_ASM_TAC) THEN
  (RULE_ASSUM_TAC(REWRITE_RULE[LET_DEF; LET_END_DEF; APPEND]) THEN
   MP_TAC(ISPECL [`[x:clos_exp]`; `CONS (y:clos_exp) xs`;
                  `g0:num_set # (num # num # clos_exp) list`;
                  `g':num_set # (num # num # clos_exp) list`;
                  `g:num_set # (num # num # clos_exp) list`;
                  `[y':clos_exp]`; `e2':clos_exp list`] CLOSCALLPAUX_calls_chain) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC) THEN
  (RULE_ASSUM_TAC(REWRITE_RULE[ALL_DISTINCT_APPEND; SET_OF_LIST_APPEND; IMAGE_UNION;
                               DISJOINT_UNION]) THEN
   CLOSCALLPAUX_SPLIT_ASM_TAC THEN
   SUBGOAL_THEN `subg (g':num_set # (num # num # clos_exp) list) g1` ASSUME_TAC THENL
    [ASM_MESON_TAC[subg_trans]; ALL_TAC] THEN
   SUBGOAL_THEN `set_of_list (code_locs [x]) DIFF
                 domain (FST (g':num_set # (num # num # clos_exp) list)) SUBSET l1`
     ASSUME_TAC THENL
    [UNDISCH_TAC `(set_of_list (code_locs [x]) UNION set_of_list (code_locs (CONS y xs))) DIFF
                  domain (FST (g:num_set # (num # num # clos_exp) list)) SUBSET l1` THEN
     REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_SET_OF_LIST] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `code_includes (SND (g':num_set # (num # num # clos_exp) list))
                   (clos_state_code (t0:(C,FFI)clos_state))` ASSUME_TAC THENL
    [ASM_MESON_TAC[code_includes_subg]; ALL_TAC] THEN
   SUBGOAL_THEN `clos_callProof_env_rel (clos_callProof_v_rel g1 l1
                   (clos_state_code (t0:(C,FFI)clos_state))) env env2 0
                   (MAP (\x. (0,x)) [y'])` ASSUME_TAC THENL
    [MATCH_MP_TAC CLOSCALLPAUX_env_rel_MAP0_mono THEN
     EXISTS_TAC `CONS (y':clos_exp) e2'` THEN ASM_REWRITE_TAC[fv_cons; fv_nil] THEN
     MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
     ASM_MESON_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`g0:num_set # (num # num # clos_exp) list`;
     `g':num_set # (num # num # clos_exp) list`; `env2:clos_v list`; `t0:(C,FFI)clos_state`;
     `[y':clos_exp]`; `r1:(clos_v list,clos_v)result`;
     `s1:(abs_calls_state # C,FFI)clos_state`;
     `set_of_list (code_locs [x]) DIFF domain (FST (g':num_set # (num # num # clos_exp) list))`;
     `l1:num->bool`; `g1:num_set # (num # num # clos_exp) list`] o
     check (fun th -> let vs,b = strip_forall (concl th) in length vs = 10)) THEN
   ASM_REWRITE_TAC[]) THEN
  (DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck1:num`; `res1:(clos_v list,clos_v)result`;
     `t1:(C,FFI)clos_state`; `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`]) THEN
   SUBGOAL_THEN `?z zs. e2' = CONS (z:clos_exp) zs` STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP calls_length o check (fun th ->
       concl th = `clos_call_calls (CONS y xs) g' = e2',g`)) THEN
     STRUCT_CASES_TAC(ISPEC `e2':clos_exp list` list_CASES) THEN
     REWRITE_TAC[LENGTH; NOT_SUC; CONS_11] THEN MESON_TAC[];
     ALL_TAC] THEN
   RVEQ_TAC THEN REWRITE_TAC[APPEND] THEN
   CASES_ON `r1:(clos_v list,clos_v)result` THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN CLOSCALLPAUX_SPLIT_ASM_TAC THEN
   RVEQ_TAC) THENL
   [(SUBGOAL_THEN `clos_state_code (t0:(C,FFI)clos_state) SUBMAP clos_state_code (t1:(C,FFI)clos_state)`
     ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP clos_evaluate_mono o check (fun th ->
       try rand(concl th) = `res1:(clos_v list,clos_v)result,t1:(C,FFI)clos_state` with _ -> false)) THEN
     REWRITE_TAC[clos_state_INFO.ri_accfupds];
     ALL_TAC] THEN
   SUBGOAL_THEN `ALL (wfv g2 l2 (clos_state_code (t1:(C,FFI)clos_state))) env` ASSUME_TAC THENL
    [MATCH_MP_TAC (GEN_ALL EVERY_wfv_subg) THEN
     MAP_EVERY EXISTS_TAC [`clos_state_code (t0:(C,FFI)clos_state)`;
                           `g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `subg (g:num_set # (num # num # clos_exp) list) g2` ASSUME_TAC THENL
    [ASM_MESON_TAC[subg_trans]; ALL_TAC] THEN
   SUBGOAL_THEN `set_of_list (code_locs (CONS y xs)) DIFF
                 domain (FST (g:num_set # (num # num # clos_exp) list)) SUBSET l2`
     ASSUME_TAC THENL
    [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l1:num->bool` THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `(set_of_list (code_locs [x]) UNION set_of_list (code_locs (CONS y xs))) DIFF
                  domain (FST (g:num_set # (num # num # clos_exp) list)) SUBSET l1` THEN
     SET_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `clos_callProof_env_rel (clos_callProof_v_rel g2 l2
                   (clos_state_code (t1:(C,FFI)clos_state))) env env2 0
                   (MAP (\x. (0,x)) (CONS z zs))` ASSUME_TAC THENL
    [MATCH_MP_TAC CLOSCALLPAUX_env_rel_MAP0_mono THEN
     EXISTS_TAC `CONS (y':clos_exp) (CONS z zs)` THEN
     CONJ_TAC THENL [REWRITE_TAC[fv_cons] THEN MESON_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC (GEN_ALL env_rel_subg) THEN
     MAP_EVERY EXISTS_TAC [`g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`;
                           `clos_state_code (t0:(C,FFI)clos_state)`] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `code_includes (SND (g:num_set # (num # num # clos_exp) list))
                   (clos_state_code (t1:(C,FFI)clos_state))` ASSUME_TAC THENL
    [ASM_MESON_TAC[code_includes_SUBMAP]; ALL_TAC] THEN
   SUBGOAL_THEN `~(x' = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
     ASM_MESON_TAC[];
     ALL_TAC]) THEN
    (FIRST_X_ASSUM(MP_TAC o SPECL [`a:clos_v list`; `s1:(abs_calls_state # C,FFI)clos_state`] o
     check (fun th -> let vs,b = strip_forall (concl th) in length vs = 2)) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`g':num_set # (num # num # clos_exp) list`;
     `g:num_set # (num # num # clos_exp) list`; `env2:clos_v list`; `t1:(C,FFI)clos_state`;
     `CONS (z:clos_exp) zs`; `x':(clos_v list,clos_v)result`;
     `s2':(abs_calls_state # C,FFI)clos_state`;
     `set_of_list (code_locs (CONS y xs)) DIFF domain (FST (g:num_set # (num # num # clos_exp) list))`;
     `l2:num->bool`; `g2:num_set # (num # num # clos_exp) list`]) THEN
   ASM_REWRITE_TAC[]) THEN
    (DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck2:num`; `res2:(clos_v list,clos_v)result`;
     `t2:(C,FFI)clos_state`; `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`]) THEN
   CLOSCALLPAUX_ADD_FACTS_TAC (MATCH_MP clos_evaluate_SING) THEN
   CLOSCALLPAUX_RES_CLEAN_TAC) THEN
    (SUBGOAL_THEN `clos_state_code (t1:(C,FFI)clos_state) SUBMAP clos_state_code (t2:(C,FFI)clos_state)`
     ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP clos_evaluate_mono o check (fun th ->
       try rand(concl th) = `res2:(clos_v list,clos_v)result,t2:(C,FFI)clos_state` with _ -> false)) THEN
     REWRITE_TAC[clos_state_INFO.ri_accfupds];
     ALL_TAC] THEN
   FIRST_ASSUM(MP_TAC o SPEC `ck2:num` o
     MATCH_MP (REWRITE_RULE[IMP_CONJ] CLOSCALLPAUX_evaluate_add_clock_res) o
     check (fun th -> try (let l = lhs (concl th) in
                           fst(dest_const(rator l)) = "clos_evaluate" &&
                           fst (dest_pair (rand l)) = `[y':clos_exp]`)
                      with _ -> false)) THEN
   REWRITE_TAC[distinctness "result"] THEN DISCH_TAC) THEN
    (MAP_EVERY EXISTS_TAC [`ck1 + ck2:num`;
     CASE_TERM `match (res2:(clos_v list,clos_v)result) with
                  Rval vs -> (Rval (CONS h' vs):(clos_v list,clos_v)result)
                | Rerr e -> Rerr e`;
     `t2:(C,FFI)clos_state`; `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`] THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[HD] THEN
   SUBGOAL_THEN `subg (g1:num_set # (num # num # clos_exp) list) g3 /\ (l1:num->bool) SUBSET l3`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[subg_trans; SUBSET_TRANS]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   CASES_ON `x':(clos_v list,clos_v)result` THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN CLOSCALLPAUX_SPLIT_ASM_TAC THEN RVEQ_TAC THEN
   CLOSCALLPAUX_RES_CLEAN_TAC THEN CASE_REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[HD; every_result_def; result_rel_def; ALL; ALL2] THEN
   ASM_MESON_TAC[wfv_subg; v_rel_SUBMAP_subg]);
    (MAP_EVERY EXISTS_TAC [`ck1:num`; `res1:(clos_v list,clos_v)result`;
     `t1:(C,FFI)clos_state`; `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`] THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
   CLOSCALLPAUX_RES_CLEAN_TAC THEN CASE_REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[every_result_def; result_rel_def])]);;

let CLOSCALLPAUX_WITH_EVAL_VAL (e:term) (f:term -> tactic) : tactic = fun (asl,w as gl) ->
  let th = snd(find (fun (_,th) ->
    try (let l = lhs (concl th) in fst(dest_const(rator l)) = "clos_evaluate" &&
         fst (dest_pair (rand l)) = e &&
         (let r = fst(dest_pair(rhs (concl th))) in
          is_comb r && fst(dest_const(rator r)) = "Rval"))
    with Failure _ -> false) asl) in
  let v = hd (dest_list (rand (fst (dest_pair (rhs (concl th)))))) in
  f v gl;;

(* case If *)
let CLOSCALLPAUX_cc_If = prove
 (CLOSCALLPAUX_cc_case 3,
  (REPEAT GEN_TAC THEN REWRITE_TAC[CLOSCALLPAUX_cc_P_def] THEN STRIP_TAC THEN
   REPEAT GEN_TAC THEN
   SUBGOAL_THEN `?r1 s1. clos_evaluate ([x1],env,(s:(abs_calls_state # C,FFI)clos_state)) =
                         (r1,s1)` STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN ONCE_REWRITE_TAC[clos_call_calls_def] THEN
   ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   REPEAT IL1AUX_PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   CLOSCALLPAUX_ADD_FACTS_TAC (fun th ->
     if CLOSCALLPAUX_is_calls_eq th then MATCH_MP calls_sing th else failwith "") THEN
   REPEAT (FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o check (fun th ->
     is_exists (concl th) && is_eq (snd(dest_exists(concl th))) &&
     is_var (lhs (snd(dest_exists(concl th))))))) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[code_locs_def; every_Fn_SOME_def; every_Fn_vs_NONE_def;
                               LET_DEF; LET_END_DEF; HD]) THEN
   REWRITE_TAC[HD] THEN CLOSCALLPAUX_SPLIT_ASM_TAC) THEN
    (SUBGOAL_THEN `clos_call_calls [x2; x3] g' = ([y'; y''],(g:num_set # (num # num # clos_exp) list))`
     ASSUME_TAC THENL
    [ONCE_REWRITE_TAC[clos_call_calls_def] THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
     CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[APPEND];
     ALL_TAC] THEN
   SUBGOAL_THEN `code_locs [x2; x3] = APPEND (code_locs [x2]) (code_locs [x3])` ASSUME_TAC THENL
    [REWRITE_TAC[code_locs_def; LET_DEF; LET_END_DEF]; ALL_TAC]) THEN
    (MP_TAC(ISPECL [`[x1:clos_exp]`; `[x2:clos_exp; x3]`;
                  `g0:num_set # (num # num # clos_exp) list`;
                  `g':num_set # (num # num # clos_exp) list`;
                  `g:num_set # (num # num # clos_exp) list`;
                  `[y:clos_exp]`; `[y':clos_exp; y'']`] CLOSCALLPAUX_calls_chain) THEN
   ASM_REWRITE_TAC[APPEND_ASSOC; every_Fn_SOME_def] THEN STRIP_TAC THEN
   MP_TAC(ISPECL [`[x2:clos_exp]`; `[x3:clos_exp]`;
                  `g':num_set # (num # num # clos_exp) list`;
                  `g'':num_set # (num # num # clos_exp) list`;
                  `g:num_set # (num # num # clos_exp) list`;
                  `[y':clos_exp]`; `[y'':clos_exp]`] CLOSCALLPAUX_calls_chain) THEN
   ASM_REWRITE_TAC[] THEN
   ANTS_TAC THENL
    [UNDISCH_TAC `ALL_DISTINCT (APPEND (APPEND (code_locs [x1]) (code_locs [x2]))
                    (code_locs [x3]))` THEN
     REWRITE_TAC[ALL_DISTINCT_APPEND; MEM_APPEND] THEN MESON_TAC[];
     STRIP_TAC]) THEN
    (RULE_ASSUM_TAC(REWRITE_RULE[ALL_DISTINCT_APPEND; SET_OF_LIST_APPEND; IMAGE_UNION;
                               DISJOINT_UNION; MEM_APPEND]) THEN
   CLOSCALLPAUX_SPLIT_ASM_TAC THEN
   SUBGOAL_THEN `subg (g':num_set # (num # num # clos_exp) list) g1` ASSUME_TAC THENL
    [MATCH_MP_TAC subg_trans THEN
     EXISTS_TAC `g:num_set # (num # num # clos_exp) list` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `set_of_list (code_locs [x1]) DIFF
                 domain (FST (g':num_set # (num # num # clos_exp) list)) SUBSET l1`
     ASSUME_TAC THENL
    [UNDISCH_TAC `((set_of_list (code_locs [x1]) UNION set_of_list (code_locs [x2])) UNION
                   set_of_list (code_locs [x3])) DIFF
                  domain (FST (g:num_set # (num # num # clos_exp) list)) SUBSET l1` THEN
     REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_SET_OF_LIST] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `code_includes (SND (g':num_set # (num # num # clos_exp) list))
                   (clos_state_code (t0:(C,FFI)clos_state))` ASSUME_TAC THENL
    [MATCH_MP_TAC(GEN_ALL(REWRITE_RULE[IMP_IMP] code_includes_subg)) THEN
     EXISTS_TAC `g:num_set # (num # num # clos_exp) list` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `clos_callProof_env_rel (clos_callProof_v_rel g1 l1
                   (clos_state_code (t0:(C,FFI)clos_state))) env env2 0
                   (MAP (\x. (0,x)) [y])` ASSUME_TAC THENL
    [MATCH_MP_TAC CLOSCALLPAUX_env_rel_MAP0_mono THEN
     EXISTS_TAC `[clos_If x y y' y'']` THEN ASM_REWRITE_TAC[clos_fv_def] THEN MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
     ASM_MESON_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`g0:num_set # (num # num # clos_exp) list`;
     `g':num_set # (num # num # clos_exp) list`; `env2:clos_v list`; `t0:(C,FFI)clos_state`;
     `[y:clos_exp]`; `r1:(clos_v list,clos_v)result`;
     `s1:(abs_calls_state # C,FFI)clos_state`;
     `set_of_list (code_locs [x1]) DIFF domain (FST (g':num_set # (num # num # clos_exp) list))`;
     `l1:num->bool`; `g1:num_set # (num # num # clos_exp) list`] o
     check (fun th -> let vs,b = strip_forall (concl th) in length vs = 10)) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck1:num`; `res1:(clos_v list,clos_v)result`;
     `t1:(C,FFI)clos_state`; `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`])) THEN
    (CASES_ON `r1:(clos_v list,clos_v)result` THENL
    [ALL_TAC;
     RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN CLOSCALLPAUX_SPLIT_ASM_TAC THEN RVEQ_TAC THEN
     MAP_EVERY EXISTS_TAC [`ck1:num`; `res1:(clos_v list,clos_v)result`;
       `t1:(C,FFI)clos_state`; `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`] THEN
     ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
     CLOSCALLPAUX_RES_CLEAN_TAC THEN CASE_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[every_result_def; result_rel_def]]) THEN
    (CLOSCALLPAUX_ADD_FACTS_TAC (MATCH_MP clos_evaluate_SING) THEN
   CLOSCALLPAUX_RES_CLEAN_TAC THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[HD]) THEN
   SUBGOAL_THEN `clos_state_code (t0:(C,FFI)clos_state) SUBMAP clos_state_code (t1:(C,FFI)clos_state)`
     ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP clos_evaluate_mono o check (fun th ->
       try (let l = lhs (concl th) in fst(dest_const(rator l)) = "clos_evaluate" &&
                fst (dest_pair (rand l)) = `[y:clos_exp]`) with _ -> false)) THEN
     REWRITE_TAC[clos_state_INFO.ri_accfupds];
     ALL_TAC] THEN
   SUBGOAL_THEN `ALL (wfv g2 l2 (clos_state_code (t1:(C,FFI)clos_state))) env` ASSUME_TAC THENL
    [MATCH_MP_TAC (GEN_ALL EVERY_wfv_subg) THEN
     MAP_EVERY EXISTS_TAC [`clos_state_code (t0:(C,FFI)clos_state)`;
                           `g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `subg (g:num_set # (num # num # clos_exp) list) g2` ASSUME_TAC THENL
    [MATCH_MP_TAC subg_trans THEN
     EXISTS_TAC `g1:num_set # (num # num # clos_exp) list` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `subg (g'':num_set # (num # num # clos_exp) list) g2` ASSUME_TAC THENL
    [MATCH_MP_TAC subg_trans THEN
     EXISTS_TAC `g:num_set # (num # num # clos_exp) list` THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
    (CLOSCALLPAUX_WITH_EVAL_VAL `[x1:clos_exp]` (fun v ->
     ASM_CASES_TAC (mk_eq(`clos_Boolv T`, v)) THENL
      [ALL_TAC; ASM_CASES_TAC (mk_eq(`clos_Boolv F`, v))])) THENL
   [(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
     is_eq (concl th) && lhs (concl th) = `clos_Boolv T`)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[clos_callProof_v_rel_Boolv]) THEN RVEQ_TAC THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`[clos_Boolv T]`; `s1:(abs_calls_state # C,FFI)clos_state`] o
     check (fun th -> let vs,b = strip_forall (concl th) in length vs = 2 &&
              is_imp b && not (is_conj (rand (lhand b))))) THEN
   ASM_REWRITE_TAC[HD]) THEN
    (DISCH_THEN(MP_TAC o SPECL [`g':num_set # (num # num # clos_exp) list`;
     `g'':num_set # (num # num # clos_exp) list`; `env2:clos_v list`; `t1:(C,FFI)clos_state`;
     `[y':clos_exp]`; `res:(clos_v list,clos_v)result`;
     `s':(abs_calls_state # C,FFI)clos_state`;
     `set_of_list (code_locs [x2]) DIFF domain (FST (g'':num_set # (num # num # clos_exp) list))`;
     `l2:num->bool`; `g2:num_set # (num # num # clos_exp) list`]) THEN
   ASM_REWRITE_TAC[]) THEN
    (ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l1:num->bool` THEN ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `((set_of_list (code_locs [x1]) UNION set_of_list (code_locs [x2])) UNION
                     set_of_list (code_locs [x3])) DIFF
                    domain (FST (g:num_set # (num # num # clos_exp) list)) SUBSET l1` THEN
       REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_SET_OF_LIST] THEN ASM_MESON_TAC[];
       MATCH_MP_TAC CLOSCALLPAUX_env_rel_MAP0_mono THEN
       EXISTS_TAC `[clos_If x y y' y'']` THEN
       CONJ_TAC THENL [REWRITE_TAC[clos_fv_def] THEN MESON_TAC[]; ALL_TAC] THEN
       MATCH_MP_TAC (GEN_ALL env_rel_subg) THEN
       MAP_EVERY EXISTS_TAC [`g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`;
                             `clos_state_code (t0:(C,FFI)clos_state)`] THEN
       ASM_REWRITE_TAC[];
       ASM_MESON_TAC[code_includes_subg; code_includes_SUBMAP]];
     ALL_TAC] THEN
   DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck2:num`; `res2:(clos_v list,clos_v)result`;
     `t2:(C,FFI)clos_state`; `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`])) THEN
    (FIRST_ASSUM(MP_TAC o SPEC `ck2:num` o
     MATCH_MP (REWRITE_RULE[IMP_CONJ] CLOSCALLPAUX_evaluate_add_clock_res) o
     check (fun th -> try (let l = lhs (concl th) in
                           fst(dest_const(rator l)) = "clos_evaluate" &&
                           fst (dest_pair (rand l)) = `[y:clos_exp]`)
                      with _ -> false)) THEN
   REWRITE_TAC[distinctness "result"] THEN DISCH_TAC THEN
   MAP_EVERY EXISTS_TAC [`ck1 + ck2:num`; `res2:(clos_v list,clos_v)result`;
     `t2:(C,FFI)clos_state`; `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`] THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD] THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[subg_trans; SUBSET_TRANS]);
    (FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
     is_eq (concl th) && lhs (concl th) = `clos_Boolv F`)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[clos_callProof_v_rel_Boolv; clos_Boolv_11]) THEN RVEQ_TAC THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[clos_Boolv_11]) THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`[clos_Boolv F]`; `s1:(abs_calls_state # C,FFI)clos_state`] o
     check (fun th -> let vs,b = strip_forall (concl th) in length vs = 2 &&
              is_imp b && is_conj (rand (lhand b)))) THEN
   ASM_REWRITE_TAC[HD; clos_Boolv_11] THEN
   DISCH_THEN(MP_TAC o SPECL [`g'':num_set # (num # num # clos_exp) list`;
     `g:num_set # (num # num # clos_exp) list`; `env2:clos_v list`; `t1:(C,FFI)clos_state`;
     `[y'':clos_exp]`; `res:(clos_v list,clos_v)result`;
     `s':(abs_calls_state # C,FFI)clos_state`;
     `set_of_list (code_locs [x3]) DIFF domain (FST (g:num_set # (num # num # clos_exp) list))`;
     `l2:num->bool`; `g2:num_set # (num # num # clos_exp) list`]) THEN
   ASM_REWRITE_TAC[]) THEN
    (ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l1:num->bool` THEN ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `((set_of_list (code_locs [x1]) UNION set_of_list (code_locs [x2])) UNION
                     set_of_list (code_locs [x3])) DIFF
                    domain (FST (g:num_set # (num # num # clos_exp) list)) SUBSET l1` THEN
       SET_TAC[];
       MATCH_MP_TAC CLOSCALLPAUX_env_rel_MAP0_mono THEN
       EXISTS_TAC `[clos_If x y y' y'']` THEN
       CONJ_TAC THENL [REWRITE_TAC[clos_fv_def] THEN MESON_TAC[]; ALL_TAC] THEN
       MATCH_MP_TAC (GEN_ALL env_rel_subg) THEN
       MAP_EVERY EXISTS_TAC [`g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`;
                             `clos_state_code (t0:(C,FFI)clos_state)`] THEN
       ASM_REWRITE_TAC[];
       ASM_MESON_TAC[code_includes_SUBMAP]];
     ALL_TAC] THEN
   DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck2:num`; `res2:(clos_v list,clos_v)result`;
     `t2:(C,FFI)clos_state`; `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`]) THEN
   FIRST_ASSUM(MP_TAC o SPEC `ck2:num` o
     MATCH_MP (REWRITE_RULE[IMP_CONJ] CLOSCALLPAUX_evaluate_add_clock_res) o
     check (fun th -> try (let l = lhs (concl th) in
                           fst(dest_const(rator l)) = "clos_evaluate" &&
                           fst (dest_pair (rand l)) = `[y:clos_exp]`)
                      with _ -> false)) THEN
   REWRITE_TAC[distinctness "result"] THEN DISCH_TAC THEN
   MAP_EVERY EXISTS_TAC [`ck1 + ck2:num`; `res2:(clos_v list,clos_v)result`;
     `t2:(C,FFI)clos_state`; `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`] THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
   CASE_REWRITE_TAC[HD; clos_Boolv_11] THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[subg_trans; SUBSET_TRANS]);
    (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     (try is_cond (lhs (concl th)) with _ -> false))) THEN
   ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
     `~(res = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)`)) THEN
   ASM_REWRITE_TAC[])]);;

let CLOSCALLPAUX_env_rel_APPEND_body = prove
 (`!(R:clos_v->clos_v->bool) vs vs' env env2 e2 ys.
     ALL2 R vs vs' /\
     (!x. clos_fv x [e2] /\ ~(x < LENGTH vs) ==> clos_fv (x - LENGTH vs) ys) /\
     clos_callProof_env_rel R env env2 0 (MAP (\x. (0,x)) ys)
     ==> clos_callProof_env_rel R (APPEND vs env) (APPEND vs' env2) 0 (MAP (\x. (0,x)) [e2])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSCALLPAUX_env_rel_MAP0; LENGTH_APPEND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (vs':clos_v list) = LENGTH (vs:clos_v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC] THEN
  ASM_REWRITE_TAC[EQ_ADD_LCANCEL] THEN
  ASM_CASES_TAC `LENGTH (env:clos_v list) = LENGTH (env2:clos_v list)` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[EVERY2_APPEND_suff]; ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN REWRITE_TAC[EL_APPEND] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[LIST_REL_EL_EQN];
    FIRST_X_ASSUM(MP_TAC o SPEC `x - LENGTH (vs:clos_v list)` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `LENGTH (env2:clos_v list)`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let CLOSCALLPAUX_WITH_EVAL_VALS (e:term) (f:term -> tactic) : tactic = fun (asl,w as gl) ->
  let th = snd(find (fun (_,th) ->
    try (let l = lhs (concl th) in fst(dest_const(rator l)) = "clos_evaluate" &&
         fst (dest_pair (rand l)) = e &&
         (let r = fst(dest_pair(rhs (concl th))) in
          is_comb r && fst(dest_const(rator r)) = "Rval"))
    with Failure _ -> false) asl) in
  f (rand (fst (dest_pair (rhs (concl th))))) gl;;

(* case Let *)
let CLOSCALLPAUX_cc_Let = prove
 (CLOSCALLPAUX_cc_case 4,
  (REPEAT GEN_TAC THEN REWRITE_TAC[CLOSCALLPAUX_cc_P_def] THEN STRIP_TAC THEN
   REPEAT GEN_TAC THEN
   SUBGOAL_THEN `?r1 s1. clos_evaluate (xs,env,(s:(abs_calls_state # C,FFI)clos_state)) =
                         (r1,s1)` STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN ONCE_REWRITE_TAC[clos_call_calls_def] THEN
   ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   REPEAT IL1AUX_PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   CLOSCALLPAUX_ADD_FACTS_TAC (fun th ->
     if CLOSCALLPAUX_is_calls_eq th then MATCH_MP calls_sing th else failwith "") THEN
   REPEAT (FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o check (fun th ->
     is_exists (concl th) && is_eq (snd(dest_exists(concl th))) &&
     is_var (lhs (snd(dest_exists(concl th))))))) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[code_locs_def; every_Fn_SOME_def; every_Fn_vs_NONE_def;
                               LET_DEF; LET_END_DEF; HD]) THEN
   REWRITE_TAC[HD] THEN CLOSCALLPAUX_SPLIT_ASM_TAC) THEN
  (MP_TAC(ISPECL [`xs:clos_exp list`; `[x2:clos_exp]`;
                  `g0:num_set # (num # num # clos_exp) list`;
                  `g':num_set # (num # num # clos_exp) list`;
                  `g:num_set # (num # num # clos_exp) list`;
                  `e1':clos_exp list`; `[y:clos_exp]`] CLOSCALLPAUX_calls_chain) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ALL_DISTINCT_APPEND; SET_OF_LIST_APPEND; IMAGE_UNION;
                               DISJOINT_UNION; MEM_APPEND]) THEN
   CLOSCALLPAUX_SPLIT_ASM_TAC THEN
   SUBGOAL_THEN `subg (g':num_set # (num # num # clos_exp) list) g1` ASSUME_TAC THENL
    [ASM_MESON_TAC[subg_trans]; ALL_TAC] THEN
   SUBGOAL_THEN `set_of_list (code_locs xs) DIFF
                 domain (FST (g':num_set # (num # num # clos_exp) list)) SUBSET l1`
     ASSUME_TAC THENL
    [UNDISCH_TAC `(set_of_list (code_locs xs) UNION set_of_list (code_locs [x2])) DIFF
                  domain (FST (g:num_set # (num # num # clos_exp) list)) SUBSET l1` THEN
     REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_SET_OF_LIST] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `code_includes (SND (g':num_set # (num # num # clos_exp) list))
                   (clos_state_code (t0:(C,FFI)clos_state))` ASSUME_TAC THENL
    [ASM_MESON_TAC[code_includes_subg]; ALL_TAC] THEN
   SUBGOAL_THEN `clos_callProof_env_rel (clos_callProof_v_rel g1 l1
                   (clos_state_code (t0:(C,FFI)clos_state))) env env2 0
                   (MAP (\x. (0,x)) e1')` ASSUME_TAC THENL
    [MATCH_MP_TAC CLOSCALLPAUX_env_rel_MAP0_mono THEN
     EXISTS_TAC `[clos_Let x e1' y]` THEN ASM_REWRITE_TAC[clos_fv_def] THEN MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
     ASM_MESON_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`g0:num_set # (num # num # clos_exp) list`;
     `g':num_set # (num # num # clos_exp) list`; `env2:clos_v list`; `t0:(C,FFI)clos_state`;
     `e1':clos_exp list`; `r1:(clos_v list,clos_v)result`;
     `s1:(abs_calls_state # C,FFI)clos_state`;
     `set_of_list (code_locs xs) DIFF domain (FST (g':num_set # (num # num # clos_exp) list))`;
     `l1:num->bool`; `g1:num_set # (num # num # clos_exp) list`] o
     check (fun th -> let vs,b = strip_forall (concl th) in length vs = 10)) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck1:num`; `res1:(clos_v list,clos_v)result`;
     `t1:(C,FFI)clos_state`; `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`]) THEN
   CASES_ON `r1:(clos_v list,clos_v)result` THENL
    [ALL_TAC;
     RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN CLOSCALLPAUX_SPLIT_ASM_TAC THEN RVEQ_TAC THEN
     MAP_EVERY EXISTS_TAC [`ck1:num`; `res1:(clos_v list,clos_v)result`;
       `t1:(C,FFI)clos_state`; `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`] THEN
     ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
     CLOSCALLPAUX_RES_CLEAN_TAC THEN CASE_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[every_result_def; result_rel_def]]) THEN
  (RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
   CLOSCALLPAUX_RES_CLEAN_TAC THEN
   SUBGOAL_THEN `clos_state_code (t0:(C,FFI)clos_state) SUBMAP clos_state_code (t1:(C,FFI)clos_state)`
     ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP clos_evaluate_mono o check (fun th ->
       try (let l = lhs (concl th) in fst(dest_const(rator l)) = "clos_evaluate" &&
                fst (dest_pair (rand l)) = `e1':clos_exp list`) with _ -> false)) THEN
     REWRITE_TAC[clos_state_INFO.ri_accfupds];
     ALL_TAC] THEN
   SUBGOAL_THEN `ALL (wfv g2 l2 (clos_state_code (t1:(C,FFI)clos_state))) env` ASSUME_TAC THENL
    [MATCH_MP_TAC (GEN_ALL EVERY_wfv_subg) THEN
     MAP_EVERY EXISTS_TAC [`clos_state_code (t0:(C,FFI)clos_state)`;
                           `g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `subg (g:num_set # (num # num # clos_exp) list) g2` ASSUME_TAC THENL
    [ASM_MESON_TAC[subg_trans]; ALL_TAC] THEN
   SUBGOAL_THEN `set_of_list (code_locs [x2]) DIFF
                 domain (FST (g:num_set # (num # num # clos_exp) list)) SUBSET l2`
     ASSUME_TAC THENL
    [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l1:num->bool` THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `(set_of_list (code_locs xs) UNION set_of_list (code_locs [x2])) DIFF
                  domain (FST (g:num_set # (num # num # clos_exp) list)) SUBSET l1` THEN
     SET_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `code_includes (SND (g:num_set # (num # num # clos_exp) list))
                   (clos_state_code (t1:(C,FFI)clos_state))` ASSUME_TAC THENL
    [ASM_MESON_TAC[code_includes_SUBMAP]; ALL_TAC] THEN
   SUBGOAL_THEN `LENGTH (a:clos_v list) = LENGTH (e1':clos_exp list)` ASSUME_TAC THENL
    [ASM_MESON_TAC[clos_evaluate_IMP_LENGTH; calls_length]; ALL_TAC]) THEN
  (CLOSCALLPAUX_WITH_EVAL_VALS `e1':clos_exp list` (fun vs' ->
   SUBGOAL_THEN (subst [vs',`vv:clos_v list`]
     `clos_callProof_env_rel (clos_callProof_v_rel g2 l2
        (clos_state_code (t1:(C,FFI)clos_state))) (APPEND a env) (APPEND vv env2) 0
        (MAP (\x. (0,x)) [y])`) ASSUME_TAC THENL
    [MATCH_MP_TAC CLOSCALLPAUX_env_rel_APPEND_body THEN
     EXISTS_TAC `[clos_Let x e1' y]` THEN ASM_REWRITE_TAC[clos_fv_def] THEN CONJ_TAC THENL
      [REPEAT STRIP_TAC THEN DISJ2_TAC THEN
       FIRST_ASSUM(fun th -> if is_neg (concl th) && is_binary "<" (rand (concl th))
                             then ASSUME_TAC (REWRITE_RULE[NOT_LT] th) else NO_TAC) THEN
       ASM_SIMP_TAC[SUB_ADD];
       MATCH_MP_TAC (GEN_ALL env_rel_subg) THEN
       MAP_EVERY EXISTS_TAC [`g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`;
                             `clos_state_code (t0:(C,FFI)clos_state)`] THEN
       ASM_REWRITE_TAC[]];
     ALL_TAC])) THEN
  (CLOSCALLPAUX_WITH_EVAL_VALS `e1':clos_exp list` (fun vs' ->
   FIRST_X_ASSUM(MP_TAC o SPECL [`a:clos_v list`; `s1:(abs_calls_state # C,FFI)clos_state`] o
     check (fun th -> let vs,b = strip_forall (concl th) in length vs = 2)) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`g':num_set # (num # num # clos_exp) list`;
     `g:num_set # (num # num # clos_exp) list`; mk_comb(mk_comb(`APPEND:clos_v list -> clos_v list -> clos_v list`, vs'), `env2:clos_v list`);
     `t1:(C,FFI)clos_state`;
     `[y:clos_exp]`; `res:(clos_v list,clos_v)result`;
     `s':(abs_calls_state # C,FFI)clos_state`;
     `set_of_list (code_locs [x2]) DIFF domain (FST (g:num_set # (num # num # clos_exp) list))`;
     `l2:num->bool`; `g2:num_set # (num # num # clos_exp) list`]) THEN
   ASM_REWRITE_TAC[ALL_APPEND])) THEN
  (DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck2:num`; `res2:(clos_v list,clos_v)result`;
     `t2:(C,FFI)clos_state`; `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`]) THEN
   FIRST_ASSUM(MP_TAC o SPEC `ck2:num` o
     MATCH_MP (REWRITE_RULE[IMP_CONJ] CLOSCALLPAUX_evaluate_add_clock_res) o
     check (fun th -> try (let l = lhs (concl th) in
                           fst(dest_const(rator l)) = "clos_evaluate" &&
                           fst (dest_pair (rand l)) = `e1':clos_exp list`)
                      with _ -> false)) THEN
   REWRITE_TAC[distinctness "result"] THEN DISCH_TAC THEN
   MAP_EVERY EXISTS_TAC [`ck1 + ck2:num`; `res2:(clos_v list,clos_v)result`;
     `t2:(C,FFI)clos_state`; `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`] THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[subg_trans; SUBSET_TRANS]));;

let CLOSCALLPAUX_WITH_ASM (p:term->bool) (f:term -> tactic) : tactic = fun (asl,w as gl) ->
  let th = snd(find (fun (_,th) -> try p (concl th) with Failure _ -> false) asl) in
  f (concl th) gl;;

(* case Handle *)
let CLOSCALLPAUX_cc_Handle = prove
 (CLOSCALLPAUX_cc_case 6,
  (REPEAT GEN_TAC THEN REWRITE_TAC[CLOSCALLPAUX_cc_P_def] THEN STRIP_TAC THEN
   REPEAT GEN_TAC THEN
   SUBGOAL_THEN `?r1 s2. clos_evaluate ([x1],env,(s1:(abs_calls_state # C,FFI)clos_state)) =
                         (r1,s2)` STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN ONCE_REWRITE_TAC[clos_call_calls_def] THEN
   ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   REPEAT IL1AUX_PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   CLOSCALLPAUX_ADD_FACTS_TAC (fun th ->
     if CLOSCALLPAUX_is_calls_eq th then MATCH_MP calls_sing th else failwith "") THEN
   REPEAT (FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o check (fun th ->
     is_exists (concl th) && is_eq (snd(dest_exists(concl th))) &&
     is_var (lhs (snd(dest_exists(concl th))))))) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[code_locs_def; every_Fn_SOME_def; every_Fn_vs_NONE_def;
                               LET_DEF; LET_END_DEF; HD]) THEN
   REWRITE_TAC[HD] THEN CLOSCALLPAUX_SPLIT_ASM_TAC THEN
   MP_TAC(ISPECL [`[x1:clos_exp]`; `[x2:clos_exp]`;
                  `g0:num_set # (num # num # clos_exp) list`;
                  `g':num_set # (num # num # clos_exp) list`;
                  `g:num_set # (num # num # clos_exp) list`;
                  `[y:clos_exp]`; `[y':clos_exp]`] CLOSCALLPAUX_calls_chain) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ALL_DISTINCT_APPEND; SET_OF_LIST_APPEND; IMAGE_UNION;
                               DISJOINT_UNION; MEM_APPEND]) THEN
   CLOSCALLPAUX_SPLIT_ASM_TAC) THEN
  (SUBGOAL_THEN `subg (g':num_set # (num # num # clos_exp) list) g1` ASSUME_TAC THENL
    [ASM_MESON_TAC[subg_trans]; ALL_TAC] THEN
   SUBGOAL_THEN `set_of_list (code_locs [x1]) DIFF
                 domain (FST (g':num_set # (num # num # clos_exp) list)) SUBSET l1`
     ASSUME_TAC THENL
    [UNDISCH_TAC `(set_of_list (code_locs [x1]) UNION set_of_list (code_locs [x2])) DIFF
                  domain (FST (g:num_set # (num # num # clos_exp) list)) SUBSET l1` THEN
     REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_SET_OF_LIST] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `code_includes (SND (g':num_set # (num # num # clos_exp) list))
                   (clos_state_code (t0:(C,FFI)clos_state))` ASSUME_TAC THENL
    [ASM_MESON_TAC[code_includes_subg]; ALL_TAC] THEN
   SUBGOAL_THEN `clos_callProof_env_rel (clos_callProof_v_rel g1 l1
                   (clos_state_code (t0:(C,FFI)clos_state))) env env2 0
                   (MAP (\x. (0,x)) [y])` ASSUME_TAC THENL
    [MATCH_MP_TAC CLOSCALLPAUX_env_rel_MAP0_mono THEN
     EXISTS_TAC `[clos_Handle x y y']` THEN ASM_REWRITE_TAC[clos_fv_def] THEN MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
     ASM_MESON_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`g0:num_set # (num # num # clos_exp) list`;
     `g':num_set # (num # num # clos_exp) list`; `env2:clos_v list`; `t0:(C,FFI)clos_state`;
     `[y:clos_exp]`; `r1:(clos_v list,clos_v)result`;
     `s2:(abs_calls_state # C,FFI)clos_state`;
     `set_of_list (code_locs [x1]) DIFF domain (FST (g':num_set # (num # num # clos_exp) list))`;
     `l1:num->bool`; `g1:num_set # (num # num # clos_exp) list`] o
     check (fun th -> let vs,b = strip_forall (concl th) in length vs = 10)) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck1:num`; `res1:(clos_v list,clos_v)result`;
     `t1:(C,FFI)clos_state`; `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`]) THEN
   SUBGOAL_THEN `(?vv. r1 = Rerr (Rraise vv):(clos_v list,clos_v)result) \/
                 (!vv. ~(r1 = Rerr (Rraise vv)))` STRIP_ASSUME_TAC THENL
    [MESON_TAC[];
     (FIRST_X_ASSUM SUBST_ALL_TAC THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[exc_rel_raise1; exc_rel_type_error1]) THEN
   CLOSCALLPAUX_RES_CLEAN_TAC THEN
   SUBGOAL_THEN `clos_state_code (t0:(C,FFI)clos_state) SUBMAP clos_state_code (t1:(C,FFI)clos_state)`
     ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP clos_evaluate_mono o check (fun th ->
       try (let l = lhs (concl th) in fst(dest_const(rator l)) = "clos_evaluate" &&
                fst (dest_pair (rand l)) = `[y:clos_exp]`) with _ -> false)) THEN
     REWRITE_TAC[clos_state_INFO.ri_accfupds];
     ALL_TAC] THEN
   SUBGOAL_THEN `ALL (wfv g2 l2 (clos_state_code (t1:(C,FFI)clos_state))) env` ASSUME_TAC THENL
    [MATCH_MP_TAC (GEN_ALL EVERY_wfv_subg) THEN
     MAP_EVERY EXISTS_TAC [`clos_state_code (t0:(C,FFI)clos_state)`;
                           `g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `subg (g:num_set # (num # num # clos_exp) list) g2` ASSUME_TAC THENL
    [ASM_MESON_TAC[subg_trans]; ALL_TAC] THEN
   SUBGOAL_THEN `set_of_list (code_locs [x2]) DIFF
                 domain (FST (g:num_set # (num # num # clos_exp) list)) SUBSET l2`
     ASSUME_TAC THENL
    [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l1:num->bool` THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `(set_of_list (code_locs [x1]) UNION set_of_list (code_locs [x2])) DIFF
                  domain (FST (g:num_set # (num # num # clos_exp) list)) SUBSET l1` THEN
     SET_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `code_includes (SND (g:num_set # (num # num # clos_exp) list))
                   (clos_state_code (t1:(C,FFI)clos_state))` ASSUME_TAC THENL
    [ASM_MESON_TAC[code_includes_SUBMAP]; ALL_TAC]) THEN
    (RULE_ASSUM_TAC(REWRITE_RULE[exc_rel_raise1; exc_rel_type_error1]) THEN
   CLOSCALLPAUX_RES_CLEAN_TAC) THEN
    (CLOSCALLPAUX_WITH_ASM (fun t -> fst(dest_const(fst(strip_comb t))) = "clos_callProof_v_rel" &&
                                   rand(rator t) = `vv:clos_v`) (fun t ->
   let vv' = rand t in
   SUBGOAL_THEN (subst [vv',`ww:clos_v`]
     `clos_callProof_env_rel (clos_callProof_v_rel g2 l2
        (clos_state_code (t1:(C,FFI)clos_state))) (APPEND [vv] env) (APPEND [ww] env2) 0
        (MAP (\x. (0,x)) [y'])`) (ASSUME_TAC o REWRITE_RULE[APPEND]) THENL
    [MATCH_MP_TAC CLOSCALLPAUX_env_rel_APPEND_body THEN
     EXISTS_TAC `[clos_Handle x y y']` THEN ASM_REWRITE_TAC[clos_fv_def; ALL2; LENGTH] THEN
     CONJ_TAC THENL
      [REPEAT STRIP_TAC THEN DISJ2_TAC THEN
       FIRST_ASSUM(fun th -> if is_neg (concl th) && is_binary "<" (rand (concl th))
                             then ASSUME_TAC (REWRITE_RULE[NOT_LT] th) else NO_TAC) THEN
       ASM_SIMP_TAC[SUB_ADD; ONE];
       MATCH_MP_TAC (GEN_ALL env_rel_subg) THEN
       MAP_EVERY EXISTS_TAC [`g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`;
                             `clos_state_code (t0:(C,FFI)clos_state)`] THEN
       ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`vv:clos_v`; `s2:(abs_calls_state # C,FFI)clos_state`] o
     check (fun th -> let vs,b = strip_forall (concl th) in length vs = 2)) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`g':num_set # (num # num # clos_exp) list`;
     `g:num_set # (num # num # clos_exp) list`; mk_comb(mk_comb(`CONS:clos_v -> clos_v list -> clos_v list`, vv'), `env2:clos_v list`);
     `t1:(C,FFI)clos_state`;
     `[y':clos_exp]`; `res:(clos_v list,clos_v)result`;
     `s:(abs_calls_state # C,FFI)clos_state`;
     `set_of_list (code_locs [x2]) DIFF domain (FST (g:num_set # (num # num # clos_exp) list))`;
     `l2:num->bool`; `g2:num_set # (num # num # clos_exp) list`]) THEN
   ASM_REWRITE_TAC[ALL])) THEN
    (DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck2:num`; `res2:(clos_v list,clos_v)result`;
     `t2:(C,FFI)clos_state`; `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`]) THEN
   FIRST_ASSUM(MP_TAC o SPEC `ck2:num` o
     MATCH_MP (REWRITE_RULE[IMP_CONJ] CLOSCALLPAUX_evaluate_add_clock_res) o
     check (fun th -> try (let l = lhs (concl th) in
                           fst(dest_const(rator l)) = "clos_evaluate" &&
                           fst (dest_pair (rand l)) = `[y:clos_exp]`)
                      with _ -> false)) THEN
   REWRITE_TAC[distinctness "result"; injectivity "result"; distinctness "error_result"] THEN
   DISCH_TAC THEN
   MAP_EVERY EXISTS_TAC [`ck1 + ck2:num`; `res2:(clos_v list,clos_v)result`;
     `t2:(C,FFI)clos_state`; `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`] THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[subg_trans; SUBSET_TRANS]);
     (SUBGOAL_THEN `res:(clos_v list,clos_v)result = r1 /\ (s:(abs_calls_state # C,FFI)clos_state) = s2`
     STRIP_ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
       rhs (concl th) = `res:(clos_v list,clos_v)result,s:(abs_calls_state # C,FFI)clos_state`)) THEN
     CASES_ON `r1:(clos_v list,clos_v)result` THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
      [MESON_TAC[];
       CASES_ON `a:clos_v error_result` THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
        [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall (concl th) &&
           is_neg (snd (dest_forall (concl th))))) THEN
         REWRITE_TAC[injectivity "result"; injectivity "error_result"] THEN MESON_TAC[];
         MESON_TAC[]]];
     ALL_TAC]) THEN
    (RVEQ_TAC THEN
   MAP_EVERY EXISTS_TAC [`ck1:num`; `res1:(clos_v list,clos_v)result`;
     `t1:(C,FFI)clos_state`; `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`] THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
   CASES_ON `r1:(clos_v list,clos_v)result` THEN
   CLOSCALLPAUX_RES_CLEAN_TAC THEN CASE_REWRITE_TAC[]) THEN
    (CASES_ON `a:clos_v error_result` THEN
   RULE_ASSUM_TAC(REWRITE_RULE[exc_rel_raise1; exc_rel_type_error1]) THEN
   CLOSCALLPAUX_RES_CLEAN_TAC THEN CASE_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall (concl th) &&
     is_neg (snd (dest_forall (concl th))))) THEN
   REWRITE_TAC[injectivity "result"; injectivity "error_result"] THEN MESON_TAC[])]));;

let CLOSCALLPAUX_recclosure_rel_Fn = prove
 (`!exp x g0 y new_g y' g' g g1 l1 code n t (body:clos_exp).
     clos_call_calls [exp] (insert_each x 1 g0) = ([y],new_g) /\
     clos_call_calls [exp] g0 = ([y'],g') /\ wfg g0 /\ ~(x IN domain (FST g0)) /\
     every_Fn_SOME [exp] /\ every_Fn_vs_NONE [exp] /\ ALL_DISTINCT (code_locs [exp]) /\
     ~MEM x (code_locs [exp]) /\
     DISJOINT (IMAGE SUC (set_of_list (code_locs [exp]))) (set_of_list (MAP FST (SND g0))) /\
     ~MEM (x + 1) (MAP FST (SND g0)) /\
     g = (if clos_call_closed (Fn t (SOME x) NONE n y)
          then (FST new_g, CONS (x + 1,n,y) (SND new_g)) else g') /\
     body = (if clos_call_closed (Fn t (SOME x) NONE n y)
             then clos_Call backend_common_None 0 (x + 1) (GENLIST_Var backend_common_None 1 n)
             else y') /\
     subg g g1 /\ set_of_list (APPEND (code_locs [exp]) [x]) DIFF domain (FST g) SUBSET l1 /\
     code_includes (SND g) code
     ==> recclosure_rel g1 l1 code x [(n,exp)] [(n,body)]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[recclosure_rel_def] THEN
  EXISTS_TAC `g0:num_set # (num # num # clos_exp) list` THEN
  ASM_REWRITE_TAC[recclosure_wf_def; MAP; LENGTH; GSYM ONE; LISTAUX_list_of_seq_1;
                  set_of_list; LET_DEF; LET_END_DEF; ADD_CLAUSES; MULT_CLAUSES; ZIP_def] THEN
  ASM_REWRITE_TAC[DISJOINT_INSERT; DISJOINT_EMPTY; IN_SET_OF_LIST] THEN
  CASE_REWRITE_TAC[ALL2; closed_Fn] THEN REWRITE_TAC[ZIP_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[closed_Fn]) THEN
  SUBGOAL_THEN `clos_call_code_list x [n,y] (new_g:num_set # (num # num # clos_exp) list) =
                (FST new_g, CONS (x + 1,n,y) (SND new_g))` (fun th -> REWRITE_TAC[th]) THENL
   [STRUCT_CASES_TAC(ISPEC `new_g:num_set # (num # num # clos_exp) list` PAIR_SURJECTIVE) THEN
    REWRITE_TAC[clos_call_code_list_def; FST; SND];
    ALL_TAC] THEN
  COND_CASES_TAC THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SET_OF_LIST_APPEND; set_of_list; FST; SND]) THEN
  ASM_REWRITE_TAC[calls_list_def; CONS_11; PAIR_EQ] THENL
   [CONJ_TAC THENL [EXISTS_TAC `backend_common_None` THEN REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(set_of_list (code_locs [exp]) UNION {x}) DIFF
                 domain (FST (new_g:num_set # (num # num # clos_exp) list)) SUBSET l1` THEN
    SET_TAC[];
    SUBGOAL_THEN `~(x IN domain (FST (g':num_set # (num # num # clos_exp) list)))` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`[exp:clos_exp]`; `g0:num_set # (num # num # clos_exp) list`;
                     `[y':clos_exp]`; `g':num_set # (num # num # clos_exp) list`]
                    calls_domain_locs) THEN
      ASM_REWRITE_TAC[SUBSET; IN_UNION; IN_SET_OF_LIST] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(set_of_list (code_locs [exp]) UNION {x}) DIFF
                 domain (FST (g':num_set # (num # num # clos_exp) list)) SUBSET l1` THEN
    ASM SET_TAC[]]);;
let CLOSCALLPAUX_env_rel_Fn = prove
 (`!(R:clos_v->clos_v->bool) e1 e2 t loc vs n body.
     clos_callProof_env_rel R e1 e2 0 (MAP (\x. (0,x)) [Fn t loc vs n body]) <=>
     clos_callProof_env_rel R e1 e2 0 [(n,body)]`,
  REWRITE_TAC[clos_callProof_env_rel_def; MAP; EX] THEN CASE_REWRITE_TAC[fv1_thm] THEN
  REWRITE_TAC[ADD_CLAUSES; ADD_AC]);;

(* case Fn *)
let CLOSCALLPAUX_cc_Fn = prove
 (CLOSCALLPAUX_cc_case 8,
  (REPEAT GEN_TAC THEN REWRITE_TAC[CLOSCALLPAUX_cc_P_def] THEN REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN ONCE_REWRITE_TAC[clos_call_calls_def] THEN
   REWRITE_TAC[every_Fn_SOME_def; every_Fn_vs_NONE_def; IS_SOME_EXISTS] THEN
   STRIP_TAC THEN RVEQ_TAC THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[LET_DEF; LET_END_DEF]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[code_locs_def; LET_DEF; LET_END_DEF]) THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[])) THEN
  (RULE_ASSUM_TAC(REWRITE_RULE[IS_NONE_EQ_NONE]) THEN RVEQ_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     rhs (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
   CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
    [ALL_TAC; ASM_MESON_TAC[]] THEN
   STRIP_TAC THEN RVEQ_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     rhs (concl th) = `ys:clos_exp list,g:num_set # (num # num # clos_exp) list`)) THEN
   REPEAT IL1AUX_PAIRARG_TAC THEN
   CLOSCALLPAUX_ADD_FACTS_TAC (fun th ->
     if CLOSCALLPAUX_is_calls_eq th then MATCH_MP calls_sing th else failwith "") THEN
   REPEAT (FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o check (fun th ->
     is_exists (concl th) && is_eq (snd(dest_exists(concl th))) &&
     is_var (lhs (snd(dest_exists(concl th))))))) THEN
   REWRITE_TAC[HD]) THEN
  (SUBGOAL_THEN `~(x' IN domain (FST (g0:num_set # (num # num # clos_exp) list))) /\
                 ~MEM x' (code_locs [exp]) /\ ALL_DISTINCT (code_locs [exp]) /\
                 DISJOINT (IMAGE SUC (set_of_list (code_locs [exp])))
                          (set_of_list (MAP FST (SND g0))) /\
                 ~MEM (x' + 1) (MAP FST (SND g0))` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `wfg (g0:num_set # (num # num # clos_exp) list)` THEN
     UNDISCH_TAC `ALL_DISTINCT (APPEND (code_locs [exp]) [x'])` THEN
     UNDISCH_TAC `DISJOINT (IMAGE SUC (set_of_list (APPEND (code_locs [exp]) [x'])))
                    (set_of_list (MAP FST (SND (g0:num_set # (num # num # clos_exp) list))))` THEN
     REWRITE_TAC[wfg_def; ALL_DISTINCT_APPEND; SET_OF_LIST_APPEND; set_of_list; MEM;
                 IMAGE_UNION; IMAGE_CLAUSES; DISJOINT_UNION; DISJOINT_INSERT; DISJOINT_EMPTY;
                 GSYM ADD1; IN_SET_OF_LIST] THEN
     STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL
      [UNDISCH_TAC `~MEM (SUC x') (MAP FST (SND (g0:num_set # (num # num # clos_exp) list)))` THEN
       REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN
       ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE; SUC_INJ] THEN MESON_TAC[];
       ASM_MESON_TAC[]];
     ALL_TAC]) THEN
  (DISCH_TAC THEN
   ABBREV_TAC `body = if clos_call_closed (Fn x (SOME x') NONE num_args y)
                      then clos_Call backend_common_None 0 (x' + 1)
                             (GENLIST_Var backend_common_None 1 num_args)
                      else y'` THEN
   SUBGOAL_THEN `ys = [Fn x (SOME x') NONE num_args body] /\
                 (g:num_set # (num # num # clos_exp) list) =
                   (if clos_call_closed (Fn x (SOME x') NONE num_args y)
                    then (FST new_g', CONS (x' + 1,num_args,y) (SND new_g')) else g')`
     STRIP_ASSUME_TAC THENL
    [EXPAND_TAC "body" THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
       rhs (concl th) = `ys:clos_exp list,g:num_set # (num # num # clos_exp) list`)) THEN
     COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`exp:clos_exp`; `x':num`; `g0:num_set # (num # num # clos_exp) list`;
     `y:clos_exp`; `new_g':num_set # (num # num # clos_exp) list`; `y':clos_exp`;
     `g':num_set # (num # num # clos_exp) list`; `g:num_set # (num # num # clos_exp) list`;
     `g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`;
     `clos_state_code (t0:(C,FFI)clos_state)`; `num_args:num`; `x:mlstring`; `body:clos_exp`]
     CLOSCALLPAUX_recclosure_rel_Fn) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "body" THEN REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_TAC) THEN
  (MAP_EVERY EXISTS_TAC [`0`;
     `Rval [clos_Closure (SOME x') [] env2 num_args body]:(clos_v list,clos_v)result`;
     `t0:(C,FFI)clos_state`; `g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`] THEN
   ASM_REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock; SUBSET_REFL] THEN
   ASM_SIMP_TAC[wfg_subg_refl] THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN CASE_REWRITE_TAC[] THEN
   FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP clos_callProof_state_rel_max_app) THEN
   ASM_REWRITE_TAC[every_result_def; result_rel_def; ALL; ALL2; wfv_def] THEN
   CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   ONCE_REWRITE_TAC[clos_callProof_v_rel_def] THEN
   MAP_EVERY EXISTS_TAC [`x':num`; `[]:clos_v list`; `env2:clos_v list`; `body:clos_exp`] THEN
   ASM_REWRITE_TAC[ALL2] THEN
   UNDISCH_TAC `clos_callProof_env_rel (clos_callProof_v_rel g1 l1
     (clos_state_code (t0:(C,FFI)clos_state))) env env2 0 (MAP (\x. 0,x) ys)` THEN
   ASM_REWRITE_TAC[CLOSCALLPAUX_env_rel_Fn]));;

(* the code table state after the functions of a Letrec whose bodies are closed *)
let CLOSCALLPAUX_wfg_Letrec_closed = prove
 (`!fns x (g0:num_set # (num # num # clos_exp) list) fns1 new_g.
     clos_call_calls (MAP SND fns) (insert_each x (LENGTH fns) g0) = (fns1,new_g) /\
     wfg g0 /\ ALL_DISTINCT (code_locs (MAP SND fns)) /\ every_Fn_SOME (MAP SND fns) /\
     DISJOINT (IMAGE SUC (set_of_list (code_locs (MAP SND fns))))
              (set_of_list (MAP FST (SND g0))) /\
     (!i. i < LENGTH fns ==> ~MEM (2 * i + x) (code_locs (MAP SND fns)) /\
                             ~MEM (2 * i + x + 1) (MAP FST (SND g0)))
     ==> wfg (clos_call_code_list x (ZIP (MAP FST fns) fns1) new_g)`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP calls_length) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN
   SUBGOAL_THEN `wfg' (new_g:num_set # (num # num # clos_exp) list)` ASSUME_TAC THENL
    [MATCH_MP_TAC calls_wfg' THEN
     MAP_EVERY EXISTS_TAC [`MAP SND (fns:(num # clos_exp) list)`;
       `insert_each x (LENGTH (fns:(num # clos_exp) list)) (g0:num_set # (num # num # clos_exp) list)`;
       `fns1:clos_exp list`] THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC wfg'_insert_each THEN
     UNDISCH_TAC `wfg (g0:num_set # (num # num # clos_exp) list)` THEN
     SIMP_TAC[wfg_def; wfg'_def; SUBSET_REFL];
     ALL_TAC] THEN
   SUBGOAL_THEN `domain (FST (insert_each x (LENGTH (fns:(num # clos_exp) list))
                    (g0:num_set # (num # num # clos_exp) list))) SUBSET
                 domain (FST (new_g:num_set # (num # num # clos_exp) list))` ASSUME_TAC THENL
    [ASM_MESON_TAC[calls_subspt; subspt_domain]; ALL_TAC] THEN
   SUBGOAL_THEN `ALL_DISTINCT (MAP FST (SND (new_g:num_set # (num # num # clos_exp) list)))`
     ASSUME_TAC THENL
    [MATCH_MP_TAC calls_ALL_DISTINCT THEN
     MAP_EVERY EXISTS_TAC [`MAP SND (fns:(num # clos_exp) list)`;
       `insert_each x (LENGTH (fns:(num # clos_exp) list)) (g0:num_set # (num # num # clos_exp) list)`;
       `fns1:clos_exp list`] THEN
     ASM_REWRITE_TAC[SND_insert_each] THEN ASM_MESON_TAC[wfg_def];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`MAP SND (fns:(num # clos_exp) list)`;
       `insert_each x (LENGTH (fns:(num # clos_exp) list)) (g0:num_set # (num # num # clos_exp) list)`;
       `fns1:clos_exp list`; `new_g:num_set # (num # num # clos_exp) list`]
     calls_add_SUC_code_locs) THEN
   MP_TAC(ISPECL [`MAP SND (fns:(num # clos_exp) list)`;
       `insert_each x (LENGTH (fns:(num # clos_exp) list)) (g0:num_set # (num # num # clos_exp) list)`;
       `fns1:clos_exp list`; `new_g:num_set # (num # num # clos_exp) list`]
     calls_domain) THEN
   MP_TAC(ISPECL [`MAP SND (fns:(num # clos_exp) list)`;
       `insert_each x (LENGTH (fns:(num # clos_exp) list)) (g0:num_set # (num # num # clos_exp) list)`;
       `fns1:clos_exp list`; `new_g:num_set # (num # num # clos_exp) list`]
     calls_IS_SUFFIX) THEN
   ASM_REWRITE_TAC[SND_insert_each; domain_FST_insert_each] THEN
   REPEAT DISCH_TAC) THEN
  (SUBGOAL_THEN `wfg' (clos_call_code_list x (ZIP (MAP FST (fns:(num # clos_exp) list)) fns1)
                        (new_g:num_set # (num # num # clos_exp) list))` MP_TAC THENL
    [MATCH_MP_TAC wfg'_code_list THEN ASM_REWRITE_TAC[LISTAUX_LENGTH_ZIP; LENGTH_MAP] THEN
     UNDISCH_TAC `domain (FST (insert_each x (LENGTH (fns:(num # clos_exp) list))
                    (g0:num_set # (num # num # clos_exp) list))) SUBSET
                  domain (FST (new_g:num_set # (num # num # clos_exp) list))` THEN
     REWRITE_TAC[domain_FST_insert_each] THEN
     REWRITE_TAC[SUBSET; IN_UNION; IN_SET_OF_LIST; MEM_GENLIST] THEN
     MESON_TAC[ARITH_RULE `x + 2 * m = 2 * m + x`];
     ALL_TAC] THEN
   REWRITE_TAC[wfg_def; wfg'_def; FST_code_list; MAP_FST_code_list; LISTAUX_LENGTH_ZIP;
               LENGTH_MAP] THEN
   DISCH_TAC THEN
   UNDISCH_TAC `wfg (g0:num_set # (num # num # clos_exp) list)` THEN
   UNDISCH_TAC `wfg' (new_g:num_set # (num # num # clos_exp) list)` THEN
   REWRITE_TAC[wfg_def; wfg'_def] THEN REPEAT STRIP_TAC THENL
    [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `d:num` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `d:num` o REWRITE_RULE[SUBSET] o check (fun th ->
       is_binary "SUBSET" (concl th) && can (find_term ((=) `PRE`)) (concl th))) THEN
     ASM_REWRITE_TAC[IN_UNION; IN_IMAGE; IN_SET_OF_LIST; MEM_GENLIST; MAP_APPEND; MEM_APPEND;
                     MEM_REVERSE] THEN
     STRIP_TAC THENL
      [(DISJ1_TAC THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);
       (DISJ2_TAC THEN
   UNDISCH_TAC `IS_SUFFIX (SND (new_g:num_set # (num # num # clos_exp) list))
                  (SND (g0:num_set # (num # num # clos_exp) list))` THEN
   REWRITE_TAC[IS_SUFFIX_APPEND] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[MAP_APPEND; MEM_APPEND] THEN DISJ2_TAC THEN
   REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]);
       (DISJ2_TAC THEN
   FIRST_ASSUM(MP_TAC o SPEC `x':num` o REWRITE_RULE[SUBSET] o check (fun th ->
     is_binary "SUBSET" (concl th) && can (find_term ((=) `SUC`)) (concl th) &&
     can (find_term ((=) `new_g:num_set # (num # num # clos_exp) list`)) (concl th) &&
     not (can (find_term ((=) `x:num`)) (concl th)))) THEN
   ASM_REWRITE_TAC[IN_SET_OF_LIST; IN_IMAGE] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[PRE] THEN ASM_MESON_TAC[])];
     (ASM_REWRITE_TAC[ALL_DISTINCT_APPEND; ALL_DISTINCT_REVERSE; ALL_DISTINCT_GENLIST; MEM_REVERSE;
                   MEM_GENLIST] THEN
   CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
   X_GEN_TAC `e:num` THEN DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC)) THEN (DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `e:num` o REWRITE_RULE[SUBSET] o check (fun th ->
     is_binary "SUBSET" (concl th) && can (find_term ((=) `code_locs`)) (concl th))) THEN
   ASM_REWRITE_TAC[IN_UNION; IN_SET_OF_LIST; IN_IMAGE] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (is_forall o concl)) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `x + m * 2 + 1 = 2 * m + x + 1` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[]) THEN (REWRITE_TAC[ARITH_RULE `2 * m + x + 1 = SUC y <=> y = 2 * m + x`; UNWIND_THM2] THEN
   ASM_REWRITE_TAC[])]));;
let CLOSCALLPAUX_recclosure_rel_Letrec = prove
 (CASE_TERM
  `!fns x (g0:num_set # (num # num # clos_exp) list) fns1 new_g fns1' g3 g1 l1 code
      (fns4:(num # clos_exp) list).
     clos_call_calls (MAP SND fns) (insert_each x (LENGTH fns) g0) = (fns1,new_g) /\
     clos_call_calls (MAP SND fns) g0 = (fns1',g3) /\
     wfg g0 /\ every_Fn_SOME (MAP SND fns) /\ every_Fn_vs_NONE (MAP SND fns) /\
     ALL_DISTINCT (code_locs (MAP SND fns)) /\
     DISJOINT (IMAGE SUC (set_of_list (code_locs (MAP SND fns))))
              (set_of_list (MAP FST (SND g0))) /\
     (!i. i < LENGTH fns ==> ~MEM (2 * i + x) (code_locs (MAP SND fns)) /\
                             ~MEM (2 * i + x + 1) (MAP FST (SND g0))) /\
     (ALL2 (\np p. match np with (n,y) -> clos_call_closed (Fn (implode "") NONE NONE n p))
           fns fns1
      ==> fns4 = calls_list backend_common_None 1 x fns /\
          subg (clos_call_code_list x (ZIP (MAP FST fns) fns1) new_g) g1 /\
          set_of_list (code_locs (MAP SND fns)) DIFF domain (FST new_g) SUBSET l1 /\
          code_includes (SND (clos_call_code_list x (ZIP (MAP FST fns) fns1) new_g)) code) /\
     (~ALL2 (\np p. match np with (n,y) -> clos_call_closed (Fn (implode "") NONE NONE n p))
            fns fns1
      ==> fns4 = ZIP (MAP FST fns) fns1' /\ subg g3 g1 /\
          set_of_list (code_locs (MAP SND fns)) DIFF domain (FST g3) SUBSET l1 /\
          set_of_list (list_of_seq (\i. 2 * i + x) (LENGTH fns)) SUBSET l1 /\
          code_includes (SND g3) code)
     ==> recclosure_rel g1 l1 code x fns fns4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[recclosure_rel_def] THEN
  EXISTS_TAC `g0:num_set # (num # num # clos_exp) list` THEN
  ASM_REWRITE_TAC[recclosure_wf_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN (CASE_TERM
    `ALL2 (\np p. match np with (n,y) -> clos_call_closed (Fn (implode "") NONE NONE n p))
          (fns:(num # clos_exp) list) fns1 <=>
     ALL2 (\np p. match np with (n,y) -> !v. has_var v (SND (clos_call_free [p])) ==> v < n)
          fns fns1`) (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    REPEAT GEN_TAC THEN CASE_REWRITE_TAC[closed_Fn];
    ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_SET_OF_LIST; MEM_GENLIST; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM; LEFT_AND_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    FIRST_ASSUM(MP_TAC o check (is_forall o concl)) THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM; LEFT_AND_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    FIRST_ASSUM(MP_TAC o check (is_forall o concl)) THEN MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) && not (is_neg (lhand (concl th))))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`backend_common_None`; `1`] THEN REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) && is_neg (lhand (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;
let CLOSCALLPAUX_env_rel_Letrec_fns = prove
 (`!(R:clos_v->clos_v->bool) e1 e2 t loc vs fns b.
     clos_callProof_env_rel R e1 e2 0 (MAP (\x. (0,x)) [clos_Letrec t loc vs fns b])
     ==> clos_callProof_env_rel R e1 e2 (LENGTH fns) fns`,
  REWRITE_TAC[clos_callProof_env_rel_def; MAP; EX] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN CASE_REWRITE_TAC[fv1_thm] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN DISJ1_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[EXISTS_MEM; EXISTS_PAIR_THM] THEN
  CASE_REWRITE_TAC[fv1_intro] THEN REWRITE_TAC[ADD_AC]);;

let CLOSCALLPAUX_ALL_FST = prove
 (CASE_TERM
  `!(P:A->bool) (l:(A # B) list).
     ALL (\p. match p with (n,e) -> P n) l <=> ALL P (MAP FST l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; MAP] THEN
  SPEC_TAC(`h:A # B`,`h:A # B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CASE_REWRITE_TAC[FST]);;

(* case Letrec *)
let CLOSCALLPAUX_cc_Letrec = prove
 (CLOSCALLPAUX_cc_case 9,
  (REPEAT GEN_TAC THEN REWRITE_TAC[CLOSCALLPAUX_cc_P_def] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN ONCE_REWRITE_TAC[clos_call_calls_def] THEN
   REWRITE_TAC[every_Fn_SOME_def; every_Fn_vs_NONE_def; IS_SOME_EXISTS; IS_NONE_EQ_NONE] THEN
   STRIP_TAC THEN RVEQ_TAC THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[LET_DEF; LET_END_DEF]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[code_locs_def; LET_DEF; LET_END_DEF]) THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[])) THEN
  (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     rhs (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
   COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
   DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `list_of_seq (clos_Recclosure (SOME x') [] env fns) (LENGTH fns)` o
     check (is_forall o concl)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ALL_DISTINCT_APPEND; SET_OF_LIST_APPEND; IMAGE_UNION;
                               DISJOINT_UNION; MEM_APPEND]) THEN
   CLOSCALLPAUX_SPLIT_ASM_TAC) THEN
  (SUBGOAL_THEN `!i. i < LENGTH (fns:(num # clos_exp) list) ==>
                   ~MEM (2 * i + x') (code_locs (MAP SND fns)) /\
                   ~MEM (2 * i + x' + 1) (MAP FST (SND (g0:num_set # (num # num # clos_exp) list))) /\
                   ~MEM (2 * i + x') (code_locs [exp]) /\
                   ~((2 * i + x') IN domain (FST g0))` ASSUME_TAC THENL
    [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     SUBGOAL_THEN `MEM (2 * i + x') (list_of_seq (\n. x' + 2 * n) (LENGTH (fns:(num # clos_exp) list)))`
       ASSUME_TAC THENL
      [REWRITE_TAC[MEM_GENLIST] THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
       ALL_TAC] THEN
     UNDISCH_TAC `wfg (g0:num_set # (num # num # clos_exp) list)` THEN
     REWRITE_TAC[wfg_def] THEN STRIP_TAC THEN
     UNDISCH_TAC `DISJOINT (IMAGE SUC (set_of_list (list_of_seq (\n. x' + 2 * n)
                    (LENGTH (fns:(num # clos_exp) list)))))
                  (set_of_list (MAP FST (SND (g0:num_set # (num # num # clos_exp) list))))` THEN
     REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_SET_OF_LIST] THEN
     DISCH_THEN(MP_TAC o SPEC `2 * i + x' + 1`) THEN
     SUBGOAL_THEN `2 * i + x' + 1 = SUC (2 * i + x')` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[SUC_INJ; UNWIND_THM1] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
     ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
      [ASM_MESON_TAC[];
       ASM_MESON_TAC[];
       UNDISCH_TAC `~MEM (SUC (2 * i + x')) (MAP FST (SND (g0:num_set # (num # num # clos_exp) list)))` THEN
       REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[IN_IMAGE; SUC_INJ] THEN MESON_TAC[]];
     ALL_TAC]) THEN
  (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     rhs (concl th) = `ys:clos_exp list,g:num_set # (num # num # clos_exp) list`)) THEN
   REPEAT IL1AUX_PAIRARG_TAC THEN
   CLOSCALLPAUX_ADD_FACTS_TAC (fun th ->
     if CLOSCALLPAUX_is_calls_eq th then MATCH_MP calls_sing th else failwith "") THEN
   REPEAT (FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o check (fun th ->
     is_exists (concl th) && is_eq (snd(dest_exists(concl th))) &&
     is_var (lhs (snd(dest_exists(concl th))))))) THEN
   REWRITE_TAC[HD]) THEN
  (DISCH_TAC THEN
   SUBGOAL_THEN `?g0' bb fns4. ys = [clos_Letrec x (SOME x') NONE fns4 bb] /\
                   clos_call_calls [exp] g0' = ([bb],g) /\ wfg g0' /\
                   DISJOINT (IMAGE SUC (set_of_list (code_locs [exp])))
                            (set_of_list (MAP FST (SND (g0':num_set # (num # num # clos_exp) list)))) /\
                   recclosure_rel g1 l1 (clos_state_code (t0:(C,FFI)clos_state)) x' fns fns4`
     STRIP_ASSUME_TAC THENL
    [(CLOSCALLPAUX_WITH_ASM (fun t -> is_eq t &&
     rhs t = `ys:clos_exp list,g:num_set # (num # num # clos_exp) list`) (fun t ->
   let b,_ = dest_cond (lhs t) in ASM_CASES_TAC b) THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     rhs (concl th) = `ys:clos_exp list,g:num_set # (num # num # clos_exp) list`)) THEN
   ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC) THENL
      [(MAP_EVERY EXISTS_TAC [`clos_call_code_list x' (ZIP (MAP FST (fns:(num # clos_exp) list)) fns1')
                           (new_g':num_set # (num # num # clos_exp) list)`;
                         `y:clos_exp`; `calls_list backend_common_None 1 x' (fns:(num # clos_exp) list)`] THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `wfg (clos_call_code_list x' (ZIP (MAP FST (fns:(num # clos_exp) list)) fns1')
                       (new_g':num_set # (num # num # clos_exp) list))` ASSUME_TAC THENL
    [MATCH_MP_TAC CLOSCALLPAUX_wfg_Letrec_closed THEN
     EXISTS_TAC `g0:num_set # (num # num # clos_exp) list` THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `DISJOINT (IMAGE SUC (set_of_list (code_locs [exp])))
                   (set_of_list (MAP FST (SND (clos_call_code_list x'
                      (ZIP (MAP FST (fns:(num # clos_exp) list)) fns1')
                      (new_g':num_set # (num # num # clos_exp) list)))))` ASSUME_TAC THENL
    [MP_TAC(ISPECL [`MAP SND (fns:(num # clos_exp) list)`;
       `insert_each x' (LENGTH (fns:(num # clos_exp) list)) (g0:num_set # (num # num # clos_exp) list)`;
       `fns1':clos_exp list`; `new_g':num_set # (num # num # clos_exp) list`]
       calls_add_SUC_code_locs) THEN
     FIRST_ASSUM(ASSUME_TAC o MATCH_MP calls_length o check (fun th ->
       CLOSCALLPAUX_is_calls_eq th && can (find_term ((=) `insert_each:num->num->num_set # (num # num # clos_exp) list -> num_set # (num # num # clos_exp) list`)) (concl th))) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN
     ASM_REWRITE_TAC[SND_insert_each; MAP_FST_code_list; LISTAUX_LENGTH_ZIP; LENGTH_MAP] THEN
     REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_SET_OF_LIST;
                 MEM_APPEND; MEM_REVERSE; MEM_GENLIST; IN_UNION] THEN
     DISCH_TAC THEN X_GEN_TAC `k:num` THEN
     REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`] THEN
     DISCH_THEN(X_CHOOSE_THEN `c:num` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
     REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM] THEN CONJ_TAC THENL
      [X_GEN_TAC `i:num` THEN REWRITE_TAC[TAUT `~p \/ ~q <=> p ==> ~q`] THEN
       DISCH_TAC THEN DISCH_TAC THEN
       SUBGOAL_THEN `c = 2 * i + x'` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
       FIRST_ASSUM(fun th -> if is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "i"
                             then MP_TAC (SPEC `i:num` th) else NO_TAC) THEN
       REWRITE_TAC[ASSUME `i < LENGTH (fns:(num # clos_exp) list)`;
                   ASSUME `MEM (2 * i + x') (code_locs [exp])`];
       DISCH_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `SUC c` o check (fun th -> is_forall (concl th) &&
         can (find_term ((=) `MAP FST (SND (new_g':num_set # (num # num # clos_exp) list))`)) (concl th))) THEN
       ASM_REWRITE_TAC[SUC_INJ; UNWIND_THM2] THEN
       REWRITE_TAC[UNWIND_THM1; DE_MORGAN_THM] THEN CONJ_TAC THENL
        [UNDISCH_TAC `DISJOINT (IMAGE SUC (set_of_list (code_locs [exp])))
                       (set_of_list (MAP FST (SND (g0:num_set # (num # num # clos_exp) list))))` THEN
         REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_SET_OF_LIST] THEN
         DISCH_THEN(MP_TAC o SPEC `SUC c`) THEN
         REWRITE_TAC[SUC_INJ; UNWIND_THM1; UNWIND_THM2] THEN
         REWRITE_TAC[ASSUME `MEM (c:num) (code_locs [exp])`];
         FIRST_ASSUM(MP_TAC o SPEC `c:num` o check (fun th -> is_forall (concl th) &&
           can (find_term ((=) `code_locs [exp]`)) (concl th) &&
           can (find_term ((=) `list_of_seq (\n. x' + 2 * n) (LENGTH (fns:(num # clos_exp) list))`)) (concl th))) THEN
         REWRITE_TAC[ASSUME `MEM (c:num) (code_locs [exp])`] THEN MESON_TAC[]]];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[]) THEN
    (SUBGOAL_THEN `subg (clos_call_code_list x' (ZIP (MAP FST (fns:(num # clos_exp) list)) fns1')
                        (new_g':num_set # (num # num # clos_exp) list)) g` ASSUME_TAC THENL
    [MATCH_MP_TAC calls_subg THEN
     MAP_EVERY EXISTS_TAC [`[exp:clos_exp]`; `[y:clos_exp]`] THEN ASM_MESON_TAC[wfg_def];
     ALL_TAC] THEN
   MATCH_MP_TAC CLOSCALLPAUX_recclosure_rel_Letrec THEN
   MAP_EVERY EXISTS_TAC [`g0:num_set # (num # num # clos_exp) list`; `fns1':clos_exp list`;
     `new_g':num_set # (num # num # clos_exp) list`; `fns1'':clos_exp list`;
     `g'':num_set # (num # num # clos_exp) list`] THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [ASM_MESON_TAC[];
     ASM_MESON_TAC[subg_trans];
     MP_TAC(ISPECL [`[exp:clos_exp]`;
       `clos_call_code_list x' (ZIP (MAP FST (fns:(num # clos_exp) list)) fns1')
          (new_g':num_set # (num # num # clos_exp) list)`;
       `[y:clos_exp]`; `g:num_set # (num # num # clos_exp) list`] calls_domain_locs) THEN
     ASM_REWRITE_TAC[FST_code_list] THEN
     UNDISCH_TAC `((set_of_list (code_locs (MAP SND (fns:(num # clos_exp) list))) UNION
                    set_of_list (list_of_seq (\n. x' + 2 * n) (LENGTH fns))) UNION
                   set_of_list (code_locs [exp])) DIFF
                  domain (FST (g:num_set # (num # num # clos_exp) list)) SUBSET l1` THEN
     REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_SET_OF_LIST] THEN
     REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[];
     ASM_MESON_TAC[code_includes_subg]]);
       (MP_TAC(ISPECL [`MAP SND (fns:(num # clos_exp) list)`; `[exp:clos_exp]`;
                  `g0:num_set # (num # num # clos_exp) list`;
                  `g'':num_set # (num # num # clos_exp) list`;
                  `g:num_set # (num # num # clos_exp) list`;
                  `fns1'':clos_exp list`; `[y':clos_exp]`] CLOSCALLPAUX_calls_chain) THEN
   ASM_REWRITE_TAC[ALL_DISTINCT_APPEND; SET_OF_LIST_APPEND; IMAGE_UNION; DISJOINT_UNION] THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
   MAP_EVERY EXISTS_TAC [`g'':num_set # (num # num # clos_exp) list`; `y':clos_exp`;
                         `ZIP (MAP FST (fns:(num # clos_exp) list)) (fns1'':clos_exp list)`] THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC CLOSCALLPAUX_recclosure_rel_Letrec THEN
   MAP_EVERY EXISTS_TAC [`g0:num_set # (num # num # clos_exp) list`; `fns1':clos_exp list`;
     `new_g':num_set # (num # num # clos_exp) list`; `fns1'':clos_exp list`;
     `g'':num_set # (num # num # clos_exp) list`] THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [ASM_MESON_TAC[];
     ASM_MESON_TAC[subg_trans];
     UNDISCH_TAC `((set_of_list (code_locs (MAP SND (fns:(num # clos_exp) list))) UNION
                    set_of_list (list_of_seq (\n. x' + 2 * n) (LENGTH fns))) UNION
                   set_of_list (code_locs [exp])) DIFF
                  domain (FST (g:num_set # (num # num # clos_exp) list)) SUBSET l1` THEN
     REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_SET_OF_LIST] THEN
     REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
     (REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_GENLIST] THEN X_GEN_TAC `k:num` THEN
   DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
   FIRST_ASSUM(fun th -> if is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "i"
                         then MP_TAC (SPEC `i:num` th) else NO_TAC) THEN
   REWRITE_TAC[ASSUME `i < LENGTH (fns:(num # clos_exp) list)`] THEN STRIP_TAC THEN
   MP_TAC(ISPECL [`[exp:clos_exp]`; `g'':num_set # (num # num # clos_exp) list`;
                  `[y':clos_exp]`; `g:num_set # (num # num # clos_exp) list`] calls_domain_locs) THEN
   MP_TAC(ISPECL [`MAP SND (fns:(num # clos_exp) list)`; `g0:num_set # (num # num # clos_exp) list`;
                  `fns1'':clos_exp list`; `g'':num_set # (num # num # clos_exp) list`]
                 calls_domain_locs) THEN
   ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `((set_of_list (code_locs (MAP SND (fns:(num # clos_exp) list))) UNION
                  set_of_list (list_of_seq (\n. x' + 2 * n) (LENGTH fns))) UNION
                 set_of_list (code_locs [exp])) DIFF
                domain (FST (g:num_set # (num # num # clos_exp) list)) SUBSET l1` THEN
   REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_SET_OF_LIST; MEM_GENLIST] THEN
   REPEAT DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
    [DISJ1_TAC THEN DISJ2_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
     ASM_MESON_TAC[]]);
     ASM_MESON_TAC[code_includes_subg]])];
     (RVEQ_TAC THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSCALLPAUX_recclosure_rel_MAP_FST) THEN
   SUBGOAL_THEN `LENGTH (fns4:(num # clos_exp) list) = LENGTH (fns:(num # clos_exp) list)`
     ASSUME_TAC THENL [ASM_MESON_TAC[LENGTH_MAP]; ALL_TAC] THEN
   SUBGOAL_THEN `clos_callProof_env_rel (clos_callProof_v_rel g1 l1
                   (clos_state_code (t0:(C,FFI)clos_state)))
                   (APPEND (list_of_seq (clos_Recclosure (SOME x') [] env fns) (LENGTH fns)) env)
                   (APPEND (list_of_seq (clos_Recclosure (SOME x') [] env2 fns4) (LENGTH fns4)) env2)
                   0 (MAP (\x. (0,x)) [bb])` ASSUME_TAC THENL
    [MATCH_MP_TAC CLOSCALLPAUX_env_rel_APPEND_body THEN
     EXISTS_TAC `[clos_Letrec x (SOME x') NONE fns4 bb]` THEN
     ASM_REWRITE_TAC[LIST_REL_GENLIST; LENGTH_LIST_OF_SEQ] THEN REPEAT CONJ_TAC THENL
      [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[clos_callProof_v_rel_def] THEN
       MAP_EVERY EXISTS_TAC [`x':num`; `[]:clos_v list`; `env2:clos_v list`;
                             `fns4:(num # clos_exp) list`] THEN
       ASM_REWRITE_TAC[ALL2] THEN
       MP_TAC(ISPECL [`clos_callProof_v_rel g1 l1 (clos_state_code (t0:(C,FFI)clos_state))`;
         `env:clos_v list`; `env2:clos_v list`; `x:mlstring list`; `SOME (x':num)`;
         `NONE:(num list)option`; `fns4:(num # clos_exp) list`; `bb:clos_exp`]
         CLOSCALLPAUX_env_rel_Letrec_fns) THEN
       ASM_REWRITE_TAC[];
       REWRITE_TAC[clos_fv_def] THEN REPEAT STRIP_TAC THEN DISJ2_TAC THEN
       FIRST_ASSUM(fun th -> if is_neg (concl th) && is_binary "<" (rand (concl th))
                             then ASSUME_TAC (REWRITE_RULE[NOT_LT] th) else NO_TAC) THEN
       ASM_SIMP_TAC[SUB_ADD]];
     ALL_TAC]) THEN
    (FIRST_X_ASSUM(MP_TAC o SPECL [`g0':num_set # (num # num # clos_exp) list`;
     `g:num_set # (num # num # clos_exp) list`;
     `APPEND (list_of_seq (clos_Recclosure (SOME x') [] env2 fns4) (LENGTH (fns4:(num # clos_exp) list))) env2`;
     `t0:(C,FFI)clos_state`; `[bb:clos_exp]`; `res:(clos_v list,clos_v)result`;
     `s':(abs_calls_state # C,FFI)clos_state`;
     `set_of_list (code_locs [exp]) DIFF domain (FST (g:num_set # (num # num # clos_exp) list))`;
     `l1:num->bool`; `g1:num_set # (num # num # clos_exp) list`] o
     check (fun th -> let vs,b = strip_forall (concl th) in length vs = 10)) THEN
   ASM_REWRITE_TAC[ALL_APPEND; EVERY_GENLIST; wfv_def; ALL] THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL
      [REPEAT STRIP_TAC THEN EXISTS_TAC `fns4:(num # clos_exp) list` THEN ASM_REWRITE_TAC[];
       UNDISCH_TAC `((set_of_list (code_locs (MAP SND (fns:(num # clos_exp) list))) UNION
                      set_of_list (list_of_seq (\n. x' + 2 * n) (LENGTH fns))) UNION
                     set_of_list (code_locs [exp])) DIFF
                    domain (FST (g:num_set # (num # num # clos_exp) list)) SUBSET l1` THEN
       SET_TAC[]];
     ALL_TAC] THEN
   DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES CLOSCALLPAUX_IH_NAMES) THEN
   MAP_EVERY EXISTS_TAC CLOSCALLPAUX_IH_NAMES THEN ASM_REWRITE_TAC[] THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN
   ASM_REWRITE_TAC[CLOSCALLPAUX_ALL_FST; clos_state_INFO.ri_accfupds]) THEN
    (FIRST_ASSUM(SUBST1_TAC o MATCH_MP clos_callProof_state_rel_max_app o check (fun th ->
     concl th = `clos_callProof_state_rel g1 l1 (s:(abs_calls_state # C,FFI)clos_state)
                   (t0:(C,FFI)clos_state)`)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[CLOSCALLPAUX_ALL_FST]) THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]) THEN
    (FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP clos_callProof_state_rel_max_app o check (fun th ->
     concl th = `clos_callProof_state_rel g1 l1 (s:(abs_calls_state # C,FFI)clos_state)
                   (t0:(C,FFI)clos_state)`)) THEN
   ASM_REWRITE_TAC[])]));;

(* calls_correct, case evaluate_app (CONS): helper lemmas *)

let CLOSCALLPAUX_dcvr th_v1 th_env1 ma lo env2 x1 v2 g l code =
  ISPECL [th_v1; th_env1; ma; lo; env2; x1; v2; g; l; code] (GEN_ALL dest_closure_v_rel);;

(* After the body of a full application has been simulated: the remaining *)
(* arguments are applied (induction hypothesis on evaluate_app), and the   *)
(* target reduction to the body (with c extra clock ticks) is assumed.    *)
let CLOSCALLPAUX_app_full_cont = prove
 (`!loc_opt (fe:clos_exp) fargs frest (sb:(abs_calls_state # C,FFI)clos_state)
    r1 s1 res s' (eb:clos_exp) envb (tb:(C,FFI)clos_state) f' args' rest2
    (t0:(C,FFI)clos_state) c g l g2 l2 ck res1' t1.
    clos_evaluate ([fe],fargs,sb) = (r1,s1) /\
    (!v. r1 = Rval [v] ==> evaluate_app loc_opt v frest s1 = (res,s')) /\
    (!e. r1 = Rerr e ==> res = r1 /\ s' = s1) /\
    (!v s2. clos_evaluate ([fe],fargs,sb) = (Rval [v],s2)
            ==> CLOSCALLPAUX_cc_Q loc_opt v frest s2) /\
    ~(res = Rerr (Rabort Rtype_error)) /\
    (!k v' t2. clos_evaluate ([eb],envb,
                 clos_state_clock_fupd (K (clos_state_clock tb + k)) tb) = (Rval [v'],t2)
               ==> evaluate_app loc_opt f' args'
                     (clos_state_clock_fupd (K (clos_state_clock t0 + k + c)) t0) =
                   evaluate_app loc_opt v' rest2 t2) /\
    (!k err t2. clos_evaluate ([eb],envb,
                  clos_state_clock_fupd (K (clos_state_clock tb + k)) tb) = (Rerr err,t2)
                ==> evaluate_app loc_opt f' args'
                      (clos_state_clock_fupd (K (clos_state_clock t0 + k + c)) t0) =
                    (Rerr err,t2)) /\
    code_inv (SOME g2) l2 (clos_state_code s1) (clos_state_compile s1)
      (clos_state_compile_oracle s1) (clos_state_code t1) (clos_state_compile t1)
      (clos_state_compile_oracle t1) /\
    wfv_state g2 l2 (clos_state_code t1) s1 /\
    subg g g2 /\ wfg g2 /\ l SUBSET l2 /\ DISJOINT l2 (domain (FST g2)) /\
    every_result (ALL (wfv g2 l2 (clos_state_code t1))) (wfv g2 l2 (clos_state_code t1)) r1 /\
    clos_evaluate ([eb],envb,clos_state_clock_fupd (K (clos_state_clock tb + ck)) tb) =
      (res1',t1) /\
    clos_callProof_state_rel g2 l2 s1 t1 /\
    result_rel (ALL2 (clos_callProof_v_rel g2 l2 (clos_state_code t1)))
      (clos_callProof_v_rel g2 l2 (clos_state_code t1)) r1 res1' /\
    ALL (wfv g l (clos_state_code t0)) frest /\
    ALL2 (clos_callProof_v_rel g l (clos_state_code t0)) frest rest2 /\
    clos_state_code t0 SUBMAP clos_state_code t1
    ==> ?ck res' t g3 l3.
          code_inv (SOME g3) l3 (clos_state_code s') (clos_state_compile s')
            (clos_state_compile_oracle s') (clos_state_code t) (clos_state_compile t)
            (clos_state_compile_oracle t) /\
          wfv_state g3 l3 (clos_state_code t) s' /\
          every_result (ALL (wfv g3 l3 (clos_state_code t))) (wfv g3 l3 (clos_state_code t))
            res /\
          evaluate_app loc_opt f' args'
            (clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) = (res',t) /\
          clos_callProof_state_rel g3 l3 s' t /\
          subg g g3 /\ wfg g3 /\ l SUBSET l3 /\ DISJOINT l3 (domain (FST g3)) /\
          result_rel (ALL2 (clos_callProof_v_rel g3 l3 (clos_state_code t)))
            (clos_callProof_v_rel g3 l3 (clos_state_code t)) res res'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `r1:(clos_v list,clos_v)result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs:clos_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `err:clos_v error_result` SUBST_ALL_TAC)) THENL
   [SUBGOAL_THEN `?v:clos_v. vs = [v]` (X_CHOOSE_THEN `v:clos_v` SUBST_ALL_TAC) THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP clos_evaluate_IMP_LENGTH) THEN
      REWRITE_TAC[LENGTH] THEN DISCH_THEN(MP_TAC o SYM) THEN
      REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "result"; distinctness "result"; CONS_11;
      FORALL_UNWIND_THM1; every_result_def; ALL; result_rel_Rval; LIST_REL_CONS1;
      LIST_REL_NIL]) THEN
    REPEAT (FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
    RVEQ_TAC THEN
    MP_TAC(INST [`clos_state_code (t0:(C,FFI)clos_state)`,`code:(num,num # clos_exp)fmap`;
                 `clos_state_code (t1:(C,FFI)clos_state)`,`code2:(num,num # clos_exp)fmap`;
                 `frest:clos_v list`,`env:clos_v list`] EVERY_wfv_subg) THEN
    MP_TAC(INST [`clos_state_code (t0:(C,FFI)clos_state)`,`code:(num,num # clos_exp)fmap`;
                 `clos_state_code (t1:(C,FFI)clos_state)`,`code2:(num,num # clos_exp)fmap`;
                 `frest:clos_v list`,`xs:clos_v list`;
                 `rest2:clos_v list`,`ys:clos_v list`] LIST_REL_v_rel_subg) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`v:clos_v`; `s1:(abs_calls_state # C,FFI)clos_state`] o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t &&
               fst (dest_const t) = "CLOSCALLPAUX_cc_Q")) (concl th))) THEN
    ASM_REWRITE_TAC[CLOSCALLPAUX_cc_Q_def] THEN
    DISCH_THEN(MP_TAC o SPECL [`g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`;
      `t1:(C,FFI)clos_state`; `res:(clos_v list,clos_v)result`;
      `s':(abs_calls_state # C,FFI)clos_state`; `h':clos_v`; `rest2:clos_v list`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck2:num`; `res2:(clos_v list,clos_v)result`;
      `t2:(C,FFI)clos_state`; `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`]) THEN
    FIRST_ASSUM(MP_TAC o SPEC `ck2:num` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CLOSCALLPAUX_evaluate_add_clock_res) o check (fun th ->
        concl th = `clos_evaluate ([eb],envb,clos_state_clock_fupd
          (K (clos_state_clock (tb:(C,FFI)clos_state) + ck)) tb) = (Rval [h'],t1)`)) THEN
    REWRITE_TAC[distinctness "result"] THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`(ck + ck2) + c:num`; `res2:(clos_v list,clos_v)result`;
      `t2:(C,FFI)clos_state`; `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`ck + ck2:num`; `h':clos_v`;
        `clos_state_clock_fupd (K (clos_state_clock t1 + ck2)) (t1:(C,FFI)clos_state)`] o
        check (fun th -> is_forall (concl th) &&
          can (find_term (fun t -> t = `rest2:clos_v list`)) (concl th) &&
          can (find_term (fun t -> t = `envb:clos_v list`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[subg_trans; SUBSET_TRANS]];
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "result"; distinctness "result";
      FORALL_UNWIND_THM1; every_result_def; result_rel_Rerr1]) THEN
    REPEAT (FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
    RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`ck + c:num`; `Rerr e':(clos_v list,clos_v)result`;
      `t1:(C,FFI)clos_state`; `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`] THEN
    ASM_REWRITE_TAC[every_result_def; result_rel_def] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ck:num`; `e':clos_v error_result`; `t1:(C,FFI)clos_state`] o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `envb:clos_v list`)) (concl th) &&
        not (can (find_term (fun t -> t = `rest2:clos_v list`)) (concl th)))) THEN
    ASM_REWRITE_TAC[]]);;

let CLOSCALLPAUX_ALL2_TAKE_SPLIT = prove
 (`!(R:A->B->bool) l1 l2 n m.
     ALL2 R (TAKE (n + m) l1) (TAKE (n + m) l2) /\ n <= LENGTH l1 /\ n <= LENGTH l2
     ==> ALL2 R (TAKE n l1) (TAKE n l2) /\ ALL2 R (TAKE m (DROP n l1)) (TAKE m (DROP n l2))`,
  REWRITE_TAC[TAKE_SUM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(GEN_ALL LIST_REL_APPEND_IMP) THEN ASM_SIMP_TAC[LENGTH_TAKE]);;

let CLOSCALLPAUX_DROP_DROP_ADD = prove
 (`!n m (l:A list). n + m <= LENGTH l ==> DROP m (DROP n l) = DROP (n + m) l`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`m:num`; `n:num`; `l:A list`] DROP_DROP) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD_SYM]]);;

let CLOSCALLPAUX_code_locs_EL = prove
 (`!xs i. i < LENGTH xs /\ ALL_DISTINCT (code_locs xs) ==> ALL_DISTINCT (code_locs [EL i xs])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  SUBST1_TAC(ISPECL [`h:clos_exp`; `t:clos_exp list`] code_locs_cons) THEN
  REWRITE_TAC[ALL_DISTINCT_APPEND] THEN
  INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; LT_SUC] THEN ASM_MESON_TAC[]);;

let CLOSCALLPAUX_recclosure_wf_EL = prove
 (`!loc (fns:(num # clos_exp) list) i.
     recclosure_wf loc fns /\ i < LENGTH fns
     ==> every_Fn_SOME [SND (EL i fns)] /\ every_Fn_vs_NONE [SND (EL i fns)] /\
         ALL_DISTINCT (code_locs [SND (EL i fns)])`,
  REWRITE_TAC[recclosure_wf_def] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPEC `MAP SND (fns:(num # clos_exp) list)` every_Fn_SOME_EVERY) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM ALL_EL; LENGTH_MAP] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[EL_MAP];
    MP_TAC(ISPEC `MAP SND (fns:(num # clos_exp) list)` every_Fn_vs_NONE_EVERY) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM ALL_EL; LENGTH_MAP] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[EL_MAP];
    MP_TAC(ISPECL [`MAP SND (fns:(num # clos_exp) list)`; `i:num`] CLOSCALLPAUX_code_locs_EL) THEN
    ASM_SIMP_TAC[LENGTH_MAP; EL_MAP]]);;

let CLOSCALLPAUX_env_rel_closed_TAKE = prove
 (`!(R:A->B->bool) fargs args2 n m e.
     (!x. clos_fv1 x e ==> x < n) /\ n + m <= LENGTH fargs /\ n + m <= LENGTH args2 /\
     ALL2 R (TAKE (n + m) fargs) (TAKE (n + m) args2)
     ==> clos_callProof_env_rel R fargs (TAKE n args2) 0 [(0,e)]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n <= LENGTH (fargs:A list) /\ n <= LENGTH (args2:B list)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`R:A->B->bool`; `fargs:A list`; `args2:B list`; `n:num`; `m:num`]
    CLOSCALLPAUX_ALL2_TAKE_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[LIST_REL_EL_EQN] THEN ASM_SIMP_TAC[LENGTH_TAKE; EL_TAKE] THEN DISCH_TAC THEN
  REWRITE_TAC[clos_callProof_env_rel_def; EX] THEN CASE_REWRITE_TAC[ADD_CLAUSES] THEN
  ASM_SIMP_TAC[LENGTH_TAKE; LIST_REL_EL_EQN] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[EL_TAKE; LTE_TRANS]);;

let CLOSCALLPAUX_env_rel_TAKE_DROP = prove
 (`!(R:A->B->bool) fargs args2 n m e.
     n + m <= LENGTH fargs /\ n + m <= LENGTH args2 /\
     ALL2 R (TAKE (n + m) fargs) (TAKE (n + m) args2) /\
     clos_callProof_env_rel R (DROP (n + m) fargs) (DROP (n + m) args2) m [(n,e)]
     ==> clos_callProof_env_rel R fargs args2 0 [(0,e)]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n <= LENGTH (fargs:A list) /\ n <= LENGTH (args2:B list)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`R:A->B->bool`; `fargs:A list`; `args2:B list`; `n:num`; `m:num`]
    CLOSCALLPAUX_ALL2_TAKE_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(GEN_ALL env_rel_DROP_args) THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(GEN_ALL env_rel_DROP) THEN EXISTS_TAC `m:num` THEN
  ASM_SIMP_TAC[CLOSCALLPAUX_DROP_DROP_ADD; LENGTH_DROP] THEN ASM_ARITH_TAC);;

let CLOSCALLPAUX_app_red_nc = prove
 (`!loc_opt f' h' t' eb args2 rest2 (t0:(C,FFI)clos_state).
     dest_closure (clos_state_max_app t0) loc_opt f' (CONS h' t') =
       SOME (Full_app eb args2 rest2) /\
     LENGTH (CONS h' t') - LENGTH rest2 <= clos_state_clock t0
     ==> (!k v' t2.
            clos_evaluate ([eb],args2,clos_state_clock_fupd
              (K (clos_state_clock (clos_dec_clock (LENGTH (CONS h' t') - LENGTH rest2) t0) + k))
              (clos_dec_clock (LENGTH (CONS h' t') - LENGTH rest2) t0)) = (Rval [v'],t2)
            ==> evaluate_app loc_opt f' (CONS h' t')
                  (clos_state_clock_fupd (K (clos_state_clock t0 + k + 0)) t0) =
                evaluate_app loc_opt v' rest2 t2) /\
         (!k err t2.
            clos_evaluate ([eb],args2,clos_state_clock_fupd
              (K (clos_state_clock (clos_dec_clock (LENGTH (CONS h' t') - LENGTH rest2) t0) + k))
              (clos_dec_clock (LENGTH (CONS h' t') - LENGTH rest2) t0)) = (Rerr err,t2)
            ==> evaluate_app loc_opt f' (CONS h' t')
                  (clos_state_clock_fupd (K (clos_state_clock t0 + k + 0)) t0) = (Rerr err,t2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN
   `!k. clos_dec_clock (LENGTH (CONS (h':clos_v) t') - LENGTH (rest2:clos_v list))
          (clos_state_clock_fupd (K (clos_state_clock t0 + k)) (t0:(C,FFI)clos_state)) =
        clos_state_clock_fupd
          (K (clos_state_clock (clos_dec_clock (LENGTH (CONS h' t') - LENGTH rest2) t0) + k))
          (clos_dec_clock (LENGTH (CONS h' t') - LENGTH rest2) t0)`
   ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CLOSCALLPAUX_dec_clock_add THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. ~(clos_state_clock (t0:(C,FFI)clos_state) + k <
                      LENGTH (CONS (h':clos_v) t') - LENGTH (rest2:clos_v list))`
   ASSUME_TAC THENL [GEN_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_evaluate_def] THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let CLOSCALLPAUX_app_red_cl = prove
 (`!loc_opt f' h' t' tra loc i n e args2 rest2 (t0:(C,FFI)clos_state).
     dest_closure (clos_state_max_app t0) loc_opt f' (CONS h' t') =
       SOME (Full_app (clos_Call tra 0 (loc + 2 * i + 1) (GENLIST_Var tra 1 n)) args2 rest2) /\
     FLOOKUP (clos_state_code t0) (loc + 2 * i + 1) = SOME (n,e) /\ n <= LENGTH args2 /\
     LENGTH (CONS h' t') - LENGTH rest2 <= clos_state_clock t0
     ==> (!k v' t2.
            clos_evaluate ([e],TAKE n args2,clos_state_clock_fupd
              (K (clos_state_clock (clos_dec_clock (LENGTH (CONS h' t') - LENGTH rest2) t0) + k))
              (clos_dec_clock (LENGTH (CONS h' t') - LENGTH rest2) t0)) = (Rval [v'],t2)
            ==> evaluate_app loc_opt f' (CONS h' t')
                  (clos_state_clock_fupd (K (clos_state_clock t0 + k + 1)) t0) =
                evaluate_app loc_opt v' rest2 t2) /\
         (!k err t2.
            clos_evaluate ([e],TAKE n args2,clos_state_clock_fupd
              (K (clos_state_clock (clos_dec_clock (LENGTH (CONS h' t') - LENGTH rest2) t0) + k))
              (clos_dec_clock (LENGTH (CONS h' t') - LENGTH rest2) t0)) = (Rerr err,t2)
            ==> evaluate_app loc_opt f' (CONS h' t')
                  (clos_state_clock_fupd (K (clos_state_clock t0 + k + 1)) t0) = (Rerr err,t2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `dk = LENGTH (CONS (h':clos_v) t') - LENGTH (rest2:clos_v list)` THEN
  SUBGOAL_THEN
   `!k. clos_dec_clock (0 + 1) (clos_dec_clock dk
          (clos_state_clock_fupd (K (clos_state_clock t0 + k + 1)) (t0:(C,FFI)clos_state))) =
        clos_state_clock_fupd (K (clos_state_clock (clos_dec_clock dk t0) + k))
          (clos_dec_clock dk t0)`
   ASSUME_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC[clos_dec_clock_def; clos_state_component_equality;
                clos_state_INFO.ri_accfupds; K_THM] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. ~(clos_state_clock (clos_dec_clock dk
          (clos_state_clock_fupd (K (clos_state_clock t0 + k + 1)) (t0:(C,FFI)clos_state))) < 0 + 1) /\
        ~(clos_state_clock t0 + k + 1 < dk)`
   ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_evaluate_def] THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN
  ASM_REWRITE_TAC[evaluate_GENLIST_Var_tra] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[clos_find_code_def; clos_dec_clock_code; clos_state_INFO.ri_accfupds] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[LENGTH_TAKE] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

let CLOSCALLPAUX_fv1_has_var = prove
 (`!e x. clos_fv1 x e <=> has_var x (SND (clos_call_free [e]))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_fv1_def] THEN MP_TAC(SPEC `[e:clos_exp]` free_thm) THEN
  IL1AUX_PAIRARG_TAC THEN ASM_REWRITE_TAC[SND] THEN SIMP_TAC[]);;

let CLOSCALLPAUX_ALOOKUP_code_list_EL = prove
 (`!loc fns (g:B # (num # num # A) list) i.
     i < LENGTH fns
     ==> ALOOKUP (SND (clos_call_code_list loc fns g)) (loc + 2 * i + 1) = SOME (EL i fns)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ALOOKUP_code_list] THEN
  CLOSCALLPAUX_SOME_INTRO_TAC THEN CASE_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `j:num = i` SUBST1_TAC THENL [ASM_ARITH_TAC; CASE_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[]]);;

let CLOSCALLPAUX_insert_each'_setup = prove
 (`!loc (fns1:(num # clos_exp) list) (g0:num_set # (num # num # clos_exp) list) gt.
     recclosure_wf loc fns1 /\ wfg g0 /\
     DISJOINT (IMAGE SUC (set_of_list (code_locs (MAP SND fns1))))
              (set_of_list (MAP FST (SND g0))) /\
     DISJOINT (set_of_list (list_of_seq (\i. 2 * i + loc + 1) (LENGTH fns1)))
              (set_of_list (MAP FST (SND g0)))
     ==> ALL_DISTINCT (MAP FST (SND (insert_each' gt loc (LENGTH fns1) g0))) /\
         DISJOINT (IMAGE SUC (set_of_list (code_locs (MAP SND fns1))))
                  (set_of_list (MAP FST (SND (insert_each' gt loc (LENGTH fns1) g0)))) /\
         wfg (insert_each' gt loc (LENGTH fns1) g0) /\
         DISJOINT (set_of_list (list_of_seq (\i. 2 * i + loc + 1) (LENGTH fns1)))
                  (IMAGE SUC (domain (FST g0)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[recclosure_wf_def] THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[wfg_def] (ASSUME `wfg (g0:num_set # (num # num # clos_exp) list)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `DISJOINT (set_of_list (list_of_seq (\i. 2 * i + loc + 1)
                (LENGTH (fns1:(num # clos_exp) list))))
             (IMAGE SUC (domain (FST (g0:num_set # (num # num # clos_exp) list))))`
   ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (set_of_list (list_of_seq (\i. 2 * i + loc + 1)
                   (LENGTH (fns1:(num # clos_exp) list))))
             (set_of_list (MAP FST (SND (g0:num_set # (num # num # clos_exp) list))))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[MAP_FST_insert_each'] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC; ALL_TAC; MATCH_MP_TAC wfg_insert_each' THEN ASM_REWRITE_TAC[]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_DISJOINT; IN_SET_OF_LIST; MEM_GENLIST; IN_IMAGE]) THEN
  REWRITE_TAC[IN_DISJOINT; IN_SET_OF_LIST; MEM_GENLIST; IN_IMAGE; ALL_DISTINCT_APPEND;
    ALL_DISTINCT_REVERSE; ALL_DISTINCT_GENLIST; MEM_REVERSE; MEM_APPEND;
    SET_OF_LIST_APPEND; IN_UNION] THENL
   [REPEAT CONJ_TAC THENL [ARITH_TAC; ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `x:num` THEN DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `2 * m + loc + 1`)) (concl th) &&
      can (find_term (fun t -> t = `MEM:num->num list->bool`)) (concl th))) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ARITH_RULE `loc + m * 2 + 1 = 2 * m + loc + 1`];
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `x':num` o REWRITE_RULE[NOT_EXISTS_THM] o check (fun th ->
        can (find_term (fun t -> t = `2 * m + loc`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `m:num` THEN ASM_ARITH_TAC;
      ASM_MESON_TAC[]];
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC x` o REWRITE_RULE[NOT_EXISTS_THM] o check (fun th ->
      can (find_term (fun t -> t = `2 * m + loc + 1`)) (concl th) &&
      can (find_term (fun t -> t = `domain:num_set->num->bool`)) (concl th))) THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `m:num` THEN ASM_ARITH_TAC; EXISTS_TAC `x:num` THEN ASM_REWRITE_TAC[]]]);;

(* calls_correct, case evaluate_app (CONS), full application of a closure *)
(* whose body was not compiled to a call of the code table.              *)
let CLOSCALLPAUX_cc_app_full_nc = prove
 (`!loc_opt (s:(abs_calls_state # C,FFI)clos_state) fe fargs frest r1 s1 res s'
    g l (t0:(C,FFI)clos_state) f' h' t' args2 rest2 m n i loc fns1
    (g0:num_set # (num # num # clos_exp) list) es' new_g'.
    ~(clos_state_clock s < LENGTH (CONS h' t') - LENGTH rest2) /\
    clos_evaluate ([fe],fargs,clos_dec_clock (LENGTH (CONS h' t') - LENGTH rest2) s) = (r1,s1) /\
    (!v. r1 = Rval [v] ==> evaluate_app loc_opt v frest s1 = (res,s')) /\
    (!e. r1 = Rerr e ==> res = r1 /\ s' = s1) /\
    (!v s2. clos_evaluate ([fe],fargs,clos_dec_clock (LENGTH (CONS h' t') - LENGTH rest2) s) =
              (Rval [v],s2)
            ==> CLOSCALLPAUX_cc_Q loc_opt v frest s2) /\
    CLOSCALLPAUX_cc_P ([fe],fargs,clos_dec_clock (LENGTH (CONS h' t') - LENGTH rest2) s) /\
    ~(res = Rerr (Rabort Rtype_error)) /\
    code_inv (SOME g) l (clos_state_code s) (clos_state_compile s)
      (clos_state_compile_oracle s) (clos_state_code t0) (clos_state_compile t0)
      (clos_state_compile_oracle t0) /\
    wfv_state g l (clos_state_code t0) s /\ wfg g /\ DISJOINT l (domain (FST g)) /\
    clos_callProof_state_rel g l s t0 /\
    ALL (wfv g l (clos_state_code t0)) fargs /\ ALL (wfv g l (clos_state_code t0)) frest /\
    dest_closure (clos_state_max_app t0) loc_opt f' (CONS h' t') =
      SOME (Full_app (EL i es') args2 rest2) /\
    n + m <= LENGTH fargs /\ n + m <= LENGTH args2 /\
    ALL2 (clos_callProof_v_rel g l (clos_state_code t0)) (TAKE (n + m) fargs)
      (TAKE (n + m) args2) /\
    clos_callProof_env_rel (clos_callProof_v_rel g l (clos_state_code t0))
      (DROP (n + m) fargs) (DROP (n + m) args2) m [(n,EL i es')] /\
    ALL2 (clos_callProof_v_rel g l (clos_state_code t0)) frest rest2 /\
    i < LENGTH fns1 /\ EL i fns1 = (n,fe) /\
    recclosure_wf loc fns1 /\ wfg g0 /\
    DISJOINT (IMAGE SUC (set_of_list (code_locs (MAP SND fns1))))
             (set_of_list (MAP FST (SND g0))) /\
    clos_call_calls (MAP SND fns1) g0 = (es',new_g') /\
    subg new_g' g /\
    set_of_list (code_locs (MAP SND fns1)) DIFF domain (FST new_g') SUBSET l /\
    code_includes (SND new_g') (clos_state_code t0)
    ==> ?ck res' t g2 l2.
          code_inv (SOME g2) l2 (clos_state_code s') (clos_state_compile s')
            (clos_state_compile_oracle s') (clos_state_code t) (clos_state_compile t)
            (clos_state_compile_oracle t) /\
          wfv_state g2 l2 (clos_state_code t) s' /\
          every_result (ALL (wfv g2 l2 (clos_state_code t))) (wfv g2 l2 (clos_state_code t))
            res /\
          evaluate_app loc_opt f' (CONS h' t')
            (clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) = (res',t) /\
          clos_callProof_state_rel g2 l2 s' t /\
          subg g g2 /\ wfg g2 /\ l SUBSET l2 /\ DISJOINT l2 (domain (FST g2)) /\
          result_rel (ALL2 (clos_callProof_v_rel g2 l2 (clos_state_code t)))
            (clos_callProof_v_rel g2 l2 (clos_state_code t)) res res'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `clos_state_clock (s:(abs_calls_state # C,FFI)clos_state) = clos_state_clock (t0:(C,FFI)clos_state) /\
                 LENGTH (CONS (h':clos_v) t') - LENGTH (rest2:clos_v list) <= clos_state_clock t0 /\
                 EL i (MAP SND (fns1:(num # clos_exp) list)) = fe /\ SND (EL i fns1) = fe /\
                 ~(r1 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(ASSUME_TAC o MATCH_MP clos_callProof_state_rel_clock) THEN
     ASM_SIMP_TAC[EL_MAP] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `Rabort Rtype_error:clos_v error_result` o
       check (fun th -> is_forall (concl th) && can (find_term (fun t -> t = `s':(abs_calls_state # C,FFI)clos_state`)) (concl th) && not (can (find_term (fun t -> t = `evaluate_app:num option->clos_v->clos_v list->(abs_calls_state # C,FFI)clos_state->(clos_v list,clos_v)result # (abs_calls_state # C,FFI)clos_state`)) (concl th)))) THEN
     ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`loc:num`; `fns1:(num # clos_exp) list`; `i:num`] CLOSCALLPAUX_recclosure_wf_EL) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   MP_TAC(ISPECL [`MAP SND (fns1:(num # clos_exp) list)`; `g0:num_set # (num # num # clos_exp) list`;
                  `es':clos_exp list`; `new_g':num_set # (num # num # clos_exp) list`; `i:num`] calls_el_sing) THEN
   ANTS_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[recclosure_wf_def]) THEN
     ASM_REWRITE_TAC[LENGTH_MAP] THEN ASM_MESON_TAC[wfg_def];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `ga:num_set # (num # num # clos_exp) list`
     (X_CHOOSE_THEN `gb:num_set # (num # num # clos_exp) list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSCALLPAUX_cc_P_def] o check (fun th -> CLOSCALLPAUX_head_is "CLOSCALLPAUX_cc_P" th)) THEN
   DISCH_THEN(MP_TAC o SPECL [`ga:num_set # (num # num # clos_exp) list`;
     `gb:num_set # (num # num # clos_exp) list`; `args2:clos_v list`;
     `clos_dec_clock (LENGTH (CONS (h':clos_v) t') - LENGTH (rest2:clos_v list)) (t0:(C,FFI)clos_state)`;
     `[EL i (es':clos_exp list)]`; `r1:(clos_v list,clos_v)result`;
     `s1:(abs_calls_state # C,FFI)clos_state`;
     `set_of_list (code_locs [fe]) DIFF domain (FST (gb:num_set # (num # num # clos_exp) list))`;
     `l:num->bool`; `g:num_set # (num # num # clos_exp) list`]) THEN
   ANTS_TAC THENL
    [REWRITE_TAC[clos_dec_clock_code; dec_clock_compile; dec_clock_compile_oracle;
                 CLOSCALLPAUX_wfv_state_dec_clock; MAP] THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC subg_trans THEN EXISTS_TAC `new_g':num_set # (num # num # clos_exp) list` THEN
     ASM_REWRITE_TAC[];
     MATCH_MP_TAC SUBSET_TRANS THEN
     EXISTS_TAC `set_of_list (code_locs (MAP SND (fns1:(num # clos_exp) list))) DIFF
                 domain (FST (new_g':num_set # (num # num # clos_exp) list))` THEN
     ASM_REWRITE_TAC[];
     MATCH_MP_TAC CLOSCALLPAUX_env_rel_TAKE_DROP THEN
     MAP_EVERY EXISTS_TAC [`n:num`; `m:num`] THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC CLOSCALLPAUX_state_rel_dec_clock THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (GEN_ALL code_includes_subg)) THEN
     EXISTS_TAC `new_g':num_set # (num # num # clos_exp) list` THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
  DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck1:num`; `res1:(clos_v list,clos_v)result`;
     `t1:(C,FFI)clos_state`; `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`]) THEN
   MP_TAC(ISPECL [`loc_opt:num option`; `f':clos_v`; `h':clos_v`; `t':clos_v list`;
     `EL i (es':clos_exp list)`; `args2:clos_v list`; `rest2:clos_v list`; `t0:(C,FFI)clos_state`]
     CLOSCALLPAUX_app_red_nc) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   SUBGOAL_THEN `clos_state_code (t0:(C,FFI)clos_state) SUBMAP clos_state_code (t1:(C,FFI)clos_state)`
     ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP clos_evaluate_mono o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `res1:(clos_v list,clos_v)result,t1:(C,FFI)clos_state`)) THEN
     REWRITE_TAC[clos_state_INFO.ri_accfupds; clos_dec_clock_code];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`loc_opt:num option`; `fe:clos_exp`; `fargs:clos_v list`; `frest:clos_v list`;
     `clos_dec_clock (LENGTH (CONS (h':clos_v) t') - LENGTH (rest2:clos_v list))
        (s:(abs_calls_state # C,FFI)clos_state)`;
     `r1:(clos_v list,clos_v)result`; `s1:(abs_calls_state # C,FFI)clos_state`;
     `res:(clos_v list,clos_v)result`; `s':(abs_calls_state # C,FFI)clos_state`;
     `EL i (es':clos_exp list)`; `args2:clos_v list`;
     `clos_dec_clock (LENGTH (CONS (h':clos_v) t') - LENGTH (rest2:clos_v list))
        (t0:(C,FFI)clos_state)`;
     `f':clos_v`; `CONS (h':clos_v) t'`; `rest2:clos_v list`; `t0:(C,FFI)clos_state`; `0`;
     `g:num_set # (num # num # clos_exp) list`; `l:num->bool`;
     `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`; `ck1:num`;
     `res1:(clos_v list,clos_v)result`; `t1:(C,FFI)clos_state`] CLOSCALLPAUX_app_full_cont) THEN
   ASM_REWRITE_TAC[]);;


(* calls_correct, case evaluate_app (CONS), full application of a closure *)
(* whose body was compiled to a call of the code table (closed bodies).   *)
let CLOSCALLPAUX_cc_app_full_cl = prove
 (`!loc_opt (s:(abs_calls_state # C,FFI)clos_state) fe fargs frest r1 s1 res s'
    g l (t0:(C,FFI)clos_state) f' h' t' args2 rest2 m n i loc fns1
    (g0:num_set # (num # num # clos_exp) list) es new_g tra.
    ~(clos_state_clock s < LENGTH (CONS h' t') - LENGTH rest2) /\
    clos_evaluate ([fe],fargs,clos_dec_clock (LENGTH (CONS h' t') - LENGTH rest2) s) = (r1,s1) /\
    (!v. r1 = Rval [v] ==> evaluate_app loc_opt v frest s1 = (res,s')) /\
    (!e. r1 = Rerr e ==> res = r1 /\ s' = s1) /\
    (!v s2. clos_evaluate ([fe],fargs,clos_dec_clock (LENGTH (CONS h' t') - LENGTH rest2) s) =
              (Rval [v],s2)
            ==> CLOSCALLPAUX_cc_Q loc_opt v frest s2) /\
    CLOSCALLPAUX_cc_P ([fe],fargs,clos_dec_clock (LENGTH (CONS h' t') - LENGTH rest2) s) /\
    ~(res = Rerr (Rabort Rtype_error)) /\
    code_inv (SOME g) l (clos_state_code s) (clos_state_compile s)
      (clos_state_compile_oracle s) (clos_state_code t0) (clos_state_compile t0)
      (clos_state_compile_oracle t0) /\
    wfv_state g l (clos_state_code t0) s /\ wfg g /\ DISJOINT l (domain (FST g)) /\
    clos_callProof_state_rel g l s t0 /\
    ALL (wfv g l (clos_state_code t0)) fargs /\ ALL (wfv g l (clos_state_code t0)) frest /\
    dest_closure (clos_state_max_app t0) loc_opt f' (CONS h' t') =
      SOME (Full_app (clos_Call tra 0 (loc + 2 * i + 1) (GENLIST_Var tra 1 n)) args2 rest2) /\
    n + m <= LENGTH fargs /\ n + m <= LENGTH args2 /\
    ALL2 (clos_callProof_v_rel g l (clos_state_code t0)) (TAKE (n + m) fargs)
      (TAKE (n + m) args2) /\
    ALL2 (clos_callProof_v_rel g l (clos_state_code t0)) frest rest2 /\
    i < LENGTH fns1 /\ EL i fns1 = (n,fe) /\
    recclosure_wf loc fns1 /\ wfg g0 /\
    DISJOINT (IMAGE SUC (set_of_list (code_locs (MAP SND fns1))))
             (set_of_list (MAP FST (SND g0))) /\
    DISJOINT (set_of_list (list_of_seq (\i. 2 * i + loc + 1) (LENGTH fns1)))
             (set_of_list (MAP FST (SND g0))) /\
    clos_call_calls (MAP SND fns1) (insert_each loc (LENGTH fns1) g0) = (es,new_g) /\
    (!v. has_var v (SND (clos_call_free [EL i es])) ==> v < n) /\
    subg (clos_call_code_list loc (ZIP (MAP FST fns1) es) new_g) g /\
    set_of_list (code_locs (MAP SND fns1)) DIFF domain (FST new_g) SUBSET l /\
    code_includes (SND (clos_call_code_list loc (ZIP (MAP FST fns1) es) new_g))
      (clos_state_code t0)
    ==> ?ck res' t g2 l2.
          code_inv (SOME g2) l2 (clos_state_code s') (clos_state_compile s')
            (clos_state_compile_oracle s') (clos_state_code t) (clos_state_compile t)
            (clos_state_compile_oracle t) /\
          wfv_state g2 l2 (clos_state_code t) s' /\
          every_result (ALL (wfv g2 l2 (clos_state_code t))) (wfv g2 l2 (clos_state_code t))
            res /\
          evaluate_app loc_opt f' (CONS h' t')
            (clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) = (res',t) /\
          clos_callProof_state_rel g2 l2 s' t /\
          subg g g2 /\ wfg g2 /\ l SUBSET l2 /\ DISJOINT l2 (domain (FST g2)) /\
          result_rel (ALL2 (clos_callProof_v_rel g2 l2 (clos_state_code t)))
            (clos_callProof_v_rel g2 l2 (clos_state_code t)) res res'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `clos_state_clock (s:(abs_calls_state # C,FFI)clos_state) = clos_state_clock (t0:(C,FFI)clos_state) /\
                 LENGTH (CONS (h':clos_v) t') - LENGTH (rest2:clos_v list) <= clos_state_clock t0 /\
                 EL i (MAP SND (fns1:(num # clos_exp) list)) = fe /\ SND (EL i fns1) = fe /\
                 ~(r1 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(ASSUME_TAC o MATCH_MP clos_callProof_state_rel_clock) THEN
     ASM_SIMP_TAC[EL_MAP] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `Rabort Rtype_error:clos_v error_result` o
       check (fun th -> is_forall (concl th) && can (find_term (fun t -> t = `s':(abs_calls_state # C,FFI)clos_state`)) (concl th) && not (can (find_term (fun t -> t = `evaluate_app:num option->clos_v->clos_v list->(abs_calls_state # C,FFI)clos_state->(clos_v list,clos_v)result # (abs_calls_state # C,FFI)clos_state`)) (concl th)))) THEN
     ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`loc:num`; `fns1:(num # clos_exp) list`; `i:num`] CLOSCALLPAUX_recclosure_wf_EL) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   ALL_TAC THEN
  SUBGOAL_THEN `LENGTH (es:clos_exp list) = LENGTH (fns1:(num # clos_exp) list)` ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP calls_length o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `es:clos_exp list,new_g:num_set # (num # num # clos_exp) list`)) THEN
     REWRITE_TAC[LENGTH_MAP];
     ALL_TAC] THEN
   SUBGOAL_THEN `EL i (ZIP (MAP FST (fns1:(num # clos_exp) list)) (es:clos_exp list)) = (n,EL i es) /\
                 i < LENGTH (ZIP (MAP FST fns1) es)` STRIP_ASSUME_TAC THENL
    [ASM_SIMP_TAC[EL_ZIP; LENGTH_MAP; EL_MAP; LENGTH_ZIP; FST]; ALL_TAC] THEN
   SUBGOAL_THEN `FLOOKUP (clos_state_code (t0:(C,FFI)clos_state)) (loc + 2 * i + 1) =
                 SOME (n,EL i (es:clos_exp list))` ASSUME_TAC THENL
    [MATCH_MP_TAC(GEN_ALL code_includes_ALOOKUP) THEN
     EXISTS_TAC `SND (clos_call_code_list loc (ZIP (MAP FST (fns1:(num # clos_exp) list)) es)
                   (new_g:num_set # (num # num # clos_exp) list))` THEN
     ASM_SIMP_TAC[CLOSCALLPAUX_ALOOKUP_code_list_EL];
     ALL_TAC] THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP calls_IS_SUFFIX o check (fun th -> is_eq (concl th) &&
     rand (concl th) = `es:clos_exp list,new_g:num_set # (num # num # clos_exp) list`)) THEN
   REWRITE_TAC[IS_SUFFIX_APPEND; SND_insert_each] THEN
   DISCH_THEN(X_CHOOSE_TAC `ls:(num # num # clos_exp) list`) THEN
   MP_TAC(ISPECL [`MAP SND (fns1:(num # clos_exp) list)`;
     `insert_each loc (LENGTH (fns1:(num # clos_exp) list)) (g0:num_set # (num # num # clos_exp) list)`;
     `es:clos_exp list`; `new_g:num_set # (num # num # clos_exp) list`;
     `insert_each' (SND (g:num_set # (num # num # clos_exp) list)) loc (LENGTH (fns1:(num # clos_exp) list)) (g0:num_set # (num # num # clos_exp) list)`;
     `ls:(num # num # clos_exp) list`] calls_replace_SND) THEN
   ASM_REWRITE_TAC[FST_insert_each'; SND_insert_each] THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`loc:num`; `fns1:(num # clos_exp) list`; `g0:num_set # (num # num # clos_exp) list`;
     `SND (g:num_set # (num # num # clos_exp) list)`] CLOSCALLPAUX_insert_each'_setup) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   MP_TAC(ISPECL [`MAP SND (fns1:(num # clos_exp) list)`;
     `insert_each' (SND (g:num_set # (num # num # clos_exp) list)) loc (LENGTH (fns1:(num # clos_exp) list)) (g0:num_set # (num # num # clos_exp) list)`;
     `es:clos_exp list`;
     `FST (new_g:num_set # (num # num # clos_exp) list),
      APPEND ls (SND (insert_each' (SND (g:num_set # (num # num # clos_exp) list)) loc (LENGTH (fns1:(num # clos_exp) list)) (g0:num_set # (num # num # clos_exp) list)))`;
     `i:num`] calls_el_sing) THEN
   ANTS_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[recclosure_wf_def]) THEN ASM_REWRITE_TAC[LENGTH_MAP];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `ga:num_set # (num # num # clos_exp) list`
     (X_CHOOSE_THEN `gb:num_set # (num # num # clos_exp) list` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `subg (FST (new_g:num_set # (num # num # clos_exp) list),
        APPEND ls (SND (insert_each' (SND (g:num_set # (num # num # clos_exp) list)) loc
          (LENGTH (fns1:(num # clos_exp) list)) (g0:num_set # (num # num # clos_exp) list))))
       (clos_call_code_list loc (ZIP (MAP FST fns1) es) new_g)` ASSUME_TAC THENL
    [MATCH_MP_TAC(GEN_ALL subg_insert_each') THEN
     EXISTS_TAC `gb:num_set # (num # num # clos_exp) list` THEN
     ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
      [SUBGOAL_THEN `ALL_DISTINCT (MAP FST (SND (new_g:num_set # (num # num # clos_exp) list)))`
         MP_TAC THENL
        [MATCH_MP_TAC calls_ALL_DISTINCT THEN
         MAP_EVERY EXISTS_TAC [`MAP SND (fns1:(num # clos_exp) list)`;
           `insert_each loc (LENGTH (fns1:(num # clos_exp) list))
              (g0:num_set # (num # num # clos_exp) list)`; `es:clos_exp list`] THEN
         REWRITE_TAC[SND_insert_each] THEN
         MP_TAC(CONJUNCT2(REWRITE_RULE[wfg_def]
           (ASSUME `wfg (g0:num_set # (num # num # clos_exp) list)`))) THEN
         MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2(REWRITE_RULE[recclosure_wf_def]
           (ASSUME `recclosure_wf loc (fns1:(num # clos_exp) list)`))))) THEN
         REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       ASM_REWRITE_TAC[MAP_APPEND; ALL_DISTINCT_APPEND'] THEN
       MP_TAC(REWRITE_RULE[wfg_def] (ASSUME `wfg (g0:num_set # (num # num # clos_exp) list)`)) THEN
       SIMP_TAC[];
       X_GEN_TAC `j:num` THEN DISCH_TAC THEN
       UNDISCH_TAC `subg (clos_call_code_list loc (ZIP (MAP FST (fns1:(num # clos_exp) list)) es)
         (new_g:num_set # (num # num # clos_exp) list)) (g:num_set # (num # num # clos_exp) list)` THEN
       REWRITE_TAC[subg_def] THEN STRIP_TAC THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       ONCE_REWRITE_TAC[ARITH_RULE `2 * j + loc + 1 = loc + 2 * j + 1`] THEN
       MP_TAC(ISPECL [`loc:num`; `ZIP (MAP FST (fns1:(num # clos_exp) list)) (es:clos_exp list)`;
         `new_g:num_set # (num # num # clos_exp) list`; `j:num`] CLOSCALLPAUX_ALOOKUP_code_list_EL) THEN
       ASM_SIMP_TAC[LENGTH_ZIP; LENGTH_MAP; EL_ZIP; EL_MAP]];
     ALL_TAC] THEN
   SUBGOAL_THEN `subg (gb:num_set # (num # num # clos_exp) list)
       (clos_call_code_list loc (ZIP (MAP FST (fns1:(num # clos_exp) list)) es)
         (new_g:num_set # (num # num # clos_exp) list))` ASSUME_TAC THENL
    [MATCH_MP_TAC subg_trans THEN
     EXISTS_TAC `FST (new_g:num_set # (num # num # clos_exp) list),
        APPEND ls (SND (insert_each' (SND (g:num_set # (num # num # clos_exp) list)) loc
          (LENGTH (fns1:(num # clos_exp) list)) (g0:num_set # (num # num # clos_exp) list)))` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `subg (gb:num_set # (num # num # clos_exp) list) g` ASSUME_TAC THENL
    [MATCH_MP_TAC subg_trans THEN
     EXISTS_TAC `clos_call_code_list loc (ZIP (MAP FST (fns1:(num # clos_exp) list)) es)
         (new_g:num_set # (num # num # clos_exp) list)` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSCALLPAUX_cc_P_def] o check (fun th -> CLOSCALLPAUX_head_is "CLOSCALLPAUX_cc_P" th)) THEN
   DISCH_THEN(MP_TAC o SPECL [`ga:num_set # (num # num # clos_exp) list`;
     `gb:num_set # (num # num # clos_exp) list`; `TAKE n (args2:clos_v list)`;
     `clos_dec_clock (LENGTH (CONS (h':clos_v) t') - LENGTH (rest2:clos_v list)) (t0:(C,FFI)clos_state)`;
     `[EL i (es:clos_exp list)]`; `r1:(clos_v list,clos_v)result`;
     `s1:(abs_calls_state # C,FFI)clos_state`;
     `set_of_list (code_locs [fe]) DIFF domain (FST (gb:num_set # (num # num # clos_exp) list))`;
     `l:num->bool`; `g:num_set # (num # num # clos_exp) list`]) THEN
   ANTS_TAC THENL
    [REWRITE_TAC[clos_dec_clock_code; dec_clock_compile; dec_clock_compile_oracle;
                 CLOSCALLPAUX_wfv_state_dec_clock; MAP] THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC SUBSET_TRANS THEN
       EXISTS_TAC `set_of_list (code_locs (MAP SND (fns1:(num # clos_exp) list))) DIFF
                   domain (FST (new_g:num_set # (num # num # clos_exp) list))` THEN
       ASM_REWRITE_TAC[];
       MATCH_MP_TAC CLOSCALLPAUX_env_rel_closed_TAKE THEN EXISTS_TAC `m:num` THEN
       ASM_REWRITE_TAC[CLOSCALLPAUX_fv1_has_var];
       MATCH_MP_TAC CLOSCALLPAUX_state_rel_dec_clock THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (GEN_ALL code_includes_subg)) THEN
       EXISTS_TAC `clos_call_code_list loc (ZIP (MAP FST (fns1:(num # clos_exp) list)) es)
         (new_g:num_set # (num # num # clos_exp) list)` THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
  DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck1:num`; `res1:(clos_v list,clos_v)result`;
     `t1:(C,FFI)clos_state`; `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`]) THEN
   MP_TAC(ISPECL [`loc_opt:num option`; `f':clos_v`; `h':clos_v`; `t':clos_v list`;
     `tra:tra`; `loc:num`; `i:num`; `n:num`; `EL i (es:clos_exp list)`; `args2:clos_v list`;
     `rest2:clos_v list`; `t0:(C,FFI)clos_state`] CLOSCALLPAUX_app_red_cl) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
   SUBGOAL_THEN `clos_state_code (t0:(C,FFI)clos_state) SUBMAP clos_state_code (t1:(C,FFI)clos_state)`
     ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP clos_evaluate_mono o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `res1:(clos_v list,clos_v)result,t1:(C,FFI)clos_state`)) THEN
     REWRITE_TAC[clos_state_INFO.ri_accfupds; clos_dec_clock_code];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`loc_opt:num option`; `fe:clos_exp`; `fargs:clos_v list`; `frest:clos_v list`;
     `clos_dec_clock (LENGTH (CONS (h':clos_v) t') - LENGTH (rest2:clos_v list))
        (s:(abs_calls_state # C,FFI)clos_state)`;
     `r1:(clos_v list,clos_v)result`; `s1:(abs_calls_state # C,FFI)clos_state`;
     `res:(clos_v list,clos_v)result`; `s':(abs_calls_state # C,FFI)clos_state`;
     `EL i (es:clos_exp list)`; `TAKE n (args2:clos_v list)`;
     `clos_dec_clock (LENGTH (CONS (h':clos_v) t') - LENGTH (rest2:clos_v list))
        (t0:(C,FFI)clos_state)`;
     `f':clos_v`; `CONS (h':clos_v) t'`; `rest2:clos_v list`; `t0:(C,FFI)clos_state`; `1`;
     `g:num_set # (num # num # clos_exp) list`; `l:num->bool`;
     `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`; `ck1:num`;
     `res1:(clos_v list,clos_v)result`; `t1:(C,FFI)clos_state`] CLOSCALLPAUX_app_full_cont) THEN
   ASM_REWRITE_TAC[]);;

let CLOSCALLPAUX_cc_app_full_to = prove
 (`!loc_opt f v4 v5 (s:(abs_calls_state # C,FFI)clos_state) fe fargs frest res s' g l
    (t0:(C,FFI)clos_state) f' h' t'.
    dest_closure (clos_state_max_app s) loc_opt f (CONS v4 v5) =
      SOME (Full_app fe fargs frest) /\
    clos_state_clock s < LENGTH (CONS v4 v5) - LENGTH frest /\
    res = Rerr (Rabort Rtimeout_error) /\ s' = clos_state_clock_fupd (K 0) s /\
    code_inv (SOME g) l (clos_state_code s) (clos_state_compile s)
      (clos_state_compile_oracle s) (clos_state_code t0) (clos_state_compile t0)
      (clos_state_compile_oracle t0) /\
    wfv_state g l (clos_state_code t0) s /\ wfg g /\ DISJOINT l (domain (FST g)) /\
    clos_callProof_v_rel g l (clos_state_code t0) f f' /\
    ALL2 (clos_callProof_v_rel g l (clos_state_code t0)) (CONS v4 v5) (CONS h' t') /\
    clos_callProof_state_rel g l s t0
    ==> ?ck res' t g2 l2.
          code_inv (SOME g2) l2 (clos_state_code s') (clos_state_compile s')
            (clos_state_compile_oracle s') (clos_state_code t) (clos_state_compile t)
            (clos_state_compile_oracle t) /\
          wfv_state g2 l2 (clos_state_code t) s' /\
          every_result (ALL (wfv g2 l2 (clos_state_code t))) (wfv g2 l2 (clos_state_code t))
            res /\
          evaluate_app loc_opt f' (CONS h' t')
            (clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) = (res',t) /\
          clos_callProof_state_rel g2 l2 s' t /\
          subg g g2 /\ wfg g2 /\ l SUBSET l2 /\ DISJOINT l2 (domain (FST g2)) /\
          result_rel (ALL2 (clos_callProof_v_rel g2 l2 (clos_state_code t)))
            (clos_callProof_v_rel g2 l2 (clos_state_code t)) res res'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(CLOSCALLPAUX_dcvr `f:clos_v` `CONS v4 v5:clos_v list`
    `clos_state_max_app (s:(abs_calls_state # C,FFI)clos_state)` `loc_opt:num option`
    `CONS (h':clos_v) t'` `Full_app fe fargs frest` `f':clos_v`
    `g:num_set # (num # num # clos_exp) list` `l:num->bool`
    `clos_state_code (t0:(C,FFI)clos_state)`) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x2:app_kind` (CONJUNCTS_THEN2 ASSUME_TAC
    (CLOSCALLPAUX_CHOOSE_NAMES [`fns1:(num # clos_exp) list`; `loc:num`; `i:num`;
       `fns2:(num # clos_exp) list`; `args2:clos_v list`; `rest2:clos_v list`; `n:num`]))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `x2:app_kind`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ALL2] o check (fun th ->
    CLOSCALLPAUX_head_is "ALL2" th && rand (concl th) = `CONS (h':clos_v) t'`)) THEN
  SUBGOAL_THEN `LENGTH (t':clos_v list) = LENGTH (v5:clos_v list) /\
                LENGTH (rest2:clos_v list) = LENGTH (frest:clos_v list) /\
                clos_state_max_app (t0:(C,FFI)clos_state) =
                clos_state_max_app (s:(abs_calls_state # C,FFI)clos_state) /\
                clos_state_clock t0 = clos_state_clock s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_REL_LENGTH; clos_callProof_state_rel_max_app;
                  clos_callProof_state_rel_clock];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
  SUBGOAL_THEN `evaluate_app loc_opt f' (CONS h' t') (t0:(C,FFI)clos_state) =
                (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) t0)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[LENGTH];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`0`; `Rerr (Rabort Rtimeout_error):(clos_v list,clos_v)result`;
    `clos_state_clock_fupd (K 0) (t0:(C,FFI)clos_state)`;
    `g:num_set # (num # num # clos_exp) list`; `l:num->bool`] THEN
  REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock] THEN
  ASM_REWRITE_TAC[LENGTH; clos_state_INFO.ri_accfupds; K_THM; SUBSET_REFL;
                  every_result_def; every_error_result_def; result_rel_def; exc_rel_def] THEN
  ASM_SIMP_TAC[wfg_subg_refl; clos_callProof_state_rel_with_clock] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wfv_state_def]) THEN
  ASM_REWRITE_TAC[wfv_state_def; clos_state_INFO.ri_accfupds]);;


(* calls_correct, case evaluate_app (CONS), full application, not timed out *)
let CLOSCALLPAUX_cc_app_full = prove
 (`!loc_opt f v4 v5 (s:(abs_calls_state # C,FFI)clos_state) fe fargs frest
    r1 s1 res s' g l (t0:(C,FFI)clos_state) f' h' t'.
    dest_closure (clos_state_max_app s) loc_opt f (CONS v4 v5) =
      SOME (Full_app fe fargs frest) /\
    ~(clos_state_clock s < LENGTH (CONS v4 v5) - LENGTH frest) /\
    clos_evaluate ([fe],fargs,clos_dec_clock (LENGTH (CONS v4 v5) - LENGTH frest) s) = (r1,s1) /\
    (!v. r1 = Rval [v] ==> evaluate_app loc_opt v frest s1 = (res,s')) /\
    (!e. r1 = Rerr e ==> res = r1 /\ s' = s1) /\
    (!v s2. clos_evaluate ([fe],fargs,clos_dec_clock (LENGTH (CONS v4 v5) - LENGTH frest) s) =
              (Rval [v],s2)
            ==> CLOSCALLPAUX_cc_Q loc_opt v frest s2) /\
    CLOSCALLPAUX_cc_P ([fe],fargs,clos_dec_clock (LENGTH (CONS v4 v5) - LENGTH frest) s) /\
    ~(res = Rerr (Rabort Rtype_error)) /\
    code_inv (SOME g) l (clos_state_code s) (clos_state_compile s)
      (clos_state_compile_oracle s) (clos_state_code t0) (clos_state_compile t0)
      (clos_state_compile_oracle t0) /\
    wfv g l (clos_state_code t0) f /\ ALL (wfv g l (clos_state_code t0)) (CONS v4 v5) /\
    wfv_state g l (clos_state_code t0) s /\ wfg g /\ DISJOINT l (domain (FST g)) /\
    clos_callProof_v_rel g l (clos_state_code t0) f f' /\
    ALL2 (clos_callProof_v_rel g l (clos_state_code t0)) (CONS v4 v5) (CONS h' t') /\
    clos_callProof_state_rel g l s t0
    ==> ?ck res' t g2 l2.
          code_inv (SOME g2) l2 (clos_state_code s') (clos_state_compile s')
            (clos_state_compile_oracle s') (clos_state_code t) (clos_state_compile t)
            (clos_state_compile_oracle t) /\
          wfv_state g2 l2 (clos_state_code t) s' /\
          every_result (ALL (wfv g2 l2 (clos_state_code t))) (wfv g2 l2 (clos_state_code t))
            res /\
          evaluate_app loc_opt f' (CONS h' t')
            (clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) = (res',t) /\
          clos_callProof_state_rel g2 l2 s' t /\
          subg g g2 /\ wfg g2 /\ l SUBSET l2 /\ DISJOINT l2 (domain (FST g2)) /\
          result_rel (ALL2 (clos_callProof_v_rel g2 l2 (clos_state_code t)))
            (clos_callProof_v_rel g2 l2 (clos_state_code t)) res res'`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(CLOSCALLPAUX_dcvr `f:clos_v` `CONS v4 v5:clos_v list`
    `clos_state_max_app (s:(abs_calls_state # C,FFI)clos_state)` `loc_opt:num option`
    `CONS (h':clos_v) t'` `Full_app fe fargs frest` `f':clos_v`
    `g:num_set # (num # num # clos_exp) list` `l:num->bool`
    `clos_state_code (t0:(C,FFI)clos_state)`) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x2:app_kind` (CONJUNCTS_THEN2 ASSUME_TAC
    (CLOSCALLPAUX_CHOOSE_NAMES [`fns1:(num # clos_exp) list`; `loc:num`; `i:num`;
       `fns2:(num # clos_exp) list`; `args2:clos_v list`; `rest2:clos_v list`; `n:num`]))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `x2:app_kind`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LET_DEF; LET_END_DEF]) THEN
  CLOSCALLPAUX_SPLIT_ASM_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ALL2] o check (fun th ->
    CLOSCALLPAUX_head_is "ALL2" th && rand (concl th) = `CONS (h':clos_v) t'`)) THEN
  SUBGOAL_THEN `LENGTH (t':clos_v list) = LENGTH (v5:clos_v list) /\
                LENGTH (rest2:clos_v list) = LENGTH (frest:clos_v list) /\
                clos_state_max_app (t0:(C,FFI)clos_state) =
                clos_state_max_app (s:(abs_calls_state # C,FFI)clos_state)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_REL_LENGTH; clos_callProof_state_rel_max_app];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (CONS (v4:clos_v) v5) - LENGTH (frest:clos_v list) =
                LENGTH (CONS (h':clos_v) t') - LENGTH (rest2:clos_v list)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REWRITE_TAC[LENGTH]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(ASSUME `clos_state_max_app (t0:(C,FFI)clos_state) =
                clos_state_max_app (s:(abs_calls_state # C,FFI)clos_state)`)]) THEN
  MP_TAC(ISPECL [`clos_state_max_app (t0:(C,FFI)clos_state)`; `loc_opt:num option`; `f:clos_v`;
    `CONS (v4:clos_v) v5`; `fargs:clos_v list`; `frest:clos_v list`;
    `g:num_set # (num # num # clos_exp) list`; `l:num->bool`;
    `clos_state_code (t0:(C,FFI)clos_state)`; `fe:clos_exp`] (GEN_ALL dest_closure_full_wfv)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[recclosure_rel_def; LET_DEF; LET_END_DEF] o
    check (fun th -> CLOSCALLPAUX_head_is "recclosure_rel" th &&
      rand (concl th) = `fns2:(num # clos_exp) list`)) THEN
  STRIP_TAC THEN POP_ASSUM MP_TAC THEN IL1AUX_PAIRARG_TAC THEN COND_CASES_TAC THENL
   [ALL_TAC; IL1AUX_PAIRARG_TAC] THEN STRIP_TAC) THENL
  [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     lhs (concl th) = `fns2:(num # clos_exp) list`)) THEN
   SUBGOAL_THEN `SND (EL i (calls_list tra n' loc (fns1:(num # clos_exp) list))) =
                 clos_Call tra 0 (loc + 2 * i + 1) (GENLIST_Var tra 1 n)` ASSUME_TAC THENL
    [REWRITE_TAC[calls_list_MAPi] THEN ASM_SIMP_TAC[EL_MAPi; FST; SND]; ALL_TAC] THEN
   SUBGOAL_THEN `!v. has_var v (SND (clos_call_free [EL i (es':clos_exp list)])) ==> v < n`
     ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o CONJUNCT2 o GEN_REWRITE_RULE I [LIST_REL_EL_EQN] o
       check (fun th -> CLOSCALLPAUX_head_is "ALL2" th &&
         rand (concl th) = `es':clos_exp list`)) THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
     ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `SND (EL i (calls_list tra n' loc (fns1:(num # clos_exp) list))) =
                 clos_Call tra 0 (loc + 2 * i + 1) (GENLIST_Var tra 1 n)`]) THEN
   MP_TAC(ISPECL [`loc_opt:num option`; `s:(abs_calls_state # C,FFI)clos_state`; `fe:clos_exp`;
     `fargs:clos_v list`; `frest:clos_v list`; `r1:(clos_v list,clos_v)result`;
     `s1:(abs_calls_state # C,FFI)clos_state`; `res:(clos_v list,clos_v)result`;
     `s':(abs_calls_state # C,FFI)clos_state`; `g:num_set # (num # num # clos_exp) list`;
     `l:num->bool`; `t0:(C,FFI)clos_state`; `f':clos_v`; `h':clos_v`; `t':clos_v list`;
     `args2:clos_v list`; `rest2:clos_v list`;
     `if is_Recclosure f' then LENGTH (calls_list tra n' loc (fns1:(num # clos_exp) list)) else 0`;
     `n:num`; `i:num`; `loc:num`; `fns1:(num # clos_exp) list`;
     `g0:num_set # (num # num # clos_exp) list`; `es':clos_exp list`;
     `new_g':num_set # (num # num # clos_exp) list`; `tra:tra`] CLOSCALLPAUX_cc_app_full_cl) THEN
   ASM_REWRITE_TAC[];
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     lhs (concl th) = `fns2:(num # clos_exp) list`)) THEN
   SUBGOAL_THEN `EL i (ZIP (MAP FST (fns1:(num # clos_exp) list)) (es'':clos_exp list)) =
                 (n,EL i es'')` ASSUME_TAC THENL
    [SUBGOAL_THEN `LENGTH (es'':clos_exp list) = LENGTH (fns1:(num # clos_exp) list)` ASSUME_TAC THENL
      [FIRST_ASSUM(MP_TAC o MATCH_MP calls_length o check (fun th -> is_eq (concl th) &&
         rand (concl th) = `es'':clos_exp list,new_g'':num_set # (num # num # clos_exp) list`)) THEN
       REWRITE_TAC[LENGTH_MAP];
       ALL_TAC] THEN
     ASM_SIMP_TAC[EL_ZIP; LENGTH_MAP; EL_MAP; FST];
     ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `EL i (ZIP (MAP FST (fns1:(num # clos_exp) list)) (es'':clos_exp list)) =
                 (n,EL i es'')`; SND]) THEN
   MP_TAC(ISPECL [`loc_opt:num option`; `s:(abs_calls_state # C,FFI)clos_state`; `fe:clos_exp`;
     `fargs:clos_v list`; `frest:clos_v list`; `r1:(clos_v list,clos_v)result`;
     `s1:(abs_calls_state # C,FFI)clos_state`; `res:(clos_v list,clos_v)result`;
     `s':(abs_calls_state # C,FFI)clos_state`; `g:num_set # (num # num # clos_exp) list`;
     `l:num->bool`; `t0:(C,FFI)clos_state`; `f':clos_v`; `h':clos_v`; `t':clos_v list`;
     `args2:clos_v list`; `rest2:clos_v list`;
     `if is_Recclosure f' then LENGTH (ZIP (MAP FST (fns1:(num # clos_exp) list)) (es'':clos_exp list)) else 0`;
     `n:num`; `i:num`; `loc:num`; `fns1:(num # clos_exp) list`;
     `g0:num_set # (num # num # clos_exp) list`; `es'':clos_exp list`;
     `new_g'':num_set # (num # num # clos_exp) list`] CLOSCALLPAUX_cc_app_full_nc) THEN
   ASM_REWRITE_TAC[]]);;

(* calls_correct, case evaluate_app (CONS) (HOL4 evaluate_app_CONS) *)
let CLOSCALLPAUX_cc_app_CONS = prove
 (CLOSCALLPAUX_cc_case 14,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[CLOSCALLPAUX_cc_Q_def] THEN
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN
   MP_TAC(ISPEC `dest_closure (clos_state_max_app (s:(abs_calls_state # C,FFI)clos_state))
                   loc_opt f (CONS v4 v5)` option_nchotomy) THEN
   DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `d:app_kind` ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THENL [MESON_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPEC `d:app_kind` (cases "app_kind")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `pv:clos_v` SUBST_ALL_TAC)
     (X_CHOOSE_THEN `fe:clos_exp` (X_CHOOSE_THEN `fargs:clos_v list`
        (X_CHOOSE_THEN `frest:clos_v list` SUBST_ALL_TAC)))) THEN
   CASE_REWRITE_TAC[]) THENL
  [(STRIP_TAC THEN
   MP_TAC(CLOSCALLPAUX_dcvr `f:clos_v` `CONS v4 v5:clos_v list`
     `clos_state_max_app (s:(abs_calls_state # C,FFI)clos_state)` `loc_opt:num option`
     `args':clos_v list` `Partial_app pv` `f':clos_v`
     `g:num_set # (num # num # clos_exp) list` `l:num->bool`
     `clos_state_code (t0:(C,FFI)clos_state)`) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `x2:app_kind` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `c2:clos_v` STRIP_ASSUME_TAC))) THEN RVEQ_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[LIST_REL_CONS1] o check (fun th ->
     CLOSCALLPAUX_head_is "ALL2" th)) THEN RVEQ_TAC THEN
   SUBGOAL_THEN `LENGTH (t':clos_v list) = LENGTH (v5:clos_v list) /\
                 clos_state_max_app (t0:(C,FFI)clos_state) =
                 clos_state_max_app (s:(abs_calls_state # C,FFI)clos_state) /\
                 clos_state_clock t0 = clos_state_clock s` STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC[LIST_REL_LENGTH; clos_callProof_state_rel_max_app;
                   clos_callProof_state_rel_clock];
     ALL_TAC]) THEN
  (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     rhs (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
   COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC) THENL
  [(RVEQ_TAC THEN
   MAP_EVERY EXISTS_TAC [`0`; `Rerr (Rabort Rtimeout_error):(clos_v list,clos_v)result`;
       `clos_state_clock_fupd (K 0) (t0:(C,FFI)clos_state)`;
       `g:num_set # (num # num # clos_exp) list`; `l:num->bool`] THEN
   REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock] THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THEN
   (RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
   ASM_REWRITE_TAC[LENGTH; clos_state_INFO.ri_accfupds; K_THM; SUBSET_REFL;
                   every_result_def; every_error_result_def; result_rel_def; exc_rel_def] THEN
   ASM_SIMP_TAC[wfg_subg_refl; clos_callProof_state_rel_with_clock] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[wfv_state_def]) THEN
   ASM_REWRITE_TAC[wfv_state_def; clos_state_INFO.ri_accfupds]);
   (RVEQ_TAC THEN
   MAP_EVERY EXISTS_TAC [`0`; `Rval [c2]:(clos_v list,clos_v)result`;
       `clos_dec_clock (LENGTH (CONS (h':clos_v) t')) (t0:(C,FFI)clos_state)`;
       `g:num_set # (num # num # clos_exp) list`; `l:num->bool`] THEN
   REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock] THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
   ASM_REWRITE_TAC[LENGTH; CLOSCALLPAUX_wfv_state_dec_clock; SUBSET_REFL;
                   every_result_def; ALL; result_rel_def; ALL2] THEN
   ASM_SIMP_TAC[wfg_subg_refl; CLOSCALLPAUX_state_rel_dec_clock] THEN
   REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds] THEN
   ASM_REWRITE_TAC[]) THEN
   (SUBGOAL_THEN `dest_closure (clos_state_max_app (s:(abs_calls_state # C,FFI)clos_state)) loc_opt f (CONS v4 v5) = SOME (Partial_app pv) /\ ALL (wfv g l (clos_state_code (t0:(C,FFI)clos_state))) (CONS v4 v5) /\ wfv g l (clos_state_code t0) f` MP_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[GEN_ALL dest_closure_partial_wfv]])];
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[LIST_REL_CONS1] o check (fun th ->
    CLOSCALLPAUX_head_is "ALL2" th)) THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`loc_opt:num option`; `f:clos_v`; `v4:clos_v`; `v5:clos_v list`;
      `s:(abs_calls_state # C,FFI)clos_state`; `fe:clos_exp`; `fargs:clos_v list`;
      `frest:clos_v list`; `res:(clos_v list,clos_v)result`;
      `s':(abs_calls_state # C,FFI)clos_state`; `g:num_set # (num # num # clos_exp) list`;
      `l:num->bool`; `t0:(C,FFI)clos_state`; `f':clos_v`; `h':clos_v`; `t':clos_v list`]
      CLOSCALLPAUX_cc_app_full_to) THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `!v s2. clos_evaluate ([fe],fargs,clos_dec_clock
        (LENGTH (CONS (v4:clos_v) v5) - LENGTH (frest:clos_v list))
        (s:(abs_calls_state # C,FFI)clos_state)) = (Rval [v],s2)
        ==> CLOSCALLPAUX_cc_Q loc_opt v frest s2` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t &&
          fst (dest_const t) = "CLOSCALLPAUX_cc_Q")) (concl th))) THEN
      MAP_EVERY EXISTS_TAC [`fe:clos_exp`; `fargs:clos_v list`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `CLOSCALLPAUX_cc_P ([fe],fargs,clos_dec_clock
        (LENGTH (CONS (v4:clos_v) v5) - LENGTH (frest:clos_v list))
        (s:(abs_calls_state # C,FFI)clos_state))` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t &&
          fst (dest_const t) = "CLOSCALLPAUX_cc_P")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?r1 s1. clos_evaluate ([fe],fargs,clos_dec_clock
        (LENGTH (CONS (v4:clos_v) v5) - LENGTH (frest:clos_v list))
        (s:(abs_calls_state # C,FFI)clos_state)) = (r1,s1)` STRIP_ASSUME_TAC THENL
     [MESON_TAC[PAIR]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(!v. r1 = Rval [v] ==> evaluate_app loc_opt v frest (s1:(abs_calls_state # C,FFI)clos_state) =
             (res,(s':(abs_calls_state # C,FFI)clos_state))) /\
      (!e. r1 = Rerr e ==> res = r1 /\ s' = s1)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
        rhs (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
      CASE_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`loc_opt:num option`; `f:clos_v`; `v4:clos_v`; `v5:clos_v list`;
      `s:(abs_calls_state # C,FFI)clos_state`; `fe:clos_exp`; `fargs:clos_v list`;
      `frest:clos_v list`; `r1:(clos_v list,clos_v)result`;
      `s1:(abs_calls_state # C,FFI)clos_state`; `res:(clos_v list,clos_v)result`;
      `s':(abs_calls_state # C,FFI)clos_state`; `g:num_set # (num # num # clos_exp) list`;
      `l:num->bool`; `t0:(C,FFI)clos_state`; `f':clos_v`; `h':clos_v`; `t':clos_v list`]
      CLOSCALLPAUX_cc_app_full) THEN
    ASM_REWRITE_TAC[]]]);;

(* calls_correct, case Op: primitive operations other than Install and   *)
(* ForceThunk, after the arguments have been evaluated                    *)
let CLOSCALLPAUX_cc_Op_app = prove
 (`!x op e1 env2 vs (s0:(abs_calls_state # C,FFI)clos_state) res s'
    (t0:(C,FFI)clos_state) ck vs' t1 g l g2 l2.
    ~(op = clos_Install) /\ ~(op = clos_ThunkOp ForceThunk) /\
    (!err. clos_do_app op (REVERSE vs) s0 = Rerr err ==> res = Rerr err /\ s' = s0) /\
    (!v s3. clos_do_app op (REVERSE vs) s0 = Rval (v,s3) ==> res = Rval [v] /\ s' = s3) /\
    ~(res = Rerr (Rabort Rtype_error)) /\
    clos_evaluate (e1,env2,clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) =
      (Rval vs',t1) /\
    code_inv (SOME g2) l2 (clos_state_code s0) (clos_state_compile s0)
      (clos_state_compile_oracle s0) (clos_state_code t1) (clos_state_compile t1)
      (clos_state_compile_oracle t1) /\
    wfv_state g2 l2 (clos_state_code t1) s0 /\ subg g g2 /\ wfg g2 /\ l SUBSET l2 /\
    DISJOINT l2 (domain (FST g2)) /\
    ALL (wfv g2 l2 (clos_state_code t1)) vs /\ clos_callProof_state_rel g2 l2 s0 t1 /\
    ALL2 (clos_callProof_v_rel g2 l2 (clos_state_code t1)) vs vs'
    ==> ?ck res' t g3 l3.
          code_inv (SOME g3) l3 (clos_state_code s') (clos_state_compile s')
            (clos_state_compile_oracle s') (clos_state_code t) (clos_state_compile t)
            (clos_state_compile_oracle t) /\
          wfv_state g3 l3 (clos_state_code t) s' /\
          subg g g3 /\ wfg g3 /\ l SUBSET l3 /\ DISJOINT l3 (domain (FST g3)) /\
          every_result (ALL (wfv g3 l3 (clos_state_code t))) (wfv g3 l3 (clos_state_code t))
            res /\
          clos_evaluate ([clos_Op x op e1],env2,
            clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) = (res',t) /\
          clos_callProof_state_rel g3 l3 s' t /\
          result_rel (ALL2 (clos_callProof_v_rel g3 l3 (clos_state_code t)))
            (clos_callProof_v_rel g3 l3 (clos_state_code t)) res res'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(INST [`vs:clos_v list`,`a:clos_v list`;
    `s0:(abs_calls_state # C,FFI)clos_state`,`r:(abs_calls_state # C,FFI)clos_state`;
    `t1:(C,FFI)clos_state`,`t:(C,FFI)clos_state`; `vs':clos_v list`,`v:clos_v list`]
    clos_callProof_do_app_thm) THEN
  MP_TAC(ISPEC `clos_do_app op (REVERSE vs) (s0:(abs_calls_state # C,FFI)clos_state)`
    (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (X_CHOOSE_THEN `p:clos_v # (abs_calls_state # C,FFI)clos_state` ASSUME_TAC)
    (X_CHOOSE_THEN `err:clos_v error_result` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `?w s3. p = (w:clos_v,(s3:(abs_calls_state # C,FFI)clos_state))`
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      (X_CHOOSE_THEN `w':clos_v` (X_CHOOSE_THEN `s3':(C,FFI)clos_state` STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`w:clos_v`; `s3:(abs_calls_state # C,FFI)clos_state`] o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `s3:(abs_calls_state # C,FFI)clos_state`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    MP_TAC(MATCH_MP clos_do_app_const (ASSUME `clos_do_app op (REVERSE vs) (s0:(abs_calls_state # C,FFI)clos_state) = Rval (w,s3)`)) THEN
    MP_TAC(MATCH_MP clos_do_app_const (ASSUME `clos_do_app op (REVERSE vs') (t1:(C,FFI)clos_state) = Rval (w',s3')`)) THEN
    REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `Rval [w']:(clos_v list,clos_v)result`;
      `s3':(C,FFI)clos_state`; `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`] THEN
    ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[every_result_def; ALL; result_rel_def; ALL2] THEN CASE_REWRITE_TAC[];
    MP_TAC(ISPEC `err:clos_v error_result` (cases "error_result")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `ex:clos_v` SUBST_ALL_TAC)
      (X_CHOOSE_THEN `ab:abort` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `ab:abort` (cases "abort")) THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (fun th ->
      if is_exists (concl th) then X_CHOOSE_THEN `fe:final_event` SUBST_ALL_TAC th
      else SUBST_ALL_TAC th)) THEN
    CASE_REWRITE_TAC[distinctness "abort"; injectivity "abort"] THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `Rabort Rtype_error:clos_v error_result` o
        check (fun th -> is_forall (concl th) &&
          not (can (find_term (fun t -> t = `s3:(abs_calls_state # C,FFI)clos_state`)) (concl th)) &&
          can (find_term (fun t -> t = `s':(abs_calls_state # C,FFI)clos_state`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      REWRITE_TAC[UNWIND_THM1] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `Rabort (Rffi_error fe):clos_v error_result` o
        check (fun th -> is_forall (concl th) &&
          not (can (find_term (fun t -> t = `s3:(abs_calls_state # C,FFI)clos_state`)) (concl th)) &&
          can (find_term (fun t -> t = `s':(abs_calls_state # C,FFI)clos_state`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      MAP_EVERY EXISTS_TAC [`ck:num`; `Rerr (Rabort (Rffi_error fe)):(clos_v list,clos_v)result`;
        `t1:(C,FFI)clos_state`; `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`] THEN
      ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[every_result_def; every_error_result_def; result_rel_def; exc_rel_def] THEN
      CASE_REWRITE_TAC[]]]);;

let CLOSCALLPAUX_calls_AppUnit = prove
 (`!t (g:num_set # (num # num # clos_exp) list).
     clos_call_calls [clos_AppUnit (clos_Var t 0)] g = ([clos_AppUnit (clos_Var t 0)],g)`,
  REWRITE_TAC[clos_AppUnit_def; clos_call_calls_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[HD; IS_SOME_DEF]);;
let CLOSCALLPAUX_AppUnit_syntax = prove
 (`!t. every_Fn_SOME [clos_AppUnit (clos_Var t 0)] /\
       every_Fn_vs_NONE [clos_AppUnit (clos_Var t 0)] /\
       code_locs [clos_AppUnit (clos_Var t 0)] = []`,
  REWRITE_TAC[clos_AppUnit_def; every_Fn_SOME_def; every_Fn_vs_NONE_def; code_locs_def;
              LET_DEF; LET_END_DEF; APPEND]);;

let CLOSCALLPAUX_dest_thunk_IsThunk = prove
 (`!vs refs m a.
     clos_dest_thunk vs refs = clos_IsThunk m a <=>
     ?ptr. vs = [clos_RefPtr F ptr] /\ FLOOKUP refs ptr = SOME (clos_Thunk m a)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[clos_dest_thunk_def] THEN CASE_REWRITE_TAC[] THEN
    STRUCT_CASES_TAC(ISPEC `m:thunk_mode` (cases "thunk_mode")) THEN CASE_REWRITE_TAC[]] THEN
  STRUCT_CASES_TAC(ISPEC `vs:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_dest_thunk_def; distinctness "clos_dest_thunk_ret"] THEN
  STRUCT_CASES_TAC(ISPEC `t:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_dest_thunk_def; distinctness "clos_dest_thunk_ret"] THEN
  CASES_ON `h:clos_v` THEN
  REWRITE_TAC[clos_dest_thunk_def; distinctness "clos_dest_thunk_ret"; CONS_11;
              injectivity "clos_v"] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  ASM_REWRITE_TAC[distinctness "clos_dest_thunk_ret"; injectivity "clos_dest_thunk_ret"] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `a1:num` THEN RVEQ_TAC THEN ASM_REWRITE_TAC[]);;

let CLOSCALLPAUX_dest_thunk_NotThunk_rel = prove
 (`!g l (s:(abs_calls_state # C,FFI)clos_state) (t:(C,FFI)clos_state) v v'.
     clos_callProof_state_rel g l s t /\ clos_callProof_v_rel g l (clos_state_code t) v v' /\
     clos_dest_thunk [v] (clos_state_refs s) = clos_NotThunk
     ==> clos_dest_thunk [v'] (clos_state_refs t) = clos_NotThunk`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `clos_callProof_v_rel g l (clos_state_code (t:(C,FFI)clos_state)) v v'` THEN
  CASES_ON `v:clos_v` THEN REWRITE_TAC[clos_callProof_v_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[clos_dest_thunk_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_dest_thunk_def]) THEN
  MP_TAC(INST [`s:(abs_calls_state # C,FFI)clos_state`,`s1:(abs_calls_state # C,FFI)clos_state`;
    `t:(C,FFI)clos_state`,`s2:(C,FFI)clos_state`; `a1:num`,`n:num`;
    `FLOOKUP (clos_state_refs (s:(abs_calls_state # C,FFI)clos_state)) a1`,
    `r1:(clos_v clos_ref)option`] (CONJUNCT1 clos_callProof_state_rel_opt_rel_refs)) THEN
  ASM_REWRITE_TAC[UNWIND_THM1] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `clos_NotThunk`)) THEN
  SPEC_TAC(`FLOOKUP (clos_state_refs (s:(abs_calls_state # C,FFI)clos_state)) a1`,
           `o1:(clos_v clos_ref)option`) THEN
  SPEC_TAC(`FLOOKUP (clos_state_refs (t:(C,FFI)clos_state)) a1`,
           `o2:(clos_v clos_ref)option`) THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `o1:(clos_v clos_ref)option` (cases "option")) THEN
  STRUCT_CASES_TAC(ISPEC `o2:(clos_v clos_ref)option` (cases "option")) THEN
  REWRITE_TAC[OPTREL_THM] THEN CASE_REWRITE_TAC[distinctness "clos_dest_thunk_ret"] THEN
  MAP_EVERY (fun v -> STRUCT_CASES_TAC (ISPEC v (cases "clos_ref")))
    [`a:clos_v clos_ref`; `a':clos_v clos_ref`] THEN
  REWRITE_TAC[clos_ref_rel_def] THEN CASE_REWRITE_TAC[distinctness "clos_dest_thunk_ret"] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[distinctness "clos_dest_thunk_ret"; distinctness "thunk_mode"]);;

let CLOSCALLPAUX_update_thunk_SOME = prove
 (`!vs refs vs2 refs'.
     clos_update_thunk vs refs vs2 = SOME refs' <=>
     ?ptr v w. vs = [clos_RefPtr F ptr] /\ vs2 = [v] /\
               clos_dest_thunk [v] refs = clos_NotThunk /\
               FLOOKUP refs ptr = SOME (clos_Thunk NotEvaluated w) /\
               refs' = refs |+ (ptr,clos_Thunk Evaluated v)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[clos_update_thunk_def; store_thunk_def] THEN
    CASE_REWRITE_TAC[]] THEN
  STRUCT_CASES_TAC(ISPEC `vs:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_update_thunk_def; option_DISTINCT] THEN
  STRUCT_CASES_TAC(ISPEC `t:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_update_thunk_def; option_DISTINCT] THEN
  CASES_ON `h:clos_v` THEN REWRITE_TAC[clos_update_thunk_def; option_DISTINCT] THEN
  STRUCT_CASES_TAC(ISPEC `vs2:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_update_thunk_def; option_DISTINCT] THEN
  STRUCT_CASES_TAC(ISPEC `t:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_update_thunk_def; option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; CONS_11; injectivity "clos_v"] THEN
  REWRITE_TAC[store_thunk_def] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN ASM_MESON_TAC[]);;

let CLOSCALLPAUX_state_rel_refs_fupd = prove
 (`!g l (s:(abs_calls_state # C,FFI)clos_state) (t:(C,FFI)clos_state) r1 r2.
     clos_callProof_state_rel g l s t /\
     fmap_rel (clos_ref_rel (clos_callProof_v_rel g l (clos_state_code t))) r1 r2
     ==> clos_callProof_state_rel g l (clos_state_refs_fupd (K r1) s)
                                      (clos_state_refs_fupd (K r2) t)`,
  REWRITE_TAC[clos_callProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  MESON_TAC[]);;

let CLOSCALLPAUX_wfv_state_refs_thunk = prove
 (`!g l code (s:(A,FFI)clos_state) ptr m v.
     wfv_state g l code s /\ wfv g l code v
     ==> wfv_state g l code
           (clos_state_refs_fupd (K (clos_state_refs s |+ (ptr,clos_Thunk m v))) s)`,
  REWRITE_TAC[wfv_state_def; clos_state_INFO.ri_accfupds; K_THM; FEVERY_ALL_FLOOKUP;
              FLOOKUP_UPDATE] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[o_THM; every_refv_def]);;


(* calls_correct, case Op ForceThunk, thunk not yet evaluated *)
let CLOSCALLPAUX_cc_Op_force_ne = prove
 (`!x e1 env2 vs ptr f (s0:(abs_calls_state # C,FFI)clos_state) r2 s2 res s'
    (t0:(C,FFI)clos_state) ck t1 f' g l g2 l2 gc.
    vs = [clos_RefPtr F ptr] /\
    FLOOKUP (clos_state_refs s0) ptr = SOME (clos_Thunk NotEvaluated f) /\
    clos_evaluate ([clos_AppUnit (clos_Var backend_common_None 0)],[f],s0) = (r2,s2) /\
    (!e. r2 = Rerr e ==> res = r2 /\ s' = s2) /\
    (!vs2. r2 = Rval vs2
           ==> (clos_update_thunk vs (clos_state_refs s2) vs2 = NONE
                ==> res = Rerr (Rabort Rtype_error)) /\
               (!refs. clos_update_thunk vs (clos_state_refs s2) vs2 = SOME refs
                       ==> res = Rval vs2 /\ s' = clos_state_refs_fupd (K refs) s2)) /\
    CLOSCALLPAUX_cc_P ([clos_AppUnit (clos_Var backend_common_None 0)],[f],s0) /\
    ~(res = Rerr (Rabort Rtype_error)) /\
    clos_evaluate (e1,env2,clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) =
      (Rval [clos_RefPtr F ptr],t1) /\
    FLOOKUP (clos_state_refs t1) ptr = SOME (clos_Thunk NotEvaluated f') /\
    clos_callProof_v_rel g2 l2 (clos_state_code t1) f f' /\
    code_inv (SOME g2) l2 (clos_state_code s0) (clos_state_compile s0)
      (clos_state_compile_oracle s0) (clos_state_code t1) (clos_state_compile t1)
      (clos_state_compile_oracle t1) /\
    wfv_state g2 l2 (clos_state_code t1) s0 /\ subg g g2 /\ wfg g2 /\ l SUBSET l2 /\
    DISJOINT l2 (domain (FST g2)) /\
    clos_callProof_state_rel g2 l2 s0 t1 /\
    wfg gc /\ subg gc g /\ code_includes (SND gc) (clos_state_code t1)
    ==> ?ck res' t g3 l3.
          code_inv (SOME g3) l3 (clos_state_code s') (clos_state_compile s')
            (clos_state_compile_oracle s') (clos_state_code t) (clos_state_compile t)
            (clos_state_compile_oracle t) /\
          wfv_state g3 l3 (clos_state_code t) s' /\
          subg g g3 /\ wfg g3 /\ l SUBSET l3 /\ DISJOINT l3 (domain (FST g3)) /\
          every_result (ALL (wfv g3 l3 (clos_state_code t))) (wfv g3 l3 (clos_state_code t))
            res /\
          clos_evaluate ([clos_Op x (clos_ThunkOp ForceThunk) e1],env2,
            clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) = (res',t) /\
          clos_callProof_state_rel g3 l3 s' t /\
          result_rel (ALL2 (clos_callProof_v_rel g3 l3 (clos_state_code t)))
            (clos_callProof_v_rel g3 l3 (clos_state_code t)) res res'`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `~(r2 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` ASSUME_TAC THENL
    [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `Rabort Rtype_error:clos_v error_result` o
       check (fun th -> is_forall (concl th) && is_imp (snd (dest_forall (concl th))) &&
         can (find_term (fun t -> t = `s':(abs_calls_state # C,FFI)clos_state`)) (concl th) &&
         not (can (find_term (fun t -> t = `clos_update_thunk`)) (concl th)))) THEN
     ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `wfv g2 l2 (clos_state_code (t1:(C,FFI)clos_state)) f` ASSUME_TAC THENL
    [UNDISCH_TAC `wfv_state g2 l2 (clos_state_code (t1:(C,FFI)clos_state)) (s0:(abs_calls_state # C,FFI)clos_state)` THEN
     REWRITE_TAC[wfv_state_def] THEN STRIP_TAC THEN
     MP_TAC(ISPECL [`every_refv (wfv g2 l2 (clos_state_code (t1:(C,FFI)clos_state))) o (SND:num # clos_v clos_ref -> clos_v clos_ref)`;
       `clos_state_refs (s0:(abs_calls_state # C,FFI)clos_state)`; `ptr:num`;
       `clos_Thunk NotEvaluated (f:clos_v)`] FEVERY_FLOOKUP) THEN
     ASM_REWRITE_TAC[o_THM; every_refv_def];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSCALLPAUX_cc_P_def] o
     check (fun th -> CLOSCALLPAUX_head_is "CLOSCALLPAUX_cc_P" th)) THEN
   DISCH_THEN(MP_TAC o SPECL [`gc:num_set # (num # num # clos_exp) list`;
     `gc:num_set # (num # num # clos_exp) list`; `[f':clos_v]`; `t1:(C,FFI)clos_state`;
     `[clos_AppUnit (clos_Var backend_common_None 0)]`; `r2:(clos_v list,clos_v)result`;
     `s2:(abs_calls_state # C,FFI)clos_state`;
     `set_of_list (code_locs [clos_AppUnit (clos_Var backend_common_None 0)]) DIFF
      domain (FST (gc:num_set # (num # num # clos_exp) list))`;
     `l2:num->bool`; `g2:num_set # (num # num # clos_exp) list`]) THEN
   ASM_REWRITE_TAC[CLOSCALLPAUX_calls_AppUnit; CLOSCALLPAUX_AppUnit_syntax; ALL; ALL_DISTINCT;
     set_of_list; IMAGE_CLAUSES; DISJOINT_EMPTY; EMPTY_DIFF; EMPTY_SUBSET; MAP] THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL
      [MATCH_MP_TAC subg_trans THEN EXISTS_TAC `g:num_set # (num # num # clos_exp) list` THEN
       ASM_REWRITE_TAC[];
       REWRITE_TAC[clos_callProof_env_rel_def; LENGTH; ALL2] THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck2:num`; `res2:(clos_v list,clos_v)result`;
     `t2:(C,FFI)clos_state`; `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`])) THEN
  (FIRST_ASSUM(MP_TAC o SPEC `ck2:num` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
     CLOSCALLPAUX_evaluate_add_clock_res) o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `(Rval [clos_RefPtr F ptr]:(clos_v list,clos_v)result),(t1:(C,FFI)clos_state)`)) THEN
   REWRITE_TAC[distinctness "result"] THEN DISCH_TAC THEN
   SUBGOAL_THEN `clos_dest_thunk [clos_RefPtr F ptr]
       (clos_state_refs (clos_state_clock_fupd (K (clos_state_clock t1 + ck2))
          (t1:(C,FFI)clos_state))) = clos_IsThunk NotEvaluated f'` ASSUME_TAC THENL
    [REWRITE_TAC[clos_state_INFO.ri_accfupds; CLOSCALLPAUX_dest_thunk_IsThunk] THEN
     EXISTS_TAC `ptr:num` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   MP_TAC(ISPEC `r2:(clos_v list,clos_v)result` (cases "result")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs2:clos_v list` SUBST_ALL_TAC)
     (X_CHOOSE_THEN `err:clos_v error_result` SUBST_ALL_TAC)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[injectivity "result"; distinctness "result"; FORALL_UNWIND_THM1;
     result_rel_Rval; result_rel_Rerr1; every_result_def]) THEN
   REPEAT (FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THENL
    [ALL_TAC;
     FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC o check (fun th -> is_conj (concl th) &&
       lhand (concl th) = `res:(clos_v list,clos_v)result = Rerr err`)) THEN
     FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
       lhs (concl th) = `res2:(clos_v list,clos_v)result`)) THEN
     MAP_EVERY EXISTS_TAC [`ck + ck2:num`; `Rerr e':(clos_v list,clos_v)result`;
       `t2:(C,FFI)clos_state`; `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`] THEN
     ASM_REWRITE_TAC[every_result_def; result_rel_def] THEN
     REPEAT CONJ_TAC THENL
      [ASM_MESON_TAC[subg_trans]; ASM_MESON_TAC[SUBSET_TRANS];
       ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[distinctness "clos_op"] THEN
       REPEAT (CHANGED_TAC (CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]))]]) THEN
  (SUBGOAL_THEN `?refs. clos_update_thunk vs (clos_state_refs (s2:(abs_calls_state # C,FFI)clos_state)) vs2 = SOME refs`
     STRIP_ASSUME_TAC THENL
    [MP_TAC(ISPEC `clos_update_thunk vs (clos_state_refs (s2:(abs_calls_state # C,FFI)clos_state)) vs2`
       (cases "option")) THEN
     STRIP_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `refs:(num,clos_v clos_ref)fmap` o CONJUNCT2 o
     check (fun th -> is_conj (concl th) &&
       can (find_term (fun t -> t = `clos_update_thunk`)) (concl th))) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSCALLPAUX_update_thunk_SOME] o
     check (fun th -> is_eq (concl th) &&
       rhs (concl th) = `SOME (refs:(num,clos_v clos_ref)fmap)`)) THEN
   ASM_REWRITE_TAC[CONS_11; injectivity "clos_v"] THEN
   DISCH_THEN(X_CHOOSE_THEN `ptr':num` (X_CHOOSE_THEN `v:clos_v` (X_CHOOSE_THEN `w:clos_v`
     STRIP_ASSUME_TAC))) THEN
   RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
   REPEAT (FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
   RVEQ_TAC) THEN
  (MP_TAC(INST [`g3:num_set # (num # num # clos_exp) list`,`g:num_set # (num # num # clos_exp) list`;
     `l3:num->bool`,`l:num->bool`; `s2:(abs_calls_state # C,FFI)clos_state`,`s:(abs_calls_state # C,FFI)clos_state`;
     `t2:(C,FFI)clos_state`,`t:(C,FFI)clos_state`; `ptr':num`,`k:num`;
     `clos_Thunk NotEvaluated (w:clos_v)`,`v:clos_v clos_ref`] state_rel_flookup_refs) THEN
   ASM_REWRITE_TAC[clos_ref_rel_simp] THEN
   DISCH_THEN(X_CHOOSE_THEN `rr:clos_v clos_ref` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `b:clos_v` STRIP_ASSUME_TAC))) THEN
   RVEQ_TAC THEN
   MP_TAC(ISPECL [`g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`;
     `s2:(abs_calls_state # C,FFI)clos_state`; `t2:(C,FFI)clos_state`; `v:clos_v`; `h':clos_v`]
     CLOSCALLPAUX_dest_thunk_NotThunk_rel) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN `clos_update_thunk [clos_RefPtr F ptr'] (clos_state_refs (t2:(C,FFI)clos_state)) [h'] =
                 SOME (clos_state_refs t2 |+ (ptr',clos_Thunk Evaluated h'))` ASSUME_TAC THENL
    [REWRITE_TAC[CLOSCALLPAUX_update_thunk_SOME] THEN
     MAP_EVERY EXISTS_TAC [`ptr':num`; `h':clos_v`; `b:clos_v`] THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`ck + ck2:num`; `Rval [h']:(clos_v list,clos_v)result`;
     `clos_state_refs_fupd (K (clos_state_refs t2 |+ (ptr',clos_Thunk Evaluated h')))
        (t2:(C,FFI)clos_state)`;
     `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`] THEN
   REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
   ASM_REWRITE_TAC[every_result_def; result_rel_def; ALL; ALL2] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN
   REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC CLOSCALLPAUX_wfv_state_refs_thunk THEN ASM_REWRITE_TAC[];
     ASM_MESON_TAC[subg_trans];
     ASM_MESON_TAC[SUBSET_TRANS];
     ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[distinctness "clos_op"] THEN
     REPEAT (CHANGED_TAC (CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]));
     MATCH_MP_TAC CLOSCALLPAUX_state_rel_refs_fupd THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC fmap_rel_FUPDATE_same THEN
     ASM_REWRITE_TAC[clos_ref_rel_def] THEN
     ASM_MESON_TAC[clos_callProof_state_rel_def]]));;


(* calls_correct, case Op ForceThunk, after the argument evaluation *)
let CLOSCALLPAUX_cc_Op_force = prove
 (`!x xs env (s:(abs_calls_state # C,FFI)clos_state) vs s0 res s' e1 env2
    (t0:(C,FFI)clos_state) ck vs' t1 g l g2 l2 gc.
    clos_evaluate ([clos_Op x (clos_ThunkOp ForceThunk) xs],env,s) = (res,s') /\
    clos_evaluate (xs,env,s) = (Rval vs,s0) /\
    (!v. clos_dest_thunk vs (clos_state_refs s0) = clos_IsThunk NotEvaluated v
         ==> CLOSCALLPAUX_cc_P ([clos_AppUnit (clos_Var backend_common_None 0)],[v],s0)) /\
    ~(res = Rerr (Rabort Rtype_error)) /\
    clos_evaluate (e1,env2,clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) =
      (Rval vs',t1) /\
    code_inv (SOME g2) l2 (clos_state_code s0) (clos_state_compile s0)
      (clos_state_compile_oracle s0) (clos_state_code t1) (clos_state_compile t1)
      (clos_state_compile_oracle t1) /\
    wfv_state g2 l2 (clos_state_code t1) s0 /\ subg g g2 /\ wfg g2 /\ l SUBSET l2 /\
    DISJOINT l2 (domain (FST g2)) /\
    clos_callProof_state_rel g2 l2 s0 t1 /\
    ALL2 (clos_callProof_v_rel g2 l2 (clos_state_code t1)) vs vs' /\
    wfg gc /\ subg gc g /\ code_includes (SND gc) (clos_state_code t1)
    ==> ?ck res' t g3 l3.
          code_inv (SOME g3) l3 (clos_state_code s') (clos_state_compile s')
            (clos_state_compile_oracle s') (clos_state_code t) (clos_state_compile t)
            (clos_state_compile_oracle t) /\
          wfv_state g3 l3 (clos_state_code t) s' /\
          subg g g3 /\ wfg g3 /\ l SUBSET l3 /\ DISJOINT l3 (domain (FST g3)) /\
          every_result (ALL (wfv g3 l3 (clos_state_code t))) (wfv g3 l3 (clos_state_code t))
            res /\
          clos_evaluate ([clos_Op x (clos_ThunkOp ForceThunk) e1],env2,
            clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) = (res',t) /\
          clos_callProof_state_rel g3 l3 s' t /\
          result_rel (ALL2 (clos_callProof_v_rel g3 l3 (clos_state_code t)))
            (clos_callProof_v_rel g3 l3 (clos_state_code t)) res res'`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     rand (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
   GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [clos_evaluate_def] THEN
   ASM_REWRITE_TAC[distinctness "clos_op"] THEN CASE_REWRITE_TAC[] THEN
   MP_TAC(ISPEC `clos_dest_thunk vs (clos_state_refs (s0:(abs_calls_state # C,FFI)clos_state))`
     (cases "clos_dest_thunk_ret")) THEN
   DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (fun th ->
     if is_exists (concl th) then
       X_CHOOSE_THEN `m:thunk_mode` (X_CHOOSE_THEN `v:clos_v` ASSUME_TAC) th
     else ASSUME_TAC th)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
    [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPEC `m:thunk_mode` (cases "thunk_mode")) THEN
   DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
   FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSCALLPAUX_dest_thunk_IsThunk] o
     check (fun th -> is_eq (concl th) &&
       can (find_term (fun t -> t = `clos_dest_thunk`)) (lhs (concl th)) &&
       is_comb (rhs (concl th)))) THEN
   DISCH_THEN(X_CHOOSE_THEN `ptr:num` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     lhs (concl th) = `vs:clos_v list`)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
   REPEAT (FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[clos_callProof_v_rel_def]) THEN
   RVEQ_TAC) THENL
  [MP_TAC(INST [`g2:num_set # (num # num # clos_exp) list`,`g:num_set # (num # num # clos_exp) list`;
     `l2:num->bool`,`l:num->bool`; `s0:(abs_calls_state # C,FFI)clos_state`,`s:(abs_calls_state # C,FFI)clos_state`;
     `t1:(C,FFI)clos_state`,`t:(C,FFI)clos_state`; `ptr:num`,`k:num`;
     `clos_Thunk Evaluated (v:clos_v)`,`v:clos_v clos_ref`] state_rel_flookup_refs) THEN
   ASM_REWRITE_TAC[clos_ref_rel_simp] THEN
   DISCH_THEN(X_CHOOSE_THEN `rr:clos_v clos_ref` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `w:clos_v` STRIP_ASSUME_TAC))) THEN
   RVEQ_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   SUBGOAL_THEN `wfv g2 l2 (clos_state_code (t1:(C,FFI)clos_state)) v` ASSUME_TAC THENL
    [UNDISCH_TAC `wfv_state g2 l2 (clos_state_code (t1:(C,FFI)clos_state))
                    (s0:(abs_calls_state # C,FFI)clos_state)` THEN
     REWRITE_TAC[wfv_state_def] THEN STRIP_TAC THEN
     MP_TAC(ISPECL [`every_refv (wfv g2 l2 (clos_state_code (t1:(C,FFI)clos_state))) o
         (SND:num # clos_v clos_ref -> clos_v clos_ref)`;
       `clos_state_refs (s0:(abs_calls_state # C,FFI)clos_state)`; `ptr:num`;
       `clos_Thunk Evaluated (v:clos_v)`] FEVERY_FLOOKUP) THEN
     ASM_REWRITE_TAC[o_THM; every_refv_def];
     ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`ck:num`; `Rval [w]:(clos_v list,clos_v)result`;
     `t1:(C,FFI)clos_state`; `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`] THEN
   ASM_REWRITE_TAC[every_result_def; ALL; result_rel_def; ALL2] THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[distinctness "clos_op"] THEN
   CASE_REWRITE_TAC[] THEN
   SUBGOAL_THEN `clos_dest_thunk [clos_RefPtr F ptr] (clos_state_refs (t1:(C,FFI)clos_state)) =
                 clos_IsThunk Evaluated w` SUBST1_TAC THENL
    [REWRITE_TAC[CLOSCALLPAUX_dest_thunk_IsThunk] THEN EXISTS_TAC `ptr:num` THEN
     ASM_REWRITE_TAC[];
     CASE_REWRITE_TAC[]];
   MP_TAC(INST [`g2:num_set # (num # num # clos_exp) list`,`g:num_set # (num # num # clos_exp) list`;
     `l2:num->bool`,`l:num->bool`; `s0:(abs_calls_state # C,FFI)clos_state`,`s:(abs_calls_state # C,FFI)clos_state`;
     `t1:(C,FFI)clos_state`,`t:(C,FFI)clos_state`; `ptr:num`,`k:num`;
     `clos_Thunk NotEvaluated (v:clos_v)`,`v:clos_v clos_ref`] state_rel_flookup_refs) THEN
   ASM_REWRITE_TAC[clos_ref_rel_simp] THEN
   DISCH_THEN(X_CHOOSE_THEN `rr:clos_v clos_ref` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `f':clos_v` STRIP_ASSUME_TAC))) THEN
   RVEQ_TAC THEN
   SUBGOAL_THEN `CLOSCALLPAUX_cc_P ([clos_AppUnit (clos_Var backend_common_None 0)],[v],
                   (s0:(abs_calls_state # C,FFI)clos_state))` ASSUME_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `?r2 s2. clos_evaluate ([clos_AppUnit (clos_Var backend_common_None 0)],[v],
       (s0:(abs_calls_state # C,FFI)clos_state)) = (r2,s2)` STRIP_ASSUME_TAC THENL
    [MESON_TAC[PAIR]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN
    `(!e. (r2:(clos_v list,clos_v)result) = Rerr e ==> res = r2 /\ s' = (s2:(abs_calls_state # C,FFI)clos_state)) /\
     (!vs2. r2 = Rval vs2
            ==> (clos_update_thunk [clos_RefPtr F ptr] (clos_state_refs s2) vs2 = NONE
                 ==> res = Rerr (Rabort Rtype_error)) /\
                (!refs. clos_update_thunk [clos_RefPtr F ptr] (clos_state_refs s2) vs2 = SOME refs
                        ==> res = Rval vs2 /\ s' = clos_state_refs_fupd (K refs) s2))`
     STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
     CASE_REWRITE_TAC[PAIR_EQ] THENL
      [MESON_TAC[];
       DISCH_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
       FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
         rand (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
       ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN TRY (MESON_TAC[] THEN NO_TAC) THEN
       STRIP_TAC THEN
       UNDISCH_TAC `~(res = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` THEN
       ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`x:tra`; `e1:clos_exp list`; `env2:clos_v list`;
     `[clos_RefPtr F ptr]`; `ptr:num`; `v:clos_v`; `s0:(abs_calls_state # C,FFI)clos_state`;
     `r2:(clos_v list,clos_v)result`; `s2:(abs_calls_state # C,FFI)clos_state`;
     `res:(clos_v list,clos_v)result`; `s':(abs_calls_state # C,FFI)clos_state`;
     `t0:(C,FFI)clos_state`; `ck:num`; `t1:(C,FFI)clos_state`; `f':clos_v`;
     `g:num_set # (num # num # clos_exp) list`; `l:num->bool`;
     `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`;
     `gc:num_set # (num # num # clos_exp) list`] CLOSCALLPAUX_cc_Op_force_ne) THEN
   ASM_REWRITE_TAC[]]);;

let CLOSCALLPAUX_do_install_char = prove
 (`!vs (s:(C,FFI)clos_state) r s'.
     clos_do_install vs s = (r,s') /\ ~(r = Rerr (Rabort Rtype_error))
     ==> ?v1 v2 bytes data cfg exps aux cfg'.
           vs = [v1; v2] /\ clos_v_to_bytes v1 = SOME bytes /\ clos_v_to_words v2 = SOME data /\
           clos_state_compile_oracle s 0 = (cfg,exps,aux) /\
           DISJOINT (FDOM (clos_state_code s)) (set_of_list (MAP FST aux)) /\
           ALL_DISTINCT (MAP FST aux) /\
           clos_state_compile s cfg (exps,aux) = SOME (bytes,data,cfg') /\
           FST (shift_seq 1 (clos_state_compile_oracle s) 0) = cfg' /\ ~(exps = []) /\
           s' = clos_state_code_fupd (K (clos_state_code s |++ aux))
                  (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle s)))
                    (clos_state_clock_fupd (K (clos_state_clock s - 1)) s)) /\
           r = (if clos_state_clock s = 0 then Rerr (Rabort Rtimeout_error) else Rval exps)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_install_def; LET_DEF; LET_END_DEF] THEN
   REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC ORELSE IL1AUX_PAIRARG_TAC) THEN
   REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   TRY (FIRST_ASSUM(CONTR_TAC o REWRITE_RULE[] o check (is_neg o concl)) THEN NO_TAC) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[]) THEN CLOSCALLPAUX_SPLIT_ASM_TAC THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[]);;

let CLOSCALLPAUX_do_install_eq = prove
 (`!v1 v2 (t:(C,FFI)clos_state) bytes data cfg exps aux cfg'.
     clos_v_to_bytes v1 = SOME bytes /\ clos_v_to_words v2 = SOME data /\
     clos_state_compile_oracle t 0 = (cfg,exps,aux) /\
     DISJOINT (FDOM (clos_state_code t)) (set_of_list (MAP FST aux)) /\
     ALL_DISTINCT (MAP FST aux) /\
     clos_state_compile t cfg (exps,aux) = SOME (bytes,data,cfg') /\
     FST (shift_seq 1 (clos_state_compile_oracle t) 0) = cfg' /\ ~(exps = [])
     ==> clos_do_install [v1; v2] t =
         ((if clos_state_clock t = 0 then Rerr (Rabort Rtimeout_error) else Rval exps),
          clos_state_code_fupd (K (clos_state_code t |++ aux))
            (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle t)))
              (clos_state_clock_fupd (K (clos_state_clock t - 1)) t)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[clos_do_install_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let CLOSCALLPAUX_ALL_LAST = prove
 (`!(P:A->bool) l. ALL P l /\ ~(l = []) ==> P (LAST l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[MEM_LAST]);;


(* calls_correct, case Op Install, after the argument evaluation *)
let CLOSCALLPAUX_cc_Op_install = prove
 (`!x xs env (s:(abs_calls_state # C,FFI)clos_state) vs s0 res s' e1 env2
    (t0:(C,FFI)clos_state) ck vs' t1 g l g2 l2.
    clos_evaluate ([clos_Op x clos_Install xs],env,s) = (res,s') /\
    clos_evaluate (xs,env,s) = (Rval vs,s0) /\
    (!es s4. clos_do_install (REVERSE vs) s0 = (Rval es,s4) ==> CLOSCALLPAUX_cc_P (es,[],s4)) /\
    ~(res = Rerr (Rabort Rtype_error)) /\
    clos_evaluate (e1,env2,clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) =
      (Rval vs',t1) /\
    code_inv (SOME g2) l2 (clos_state_code s0) (clos_state_compile s0)
      (clos_state_compile_oracle s0) (clos_state_code t1) (clos_state_compile t1)
      (clos_state_compile_oracle t1) /\
    wfv_state g2 l2 (clos_state_code t1) s0 /\ subg g g2 /\ wfg g2 /\ l SUBSET l2 /\
    DISJOINT l2 (domain (FST g2)) /\
    clos_callProof_state_rel g2 l2 s0 t1 /\
    ALL2 (clos_callProof_v_rel g2 l2 (clos_state_code t1)) vs vs'
    ==> ?ck res' t g3 l3.
          code_inv (SOME g3) l3 (clos_state_code s') (clos_state_compile s')
            (clos_state_compile_oracle s') (clos_state_code t) (clos_state_compile t)
            (clos_state_compile_oracle t) /\
          wfv_state g3 l3 (clos_state_code t) s' /\
          subg g g3 /\ wfg g3 /\ l SUBSET l3 /\ DISJOINT l3 (domain (FST g3)) /\
          every_result (ALL (wfv g3 l3 (clos_state_code t))) (wfv g3 l3 (clos_state_code t))
            res /\
          clos_evaluate ([clos_Op x clos_Install e1],env2,
            clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) = (res',t) /\
          clos_callProof_state_rel g3 l3 s' t /\
          result_rel (ALL2 (clos_callProof_v_rel g3 l3 (clos_state_code t)))
            (clos_callProof_v_rel g3 l3 (clos_state_code t)) res res'`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     rand (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
   GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [clos_evaluate_def] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   SUBGOAL_THEN `?ri si. clos_do_install (REVERSE vs) (s0:(abs_calls_state # C,FFI)clos_state) =
                         (ri,si)` STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN `~(ri = Rerr (Rabort Rtype_error):(clos_exp list,clos_v)result)` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
     CASE_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`REVERSE vs:clos_v list`; `s0:(abs_calls_state # C,FFI)clos_state`;
     `ri:(clos_exp list,clos_v)result`; `si:(abs_calls_state # C,FFI)clos_state`]
     CLOSCALLPAUX_do_install_char) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`v1:clos_v`; `v2:clos_v`; `bytes:(8 word)list`;
     `data:(64 word)list`; `cfg:num_set # C`; `exps:clos_exp list`;
     `aux:(num # num # clos_exp) list`; `ncfg:num_set # C`]) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP (ISPEC `0` code_inv_k) o check (fun th ->
     CLOSCALLPAUX_head_is "code_inv" th && rand (concl th) =
       `clos_state_compile_oracle (t1:(C,FFI)clos_state)`)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[clos_callProof_syntax_ok_def] THEN STRIP_TAC THEN
   ALL_TAC) THEN
  (SUBGOAL_THEN `?cfgt progst. clos_state_compile_oracle (t1:(C,FFI)clos_state) 0 = (cfgt,progst)`
     STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     lhs (concl th) = `aux:(num # num # clos_exp) list`)) THEN
   MP_TAC(INST [`g2:num_set # (num # num # clos_exp) list`,`g1:num_set # (num # num # clos_exp) list`;
     `l2:num->bool`,`l1:num->bool`;
     `s0:(abs_calls_state # C,FFI)clos_state`,`r:(abs_calls_state # C,FFI)clos_state`;
     `t1:(C,FFI)clos_state`,`t:(C,FFI)clos_state`;
     `[]:(num # num # clos_exp) list`,`aux:(num # num # clos_exp) list`;
     `ncfg:num_set # C`,`next_cfg:num_set # C`; `cfgt:C`,`cfg':C`;
     `progst:clos_exp list # (num # num # clos_exp) list`,
     `progs:clos_exp list # (num # num # clos_exp) list`] code_rel_state_rel_install) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CLOSCALLPAUX_CHOOSE_NAMES [`exp1:clos_exp list`; `aux1:(num # num # clos_exp) list`;
        `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`; `ncfgt:C`]))) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     lhs (concl th) = `progst:clos_exp list # (num # num # clos_exp) list`)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[SND; FUPDATE_LIST_THM]) THEN
   ALL_TAC) THEN
  (SUBGOAL_THEN `?v1' v2'. REVERSE vs' = [v1';v2'] /\ clos_v_to_bytes v1' = SOME bytes /\
                           clos_v_to_words v2' = SOME data` STRIP_ASSUME_TAC THENL
    [MP_TAC(ISPECL [`clos_callProof_v_rel g2 l2 (clos_state_code (t1:(C,FFI)clos_state))`;
       `vs:clos_v list`; `vs':clos_v list`] EVERY2_REVERSE) THEN
     ASM_REWRITE_TAC[LIST_REL_CONS1; LIST_REL_NIL] THEN STRIP_TAC THEN
     ASM_REWRITE_TAC[CONS_11] THEN
     ASM_MESON_TAC[GEN_ALL v_to_bytes_thm; GEN_ALL v_to_words_thm];
     ALL_TAC] THEN
   SUBGOAL_THEN `~(exp1:clos_exp list = [])` ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP calls_length o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `exp1:clos_exp list,g3:num_set # (num # num # clos_exp) list`)) THEN
     UNDISCH_TAC `~(exps:clos_exp list = [])` THEN
     REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC;
     ALL_TAC] THEN
   SUBGOAL_THEN
    `!k. clos_do_install (REVERSE vs') (clos_state_clock_fupd (K (clos_state_clock t1 + k))
           (t1:(C,FFI)clos_state)) =
         ((if clos_state_clock t1 + k = 0 then Rerr (Rabort Rtimeout_error) else Rval exp1),
          clos_state_clock_fupd (K ((clos_state_clock t1 + k) - 1))
            (clos_state_code_fupd (K (clos_state_code t1 |++ aux1))
              (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle t1))) t1)))`
    ASSUME_TAC THENL
    [GEN_TAC THEN ASM_REWRITE_TAC[] THEN
     MP_TAC(ISPECL [`v1':clos_v`; `v2':clos_v`;
       `clos_state_clock_fupd (K (clos_state_clock t1 + k)) (t1:(C,FFI)clos_state)`;
       `bytes:(8 word)list`; `data:(64 word)list`; `cfgt:C`; `exp1:clos_exp list`;
       `aux1:(num # num # clos_exp) list`; `ncfgt:C`] CLOSCALLPAUX_do_install_eq) THEN
     ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC[PAIR_EQ; clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `clos_state_clock (s0:(abs_calls_state # C,FFI)clos_state) =
                 clos_state_clock (t1:(C,FFI)clos_state)` ASSUME_TAC THENL
    [ASM_MESON_TAC[clos_callProof_state_rel_clock]; ALL_TAC] THEN
   SUBGOAL_THEN `wfg (g3:num_set # (num # num # clos_exp) list) /\
                 code_includes (SND g3) (clos_state_code (t1:(C,FFI)clos_state) |++ aux1) /\
                 DISJOINT (IMAGE SUC (set_of_list (code_locs exps)))
                   (set_of_list (MAP FST (SND (g2:num_set # (num # num # clos_exp) list))))`
     STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `DISJOINT (IMAGE SUC (set_of_list (code_locs exps)))
                    (FDOM (clos_state_code (t1:(C,FFI)clos_state)))` THEN
     UNDISCH_TAC `code_inv (SOME (g3:num_set # (num # num # clos_exp) list)) l3
        (clos_state_code (s0:(abs_calls_state # C,FFI)clos_state)) (clos_state_compile s0)
        (shift_seq 1 (clos_state_compile_oracle s0))
        (clos_state_code (t1:(C,FFI)clos_state) |++ aux1) (clos_state_compile t1)
        (shift_seq 1 (clos_state_compile_oracle t1))` THEN
     UNDISCH_TAC `code_inv (SOME (g2:num_set # (num # num # clos_exp) list)) l2
        (clos_state_code (s0:(abs_calls_state # C,FFI)clos_state)) (clos_state_compile s0)
        (clos_state_compile_oracle s0) (clos_state_code (t1:(C,FFI)clos_state))
        (clos_state_compile t1) (clos_state_compile_oracle t1)` THEN
     REWRITE_TAC[code_inv_def; IS_SOME_DEF; option_INJ] THEN
     REPEAT STRIP_TAC THEN RVEQ_TAC THEN
     ASM_REWRITE_TAC[SND; code_includes_def; ALOOKUP_EQ_FLOOKUP] THEN
     UNDISCH_TAC `DISJOINT (IMAGE SUC (set_of_list (code_locs exps)))
                    (FDOM (clos_state_code (t1:(C,FFI)clos_state)))` THEN
     ASM_REWRITE_TAC[FDOM_alist_to_fmap];
     ALL_TAC] THEN
   SUBGOAL_THEN `wfv_state g3 l3 (clos_state_code (t1:(C,FFI)clos_state) |++ aux1)
                   (s0:(abs_calls_state # C,FFI)clos_state)` ASSUME_TAC THENL
    [MATCH_MP_TAC(GEN_ALL wfv_state_subg) THEN
     MAP_EVERY EXISTS_TAC [`clos_state_code (t1:(C,FFI)clos_state)`;
       `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
    `si = clos_state_clock_fupd (K (clos_state_clock (s0:(abs_calls_state # C,FFI)clos_state) - 1))
            (clos_state_code_fupd (K (clos_state_code s0))
              (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle s0))) s0))`
     ASSUME_TAC THENL
    [ASM_REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM];
     ALL_TAC] THEN
   ASM_CASES_TAC `clos_state_clock (s0:(abs_calls_state # C,FFI)clos_state) = 0` THENL
    [SUBGOAL_THEN `clos_state_clock (t1:(C,FFI)clos_state) = 0` ASSUME_TAC THENL
      [FIRST_ASSUM(MP_TAC o SYM o check (fun th -> concl th =
         `clos_state_clock (s0:(abs_calls_state # C,FFI)clos_state) =
          clos_state_clock (t1:(C,FFI)clos_state)`)) THEN
       REWRITE_TAC[ASSUME `clos_state_clock (s0:(abs_calls_state # C,FFI)clos_state) = 0`];
       ALL_TAC] THEN
     FIRST_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall (concl th) &&
       can (find_term (fun t -> is_const t && fst (dest_const t) = "clos_do_install")) (concl th))) THEN
     REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock] THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
     DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
     MAP_EVERY EXISTS_TAC [`ck:num`; `Rerr (Rabort Rtimeout_error):(clos_v list,clos_v)result`;
       `clos_state_clock_fupd (K (clos_state_clock (t1:(C,FFI)clos_state) - 1))
          (clos_state_code_fupd (K (clos_state_code t1 |++ aux1))
            (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle t1))) t1))`;
       `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`] THEN
     ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM; every_result_def;
       every_error_result_def; result_rel_def; exc_rel_def] THEN
     REPEAT CONJ_TAC THENL
      [UNDISCH_TAC `wfv_state g3 l3 (clos_state_code (t1:(C,FFI)clos_state) |++ aux1)
                      (s0:(abs_calls_state # C,FFI)clos_state)` THEN
       REWRITE_TAC[wfv_state_def; clos_state_INFO.ri_accfupds; K_THM];
       MATCH_MP_TAC subg_trans THEN EXISTS_TAC `g2:num_set # (num # num # clos_exp) list` THEN
       ASM_REWRITE_TAC[];
       MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l2:num->bool` THEN ASM_REWRITE_TAC[];
       ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
       REPEAT (CHANGED_TAC (CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]));
       SUBGOAL_THEN `!c a b (s:(abs_calls_state # C,FFI)clos_state).
           clos_state_code_fupd (K a) (clos_state_compile_oracle_fupd (K b)
             (clos_state_clock_fupd (K c) s)) =
           clos_state_clock_fupd (K c) (clos_state_code_fupd (K a)
             (clos_state_compile_oracle_fupd (K b) s))` (fun th -> REWRITE_TAC[th]) THENL
        [REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM];
         ALL_TAC] THEN
       MATCH_MP_TAC clos_callProof_state_rel_with_clock THEN ASM_REWRITE_TAC[]];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `!c a b (s:(abs_calls_state # C,FFI)clos_state).
       clos_state_code_fupd (K a) (clos_state_compile_oracle_fupd (K b)
         (clos_state_clock_fupd (K c) s)) =
       clos_state_clock_fupd (K c) (clos_state_code_fupd (K a)
         (clos_state_compile_oracle_fupd (K b) s))` ASSUME_TAC THENL
    [REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     rand (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   SUBGOAL_THEN `?r3 s3. clos_evaluate (exps,[],
       clos_state_clock_fupd (K (clos_state_clock (t1:(C,FFI)clos_state) - 1))
         (clos_state_code_fupd (K (clos_state_code (s0:(abs_calls_state # C,FFI)clos_state)))
           (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle s0))) s0))) =
       (r3,s3)` STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN `~(r3 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
     CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
     UNDISCH_TAC `~(res = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`exps:clos_exp list`; `si:(abs_calls_state # C,FFI)clos_state`] o
     check (fun th -> is_forall (concl th) &&
       can (find_term (fun t -> is_const t && fst (dest_const t) = "CLOSCALLPAUX_cc_P")) (concl th))) THEN
   ASM_REWRITE_TAC[CLOSCALLPAUX_cc_P_def] THEN
   DISCH_THEN(MP_TAC o SPECL [`g2:num_set # (num # num # clos_exp) list`;
     `g3:num_set # (num # num # clos_exp) list`; `[]:clos_v list`;
     `clos_state_clock_fupd (K (clos_state_clock (t1:(C,FFI)clos_state) - 1))
        (clos_state_code_fupd (K (clos_state_code t1 |++ aux1))
          (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle t1))) t1))`;
     `exp1:clos_exp list`; `r3:(clos_v list,clos_v)result`;
     `s3:(abs_calls_state # C,FFI)clos_state`;
     `set_of_list (code_locs exps) DIFF domain (FST (g3:num_set # (num # num # clos_exp) list))`;
     `l3:num->bool`; `g3:num_set # (num # num # clos_exp) list`]) THEN
   ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM; ALL; MAP] THEN
   ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
      [UNDISCH_TAC `wfv_state g3 l3 (clos_state_code (t1:(C,FFI)clos_state) |++ aux1)
                      (s0:(abs_calls_state # C,FFI)clos_state)` THEN
       REWRITE_TAC[wfv_state_def; clos_state_INFO.ri_accfupds; K_THM];
       MATCH_MP_TAC wfg_subg_refl THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[clos_callProof_env_rel_def; LENGTH; ALL2];
       MATCH_MP_TAC clos_callProof_state_rel_with_clock THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck3:num`; `res3:(clos_v list,clos_v)result`;
     `t3:(C,FFI)clos_state`; `g4:num_set # (num # num # clos_exp) list`; `l4:num->bool`])) THEN
  (FIRST_ASSUM(MP_TAC o SPEC `ck3:num` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
     CLOSCALLPAUX_evaluate_add_clock_res) o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `(Rval vs':(clos_v list,clos_v)result),(t1:(C,FFI)clos_state)`)) THEN
   REWRITE_TAC[distinctness "result"] THEN DISCH_TAC THEN
   SUBGOAL_THEN `~(clos_state_clock (t1:(C,FFI)clos_state) = 0)` ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o SYM o check (fun th -> concl th =
       `clos_state_clock (s0:(abs_calls_state # C,FFI)clos_state) =
        clos_state_clock (t1:(C,FFI)clos_state)`)) THEN
     DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   FIRST_ASSUM(MP_TAC o SPEC `ck3:num` o check (fun th -> is_forall (concl th) &&
     can (find_term (fun t -> is_const t && fst (dest_const t) = "clos_do_install")) (concl th))) THEN
   REWRITE_TAC[ADD_EQ_0; ASSUME `~(clos_state_clock (t1:(C,FFI)clos_state) = 0)`] THEN
   DISCH_TAC THEN
   SUBGOAL_THEN
    `clos_state_clock_fupd (K ((clos_state_clock (t1:(C,FFI)clos_state) + ck3) - 1))
       (clos_state_code_fupd (K (clos_state_code t1 |++ aux1))
         (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle t1))) t1)) =
     clos_state_clock_fupd (K (clos_state_clock t1 - 1 + ck3))
       (clos_state_clock_fupd (K (clos_state_clock t1 - 1))
         (clos_state_code_fupd (K (clos_state_code t1 |++ aux1))
           (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle t1))) t1)))`
     ASSUME_TAC THENL
    [REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM] THEN
     ASM_ARITH_TAC;
     ALL_TAC] THEN
   MP_TAC(ISPEC `r3:(clos_v list,clos_v)result` (cases "result")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs3:clos_v list` SUBST_ALL_TAC)
     (X_CHOOSE_THEN `err:clos_v error_result` SUBST_ALL_TAC)) THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ; result_rel_Rval; result_rel_Rerr1; every_result_def]) THEN
   REPEAT (FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl)))) THENL
  [FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o check (fun th -> is_conj (concl th) &&
     lhand (concl th) = `(Rval [LAST vs3]:(clos_v list,clos_v)result) = res`)) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     lhs (concl th) = `res3:(clos_v list,clos_v)result`)) THEN
   SUBGOAL_THEN `~(vs3:clos_v list = [])` ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP clos_evaluate_IMP_LENGTH o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `(Rval vs3:(clos_v list,clos_v)result),(s3:(abs_calls_state # C,FFI)clos_state)`)) THEN
     UNDISCH_TAC `~(exps:clos_exp list = [])` THEN REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC;
     ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`ck + ck3:num`; `Rval [LAST v']:(clos_v list,clos_v)result`;
     `t3:(C,FFI)clos_state`; `g4:num_set # (num # num # clos_exp) list`; `l4:num->bool`] THEN
   ASM_REWRITE_TAC[every_result_def; ALL; result_rel_def; ALL2] THEN
   REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC subg_trans THEN EXISTS_TAC `g3:num_set # (num # num # clos_exp) list` THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC subg_trans THEN
     EXISTS_TAC `g2:num_set # (num # num # clos_exp) list` THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l3:num->bool` THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l2:num->bool` THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC CLOSCALLPAUX_ALL_LAST THEN ASM_REWRITE_TAC[];
     ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
     REPEAT (CHANGED_TAC (CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]));
     MATCH_MP_TAC LIST_REL_LAST THEN ASM_REWRITE_TAC[]];
   FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o check (fun th -> is_conj (concl th) &&
     lhand (concl th) = `(Rerr err:(clos_v list,clos_v)result) = res`)) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     lhs (concl th) = `res3:(clos_v list,clos_v)result`)) THEN
   MAP_EVERY EXISTS_TAC [`ck + ck3:num`; `Rerr e':(clos_v list,clos_v)result`;
     `t3:(C,FFI)clos_state`; `g4:num_set # (num # num # clos_exp) list`; `l4:num->bool`] THEN
   ASM_REWRITE_TAC[every_result_def; result_rel_def] THEN
   REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC subg_trans THEN EXISTS_TAC `g3:num_set # (num # num # clos_exp) list` THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC subg_trans THEN
     EXISTS_TAC `g2:num_set # (num # num # clos_exp) list` THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l3:num->bool` THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l2:num->bool` THEN ASM_REWRITE_TAC[];
     ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
     REPEAT (CHANGED_TAC (CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]))]]);;

(* calls_correct, case Op (HOL4 "Op") *)
let CLOSCALLPAUX_cc_Op = prove
 (CLOSCALLPAUX_cc_case 7,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[CLOSCALLPAUX_cc_P_def] THEN
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC[clos_call_calls_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   IL1AUX_PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[code_locs_def; every_Fn_SOME_def; every_Fn_vs_NONE_def]) THEN
   SUBGOAL_THEN `?r0 s0. clos_evaluate (xs,env,(s:(abs_calls_state # C,FFI)clos_state)) = (r0,s0)`
     STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC]) THEN
  (SUBGOAL_THEN `~(r0 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN
     UNDISCH_TAC `clos_evaluate ([clos_Op x op xs],env,(s:(abs_calls_state # C,FFI)clos_state)) =
                  (res,s')` THEN
     GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [clos_evaluate_def] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
     STRIP_TAC THEN
     UNDISCH_TAC `~(res = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `clos_callProof_env_rel (clos_callProof_v_rel g1 l1
       (clos_state_code (t0:(C,FFI)clos_state))) env env2 0 (MAP (\x. (0,x)) e1')` ASSUME_TAC THENL
    [MATCH_MP_TAC CLOSCALLPAUX_env_rel_MAP0_mono THEN EXISTS_TAC `[clos_Op x op e1']` THEN
     ASM_REWRITE_TAC[clos_fv_def];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSCALLPAUX_cc_P_def] o check (fun th ->
     concl th = `CLOSCALLPAUX_cc_P (xs,env,(s:(abs_calls_state # C,FFI)clos_state))`)) THEN
   DISCH_THEN(MP_TAC o SPECL [`g0:num_set # (num # num # clos_exp) list`;
     `g:num_set # (num # num # clos_exp) list`; `env2:clos_v list`; `t0:(C,FFI)clos_state`;
     `e1':clos_exp list`; `r0:(clos_v list,clos_v)result`;
     `s0:(abs_calls_state # C,FFI)clos_state`;
     `set_of_list (code_locs xs) DIFF domain (FST (g:num_set # (num # num # clos_exp) list))`;
     `l1:num->bool`; `g1:num_set # (num # num # clos_exp) list`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck:num`; `res0:(clos_v list,clos_v)result`;
     `t1:(C,FFI)clos_state`; `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`]) THEN
   MP_TAC(ISPEC `r0:(clos_v list,clos_v)result` (cases "result")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs:clos_v list` SUBST_ALL_TAC)
     (X_CHOOSE_THEN `err:clos_v error_result` SUBST_ALL_TAC)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[result_rel_Rval; result_rel_Rerr1; every_result_def]) THEN
   REPEAT (FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     lhs (concl th) = `res0:(clos_v list,clos_v)result`)) THENL
    [ALL_TAC;
     UNDISCH_TAC `clos_evaluate ([clos_Op x op xs],env,(s:(abs_calls_state # C,FFI)clos_state)) =
                  (res,s')` THEN
     GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [clos_evaluate_def] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
     DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
     MAP_EVERY EXISTS_TAC [`ck:num`; `Rerr e':(clos_v list,clos_v)result`; `t1:(C,FFI)clos_state`;
       `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`] THEN
     ASM_REWRITE_TAC[every_result_def; result_rel_def] THEN
     ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]]) THEN
  (ASM_CASES_TAC `op = clos_Install` THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN
     SUBGOAL_THEN `!es s4. clos_do_install (REVERSE vs) (s0:(abs_calls_state # C,FFI)clos_state) =
                           (Rval es,s4) ==> CLOSCALLPAUX_cc_P (es,[],s4)` ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       MAP_EVERY EXISTS_TAC [`vs:clos_v list`; `s0:(abs_calls_state # C,FFI)clos_state`] THEN
       ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     MP_TAC(ISPECL [`x:tra`; `xs:clos_exp list`; `env:clos_v list`;
       `s:(abs_calls_state # C,FFI)clos_state`; `vs:clos_v list`;
       `s0:(abs_calls_state # C,FFI)clos_state`; `res:(clos_v list,clos_v)result`;
       `s':(abs_calls_state # C,FFI)clos_state`; `e1':clos_exp list`; `env2:clos_v list`;
       `t0:(C,FFI)clos_state`; `ck:num`; `v':clos_v list`; `t1:(C,FFI)clos_state`;
       `g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`;
       `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`] CLOSCALLPAUX_cc_Op_install) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `clos_state_code (t0:(C,FFI)clos_state) SUBMAP clos_state_code (t1:(C,FFI)clos_state)`
     ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP clos_evaluate_mono o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `(Rval v':(clos_v list,clos_v)result),(t1:(C,FFI)clos_state)`)) THEN
     REWRITE_TAC[clos_state_INFO.ri_accfupds];
     ALL_TAC] THEN
   ASM_CASES_TAC `op = clos_ThunkOp ForceThunk` THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN
     SUBGOAL_THEN `!v. clos_dest_thunk vs (clos_state_refs (s0:(abs_calls_state # C,FFI)clos_state)) =
                       clos_IsThunk NotEvaluated v
                       ==> CLOSCALLPAUX_cc_P ([clos_AppUnit (clos_Var backend_common_None 0)],[v],s0)`
       ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       EXISTS_TAC `vs:clos_v list` THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     SUBGOAL_THEN `wfg (g:num_set # (num # num # clos_exp) list)` ASSUME_TAC THENL
      [MATCH_MP_TAC calls_wfg THEN MAP_EVERY EXISTS_TAC [`xs:clos_exp list`;
         `g0:num_set # (num # num # clos_exp) list`; `e1':clos_exp list`] THEN
       ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     MP_TAC(ISPECL [`x:tra`; `xs:clos_exp list`; `env:clos_v list`;
       `s:(abs_calls_state # C,FFI)clos_state`; `vs:clos_v list`;
       `s0:(abs_calls_state # C,FFI)clos_state`; `res:(clos_v list,clos_v)result`;
       `s':(abs_calls_state # C,FFI)clos_state`; `e1':clos_exp list`; `env2:clos_v list`;
       `t0:(C,FFI)clos_state`; `ck:num`; `v':clos_v list`; `t1:(C,FFI)clos_state`;
       `g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`;
       `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`;
       `g:num_set # (num # num # clos_exp) list`] CLOSCALLPAUX_cc_Op_force) THEN
     ASM_REWRITE_TAC[] THEN
     ANTS_TAC THENL [ASM_MESON_TAC[code_includes_SUBMAP]; REWRITE_TAC[]];
     ALL_TAC] THEN
   SUBGOAL_THEN
    `(!err. clos_do_app op (REVERSE vs) (s0:(abs_calls_state # C,FFI)clos_state) = Rerr err
            ==> res = Rerr err /\ s' = s0) /\
     (!v s3. clos_do_app op (REVERSE vs) s0 = Rval (v,s3) ==> res = Rval [v] /\ s' = s3)`
     STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `clos_evaluate ([clos_Op x op xs],env,(s:(abs_calls_state # C,FFI)clos_state)) =
                  (res,s')` THEN
     GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [clos_evaluate_def] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
     DISCH_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`x:tra`; `op:clos_op`; `e1':clos_exp list`; `env2:clos_v list`;
     `vs:clos_v list`; `s0:(abs_calls_state # C,FFI)clos_state`; `res:(clos_v list,clos_v)result`;
     `s':(abs_calls_state # C,FFI)clos_state`; `t0:(C,FFI)clos_state`; `ck:num`; `v':clos_v list`;
     `t1:(C,FFI)clos_state`; `g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`;
     `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`] CLOSCALLPAUX_cc_Op_app) THEN
   ASM_REWRITE_TAC[]));;

(* calls_correct, case App: no direct call (target is an App) *)
let CLOSCALLPAUX_cc_App_app = prove
 (`!x loc_opt x1 args env (s:(abs_calls_state # C,FFI)clos_state) y2 s1 res s'
    es e1' (g':num_set # (num # num # clos_exp) list) g g1 l1 env2 (t0:(C,FFI)clos_state)
    ck y2' t1 g2 l2.
    LENGTH args > 0 /\ LENGTH es > 0 /\
    clos_evaluate (args,env,s) = (Rval y2,s1) /\
    clos_evaluate ([clos_App x loc_opt x1 args],env,s) = (res,s') /\
    (!y1 s2. clos_evaluate ([x1],env,s1) = (Rval y1,s2)
             ==> CLOSCALLPAUX_cc_Q loc_opt (HD y1) y2 s2) /\
    CLOSCALLPAUX_cc_P ([x1],env,s1) /\
    ~(res = Rerr (Rabort Rtype_error)) /\
    clos_call_calls [x1] g' = ([e1'],g) /\
    wfg g' /\
    DISJOINT (IMAGE SUC (set_of_list (code_locs [x1]))) (set_of_list (MAP FST (SND g'))) /\
    ALL_DISTINCT (code_locs [x1]) /\ every_Fn_SOME [x1] /\ every_Fn_vs_NONE [x1] /\
    subg g g1 /\ set_of_list (code_locs [x1]) DIFF domain (FST g) SUBSET l1 /\
    code_includes (SND g) (clos_state_code t0) /\
    ALL (wfv g1 l1 (clos_state_code t0)) env /\
    clos_callProof_env_rel (clos_callProof_v_rel g1 l1 (clos_state_code t0)) env env2 0
      (MAP (\x. (0,x)) [e1']) /\
    clos_evaluate (es,env2,clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) =
      (Rval y2',t1) /\
    code_inv (SOME g2) l2 (clos_state_code s1) (clos_state_compile s1)
      (clos_state_compile_oracle s1) (clos_state_code t1) (clos_state_compile t1)
      (clos_state_compile_oracle t1) /\
    wfv_state g2 l2 (clos_state_code t1) s1 /\
    subg g1 g2 /\ wfg g2 /\ l1 SUBSET l2 /\ DISJOINT l2 (domain (FST g2)) /\
    ALL (wfv g2 l2 (clos_state_code t1)) y2 /\
    clos_callProof_state_rel g2 l2 s1 t1 /\
    ALL2 (clos_callProof_v_rel g2 l2 (clos_state_code t1)) y2 y2' /\
    clos_state_code t0 SUBMAP clos_state_code t1
    ==> ?ck res' t g3 l3.
          code_inv (SOME g3) l3 (clos_state_code s') (clos_state_compile s')
            (clos_state_compile_oracle s') (clos_state_code t) (clos_state_compile t)
            (clos_state_compile_oracle t) /\
          wfv_state g3 l3 (clos_state_code t) s' /\
          subg g1 g3 /\ wfg g3 /\ l1 SUBSET l3 /\ DISJOINT l3 (domain (FST g3)) /\
          every_result (ALL (wfv g3 l3 (clos_state_code t))) (wfv g3 l3 (clos_state_code t))
            res /\
          clos_evaluate ([clos_App x loc_opt e1' es],env2,
            clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) = (res',t) /\
          clos_callProof_state_rel g3 l3 s' t /\
          result_rel (ALL2 (clos_callProof_v_rel g3 l3 (clos_state_code t)))
            (clos_callProof_v_rel g3 l3 (clos_state_code t)) res res'`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     rand (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
   GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [clos_evaluate_def] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   SUBGOAL_THEN `?r2 s2. clos_evaluate ([x1],env,(s1:(abs_calls_state # C,FFI)clos_state)) = (r2,s2)`
     STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC) THEN
  (SUBGOAL_THEN `~(r2 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
     CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
     UNDISCH_TAC `~(res = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN
    `ALL (wfv g2 l2 (clos_state_code (t1:(C,FFI)clos_state))) env /\
     clos_callProof_env_rel (clos_callProof_v_rel g2 l2 (clos_state_code t1)) env env2 0
       (MAP (\x. (0,x)) [e1']) /\
     subg (g:num_set # (num # num # clos_exp) list) g2 /\
     set_of_list (code_locs [x1]) DIFF domain (FST g) SUBSET l2 /\
     code_includes (SND g) (clos_state_code t1)` STRIP_ASSUME_TAC THENL
    [REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC(GEN_ALL EVERY_wfv_subg) THEN
       MAP_EVERY EXISTS_TAC [`clos_state_code (t0:(C,FFI)clos_state)`;
         `g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`] THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC(GEN_ALL env_rel_subg) THEN
       MAP_EVERY EXISTS_TAC [`g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`;
         `clos_state_code (t0:(C,FFI)clos_state)`] THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC subg_trans THEN EXISTS_TAC `g1:num_set # (num # num # clos_exp) list` THEN
       ASM_REWRITE_TAC[];
       MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l1:num->bool` THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC(GEN_ALL code_includes_SUBMAP) THEN
       EXISTS_TAC `clos_state_code (t0:(C,FFI)clos_state)` THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSCALLPAUX_cc_P_def] o check (fun th ->
     concl th = `CLOSCALLPAUX_cc_P ([x1],env,(s1:(abs_calls_state # C,FFI)clos_state))`)) THEN
   DISCH_THEN(MP_TAC o SPECL [`g':num_set # (num # num # clos_exp) list`;
     `g:num_set # (num # num # clos_exp) list`; `env2:clos_v list`; `t1:(C,FFI)clos_state`;
     `[e1':clos_exp]`; `r2:(clos_v list,clos_v)result`; `s2:(abs_calls_state # C,FFI)clos_state`;
     `set_of_list (code_locs [x1]) DIFF domain (FST (g:num_set # (num # num # clos_exp) list))`;
     `l2:num->bool`; `g2:num_set # (num # num # clos_exp) list`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck2:num`; `r2':(clos_v list,clos_v)result`;
     `t2:(C,FFI)clos_state`; `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`]) THEN
   FIRST_ASSUM(MP_TAC o SPEC `ck2:num` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
     CLOSCALLPAUX_evaluate_add_clock_res) o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `(Rval y2':(clos_v list,clos_v)result),(t1:(C,FFI)clos_state)`)) THEN
   REWRITE_TAC[distinctness "result"] THEN DISCH_TAC THEN
   SUBGOAL_THEN `clos_state_code (t1:(C,FFI)clos_state) SUBMAP clos_state_code (t2:(C,FFI)clos_state)`
     ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP clos_evaluate_mono o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `r2':(clos_v list,clos_v)result,(t2:(C,FFI)clos_state)`)) THEN
     REWRITE_TAC[clos_state_INFO.ri_accfupds];
     ALL_TAC] THEN
   MP_TAC(ISPEC `r2:(clos_v list,clos_v)result` (cases "result")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `y1:clos_v list` SUBST_ALL_TAC)
     (X_CHOOSE_THEN `err:clos_v error_result` SUBST_ALL_TAC)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[result_rel_Rval; result_rel_Rerr1; every_result_def]) THEN
   REPEAT (FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     lhs (concl th) = `r2':(clos_v list,clos_v)result`))) THENL
  [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP clos_evaluate_SING o check (fun th -> is_eq (concl th) &&
     rand (concl th) = `(Rval y1:(clos_v list,clos_v)result),(s2:(abs_calls_state # C,FFI)clos_state)`)) THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[HD; LIST_REL_CONS1; LIST_REL_NIL; ALL]) THEN
   REPEAT (FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
   RVEQ_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`[r1:clos_v]`; `s2:(abs_calls_state # C,FFI)clos_state`] o
     check (fun th -> is_forall (concl th) &&
       can (find_term (fun t -> is_const t && fst (dest_const t) = "CLOSCALLPAUX_cc_Q")) (concl th))) THEN
   ASM_REWRITE_TAC[HD; CLOSCALLPAUX_cc_Q_def] THEN
   DISCH_THEN(MP_TAC o SPECL [`g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`;
     `t2:(C,FFI)clos_state`; `res:(clos_v list,clos_v)result`;
     `s':(abs_calls_state # C,FFI)clos_state`; `h':clos_v`; `y2':clos_v list`]) THEN
   ASM_REWRITE_TAC[] THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL
      [MATCH_MP_TAC(GEN_ALL EVERY_wfv_subg) THEN
       MAP_EVERY EXISTS_TAC [`clos_state_code (t1:(C,FFI)clos_state)`;
         `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`] THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC(GEN_ALL LIST_REL_v_rel_subg) THEN
       MAP_EVERY EXISTS_TAC [`g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`;
         `clos_state_code (t1:(C,FFI)clos_state)`] THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck3:num`; `res3:(clos_v list,clos_v)result`;
     `t3:(C,FFI)clos_state`; `g4:num_set # (num # num # clos_exp) list`; `l4:num->bool`]) THEN
   FIRST_ASSUM(MP_TAC o SPEC `ck2 + ck3:num` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
     CLOSCALLPAUX_evaluate_add_clock_res) o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `(Rval y2':(clos_v list,clos_v)result),(t1:(C,FFI)clos_state)`)) THEN
   REWRITE_TAC[distinctness "result"] THEN DISCH_TAC THEN
   FIRST_ASSUM(MP_TAC o SPEC `ck3:num` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
     CLOSCALLPAUX_evaluate_add_clock_res) o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `(Rval [h']:(clos_v list,clos_v)result),(t2:(C,FFI)clos_state)`)) THEN
   REWRITE_TAC[distinctness "result"] THEN DISCH_TAC THEN
   MAP_EVERY EXISTS_TAC [`ck + ck2 + ck3:num`; `res3:(clos_v list,clos_v)result`;
     `t3:(C,FFI)clos_state`; `g4:num_set # (num # num # clos_exp) list`; `l4:num->bool`] THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC subg_trans THEN EXISTS_TAC `g3:num_set # (num # num # clos_exp) list` THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC subg_trans THEN
     EXISTS_TAC `g2:num_set # (num # num # clos_exp) list` THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l3:num->bool` THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l2:num->bool` THEN ASM_REWRITE_TAC[];
     ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
     REPEAT (CHANGED_TAC (CASE_REWRITE_TAC[HD] THEN ASM_REWRITE_TAC[]))];
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     rand (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
   CASE_REWRITE_TAC[PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   MAP_EVERY EXISTS_TAC [`ck + ck2:num`; `Rerr e':(clos_v list,clos_v)result`;
     `t2:(C,FFI)clos_state`; `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`] THEN
   ASM_REWRITE_TAC[every_result_def; result_rel_def] THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC subg_trans THEN EXISTS_TAC `g2:num_set # (num # num # clos_exp) list` THEN
     ASM_REWRITE_TAC[];
     MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l2:num->bool` THEN ASM_REWRITE_TAC[];
     ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
     REPEAT (CHANGED_TAC (CASE_REWRITE_TAC[HD] THEN ASM_REWRITE_TAC[]))]]);;

let CLOSCALLPAUX_call_eq = prove
 (`!tt n xs env (T0:(C,FFI)clos_state) y2' ts loc body.
     clos_evaluate (xs,env,T0) = (Rval y2',ts) /\
     FLOOKUP (clos_state_code ts) (loc + 1) = SOME (LENGTH y2',body)
     ==> clos_evaluate ([clos_Call tt n (loc + 1) xs],env,T0) =
         (if clos_state_clock ts < n + 1
          then (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) ts)
          else clos_evaluate ([body],y2',clos_dec_clock (n + 1) ts))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [clos_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[clos_find_code_def] THEN
  CASE_REWRITE_TAC[]);;

let CLOSCALLPAUX_eval_sing_match = prove
 (CASE_TERM
  `!loc_opt (p:(clos_v list,clos_v)result # (C,FFI)clos_state).
     (match p with
        (x,s1) -> (match x with
                     Rval a -> (match a with
                                  [] -> (x,s1)
                                | CONS v a1 -> (match a1 with
                                                  [] -> evaluate_app loc_opt v [] s1
                                                | CONS a0 a1' -> (x,s1)))
                   | Rerr a -> (x,s1))) = p`,
  REPEAT GEN_TAC THEN SUBST1_TAC(GSYM(ISPEC `p:(clos_v list,clos_v)result # (C,FFI)clos_state` PAIR)) THEN
  SPEC_TAC(`FST (p:(clos_v list,clos_v)result # (C,FFI)clos_state)`,`r:(clos_v list,clos_v)result`) THEN
  SPEC_TAC(`SND (p:(clos_v list,clos_v)result # (C,FFI)clos_state)`,`st:(C,FFI)clos_state`) THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `r:(clos_v list,clos_v)result` (cases "result")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `a:clos_v list` list_CASES) THEN CASE_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `t:clos_v list` list_CASES) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_evaluate_def]);;

let CLOSCALLPAUX_app_call_eq = prove
 (`!loc f' y2' (ts:(C,FFI)clos_state) tra l1' body.
     dest_closure (clos_state_max_app ts) (SOME loc) f' y2' =
       SOME (Full_app (clos_Call tra 0 (loc + 1) (GENLIST_Var tra 1 (LENGTH y2')))
               (APPEND y2' l1') []) /\
     FLOOKUP (clos_state_code ts) (loc + 1) = SOME (LENGTH y2',body) /\ ~(y2' = [])
     ==> evaluate_app (SOME loc) f' y2' ts =
         (if clos_state_clock ts < LENGTH y2' + 1
          then (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) ts)
          else clos_evaluate ([body],y2',clos_dec_clock (LENGTH y2' + 1) ts))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[evaluate_app_rw] THEN CASE_REWRITE_TAC[LENGTH; SUB_0] THEN
  MP_TAC(ISPECL [`tra:tra`; `0`; `GENLIST_Var tra 1 (LENGTH (y2':clos_v list))`;
    `APPEND (y2':clos_v list) l1'`; `clos_dec_clock (LENGTH (y2':clos_v list)) (ts:(C,FFI)clos_state)`;
    `y2':clos_v list`; `clos_dec_clock (LENGTH (y2':clos_v list)) (ts:(C,FFI)clos_state)`;
    `loc:num`; `body:clos_exp`] CLOSCALLPAUX_call_eq) THEN
  ASM_REWRITE_TAC[evaluate_GENLIST_Var_tra; clos_dec_clock_code; LENGTH_APPEND; LE_ADD;
    TAKE_LENGTH_APPEND] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  ASM_CASES_TAC `clos_state_clock (ts:(C,FFI)clos_state) < LENGTH (y2':clos_v list)` THEN
  ASM_SIMP_TAC[ARITH_RULE `a < b ==> a < b + 1`] THEN
  ASM_CASES_TAC `clos_state_clock (ts:(C,FFI)clos_state) = LENGTH (y2':clos_v list)` THENL
   [ASM_REWRITE_TAC[SUB_REFL; ARITH_RULE `0 < 1 /\ n < n + 1`] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM];
    SUBGOAL_THEN `~(clos_state_clock (ts:(C,FFI)clos_state) - LENGTH (y2':clos_v list) < 1) /\
                  ~(clos_state_clock ts < LENGTH y2' + 1)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `clos_state_clock_fupd (K (clos_state_clock (ts:(C,FFI)clos_state) -
                    LENGTH (y2':clos_v list) - 1))
                    (clos_state_clock_fupd (K (clos_state_clock ts - LENGTH y2')) ts) =
                  clos_state_clock_fupd (K (clos_state_clock ts - (LENGTH y2' + 1))) ts`
      SUBST1_TAC THENL
     [REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM] THEN
      ARITH_TAC;
      REWRITE_TAC[CLOSCALLPAUX_eval_sing_match]]]);;

let CLOSCALLPAUX_let_call_eq = prove
 (`!tt tt' xs e1 env (T0:(C,FFI)clos_state) y2' t1 f' ts loc body.
     clos_evaluate (xs,env,T0) = (Rval y2',t1) /\
     clos_evaluate ([e1],env,t1) = (Rval [f'],ts) /\
     FLOOKUP (clos_state_code ts) (loc + 1) = SOME (LENGTH y2',body)
     ==> clos_evaluate ([clos_Let tt (SNOC e1 xs)
            (clos_Call tt' (LENGTH xs) (loc + 1)
               (GENLIST_Var backend_common_None 2 (LENGTH xs)))],env,T0) =
         (if clos_state_clock ts < LENGTH xs + 1
          then (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) ts)
          else clos_evaluate ([body],y2',clos_dec_clock (LENGTH xs + 1) ts))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (xs:clos_exp list) = LENGTH (y2':clos_v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[clos_evaluate_IMP_LENGTH]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [clos_evaluate_def] THEN
  REWRITE_TAC[SNOC_APPEND; clos_evaluate_append] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MATCH_MP_TAC CLOSCALLPAUX_call_eq THEN
  ASM_REWRITE_TAC[evaluate_GENLIST_Var_tra; LENGTH_APPEND; LE_ADD; GSYM APPEND_ASSOC;
                  TAKE_LENGTH_APPEND; ARITH_RULE `a <= (a + b) + c:num`]);;


(* calls_correct, case App with a known closure (compiled to a direct call): *)
(* the closure's code is in the code table, and evaluate_app of the target  *)
(* closure reduces to an evaluation of that code                            *)
let CLOSCALLPAUX_app_core = prove
 (`!loc f y2 (s2:(abs_calls_state # C,FFI)clos_state) res s' f' y2'
    (t2:(C,FFI)clos_state) g g3 l3.
    evaluate_app (SOME loc) f y2 s2 = (res,s') /\ ~(res = Rerr (Rabort Rtype_error)) /\
    CLOSCALLPAUX_cc_Q (SOME loc) f y2 s2 /\
    code_inv (SOME g3) l3 (clos_state_code s2) (clos_state_compile s2)
      (clos_state_compile_oracle s2) (clos_state_code t2) (clos_state_compile t2)
      (clos_state_compile_oracle t2) /\
    wfv g3 l3 (clos_state_code t2) f /\ ALL (wfv g3 l3 (clos_state_code t2)) y2 /\
    wfv_state g3 l3 (clos_state_code t2) s2 /\ wfg g3 /\ DISJOINT l3 (domain (FST g3)) /\
    clos_callProof_v_rel g3 l3 (clos_state_code t2) f f' /\
    ALL2 (clos_callProof_v_rel g3 l3 (clos_state_code t2)) y2 y2' /\
    clos_callProof_state_rel g3 l3 s2 t2 /\
    wfg (g:num_set # (num # num # clos_exp) list) /\ subg g g3 /\ loc IN domain (FST g) /\
    code_includes (SND g) (clos_state_code t2) /\ ~(y2 = [])
    ==> ?body.
          FLOOKUP (clos_state_code t2) (loc + 1) = SOME (LENGTH y2',body) /\
          (!ts:(C,FFI)clos_state. clos_state_max_app ts = clos_state_max_app t2 /\
                clos_state_code ts = clos_state_code t2
                ==> evaluate_app (SOME loc) f' y2' ts =
                    (if clos_state_clock ts < LENGTH y2' + 1
                     then (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) ts)
                     else clos_evaluate ([body],y2',clos_dec_clock (LENGTH y2' + 1) ts))) /\
          ?ck res' t g4 l4.
            code_inv (SOME g4) l4 (clos_state_code s') (clos_state_compile s')
              (clos_state_compile_oracle s') (clos_state_code t) (clos_state_compile t)
              (clos_state_compile_oracle t) /\
            wfv_state g4 l4 (clos_state_code t) s' /\
            every_result (ALL (wfv g4 l4 (clos_state_code t))) (wfv g4 l4 (clos_state_code t))
              res /\
            evaluate_app (SOME loc) f' y2'
              (clos_state_clock_fupd (K (clos_state_clock t2 + ck)) t2) = (res',t) /\
            clos_callProof_state_rel g4 l4 s' t /\
            subg g3 g4 /\ wfg g4 /\ l3 SUBSET l4 /\ DISJOINT l4 (domain (FST g4)) /\
            result_rel (ALL2 (clos_callProof_v_rel g4 l4 (clos_state_code t)))
              (clos_callProof_v_rel g4 l4 (clos_state_code t)) res res'`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   MP_TAC(ISPEC `dest_closure (clos_state_max_app (s2:(abs_calls_state # C,FFI)clos_state))
                   (SOME loc) f y2` option_nchotomy) THEN
   DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `xk:app_kind` ASSUME_TAC)) THENL
    [UNDISCH_TAC `evaluate_app (SOME loc) f y2 (s2:(abs_calls_state # C,FFI)clos_state) = (res,s')` THEN
     ASM_SIMP_TAC[evaluate_app_rw] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
     UNDISCH_TAC `~(res = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `(loc:num) IN domain (FST (g3:num_set # (num # num # clos_exp) list)) /\
                 ~(loc IN l3)` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `subg (g:num_set # (num # num # clos_exp) list) g3` THEN
     REWRITE_TAC[subg_def; subspt_domain; SUBSET] THEN STRIP_TAC THEN
     CONJ_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`f:clos_v`; `l3:num->bool`; `xk:app_kind`;
     `g3:num_set # (num # num # clos_exp) list`;
     `clos_state_max_app (s2:(abs_calls_state # C,FFI)clos_state)`; `f':clos_v`;
     `y2:clos_v list`; `y2':clos_v list`; `loc:num`; `clos_state_code (t2:(C,FFI)clos_state)`]
     (GEN_ALL dest_closure_v_rel_lookup)) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`e:clos_exp`; `l1x:clos_v list`;
     `xs:(num # clos_exp) list`; `n:num`; `ls:clos_exp list`;
     `g01:num_set # (num # num # clos_exp) list`; `g1x:num_set # (num # num # clos_exp) list`;
     `l1':clos_v list`; `tra:tra`])) THEN
  (SUBGOAL_THEN `LENGTH (y2:clos_v list) = LENGTH (y2':clos_v list) /\
                 clos_state_max_app (s2:(abs_calls_state # C,FFI)clos_state) =
                 clos_state_max_app (t2:(C,FFI)clos_state)` STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC[LIST_REL_LENGTH; clos_callProof_state_rel_max_app]; ALL_TAC] THEN
   SUBGOAL_THEN `FLOOKUP (clos_state_code (t2:(C,FFI)clos_state)) (loc + 1) =
                 SOME (LENGTH (y2':clos_v list),EL n (ls:clos_exp list))` ASSUME_TAC THENL
    [SUBGOAL_THEN `MEM (loc + 1) (MAP FST (SND (g:num_set # (num # num # clos_exp) list)))`
       ASSUME_TAC THENL
      [UNDISCH_TAC `wfg (g:num_set # (num # num # clos_exp) list)` THEN
       REWRITE_TAC[wfg_def] THEN STRIP_TAC THEN
       REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
       EXISTS_TAC `loc:num` THEN ASM_REWRITE_TAC[ADD1];
       ALL_TAC] THEN
     SUBGOAL_THEN `?v. ALOOKUP (SND (g:num_set # (num # num # clos_exp) list)) (loc + 1) = SOME v`
       STRIP_ASSUME_TAC THENL
      [MP_TAC(ISPECL [`SND (g:num_set # (num # num # clos_exp) list)`; `loc + 1`] ALOOKUP_NONE) THEN
       ASM_REWRITE_TAC[] THEN MESON_TAC[option_nchotomy];
       ALL_TAC] THEN
     SUBGOAL_THEN `v = (LENGTH (y2':clos_v list),EL n (ls:clos_exp list))` SUBST_ALL_TAC THENL
      [UNDISCH_TAC `subg (g:num_set # (num # num # clos_exp) list) g3` THEN
       REWRITE_TAC[subg_def] THEN STRIP_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPECL [`loc + 1`; `v:num # clos_exp`]) THEN
       ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[];
       ALL_TAC] THEN
     MATCH_MP_TAC(GEN_ALL code_includes_ALOOKUP) THEN
     EXISTS_TAC `SND (g:num_set # (num # num # clos_exp) list)` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   EXISTS_TAC `EL n (ls:clos_exp list)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [X_GEN_TAC `ts:(C,FFI)clos_state` THEN STRIP_TAC THEN
     MATCH_MP_TAC CLOSCALLPAUX_app_call_eq THEN
     MAP_EVERY EXISTS_TAC [`tra:tra`; `l1':clos_v list`] THEN
     ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
      [UNDISCH_TAC `dest_closure (clos_state_max_app (s2:(abs_calls_state # C,FFI)clos_state))
                      (SOME loc) f' y2' =
                    SOME (Full_app (clos_Call tra 0 (loc + 1) (GENLIST_Var tra 1 (LENGTH (y2:clos_v list))))
                      (APPEND y2' l1') [])` THEN ASM_REWRITE_TAC[];
       UNDISCH_TAC `~(y2:clos_v list = [])` THEN
       REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[]];
     MP_TAC(SPECL [`g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`;
       `t2:(C,FFI)clos_state`; `res:(clos_v list,clos_v)result`;
       `s':(abs_calls_state # C,FFI)clos_state`; `f':clos_v`; `y2':clos_v list`]
       (REWRITE_RULE[CLOSCALLPAUX_cc_Q_def] (ASSUME
         `CLOSCALLPAUX_cc_Q (SOME loc) f y2 (s2:(abs_calls_state # C,FFI)clos_state)`))) THEN
     ASM_REWRITE_TAC[]]));;


(* calls_correct, case App compiled to a direct Call (pure function expression) *)
let CLOSCALLPAUX_cc_App_call = prove
 (`!x loc_opt x1 args env (s:(abs_calls_state # C,FFI)clos_state) y2 s1 res s'
    es e1' (g':num_set # (num # num # clos_exp) list) g g1 l1 env2 (t0:(C,FFI)clos_state)
    ck y2' t1 g2 l2 loc.
    LENGTH args > 0 /\ LENGTH es > 0 /\
    clos_evaluate (args,env,s) = (Rval y2,s1) /\
    clos_evaluate ([clos_App x loc_opt x1 args],env,s) = (res,s') /\
    (!y1 s2. clos_evaluate ([x1],env,s1) = (Rval y1,s2)
             ==> CLOSCALLPAUX_cc_Q loc_opt (HD y1) y2 s2) /\
    CLOSCALLPAUX_cc_P ([x1],env,s1) /\
    ~(res = Rerr (Rabort Rtype_error)) /\
    clos_call_calls [x1] g' = ([e1'],g) /\
    wfg g' /\
    DISJOINT (IMAGE SUC (set_of_list (code_locs [x1]))) (set_of_list (MAP FST (SND g'))) /\
    ALL_DISTINCT (code_locs [x1]) /\ every_Fn_SOME [x1] /\ every_Fn_vs_NONE [x1] /\
    subg g g1 /\ set_of_list (code_locs [x1]) DIFF domain (FST g) SUBSET l1 /\
    code_includes (SND g) (clos_state_code t0) /\
    ALL (wfv g1 l1 (clos_state_code t0)) env /\
    pure x1 /\ loc_opt = SOME loc /\ loc IN domain (FST g) /\ wfg g /\
    clos_evaluate (es,env2,clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) =
      (Rval y2',t1) /\
    code_inv (SOME g2) l2 (clos_state_code s1) (clos_state_compile s1)
      (clos_state_compile_oracle s1) (clos_state_code t1) (clos_state_compile t1)
      (clos_state_compile_oracle t1) /\
    wfv_state g2 l2 (clos_state_code t1) s1 /\
    subg g1 g2 /\ wfg g2 /\ l1 SUBSET l2 /\ DISJOINT l2 (domain (FST g2)) /\
    ALL (wfv g2 l2 (clos_state_code t1)) y2 /\
    clos_callProof_state_rel g2 l2 s1 t1 /\
    ALL2 (clos_callProof_v_rel g2 l2 (clos_state_code t1)) y2 y2' /\
    clos_state_code t0 SUBMAP clos_state_code t1
    ==> ?ck res' t g3 l3.
          code_inv (SOME g3) l3 (clos_state_code s') (clos_state_compile s')
            (clos_state_compile_oracle s') (clos_state_code t) (clos_state_compile t)
            (clos_state_compile_oracle t) /\
          wfv_state g3 l3 (clos_state_code t) s' /\
          subg g1 g3 /\ wfg g3 /\ l1 SUBSET l3 /\ DISJOINT l3 (domain (FST g3)) /\
          every_result (ALL (wfv g3 l3 (clos_state_code t))) (wfv g3 l3 (clos_state_code t))
            res /\
          clos_evaluate ([clos_Call x (LENGTH es) (loc + 1) es],env2,
            clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) = (res',t) /\
          clos_callProof_state_rel g3 l3 s' t /\
          result_rel (ALL2 (clos_callProof_v_rel g3 l3 (clos_state_code t)))
            (clos_callProof_v_rel g3 l3 (clos_state_code t)) res res'`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     lhs (concl th) = `loc_opt:num option`)) THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     rand (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
   GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [clos_evaluate_def] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   SUBGOAL_THEN `?r2 s2. clos_evaluate ([x1],env,(s1:(abs_calls_state # C,FFI)clos_state)) = (r2,s2)`
     STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
   MP_TAC(MATCH_MP pure_correct_eq (CONJ (ASSUME `pure x1`) (ASSUME
     `clos_evaluate ([x1],env,(s1:(abs_calls_state # C,FFI)clos_state)) = (r2,s2)`))) THEN
   MP_TAC(ISPEC `r2:(clos_v list,clos_v)result` (cases "result")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `y1:clos_v list` SUBST_ALL_TAC)
     (X_CHOOSE_THEN `err:clos_v error_result` SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[] THENL
    [ALL_TAC;
     MP_TAC(ISPEC `err:clos_v error_result` (cases "error_result")) THEN
     DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `ex:clos_v` SUBST_ALL_TAC)
       (X_CHOOSE_THEN `ab:abort` SUBST_ALL_TAC)) THEN
     CASE_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
     CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
     UNDISCH_TAC `~(res = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` THEN
     ASM_REWRITE_TAC[]]) THEN
  (DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC
     (MP_TAC o REWRITE_RULE[ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL])) THEN
   DISCH_THEN(X_CHOOSE_THEN `f:clos_v`
     (X_CHOOSE_THEN `tl:clos_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC))) THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[HD]) THEN
   SUBGOAL_THEN
    `ALL (wfv g2 l2 (clos_state_code (t1:(C,FFI)clos_state))) env /\
     subg (g:num_set # (num # num # clos_exp) list) g2 /\
     set_of_list (code_locs [x1]) DIFF domain (FST g) SUBSET l2 /\
     code_includes (SND g) (clos_state_code t1)` STRIP_ASSUME_TAC THENL
    [REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC(GEN_ALL EVERY_wfv_subg) THEN
       MAP_EVERY EXISTS_TAC [`clos_state_code (t0:(C,FFI)clos_state)`;
         `g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`] THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC subg_trans THEN EXISTS_TAC `g1:num_set # (num # num # clos_exp) list` THEN
       ASM_REWRITE_TAC[];
       MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l1:num->bool` THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC(GEN_ALL code_includes_SUBMAP) THEN
       EXISTS_TAC `clos_state_code (t0:(C,FFI)clos_state)` THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP (ISPEC `MAP (\x. (0,x)) [e1':clos_exp]` env_rel_env_exists) o
     check (fun th -> concl th = `ALL (wfv g2 l2 (clos_state_code (t1:(C,FFI)clos_state))) env`)) THEN
   DISCH_THEN(X_CHOOSE_THEN `env5:clos_v list` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSCALLPAUX_cc_P_def] o check (fun th ->
     concl th = `CLOSCALLPAUX_cc_P ([x1],env,(s1:(abs_calls_state # C,FFI)clos_state))`)) THEN
   DISCH_THEN(MP_TAC o SPECL [`g':num_set # (num # num # clos_exp) list`;
     `g:num_set # (num # num # clos_exp) list`; `env5:clos_v list`; `t1:(C,FFI)clos_state`;
     `[e1':clos_exp]`; `Rval [f]:(clos_v list,clos_v)result`;
     `s1:(abs_calls_state # C,FFI)clos_state`;
     `set_of_list (code_locs [x1]) DIFF domain (FST (g:num_set # (num # num # clos_exp) list))`;
     `l2:num->bool`; `g2:num_set # (num # num # clos_exp) list`]) THEN
   ASM_REWRITE_TAC[distinctness "result"] THEN
   DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck2:num`; `r2':(clos_v list,clos_v)result`;
     `t2:(C,FFI)clos_state`; `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[result_rel_Rval; every_result_def; ALL; LIST_REL_CONS1;
     LIST_REL_NIL]) THEN
   REPEAT (FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
   RVEQ_TAC) THEN
  (MP_TAC(MATCH_MP calls_pure_sing (CONJ (ASSUME `pure x1`) (ASSUME
     `clos_call_calls [x1] (g':num_set # (num # num # clos_exp) list) = ([e1'],g)`))) THEN
   DISCH_TAC THEN
   MP_TAC(MATCH_MP pure_correct_eq (CONJ (ASSUME `pure e1'`) (ASSUME
     `clos_evaluate ([e1'],env5,clos_state_clock_fupd (K (clos_state_clock (t1:(C,FFI)clos_state) + ck2)) t1) =
      (Rval [h'],t2)`))) THEN
   CASE_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o CONJUNCT1) THEN
   SUBGOAL_THEN `~(y2:clos_v list = [])` ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP clos_evaluate_IMP_LENGTH o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `(Rval y2:(clos_v list,clos_v)result),(s1:(abs_calls_state # C,FFI)clos_state)`)) THEN
     UNDISCH_TAC `LENGTH (args:clos_exp list) > 0` THEN
     REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC;
     ALL_TAC] THEN
   MP_TAC(ISPECL [`loc:num`; `f:clos_v`; `y2:clos_v list`; `s1:(abs_calls_state # C,FFI)clos_state`;
     `res:(clos_v list,clos_v)result`; `s':(abs_calls_state # C,FFI)clos_state`; `h':clos_v`;
     `y2':clos_v list`;
     `clos_state_clock_fupd (K (clos_state_clock (t1:(C,FFI)clos_state) + ck2)) t1`;
     `g:num_set # (num # num # clos_exp) list`; `g3:num_set # (num # num # clos_exp) list`;
     `l3:num->bool`] CLOSCALLPAUX_app_core) THEN
   ANTS_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[clos_state_INFO.ri_accfupds]) THEN
     ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds] THEN REPEAT CONJ_TAC THENL
      [FIRST_X_ASSUM(MP_TAC o SPECL [`[f:clos_v]`; `s1:(abs_calls_state # C,FFI)clos_state`] o
         check (fun th -> is_forall (concl th) &&
           can (find_term (fun t -> is_const t && fst (dest_const t) = "CLOSCALLPAUX_cc_Q")) (concl th))) THEN
       ASM_REWRITE_TAC[HD];
       MATCH_MP_TAC(GEN_ALL EVERY_wfv_subg) THEN
       MAP_EVERY EXISTS_TAC [`clos_state_code (t1:(C,FFI)clos_state)`;
         `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`] THEN
       ASM_REWRITE_TAC[SUBMAP_REFL];
       MATCH_MP_TAC(GEN_ALL LIST_REL_v_rel_subg) THEN
       MAP_EVERY EXISTS_TAC [`g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`;
         `clos_state_code (t1:(C,FFI)clos_state)`] THEN ASM_REWRITE_TAC[SUBMAP_REFL];
       MATCH_MP_TAC subg_trans THEN EXISTS_TAC `g2:num_set # (num # num # clos_exp) list` THEN
       ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   REWRITE_TAC[clos_state_INFO.ri_accfupds; CLOSCALLPAUX_clock_add_add] THEN
   DISCH_THEN(X_CHOOSE_THEN `body:clos_exp` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CLOSCALLPAUX_CHOOSE_NAMES [`ck3:num`; `res3:(clos_v list,clos_v)result`;
        `t3:(C,FFI)clos_state`; `g4:num_set # (num # num # clos_exp) list`; `l4:num->bool`]))))) THEN
  (FIRST_ASSUM(MP_TAC o SPEC `ck2 + ck3:num` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
     CLOSCALLPAUX_evaluate_add_clock_res) o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `(Rval y2':(clos_v list,clos_v)result),(t1:(C,FFI)clos_state)`)) THEN
   REWRITE_TAC[distinctness "result"] THEN DISCH_TAC THEN
   SUBGOAL_THEN `LENGTH (es:clos_exp list) = LENGTH (y2':clos_v list)` ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP clos_evaluate_IMP_LENGTH o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `(Rval y2':(clos_v list,clos_v)result),(t1:(C,FFI)clos_state)`)) THEN
     REWRITE_TAC[];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`x:tra`; `LENGTH (es:clos_exp list)`; `es:clos_exp list`; `env2:clos_v list`;
     `clos_state_clock_fupd (K (clos_state_clock (t0:(C,FFI)clos_state) + ck + ck2 + ck3)) t0`;
     `y2':clos_v list`;
     `clos_state_clock_fupd (K (clos_state_clock (t1:(C,FFI)clos_state) + ck2 + ck3)) t1`;
     `loc:num`; `body:clos_exp`] CLOSCALLPAUX_call_eq) THEN
   ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC
     `clos_state_clock_fupd (K (clos_state_clock (t1:(C,FFI)clos_state) + ck2 + ck3)) t1` o
     check (fun th -> is_forall (concl th) &&
       can (find_term (fun t -> t = `body:clos_exp`)) (concl th))) THEN
   REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN DISCH_TAC THEN
   MAP_EVERY EXISTS_TAC [`ck + ck2 + ck3:num`; `res3:(clos_v list,clos_v)result`;
     `t3:(C,FFI)clos_state`; `g4:num_set # (num # num # clos_exp) list`; `l4:num->bool`] THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC subg_trans THEN EXISTS_TAC `g3:num_set # (num # num # clos_exp) list` THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC subg_trans THEN
     EXISTS_TAC `g2:num_set # (num # num # clos_exp) list` THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l3:num->bool` THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l2:num->bool` THEN ASM_REWRITE_TAC[];
     UNDISCH_TAC `evaluate_app (SOME loc) h' y2'
       (clos_state_clock_fupd (K (clos_state_clock (t1:(C,FFI)clos_state) + ck2 + ck3)) t1) =
       res3,t3` THEN ASM_REWRITE_TAC[]]));;


(* calls_correct, case App compiled to Let + direct Call (impure function expression) *)
let CLOSCALLPAUX_cc_App_let = prove
 (`!x loc_opt x1 args env (s:(abs_calls_state # C,FFI)clos_state) y2 s1 res s'
    es e1' (g':num_set # (num # num # clos_exp) list) g g1 l1 env2 (t0:(C,FFI)clos_state)
    ck y2' t1 g2 l2 loc.
    LENGTH args > 0 /\ LENGTH es > 0 /\
    clos_evaluate (args,env,s) = (Rval y2,s1) /\
    clos_evaluate ([clos_App x loc_opt x1 args],env,s) = (res,s') /\
    (!y1 s2. clos_evaluate ([x1],env,s1) = (Rval y1,s2)
             ==> CLOSCALLPAUX_cc_Q loc_opt (HD y1) y2 s2) /\
    CLOSCALLPAUX_cc_P ([x1],env,s1) /\
    ~(res = Rerr (Rabort Rtype_error)) /\
    clos_call_calls [x1] g' = ([e1'],g) /\
    wfg g' /\
    DISJOINT (IMAGE SUC (set_of_list (code_locs [x1]))) (set_of_list (MAP FST (SND g'))) /\
    ALL_DISTINCT (code_locs [x1]) /\ every_Fn_SOME [x1] /\ every_Fn_vs_NONE [x1] /\
    subg g g1 /\ set_of_list (code_locs [x1]) DIFF domain (FST g) SUBSET l1 /\
    code_includes (SND g) (clos_state_code t0) /\
    ALL (wfv g1 l1 (clos_state_code t0)) env /\
    clos_callProof_env_rel (clos_callProof_v_rel g1 l1 (clos_state_code t0)) env env2 0
      (MAP (\x. (0,x)) [e1']) /\
    loc_opt = SOME loc /\ loc IN domain (FST g) /\ wfg g /\
    clos_evaluate (es,env2,clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) =
      (Rval y2',t1) /\
    code_inv (SOME g2) l2 (clos_state_code s1) (clos_state_compile s1)
      (clos_state_compile_oracle s1) (clos_state_code t1) (clos_state_compile t1)
      (clos_state_compile_oracle t1) /\
    wfv_state g2 l2 (clos_state_code t1) s1 /\
    subg g1 g2 /\ wfg g2 /\ l1 SUBSET l2 /\ DISJOINT l2 (domain (FST g2)) /\
    ALL (wfv g2 l2 (clos_state_code t1)) y2 /\
    clos_callProof_state_rel g2 l2 s1 t1 /\
    ALL2 (clos_callProof_v_rel g2 l2 (clos_state_code t1)) y2 y2' /\
    clos_state_code t0 SUBMAP clos_state_code t1
    ==> ?ck res' t g3 l3.
          code_inv (SOME g3) l3 (clos_state_code s') (clos_state_compile s')
            (clos_state_compile_oracle s') (clos_state_code t) (clos_state_compile t)
            (clos_state_compile_oracle t) /\
          wfv_state g3 l3 (clos_state_code t) s' /\
          subg g1 g3 /\ wfg g3 /\ l1 SUBSET l3 /\ DISJOINT l3 (domain (FST g3)) /\
          every_result (ALL (wfv g3 l3 (clos_state_code t))) (wfv g3 l3 (clos_state_code t))
            res /\
          clos_evaluate ([clos_Let (mk_cons x 0) (SNOC e1' es)
              (clos_Call (mk_cons x 1) (LENGTH es) (loc + 1)
                 (GENLIST_Var backend_common_None 2 (LENGTH es)))],env2,
            clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) = (res',t) /\
          clos_callProof_state_rel g3 l3 s' t /\
          result_rel (ALL2 (clos_callProof_v_rel g3 l3 (clos_state_code t)))
            (clos_callProof_v_rel g3 l3 (clos_state_code t)) res res'`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     lhs (concl th) = `loc_opt:num option`)) THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     rand (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
   GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [clos_evaluate_def] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   SUBGOAL_THEN `?r2 s2. clos_evaluate ([x1],env,(s1:(abs_calls_state # C,FFI)clos_state)) = (r2,s2)`
     STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC) THEN
  (SUBGOAL_THEN `~(r2 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
     CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
     UNDISCH_TAC `~(res = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN
    `ALL (wfv g2 l2 (clos_state_code (t1:(C,FFI)clos_state))) env /\
     clos_callProof_env_rel (clos_callProof_v_rel g2 l2 (clos_state_code t1)) env env2 0
       (MAP (\x. (0,x)) [e1']) /\
     subg (g:num_set # (num # num # clos_exp) list) g2 /\
     set_of_list (code_locs [x1]) DIFF domain (FST g) SUBSET l2 /\
     code_includes (SND g) (clos_state_code t1)` STRIP_ASSUME_TAC THENL
    [REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC(GEN_ALL EVERY_wfv_subg) THEN
       MAP_EVERY EXISTS_TAC [`clos_state_code (t0:(C,FFI)clos_state)`;
         `g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`] THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC(GEN_ALL env_rel_subg) THEN
       MAP_EVERY EXISTS_TAC [`g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`;
         `clos_state_code (t0:(C,FFI)clos_state)`] THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC subg_trans THEN EXISTS_TAC `g1:num_set # (num # num # clos_exp) list` THEN
       ASM_REWRITE_TAC[];
       MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l1:num->bool` THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC(GEN_ALL code_includes_SUBMAP) THEN
       EXISTS_TAC `clos_state_code (t0:(C,FFI)clos_state)` THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSCALLPAUX_cc_P_def] o check (fun th ->
     concl th = `CLOSCALLPAUX_cc_P ([x1],env,(s1:(abs_calls_state # C,FFI)clos_state))`)) THEN
   DISCH_THEN(MP_TAC o SPECL [`g':num_set # (num # num # clos_exp) list`;
     `g:num_set # (num # num # clos_exp) list`; `env2:clos_v list`; `t1:(C,FFI)clos_state`;
     `[e1':clos_exp]`; `r2:(clos_v list,clos_v)result`; `s2:(abs_calls_state # C,FFI)clos_state`;
     `set_of_list (code_locs [x1]) DIFF domain (FST (g:num_set # (num # num # clos_exp) list))`;
     `l2:num->bool`; `g2:num_set # (num # num # clos_exp) list`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck2:num`; `r2':(clos_v list,clos_v)result`;
     `t2:(C,FFI)clos_state`; `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`]) THEN
   FIRST_ASSUM(MP_TAC o SPEC `ck2:num` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
     CLOSCALLPAUX_evaluate_add_clock_res) o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `(Rval y2':(clos_v list,clos_v)result),(t1:(C,FFI)clos_state)`)) THEN
   REWRITE_TAC[distinctness "result"] THEN DISCH_TAC THEN
   SUBGOAL_THEN `clos_state_code (t1:(C,FFI)clos_state) SUBMAP clos_state_code (t2:(C,FFI)clos_state)`
     ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP clos_evaluate_mono o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `r2':(clos_v list,clos_v)result,(t2:(C,FFI)clos_state)`)) THEN
     REWRITE_TAC[clos_state_INFO.ri_accfupds];
     ALL_TAC] THEN
   MP_TAC(ISPEC `r2:(clos_v list,clos_v)result` (cases "result")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `y1:clos_v list` SUBST_ALL_TAC)
     (X_CHOOSE_THEN `err:clos_v error_result` SUBST_ALL_TAC)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[result_rel_Rval; result_rel_Rerr1; every_result_def]) THEN
   REPEAT (FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     lhs (concl th) = `r2':(clos_v list,clos_v)result`))) THENL
  [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP clos_evaluate_SING o check (fun th -> is_eq (concl th) &&
     rand (concl th) = `(Rval y1:(clos_v list,clos_v)result),(s2:(abs_calls_state # C,FFI)clos_state)`)) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     lhs (concl th) = `y1:clos_v list`)) THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[HD; LIST_REL_CONS1; LIST_REL_NIL; ALL]) THEN
   REPEAT (FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
   RVEQ_TAC THEN
   SUBGOAL_THEN `~(y2:clos_v list = [])` ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP clos_evaluate_IMP_LENGTH o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `(Rval y2:(clos_v list,clos_v)result),(s1:(abs_calls_state # C,FFI)clos_state)`)) THEN
     UNDISCH_TAC `LENGTH (args:clos_exp list) > 0` THEN
     REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC;
     ALL_TAC] THEN
   MP_TAC(ISPECL [`loc:num`; `r1:clos_v`; `y2:clos_v list`; `s2:(abs_calls_state # C,FFI)clos_state`;
     `res:(clos_v list,clos_v)result`; `s':(abs_calls_state # C,FFI)clos_state`; `h':clos_v`;
     `y2':clos_v list`; `t2:(C,FFI)clos_state`;
     `g:num_set # (num # num # clos_exp) list`; `g3:num_set # (num # num # clos_exp) list`;
     `l3:num->bool`] CLOSCALLPAUX_app_core) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
      [FIRST_X_ASSUM(MP_TAC o SPECL [`[r1:clos_v]`; `s2:(abs_calls_state # C,FFI)clos_state`] o
         check (fun th -> is_forall (concl th) &&
           can (find_term (fun t -> is_const t && fst (dest_const t) = "CLOSCALLPAUX_cc_Q")) (concl th))) THEN
       ASM_REWRITE_TAC[HD];
       MATCH_MP_TAC(GEN_ALL EVERY_wfv_subg) THEN
       MAP_EVERY EXISTS_TAC [`clos_state_code (t1:(C,FFI)clos_state)`;
         `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`] THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC(GEN_ALL LIST_REL_v_rel_subg) THEN
       MAP_EVERY EXISTS_TAC [`g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`;
         `clos_state_code (t1:(C,FFI)clos_state)`] THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC subg_trans THEN EXISTS_TAC `g2:num_set # (num # num # clos_exp) list` THEN
       ASM_REWRITE_TAC[];
       MATCH_MP_TAC(GEN_ALL code_includes_SUBMAP) THEN
       EXISTS_TAC `clos_state_code (t1:(C,FFI)clos_state)` THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `body:clos_exp` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CLOSCALLPAUX_CHOOSE_NAMES [`ck3:num`; `res3:(clos_v list,clos_v)result`;
        `t3:(C,FFI)clos_state`; `g4:num_set # (num # num # clos_exp) list`; `l4:num->bool`])))) THEN
   FIRST_ASSUM(MP_TAC o SPEC `ck2 + ck3:num` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
     CLOSCALLPAUX_evaluate_add_clock_res) o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `(Rval y2':(clos_v list,clos_v)result),(t1:(C,FFI)clos_state)`)) THEN
   REWRITE_TAC[distinctness "result"] THEN DISCH_TAC THEN
   FIRST_ASSUM(MP_TAC o SPEC `ck3:num` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
     CLOSCALLPAUX_evaluate_add_clock_res) o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `(Rval [h']:(clos_v list,clos_v)result),(t2:(C,FFI)clos_state)`)) THEN
   REWRITE_TAC[distinctness "result"] THEN DISCH_TAC THEN
   SUBGOAL_THEN `LENGTH (es:clos_exp list) = LENGTH (y2':clos_v list)` ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP clos_evaluate_IMP_LENGTH o check (fun th -> is_eq (concl th) &&
       rand (concl th) = `(Rval y2':(clos_v list,clos_v)result),(t1:(C,FFI)clos_state)`)) THEN
     REWRITE_TAC[];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`mk_cons x 0`; `mk_cons x 1`; `es:clos_exp list`; `e1':clos_exp`; `env2:clos_v list`;
     `clos_state_clock_fupd (K (clos_state_clock (t0:(C,FFI)clos_state) + ck + ck2 + ck3)) t0`;
     `y2':clos_v list`;
     `clos_state_clock_fupd (K (clos_state_clock (t1:(C,FFI)clos_state) + ck2 + ck3)) t1`;
     `h':clos_v`;
     `clos_state_clock_fupd (K (clos_state_clock (t2:(C,FFI)clos_state) + ck3)) t2`;
     `loc:num`; `body:clos_exp`] CLOSCALLPAUX_let_call_eq) THEN
   ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC
     `clos_state_clock_fupd (K (clos_state_clock (t2:(C,FFI)clos_state) + ck3)) t2` o
     check (fun th -> is_forall (concl th) &&
       can (find_term (fun t -> t = `body:clos_exp`)) (concl th))) THEN
   REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN DISCH_TAC THEN
   MAP_EVERY EXISTS_TAC [`ck + ck2 + ck3:num`; `res3:(clos_v list,clos_v)result`;
     `t3:(C,FFI)clos_state`; `g4:num_set # (num # num # clos_exp) list`; `l4:num->bool`] THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC subg_trans THEN EXISTS_TAC `g3:num_set # (num # num # clos_exp) list` THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC subg_trans THEN
     EXISTS_TAC `g2:num_set # (num # num # clos_exp) list` THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l3:num->bool` THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l2:num->bool` THEN ASM_REWRITE_TAC[];
     UNDISCH_TAC `evaluate_app (SOME loc) h' y2'
       (clos_state_clock_fupd (K (clos_state_clock (t2:(C,FFI)clos_state) + ck3)) t2) =
       res3,t3` THEN ASM_REWRITE_TAC[]];
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     rand (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
   CASE_REWRITE_TAC[PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   MAP_EVERY EXISTS_TAC [`ck + ck2:num`; `Rerr e':(clos_v list,clos_v)result`;
     `t2:(C,FFI)clos_state`; `g3:num_set # (num # num # clos_exp) list`; `l3:num->bool`] THEN
   ASM_REWRITE_TAC[every_result_def; result_rel_def] THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC subg_trans THEN EXISTS_TAC `g2:num_set # (num # num # clos_exp) list` THEN
     ASM_REWRITE_TAC[];
     MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `l2:num->bool` THEN ASM_REWRITE_TAC[];
     GEN_REWRITE_TAC LAND_CONV [clos_evaluate_def] THEN
     REWRITE_TAC[SNOC_APPEND; clos_evaluate_append] THEN ASM_REWRITE_TAC[] THEN
     REPEAT (CHANGED_TAC (CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]))]]);;


(* calls_correct, case App: the argument evaluation, shared by the three *)
(* compiled forms (direct call, Let and call, App)                         *)
let CLOSCALLPAUX_APP_IH3_TAC (lo:term) : tactic =
  SUBGOAL_THEN `?r1 s1. clos_evaluate (args,env,(s:(abs_calls_state # C,FFI)clos_state)) = (r1,s1)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      rand (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [clos_evaluate_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    UNDISCH_TAC `~(res = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSCALLPAUX_cc_P_def] o check (fun th ->
    concl th = `CLOSCALLPAUX_cc_P (args,env,(s:(abs_calls_state # C,FFI)clos_state))`)) THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:num_set # (num # num # clos_exp) list`;
    `g':num_set # (num # num # clos_exp) list`; `env2:clos_v list`; `t0:(C,FFI)clos_state`;
    `es':clos_exp list`; `r1:(clos_v list,clos_v)result`;
    `s1:(abs_calls_state # C,FFI)clos_state`;
    `set_of_list (code_locs (args:clos_exp list)) DIFF
     domain (FST (g':num_set # (num # num # clos_exp) list))`;
    `l1:num->bool`; `g1:num_set # (num # num # clos_exp) list`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CLOSCALLPAUX_CHOOSE_NAMES [`ck:num`; `res1:(clos_v list,clos_v)result`;
    `t1:(C,FFI)clos_state`; `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`]) THEN
  MP_TAC(ISPEC `r1:(clos_v list,clos_v)result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `y2:clos_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `err:clos_v error_result` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[result_rel_Rval; result_rel_Rerr1; every_result_def]) THEN
  REPEAT (FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `res1:(clos_v list,clos_v)result`)) THENL
   [SUBGOAL_THEN `clos_state_code (t0:(C,FFI)clos_state) SUBMAP clos_state_code (t1:(C,FFI)clos_state)`
      ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP clos_evaluate_mono o check (fun th -> is_eq (concl th) &&
        rand (concl th) = `(Rval v':(clos_v list,clos_v)result),(t1:(C,FFI)clos_state)`)) THEN
      REWRITE_TAC[clos_state_INFO.ri_accfupds];
      ALL_TAC] THEN
    SUBGOAL_THEN
     (subst [lo,`loc_opt:num option`]
      `(!y1 s2. clos_evaluate ([x1],env,(s1:(abs_calls_state # C,FFI)clos_state)) = (Rval y1,s2)
               ==> CLOSCALLPAUX_cc_Q loc_opt (HD y1) y2 s2) /\
      CLOSCALLPAUX_cc_P ([x1],env,s1)`) STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        MAP_EVERY EXISTS_TAC [`s1:(abs_calls_state # C,FFI)clos_state`] THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `y2:clos_v list` THEN ASM_REWRITE_TAC[]];
      ALL_TAC];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      rand (concl th) = `res:(clos_v list,clos_v)result,s':(abs_calls_state # C,FFI)clos_state`)) THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [clos_evaluate_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `Rerr e':(clos_v list,clos_v)result`; `t1:(C,FFI)clos_state`;
      `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`] THEN
    ASM_REWRITE_TAC[every_result_def; result_rel_def] THEN
    GEN_REWRITE_TAC LAND_CONV [clos_evaluate_def] THEN
    REWRITE_TAC[SNOC_APPEND; clos_evaluate_append] THEN ASM_REWRITE_TAC[] THEN
    REPEAT (CHANGED_TAC (CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]))];;

let CLOSCALLPAUX_APP_LOC_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_conj (concl th) &&
    can (find_term (fun t -> is_const t && fst (dest_const t) = "IS_SOME")) (concl th))) THEN
  REWRITE_TAC[IS_SOME_EXISTS] THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `loc:num` SUBST_ALL_TAC o check (fun th -> is_exists (concl th) &&
    (let (_,b) = dest_exists (concl th) in is_eq b && lhs b = `loc_opt:num option`))) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[GSYM domain_lookup] o check (fun th ->
    is_exists (concl th) && can (find_term (fun t -> is_const t && fst (dest_const t) = "lookup")) (concl th)));;

(* calls_correct, case App (HOL4 "App") *)
let CLOSCALLPAUX_cc_App = prove
 (CLOSCALLPAUX_cc_case 10,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[CLOSCALLPAUX_cc_P_def] THEN
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC[clos_call_calls_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   REPEAT IL1AUX_PAIRARG_TAC THEN STRIP_TAC) THEN
  (FIRST_ASSUM(X_CHOOSE_THEN `ex:clos_exp` SUBST_ALL_TAC o MATCH_MP calls_sing o check (fun th ->
     is_eq (concl th) && rand (concl th) = `e1':clos_exp list,g'':num_set # (num # num # clos_exp) list`)) THEN
   SUBGOAL_THEN `LENGTH (args:clos_exp list) > 0` ASSUME_TAC THENL
    [UNDISCH_TAC `clos_evaluate ([clos_App x loc_opt x1 args],env,(s:(abs_calls_state # C,FFI)clos_state)) =
                  (res,s')` THEN
     GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [clos_evaluate_def] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
     UNDISCH_TAC `~(res = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   RULE_ASSUM_TAC(fun th -> if concl th = `LENGTH (args:clos_exp list) > 0` then th
     else REWRITE_RULE[ASSUME `LENGTH (args:clos_exp list) > 0`] th) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[code_locs_def; every_Fn_SOME_def; every_Fn_vs_NONE_def;
     LET_DEF; LET_END_DEF]) THEN
   CLOSCALLPAUX_SPLIT_ASM_TAC THEN
   MP_TAC(ISPECL [`args:clos_exp list`; `[x1:clos_exp]`;
     `g0:num_set # (num # num # clos_exp) list`; `g':num_set # (num # num # clos_exp) list`;
     `g'':num_set # (num # num # clos_exp) list`; `es':clos_exp list`; `[ex:clos_exp]`]
     CLOSCALLPAUX_calls_chain) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[ALL_DISTINCT_APPEND'; SET_OF_LIST_APPEND; IMAGE_UNION;
       DISJOINT_UNION]) THEN
     ASM_REWRITE_TAC[ALL_DISTINCT_APPEND'; SET_OF_LIST_APPEND; IMAGE_UNION; DISJOINT_UNION] THEN
     ASM_MESON_TAC[DISJOINT_SYM];
     ALL_TAC] THEN
   STRIP_TAC) THEN
  (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     rand (concl th) = `ys:clos_exp list,g:num_set # (num # num # clos_exp) list`)) THEN
   DISCH_THEN(fun th -> ASSUME_TAC th THEN
     SUBGOAL_THEN `(g:num_set # (num # num # clos_exp) list) = g''` SUBST_ALL_TAC THENL
      [UNDISCH_TAC (concl th) THEN REPEAT COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
       ALL_TAC]) THEN
   SUBGOAL_THEN
    `ALL_DISTINCT (code_locs (args:clos_exp list)) /\ ALL_DISTINCT (code_locs [x1]) /\
     DISJOINT (IMAGE SUC (set_of_list (code_locs args)))
       (set_of_list (MAP FST (SND (g0:num_set # (num # num # clos_exp) list)))) /\
     set_of_list (code_locs args) DIFF domain (FST (g':num_set # (num # num # clos_exp) list))
       SUBSET l1 /\
     set_of_list (code_locs [x1]) DIFF domain (FST (g'':num_set # (num # num # clos_exp) list))
       SUBSET l1 /\
     subg g' g1 /\ code_includes (SND g') (clos_state_code (t0:(C,FFI)clos_state)) /\
     LENGTH (es':clos_exp list) > 0`
     STRIP_ASSUME_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[ALL_DISTINCT_APPEND'; SET_OF_LIST_APPEND; IMAGE_UNION;
       DISJOINT_UNION]) THEN
     ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
      [UNDISCH_TAC `l SUBSET (l1:num->bool)` THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_SET_OF_LIST] THEN ASM_MESON_TAC[];
       UNDISCH_TAC `l SUBSET (l1:num->bool)` THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_SET_OF_LIST] THEN MESON_TAC[];
       MATCH_MP_TAC subg_trans THEN EXISTS_TAC `g'':num_set # (num # num # clos_exp) list` THEN
       ASM_REWRITE_TAC[];
       MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (GEN_ALL code_includes_subg)) THEN
       EXISTS_TAC `g'':num_set # (num # num # clos_exp) list` THEN ASM_REWRITE_TAC[];
       FIRST_ASSUM(MP_TAC o MATCH_MP calls_length o check (fun th -> is_eq (concl th) &&
         rand (concl th) = `es':clos_exp list,g':num_set # (num # num # clos_exp) list`)) THEN
       ASM_SIMP_TAC[]];
     ALL_TAC]) THEN
  (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     rand (concl th) = `ys:clos_exp list,g'':num_set # (num # num # clos_exp) list`)) THEN
   COND_CASES_TAC THENL [COND_CASES_TAC; ALL_TAC] THEN
   REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM)) THENL
  [CLOSCALLPAUX_APP_LOC_TAC THEN
   SUBGOAL_THEN
    `clos_callProof_env_rel (clos_callProof_v_rel g1 l1 (clos_state_code (t0:(C,FFI)clos_state)))
       env env2 0 (MAP (\x. (0,x)) es')` ASSUME_TAC THENL
    [MATCH_MP_TAC CLOSCALLPAUX_env_rel_MAP0_mono THEN
     EXISTS_TAC `[clos_Call x (LENGTH (es':clos_exp list)) (loc + 1) es']` THEN
     ASM_REWRITE_TAC[clos_fv_def] THEN MESON_TAC[];
     ALL_TAC] THEN
   CLOSCALLPAUX_APP_IH3_TAC `SOME loc:num option` THEN
   MP_TAC(ISPECL [`x:tra`; `SOME loc:num option`; `x1:clos_exp`; `args:clos_exp list`;
     `env:clos_v list`; `s:(abs_calls_state # C,FFI)clos_state`; `y2:clos_v list`;
     `s1:(abs_calls_state # C,FFI)clos_state`; `res:(clos_v list,clos_v)result`;
     `s':(abs_calls_state # C,FFI)clos_state`; `es':clos_exp list`; `ex:clos_exp`;
     `g':num_set # (num # num # clos_exp) list`; `g'':num_set # (num # num # clos_exp) list`;
     `g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`; `env2:clos_v list`;
     `t0:(C,FFI)clos_state`; `ck:num`; `v':clos_v list`; `t1:(C,FFI)clos_state`;
     `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`; `loc:num`]
     CLOSCALLPAUX_cc_App_call) THEN
   ASM_REWRITE_TAC[];
   CLOSCALLPAUX_APP_LOC_TAC THEN REWRITE_TAC[HD] THEN RULE_ASSUM_TAC(REWRITE_RULE[HD]) THEN
   SUBGOAL_THEN
    `clos_callProof_env_rel (clos_callProof_v_rel g1 l1 (clos_state_code (t0:(C,FFI)clos_state)))
       env env2 0 (MAP (\x. (0,x)) es') /\
     clos_callProof_env_rel (clos_callProof_v_rel g1 l1 (clos_state_code t0))
       env env2 0 (MAP (\x. (0,x)) [ex])` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC CLOSCALLPAUX_env_rel_MAP0_mono THEN
     EXISTS_TAC `[clos_Let (mk_cons x 0) (SNOC ex es')
                    (clos_Call (mk_cons x 1) (LENGTH (es':clos_exp list)) (loc + 1)
                       (GENLIST_Var backend_common_None 2 (LENGTH es')))]` THEN
     ASM_REWRITE_TAC[clos_fv_def; SNOC_APPEND; fv_append] THEN MESON_TAC[];
     ALL_TAC] THEN
   CLOSCALLPAUX_APP_IH3_TAC `SOME loc:num option` THEN
   MP_TAC(ISPECL [`x:tra`; `SOME loc:num option`; `x1:clos_exp`; `args:clos_exp list`;
     `env:clos_v list`; `s:(abs_calls_state # C,FFI)clos_state`; `y2:clos_v list`;
     `s1:(abs_calls_state # C,FFI)clos_state`; `res:(clos_v list,clos_v)result`;
     `s':(abs_calls_state # C,FFI)clos_state`; `es':clos_exp list`; `ex:clos_exp`;
     `g':num_set # (num # num # clos_exp) list`; `g'':num_set # (num # num # clos_exp) list`;
     `g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`; `env2:clos_v list`;
     `t0:(C,FFI)clos_state`; `ck:num`; `v':clos_v list`; `t1:(C,FFI)clos_state`;
     `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`; `loc:num`]
     CLOSCALLPAUX_cc_App_let) THEN
   ASM_REWRITE_TAC[HD];
   REWRITE_TAC[HD] THEN RULE_ASSUM_TAC(REWRITE_RULE[HD]) THEN
   SUBGOAL_THEN
    `clos_callProof_env_rel (clos_callProof_v_rel g1 l1 (clos_state_code (t0:(C,FFI)clos_state)))
       env env2 0 (MAP (\x. (0,x)) es') /\
     clos_callProof_env_rel (clos_callProof_v_rel g1 l1 (clos_state_code t0))
       env env2 0 (MAP (\x. (0,x)) [ex])` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC CLOSCALLPAUX_env_rel_MAP0_mono THEN
     EXISTS_TAC `[clos_App x loc_opt ex es']` THEN ASM_REWRITE_TAC[clos_fv_def] THEN MESON_TAC[];
     ALL_TAC] THEN
   CLOSCALLPAUX_APP_IH3_TAC `loc_opt:num option` THEN
   MP_TAC(ISPECL [`x:tra`; `loc_opt:num option`; `x1:clos_exp`; `args:clos_exp list`;
     `env:clos_v list`; `s:(abs_calls_state # C,FFI)clos_state`; `y2:clos_v list`;
     `s1:(abs_calls_state # C,FFI)clos_state`; `res:(clos_v list,clos_v)result`;
     `s':(abs_calls_state # C,FFI)clos_state`; `es':clos_exp list`; `ex:clos_exp`;
     `g':num_set # (num # num # clos_exp) list`; `g'':num_set # (num # num # clos_exp) list`;
     `g1:num_set # (num # num # clos_exp) list`; `l1:num->bool`; `env2:clos_v list`;
     `t0:(C,FFI)clos_state`; `ck:num`; `v':clos_v list`; `t1:(C,FFI)clos_state`;
     `g2:num_set # (num # num # clos_exp) list`; `l2:num->bool`] CLOSCALLPAUX_cc_App_app) THEN
   ASM_REWRITE_TAC[]]);;

(* calls_correct: the main simulation theorem, by evaluate induction from the cases *)
let CLOSCALLPAUX_cc_cases = [CLOSCALLPAUX_cc_NIL; CLOSCALLPAUX_cc_CONS; CLOSCALLPAUX_cc_Var;
  CLOSCALLPAUX_cc_If; CLOSCALLPAUX_cc_Let; CLOSCALLPAUX_cc_Raise; CLOSCALLPAUX_cc_Handle;
  CLOSCALLPAUX_cc_Op; CLOSCALLPAUX_cc_Fn; CLOSCALLPAUX_cc_Letrec; CLOSCALLPAUX_cc_App;
  CLOSCALLPAUX_cc_Tick; CLOSCALLPAUX_cc_Call; CLOSCALLPAUX_cc_app_NIL; CLOSCALLPAUX_cc_app_CONS];;

let calls_correct = prove
 (`(!tmp xs env1 (s0:(abs_calls_state # C,FFI)clos_state)
       (g0:num_set # (num # num # clos_exp) list) g env2 (t0:(C,FFI)clos_state)
       ys res s l l1 g1.
     tmp = (xs,env1,s0) /\
     clos_evaluate (xs,env1,s0) = (res,s) /\
     ~(res = Rerr (Rabort Rtype_error)) /\
     clos_call_calls xs g0 = (ys,g) /\
     code_inv (SOME g1) l1 (clos_state_code s0) (clos_state_compile s0)
       (clos_state_compile_oracle s0) (clos_state_code t0) (clos_state_compile t0)
       (clos_state_compile_oracle t0) /\
     every_Fn_SOME xs /\ every_Fn_vs_NONE xs /\
     ALL (wfv g1 l1 (clos_state_code t0)) env1 /\ wfv_state g1 l1 (clos_state_code t0) s0 /\
     wfg g0 /\
     ALL_DISTINCT (code_locs xs) /\
     DISJOINT (IMAGE SUC (set_of_list (code_locs xs))) (set_of_list (MAP FST (SND g0))) /\
     l = set_of_list (code_locs xs) DIFF domain (FST g) /\
     subg g g1 /\ l SUBSET l1 /\ DISJOINT l1 (domain (FST g1)) /\ wfg g1 /\
     clos_callProof_env_rel (clos_callProof_v_rel g1 l1 (clos_state_code t0)) env1 env2 0
       (MAP (\x. (0,x)) ys) /\
     clos_callProof_state_rel g1 l1 s0 t0 /\ code_includes (SND g) (clos_state_code t0)
     ==> ?ck res' t g2 l2.
           code_inv (SOME g2) l2 (clos_state_code s) (clos_state_compile s)
             (clos_state_compile_oracle s) (clos_state_code t) (clos_state_compile t)
             (clos_state_compile_oracle t) /\
           wfv_state g2 l2 (clos_state_code t) s /\
           subg g1 g2 /\ wfg g2 /\ l1 SUBSET l2 /\ DISJOINT l2 (domain (FST g2)) /\
           every_result (ALL (wfv g2 l2 (clos_state_code t))) (wfv g2 l2 (clos_state_code t))
             res /\
           clos_evaluate (ys,env2,clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) =
             (res',t) /\
           clos_callProof_state_rel g2 l2 s t /\
           result_rel (ALL2 (clos_callProof_v_rel g2 l2 (clos_state_code t)))
             (clos_callProof_v_rel g2 l2 (clos_state_code t)) res res') /\
   (!loco f args (s0:(abs_calls_state # C,FFI)clos_state) (loc:L) g l (t0:(C,FFI)clos_state)
       res s f' args'.
     evaluate_app loco f args s0 = (res,s) /\
     ~(res = Rerr (Rabort Rtype_error)) /\
     code_inv (SOME g) l (clos_state_code s0) (clos_state_compile s0)
       (clos_state_compile_oracle s0) (clos_state_code t0) (clos_state_compile t0)
       (clos_state_compile_oracle t0) /\
     wfv g l (clos_state_code t0) f /\ ALL (wfv g l (clos_state_code t0)) args /\
     wfv_state g l (clos_state_code t0) s0 /\
     wfg g /\ DISJOINT l (domain (FST g)) /\
     clos_callProof_v_rel g l (clos_state_code t0) f f' /\
     ALL2 (clos_callProof_v_rel g l (clos_state_code t0)) args args' /\
     clos_callProof_state_rel g l s0 t0
     ==> ?ck res' t g2 l2.
           code_inv (SOME g2) l2 (clos_state_code s) (clos_state_compile s)
             (clos_state_compile_oracle s) (clos_state_code t) (clos_state_compile t)
             (clos_state_compile_oracle t) /\
           wfv_state g2 l2 (clos_state_code t) s /\
           every_result (ALL (wfv g2 l2 (clos_state_code t))) (wfv g2 l2 (clos_state_code t))
             res /\
           evaluate_app loco f' args'
             (clos_state_clock_fupd (K (clos_state_clock t0 + ck)) t0) = (res',t) /\
           clos_callProof_state_rel g2 l2 s t /\
           subg g g2 /\ wfg g2 /\ l SUBSET l2 /\ DISJOINT l2 (domain (FST g2)) /\
           result_rel (ALL2 (clos_callProof_v_rel g2 l2 (clos_state_code t)))
             (clos_callProof_v_rel g2 l2 (clos_state_code t)) res res')`,
  MP_TAC(MATCH_MP CLOSCALLPAUX_cc_ind (end_itlist CONJ CLOSCALLPAUX_cc_cases)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "P") (LABEL_TAC "Q")) THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `l:num->bool`)) THEN
    REMOVE_THEN "P" (MP_TAC o REWRITE_RULE[CLOSCALLPAUX_cc_P_def] o
      SPEC `(xs:clos_exp list,env1:clos_v list,(s0:(abs_calls_state # C,FFI)clos_state))`) THEN
    DISCH_THEN(MP_TAC o SPECL [`g0:num_set # (num # num # clos_exp) list`;
      `g:num_set # (num # num # clos_exp) list`; `env2:clos_v list`; `t0:(C,FFI)clos_state`;
      `ys:clos_exp list`; `res:(clos_v list,clos_v)result`;
      `s:(abs_calls_state # C,FFI)clos_state`;
      `set_of_list (code_locs xs) DIFF domain (FST (g:num_set # (num # num # clos_exp) list))`;
      `l1:num->bool`; `g1:num_set # (num # num # clos_exp) list`]) THEN
    ASM_REWRITE_TAC[];
    REMOVE_THEN "Q" (MP_TAC o REWRITE_RULE[CLOSCALLPAUX_cc_Q_def] o
      SPECL [`loco:num option`; `f:clos_v`; `args:clos_v list`;
             `s0:(abs_calls_state # C,FFI)clos_state`]) THEN
    DISCH_THEN(MP_TAC o SPECL [`g:num_set # (num # num # clos_exp) list`;
      `l:num->bool`; `t0:(C,FFI)clos_state`; `res:(clos_v list,clos_v)result`;
      `s:(abs_calls_state # C,FFI)clos_state`; `f':clos_v`; `args':clos_v list`]) THEN
    ASM_REWRITE_TAC[]]);;

(* code_locs of the compiled code (HOL4 code_locs_calls_list .. calls_code_locs_MEM) *)
let code_locs_calls_list = prove
 (`!ls:(num # A) list n tr i. code_locs (MAP SND (calls_list tr i n ls)) = []`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[calls_list_def; MAP; code_locs_def] THEN
  CASES_ON `h:num # A` THEN
  ASM_REWRITE_TAC[calls_list_def; MAP; SND] THEN
  ONCE_REWRITE_TAC[code_locs_cons] THEN
  ASM_REWRITE_TAC[code_locs_def; code_locs_GENLIST_Var; APPEND]);;

let code_locs_code_list_MEM = prove
 (`!ls n (rest:B # (num # num # clos_exp) list) x.
     MEM x (code_locs (MAP (SND o SND) (SND (clos_call_code_list n ls rest)))) <=>
     MEM x (code_locs (APPEND (MAP (SND o SND) (SND rest)) (MAP SND ls)))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[clos_call_code_list_def; MAP; APPEND_NIL] THEN
  CASES_ON `h:num # clos_exp` THEN REPEAT GEN_TAC THEN
  SUBST1_TAC(GSYM(ISPEC `rest:B # (num # num # clos_exp) list` PAIR)) THEN
  ASM_REWRITE_TAC[clos_call_code_list_def; MAP; SND; o_THM] THEN
  REWRITE_TAC[code_locs_append; MEM_APPEND] THEN
  ONCE_REWRITE_TAC[code_locs_cons] THEN REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[]);;

let code_locs_code_list_ALL_DISTINCT = prove
 (`!ls n (rest:B # (num # num # clos_exp) list).
     ALL_DISTINCT (code_locs (MAP (SND o SND) (SND (clos_call_code_list n ls rest)))) <=>
     ALL_DISTINCT (code_locs (APPEND (MAP (SND o SND) (SND rest)) (MAP SND ls)))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[clos_call_code_list_def; MAP; APPEND_NIL] THEN
  CASES_ON `h:num # clos_exp` THEN REPEAT GEN_TAC THEN
  SUBST1_TAC(GSYM(ISPEC `rest:B # (num # num # clos_exp) list` PAIR)) THEN
  ASM_REWRITE_TAC[clos_call_code_list_def; MAP; SND; o_THM] THEN
  REWRITE_TAC[code_locs_append] THEN
  ONCE_REWRITE_TAC[code_locs_cons] THEN
  REWRITE_TAC[ALL_DISTINCT_APPEND'; SET_OF_LIST_APPEND] THEN SET_TAC[]);;


let CLOSCALLPAUX_code_locs_cons_MAP = prove
 (`!x (f:A->clos_exp) l. code_locs (CONS x (MAP f l)) = APPEND (code_locs [x]) (code_locs (MAP f l))`,
  REWRITE_TAC[GSYM code_locs_cons]);;
let CLOSCALLPAUX_CLM_RW = [calls_list_length; LENGTH_MAP; CLOSCALLPAUX_code_locs_cons_MAP; code_locs_def; LET_DEF; LET_END_DEF; code_locs_append; MEM_APPEND;
     MAP; o_THM; SND; FST; HD; code_locs_calls_list; code_locs_code_list_MEM; code_locs_GENLIST_Var;
     SND_insert_each; MEM; SNOC_APPEND; IS_SOME_DEF];;
let CLOSCALLPAUX_CLM_TAC : tactic =
   CLOSCALLPAUX_ADD_FACTS_TAC (fun th ->
     if CLOSCALLPAUX_is_calls_eq th then MATCH_MP calls_sing th else failwith "") THEN
   REPEAT (FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o check (fun th ->
     is_exists (concl th) && is_eq (snd(dest_exists(concl th))) &&
     is_var (lhs (snd(dest_exists(concl th))))))) THEN
   CLOSCALLPAUX_ADD_FACTS_TAC (fun th ->
     if CLOSCALLPAUX_is_calls_eq th then REWRITE_RULE[LENGTH_MAP] (MATCH_MP calls_length th)
     else failwith "") THEN
   REPEAT (FIRST_X_ASSUM(MP_TAC o SPEC `xloc:num` o check (fun th -> is_forall (concl th) &&
     fst (dest_var (fst (dest_forall (concl th)))) = "xloc"))) THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE CLOSCALLPAUX_CLM_RW) THEN
   TRY (FIRST_ASSUM(fun th -> if concl th = `F` then CONTR_TAC th else NO_TAC)) THEN
   CASE_REWRITE_TAC CLOSCALLPAUX_CLM_RW THEN
   (* drop the general induction hypotheses, instantiated in the goal by now: else   *)
   (* ASM_SIMP_TAC rewrites those instances to T (since HOL Light 2828953 its        *)
   (* satisfy_prover finds the variables of their conditions), and TAUT needs them   *)
   REPEAT (FIRST_X_ASSUM (K ALL_TAC o check (fun th -> is_forall (concl th) &&
     can (find_term (fun t -> is_abs t && fst (dest_var (bndvar t)) = "xloc")) (concl th)))) THEN
   ASM_SIMP_TAC[MAP_ZIP; LENGTH_ZIP; LENGTH_MAP] THEN
   REPEAT (FIRST_X_ASSUM(MP_TAC o check (fun th -> vfree_in `xloc:num` (concl th) &&
     not (is_forall (concl th))))) THEN
   ASM_SIMP_TAC[MAP_ZIP; LENGTH_ZIP; LENGTH_MAP] THEN CONV_TAC TAUT;;

(* All code_locs come from the original code, and therefore are all even *)
let calls_code_locs_MEM = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g.
     clos_call_calls xs g0 = (ys,g) ==>
     !xloc. (MEM xloc (code_locs ys) \/ MEM xloc (code_locs (MAP (SND o SND) (SND g)))) ==>
            (MEM xloc (code_locs xs) \/ MEM xloc (code_locs (MAP (SND o SND) (SND g0))))`,
  CLOSCALLPAUX_CALLS_IND2_TAC THEN CLOSCALLPAUX_UNWIND_IH_TAC THEN CLOSCALLPAUX_IH_CALLS_TAC THEN
  CLOSCALLPAUX_CLM_TAC);;

(* calls_code_locs_ALL_DISTINCT, proved by counting: ALL_DISTINCT l holds   *)
(* iff every value occurs at most once in l, and calls does not increase     *)
(* the number of occurrences of any location (HOL4: case analysis + metis)   *)
let CLOSCALLPAUX_FILTER_EQ_NIL = prove
 (`!t n:num. FILTER (\x. x = n) t = [] <=> ~MEM n t`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; MEM] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL] THEN ASM_MESON_TAC[]);;

let CLOSCALLPAUX_ALL_DISTINCT_COUNT = prove
 (`!l:num list. ALL_DISTINCT l <=> !n. LENGTH (FILTER (\x. x = n) l) <= 1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL_DISTINCT; FILTER; LENGTH; ARITH_RULE `0 <= 1`] THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [STRIP_TAC THEN X_GEN_TAC `n:num` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[REWRITE_RULE[GSYM CLOSCALLPAUX_FILTER_EQ_NIL] (ASSUME `~MEM (h:num) t`);
      LENGTH] THEN ARITH_TAC;
    DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `h:num`) THEN REWRITE_TAC[LENGTH] THEN
      REWRITE_TAC[GSYM CLOSCALLPAUX_FILTER_EQ_NIL; GSYM LENGTH_EQ_NIL] THEN ARITH_TAC;
      X_GEN_TAC `n:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
      COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC]]);;

let CLOSCALLPAUX_code_list_COUNT = prove
 (`!ls n (rest:B # (num # num # clos_exp) list) P.
     LENGTH (FILTER P (code_locs (MAP (SND o SND) (SND (clos_call_code_list n ls rest))))) =
     LENGTH (FILTER P (code_locs (APPEND (MAP (SND o SND) (SND rest)) (MAP SND ls))))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[clos_call_code_list_def; MAP; APPEND_NIL] THEN
  CASES_ON `h:num # clos_exp` THEN REPEAT GEN_TAC THEN
  SUBST1_TAC(GSYM(ISPEC `rest:B # (num # num # clos_exp) list` PAIR)) THEN
  ASM_REWRITE_TAC[clos_call_code_list_def; MAP; SND; o_THM] THEN
  REWRITE_TAC[code_locs_append] THEN ONCE_REWRITE_TAC[code_locs_cons] THEN
  REWRITE_TAC[FILTER_APPEND; LENGTH_APPEND] THEN ARITH_TAC);;

let CLOSCALLPAUX_CNT_RW = [calls_list_length; LENGTH_MAP; CLOSCALLPAUX_code_locs_cons_MAP;
     code_locs_def; LET_DEF; LET_END_DEF; code_locs_append; FILTER_APPEND; LENGTH_APPEND;
     MAP; o_THM; SND; FST; HD; code_locs_calls_list; CLOSCALLPAUX_code_list_COUNT;
     code_locs_GENLIST_Var; SND_insert_each; SNOC_APPEND; IS_SOME_DEF; FILTER; LENGTH];;

(* the unresolved induction hypotheses are dropped first: as conditional    *)
(* rewrites they would turn the resolved ones into T                          *)
let CLOSCALLPAUX_CNT_TAC : tactic =
   CLOSCALLPAUX_ADD_FACTS_TAC (fun th ->
     if CLOSCALLPAUX_is_calls_eq th then MATCH_MP calls_sing th else failwith "") THEN
   REPEAT (FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o check (fun th ->
     is_exists (concl th) && is_eq (snd(dest_exists(concl th))) &&
     is_var (lhs (snd(dest_exists(concl th))))))) THEN
   CLOSCALLPAUX_ADD_FACTS_TAC (fun th ->
     if CLOSCALLPAUX_is_calls_eq th then REWRITE_RULE[LENGTH_MAP] (MATCH_MP calls_length th)
     else failwith "") THEN
   REPEAT (FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_imp (snd (strip_forall (concl th)))))) THEN
   REPEAT (FIRST_X_ASSUM(MP_TAC o SPEC `cnt:num` o check (fun th -> is_forall (concl th) &&
     fst (dest_var (fst (dest_forall (concl th)))) = "cnt"))) THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE CLOSCALLPAUX_CNT_RW) THEN
   TRY (FIRST_ASSUM(fun th -> if concl th = `F` then CONTR_TAC th else NO_TAC)) THEN
   CASE_REWRITE_TAC CLOSCALLPAUX_CNT_RW THEN ASM_SIMP_TAC[MAP_ZIP; LENGTH_ZIP; LENGTH_MAP] THEN
   ARITH_TAC;;

let CLOSCALLPAUX_calls_code_locs_COUNT = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g.
     clos_call_calls xs g0 = (ys,g) ==>
     !cnt. LENGTH (FILTER (\x. x = cnt)
                    (APPEND (code_locs ys) (code_locs (MAP (SND o SND) (SND g))))) <=
           LENGTH (FILTER (\x. x = cnt)
                    (APPEND (code_locs xs) (code_locs (MAP (SND o SND) (SND g0)))))`,
  CLOSCALLPAUX_CALLS_IND2_TAC THEN CLOSCALLPAUX_UNWIND_IH_TAC THEN CLOSCALLPAUX_IH_CALLS_TAC THEN
  CLOSCALLPAUX_CNT_TAC);;

let calls_code_locs_ALL_DISTINCT = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g.
     clos_call_calls xs g0 = (ys,g) ==>
     ALL_DISTINCT (APPEND (code_locs xs) (code_locs (MAP (SND o SND) (SND g0)))) ==>
     ALL_DISTINCT (APPEND (code_locs ys) (code_locs (MAP (SND o SND) (SND g))))`,
  REWRITE_TAC[CLOSCALLPAUX_ALL_DISTINCT_COUNT] THEN
  MESON_TAC[CLOSCALLPAUX_calls_code_locs_COUNT; LE_TRANS]);;

let oracle_monotonic_init_UNION = prove
 (`oracle_monotonic (f:A->B->bool) R (A UNION B) co <=>
   oracle_monotonic f R A co /\ oracle_monotonic f R B co`,
  REWRITE_TAC[oracle_monotonic_def; IN_UNION] THEN MESON_TAC[]);;

(* clos_IMP_semantics_eq is used with the relation that is always true *)
let CLOSCALLPAUX_TRUE_REL_TAC : tactic = fun (asl,w) ->
  let v,_ = dest_exists w in
  let rec mk ty = match dest_type ty with
      ("fun",[a;b]) -> mk_abs (genvar a, mk b)
    | _ -> `T` in
  EXISTS_TAC (mk (type_of v)) (asl,w);;

let semantics_calls = prove
 (`~(clos_semantics (ffi:(FFI)ffi_state) max_app FEMPTY
       (co:num -> (abs_calls_state # C) # clos_exp list # (num # num # clos_exp) list) cc x =
     Fail) ==>
   clos_call_compile T x = (y,g0,aux) /\ every_Fn_SOME x /\ every_Fn_vs_NONE x /\
   ALL_DISTINCT (code_locs x) /\
   FST (FST (co 0)) = g0 /\
   code_inv NONE (set_of_list (code_locs x)) FEMPTY cc co (FEMPTY |++ aux) cc1 co1 ==>
   clos_semantics ffi max_app (FEMPTY |++ aux) co1 cc1 y =
   clos_semantics ffi max_app FEMPTY co cc x`,
  DISCH_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] clos_IMP_semantics_eq) THEN CLOSCALLPAUX_TRUE_REL_TAC THEN
  ASM_REWRITE_TAC[clos_eval_sim_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `clos_call_calls x (LN,[]) = (y,(g0:num_set),(aux:(num # num # clos_exp) list))`
   ASSUME_TAC THENL
   [UNDISCH_TAC `clos_call_compile T x = (y,(g0:num_set),(aux:(num # num # clos_exp) list))` THEN
    REWRITE_TAC[clos_call_compile_def] THEN
    STRUCT_CASES_TAC(ISPEC `clos_call_calls x (LN,[])` PAIR_SURJECTIVE) THEN
    CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wfg ((g0:num_set),(aux:(num # num # clos_exp) list))` ASSUME_TAC THENL
   [MATCH_MP_TAC calls_wfg THEN
    MAP_EVERY EXISTS_TAC [`x:clos_exp list`; `(LN:num_set),([]:(num # num # clos_exp) list)`;
      `y:clos_exp list`] THEN
    ASM_REWRITE_TAC[wfg_def; MAP; set_of_list; DISJOINT_EMPTY; domain_def; IMAGE_CLAUSES;
      ALL_DISTINCT; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `FEMPTY |++ aux = alist_to_fmap (aux:(num # num # clos_exp) list)` ASSUME_TAC THENL
   [REWRITE_TAC[FUPDATE_LIST_alist_to_fmap; FUNION_FEMPTY_2] THEN
    MATCH_MP_TAC ALL_DISTINCT_alist_to_fmap_REVERSE THEN
    UNDISCH_TAC `wfg ((g0:num_set),(aux:(num # num # clos_exp) list))` THEN
    SIMP_TAC[wfg_def; SND];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "code_inv" with _ -> false)) THEN
  REWRITE_TAC[code_inv_def; IS_SOME_DEF] THEN STRIP_TAC THEN
  SUBGOAL_THEN `g:num_set = g0` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(x:clos_exp list),([]:clos_v list),
      clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY
        (co:num -> (abs_calls_state # C) # clos_exp list # (num # num # clos_exp) list) cc k`;
    `x:clos_exp list`; `[]:clos_v list`;
    `clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY
       (co:num -> (abs_calls_state # C) # clos_exp list # (num # num # clos_exp) list) cc k`;
    `(LN:num_set),([]:(num # num # clos_exp) list)`;
    `(g0:num_set),(aux:(num # num # clos_exp) list)`; `[]:clos_v list`;
    `clos_initial_state (ffi:(FFI)ffi_state) max_app (FEMPTY |++ aux)
       (co1:num -> C # clos_exp list # (num # num # clos_exp) list) cc1 k`;
    `y:clos_exp list`; `res1:(clos_v list,clos_v)result`;
    `s2:(abs_calls_state # C,FFI)clos_state`;
    `set_of_list (code_locs x) DIFF domain (g0:num_set)`;
    `set_of_list (code_locs x) DIFF domain (g0:num_set)`;
    `(g0:num_set),(aux:(num # num # clos_exp) list)`] (CONJUNCT1 calls_correct)) THEN
  REPEAT (FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    is_var (lhs (concl th)) && mem (fst(dest_var(lhs (concl th)))) ["co1"; "cc"]))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[wfv_state_def; clos_callProof_state_rel_def; clos_callProof_env_rel_def;
      code_includes_def] THEN
    ASM_REWRITE_TAC[clos_initial_state_def; clos_state_INFO.ri_accessors; FST; SND; ALL;
      SUBSET_REFL] THEN
    ASM_SIMP_TAC[wfg_subg_refl; ALL; FEVERY_FEMPTY; LENGTH; ALL2;
      fmap_rel_FEMPTY; ALOOKUP_EQ_FLOOKUP;
      wfg_def; MAP; set_of_list; DISJOINT_EMPTY; domain_def; IMAGE_CLAUSES; ALL_DISTINCT;
      SET_RULE `DISJOINT (s DIFF t:num->bool) t`] THEN
    REWRITE_TAC[code_inv_def; IS_SOME_DEF] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`g0:num_set`; `aux:(num # num # clos_exp) list`] THEN
    ASM_REWRITE_TAC[SET_RULE `(s:num->bool) UNION (t DIFF s) = s UNION t`];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `res':(clos_v list,clos_v)result`; `t:(C,FFI)clos_state`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_initial_state_with_clock]) THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "result_rel" with _ -> false)) THEN
    STRUCT_CASES_TAC(ISPEC `res1:(clos_v list,clos_v)result` (cases "result")) THEN
    STRUCT_CASES_TAC(ISPEC `res':(clos_v list,clos_v)result` (cases "result")) THEN
    REWRITE_TAC[result_rel_def] THEN
    STRUCT_CASES_TAC(ISPEC `a:clos_v error_result` (cases "error_result")) THEN
    STRUCT_CASES_TAC(ISPEC `a':clos_v error_result` (cases "error_result")) THEN
    REWRITE_TAC[exc_rel_def];
    ASM_MESON_TAC[clos_callProof_state_rel_def]]);;

let clos_callProof_semantics_compile = prove
 (`~(clos_semantics (ffi:(FFI)ffi_state) max_app FEMPTY
       (co:num -> (abs_calls_state # C) # clos_exp list # (num # num # clos_exp) list) cc x =
     Fail) /\
   clos_call_compile do_call x = (y,g1,aux) /\
   (if do_call then
      clos_callProof_syntax_ok x /\ g1 = FST (FST (co 0)) /\
      code_inv NONE (set_of_list (code_locs x)) FEMPTY cc co (FEMPTY |++ aux) cc1 co1
    else cc = state_cc (CURRY I) cc1 /\
         co1 = state_co (CURRY I) co) ==>
   clos_semantics ffi max_app (FEMPTY |++ aux) co1 cc1 y =
   clos_semantics ffi max_app FEMPTY co cc x`,
  BOOL_CASES_TAC `do_call:bool` THEN REWRITE_TAC[] THEN STRIP_TAC THENL
   [MATCH_MP_TAC(GEN_ALL(REWRITE_RULE[IMP_IMP] semantics_calls)) THEN
    EXISTS_TAC `g1:num_set` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[clos_callProof_syntax_ok_def]) THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `clos_call_compile F x = (y,(g1:num_set),(aux:(num # num # clos_exp) list))` THEN
    REWRITE_TAC[clos_call_compile_def; PAIR_EQ] THEN STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
      is_var (rhs (concl th)) && mem (fst(dest_var(rhs (concl th)))) ["y"; "aux"]))) THEN
    REPEAT (FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
      is_var (lhs (concl th)) && mem (fst(dest_var(lhs (concl th)))) ["co1"; "cc"]))) THEN
    REWRITE_TAC[FUPDATE_LIST_THM] THEN MATCH_MP_TAC clos_semantics_CURRY_I THEN
    ASM_REWRITE_TAC[]]);;

let clos_callProof_nth_code_def = cake_def
  `(clos_callProof_nth_code (code:(num,num # clos_exp)fmap)
      (co:num -> (abs_calls_state # C) # clos_exp list # (num # num # clos_exp) list) 0 = code) /\
   (clos_callProof_nth_code code co (SUC k) =
      let (cfg,exp,aux) = co 0 in
      let (g',exp',aux') = clos_call_compile_inc (FST cfg) (exp,aux) in
        clos_callProof_nth_code (code |++ aux') (shift_seq 1 co) k)`;;

(* TODO: move (HOL4) *)
let FUNION_FEMPTY_FUPDATE_LIST = prove
 (`DISJOINT (FDOM (code:(A,B)fmap)) (set_of_list (MAP FST (aux:(A#B)list))) ==>
   FUNION code (FEMPTY |++ aux) = code |++ aux`,
  REWRITE_TAC[fmap_EXT; FDOM_FUPDATE_LIST; FUNION_DEF; FDOM_FEMPTY; UNION_EMPTY] THEN
  REWRITE_TAC[IN_DISJOINT; IN_UNION; IN_SET_OF_LIST] THEN DISCH_TAC THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC(GSYM FUPDATE_LIST_APPLY_NOT_MEM) THEN ASM_MESON_TAC[];
    MATCH_MP_TAC FUPDATE_SAME_LIST_APPLY THEN ASM_MESON_TAC[]]);;

(* Preservation of some label properties: every_Fn_SOME xs /\ every_Fn_vs_NONE xs *)

let every_Fn_GENLIST_Var = prove
 (`!n i t. every_Fn_SOME (GENLIST_Var t i n) /\ every_Fn_vs_NONE (GENLIST_Var t i n)`,
  INDUCT_TAC THEN ONCE_REWRITE_TAC[GENLIST_Var_def] THEN
  ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; every_Fn_SOME_def; every_Fn_vs_NONE_def;
    every_Fn_SOME_APPEND; every_Fn_vs_NONE_APPEND]);;

let CLOSCALLPAUX_every_Fn_CONS_MAP = prove
 (`!x:clos_exp (f:A->clos_exp) l.
     (every_Fn_SOME (CONS x (MAP f l)) <=> every_Fn_SOME [x] /\ every_Fn_SOME (MAP f l)) /\
     (every_Fn_vs_NONE (CONS x (MAP f l)) <=>
      every_Fn_vs_NONE [x] /\ every_Fn_vs_NONE (MAP f l))`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(REWRITE_CONV[APPEND] `APPEND [x:clos_exp] (MAP (f:A->clos_exp) l)`)) THEN
  REWRITE_TAC[every_Fn_SOME_APPEND; every_Fn_vs_NONE_APPEND]);;

let every_Fn_calls_list = prove
 (`!ls:(num # A) list n i t.
     every_Fn_SOME (MAP SND (calls_list t i n ls)) /\
     every_Fn_vs_NONE (MAP SND (calls_list t i n ls))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[calls_list_def; MAP; every_Fn_SOME_def; every_Fn_vs_NONE_def] THEN
  CASES_ON `h:num # A` THEN
  ASM_REWRITE_TAC[calls_list_def; MAP; SND; CLOSCALLPAUX_every_Fn_CONS_MAP; every_Fn_SOME_def;
    every_Fn_vs_NONE_def; every_Fn_GENLIST_Var]);;

let every_Fn_code_list = prove
 (`!ls n (rest:B # (num # num # clos_exp) list).
     (every_Fn_SOME (MAP (SND o SND) (SND (clos_call_code_list n ls rest))) <=>
      every_Fn_SOME (MAP SND ls) /\ every_Fn_SOME (MAP (SND o SND) (SND rest))) /\
     (every_Fn_vs_NONE (MAP (SND o SND) (SND (clos_call_code_list n ls rest))) <=>
      every_Fn_vs_NONE (MAP SND ls) /\ every_Fn_vs_NONE (MAP (SND o SND) (SND rest)))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[clos_call_code_list_def; MAP; every_Fn_SOME_def;
    every_Fn_vs_NONE_def] THEN
  CASES_ON `h:num # clos_exp` THEN REPEAT GEN_TAC THEN
  SUBST1_TAC(GSYM(ISPEC `rest:B # (num # num # clos_exp) list` PAIR)) THEN
  ASM_REWRITE_TAC[clos_call_code_list_def; MAP; SND; o_THM; CLOSCALLPAUX_every_Fn_CONS_MAP] THEN
  CONV_TAC TAUT);;

(* the induction cases of the preservation theorems: the resolved induction  *)
(* hypotheses moved into the goal, everything split into atomic properties   *)
(* of the subterms, then propositional logic                                  *)
let CLOSCALLPAUX_PROP_TAC (rw:thm list) : tactic =
   CLOSCALLPAUX_ADD_FACTS_TAC (fun th ->
     if CLOSCALLPAUX_is_calls_eq th then MATCH_MP calls_sing th else failwith "") THEN
   REPEAT (FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o check (fun th ->
     is_exists (concl th) && is_eq (snd(dest_exists(concl th))) &&
     is_var (lhs (snd(dest_exists(concl th))))))) THEN
   CLOSCALLPAUX_ADD_FACTS_TAC (fun th ->
     if CLOSCALLPAUX_is_calls_eq th then REWRITE_RULE[LENGTH_MAP] (MATCH_MP calls_length th)
     else failwith "") THEN
   REPEAT (FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
     let c = snd (strip_forall (concl th)) in
     is_imp c && CLOSCALLPAUX_is_calls_eq (ASSUME (lhand c))))) THEN
   REPEAT (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th)))) THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE rw) THEN
   TRY (FIRST_ASSUM(fun th -> if concl th = `F` then CONTR_TAC th else NO_TAC)) THEN
   CASE_REWRITE_TAC rw THEN ASM_SIMP_TAC[MAP_ZIP; LENGTH_ZIP; LENGTH_MAP] THEN CONV_TAC TAUT;;

let CLOSCALLPAUX_EFN_RW = [calls_list_length; LENGTH_MAP; CLOSCALLPAUX_every_Fn_CONS_MAP;
  every_Fn_SOME_def; every_Fn_vs_NONE_def; every_Fn_SOME_APPEND; every_Fn_vs_NONE_APPEND;
  LET_DEF; LET_END_DEF; MAP; o_THM; SND; FST; HD; every_Fn_calls_list; every_Fn_code_list;
  every_Fn_GENLIST_Var; SND_insert_each; SNOC_APPEND; IS_SOME_DEF];;

let calls_preserves_every_Fn_SOME = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g.
     clos_call_calls xs g0 = (ys,g) ==>
     every_Fn_SOME xs /\ every_Fn_SOME (MAP (SND o SND) (SND g0)) ==>
     every_Fn_SOME ys /\ every_Fn_SOME (MAP (SND o SND) (SND g))`,
  CLOSCALLPAUX_CALLS_IND2_TAC THEN CLOSCALLPAUX_UNWIND_IH_TAC THEN CLOSCALLPAUX_IH_CALLS_TAC THEN
  CLOSCALLPAUX_PROP_TAC CLOSCALLPAUX_EFN_RW);;

let calls_preserves_every_Fn_vs_NONE = prove
 (`!xs (g0:num_set # (num # num # clos_exp) list) ys g.
     clos_call_calls xs g0 = (ys,g) ==>
     every_Fn_vs_NONE xs /\ every_Fn_vs_NONE (MAP (SND o SND) (SND g0)) ==>
     every_Fn_vs_NONE ys /\ every_Fn_vs_NONE (MAP (SND o SND) (SND g))`,
  CLOSCALLPAUX_CALLS_IND2_TAC THEN CLOSCALLPAUX_UNWIND_IH_TAC THEN CLOSCALLPAUX_IH_CALLS_TAC THEN
  CLOSCALLPAUX_PROP_TAC CLOSCALLPAUX_EFN_RW);;

(* HOL4 has two commented-out EVAL tests here *)

(* obeys_max_app and no_Labels *)

let state_syntax_def = cake_def
  `state_syntax (f:clos_exp->bool) ((g,xs):calls_state) <=> ALL (\(x1,x2,x3). f x3) xs`;;

let CLOSCALLPAUX_state_syntax_SND = prove
 (`!f (g:calls_state). state_syntax f g <=> ALL (\x. f (SND (SND x))) (SND g)`,
  REPEAT GEN_TAC THEN SUBST1_TAC(GSYM(ISPEC `g:calls_state` PAIR)) THEN
  REWRITE_TAC[state_syntax_def; SND] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[SND]);;

let state_syntax_insert_each = prove
 (`!k1 loc (g:calls_state). state_syntax f (insert_each loc k1 g) = state_syntax f g`,
  REWRITE_TAC[CLOSCALLPAUX_state_syntax_SND; SND_insert_each]);;

let state_syntax_code_list = prove
 (`!n xs (g:calls_state).
     state_syntax f (clos_call_code_list n xs g) <=> state_syntax f g /\ ALL f (MAP SND xs)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[clos_call_code_list_def; MAP; ALL] THEN
  CASES_ON `h:num # clos_exp` THEN REPEAT GEN_TAC THEN
  SUBST1_TAC(GSYM(ISPEC `g:calls_state` PAIR)) THEN
  ASM_REWRITE_TAC[clos_call_code_list_def] THEN
  REWRITE_TAC[MAP; ALL; CLOSCALLPAUX_state_syntax_SND; SND] THEN CONV_TAC TAUT);;

let CLOSCALLPAUX_state_syntax_CONS = prove
 (`!f g (x:num # num # clos_exp) xs.
     state_syntax f (g,CONS x xs) <=> f (SND (SND x)) /\ state_syntax f (g,xs)`,
  REWRITE_TAC[CLOSCALLPAUX_state_syntax_SND; ALL; SND]);;

let obeys_max_app_GENLIST_Var = prove
 (`!n l w. ALL (obeys_max_app k) (GENLIST_Var n l w)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`l:num`,`l:num`) THEN SPEC_TAC(`w:num`,`w:num`) THEN
  INDUCT_TAC THEN ONCE_REWRITE_TAC[GENLIST_Var_def] THEN
  ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; ALL; ALL_APPEND; obeys_max_app_def]);;

let obeys_max_app_calls_list = prove
 (`!t k1 loc fns:(num # A) list. ALL (obeys_max_app k) (MAP SND (calls_list t k1 loc fns))`,
  REPEAT GEN_TAC THEN SPEC_TAC(`loc:num`,`loc:num`) THEN SPEC_TAC(`k1:num`,`k1:num`) THEN
  SPEC_TAC(`fns:(num # A) list`,`fns:(num # A) list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[calls_list_def; MAP; ALL] THEN
  CASES_ON `h:num # A` THEN
  ASM_REWRITE_TAC[calls_list_def; MAP; ALL; SND; obeys_max_app_def; obeys_max_app_GENLIST_Var]);;

let CLOSCALLPAUX_OMA_RW = [calls_list_length; LENGTH_MAP; ALL; ALL_APPEND; obeys_max_app_def;
  obeys_max_app_GENLIST_Var; obeys_max_app_calls_list; state_syntax_insert_each;
  state_syntax_code_list; CLOSCALLPAUX_state_syntax_CONS; PAIR; LET_DEF; LET_END_DEF; MAP; o_THM;
  SND; FST; HD; SNOC_APPEND; IS_SOME_DEF];;

let calls_obeys_max_app = prove
 (`!xs (g:calls_state) ys g1.
     clos_call_calls xs g = (ys,g1) /\ state_syntax (obeys_max_app k) g /\
     ALL (obeys_max_app k) xs ==>
     ALL (obeys_max_app k) ys /\ state_syntax (obeys_max_app k) g1`,
  REWRITE_TAC[IMP_CONJ] THEN
  CLOSCALLPAUX_CALLS_IND2_TAC THEN CLOSCALLPAUX_UNWIND_IH_TAC THEN CLOSCALLPAUX_IH_CALLS_TAC THEN
  CLOSCALLPAUX_PROP_TAC CLOSCALLPAUX_OMA_RW);;

let no_Labels_GENLIST_Var = prove
 (`!n l w. ALL no_Labels (GENLIST_Var n l w)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`l:num`,`l:num`) THEN SPEC_TAC(`w:num`,`w:num`) THEN
  INDUCT_TAC THEN ONCE_REWRITE_TAC[GENLIST_Var_def] THEN
  ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; ALL; ALL_APPEND; no_Labels_def]);;

let no_Labels_calls_list = prove
 (`!t k1 loc fns:(num # A) list. ALL no_Labels (MAP SND (calls_list t k1 loc fns))`,
  REPEAT GEN_TAC THEN SPEC_TAC(`loc:num`,`loc:num`) THEN SPEC_TAC(`k1:num`,`k1:num`) THEN
  SPEC_TAC(`fns:(num # A) list`,`fns:(num # A) list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[calls_list_def; MAP; ALL] THEN
  CASES_ON `h:num # A` THEN
  ASM_REWRITE_TAC[calls_list_def; MAP; ALL; SND; no_Labels_def; no_Labels_GENLIST_Var]);;

let CLOSCALLPAUX_NL_RW = [calls_list_length; LENGTH_MAP; ALL; ALL_APPEND; no_Labels_def;
  no_Labels_GENLIST_Var; no_Labels_calls_list; state_syntax_insert_each;
  state_syntax_code_list; CLOSCALLPAUX_state_syntax_CONS; PAIR; LET_DEF; LET_END_DEF; MAP; o_THM;
  SND; FST; HD; SNOC_APPEND; IS_SOME_DEF];;
let calls_no_Labels = prove
 (`!xs (g:calls_state) ys g1.
     clos_call_calls xs g = (ys,g1) /\ state_syntax no_Labels g /\
     ALL no_Labels xs ==>
     ALL no_Labels ys /\ state_syntax no_Labels g1`,
  REWRITE_TAC[IMP_CONJ] THEN
  CLOSCALLPAUX_CALLS_IND2_TAC THEN CLOSCALLPAUX_UNWIND_IH_TAC THEN CLOSCALLPAUX_IH_CALLS_TAC THEN
  CLOSCALLPAUX_PROP_TAC CLOSCALLPAUX_NL_RW);;
