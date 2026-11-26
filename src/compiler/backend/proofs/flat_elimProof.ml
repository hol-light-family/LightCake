(* ========================================================================= *)
(* flat_elimProof: port of HOL4 compiler/backend/proofs/flat_elimProofScript *)
(* .sml (CakeML v3479).  Correctness proof for flatLang dead code            *)
(* elimination.                                                              *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/sptree.ml";;
needs "hol4/spt_closure.ml";;
needs "hol4/bag.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/flat_elim.ml";;
needs "compiler/backend/semantics/flatSem.ml";;
needs "compiler/backend/semantics/flatProps.ml";;

type_invention_error := true;;
(* LEMMAS *)

(* HOL4 comments out wf_find_loc_wf_find_locL ... wf_find_lookups *)

let is_pure_EVERY_aconv = prove
 (`!es. ALL (\a. flat_elim_is_pure a) es <=> ALL flat_elim_is_pure es`,
  REWRITE_TAC[ETA_AX]);;

let find_lookupsL_MEM = prove
 (`!e es. MEM e es ==> domain (find_lookups e) SUBSET domain (find_lookupsL es)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; find_lookups_def; domain_union] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_UNION] THEN ASM SET_TAC[]);;

let find_lookupsL_APPEND = prove
 (`!l1 l2. find_lookupsL (APPEND l1 l2) =
           sptree_union (find_lookupsL l1) (find_lookupsL l2)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; find_lookups_def; union_LN; union_assoc]);;

let find_lookupsL_REVERSE = prove
 (`!l. find_lookupsL l = find_lookupsL (REVERSE l)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REVERSE; find_lookups_def; find_lookupsL_APPEND; union_LN] THEN
  MATCH_ACCEPT_TAC union_num_set_sym);;

let find_loc_EVERY_isEmpty = prove
 (`!l (reachable:num_set).
     ALL (\e. sptree_inter (find_loc e) reachable = LN) l <=>
     sptree_inter (find_locL l) reachable = LN`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL; find_loc_def; inter_LN; inter_union_empty]);;

(* DEFINITIONS *)

(* HOL4's v3_size is pair_size mlstring_size flat_v_size *)

let SUM_MAP_v3_size = prove
 (`!xs. SUM (MAP (pair_size mlstring_size flat_v_size) xs) =
        LENGTH xs + SUM (MAP (mlstring_size o FST) xs) +
        SUM (MAP (flat_v_size o SND) xs)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; SUM; LENGTH; ADD_CLAUSES] THEN
  SPEC_TAC(`h:mlstring#flat_v`,`p:mlstring#flat_v`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_size_THM; o_THM; FST; SND] THEN ARITH_TAC);;
(* termination of the functions on values: the size of an environment is   *)
(* that of its bindings (flatProps v_size_aux)                              *)

let FLATPAUX_V_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  REWRITE_TAC(WF_REL_THMS @ [sum_CASE; type_size_def "flat_v"; list_size;
                             CONJUNCT1 v_size_aux] @ size_aux_eqs "flat_v") THEN
  REWRITE_TAC[list_size_pair_size_MAP_FST_SND] THEN ARITH_TAC;;

let find_v_globals_def = sem1aux_def_wf
  `MEASURE (\x:flat_v + flat_v list.
              sum_CASE x flat_v_size (list_size flat_v_size))`
  FLATPAUX_V_TC_TAC
  `(find_v_globals (flat_Conv _ vl) = (find_v_globalsL vl):num_set) /\
   (find_v_globals (flat_Closure env _ e) =
      sptree_union (find_v_globalsL (MAP SND (flat_environment_v env)))
            (find_lookups e)) /\
   (find_v_globals (flat_Recclosure env vves _) =
      sptree_union (find_v_globalsL (MAP SND (flat_environment_v env)))
            (find_lookupsL (MAP (SND o SND) vves))) /\
   (find_v_globals (flat_Vectorv vl) = find_v_globalsL vl) /\
   (find_v_globals _ = LN) /\
   (find_v_globalsL [] = LN) /\
   (find_v_globalsL (CONS h t) = sptree_union (find_v_globals h) (find_v_globalsL t))`;;

let find_v_globals_ind = cake_ind "find_v_globals";;

let find_v_globalsL_APPEND = prove
 (`!l1 l2. find_v_globalsL (APPEND l1 l2) =
           sptree_union (find_v_globalsL l1) (find_v_globalsL l2)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; find_v_globals_def; union_LN; union_assoc]);;

let find_v_globalsL_REVERSE = prove
 (`!l. find_v_globalsL l = find_v_globalsL (REVERSE l)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REVERSE; find_v_globals_def; find_v_globalsL_APPEND;
                  union_LN] THEN
  MATCH_ACCEPT_TAC union_num_set_sym);;

let find_v_globalsL_MEM = prove
 (`!(k:A) v (vs:(A#flat_v)list).
     MEM (k,v) vs
     ==> domain (find_v_globals v) SUBSET domain (find_v_globalsL (MAP SND vs))`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; MAP; find_v_globals_def; domain_union] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[SND] THEN SET_TAC[];
    ASM SET_TAC[]]);;

let find_v_globalsL_EL = prove
 (`!n vs. n < LENGTH vs
          ==> domain (find_v_globals (EL n vs)) SUBSET
              domain (find_v_globalsL vs)`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; EL; HD; TL; find_v_globals_def; domain_union;
              SUBSET_UNION; LT_SUC; LT_0; ARITH_RULE `~(n < 0)`] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `t:flat_v list`) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* HOL4 [local] *)
let find_v_globalsL_EL_trans = prove
 (`!n vs (R:num->bool).
     n < LENGTH vs /\ domain (find_v_globalsL vs) SUBSET R
     ==> domain (find_v_globals (EL n vs)) SUBSET R`,
  MESON_TAC[find_v_globalsL_EL; SUBSET_TRANS]);;

let find_v_globals_MAP_Recclosure = prove
 (`!env (f:A->varN) funs (v:B) l.
     domain (find_v_globalsL (MAP (\x. flat_Recclosure env l (f x)) funs)) =
     (if NULL funs then {}
      else domain (find_v_globalsL (MAP SND (flat_environment_v env))) UNION
           domain (find_lookupsL (MAP (SND o SND) l)))`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; NULL; find_v_globals_def; domain_union; domain_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN SET_TAC[]);;

let find_v_globalsL_REPLICATE = prove
 (`!n v (vs:A). domain (find_v_globalsL (REPLICATE n v)) SUBSET
                domain (find_v_globals v)`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[REPLICATE; find_v_globals_def; domain_union; domain_def;
                  EMPTY_SUBSET; UNION_SUBSET; SUBSET_REFL]);;

let find_v_globalsL_LUPDATE = prove
 (`!n vs (reachable:num_set) v.
     n < LENGTH vs /\
     domain (find_v_globalsL vs) SUBSET domain reachable /\
     domain (find_v_globals v) SUBSET domain reachable
     ==> domain (find_v_globalsL (LUPDATE v n vs)) SUBSET domain reachable`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(n < 0)`] THEN INDUCT_TAC THEN
  REWRITE_TAC[LUPDATE_def; find_v_globals_def; domain_union; UNION_SUBSET;
              LT_0; LT_SUC] THEN
  ASM_MESON_TAC[]);;

let find_v_globals_v_to_list = prove
 (`!x (reachable:num_set) xs.
     domain (find_v_globals x) SUBSET domain reachable /\
     flat_v_to_list x = SOME xs
     ==> domain (find_v_globalsL xs) SUBSET domain reachable`,
  MATCH_MP_TAC flat_v_to_list_ind THEN
  RW[flat_v_to_list_def; find_v_globals_def; domain_union; union_LN] THEN
  FS[case_eq "option"] THEN RVEQ_TAC THEN
  FS[find_v_globals_def; domain_union; UNION_SUBSET] THEN ASM_MESON_TAC[]);;

let find_v_globals_list_to_v = prove
 (`!xs (reachable:num_set) x.
     domain (find_v_globalsL xs) SUBSET domain reachable /\
     flat_list_to_v xs = x
     ==> domain (find_v_globals x) SUBSET domain reachable`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[flat_list_to_v_def; find_v_globals_def; domain_union;
              union_LN; UNION_SUBSET] THEN
  ASM_MESON_TAC[]);;

let find_refs_globals_def = sem1aux_def
  `(find_refs_globals (CONS (Refv a) t) =
      sptree_union (find_v_globals a) (find_refs_globals t)) /\
   (find_refs_globals (CONS (Varray l) t) =
      sptree_union (find_v_globalsL l) (find_refs_globals t)) /\
   (find_refs_globals (CONS (Thunk _ a) t) =
      sptree_union (find_v_globals a) (find_refs_globals t)) /\
   (find_refs_globals (CONS _ t) = find_refs_globals t) /\
   (find_refs_globals ([]:(flat_v store_v) list) = LN)`;;

let find_refs_globals_ind = cake_ind "find_refs_globals";;

let find_refs_globals_MEM = prove
 (`!refs (reachable:num_set) (R:num->bool).
     domain (find_refs_globals refs) SUBSET R
     ==> (!a. MEM (Refv a) refs ==> domain (find_v_globals a) SUBSET R) /\
         (!vs. MEM (Varray vs) refs ==> domain (find_v_globalsL vs) SUBSET R) /\
         (!m a. MEM (Thunk m a) refs ==> domain (find_v_globals a) SUBSET R)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN REPEAT GEN_TAC THEN
  CASES_ON `h:flat_v store_v` THEN
  REWRITE_TAC[find_refs_globals_def; domain_union; UNION_SUBSET] THEN
  SIMP[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`reachable:num_set`; `R:num->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let find_refs_globals_EL = prove
 (`!n refs (R:num->bool).
     n < LENGTH refs /\ domain (find_refs_globals refs) SUBSET R
     ==> (!a. EL n refs = Refv a ==> domain (find_v_globals a) SUBSET R) /\
         (!vs. EL n refs = Varray vs ==> domain (find_v_globalsL vs) SUBSET R) /\
         (!m a. EL n refs = Thunk m a ==> domain (find_v_globals a) SUBSET R)`,
  MESON_TAC[MEM_EL; find_refs_globals_MEM]);;

let find_refs_globals_LUPDATE = prove
 (`!(reachable:num_set) refs n.
     n < LENGTH refs /\ domain (find_refs_globals refs) SUBSET domain reachable
     ==> (!a. domain (find_v_globals a) SUBSET domain reachable
              ==> domain (find_refs_globals (LUPDATE (Refv a) n refs))
                  SUBSET domain reachable) /\
         (!vs. domain (find_v_globalsL vs) SUBSET domain reachable
               ==> domain (find_refs_globals (LUPDATE (Varray vs) n refs))
                   SUBSET domain reachable) /\
         (!ws. domain (find_refs_globals (LUPDATE (W8array ws) n refs))
               SUBSET domain reachable) /\
         (!m a. domain (find_v_globals a) SUBSET domain reachable
                ==> domain (find_refs_globals (LUPDATE (Thunk m a) n refs))
                    SUBSET domain reachable)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(n < 0)`] THEN INDUCT_TAC THEN
  REWRITE_TAC[LUPDATE_def; LT_0; LT_SUC] THEN
  CASES_ON `h:flat_v store_v` THEN
  REWRITE_TAC[find_refs_globals_def; domain_union; UNION_SUBSET] THEN
  ASM_MESON_TAC[]);;

let find_refs_globals_APPEND = prove
 (`!refs new. find_refs_globals (APPEND refs new) =
              sptree_union (find_refs_globals refs) (find_refs_globals new)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; find_refs_globals_def; union_LN] THEN
  GEN_TAC THEN CASES_ON `h:flat_v store_v` THEN
  ASM_REWRITE_TAC[find_refs_globals_def; union_assoc]);;

let find_env_globals_def = cake_def
  `find_env_globals (env:(flat_v)flat_environment) =
     find_v_globalsL (MAP SND (flat_environment_v env))`;;

let find_result_globals_def = sem1aux_def
  `(find_result_globals (SOME (Rraise v)) = find_v_globals v) /\
   (find_result_globals (_:((flat_v)error_result)option) = LN)`;;

(* HOL4's induction theorem of the non-recursive definition (a case split) *)

let find_result_globals_ind = prove
 (`!P. (!v. P (SOME (Rraise v))) /\ P NONE /\ (!v3. P (SOME (Rabort v3)))
       ==> !v:((flat_v)error_result)option. P v`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[FORALL_OPTION_THM] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:(flat_v)error_result` THEN
  STRUCT_CASES_TAC(ISPEC `e:(flat_v)error_result` (cases "error_result")) THEN
  ASM_REWRITE_TAC[]);;

(* the variable of the Rval clause is es (one quotation, one type per name) *)

let find_sem_prim_res_globals_def = cake_def
  `(find_sem_prim_res_globals (Rerr e:(flat_v list,flat_v)result) =
      find_result_globals (SOME e)) /\
   (find_sem_prim_res_globals (Rval es) = find_v_globalsL es)`;;

(* HOL4's termination proof: measure v_size, with the size of the          *)
(* environment as that of its bindings; the calls under EX get the context *)
(* MEM y l                                                                   *)

let FLATPAUX_V_MEM_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  REWRITE_TAC(WF_REL_THMS @ [type_size_def "flat_v"; CONJUNCT1 v_size_aux] @
              size_aux_eqs "flat_v") THEN
  REWRITE_TAC[list_size_pair_size_MAP_FST_SND] THEN
  MEM_SIZE_TAC THEN ASM_ARITH_TAC;;

let v_has_Eval_def1 = sem1aux_def_wf
  `MEASURE flat_v_size`
  FLATPAUX_V_MEM_TC_TAC
  `(v_has_Eval (flat_Closure env _ e) <=>
      has_Eval e \/ EX v_has_Eval (MAP SND (flat_environment_v env))) /\
   (v_has_Eval (flat_Conv _ vl) <=> EX v_has_Eval vl) /\
   (v_has_Eval (flat_Recclosure env nm_es _) <=>
      EX v_has_Eval (MAP SND (flat_environment_v env)) \/
      EX has_Eval (MAP (SND o SND) nm_es)) /\
   (v_has_Eval (flat_Vectorv vl) <=> EX v_has_Eval vl) /\
   (v_has_Eval _ <=> F)`;;

let v_has_Eval_def1_ind = cake_ind "v_has_Eval";;

let v_has_Eval_def = CONV_RULE (DEPTH_CONV ETA_CONV) v_has_Eval_def1;;

(* s_g = state globals, t_g = removed state globals *)

let globals_rel_def = cake_def
  `globals_rel (reachable:num_set) (s_g:(flat_v option) list)
               (t_g:(flat_v option) list) <=>
     LENGTH s_g = LENGTH t_g /\
     (!n. n IN domain reachable /\ n < LENGTH t_g ==> EL n s_g = EL n t_g) /\
     (!n x. n < LENGTH t_g /\ EL n t_g = SOME x ==> EL n s_g = SOME x) /\
     (!n. n < LENGTH t_g /\ EL n s_g = NONE ==> EL n t_g = NONE) /\
     (!n x. n IN domain reachable /\ n < LENGTH t_g /\ EL n t_g = SOME x
            ==> ~v_has_Eval x /\ domain (find_v_globals x) SUBSET domain reachable)`;;

let globals_rel_trans = prove
 (`!reachable s1 s2 s3.
     globals_rel reachable s1 s2 /\ globals_rel reachable s2 s3
     ==> globals_rel reachable s1 s3`,
  REWRITE_TAC[globals_rel_def] THEN MESON_TAC[]);;

let decs_closed_def = cake_def
  `decs_closed (reachable:num_set) decs <=>
     !r t. analyse_code decs = (r,t)
           ==> domain r SUBSET domain reachable /\
               (!n m. n IN domain reachable /\ is_reachable t n m
                      ==> m IN domain reachable)`;;

let decs_closed_reduce = prove
 (`!reachable e t. decs_closed reachable (CONS e t) ==> decs_closed reachable t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[decs_closed_def; analyse_code_def] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`r:num_set`; `t0:(num_set)spt`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?r1 t1. analyse_exp e = (r1:num_set,t1:(num_set)spt)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`sptree_union r1 r:num_set`;
                                `num_set_tree_union t1 t0`]) THEN
  ASM_REWRITE_TAC[code_analysis_union_def; domain_union; UNION_SUBSET] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[num_set_tree_union_sym] THEN
  MATCH_MP_TAC is_reachable_num_set_tree_union THEN ASM_REWRITE_TAC[]);;

let decs_closed_reduce_HD = prove
 (`!reachable e t. decs_closed reachable (CONS e t) ==> decs_closed reachable [e]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[decs_closed_def; analyse_code_def] THEN
  SUBGOAL_THEN `?r1 t1. analyse_exp e = (r1:num_set,t1:(num_set)spt)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `?r2 t2. analyse_code t = (r2:num_set,t2:(num_set)spt)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[code_analysis_union_def; PAIR_EQ] THEN
  ONCE_REWRITE_TAC[num_set_tree_union_sym] THEN
  REWRITE_TAC[num_set_tree_union_def; union_LN] THEN
  DISCH_THEN(MP_TAC o SPECL [`sptree_union r1 r2:num_set`;
                             `num_set_tree_union t2 t1`]) THEN
  REWRITE_TAC[domain_union; UNION_SUBSET] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[num_set_tree_union_sym] THEN
  MATCH_MP_TAC is_reachable_num_set_tree_union THEN ASM_REWRITE_TAC[]);;

(* s = state, t = removed state *)

let flat_state_rel_def = cake_def
  `flat_state_rel (reachable:num_set) (s:(C,FFI)flat_state)
                  (t:(C,FFI)flat_state) <=>
     flat_state_clock s = flat_state_clock t /\
     flat_state_refs s = flat_state_refs t /\
     flat_state_ffi s = flat_state_ffi t /\
     globals_rel reachable (flat_state_globals s) (flat_state_globals t) /\
     domain (find_refs_globals (flat_state_refs s)) SUBSET domain reachable /\
     ALL (ALL ((~) o v_has_Eval) o flat_store_v_vs) (flat_state_refs s)`;;

let flat_state_rel_trans = prove
 (`!reachable (s1:(C,FFI)flat_state) s2 s3.
     flat_state_rel reachable s1 s2 /\ flat_state_rel reachable s2 s3
     ==> flat_state_rel reachable s1 s3`,
  REWRITE_TAC[flat_state_rel_def] THEN MESON_TAC[globals_rel_trans]);;

(* FLATLANG LEMMAS *)

(* a local helper: the values of a looked-up store entry *)

let FLATPAUX_store_lookup_globals = prove
 (`!n refs (R:num->bool).
     domain (find_refs_globals refs) SUBSET R
     ==> (!a. store_lookup n refs = SOME (Refv a)
              ==> domain (find_v_globals a) SUBSET R) /\
         (!vs. store_lookup n refs = SOME (Varray vs)
               ==> domain (find_v_globalsL vs) SUBSET R) /\
         (!m a. store_lookup n refs = SOME (Thunk m a)
                ==> domain (find_v_globals a) SUBSET R)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[store_lookup_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  ASM_MESON_TAC[find_refs_globals_EL]);;

let pmatch_Match_reachable = prove
 (`(!(s:(C,FFI)flat_state) p v l a (reachable:num_set).
      flat_pmatch s p v l = Match a /\
      domain (find_v_globals v) SUBSET domain reachable /\
      domain (find_v_globalsL (MAP SND l)) SUBSET domain reachable /\
      domain (find_refs_globals (flat_state_refs s)) SUBSET domain reachable
      ==> domain (find_v_globalsL (MAP SND a)) SUBSET domain reachable) /\
   (!(s:(C,FFI)flat_state) p vs l a (reachable:num_set).
      flat_pmatch_list s p vs l = Match a /\
      domain (find_v_globalsL vs) SUBSET domain reachable /\
      domain (find_v_globalsL (MAP SND l)) SUBSET domain reachable /\
      domain (find_refs_globals (flat_state_refs s)) SUBSET domain reachable
      ==> domain (find_v_globalsL (MAP SND a)) SUBSET domain reachable)`,
  MATCH_MP_TAC flat_pmatch_ind THEN REPEAT CONJ_TAC THEN
  RW[flat_pmatch_def; find_v_globals_def; domain_union; MAP; UNION_SUBSET] THEN
  GVS[case_eq "option"; case_eq "store_v"; case_eq "match_result"] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[FLATPAUX_store_lookup_globals]);;

let find_v_globals_list_to_v_APPEND = prove
 (`!xs (reachable:num_set) ys.
     domain (find_v_globalsL xs) SUBSET domain reachable /\
     domain (find_v_globalsL ys) SUBSET domain reachable
     ==> domain (find_v_globals (flat_list_to_v (APPEND xs ys))) SUBSET
         domain reachable`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC find_v_globals_list_to_v THEN
  EXISTS_TAC `APPEND xs ys:flat_v list` THEN
  ASM_REWRITE_TAC[find_v_globalsL_APPEND; domain_union; UNION_SUBSET]);;

let find_v_globals_Unitv = prove
 (`find_v_globals Unitv = LN`,
  REWRITE_TAC[flat_Unitv_def; find_v_globals_def]);;
let _ = cake_add_simps [find_v_globals_Unitv];;

let EVERY_EL_IMP = prove
 (`!(P:A->bool) xs n. ALL P xs /\ n < LENGTH xs ==> P (EL n xs)`,
  REWRITE_TAC[GSYM ALL_EL] THEN MESON_TAC[]);;

(* HOL4 [local] *)
let not_v_has_Eval_EVERY_EL = prove
 (`!xs i. ALL ((~) o v_has_Eval) xs /\ i < LENGTH xs ==> ~v_has_Eval (EL i xs)`,
  REWRITE_TAC[GSYM ALL_EL; o_THM] THEN MESON_TAC[]);;

(* HOL4: v_has_Eval_Unitv is an EVAL of v_has_Eval Unitv *)
let v_has_Eval_Unitv = prove
 (`v_has_Eval Unitv <=> F`,
  REWRITE_TAC[flat_Unitv_def; v_has_Eval_def; EX]);;

let v_has_Eval_list_to_v = prove
 (`!xs. v_has_Eval (flat_list_to_v xs) <=> EX v_has_Eval xs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[flat_list_to_v_def; v_has_Eval_def; EX]);;

let v_has_Eval_v_to_list = prove
 (`!v xs. flat_v_to_list v = SOME xs ==> (v_has_Eval v <=> EX v_has_Eval xs)`,
  MATCH_MP_TAC flat_v_to_list_ind THEN
  RW[flat_v_to_list_def; v_has_Eval_def; EX] THEN
  FS[case_eq "option"] THEN RVEQ_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[EX]);;

(* HOL4 [local] *)
let fvg_map_char_empty = prove
 (`!ss. find_v_globals (flat_list_to_v (MAP (\c. flat_Litv (Char c)) ss)) = LN`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; flat_list_to_v_def; find_v_globals_def; union_LN]);;

(* HOL4 [local] *)
let not_LE_LESS_IMP = prove
 (`!x y. ~(x >= y) ==> (x:num) < y`,
  ARITH_TAC);;

(* HOL4 [local] *)
let EL_REP_NONE_SOME_trivia = prove
 (`!n (xs:(A option) list) i y.
     n < LENGTH xs + i
     ==> (EL n (APPEND xs (REPLICATE i NONE)) = SOME y <=>
          n < LENGTH xs /\ EL n xs = SOME y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EL_APPEND] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n - LENGTH (xs:(A option) list) < i` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[EL_REPLICATE; option_DISTINCT]]);;

(* HOL4 [local] *)
let flat_elimProof_pair_case_eq = prove
 (`!(x:A#B) (f:A->B->C) v.
     pair_CASE x f = v <=> ?x1 x2. x = (x1,x2) /\ f x1 x2 = v`,
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 [local]; the paired let is pair_CASE (kit) *)
let flat_elimProof_pair_lam_lem = prove
 (CASE_TERM
  `!(f:A->B->C) v z.
     (let (x,y) = z in f x y) = v <=> ?x1 x2. z = (x1,x2) /\ f x1 x2 = v`,
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4's do_app_cases (an SIMP_CONV expansion of do_app, unused) is not  *)
(* ported                                                                    *)

(* HOL4 [local,simp] *)
let fvg_v_to_flat = prove
 (`!v (reachable:num_set).
     domain (find_v_globals (v_to_flat v)) SUBSET domain reachable /\
     ~v_has_Eval (v_to_flat v)`,
  GEN_TAC THEN CASES_ON `v:v` THEN REWRITE_TAC[v_to_flat_def] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[flat_Boolv_def; find_v_globals_def; v_has_Eval_def; domain_def;
              EMPTY_SUBSET; EX]);;
let _ = cake_add_simps [fvg_v_to_flat];;

(* local helpers of do_app_SOME_flat_state_rel: the store and the values *)

let FLATPAUX_refs_rel = prove
 (`!reachable (s:(C,FFI)flat_state) t refs.
     flat_state_rel reachable s t /\
     domain (find_refs_globals refs) SUBSET domain reachable /\
     ALL (ALL ((~) o v_has_Eval) o flat_store_v_vs) refs
     ==> flat_state_rel reachable (flat_state_refs_fupd (combin_K refs) s)
                                  (flat_state_refs_fupd (combin_K refs) t)`,
  SIMP[flat_state_rel_def]);;

let FLATPAUX_refs_ffi_rel = prove
 (`!reachable (s:(C,FFI)flat_state) t refs ffi.
     flat_state_rel reachable s t /\
     domain (find_refs_globals refs) SUBSET domain reachable /\
     ALL (ALL ((~) o v_has_Eval) o flat_store_v_vs) refs
     ==> flat_state_rel reachable
           (flat_state_refs_fupd (combin_K refs) (flat_state_ffi_fupd (combin_K ffi) s))
           (flat_state_refs_fupd (combin_K refs) (flat_state_ffi_fupd (combin_K ffi) t))`,
  SIMP[flat_state_rel_def]);;

let FLATPAUX_find_refs_globals_LUPDATE = prove
 (`!refs n (v:flat_v store_v).
     domain (find_refs_globals (LUPDATE v n refs)) SUBSET
     domain (find_refs_globals refs) UNION domain (find_refs_globals [v])`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LUPDATE_def; find_refs_globals_def; domain_def; EMPTY_SUBSET] THEN
  INDUCT_TAC THEN GEN_TAC THEN REWRITE_TAC[LUPDATE_def] THENL
   [ALL_TAC; FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:flat_v store_v`])] THEN
  CASES_ON `h:flat_v store_v` THEN CASES_ON `v:flat_v store_v` THEN
  REWRITE_TAC[find_refs_globals_def; domain_union; union_LN] THEN SET_TAC[]);;

let FLATPAUX_find_refs_globals_MEM = prove
 (`!refs (x:flat_v store_v).
     MEM x refs
     ==> domain (find_refs_globals [x]) SUBSET domain (find_refs_globals refs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN GEN_TAC THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL
   [ALL_TAC; FIRST_X_ASSUM(MP_TAC o SPEC `x:flat_v store_v`) THEN
    ASM_REWRITE_TAC[]] THEN
  CASES_ON `h:flat_v store_v` THEN TRY(CASES_ON `x:flat_v store_v`) THEN
  REWRITE_TAC[find_refs_globals_def; domain_union; union_LN; domain_def;
              EMPTY_SUBSET] THEN SET_TAC[]);;

let FLATPAUX_store_assign_facts = prove
 (`!n (v:flat_v store_v) refs refs' (R:num->bool).
     store_assign n v refs = SOME refs' /\
     domain (find_refs_globals refs) SUBSET R /\
     ALL (ALL ((~) o v_has_Eval) o flat_store_v_vs) refs /\
     domain (find_refs_globals [v]) SUBSET R /\
     ALL ((~) o v_has_Eval) (flat_store_v_vs v)
     ==> domain (find_refs_globals refs') SUBSET R /\
         ALL (ALL ((~) o v_has_Eval) o flat_store_v_vs) refs'`,
  REWRITE_TAC[store_assign_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`refs:(flat_v store_v)list`; `n:num`; `v:flat_v store_v`]
             FLATPAUX_find_refs_globals_LUPDATE) THEN ASM SET_TAC[];
    MATCH_MP_TAC IMP_EVERY_LUPDATE THEN ASM_REWRITE_TAC[o_THM]]);;

let FLATPAUX_store_alloc_facts = prove
 (`!(v:flat_v store_v) refs refs' n (R:num->bool).
     store_alloc v refs = (refs',n) /\
     domain (find_refs_globals refs) SUBSET R /\
     ALL (ALL ((~) o v_has_Eval) o flat_store_v_vs) refs /\
     domain (find_refs_globals [v]) SUBSET R /\
     ALL ((~) o v_has_Eval) (flat_store_v_vs v)
     ==> domain (find_refs_globals refs') SUBSET R /\
         ALL (ALL ((~) o v_has_Eval) o flat_store_v_vs) refs'`,
  REWRITE_TAC[store_alloc_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM o CONJUNCT1) STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[find_refs_globals_APPEND; domain_union; UNION_SUBSET;
                  ALL_APPEND; ALL; o_THM]);;

let FLATPAUX_store_lookup_facts = prove
 (`!n refs (sv:flat_v store_v) (R:num->bool).
     store_lookup n refs = SOME sv /\
     domain (find_refs_globals refs) SUBSET R /\
     ALL (ALL ((~) o v_has_Eval) o flat_store_v_vs) refs
     ==> domain (find_refs_globals [sv]) SUBSET R /\
         ALL ((~) o v_has_Eval) (flat_store_v_vs sv)`,
  REWRITE_TAC[store_lookup_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `MEM (EL n refs:flat_v store_v) refs` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM_EL]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[FLATPAUX_find_refs_globals_MEM; SUBSET_TRANS];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM ALL_MEM]) THEN
    DISCH_THEN(MP_TAC o SPEC `EL n refs:flat_v store_v`) THEN
    ASM_REWRITE_TAC[o_THM]]);;

let FLATPAUX_EL_noEval = prove
 (`!n vs. n < LENGTH vs /\ ALL (\x. ~v_has_Eval x) vs ==> ~v_has_Eval (EL n vs)`,
  REWRITE_TAC[GSYM ALL_EL] THEN MESON_TAC[]);;

let FLATPAUX_store_assign_facts' = prove
 (`!n (v:flat_v store_v) refs refs'.
     store_assign n v refs = SOME refs'
     ==> !R. domain (find_refs_globals refs) SUBSET R /\
             ALL (ALL ((~) o v_has_Eval) o flat_store_v_vs) refs /\
             domain (find_refs_globals [v]) SUBSET R /\
             ALL ((~) o v_has_Eval) (flat_store_v_vs v)
             ==> domain (find_refs_globals refs') SUBSET R /\
                 ALL (ALL ((~) o v_has_Eval) o flat_store_v_vs) refs'`,
  MESON_TAC[FLATPAUX_store_assign_facts]);;

let FLATPAUX_store_alloc_facts' = prove
 (`!(v:flat_v store_v) refs refs' n.
     store_alloc v refs = (refs',n)
     ==> !R. domain (find_refs_globals refs) SUBSET R /\
             ALL (ALL ((~) o v_has_Eval) o flat_store_v_vs) refs /\
             domain (find_refs_globals [v]) SUBSET R /\
             ALL ((~) o v_has_Eval) (flat_store_v_vs v)
             ==> domain (find_refs_globals refs') SUBSET R /\
                 ALL (ALL ((~) o v_has_Eval) o flat_store_v_vs) refs'`,
  MESON_TAC[FLATPAUX_store_alloc_facts]);;

let FLATPAUX_v_to_list_noEval = prove
 (`!v xs. flat_v_to_list v = SOME xs /\ ~v_has_Eval v
          ==> ALL (\x. ~v_has_Eval x) xs`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP v_has_Eval_v_to_list) THEN
  REWRITE_TAC[NOT_EX]);;

let FLATPAUX_REPLICATE_globals = prove
 (`!n v (R:num->bool).
     domain (find_v_globals v) SUBSET R
     ==> domain (find_v_globalsL (REPLICATE n v)) SUBSET R`,
  MESON_TAC[find_v_globalsL_REPLICATE; SUBSET_TRANS]);;

let FLATPAUX_globals_state_rel = prove
 (`!reachable (s:(C,FFI)flat_state) t g1 g2.
     flat_state_rel reachable s t /\ globals_rel reachable g1 g2
     ==> flat_state_rel reachable (flat_state_globals_fupd (combin_K g1) s)
                                  (flat_state_globals_fupd (combin_K g2) t)`,
  REWRITE_TAC[flat_state_rel_def; flat_state_INFO.ri_accfupds; K_THM] THEN
  MESON_TAC[]);;

let FLATPAUX_EL_APPEND_REPLICATE_NONE = prove
 (`!(l:(A option)list) k n.
     n < LENGTH l + k
     ==> EL n (APPEND l (REPLICATE k NONE)) = if n < LENGTH l then EL n l else NONE`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EL_APPEND] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EL_REPLICATE THEN ASM_ARITH_TAC);;

let FLATPAUX_globals_rel_alloc = prove
 (`!reachable s_g t_g k.
     globals_rel reachable s_g t_g
     ==> globals_rel reachable (APPEND s_g (REPLICATE k NONE))
                               (APPEND t_g (REPLICATE k NONE))`,
  REWRITE_TAC[globals_rel_def; LENGTH_APPEND; LENGTH_REPLICATE] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!n. n < LENGTH (t_g:(flat_v option)list) + k
        ==> EL n (APPEND (s_g:(flat_v option)list) (REPLICATE k NONE)) =
              (if n < LENGTH t_g then EL n s_g else NONE) /\
            EL n (APPEND t_g (REPLICATE k NONE)) =
              (if n < LENGTH t_g then EL n t_g else NONE)`
   (LABEL_TAC "elq") THENL
   [GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `LENGTH (s_g:(flat_v option)list) = LENGTH (t_g:(flat_v option)list)` THEN
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[SYM th]) THEN
                           REWRITE_TAC[SYM th]) THEN
      MATCH_MP_TAC FLATPAUX_EL_APPEND_REPLICATE_NONE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FLATPAUX_EL_APPEND_REPLICATE_NONE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "elq" (MP_TAC o C MP (ASSUME `n < LENGTH (t_g:(flat_v option)list) + k`) o
                  SPEC `n:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  ASM_CASES_TAC `n < LENGTH (t_g:(flat_v option)list)` THEN
  FS[option_DISTINCT] THEN ASM_MESON_TAC[]);;

let FLATPAUX_globals_rel_init = prove
 (`!reachable s_g t_g n v.
     globals_rel reachable s_g t_g /\ n < LENGTH s_g /\ EL n s_g = NONE /\
     ~v_has_Eval v /\ domain (find_v_globals v) SUBSET domain reachable
     ==> globals_rel reachable (LUPDATE (SOME v) n s_g) (LUPDATE (SOME v) n t_g) /\
         n < LENGTH t_g /\ EL n t_g = NONE`,
  REWRITE_TAC[globals_rel_def; LENGTH_LUPDATE] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN ASM_SIMP_TAC[EL_LUPDATE] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_INJ; option_DISTINCT] THEN ASM_MESON_TAC[]);;

let FLATPAUX_globals_rel_lookup = prove
 (`!reachable s_g t_g n.
     globals_rel reachable s_g t_g /\ n IN domain reachable /\
     n < LENGTH s_g /\ IS_SOME (EL n s_g)
     ==> n < LENGTH t_g /\ EL n t_g = EL n s_g /\
         ~v_has_Eval (THE (EL n s_g)) /\
         domain (find_v_globals (THE (EL n s_g))) SUBSET domain reachable`,
  REWRITE_TAC[globals_rel_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n < LENGTH (t_g:(flat_v option)list) /\
                EL n t_g = EL n (s_g:(flat_v option)list)` STRIP_ASSUME_TAC
  THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[IS_SOME_EXISTS; THE_DEF]);;

(* the equations of do_app at each operator (HOL4 proves the theorem by    *)
(* Cases_on op and gvs [do_app_def, AllCaseEqs()])                          *)

let FLATPAUX_case_pats ty =
  let th = cases ty in
  let _,body = dest_forall (concl th) in
  map (fun d -> rhs (snd (strip_exists d))) (disjuncts body);;

let FLATPAUX_do_app_eqs = ref ([]:thm list);;

FLATPAUX_do_app_eqs :=
  let th0 = SPEC_ALL flat_do_app_def and opv = `op:flat_op` in
  let srcs = map (fun p -> mk_comb(`Src`,p)) (FLATPAUX_case_pats "op") in
  let others = filter (fun p -> try fst(dest_const(fst(strip_comb p))) <> "Src"
                                with Failure _ -> true)
                      (FLATPAUX_case_pats "flat_op") in
  map (fun c -> CONV_RULE (RAND_CONV (CAKE_REWRITE_CONV [])) (INST [c,opv] th0))
      (srcs @ others);;

let FLATPAUX_is_do_app_eq th =
  let c = concl th in
  is_eq c && (try fst(dest_const(fst(strip_comb(lhs c)))) = "flat_do_app"
              with Failure _ -> false);;

(* the hypotheses, the parts of flat_state_rel, and the case split of the  *)
(* do_app equation (flatSem's FLATSEMAUX_SPLIT_TAC)                         *)

let FLATPAUX_INTRO_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
                       STRIP_ASSUME_TAC(REWRITE_RULE[flat_state_rel_def] th)) THEN
  REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check FLATPAUX_is_do_app_eq) THEN
  REWRITE_TAC (!FLATPAUX_do_app_eqs) THEN DISCH_TAC THEN
  FLATSEMAUX_SPLIT_TAC;;

let FLATPAUX_val_simps =
  [find_sem_prim_res_globals_def; find_result_globals_def; find_v_globals_def;
   v_has_Eval_def; flat_div_exn_v_def; flat_chr_exn_v_def; subscript_exn_v_def;
   flat_bind_exn_v_def; flat_Boolv_def; flat_Unitv_def; domain_def; domain_union;
   union_LN; EMPTY_SUBSET; UNION_SUBSET; EX; ALL; list_result_def; result_vs_def;
   o_THM];;

let FLATPAUX_norm =
  FLATPAUX_val_simps @
  [o_DEF; NOT_EX; EVERY_MAP; EXISTS_MAP; EXISTS_APPEND; ALL_APPEND; fvg_v_to_flat;
   find_refs_globals_def; flat_store_v_vs_def; fvg_map_char_empty;
   v_has_Eval_list_to_v; ALL_T; DE_MORGAN_THM; EVERY_REPLICATE; find_lookups_def;
   dest_GlobalVarLookup_def; domain_insert; INSERT_SUBSET; IS_NONE_DEF;
   option_CASE];;

let FLATPAUX_match_asm pat (asl:(string*thm) list) =
  map snd (filter (fun (_,th) -> can (term_match [] pat) (concl th)) asl);;

(* the values of the store entries that do_app looked up *)

let FLATPAUX_LOOKUP_FACTS_TAC : tactic = fun (asl,w as g) ->
  let rg = FLATPAUX_match_asm
    `domain (find_refs_globals (refs:(flat_v store_v)list)) SUBSET (R:num->bool)` asl
  and re = FLATPAUX_match_asm
    `ALL (ALL ((~) o v_has_Eval) o flat_store_v_vs) (refs:(flat_v store_v)list)` asl
  and lk = FLATPAUX_match_asm
    `store_lookup (n:num) (refs:(flat_v store_v)list) = SOME sv` asl in
  let facts = flat (map (fun th -> mapfilter (fun (a,b) ->
      MATCH_MP FLATPAUX_store_lookup_facts (CONJ th (CONJ a b)))
      (allpairs (fun a b -> (a,b)) rg re)) lk) in
  MAP_EVERY ASSUME_TAC facts g;;

(* a new store: the stored value must satisfy the invariants *)

let FLATPAUX_REFS_TAC : tactic = fun (asl,w as g) ->
  let sa = FLATPAUX_match_asm
     `store_assign (n:num) (v:flat_v store_v) refs = SOME refs'` asl
  and sl = FLATPAUX_match_asm
     `store_alloc (v:flat_v store_v) refs = (refs',n:num)` asl in
  let rules = map (MATCH_MP FLATPAUX_store_assign_facts') sa @
              map (MATCH_MP FLATPAUX_store_alloc_facts') sl in
  ((MATCH_MP_TAC FLATPAUX_refs_ffi_rel ORELSE MATCH_MP_TAC FLATPAUX_refs_rel) THEN
   CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; FIRST(map MATCH_MP_TAC rules)] THEN
   ASM_REWRITE_TAC[]) g;;

(* the elements of a list value *)

let FLATPAUX_V_TO_LIST_FACTS_TAC : tactic = fun (asl,w as g) ->
  let vl = FLATPAUX_match_asm `flat_v_to_list v = SOME xs` asl
  and gs = FLATPAUX_match_asm `domain (find_v_globals v) SUBSET domain (r:num_set)` asl
  and ne = FLATPAUX_match_asm `~v_has_Eval v` asl in
  let f1 = flat (map (fun th -> mapfilter (fun n ->
             MATCH_MP FLATPAUX_v_to_list_noEval (CONJ th n)) ne) vl)
  and f2 = flat (map (fun th -> mapfilter (fun g ->
             MATCH_MP find_v_globals_v_to_list (CONJ g th)) gs) vl) in
  MAP_EVERY ASSUME_TAC (f1 @ f2) g;;

let FLATPAUX_DO_APP_FINISH_TAC : tactic =
  REPEAT CONJ_TAC THEN
  FLATPAUX_LOOKUP_FACTS_TAC THEN TRY FLATPAUX_REFS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE FLATPAUX_norm) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY ASSUME_TAC
                          (mapfilter (MATCH_MP not_LE_LESS_IMP) ths)) THEN
  FLATPAUX_V_TO_LIST_FACTS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE FLATPAUX_norm) THEN
  REWRITE_TAC FLATPAUX_norm THEN
  ASM_SIMP_TAC[find_v_globalsL_EL_trans; FLATPAUX_EL_noEval;
               find_v_globals_list_to_v_APPEND; FLATPAUX_REPLICATE_globals;
               find_v_globalsL_LUPDATE; IMP_EVERY_LUPDATE] THEN
  TRY(MATCH_MP_TAC FLATPAUX_globals_state_rel THEN
      ASM_SIMP_TAC[FLATPAUX_globals_rel_alloc]) THEN
  TRY(ASM_MESON_TAC[FLATPAUX_globals_rel_init; FLATPAUX_globals_rel_lookup]);;

let do_app_SOME_flat_state_rel = prove
 (`!reachable (state:(C,FFI)flat_state) removed_state op l new_state result
    (new_removed_state:(C,FFI)flat_state).
     flat_state_rel reachable state removed_state /\ ~(op = Src Opapp) /\
     domain (find_v_globalsL l) SUBSET domain reachable /\
     domain (find_lookups (flat_App tra op [])) SUBSET domain reachable /\
     ALL ((~) o v_has_Eval) l
     ==> flat_do_app state op l = SOME (new_state,result) /\
         ~(result = Rerr (Rabort Rtype_error))
         ==> ?new_removed_state.
               flat_state_rel reachable new_state new_removed_state /\
               flat_do_app removed_state op l = SOME (new_removed_state,result) /\
               domain (find_sem_prim_res_globals (list_result result)) SUBSET
               domain reachable /\
               ALL ((~) o v_has_Eval) (result_vs (list_result result))`,
  REPEAT GEN_TAC THEN CASES_ON `op:flat_op` THENL
   [CASES_ON `a:op`; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;
    ALL_TAC] THEN
  FLATPAUX_INTRO_TAC THEN GVS[] THEN FLATPAUX_DO_APP_FINISH_TAC);;

(* MAIN LEMMAS *)

(* pmatch only reads the refs of the state (flatProps pmatch_state) *)

let flat_state_rel_pmatch = prove
 (`(!(new_state:(C,FFI)flat_state) p a env.
      flat_state_rel reachable new_state new_removed_state
      ==> flat_pmatch new_removed_state p a env = flat_pmatch new_state p a env) /\
   (!(new_state:(C,FFI)flat_state) p a env.
      flat_state_rel reachable new_state new_removed_state
      ==> flat_pmatch_list new_removed_state p a env =
          flat_pmatch_list new_state p a env)`,
  REWRITE_TAC[flat_state_rel_def] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 pmatch_state); MATCH_MP_TAC(CONJUNCT2 pmatch_state)] THEN
  EXISTS_TAC `new_state:(C,FFI)flat_state` THEN ASM_REWRITE_TAC[]);;

let flat_state_rel_pmatch_rows = prove
 (`!reachable (new_state:(C,FFI)flat_state) new_removed_state
    (pes:(flat_pat#flat_exp)list) a.
     flat_state_rel reachable new_state new_removed_state
     ==> pmatch_rows pes new_removed_state a = pmatch_rows pes new_state a`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`pes:(flat_pat#flat_exp)list`,
                                              `pes:(flat_pat#flat_exp)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[pmatch_rows_def] THEN
  SPEC_TAC(`h:flat_pat#flat_exp`,`h:flat_pat#flat_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pmatch_rows_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (CONJUNCT1 flat_state_rel_pmatch) th]) THEN
  ASM_REWRITE_TAC[]);;

let pmatch_rows_find_lookups = prove
 (`!pes (q:(C,FFI)flat_state) a env' p' e' (reachable:num_set).
     pmatch_rows pes q a = Match (env',p',e') /\
     domain (find_lookupsL (MAP SND pes)) SUBSET domain reachable
     ==> domain (find_lookups e') SUBSET domain reachable`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP pmatch_rows_IMP_pmatch) THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `domain (find_lookupsL (MAP SND (pes:(flat_pat#flat_exp)list)))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC find_lookupsL_MEM THEN
  REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `(p',e'):flat_pat#flat_exp` THEN
  ASM_REWRITE_TAC[]);;

let FLATPAUX_store_lookup_Refv_noEval = prove
 (`!n refs (a:flat_v).
     store_lookup n refs = SOME (Refv a) /\
     ALL (ALL ((~) o v_has_Eval) o flat_store_v_vs) refs
     ==> ~v_has_Eval a`,
  REWRITE_TAC[store_lookup_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[GSYM ALL_EL] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[o_THM; flat_store_v_vs_def; ALL]);;

let pmatch_not_has_Eval = prove
 (`(!(s:(C,FFI)flat_state) p v bindings env.
      flat_pmatch s p v bindings = Match env /\ ~v_has_Eval v /\
      ALL (ALL ((~) o v_has_Eval) o flat_store_v_vs) (flat_state_refs s) /\
      ALL ((~) o v_has_Eval o SND) bindings
      ==> ALL ((~) o v_has_Eval o SND) env) /\
   (!(s:(C,FFI)flat_state) ps vs bindings env.
      flat_pmatch_list s ps vs bindings = Match env /\
      ALL ((~) o v_has_Eval) vs /\
      ALL (ALL ((~) o v_has_Eval) o flat_store_v_vs) (flat_state_refs s) /\
      ALL ((~) o v_has_Eval o SND) bindings
      ==> ALL ((~) o v_has_Eval o SND) env)`,
  MATCH_MP_TAC flat_pmatch_ind THEN REPEAT CONJ_TAC THEN
  RW[flat_pmatch_def; v_has_Eval_def; ALL; o_THM] THEN
  GVS[case_eq "option"; case_eq "store_v"; case_eq "match_result"] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[FLATPAUX_store_lookup_Refv_noEval]);;

let flat_elimProof_has_Eval_def = prove
 (`(!t e pes. has_Eval (flat_Handle t e pes) <=>
              has_Eval e \/ EX has_Eval (MAP SND pes)) /\
   (!t x es. has_Eval (flat_Con t x es) <=> EX has_Eval es) /\
   (!x y e. has_Eval (flat_Fun x y e) <=> has_Eval e) /\
   (!t op es. has_Eval (flat_App t op es) <=> op = Src Eval \/ EX has_Eval es) /\
   (!t e1 e2 e3. has_Eval (flat_If t e1 e2 e3) <=>
                 has_Eval e1 \/ has_Eval e2 \/ has_Eval e3) /\
   (!t e pes. has_Eval (flat_Mat t e pes) <=>
              has_Eval e \/ EX has_Eval (MAP SND pes)) /\
   (!t opt e1 e2. has_Eval (flat_Let t opt e1 e2) <=> has_Eval e1 \/ has_Eval e2) /\
   (!x funs e. has_Eval (flat_Letrec x funs e) <=>
               has_Eval e \/ EX has_Eval (MAP (SND o SND) funs)) /\
   (!t e. has_Eval (flat_Raise t e) <=> has_Eval e) /\
   (!t n. has_Eval (Var_local t n) <=> F) /\
   (!t v. has_Eval (flat_Lit t v) <=> F)`,
  SUBGOAL_THEN `!es. has_Eval_list es <=> EX has_Eval es` ASSUME_TAC THENL
   [LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[has_Eval_def; EX]; ALL_TAC] THEN
  SUBGOAL_THEN `!pes. has_Eval_pats pes <=> EX has_Eval (MAP SND pes)` ASSUME_TAC THENL
   [LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[has_Eval_def; EX; MAP] THEN
    SPEC_TAC(`h:flat_pat#flat_exp`,`h:flat_pat#flat_exp`) THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM; has_Eval_def; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `!funs. has_Eval_funs funs <=> EX has_Eval (MAP (SND o SND) funs)`
    ASSUME_TAC THENL
   [LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[has_Eval_def; EX; MAP] THEN
    SPEC_TAC(`h:varN#varN#flat_exp`,`h:varN#varN#flat_exp`) THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM; has_Eval_def; SND; o_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[has_Eval_def]);;

(* EVALUATE INDUCTION *)

(* HOL4: val evaluate_exp_ind (the case of expression lists) *)
let FLATPAUX_evaluate_exp_ind =
  let p = `P:(flat_v)flat_environment->(C,FFI)flat_state->flat_exp list->bool` in
  let th = ISPECL [p; `\(s:(C,FFI)flat_state) (d:flat_exp). T`;
                   `\(s:(C,FFI)flat_state) (ds:flat_exp list). T`] flat_evaluate_ind in
  GEN p (CONV_RULE (DEPTH_CONV BETA_CONV THENC REWRITE_CONV[]) th);;

(* EVALUATE INDUCTION: the case of kept declarations *)

let FLATPAUX_res_simps =
  [find_sem_prim_res_globals_def; find_result_globals_def; find_v_globals_def;
   v_has_Eval_def; domain_def; domain_union; union_LN; EMPTY_SUBSET;
   UNION_SUBSET; ALL; EX; result_vs_def; o_THM];;

let FLATPAUX_KEEP_NIL_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN FS[flat_evaluate_def] THEN RVEQ_TAC THEN
  REWRITE_TAC FLATPAUX_res_simps;;

let FLATPAUX_PAIR_TAC tm s r =
  MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN s (X_CHOOSE_THEN r ASSUME_TAC));;

let FLATPAUX_lookups_simps =
  [find_lookups_def; domain_union; union_LN; UNION_SUBSET; ALL; o_THM;
   dest_GlobalVarLookup_def; option_CASE; domain_def; EMPTY_SUBSET;
   GSYM find_lookupsL_REVERSE; EVERY_REVERSE; o_DEF; NOT_EX; DE_MORGAN_THM;
   flat_elimProof_has_Eval_def];;
let FLATPAUX_DISCH_TAC : tactic =
  REWRITE_TAC FLATPAUX_lookups_simps THEN
  ASM_REWRITE_TAC[distinctness "result"; injectivity "result";
                  distinctness "error_result"; injectivity "error_result"] THEN NO_TAC;;
let FLATPAUX_IH_TAC lab rs : tactic =
  USE_THEN lab (fun ih ->
    let ih' = REWRITE_RULE[IMP_CONJ] ih in
    FIRST_ASSUM (fun th ->
      MP_TAC (REWRITE_RULE[IMP_IMP] (SPECL [`reachable:num_set`; rs]
                                       (MATCH_MP ih' th))))) THEN
  ANTS_TAC THENL [FLATPAUX_DISCH_TAC; STRIP_TAC];;
let FLATPAUX_KEEP_FINISH_TAC : tactic =
  TRY(FIRST_ASSUM(CONTR_TAC o REWRITE_RULE[distinctness "result"; injectivity "result";
                                           distinctness "error_result"])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE (HD :: o_DEF :: FLATPAUX_res_simps)) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  ASM_REWRITE_TAC(UNWIND_THM1 :: UNWIND_THM2 :: HD :: o_DEF :: NOT_EX :: EVERY_REVERSE ::
                  GSYM find_v_globalsL_REVERSE :: FLATPAUX_res_simps);;
let FLATPAUX_NORM_ASM_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE FLATPAUX_lookups_simps) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;
let FLATPAUX_SING_TAC : tactic =
  TRY(FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP flat_evaluate_sing) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC);;

let FLATPAUX_SIMPLE_ERR_TAC : tactic =
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  FLATPAUX_IH_TAC "ih1" `removed_state:(C,FFI)flat_state` THEN
  ASM_REWRITE_TAC[pair_CASE] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
  FLATPAUX_SING_TAC THEN FLATPAUX_KEEP_FINISH_TAC;;
let FLATPAUX_IS_HYP_EVAL th =
  rand(concl th) = `(new_state:(C,FFI)flat_state, result:(flat_v list,flat_v)result)`;;
let FLATPAUX_UNFOLD_HYP_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check FLATPAUX_IS_HYP_EVAL) THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[pair_CASE] THEN
  FLATPAUX_NORM_ASM_TAC;;
let FLATPAUX_SUBST_RES_TAC : tactic =
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE (HD :: FLATPAUX_res_simps));;
let FLATPAUX_CHAIN n (ttac:thm_tactic) lab : tactic = fun (asl,w as g) ->
  let th0 = REWRITE_RULE[IMP_CONJ] (snd(find (fun (l,_) -> l = lab) asl)) in
  let rec go k th = if k = 0 then th else
    go (k-1) (tryfind (fun (_,a) -> MATCH_MP th a) asl) in
  ttac (go n th0) g;;

let FLATPAUX_EXPAND_REL_TAC : tactic =
  ASSUM_LIST(fun ths -> MAP_EVERY (STRIP_ASSUME_TAC o REWRITE_RULE[flat_state_rel_def])
    (filter (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "flat_state_rel"
                       with Failure _ -> false) ths));;
let FLATPAUX_pmatch_env_facts = prove
 (`!pes (s:(C,FFI)flat_state) v env' p e (reachable:num_set) env.
     pmatch_rows pes s v = Match (env',p,e) /\
     domain (find_v_globals v) SUBSET domain reachable /\ ~v_has_Eval v /\
     domain (find_refs_globals (flat_state_refs s)) SUBSET domain reachable /\
     ALL (ALL ((~) o v_has_Eval) o flat_store_v_vs) (flat_state_refs s) /\
     domain (find_env_globals env) SUBSET domain reachable /\
     ALL ((~) o v_has_Eval o SND) (flat_environment_v env) /\
     domain (find_lookupsL (MAP SND pes)) SUBSET domain reachable /\
     ~EX has_Eval (MAP SND pes)
     ==> domain (find_lookups e) SUBSET domain reachable /\
         domain (find_env_globals
                   (flat_environment_v_fupd
                      (combin_K (APPEND env' (flat_environment_v env))) env)) SUBSET
         domain reachable /\
         ALL ((~) o v_has_Eval o SND)
           (flat_environment_v
              (flat_environment_v_fupd
                 (combin_K (APPEND env' (flat_environment_v env))) env)) /\
         ~has_Eval e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP pmatch_rows_IMP_pmatch) THEN
  REWRITE_TAC[find_env_globals_def; flat_environment_INFO.ri_accfupds; K_THM;
              MAP_APPEND; find_v_globalsL_APPEND; domain_union; UNION_SUBSET;
              ALL_APPEND] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[find_env_globals_def]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[pmatch_rows_find_lookups];
    MATCH_MP_TAC(CONJUNCT1 pmatch_Match_reachable) THEN
    MAP_EVERY EXISTS_TAC [`s:(C,FFI)flat_state`; `p:flat_pat`; `v:flat_v`;
                          `[]:(varN#flat_v)list`] THEN
    ASM_REWRITE_TAC[MAP; find_v_globals_def; domain_def; EMPTY_SUBSET];
    MATCH_MP_TAC(CONJUNCT1 pmatch_not_has_Eval) THEN
    MAP_EVERY EXISTS_TAC [`s:(C,FFI)flat_state`; `p:flat_pat`; `v:flat_v`;
                          `[]:(varN#flat_v)list`] THEN
    ASM_REWRITE_TAC[ALL];
    UNDISCH_TAC `~EX has_Eval (MAP SND (pes:(flat_pat#flat_exp)list))` THEN
    REWRITE_TAC[EXISTS_MEM; MEM_MAP] THEN ASM_MESON_TAC[SND]]);;

let FLATPAUX_PMATCH_ENV_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE FLATPAUX_res_simps) THEN FLATPAUX_EXPAND_REL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE FLATPAUX_lookups_simps) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    (REWRITE_RULE FLATPAUX_lookups_simps FLATPAUX_pmatch_env_facts))) THEN
  DISCH_THEN(MP_TAC o SPECL [`reachable:num_set`; `env:(flat_v)flat_environment`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];;
let FLATPAUX_IH2_CONS_TAC r2 =
  USE_THEN "ih2" (MP_TAC o SPECL [`s2:(C,FFI)flat_state`; r2;
                                  `reachable:num_set`; `new_removed_state:(C,FFI)flat_state`] o
                  C MP (ASSUME `flat_evaluate env (s:(C,FFI)flat_state) [e1] = (s1,Rval a)`) o
                  SPECL [`a:flat_v list`; `s1:(C,FFI)flat_state`]) THEN
  ANTS_TAC THENL [FLATPAUX_DISCH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP flat_evaluate_sing) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE (HD :: FLATPAUX_res_simps)) THEN
  FLATPAUX_KEEP_FINISH_TAC;;

let FLATPAUX_KEEP_CONS_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FLATPAUX_PAIR_TAC `flat_evaluate env (s:(C,FFI)flat_state) [e1]`
    `s1:(C,FFI)flat_state` `r1:(flat_v list,flat_v)result` THEN
  UNDISCH_TAC `flat_evaluate env (s:(C,FFI)flat_state) (CONS e1 (CONS e2 es)) =
               (new_state,result)` THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[pair_CASE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE FLATPAUX_lookups_simps) THEN
  CASES_ON `r1:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[] THENL
   [USE_THEN "ih1" (MP_TAC o SPECL [`s1:(C,FFI)flat_state`; `Rval a:(flat_v list,flat_v)result`;
                                  `reachable:num_set`; `removed_state:(C,FFI)flat_state`]) THEN
    ANTS_TAC THENL [FLATPAUX_DISCH_TAC; STRIP_TAC] THEN
    FLATPAUX_PAIR_TAC `flat_evaluate env (s1:(C,FFI)flat_state) (CONS e2 es)`
      `s2:(C,FFI)flat_state` `r2:(flat_v list,flat_v)result` THEN
    ASM_REWRITE_TAC[pair_CASE] THEN
    CASES_ON `r2:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THENL
     [FLATPAUX_IH2_CONS_TAC `Rval a':(flat_v list,flat_v)result`;
      FLATPAUX_IH2_CONS_TAC `Rerr a':(flat_v list,flat_v)result`];
    REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    USE_THEN "ih1" (MP_TAC o SPECL [`s1:(C,FFI)flat_state`; `Rerr a:(flat_v list,flat_v)result`;
                                  `reachable:num_set`; `removed_state:(C,FFI)flat_state`]) THEN
    ANTS_TAC THENL [FLATPAUX_DISCH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[pair_CASE] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
    FLATPAUX_KEEP_FINISH_TAC];;

let FLATPAUX_KEEP_RAISE_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih1") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FLATPAUX_PAIR_TAC `flat_evaluate env (s:(C,FFI)flat_state) [e]`
    `s1:(C,FFI)flat_state` `r1:(flat_v list,flat_v)result` THEN
  UNDISCH_TAC `flat_evaluate env (s:(C,FFI)flat_state) [flat_Raise x e] =
               (new_state,result)` THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[pair_CASE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE (flat_elimProof_has_Eval_def :: FLATPAUX_lookups_simps)) THEN
  CASES_ON `r1:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  FLATPAUX_IH_TAC "ih1" `removed_state:(C,FFI)flat_state` THEN
  ASM_REWRITE_TAC[pair_CASE] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
  FLATPAUX_SING_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE (HD :: FLATPAUX_res_simps)) THEN
  FLATPAUX_KEEP_FINISH_TAC;;

let FLATPAUX_KEEP_HANDLE_RAISE_TAC : tactic =
  FLATPAUX_IH_TAC "ih1" `removed_state:(C,FFI)flat_state` THEN
  ASM_REWRITE_TAC[pair_CASE] THEN CAKE_REWRITE_TAC[] THEN
  ASSUM_LIST(fun ths -> REWRITE_TAC(mapfilter (MATCH_MP flat_state_rel_pmatch_rows) ths)) THEN
  CASES_ON `pmatch_rows (pes:(flat_pat#flat_exp)list) (s1:(C,FFI)flat_state) a'` THEN
  CAKE_REWRITE_TAC[PAIR_EQ] THENL
   [FLATPAUX_SUBST_RES_TAC THEN FLATPAUX_KEEP_FINISH_TAC;
    FLATPAUX_SUBST_RES_TAC THEN FLATPAUX_KEEP_FINISH_TAC;
    SUBGOAL_THEN `?env1 p1 e1. a'' = (env1:(varN#flat_v)list,p1:flat_pat,e1:flat_exp)`
      STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; FIRST_X_ASSUM SUBST_ALL_TAC] THEN
    CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
     [DISCH_TAC THEN REWRITE_TAC[o_DEF] THEN
      FLATPAUX_CHAIN 3 (fun th -> MATCH_MP_TAC (REWRITE_RULE[IMP_IMP]
         (SPECL [`new_state:(C,FFI)flat_state`; `result:(flat_v list,flat_v)result`;
                 `reachable:num_set`; `new_removed_state:(C,FFI)flat_state`] th))) "ih2" THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP pmatch_rows_IMP_pmatch) THEN
      REWRITE_TAC FLATPAUX_lookups_simps THEN ASM_REWRITE_TAC[] THEN
      FLATPAUX_PMATCH_ENV_TAC;
      FLATPAUX_SUBST_RES_TAC THEN FLATPAUX_KEEP_FINISH_TAC]];;

let FLATPAUX_KEEP_HANDLE_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FLATPAUX_PAIR_TAC `flat_evaluate env (s:(C,FFI)flat_state) [e]`
    `s1:(C,FFI)flat_state` `r1:(flat_v list,flat_v)result` THEN
  FLATPAUX_UNFOLD_HYP_TAC THEN
  CASES_ON `r1:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[PAIR_EQ] THENL
   [FLATPAUX_SIMPLE_ERR_TAC;
    CASES_ON `a:(flat_v)error_result` THEN CAKE_REWRITE_TAC[PAIR_EQ] THENL
     [FLATPAUX_KEEP_HANDLE_RAISE_TAC; FLATPAUX_SIMPLE_ERR_TAC]];;

let FLATPAUX_KEEP_CON_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih1") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FLATPAUX_PAIR_TAC `flat_evaluate env (s:(C,FFI)flat_state) (REVERSE es)`
    `s1:(C,FFI)flat_state` `r1:(flat_v list,flat_v)result` THEN
  FLATPAUX_UNFOLD_HYP_TAC THEN
  CASES_ON `r1:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
  FLATPAUX_SIMPLE_ERR_TAC;;
let FLATPAUX_KEEP_VAR_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN FLATPAUX_UNFOLD_HYP_TAC THEN
  CASES_ON `ALOOKUP (flat_environment_v (env:(flat_v)flat_environment)) n` THEN
  CAKE_REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_SUBST_RES_TAC THEN
  FLATPAUX_KEEP_FINISH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALOOKUP_MEM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[find_env_globals_def; GSYM ALL_MEM]) THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[find_v_globalsL_MEM; SUBSET_TRANS];
    FIRST_X_ASSUM(MP_TAC o SPEC `(n,a):varN#flat_v` o
                  check (is_forall o concl)) THEN ASM_REWRITE_TAC[]];;
let FLATPAUX_KEEP_FUN_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN FLATPAUX_UNFOLD_HYP_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_SUBST_RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[find_env_globals_def]) THEN
  FLATPAUX_KEEP_FINISH_TAC THEN ASM_REWRITE_TAC[EVERY_MAP];;

(* local helpers: the environments that closures and Letrec create *)

let FLATPAUX_build_rec_env_facts = prove
 (`!funs (env:(flat_v)flat_environment) vs (R:num->bool).
     domain (find_v_globalsL (MAP SND (flat_environment_v env))) SUBSET R /\
     domain (find_lookupsL (MAP (SND o SND) funs)) SUBSET R /\
     domain (find_v_globalsL (MAP SND vs)) SUBSET R /\
     ALL (\x. ~v_has_Eval (SND x)) (flat_environment_v env) /\
     ALL (\x. ~has_Eval x) (MAP (SND o SND) funs) /\
     ALL (\x. ~v_has_Eval (SND x)) vs
     ==> domain (find_v_globalsL (MAP SND (flat_build_rec_env funs env vs)))
           SUBSET R /\
         ALL (\x. ~v_has_Eval (SND x)) (flat_build_rec_env funs env vs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[build_rec_env_eq_MAP; MAP_APPEND; find_v_globalsL_APPEND;
              domain_union; UNION_SUBSET; ALL_APPEND] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (CASE_TERM
   `!l:(varN#varN#flat_exp)list.
      domain (find_v_globalsL (MAP SND (MAP (\fxe. match fxe with
                 (f,x,e) -> (f,flat_Recclosure env funs f)) l))) SUBSET R /\
      ALL (\x. ~v_has_Eval (SND x)) (MAP (\fxe. match fxe with
                 (f,x,e) -> (f,flat_Recclosure env funs f)) l)`)
   (fun th -> REWRITE_TAC[th]) THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; ALL; find_v_globals_def; domain_def; EMPTY_SUBSET;
                  domain_union; UNION_SUBSET] THEN
  SPEC_TAC(`h:varN#varN#flat_exp`,`h:varN#varN#flat_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; SND; find_v_globals_def; domain_union;
              UNION_SUBSET; v_has_Eval_def; DE_MORGAN_THM; NOT_EX] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_EX; EVERY_MAP; o_DEF]) THEN
  ASM_REWRITE_TAC[EVERY_MAP; o_DEF]);;

let FLATPAUX_find_recfun_facts = prove
 (`!n (funs:(varN#varN#flat_exp)list) x e.
     find_recfun n funs = SOME (x,e)
     ==> domain (find_lookups e) SUBSET domain (find_lookupsL (MAP (SND o SND) funs)) /\
         (ALL (\x. ~has_Eval x) (MAP (SND o SND) funs) ==> ~has_Eval e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[find_recfun_ALOOKUP] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP ALOOKUP_MEM) THEN
  SUBGOAL_THEN `MEM (e:flat_exp) (MAP (SND o SND) (funs:(varN#varN#flat_exp)list))`
    ASSUME_TAC THENL
   [REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `(n,x,e):varN#varN#flat_exp` THEN
    ASM_REWRITE_TAC[o_THM];
    ASM_SIMP_TAC[find_lookupsL_MEM] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    ASM_MESON_TAC[]]);;
let FLATPAUX_do_opapp_facts = prove
 (`!vs env' e (reachable:num_set).
     flat_do_opapp vs = SOME (env',e) /\
     domain (find_v_globalsL vs) SUBSET domain reachable /\
     ALL (\x. ~v_has_Eval x) vs
     ==> domain (find_lookups e) SUBSET domain reachable /\
         domain (find_env_globals env') SUBSET domain reachable /\
         ALL (\x. ~v_has_Eval (SND x)) (flat_environment_v env') /\
         ~has_Eval e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_do_opapp_def] THEN STRIP_TAC THEN
  FLATSEMAUX_SPLIT_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[find_v_globals_def; domain_union; UNION_SUBSET; ALL;
                              v_has_Eval_def; DE_MORGAN_THM; NOT_EX; union_LN;
                              EVERY_MAP]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REWRITE_TAC[find_env_globals_def; flat_environment_INFO.ri_accfupds; K_THM; MAP;
              find_v_globals_def; domain_union; UNION_SUBSET; ALL] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FLATPAUX_find_recfun_facts) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `domain (find_lookupsL (MAP (SND o SND) (a1':(varN#varN#flat_exp)list)))` THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`a1':(varN#varN#flat_exp)list`; `a0':(flat_v)flat_environment`;
                   `flat_environment_v (a0':(flat_v)flat_environment)`;
                   `domain (reachable:num_set)`] FLATPAUX_build_rec_env_facts) THEN
    ASM_SIMP_TAC[EVERY_MAP];
    MP_TAC(ISPECL [`a1':(varN#varN#flat_exp)list`; `a0':(flat_v)flat_environment`;
                   `flat_environment_v (a0':(flat_v)flat_environment)`;
                   `domain (reachable:num_set)`] FLATPAUX_build_rec_env_facts) THEN
    ASM_SIMP_TAC[EVERY_MAP];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[EVERY_MAP]]);;

let FLATPAUX_dest_thunk_IsThunk = prove
 (`!vs (st:(flat_v store_v)list) m v.
     flat_dest_thunk vs st = flat_IsThunk m v
     ==> ?b n. vs = [flat_Loc b n] /\ store_lookup n st = SOME (Thunk m v)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[flat_dest_thunk_def; distinctness "flat_dest_thunk_ret"] THEN
  CASES_ON `h:flat_v` THEN
  REWRITE_TAC[flat_dest_thunk_def; distinctness "flat_dest_thunk_ret"] THEN
  CASES_ON `t:flat_v list` THEN
  REWRITE_TAC[flat_dest_thunk_def; distinctness "flat_dest_thunk_ret"] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_eq "option"; case_eq "store_v"; case_eq "thunk_mode";
     COND_CASE_EQ; distinctness "flat_dest_thunk_ret"; injectivity "flat_dest_thunk_ret"]) THEN
  ASM_MESON_TAC[]);;

(* the one-clause (case tree) definition that sem1aux_def made (HOL4 oneline) *)
let FLATPAUX_oneline name =
  find (fun th -> try fst(dest_const(fst(strip_comb(lhs(snd(strip_forall(concl th)))))))
                      = name with Failure _ -> false) (definitions());;

let FLATPAUX_update_thunk_SOME = prove
 (`!vs (st:(flat_v store_v)list) vs2 refs.
     flat_update_thunk vs st vs2 = SOME refs
     ==> ?n v. vs2 = [v] /\ store_assign n (Thunk Evaluated v) st = SOME refs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FLATPAUX_oneline "flat_update_thunk"] THEN
  BETA_TAC THEN DISCH_TAC THEN FLATSEMAUX_SPLIT_TAC THEN RVEQ_TAC THEN
  ASM_MESON_TAC[]);;

let FLATPAUX_dec_clock_rel = prove
 (`!reachable (s:(C,FFI)flat_state) t.
     flat_state_rel reachable s t
     ==> flat_state_rel reachable (flat_dec_clock s) (flat_dec_clock t)`,
  REWRITE_TAC[flat_state_rel_def; flat_dec_clock_def; flat_state_INFO.ri_accfupds;
              K_THM] THEN MESON_TAC[]);;

let FLATPAUX_IH_N_TAC lab n rs (dtac:tactic) : tactic = fun (asl,w as g) ->
  let th0 = REWRITE_RULE[IMP_CONJ] (snd(find (fun (l,_) -> l = lab) asl)) in
  let rec go k th = if k = 0 then th else
    go (k-1) (tryfind (fun (_,a) -> MATCH_MP th a) asl) in
  let th = REWRITE_RULE[IMP_IMP] (SPECL [`reachable:num_set`; rs] (go n th0)) in
  (MP_TAC th THEN ANTS_TAC THENL [dtac; STRIP_TAC]) g;;

let FLATPAUX_res_inj = [distinctness "result"; injectivity "result";
                        distinctness "error_result"; injectivity "error_result"];;

let FLATPAUX_FORCE_DISCH_TAC : tactic =
  REWRITE_TAC (flat_AppUnit_def :: find_env_globals_def ::
               flat_environment_INFO.ri_accessors :: MAP :: find_v_globals_def ::
               FLATPAUX_lookups_simps) THEN
  CAKE_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE FLATPAUX_res_inj) THEN
  ASM_REWRITE_TAC FLATPAUX_res_inj THEN NO_TAC;;

let FLATPAUX_KEEP_APP_OPAPP_TAC : tactic =
  REWRITE_TAC[GSYM (CONJUNCT1 (REWRITE_RULE[flat_state_rel_def]
     (ASSUME `flat_state_rel reachable (s1:(C,FFI)flat_state) new_removed_state`)))] THEN
  CASES_ON `flat_do_opapp (REVERSE a)` THEN CAKE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_SUBST_RES_TAC THEN FLATPAUX_KEEP_FINISH_TAC;
    SUBGOAL_THEN `?env1 e1. a' = (env1:(flat_v)flat_environment, e1:flat_exp)`
      STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; FIRST_X_ASSUM SUBST_ALL_TAC] THEN
    CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_SUBST_RES_TAC THEN FLATPAUX_KEEP_FINISH_TAC;
      DISCH_TAC THEN REWRITE_TAC[o_DEF] THEN
      FLATPAUX_CHAIN 3 (fun th -> MATCH_MP_TAC (REWRITE_RULE[IMP_IMP]
         (SPECL [`new_state:(C,FFI)flat_state`; `result:(flat_v list,flat_v)result`;
                 `reachable:num_set`;
                 `flat_dec_clock (new_removed_state:(C,FFI)flat_state)`] th))) "ih_opapp" THEN
      SUBGOAL_THEN `domain (find_v_globalsL (REVERSE a)) SUBSET domain (reachable:num_set) /\
                    ALL (\x. ~v_has_Eval x) (REVERSE a)` STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[GSYM find_v_globalsL_REVERSE; EVERY_REVERSE]; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `reachable:num_set` o
                  MATCH_MP (REWRITE_RULE[IMP_CONJ] FLATPAUX_do_opapp_facts)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      REWRITE_TAC FLATPAUX_lookups_simps THEN ASM_SIMP_TAC[FLATPAUX_dec_clock_rel]]];;

let FLATPAUX_KEEP_APP_UPDATE_TAC : tactic =
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FLATPAUX_update_thunk_SOME) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  FLATPAUX_EXPAND_REL_TAC THEN FLATPAUX_REFS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE (o_DEF :: FLATPAUX_res_simps)) THEN
  REWRITE_TAC (find_refs_globals_def :: flat_store_v_vs_def :: o_DEF :: FLATPAUX_res_simps) THEN
  ASM_REWRITE_TAC[];;

let FLATPAUX_KEEP_APP_FORCE_TAC : tactic =
  REWRITE_TAC[GSYM (CONJUNCT1 (CONJUNCT2 (REWRITE_RULE[flat_state_rel_def]
     (ASSUME `flat_state_rel reachable (s1:(C,FFI)flat_state) new_removed_state`))))] THEN
  CASES_ON `flat_dest_thunk a (flat_state_refs (s1:(C,FFI)flat_state))` THEN
  CAKE_REWRITE_TAC[] THENL
   [FLATPAUX_SUBST_RES_TAC THEN FLATPAUX_KEEP_FINISH_TAC;
    FLATPAUX_SUBST_RES_TAC THEN FLATPAUX_KEEP_FINISH_TAC;
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FLATPAUX_dest_thunk_IsThunk) THEN
    FLATPAUX_EXPAND_REL_TAC THEN FLATPAUX_LOOKUP_FACTS_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE (find_refs_globals_def :: flat_store_v_vs_def :: o_DEF ::
                                 FLATPAUX_res_simps)) THEN
    CASES_ON `a0:thunk_mode` THEN CAKE_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_SUBST_RES_TAC THEN FLATPAUX_KEEP_FINISH_TAC;
      FLATPAUX_PAIR_TAC `flat_evaluate (flat_environment_REC [implode "f",a1])
          (s1:(C,FFI)flat_state) [flat_AppUnit (Var_local backend_common_None (implode "f"))]`
        `s2:(C,FFI)flat_state` `r2:(flat_v list,flat_v)result` THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[th; pair_CASE]) THEN
      CASES_ON `r2:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[] THENL
       [FLATPAUX_IH_N_TAC "ih_force" 3 `new_removed_state:(C,FFI)flat_state`
          FLATPAUX_FORCE_DISCH_TAC THEN
        ASM_REWRITE_TAC[pair_CASE] THEN CAKE_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM (CONJUNCT1 (CONJUNCT2 (REWRITE_RULE[flat_state_rel_def]
          (ASSUME `flat_state_rel reachable (s2:(C,FFI)flat_state) new_removed_state'`))))] THEN
        CASES_ON `flat_update_thunk [flat_Loc b n] (flat_state_refs (s2:(C,FFI)flat_state)) a'` THEN
        CAKE_REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_SUBST_RES_TAC THENL
         [FLATPAUX_KEEP_FINISH_TAC;
          FLATPAUX_KEEP_FINISH_TAC THEN FLATPAUX_KEEP_APP_UPDATE_TAC];
        REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_SUBST_RES_TAC THEN
        FLATPAUX_IH_N_TAC "ih_force" 3 `new_removed_state:(C,FFI)flat_state`
          FLATPAUX_FORCE_DISCH_TAC THEN
        ASM_REWRITE_TAC[pair_CASE] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
        FLATPAUX_KEEP_FINISH_TAC]]];;

let FLATPAUX_KEEP_APP_OTHER_TAC : tactic =
  REWRITE_TAC[ASSUME `~(op = Src (ThunkOp ForceThunk))`] THEN
  CASES_ON `flat_do_app (s1:(C,FFI)flat_state) op (REVERSE a)` THEN CAKE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_SUBST_RES_TAC THEN FLATPAUX_KEEP_FINISH_TAC;
    SUBGOAL_THEN `?s3 r3. a' = (s3:(C,FFI)flat_state, r3:(flat_v,flat_v)result)`
      STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; FIRST_X_ASSUM SUBST_ALL_TAC] THEN
    CAKE_REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_SUBST_RES_TAC THEN
    SUBGOAL_THEN `domain (find_lookups (flat_App x op [])) SUBSET domain (reachable:num_set)`
      ASSUME_TAC THENL
     [REWRITE_TAC[find_lookups_def] THEN
      FIRST_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
        t = `dest_GlobalVarLookup op`)) (concl th))) THEN
      CASES_ON `dest_GlobalVarLookup op` THEN
      CAKE_REWRITE_TAC[domain_insert; INSERT_SUBSET; domain_def; EMPTY_SUBSET;
                       find_lookups_def] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(r3 = Rerr (Rabort Rtype_error):(flat_v,flat_v)result)` ASSUME_TAC THENL
     [UNDISCH_TAC `~(list_result (r3:(flat_v,flat_v)result) = Rerr (Rabort Rtype_error))` THEN
      CASES_ON `r3:(flat_v,flat_v)result` THEN
      REWRITE_TAC[list_result_def; distinctness "result"; injectivity "result"];
      ALL_TAC] THEN
    MP_TAC (SPECL [`reachable:num_set`; `s1:(C,FFI)flat_state`;
                   `new_removed_state:(C,FFI)flat_state`; `op:flat_op`;
                   `REVERSE a:flat_v list`; `s3:(C,FFI)flat_state`;
                   `r3:(flat_v,flat_v)result`; `new_removed_state:(C,FFI)flat_state`]
                  (INST [`x:tra`,`tra:tra`] do_app_SOME_flat_state_rel)) THEN
    REWRITE_TAC[IMP_IMP] THEN ANTS_TAC THENL
     [REWRITE_TAC[o_DEF; EVERY_REVERSE; GSYM find_v_globalsL_REVERSE] THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_KEEP_FINISH_TAC];;

let FLATPAUX_KEEP_APP_TAC : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1")
     (CONJUNCTS_THEN2 (LABEL_TAC "ih_opapp") (LABEL_TAC "ih_force"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FLATPAUX_PAIR_TAC `flat_evaluate env (s:(C,FFI)flat_state) (REVERSE es)`
    `s1:(C,FFI)flat_state` `r1:(flat_v list,flat_v)result` THEN
  FLATPAUX_UNFOLD_HYP_TAC THEN
  SUBGOAL_THEN `domain (find_lookupsL es) SUBSET domain (reachable:num_set)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
      t = `dest_GlobalVarLookup op`)) (concl th))) THEN
    CASES_ON `dest_GlobalVarLookup op` THEN
    CAKE_REWRITE_TAC[domain_insert; INSERT_SUBSET] THEN SIMP_TAC[];
    ALL_TAC] THEN
  CASES_ON `r1:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[] THENL
   [FLATPAUX_IH_TAC "ih1" `removed_state:(C,FFI)flat_state` THEN
    ASM_REWRITE_TAC[pair_CASE] THEN CAKE_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE (o_DEF :: FLATPAUX_res_simps)) THEN
    ASM_CASES_TAC `op = Src Opapp` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FLATPAUX_KEEP_APP_OPAPP_TAC;
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `op = Src (ThunkOp ForceThunk)` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN CAKE_REWRITE_TAC[] THEN
        RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN FLATPAUX_KEEP_APP_FORCE_TAC;
        FLATPAUX_KEEP_APP_OTHER_TAC]];
    REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_SIMPLE_ERR_TAC];;

let FLATPAUX_KEEP_IF_BRANCH_TAC : tactic =
  DISCH_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP do_if_either_or) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[o_DEF] THEN
  FLATPAUX_CHAIN 2 (fun th -> MATCH_MP_TAC (REWRITE_RULE[IMP_IMP]
     (SPECL [`new_state:(C,FFI)flat_state`; `result:(flat_v list,flat_v)result`;
             `reachable:num_set`; `new_removed_state:(C,FFI)flat_state`] th))) "ih2" THEN
  REWRITE_TAC FLATPAUX_lookups_simps THEN ASM_REWRITE_TAC[];;
let FLATPAUX_KEEP_IF_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FLATPAUX_PAIR_TAC `flat_evaluate env (s:(C,FFI)flat_state) [e1]`
    `s1:(C,FFI)flat_state` `r1:(flat_v list,flat_v)result` THEN
  FLATPAUX_UNFOLD_HYP_TAC THEN
  CASES_ON `r1:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[] THENL
   [FLATPAUX_IH_TAC "ih1" `removed_state:(C,FFI)flat_state` THEN
    ASM_REWRITE_TAC[pair_CASE] THEN CAKE_REWRITE_TAC[] THEN
    CASES_ON `flat_do_if (HD a) e2 e3` THEN CAKE_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_SUBST_RES_TAC THEN FLATPAUX_KEEP_FINISH_TAC;
      FLATPAUX_KEEP_IF_BRANCH_TAC];
    REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_SIMPLE_ERR_TAC];;

let FLATPAUX_CHAINR n rws (ttac:thm_tactic) lab : tactic = fun (asl,w as g) ->
  let th0 = REWRITE_RULE[IMP_CONJ] (snd(find (fun (l,_) -> l = lab) asl)) in
  let rec go k th = if k = 0 then th else
    go (k-1) (REWRITE_RULE rws (tryfind (fun (_,a) -> MATCH_MP th a) asl)) in
  ttac (go n th0) g;;
let FLATPAUX_KEEP_MAT_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FLATPAUX_PAIR_TAC `flat_evaluate env (s:(C,FFI)flat_state) [e]`
    `s1:(C,FFI)flat_state` `r1:(flat_v list,flat_v)result` THEN
  FLATPAUX_UNFOLD_HYP_TAC THEN
  CASES_ON `r1:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[] THENL
   [FLATPAUX_IH_TAC "ih1" `removed_state:(C,FFI)flat_state` THEN
    ASM_REWRITE_TAC[pair_CASE] THEN CAKE_REWRITE_TAC[] THEN
    FLATPAUX_SING_TAC THEN REWRITE_TAC[HD] THEN
    ASSUM_LIST(fun ths -> REWRITE_TAC(mapfilter (MATCH_MP flat_state_rel_pmatch_rows) ths)) THEN
    CASES_ON `pmatch_rows (pes:(flat_pat#flat_exp)list) (s1:(C,FFI)flat_state) y` THEN
    CAKE_REWRITE_TAC[PAIR_EQ] THENL
     [FLATPAUX_SUBST_RES_TAC THEN REWRITE_TAC[flat_bind_exn_v_def] THEN
      FLATPAUX_KEEP_FINISH_TAC;
      FLATPAUX_SUBST_RES_TAC THEN FLATPAUX_KEEP_FINISH_TAC;
      SUBGOAL_THEN `?env1 p1 e1. a' = (env1:(varN#flat_v)list,p1:flat_pat,e1:flat_exp)`
        STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; FIRST_X_ASSUM SUBST_ALL_TAC] THEN
      CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
       [DISCH_TAC THEN REWRITE_TAC[o_DEF] THEN
        FLATPAUX_CHAINR 3 [HD] (fun th -> MATCH_MP_TAC (REWRITE_RULE[IMP_IMP]
           (SPECL [`new_state:(C,FFI)flat_state`; `result:(flat_v list,flat_v)result`;
                   `reachable:num_set`; `new_removed_state:(C,FFI)flat_state`] th))) "ih2" THEN
        FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP pmatch_rows_IMP_pmatch) THEN
        REWRITE_TAC FLATPAUX_lookups_simps THEN ASM_REWRITE_TAC[] THEN
        FLATPAUX_PMATCH_ENV_TAC;
        FLATPAUX_SUBST_RES_TAC THEN FLATPAUX_KEEP_FINISH_TAC]];
    REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_SIMPLE_ERR_TAC];;

let FLATPAUX_KEEP_LET_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FLATPAUX_PAIR_TAC `flat_evaluate env (s:(C,FFI)flat_state) [e1]`
    `s1:(C,FFI)flat_state` `r1:(flat_v list,flat_v)result` THEN
  FLATPAUX_UNFOLD_HYP_TAC THEN
  CASES_ON `r1:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[] THENL
   [FLATPAUX_IH_TAC "ih1" `removed_state:(C,FFI)flat_state` THEN
    ASM_REWRITE_TAC[pair_CASE] THEN CAKE_REWRITE_TAC[] THEN
    FLATPAUX_SING_TAC THEN REWRITE_TAC[HD] THEN
    DISCH_TAC THEN REWRITE_TAC[o_DEF] THEN
    FLATPAUX_CHAINR 1 [HD] (fun th -> MATCH_MP_TAC (REWRITE_RULE[IMP_IMP]
       (SPECL [`new_state:(C,FFI)flat_state`; `result:(flat_v list,flat_v)result`;
               `reachable:num_set`; `new_removed_state:(C,FFI)flat_state`] th))) "ih2" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[find_env_globals_def]) THEN
    REWRITE_TAC (find_env_globals_def :: flat_environment_INFO.ri_accfupds ::
                 FLATPAUX_lookups_simps) THEN
    CASES_ON `n:varN option` THEN
    REWRITE_TAC[opt_bind_def; option_CASE; MAP; find_v_globals_def; domain_union;
                UNION_SUBSET; ALL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE (o_DEF :: FLATPAUX_res_simps)) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_SIMPLE_ERR_TAC];;

let FLATPAUX_KEEP_LETREC_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih1") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FLATPAUX_UNFOLD_HYP_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [DISCH_TAC THEN REWRITE_TAC[o_DEF] THEN
    FLATPAUX_CHAINR 1 [] (fun th -> MATCH_MP_TAC (REWRITE_RULE[IMP_IMP]
       (SPECL [`new_state:(C,FFI)flat_state`; `result:(flat_v list,flat_v)result`;
               `reachable:num_set`; `removed_state:(C,FFI)flat_state`] th))) "ih1" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[find_env_globals_def]) THEN
    REWRITE_TAC (find_env_globals_def :: flat_environment_INFO.ri_accfupds :: K_THM ::
                 FLATPAUX_lookups_simps) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`funs:(varN#varN#flat_exp)list`; `env:(flat_v)flat_environment`;
                   `flat_environment_v (env:(flat_v)flat_environment)`;
                   `domain (reachable:num_set)`] FLATPAUX_build_rec_env_facts) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[EVERY_MAP; o_DEF]) THEN
    ASM_SIMP_TAC[EVERY_MAP; o_DEF];
    FLATPAUX_SUBST_RES_TAC THEN FLATPAUX_KEEP_FINISH_TAC];;

let evaluate_keep_flat_state_rel_eq_lemma = prove
 (`!env (state:(C,FFI)flat_state) exprL new_state result (reachable:num_set)
    removed_state.
     flat_evaluate env state exprL = (new_state,result) /\
     domain (find_lookupsL exprL) SUBSET domain reachable /\
     flat_state_rel reachable state removed_state /\
     domain (find_env_globals env) SUBSET domain reachable /\
     ALL ((~) o v_has_Eval o SND) (flat_environment_v env) /\
     ALL ((~) o has_Eval) exprL /\
     ~(result = Rerr (Rabort Rtype_error))
     ==> ?new_removed_state.
           flat_evaluate env removed_state exprL = (new_removed_state,result) /\
           flat_state_rel reachable new_state new_removed_state /\
           domain (find_sem_prim_res_globals result) SUBSET domain reachable /\
           ALL ((~) o v_has_Eval) (result_vs result)`,
  MATCH_MP_TAC FLATPAUX_evaluate_exp_ind THEN REPEAT CONJ_TAC THENL
   [FLATPAUX_KEEP_NIL_TAC; FLATPAUX_KEEP_CONS_TAC; FLATPAUX_KEEP_NIL_TAC;
    FLATPAUX_KEEP_RAISE_TAC; FLATPAUX_KEEP_HANDLE_TAC; FLATPAUX_KEEP_CON_TAC;
    FLATPAUX_KEEP_CON_TAC; FLATPAUX_KEEP_VAR_TAC; FLATPAUX_KEEP_FUN_TAC;
    FLATPAUX_KEEP_APP_TAC; FLATPAUX_KEEP_IF_TAC; FLATPAUX_KEEP_MAT_TAC;
    FLATPAUX_KEEP_LET_TAC; FLATPAUX_KEEP_LETREC_TAC]);;

(* EVALUATE SPECIALISATION *)

let evaluate_sing_keep_flat_state_rel_eq = prove
 (`!env (state:(C,FFI)flat_state) exprL new_state result expr (reachable:num_set)
    removed_state.
     flat_evaluate (flat_environment_v_fupd (combin_K []) env) state exprL =
       (new_state,result) /\
     flat_state_rel reachable state removed_state /\
     exprL = [expr] /\
     keep reachable expr /\
     domain (find_lookups expr) SUBSET domain reachable /\
     ~has_Eval expr /\
     ~(result = Rerr (Rabort Rtype_error))
     ==> ?new_removed_state.
           flat_evaluate (flat_environment_v_fupd (combin_K []) env) removed_state exprL =
             (new_removed_state,result) /\
           flat_state_rel reachable new_state new_removed_state`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`flat_environment_v_fupd (combin_K []) (env:(flat_v)flat_environment)`;
                 `state:(C,FFI)flat_state`; `exprL:flat_exp list`;
                 `new_state:(C,FFI)flat_state`; `result:(flat_v list,flat_v)result`;
                 `reachable:num_set`; `removed_state:(C,FFI)flat_state`]
                evaluate_keep_flat_state_rel_eq_lemma) THEN
  ASM_REWRITE_TAC[find_env_globals_def; flat_environment_INFO.ri_accfupds; K_THM; MAP;
                  ALL; find_v_globals_def; find_lookups_def; union_LN; domain_def;
                  EMPTY_SUBSET; o_THM] THEN
  MESON_TAC[]);;

(* EVALUATE_DEC *)

(* a local helper: the lookups of a kept declaration of a closed program are *)
(* reachable (the analysis step of HOL4's proof of evaluate_dec_flat_state_rel) *)

let FLATPAUX_decs_closed_lookups = prove
 (`!(reachable:num_set) dec.
     decs_closed reachable [dec] /\ keep reachable dec
     ==> domain (find_lookups dec) SUBSET domain reachable`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[decs_closed_def; analyse_code_def; analyse_exp_def; keep_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_CASES_TAC `flat_elim_is_pure dec` THEN ASM_REWRITE_TAC[] THEN
  TRY(ASM_CASES_TAC `is_hidden dec` THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[code_analysis_union_def] THEN
  ONCE_REWRITE_TAC[num_set_tree_union_sym] THEN
  REWRITE_TAC[num_set_tree_union_def; union_LN; PAIR_EQ] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_UNWIND_THM1] THEN
  TRY(REWRITE_TAC[domain_union] THEN SET_TAC[] THEN NO_TAC) THEN
  STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[inter_eq_LN; DISJOINT; EXTENSION; IN_INTER;
                                      NOT_IN_EMPTY] o check (is_neg o concl)) THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[is_reachable_def] THEN MATCH_MP_TAC RTC_SINGLE THEN
  REWRITE_TAC[is_adjacent_def; lookup_map] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[domain_lookup]) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN ASSUME_TAC o check (is_exists o concl))) THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; option_INJ; K_THM] THEN ASM_MESON_TAC[one]);;

let evaluate_dec_flat_state_rel = prove
 (`!(state:(C,FFI)flat_state) dec new_state result (reachable:num_set) removed_state.
     evaluate_dec state dec = (new_state,result) /\
     decs_closed reachable [dec] /\
     flat_state_rel reachable state removed_state /\ keep reachable dec /\
     ~has_Eval_dec dec /\
     ~(result = SOME (Rabort Rtype_error))
     ==> ?new_removed_state.
           evaluate_dec removed_state dec = (new_removed_state,result) /\
           flat_state_rel reachable new_state new_removed_state`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FLATPAUX_decs_closed_lookups o
              CONJ (ASSUME `decs_closed (reachable:num_set) [dec]`)) THEN
  FLATPAUX_PAIR_TAC `flat_evaluate (flat_environment_REC []) (state:(C,FFI)flat_state)
                       [dec]` `s1:(C,FFI)flat_state` `r1:(flat_v list,flat_v)result` THEN
  MP_TAC(ISPECL [`flat_environment_REC []:(flat_v)flat_environment`;
                 `state:(C,FFI)flat_state`; `[dec]:flat_exp list`;
                 `s1:(C,FFI)flat_state`; `r1:(flat_v list,flat_v)result`; `dec:flat_exp`;
                 `reachable:num_set`; `removed_state:(C,FFI)flat_state`]
                evaluate_sing_keep_flat_state_rel_eq) THEN
  REWRITE_TAC[flat_environment_INFO.ri_fupds; K_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[has_Eval_dec_def]) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `evaluate_dec (state:(C,FFI)flat_state) dec = (new_state,result)` THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[pair_CASE] THEN
  CASES_ON `r1:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
    REWRITE_TAC[distinctness "result"] THEN STRIP_TAC THEN
    EXISTS_TAC `new_removed_state:(C,FFI)flat_state` THEN
    ASM_REWRITE_TAC[pair_CASE] THEN CAKE_REWRITE_TAC[];
    REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN
    ASM_REWRITE_TAC[injectivity "result"] THEN STRIP_TAC THEN
    EXISTS_TAC `new_removed_state:(C,FFI)flat_state` THEN
    ASM_REWRITE_TAC[pair_CASE] THEN CAKE_REWRITE_TAC[]]);;

let total_pat_IMP = prove
 (`(!(s:(C,FFI)flat_state) p v env res.
      flat_pmatch s p v env = res /\ total_pat p ==> ~(res = No_match)) /\
   (!(s:(C,FFI)flat_state) ps vs env res.
      LENGTH ps = LENGTH vs /\ flat_pmatch_list s ps vs env = res /\
      total_pat_list ps ==> ~(res = No_match))`,
  MATCH_MP_TAC flat_pmatch_ind THEN REPEAT CONJ_TAC THEN
  RW[flat_pmatch_def; total_pat_def] THEN
  FIRST
   [FIRST_ASSUM(MP_TAC o check (fun th ->
      can (term_match [] `total_pat (flat_Pcon stmp ps)`) (concl th))) THEN
    CASES_ON `stmp:((ctor_id#type_group_id)option)` THEN
    REWRITE_TAC[total_pat_def] THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pmatch_stamps_ok_cases; option_DISTINCT;
                                OPTION_MAP_DEF]) THEN
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[OPTION_MAP_DEF]) THEN
    ASM_MESON_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[case_eq "match_result"]) THEN
    ASM_MESON_TAC[distinctness "match_result"]]);;

let EXISTS_total_pat = prove
 (`!(pes:(flat_pat#A)list) (new_state:(C,FFI)flat_state) v.
     EX total_pat (MAP FST pes) ==> ~(pmatch_rows pes new_state v = No_match)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; EX] THEN
  SPEC_TAC(`h:flat_pat#A`,`h:flat_pat#A`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; pmatch_rows_def] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_eq "match_result"]) THEN
  ASM_MESON_TAC[CONJUNCT1 total_pat_IMP; distinctness "match_result"]);;

let FLATPAUX_globals_rel_init_unreachable = prove
 (`!reachable s_g t_g n (v:flat_v).
     globals_rel reachable s_g t_g /\ ~(n IN domain reachable) /\
     n < LENGTH s_g /\ EL n s_g = NONE
     ==> globals_rel reachable (LUPDATE (SOME v) n s_g) t_g`,
  REWRITE_TAC[globals_rel_def; LENGTH_LUPDATE; EL_LUPDATE] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[COND_CASE_EQ; option_DISTINCT] THEN ASM_MESON_TAC[option_DISTINCT]);;

let FLATPAUX_globals_state_rel1 = prove
 (`!reachable (s:(C,FFI)flat_state) t g.
     flat_state_rel reachable s t /\ globals_rel reachable g (flat_state_globals t)
     ==> flat_state_rel reachable (flat_state_globals_fupd (combin_K g) s) t`,
  REWRITE_TAC[flat_state_rel_def; flat_state_INFO.ri_accfupds; K_THM] THEN
  MESON_TAC[]);;

let FLATPAUX_pure_simps =
  [ALL; o_THM; is_pure_def1; find_loc_def; inter_union_empty; find_loc_EVERY_isEmpty;
   EVERY_REVERSE; o_DEF; NOT_EX; DE_MORGAN_THM; flat_elimProof_has_Eval_def;
   dest_GlobalVarInit_def; option_CASE; inter_LN];;

let FLATPAUX_PURE_NORM_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[EVERY_REVERSE]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE FLATPAUX_pure_simps) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;

let FLATPAUX_PURE_DISCH_TAC : tactic =
  REWRITE_TAC[EVERY_REVERSE] THEN REWRITE_TAC FLATPAUX_pure_simps THEN
  RULE_ASSUM_TAC(REWRITE_RULE FLATPAUX_res_inj) THEN
  ASM_REWRITE_TAC FLATPAUX_res_inj THEN NO_TAC;;

let FLATPAUX_PIH_TAC lab n rs : tactic = fun (asl,w as g) ->
  let th0 = REWRITE_RULE[IMP_CONJ] (snd(find (fun (l,_) -> l = lab) asl)) in
  let rec go k th = if k = 0 then th else
    go (k-1) (tryfind (fun (_,a) -> MATCH_MP th a) asl) in
  let th = REWRITE_RULE[IMP_IMP] (SPECL [`reachable:num_set`; rs] (go n th0)) in
  (MP_TAC th THEN ANTS_TAC THENL [FLATPAUX_PURE_DISCH_TAC; STRIP_TAC]) g;;

let FLATPAUX_PURE_UNFOLD_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check FLATPAUX_IS_HYP_EVAL) THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[pair_CASE] THEN
  FLATPAUX_PURE_NORM_TAC;;

let FLATPAUX_is_val_eq th =
  try let l,r = dest_eq(concl th) in is_var r && not (is_var l) &&
        fst(dest_var r) <> "result"
  with Failure _ -> false;;

let FLATPAUX_PURE_FINISH_TAC : tactic =
  TRY(FIRST_ASSUM(CONTR_TAC o REWRITE_RULE FLATPAUX_res_inj)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "result"]) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check FLATPAUX_is_val_eq)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE (HD :: o_DEF :: FLATPAUX_res_simps)) THEN
  ASM_REWRITE_TAC(injectivity "result" :: UNWIND_THM1 :: UNWIND_THM2 :: HD :: o_DEF ::
                  NOT_EX :: EVERY_REVERSE :: v_has_Eval_def :: FLATPAUX_res_simps);;

let FLATPAUX_PURE_NIL_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN FS[flat_evaluate_def] THEN RVEQ_TAC THEN
  FLATPAUX_PURE_FINISH_TAC;;

let FLATPAUX_PURE_ERR_TAC lab : tactic =
  REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_SUBST_RES_TAC THEN
  FLATPAUX_PIH_TAC lab 1 `removed_state:(C,FFI)flat_state` THEN
  FLATPAUX_PURE_FINISH_TAC;;

let FLATPAUX_PURE_CONS_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FLATPAUX_PAIR_TAC `flat_evaluate env (s:(C,FFI)flat_state) [e1]`
    `s1:(C,FFI)flat_state` `r1:(flat_v list,flat_v)result` THEN
  FLATPAUX_PURE_UNFOLD_TAC THEN
  CASES_ON `r1:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[] THENL
   [FLATPAUX_PIH_TAC "ih1" 1 `removed_state:(C,FFI)flat_state` THEN
    FLATPAUX_PAIR_TAC `flat_evaluate env (s1:(C,FFI)flat_state) (CONS e2 es)`
      `s2:(C,FFI)flat_state` `r2:(flat_v list,flat_v)result` THEN
    ASM_REWRITE_TAC[pair_CASE] THEN
    USE_THEN "ih2" (fun ih2 -> FIRST_ASSUM (LABEL_TAC "ih2'" o MATCH_MP ih2)) THEN
    CASES_ON `r2:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_SUBST_RES_TAC THEN
    FLATPAUX_PIH_TAC "ih2'" 1 `removed_state:(C,FFI)flat_state` THEN
    FLATPAUX_SING_TAC THEN FLATPAUX_PURE_FINISH_TAC;
    FLATPAUX_PURE_ERR_TAC "ih1"];;

let FLATPAUX_PURE_RAISE_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FLATPAUX_PURE_NORM_TAC THEN FIRST_ASSUM CONTR_TAC;;

let FLATPAUX_PURE_HANDLE_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FLATPAUX_PAIR_TAC `flat_evaluate env (s:(C,FFI)flat_state) [e]`
    `s1:(C,FFI)flat_state` `r1:(flat_v list,flat_v)result` THEN
  FLATPAUX_PURE_UNFOLD_TAC THEN
  CASES_ON `r1:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[] THENL
   [FLATPAUX_PURE_ERR_TAC "ih1";
    CASES_ON `a:(flat_v)error_result` THEN CAKE_REWRITE_TAC[] THENL
     [DISCH_THEN(K ALL_TAC) THEN
      FLATPAUX_PIH_TAC "ih1" 1 `removed_state:(C,FFI)flat_state` THEN
      FLATPAUX_PURE_FINISH_TAC;
      FLATPAUX_PURE_ERR_TAC "ih1"]];;

let FLATPAUX_PURE_CON_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih1") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FLATPAUX_PAIR_TAC `flat_evaluate env (s:(C,FFI)flat_state) (REVERSE es)`
    `s1:(C,FFI)flat_state` `r1:(flat_v list,flat_v)result` THEN
  FLATPAUX_PURE_UNFOLD_TAC THEN
  CASES_ON `r1:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[] THEN
  FLATPAUX_PURE_ERR_TAC "ih1";;

let FLATPAUX_PURE_VAR_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN FLATPAUX_PURE_UNFOLD_TAC THEN
  CASES_ON `ALOOKUP (flat_environment_v (env:(flat_v)flat_environment)) n` THEN
  CAKE_REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_SUBST_RES_TAC THEN
  FLATPAUX_PURE_FINISH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALOOKUP_MEM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(n,a):varN#flat_v` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[];;

let FLATPAUX_PURE_FUN_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN FLATPAUX_PURE_UNFOLD_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_SUBST_RES_TAC THEN
  FLATPAUX_PURE_FINISH_TAC THEN ASM_REWRITE_TAC[EVERY_MAP];;

let FLATPAUX_RVEQ_TAC : tactic =
  let ok th = try let l,r = dest_eq(concl th) in
                  (is_var r && not (vfree_in r l)) || (is_var l && not (vfree_in l r))
              with Failure _ -> false in
  REPEAT(FIRST_X_ASSUM(fun th ->
    if not (ok th) then failwith "FLATPAUX_RVEQ_TAC" else
    let l,r = dest_eq(concl th) in
    if is_var r && not (vfree_in r l) then SUBST_ALL_TAC (SYM th)
    else SUBST_ALL_TAC th));;

let FLATPAUX_PURE_GLOBALINIT_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  FLATPAUX_RVEQ_TAC THEN
  REWRITE_TAC[list_result_def; injectivity "result"] THEN
  EXISTS_TAC `[Unitv]:flat_v list` THEN
  REWRITE_TAC[ALL; o_THM; v_has_Eval_Unitv] THEN
  MATCH_MP_TAC FLATPAUX_globals_state_rel1 THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FLATPAUX_globals_rel_init_unreachable THEN
  FLATPAUX_EXPAND_REL_TAC THEN ASM_REWRITE_TAC[GSYM IS_NONE_EQ_NONE];;

let FLATPAUX_PURE_APP_TAC : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1")
     (CONJUNCTS_THEN2 (LABEL_TAC "ih_opapp") (LABEL_TAC "ih_force"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CASES_ON `op:flat_op` THEN
  TRY(FLATPAUX_PURE_NORM_TAC THEN FIRST_ASSUM CONTR_TAC THEN NO_TAC) THEN
  FLATPAUX_PAIR_TAC `flat_evaluate env (s:(C,FFI)flat_state) (REVERSE es)`
    `s1:(C,FFI)flat_state` `r1:(flat_v list,flat_v)result` THEN
  FLATPAUX_PURE_UNFOLD_TAC THEN CAKE_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP inter_insert_empty) THEN
  CASES_ON `r1:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[] THENL
   [FLATPAUX_PIH_TAC "ih1" 1 `removed_state:(C,FFI)flat_state` THEN
    REWRITE_TAC (!FLATPAUX_do_app_eqs) THEN DISCH_TAC THEN FLATSEMAUX_SPLIT_TAC THEN
    FLATPAUX_RVEQ_TAC THEN FLATPAUX_PURE_FINISH_TAC THEN FLATPAUX_PURE_GLOBALINIT_TAC;
    FLATPAUX_PURE_ERR_TAC "ih1"];;

let FLATPAUX_PURE_IF_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FLATPAUX_PAIR_TAC `flat_evaluate env (s:(C,FFI)flat_state) [e1]`
    `s1:(C,FFI)flat_state` `r1:(flat_v list,flat_v)result` THEN
  FLATPAUX_PURE_UNFOLD_TAC THEN
  CASES_ON `r1:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[] THENL
   [FLATPAUX_PIH_TAC "ih1" 1 `removed_state:(C,FFI)flat_state` THEN
    CASES_ON `flat_do_if (HD a) e2 e3` THEN CAKE_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN FLATPAUX_SUBST_RES_TAC THEN FLATPAUX_PURE_FINISH_TAC;
      DISCH_TAC THEN FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP do_if_either_or) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      FLATPAUX_PIH_TAC "ih2" 3 `removed_state:(C,FFI)flat_state` THEN
      FLATPAUX_PURE_FINISH_TAC];
    FLATPAUX_PURE_ERR_TAC "ih1"];;

let FLATPAUX_MEM_ALL_SND = prove
 (`!(P:B->bool) (pes:(A#B)list) p e. MEM (p,e) pes /\ ALL P (MAP SND pes) ==> P e`,
  REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN MESON_TAC[SND]);;

let FLATPAUX_PURE_MAT_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FLATPAUX_PAIR_TAC `flat_evaluate env (s:(C,FFI)flat_state) [e]`
    `s1:(C,FFI)flat_state` `r1:(flat_v list,flat_v)result` THEN
  FLATPAUX_PURE_UNFOLD_TAC THEN
  CASES_ON `r1:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[] THENL
   [FLATPAUX_PIH_TAC "ih1" 1 `removed_state:(C,FFI)flat_state` THEN
    FLATPAUX_SING_TAC THEN REWRITE_TAC[HD] THEN
    CASES_ON `pmatch_rows (pes:(flat_pat#flat_exp)list) (s1:(C,FFI)flat_state) y` THEN
    CAKE_REWRITE_TAC[PAIR_EQ] THENL
     [FIRST_ASSUM(MP_TAC o SPECL [`s1:(C,FFI)flat_state`; `y:flat_v`] o
                  MATCH_MP EXISTS_total_pat o check (fun th ->
                    can (term_match [] `EX total_pat (MAP FST (pes:(flat_pat#flat_exp)list))`)
                        (concl th))) THEN
      ASM_REWRITE_TAC[];
      FLATPAUX_SUBST_RES_TAC THEN FLATPAUX_PURE_FINISH_TAC;
      SUBGOAL_THEN `?env1 p1 e1. a' = (env1:(varN#flat_v)list,p1:flat_pat,e1:flat_exp)`
        STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; FIRST_X_ASSUM SUBST_ALL_TAC] THEN
      CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
       [DISCH_TAC THEN
        FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP pmatch_rows_IMP_pmatch) THEN
        FLATPAUX_EXPAND_REL_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[GSYM find_loc_EVERY_isEmpty]) THEN
        ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
          try ASSUME_TAC (BETA_RULE (MATCH_MP FLATPAUX_MEM_ALL_SND
                (CONJ (ASSUME `MEM (p1,e1) (pes:(flat_pat#flat_exp)list)`) th)))
          with Failure _ -> ALL_TAC) ths) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[injectivity "result"]) THEN
        REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check FLATPAUX_is_val_eq)) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN
        SUBGOAL_THEN `ALL (\x. ~v_has_Eval (SND x)) (env1:(varN#flat_v)list)` ASSUME_TAC
        THENL
         [MP_TAC(ISPECL [`s1:(C,FFI)flat_state`; `p1:flat_pat`; `y:flat_v`;
                         `[]:(varN#flat_v)list`; `env1:(varN#flat_v)list`]
                        (CONJUNCT1 pmatch_not_has_Eval)) THEN
          ASM_REWRITE_TAC[ALL; o_DEF] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        FLATPAUX_CHAINR 4 [HD] (fun th -> MP_TAC (REWRITE_RULE[IMP_IMP]
           (SPECL [`reachable:num_set`; `removed_state:(C,FFI)flat_state`] th))) "ih2" THEN
        ANTS_TAC THENL
         [REWRITE_TAC (flat_environment_INFO.ri_accfupds :: K_THM :: ALL_APPEND ::
                       FLATPAUX_pure_simps) THEN
          RULE_ASSUM_TAC(REWRITE_RULE FLATPAUX_pure_simps) THEN ASM_REWRITE_TAC[];
          STRIP_TAC THEN FLATPAUX_PURE_FINISH_TAC];
        FLATPAUX_SUBST_RES_TAC THEN FLATPAUX_PURE_FINISH_TAC]];
    FLATPAUX_PURE_ERR_TAC "ih1"];;

let FLATPAUX_PURE_LET_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FLATPAUX_PAIR_TAC `flat_evaluate env (s:(C,FFI)flat_state) [e1]`
    `s1:(C,FFI)flat_state` `r1:(flat_v list,flat_v)result` THEN
  FLATPAUX_PURE_UNFOLD_TAC THEN
  CASES_ON `r1:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[] THENL
   [FLATPAUX_PIH_TAC "ih1" 1 `removed_state:(C,FFI)flat_state` THEN
    FLATPAUX_SING_TAC THEN REWRITE_TAC[HD] THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "result"]) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check FLATPAUX_is_val_eq)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN
    FLATPAUX_CHAINR 2 [HD] (fun th -> MP_TAC (REWRITE_RULE[IMP_IMP]
           (SPECL [`reachable:num_set`; `removed_state:(C,FFI)flat_state`] th))) "ih2" THEN
    ANTS_TAC THENL
     [REWRITE_TAC (flat_environment_INFO.ri_accfupds :: FLATPAUX_pure_simps) THEN
      CASES_ON `n:varN option` THEN
      REWRITE_TAC[opt_bind_def; option_CASE; ALL] THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN FLATPAUX_PURE_FINISH_TAC];
    FLATPAUX_PURE_ERR_TAC "ih1"];;

let FLATPAUX_PURE_LETREC_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih1") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FLATPAUX_PURE_UNFOLD_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [DISCH_TAC THEN
    FLATPAUX_CHAINR 2 [] (fun th -> MP_TAC (REWRITE_RULE[IMP_IMP]
           (SPECL [`reachable:num_set`; `removed_state:(C,FFI)flat_state`] th))) "ih1" THEN
    ANTS_TAC THENL
     [REWRITE_TAC (flat_environment_INFO.ri_accfupds :: K_THM :: FLATPAUX_pure_simps) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`funs:(varN#varN#flat_exp)list`; `env:(flat_v)flat_environment`;
                     `flat_environment_v (env:(flat_v)flat_environment)`;
                     `(:num)`] FLATPAUX_build_rec_env_facts) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[EVERY_MAP; o_DEF]) THEN
      ASM_SIMP_TAC[EVERY_MAP; o_DEF; SUBSET_UNIV];
      STRIP_TAC THEN FLATPAUX_PURE_FINISH_TAC];
    FLATPAUX_SUBST_RES_TAC THEN FLATPAUX_PURE_FINISH_TAC];;

(* EVALUATE MUTUAL INDUCTION: the case of removed (pure, unreachable) code *)

let evaluate_flat_state_rel_lemma = prove
 (`!env (state:(C,FFI)flat_state) exprL new_state result (reachable:num_set)
    removed_state.
     flat_evaluate env state exprL = (new_state,result) /\
     ALL flat_elim_is_pure exprL /\
     ALL ((~) o v_has_Eval o SND) (flat_environment_v env) /\
     ALL ((~) o has_Eval) exprL /\
     ALL (\e. sptree_inter (find_loc e) reachable = LN) exprL /\
     flat_state_rel reachable state removed_state /\
     ~(result = Rerr (Rabort Rtype_error))
     ==> ?values. flat_state_rel reachable new_state removed_state /\
                  result = Rval values /\
                  ALL ((~) o v_has_Eval) values`,
  MATCH_MP_TAC FLATPAUX_evaluate_exp_ind THEN REPEAT CONJ_TAC THENL
   [FLATPAUX_PURE_NIL_TAC; FLATPAUX_PURE_CONS_TAC; FLATPAUX_PURE_NIL_TAC;
    FLATPAUX_PURE_RAISE_TAC; FLATPAUX_PURE_HANDLE_TAC; FLATPAUX_PURE_CON_TAC;
    FLATPAUX_PURE_CON_TAC; FLATPAUX_PURE_VAR_TAC; FLATPAUX_PURE_FUN_TAC;
    FLATPAUX_PURE_APP_TAC; FLATPAUX_PURE_IF_TAC; FLATPAUX_PURE_MAT_TAC;
    FLATPAUX_PURE_LET_TAC; FLATPAUX_PURE_LETREC_TAC]);;

(* EVALUATE SPECIALISATION *)

let evaluate_sing_notKeep_flat_state_rel = prove
 (`!env (state:(C,FFI)flat_state) exprL new_state result expr (reachable:num_set)
    removed_state.
     flat_evaluate (flat_environment_v_fupd (combin_K []) env) state exprL =
       (new_state,result) /\
     exprL = [expr] /\
     ~has_Eval expr /\
     ~keep reachable expr /\
     flat_state_rel reachable state removed_state /\
     ~(result = Rerr (Rabort Rtype_error))
     ==> flat_state_rel reachable new_state removed_state /\
         ?value:flat_v. result = Rval [value]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[keep_def; COND_EXPAND; DE_MORGAN_THM]) THEN
  MP_TAC(ISPECL [`flat_environment_v_fupd (combin_K []) (env:(flat_v)flat_environment)`;
                 `state:(C,FFI)flat_state`; `[expr]:flat_exp list`;
                 `new_state:(C,FFI)flat_state`; `result:(flat_v list,flat_v)result`;
                 `reachable:num_set`; `removed_state:(C,FFI)flat_state`]
                evaluate_flat_state_rel_lemma) THEN
  ASM_REWRITE_TAC[flat_environment_INFO.ri_accfupds; K_THM; ALL; o_THM] THEN

  STRIP_TAC THEN ASM_REWRITE_TAC[injectivity "result"] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP flat_evaluate_sing) THEN MESON_TAC[]);;

(* MAIN PROOFS *)

let FLATPAUX_IS_REMOVE_EQ th =
  can (term_match [] `remove_unreachable (r:num_set) (d:flat_exp list) = x`) (concl th);;

let flat_decs_removal_lemma = prove
 (`!(state:(C,FFI)flat_state) decs new_state result (reachable:num_set) removed_decs
    removed_state.
     flat_evaluate_decs state decs = (new_state,result) /\
     ~(result = SOME (Rabort Rtype_error)) /\
     remove_unreachable reachable decs = removed_decs /\
     flat_state_rel reachable state removed_state /\
     ALL ((~) o has_Eval_dec) decs /\
     decs_closed reachable decs
     ==> ?new_removed_state.
           flat_state_ffi new_removed_state = flat_state_ffi new_state /\
           flat_evaluate_decs removed_state removed_decs = (new_removed_state,result)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check FLATPAUX_IS_REMOVE_EQ) THEN
  REWRITE_TAC[remove_unreachable_def; FILTER] THENL
   [UNDISCH_TAC `flat_evaluate_decs (state:(C,FFI)flat_state) [] = (new_state,result)` THEN
  REWRITE_TAC[flat_evaluate_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  EXISTS_TAC `removed_state:(C,FFI)flat_state` THEN
  ASM_MESON_TAC[flat_state_rel_def];
    FIRST_X_ASSUM(LABEL_TAC "ih" o check (is_forall o concl)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP decs_closed_reduce) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP decs_closed_reduce_HD) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; o_THM]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  FLATPAUX_PAIR_TAC `evaluate_dec (state:(C,FFI)flat_state) h`
    `s1:(C,FFI)flat_state` `r1:((flat_v)error_result)option` THEN
  UNDISCH_TAC `flat_evaluate_decs (state:(C,FFI)flat_state) (CONS h t) = (new_state,result)` THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[pair_CASE] THEN
  ASM_CASES_TAC `keep (reachable:num_set) h` THEN ASM_REWRITE_TAC[] THENL
     [ONCE_REWRITE_TAC[flat_evaluate_def] THEN
  CASES_ON `r1:((flat_v)error_result)option` THEN CAKE_REWRITE_TAC[] THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`state:(C,FFI)flat_state`; `h:flat_exp`; `s1:(C,FFI)flat_state`;
                   `NONE:((flat_v)error_result)option`; `reachable:num_set`;
                   `removed_state:(C,FFI)flat_state`] evaluate_dec_flat_state_rel) THEN
    ASM_REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[pair_CASE] THEN CAKE_REWRITE_TAC[] THEN
    REMOVE_THEN "ih" (MP_TAC o SPECL [`s1:(C,FFI)flat_state`; `new_state:(C,FFI)flat_state`;
      `result:((flat_v)error_result)option`; `reachable:num_set`;
      `FILTER (keep (reachable:num_set)) t`; `new_removed_state:(C,FFI)flat_state`]) THEN
    ASM_REWRITE_TAC[remove_unreachable_def];
    REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    MP_TAC(ISPECL [`state:(C,FFI)flat_state`; `h:flat_exp`; `s1:(C,FFI)flat_state`;
                   `SOME a:((flat_v)error_result)option`; `reachable:num_set`;
                   `removed_state:(C,FFI)flat_state`] evaluate_dec_flat_state_rel) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[pair_CASE] THEN CAKE_REWRITE_TAC[] THEN
    EXISTS_TAC `new_removed_state:(C,FFI)flat_state` THEN
    ASM_MESON_TAC[flat_state_rel_def]];
      FLATPAUX_PAIR_TAC `flat_evaluate (flat_environment_REC []) (state:(C,FFI)flat_state) [h]`
    `s2:(C,FFI)flat_state` `r2:(flat_v list,flat_v)result` THEN
  UNDISCH_TAC `evaluate_dec (state:(C,FFI)flat_state) h = (s1,r1)` THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPECL [`flat_environment_REC []:(flat_v)flat_environment`;
                 `state:(C,FFI)flat_state`; `[h]:flat_exp list`;
                 `s2:(C,FFI)flat_state`; `r2:(flat_v list,flat_v)result`; `h:flat_exp`;
                 `reachable:num_set`; `removed_state:(C,FFI)flat_state`]
                evaluate_sing_notKeep_flat_state_rel) THEN
  REWRITE_TAC[flat_environment_INFO.ri_fupds; K_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[has_Eval_dec_def]) THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `r2:(flat_v list,flat_v)result` THEN CAKE_REWRITE_TAC[] THENL
   [STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    CAKE_REWRITE_TAC[] THENL
     [DISCH_TAC THEN
      REMOVE_THEN "ih" (MP_TAC o SPECL [`s2:(C,FFI)flat_state`;
        `new_state:(C,FFI)flat_state`; `result:((flat_v)error_result)option`;
        `reachable:num_set`; `FILTER (keep (reachable:num_set)) t`;
        `removed_state:(C,FFI)flat_state`]) THEN
      ASM_REWRITE_TAC[remove_unreachable_def];
      REWRITE_TAC[PAIR_EQ] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
      ASM_MESON_TAC[]];
    DISCH_THEN SUBST_ALL_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    CAKE_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC]]]);;

let flat_removal_thm = prove
 (`!(ffi:(FFI)ffi_state) k decs (new_state:(C,FFI)flat_state) result roots tree
    reachable removed_decs.
     flat_evaluate_decs (flat_initial_state ffi k ec) decs = (new_state,result) /\
     ~(result = SOME (Rabort Rtype_error)) /\
     (roots,tree) = analyse_code decs /\
     reachable = closure_spt roots tree /\
     ~EX has_Eval_dec decs /\
     remove_unreachable reachable decs = removed_decs
     ==> ?s. flat_state_ffi s = flat_state_ffi new_state /\
             flat_evaluate_decs (flat_initial_state ffi k ec) removed_decs =
               (s,result)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`flat_initial_state (ffi:(FFI)ffi_state) k (ec:(C)install_config)`;
                 `decs:flat_exp list`; `new_state:(C,FFI)flat_state`;
                 `result:((flat_v)error_result)option`; `reachable:num_set`;
                 `removed_decs:flat_exp list`;
                 `flat_initial_state (ffi:(FFI)ffi_state) k (ec:(C)install_config)`]
                flat_decs_removal_lemma) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[flat_state_rel_def; globals_rel_def; flat_initial_state_def;
                flat_state_INFO.ri_accessors; LENGTH; find_refs_globals_def;
                domain_def; EMPTY_SUBSET; ALL; ARITH_RULE `~(n < 0)`];
    UNDISCH_TAC `~EX has_Eval_dec decs` THEN REWRITE_TAC[NOT_EX; o_DEF];
    MP_TAC(ISPECL [`tree:(num_set)spt`; `roots:num_set`] closure_spt_thm) THEN
    ASM_REWRITE_TAC[decs_closed_def] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      can (term_match [] `(roots:num_set,tree:(num_set)spt) = x`) (concl th))) THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `a:num` THEN DISCH_TAC THEN EXISTS_TAC `a:num` THEN
      ASM_REWRITE_TAC[is_reachable_def; RTC_REFL];
      REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
        (X_CHOOSE_THEN `n0:num` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      EXISTS_TAC `n0:num` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[is_reachable_def; RTC_TRANS]]]);;

let flat_remove_eval_sim = prove
 (`flat_eval_sim (ffi:(FFI)ffi_state) ds1 (remove_flat_prog ds1) (ec:(C)install_config)
     ec (\d1 d2. d2 = remove_flat_prog d1) F`,
  REWRITE_TAC[flat_eval_sim_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES] THEN
  REWRITE_TAC[remove_flat_prog_def] THEN COND_CASES_TAC THENL
   [MAP_EVERY EXISTS_TAC [`res1:((flat_v)error_result)option`; `s2:(C,FFI)flat_state`] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r t. analyse_code ds1 = (r:num_set,t:(num_set)spt)` STRIP_ASSUME_TAC
  THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPECL [`ffi:(FFI)ffi_state`; `k:num`; `ds1:flat_exp list`;
                 `s2:(C,FFI)flat_state`; `res1:((flat_v)error_result)option`;
                 `r:num_set`; `t:(num_set)spt`; `closure_spt r (t:(num_set)spt)`;
                 `remove_unreachable (closure_spt r (t:(num_set)spt)) ds1`]
                (INST [`ec:(C)install_config`,`ec:(C)install_config`] flat_removal_thm)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:(C,FFI)flat_state` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`res1:((flat_v)error_result)option`; `s:(C,FFI)flat_state`] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let flat_remove_semantics =
  REWRITE_RULE[] (BETA_RULE (MATCH_MP (REWRITE_RULE[GSYM IMP_IMP] flat_IMP_semantics_eq)
                                      flat_remove_eval_sim));;

(* syntactic results *)

(* HOL4 [local] *)
let elist_globals_filter = prove
 (`!(P:flat_exp->bool) ds.
     flat_elist_globals ds = EMPTY_BAG
     ==> flat_elist_globals (FILTER P ds) = EMPTY_BAG`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[FILTER; flat_set_globals_def; BAG_UNION_EMPTY] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[flat_set_globals_def; BAG_UNION_EMPTY]);;

(* HOL4 [local] *)
let esgc_free_filter = prove
 (`!(P:flat_exp->bool) ds. ALL flat_esgc_free ds ==> ALL flat_esgc_free (FILTER P ds)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; ALL] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[ALL]);;

(* HOL4 [local] *)
let elist_globals_filter_SUB_BAG = prove
 (`!(P:flat_exp->bool) ds.
     SUB_BAG (flat_elist_globals (FILTER P ds)) (flat_elist_globals ds)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; SUB_BAG_REFL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[flat_set_globals_def] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "SUB_BAG" with Failure _ -> false))
        (concl th))) THEN
  REWRITE_TAC[SUB_BAG_LEQ; BAG_UNION] THEN MESON_TAC[LE_ADD_LCANCEL; LE_ADD; LE_TRANS;
    ADD_SYM]);;

(* the program that remove_flat_prog keeps is a FILTER of the program *)

let FLATPAUX_remove_flat_prog_FILTER = prove
 (`!ds. ?P. remove_flat_prog ds = FILTER P ds`,
  GEN_TAC THEN REWRITE_TAC[remove_flat_prog_def] THEN COND_CASES_TAC THENL
   [EXISTS_TAC `\x:flat_exp. T` THEN
    SUBGOAL_THEN `!l:flat_exp list. FILTER (\x. T) l = l` (fun th -> REWRITE_TAC[th]) THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER];
    SUBGOAL_THEN `?r t. analyse_code ds = (r:num_set,t:(num_set)spt)` STRIP_ASSUME_TAC
    THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
    ASM_REWRITE_TAC[pair_CASE] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[remove_unreachable_def] THEN MESON_TAC[]]);;

let remove_flat_prog_elist_globals_eq_empty = prove
 (`!ds. flat_elist_globals ds = EMPTY_BAG
        ==> flat_elist_globals (remove_flat_prog ds) = EMPTY_BAG`,
  MESON_TAC[FLATPAUX_remove_flat_prog_FILTER; elist_globals_filter]);;

let remove_flat_prog_esgc_free = prove
 (`!ds. ALL flat_esgc_free ds ==> ALL flat_esgc_free (remove_flat_prog ds)`,
  MESON_TAC[FLATPAUX_remove_flat_prog_FILTER; esgc_free_filter]);;

let remove_flat_prog_sub_bag = prove
 (`!ds. SUB_BAG (flat_elist_globals (remove_flat_prog ds)) (flat_elist_globals ds)`,
  MESON_TAC[FLATPAUX_remove_flat_prog_FILTER; elist_globals_filter_SUB_BAG]);;

let remove_flat_prog_distinct_globals = prove
 (`!ds. BAG_ALL_DISTINCT (flat_elist_globals ds)
        ==> BAG_ALL_DISTINCT (flat_elist_globals (remove_flat_prog ds))`,
  MESON_TAC[remove_flat_prog_sub_bag; BAG_ALL_DISTINCT_SUB_BAG]);;
