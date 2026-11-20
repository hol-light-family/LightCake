(* ========================================================================= *)
(* bvi_tmcProof: port of HOL4 compiler/backend/proofs/bvi_tmcProofScript.sml *)
(* (CakeML v3479).  Correctness proof for bvi_tmc (tail recursion modulo     *)
(* cons).  BVITMCAUX_ names are local helpers (not HOL4 names).              *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/bvi_tmc.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;

type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - HOL4 Overload in_ns_3 n = (n MOD bvl_to_bvi_namespaces = 3) is written  *)
(*   out where it is used.                                                   *)
(* - HOL4 val s = s : (num # 'c, 'ffi) bviSem$state: the source states have  *)
(*   the type (num#C,FFI)bvi_state, the target states (C,FFI)bvi_state.      *)
(* - HOL4 refs<|k |-> v|> is refs |+ (k,v), l<|n|> is EL n l, f SUBMAP f'   *)
(*   is f SUBMAP f', compile_exp is bvi_tmc_compile_exp, compile_each is     *)
(*   bvi_tmc_compile_each, compile_prog is bvi_tmc_compile_prog.             *)
(* - The definitions keep the types HOL4 infers (some are polymorphic).      *)

let bvi_tmcProof_v_rel_rules,bvi_tmcProof_v_rel_ind,
    bvi_tmcProof_v_rel_cases,bvi_tmcProof_v_rel_strongind = cake_inductive
 `(!f i. bvi_tmcProof_v_rel f (bvl_Number i) (bvl_Number i)) /\
  (!f w. bvi_tmcProof_v_rel f (bvl_Word64 w) (bvl_Word64 w)) /\
  (!f n xs ys.
     ALL2 (bvi_tmcProof_v_rel f) xs ys ==>
     bvi_tmcProof_v_rel f (bvl_Block n xs) (bvl_Block n ys)) /\
  (!f n. bvi_tmcProof_v_rel f (bvl_CodePtr n) (bvl_CodePtr n)) /\
  (!(f:(num,num)fmap) n m b.
     FLOOKUP f n = SOME m ==>
     bvi_tmcProof_v_rel f (bvl_RefPtr b n) (bvl_RefPtr b m))`;;

let bvi_tmcProof_v_rel_Number = el 0 (CONJUNCTS bvi_tmcProof_v_rel_rules);;
let bvi_tmcProof_v_rel_Word64 = el 1 (CONJUNCTS bvi_tmcProof_v_rel_rules);;
let bvi_tmcProof_v_rel_Block = el 2 (CONJUNCTS bvi_tmcProof_v_rel_rules);;
let bvi_tmcProof_v_rel_CodePtr = el 3 (CONJUNCTS bvi_tmcProof_v_rel_rules);;
let bvi_tmcProof_v_rel_RefPtr = el 4 (CONJUNCTS bvi_tmcProof_v_rel_rules);;

let bvi_tmcProof_ref_rel_rules,bvi_tmcProof_ref_rel_ind,
    bvi_tmcProof_ref_rel_cases,bvi_tmcProof_ref_rel_strongind = cake_inductive
 `(!f b bs. bvi_tmcProof_ref_rel f (bvl_ByteArray b bs) (bvl_ByteArray b bs)) /\
  (!f xs ys.
     ALL2 (bvi_tmcProof_v_rel f) xs ys ==>
     bvi_tmcProof_ref_rel f (bvl_ValueArray xs) (bvl_ValueArray ys)) /\
  (!f x y tm.
     bvi_tmcProof_v_rel f x y ==>
     bvi_tmcProof_ref_rel f (bvl_Thunk tm x) (bvl_Thunk tm y))`;;

let bvi_tmcProof_ref_rel_ByteArray = el 0 (CONJUNCTS bvi_tmcProof_ref_rel_rules);;
let bvi_tmcProof_ref_rel_ValueArray = el 1 (CONJUNCTS bvi_tmcProof_ref_rel_rules);;
let bvi_tmcProof_ref_rel_Thunk = el 2 (CONJUNCTS bvi_tmcProof_ref_rel_rules);;

let bvi_tmcProof_env_rel_def = cake_def
 `bvi_tmcProof_env_rel opt f env1 env2 <=>
    ?xs ys.
      env2 = APPEND xs ys /\
      ALL2 (bvi_tmcProof_v_rel f) env1 xs /\
      (opt ==>
       LENGTH ys = 2 /\
       ?hole_ptr hole_idx.
         EL 0 ys = bvl_RefPtr F hole_ptr /\
         EL 1 ys = bvl_Number hole_idx /\
         small_enough_int hole_idx)`;;

(* HOL4 line 55 *)
let no_mutcons_op_def = cake_def
  `no_mutcons_op op <=> !tag i. ~(op = MemOp (MutCons tag i))`;;

(* HOL4 line 59 [simp] (Termination: measure exp_size; the dest of LetCall *)
(* is d2: one quotation types a variable once) *)
let no_mutcons_def = cake_def_wf
  `measure bvi_exp_size`
  TERM_TAC
  `(no_mutcons (bvi_Var n) <=> T) /\
   (no_mutcons (bvi_If x1 x2 x3) <=> no_mutcons x1 /\ no_mutcons x2 /\ no_mutcons x3) /\
   (no_mutcons (bvi_Let xs x) <=> ALL no_mutcons xs /\ no_mutcons x) /\
   (no_mutcons (bvi_Raise x) <=> no_mutcons x) /\
   (no_mutcons (bvi_Tick x) <=> no_mutcons x) /\
   (no_mutcons (bvi_Call ticks dest xs handler) <=>
      ALL no_mutcons xs /\ (match handler with NONE -> T | SOME x -> no_mutcons x)) /\
   (no_mutcons (bvi_Force loc n) <=> T) /\
   (no_mutcons (LetCall rets ticks d2 xs y) <=> ALL no_mutcons xs /\ no_mutcons y) /\
   (no_mutcons (bvi_Return xs) <=> ALL no_mutcons xs) /\
   (no_mutcons (bvi_Op op xs) <=> no_mutcons_op op /\ ALL no_mutcons xs)`;;

let no_mutcons_ind = cake_ind "no_mutcons";;

let _ = cake_add_simps [no_mutcons_def];;

let bvi_tmcProof_code_rel_def = cake_def
 `bvi_tmcProof_code_rel c1 c2 <=>
    !loc arity exp.
      lookup loc c1 = SOME (arity,exp) ==>
      no_mutcons exp /\
      ?n. (bvi_tmc_compile_exp loc n arity exp = NONE ==>
           lookup loc c2 = SOME (arity,exp)) /\
          !wrap work.
            bvi_tmc_compile_exp loc n arity exp = SOME (wrap,work) ==>
            lookup loc c2 = SOME (arity,wrap) /\
            lookup n c2 = SOME (arity + 2,work)`;;

let bvi_tmcProof_code_rel_domain = prove
 (`!c1 c2. bvi_tmcProof_code_rel c1 c2 ==> domain c1 SUBSET domain c2`,
  REWRITE_TAC[bvi_tmcProof_code_rel_def; SUBSET; domain_lookup] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `v:num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `exp:bvi_exp`
    SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `arity:num`; `exp:bvi_exp`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `bvi_tmc_compile_exp x n arity exp = NONE` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[cases "option"]
    `~(x:(bvi_exp#bvi_exp)option = NONE) ==> ?y. x = SOME y`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:bvi_exp#bvi_exp` MP_TAC) THEN
  MP_TAC(ISPEC `y:bvi_exp#bvi_exp` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 108 *)
let bvi_tmcProof_free_names_def = cake_def
  `bvi_tmcProof_free_names n (name:num) <=> !k. ~(n + bvl_to_bvi_namespaces * k = name)`;;

let bvi_tmcProof_namespace_rel_def = cake_def
 `bvi_tmcProof_namespace_rel (c1:A spt) (c2:A spt) <=>
    (!n. n IN domain c2 /\ bvl_num_stubs <= n ==>
         if n MOD bvl_to_bvi_namespaces = 3 then ~(n IN domain c1)
         else n IN domain c1) /\
    (!n. n IN domain c1 /\ bvl_num_stubs <= n ==>
         ~(n MOD bvl_to_bvi_namespaces = 3)) /\
    (!n. n IN domain c2 /\ n < bvl_num_stubs ==> n IN domain c1)`;;

(* This should say: expression in prog satisfies no-mutblock property *)
let bvi_tmcProof_input_condition_def = cake_def
 `bvi_tmcProof_input_condition next (prog:(num#A#bvi_exp)list) <=>
    ALL (bvi_tmcProof_free_names next o FST) prog /\
    ALL (no_mutcons o SND o SND) prog /\
    ALL_DISTINCT (MAP FST prog) /\
    ALL ((~) o (\n. n MOD bvl_to_bvi_namespaces = 3) o FST)
        (FILTER ((<=) bvl_num_stubs o FST) prog) /\
    bvl_num_stubs <= next /\ next MOD bvl_to_bvi_namespaces = 3`;;

let state_ref_rel_def = cake_def
 `state_ref_rel f (s_refs:(num,(bvl_v)bvl_ref)fmap)
                  (t_refs:(num,(bvl_v)bvl_ref)fmap) <=>
    FDOM f = FDOM s_refs /\
    !i v. FLOOKUP s_refs i = SOME v ==>
          ?j w. FLOOKUP f i = SOME j /\ bvi_tmcProof_ref_rel f v w /\
                FLOOKUP t_refs j = SOME w`;;

let fmap_inj_def = cake_def
 `fmap_inj (f:(num,num)fmap) <=>
    !p1 p2 q. FLOOKUP f p1 = SOME q /\ FLOOKUP f p2 = SOME q ==> p1 = p2`;;

let fmap_inj_FEMPTY = prove
 (`fmap_inj FEMPTY`,
  REWRITE_TAC[fmap_inj_def; FLOOKUP_EMPTY; option_DISTINCT]);;
let _ = cake_add_simps [fmap_inj_FEMPTY];;

let fmap_inj_update = prove
 (`!f k v. fmap_inj f /\ ~(v IN FRANGE f) ==> fmap_inj (f |+ (k,v))`,
  REWRITE_TAC[fmap_inj_def; FLOOKUP_UPDATE; FRANGE_FLOOKUP] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THEN ASM_MESON_TAC[]);;

let bvi_tmcProof_state_rel_def = cake_def
 `bvi_tmcProof_state_rel f (s:(num#C,FFI)bvi_state) (t:(C,FFI)bvi_state) <=>
    state_ref_rel f (bvi_state_refs s) (bvi_state_refs t) /\
    bvi_state_clock t = bvi_state_clock s /\
    OPTREL (\p p'. FLOOKUP f p = SOME p') (bvi_state_global s)
           (bvi_state_global t) /\
    bvi_state_ffi t = bvi_state_ffi s /\
    bvi_state_compile_oracle t =
      state_co bvi_tmc_compile_each (bvi_state_compile_oracle s) /\
    bvi_state_compile s = state_cc bvi_tmc_compile_each (bvi_state_compile t) /\
    bvi_tmcProof_code_rel (bvi_state_code s) (bvi_state_code t) /\
    bvi_tmcProof_namespace_rel (bvi_state_code s) (bvi_state_code t) /\
    (!n. let ((next,cfg),prog) = bvi_state_compile_oracle s n in
           bvi_tmcProof_input_condition next prog) /\
    (!n. n IN domain (bvi_state_code t) /\ n MOD bvl_to_bvi_namespaces = 3 ==>
         n < FST (FST (bvi_state_compile_oracle s 0))) /\
    fmap_inj f`;;

(* Structural facts about compile_each and the namespace allocation.       *)
(* These follow bvi_tailrecProof; they only depend on the recursion shape  *)
(* of compile_each (NONE keeps an entry, SOME emits wrapper + worker).     *)

(* HOL4 [local] *)
let bvi_tmcProof_more_free_names = prove
 (`bvi_tmcProof_free_names n name ==>
   bvi_tmcProof_free_names (n + bvl_to_bvi_namespaces) name`,
  REWRITE_TAC[bvi_tmcProof_free_names_def; bvl_to_bvi_namespaces_def] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `k + 1`) THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

(* HOL4 [local] *)
let bvi_tmcProof_is_free_name = prove
 (`bvi_tmcProof_free_names n name ==> ~(n = name)`,
  REWRITE_TAC[bvi_tmcProof_free_names_def] THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

(* HOL4 [local] *)
let bvi_tmcProof_EVERY_free_names_SUCSUC = prove
 (`!xs:(num#A)list.
     ALL (bvi_tmcProof_free_names n o FST) xs ==>
     ALL (bvi_tmcProof_free_names (n + bvl_to_bvi_namespaces) o FST) xs`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[ALL; o_THM; bvi_tmcProof_more_free_names]);;

(* HOL4 [local] *)
let bvi_tmcProof_EVERY_free_names_thm = prove
 (`ALL (bvi_tmcProof_free_names next o FST) (prog:(num#A)list) /\
   lookup loc (fromAList prog) = SOME x ==>
   bvi_tmcProof_free_names next loc`,
  REWRITE_TAC[lookup_fromAList; GSYM ALL_MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(loc,x):num#A` o check (is_forall o concl)) THEN
  ASM_SIMP_TAC[ALOOKUP_MEM; o_THM; FST]);;

(* HOL4 [local,simp] *)
let free_names_mult_F = prove
 (`bvi_tmcProof_free_names n (n + k * bvl_to_bvi_namespaces) <=> F`,
  REWRITE_TAC[bvi_tmcProof_free_names_def; NOT_FORALL_THM] THEN
  EXISTS_TAC `k:num` THEN REWRITE_TAC[MULT_SYM]);;

(* HOL4 [local,simp] *)
let free_names_refl_F = prove
 (`bvi_tmcProof_free_names n n <=> F`,
  REWRITE_TAC[bvi_tmcProof_free_names_def; NOT_FORALL_THM] THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

(* HOL4 [local,simp] *)
let free_names_succ_F = prove
 (`bvi_tmcProof_free_names n
     (n + (bvl_to_bvi_namespaces + k * bvl_to_bvi_namespaces)) <=> F`,
  REWRITE_TAC[bvi_tmcProof_free_names_def; NOT_FORALL_THM] THEN
  EXISTS_TAC `k + 1` THEN ARITH_TAC);;
let _ = cake_add_simps [free_names_mult_F; free_names_refl_F; free_names_succ_F];;

(* HOL4 [local] *)
let rewrite_wrapper_NONE_irrel = prove
 (`!loc lo1 n exp lo2.
     rewrite_wrapper loc lo1 n exp = NONE ==> rewrite_wrapper loc lo2 n exp = NONE`,
  MATCH_MP_TAC rewrite_wrapper_ind THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[rewrite_wrapper_def; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN
  GVS[option_case_eq; pair_case_eq; case_eq "call_block"; OPTION_MAP_EQ_NONE]);;

(* HOL4 [local] *)
let bvi_tmcProof_compile_exp_next_addr = prove
 (`bvi_tmc_compile_exp loc next args exp = NONE ==>
   bvi_tmc_compile_exp loc (next + bvl_to_bvi_namespaces) args exp = NONE`,
  REWRITE_TAC[bvi_tmc_compile_exp_def; LET_DEF; LET_END_DEF; option_case_eq;
              option_DISTINCT] THEN
  MESON_TAC[rewrite_wrapper_NONE_irrel]);;

(* HOL4 [local] *)
let compile_exp_SOME_irrel = prove
 (`bvi_tmc_compile_exp loc next args exp = SOME w ==>
   ?w'. bvi_tmc_compile_exp loc next2 args exp = SOME w'`,
  REWRITE_TAC[bvi_tmc_compile_exp_def; LET_DEF; LET_END_DEF; option_case_eq;
              option_DISTINCT] THEN
  MESON_TAC[rewrite_wrapper_NONE_irrel; cases "option"]);;

(* the cons case of compile_each: split on compile_exp, then on the pairs *)
let BVITMCAUX_EACH_TAC : tactic =
  REWRITE_TAC[bvi_tmc_compile_each_def] THEN
  CASES_ON `bvi_tmc_compile_exp loc next arity exp` THEN FS[] THEN
  REPEAT PAIRARG_TAC THEN FS[];;

let bvi_tmcProof_compile_each_LENGTH = prove
 (`!n prog. LENGTH (SND (bvi_tmc_compile_each n prog)) >= LENGTH prog`,
  MATCH_MP_TAC bvi_tmc_compile_each_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[bvi_tmc_compile_each_def; LENGTH; SND] THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN BVITMCAUX_EACH_TAC THEN ASM_ARITH_TAC);;

let bvi_tmcProof_compile_each_next_mono = prove
 (`!n xs n1 ys. bvi_tmc_compile_each n xs = (n1,ys) ==>
                ?k. n1 = n + bvl_to_bvi_namespaces * k`,
  MATCH_MP_TAC bvi_tmc_compile_each_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[bvi_tmc_compile_each_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `0` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  BVITMCAUX_EACH_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN RES_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[];
    EXISTS_TAC `k + 1` THEN REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN
    ARITH_TAC]);;

let bvi_tmcProof_compile_prog_next_mono = prove
 (`!b n xs n1 ys. bvi_tmc_compile_prog b n xs = (n1,ys) ==>
                  ?k. n1 = n + bvl_to_bvi_namespaces * k`,
  REPEAT GEN_TAC THEN CASES_ON `b:bool` THEN
  REWRITE_TAC[bvi_tmc_compile_prog_def; PAIR_EQ] THENL
   [MESON_TAC[bvi_tmcProof_compile_each_next_mono];
    STRIP_TAC THEN EXISTS_TAC `0` THEN ASM_ARITH_TAC]);;

let bvi_tmcProof_compile_each_MEM = prove
 (`bvi_tmc_compile_each n xs = (n1,ys) /\ MEM e (MAP FST ys) ==>
   MEM e (MAP FST xs) \/
   (n <= e /\ e < n1 /\ (?k. e = n + k * bvl_to_bvi_namespaces))`,
  SUBGOAL_THEN
   `!n xs n1 ys e.
      bvi_tmc_compile_each n xs = (n1,ys) /\ MEM e (MAP FST ys) ==>
      MEM e (MAP FST xs) \/
      (n <= e /\ e < n1 /\ (?k. e = n + k * bvl_to_bvi_namespaces))`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC bvi_tmc_compile_each_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[bvi_tmc_compile_each_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    RVEQ_TAC THEN FS[MAP; MEM]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  BVITMCAUX_EACH_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN FS[MAP; MEM] THENL
   [FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(fun mem -> MP_TAC (MATCH_MP ih mem))) THEN
    MESON_TAC[];
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvi_tmcProof_compile_each_next_mono) THEN
    DISJ2_TAC THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN ARITH_TAC;
      EXISTS_TAC `0` THEN ARITH_TAC];
    FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(fun mem -> MP_TAC (MATCH_MP ih mem))) THEN
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[];
      DISJ2_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC; ASM_ARITH_TAC;
        EXISTS_TAC `k + 1` THEN ASM_REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN
        ARITH_TAC]]]);;

let bvi_tmcProof_compile_prog_MEM = prove
 (`bvi_tmc_compile_prog b n xs = (n1,ys) /\ MEM e (MAP FST ys) ==>
   MEM e (MAP FST xs) \/
   (n <= e /\ e < n1 /\ (?k. e = n + k * bvl_to_bvi_namespaces))`,
  REWRITE_TAC[bvi_tmc_compile_prog_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_MESON_TAC[bvi_tmcProof_compile_each_MEM]);;

(* HOL4 [local] *)
let bvi_tmcProof_compile_each_intro = prove
 (`!xs n ys n1 name.
     ~MEM name (MAP FST xs) /\ bvi_tmcProof_free_names n name /\
     bvi_tmc_compile_each n xs = (n1,ys) ==>
     ~MEM name (MAP FST ys) /\ bvi_tmcProof_free_names n1 name`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC bvi_tmc_compile_each_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[bvi_tmc_compile_each_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    RVEQ_TAC THEN FS[MAP; MEM]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  BVITMCAUX_EACH_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN FS[MAP; MEM] THEN
  ASM_MESON_TAC[bvi_tmcProof_is_free_name; bvi_tmcProof_more_free_names]);;

let BVITMCAUX_ALL_FST_MEM = prove
 (`!P (l:(A#B)list) x. ALL (P o FST) l /\ MEM x (MAP FST l) ==> P x`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP; MEM; o_THM] THEN
  ASM_MESON_TAC[]);;

let BVITMCAUX_NS_POS = prove
 (`~(n + bvl_to_bvi_namespaces <= n) /\ 0 < bvl_to_bvi_namespaces /\
   ~(bvl_to_bvi_namespaces = 0)`,
  REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN ARITH_TAC);;

let bvi_tmcProof_compile_each_ALL_DISTINCT = prove
 (`bvi_tmc_compile_each n xs = (n1,ys) /\ ALL_DISTINCT (MAP FST xs) /\
   ALL (bvi_tmcProof_free_names n o FST) xs ==>
   ALL_DISTINCT (MAP FST ys) /\ ALL (bvi_tmcProof_free_names n1 o FST) ys`,
  SUBGOAL_THEN
   `!n xs n1 ys.
      bvi_tmc_compile_each n xs = (n1,ys) /\ ALL_DISTINCT (MAP FST xs) /\
      ALL (bvi_tmcProof_free_names n o FST) xs ==>
      ALL_DISTINCT (MAP FST ys) /\ ALL (bvi_tmcProof_free_names n1 o FST) ys`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC bvi_tmc_compile_each_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[bvi_tmc_compile_each_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[MAP; ALL; ALL_DISTINCT]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  BVITMCAUX_EACH_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  FS[MAP; ALL_DISTINCT; ALL; o_THM] THENL
   [ASM_MESON_TAC[bvi_tmcProof_compile_each_intro]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL (bvi_tmcProof_free_names (next + bvl_to_bvi_namespaces) o FST)
        (xs:(num#num#bvi_exp)list) /\
    bvi_tmcProof_free_names (next + bvl_to_bvi_namespaces) loc`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[bvi_tmcProof_EVERY_free_names_SUCSUC;
                  bvi_tmcProof_more_free_names]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~MEM loc (MAP FST (ys':(num#num#bvi_exp)list)) /\
    bvi_tmcProof_free_names n1 loc`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[bvi_tmcProof_compile_each_intro]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[bvi_tmcProof_is_free_name];
    DISCH_TAC THEN
    MP_TAC(INST [`next + bvl_to_bvi_namespaces`,`n:num`;
                 `xs:(num#num#bvi_exp)list`,`xs:(num#num#bvi_exp)list`;
                 `n1:num`,`n1:num`; `ys':(num#num#bvi_exp)list`,`ys:(num#num#bvi_exp)list`;
                 `next:num`,`e:num`] bvi_tmcProof_compile_each_MEM) THEN
    ASM_REWRITE_TAC[BVITMCAUX_NS_POS] THEN
    ASM_MESON_TAC[BVITMCAUX_ALL_FST_MEM; free_names_refl_F];
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvi_tmcProof_compile_each_next_mono) THEN
    ASM_REWRITE_TAC[bvi_tmcProof_free_names_def; bvl_to_bvi_namespaces_def] THEN
    ARITH_TAC]);;

let bvi_tmcProof_compile_prog_ALL_DISTINCT = prove
 (`bvi_tmc_compile_prog b n xs = (n1,ys) /\ ALL_DISTINCT (MAP FST xs) /\
   ALL (bvi_tmcProof_free_names n o FST) xs ==>
   ALL_DISTINCT (MAP FST ys) /\ ALL (bvi_tmcProof_free_names n1 o FST) ys`,
  REWRITE_TAC[bvi_tmc_compile_prog_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_MESON_TAC[bvi_tmcProof_compile_each_ALL_DISTINCT]);;

let BVITMCAUX_MOD_NS = prove
 (`!a k. (a + k * bvl_to_bvi_namespaces) MOD bvl_to_bvi_namespaces =
         a MOD bvl_to_bvi_namespaces`,
  REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

let bvi_tmcProof_compile_each_namespace_rel = prove
 (`bvi_tmc_compile_each next prog = (next1,prog2) /\
   next MOD bvl_to_bvi_namespaces = 3 /\ bvl_num_stubs <= next /\
   ALL ((~) o (\n. n MOD bvl_to_bvi_namespaces = 3) o FST)
       (FILTER ((<=) bvl_num_stubs o FST) prog) ==>
   bvi_tmcProof_namespace_rel (fromAList prog) (fromAList prog2)`,
  REWRITE_TAC[bvi_tmcProof_namespace_rel_def; domain_fromAList; IN_SET_OF_LIST;
              GSYM ALL_MEM; MEM_FILTER; o_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. MEM x (MAP FST (prog:(num#num#bvi_exp)list)) /\ bvl_num_stubs <= x ==>
        ~(x MOD bvl_to_bvi_namespaces = 3)`
   ASSUME_TAC THENL
   [REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  MP_TAC(INST [`next:num`,`n:num`; `prog:(num#num#bvi_exp)list`,`xs:(num#num#bvi_exp)list`;
               `next1:num`,`n1:num`; `prog2:(num#num#bvi_exp)list`,`ys:(num#num#bvi_exp)list`;
               `m:num`,`e:num`] bvi_tmcProof_compile_each_MEM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[BVITMCAUX_MOD_NS] THEN
  ASM_MESON_TAC[BVITMCAUX_MOD_NS; NOT_LE; LTE_TRANS; LET_TRANS; LE_TRANS]);;

let bvi_tmcProof_namespace_rel_union = prove
 (`bvi_tmcProof_namespace_rel (x:A spt) y /\ bvi_tmcProof_namespace_rel t s /\
   DISJOINT (domain s) (domain y) ==>
   bvi_tmcProof_namespace_rel (union x t) (union y s)`,
  REWRITE_TAC[bvi_tmcProof_namespace_rel_def; domain_union; IN_DISJOINT;
              IN_UNION; COND_EXPAND] THEN
  MESON_TAC[]);;

let BVITMCAUX_lookup_union_SOME = prove
 (`!k (m1:A spt) m2 v.
     lookup k (union m1 m2) = SOME v <=>
     lookup k m1 = SOME v \/ (lookup k m1 = NONE /\ lookup k m2 = SOME v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_union] THEN
  CASES_ON `lookup k (m1:A spt)` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT]);;

let bvi_tmcProof_code_rel_union = prove
 (`bvi_tmcProof_code_rel x y /\ bvi_tmcProof_code_rel t s /\
   DISJOINT (domain s) (domain y) ==>
   bvi_tmcProof_code_rel (union x t) (union y s)`,
  REWRITE_TAC[bvi_tmcProof_code_rel_def; BVITMCAUX_lookup_union_SOME] THEN
  REWRITE_TAC[IN_DISJOINT; domain_lookup] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "xy")
               (CONJUNCTS_THEN2 (LABEL_TAC "ts") ASSUME_TAC)) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [REMOVE_THEN "xy" (MP_TAC o SPECL [`loc:num`; `arity:num`; `exp:bvi_exp`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `n:num` THEN ASM_MESON_TAC[];
    REMOVE_THEN "ts" (MP_TAC o SPECL [`loc:num`; `arity:num`; `exp:bvi_exp`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `n:num` THEN
    ASM_MESON_TAC[option_DISTINCT; cases "option"]]);;

let bvi_tmcProof_state_rel_code_rel = prove
 (`bvi_tmcProof_state_rel f (s:(num#C,FFI)bvi_state) (t:(C,FFI)bvi_state) ==>
   bvi_tmcProof_code_rel (bvi_state_code s) (bvi_state_code t)`,
  SIMP_TAC[bvi_tmcProof_state_rel_def]);;

(* HOL4 [local]; next1 is free, as in HOL4 *)
let bvi_tmcProof_compile_each_untouched = prove
 (`!next prog prog2 loc exp arity.
     bvi_tmcProof_free_names next loc /\
     lookup loc (fromAList prog) = SOME (arity,exp) /\
     bvi_tmc_compile_exp loc next arity exp = NONE /\
     bvi_tmc_compile_each next prog = (next1,prog2) ==>
     lookup loc (fromAList prog2) = SOME (arity,exp)`,
  MATCH_MP_TAC bvi_tmc_compile_each_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[fromAList_def; lookup_def; option_DISTINCT]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`next:num`; `l0:num`; `a0:num`; `e0:bvi_exp`;
                       `xs:(num#num#bvi_exp)list`] THEN
  STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`prog2:(num#num#bvi_exp)list`; `loc:num`; `exp:bvi_exp`;
                       `arity:num`] THEN
  REWRITE_TAC[fromAList_def; lookup_insert] THEN
  ASM_CASES_TAC `loc:num = l0` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[option_INJ; PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[bvi_tmc_compile_each_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[fromAList_def; lookup_insert];
    ALL_TAC] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `bvi_tmc_compile_each next (CONS (l0,a0,e0) xs) = next1,prog2` THEN
  REWRITE_TAC[bvi_tmc_compile_each_def] THEN
  CASES_ON `bvi_tmc_compile_exp l0 next a0 e0` THEN FS[] THEN
  REPEAT PAIRARG_TAC THEN FS[] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[fromAList_def; lookup_insert] THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    COND_CASES_TAC THENL [ASM_MESON_TAC[bvi_tmcProof_is_free_name]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[bvi_tmcProof_more_free_names; bvi_tmcProof_compile_exp_next_addr]]);;

let BVITMCAUX_free_names_neq = prove
 (`!n name k. bvi_tmcProof_free_names n name ==>
              ~(n + bvl_to_bvi_namespaces * k = name)`,
  SIMP_TAC[bvi_tmcProof_free_names_def]);;

(* HOL4 [local]; next1 is free, as in HOL4 *)
let bvi_tmcProof_compile_each_touched = prove
 (`!next prog prog2 loc exp arity.
     ALL_DISTINCT (MAP FST prog) /\ ALL (bvi_tmcProof_free_names next o FST) prog /\
     bvi_tmcProof_free_names next loc /\
     lookup loc (fromAList prog) = SOME (arity,exp) /\
     (?w. bvi_tmc_compile_exp loc next arity exp = SOME w) /\
     bvi_tmc_compile_each next prog = (next1,prog2) ==>
     ?k. !wrap work.
       bvi_tmc_compile_exp loc (next + bvl_to_bvi_namespaces * k) arity exp =
         SOME (wrap,work) ==>
       lookup loc (fromAList prog2) = SOME (arity,wrap) /\
       lookup (next + bvl_to_bvi_namespaces * k) (fromAList prog2) =
         SOME (arity + 2,work)`,
  MATCH_MP_TAC bvi_tmc_compile_each_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[fromAList_def; lookup_def; option_DISTINCT]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`next:num`; `l0:num`; `a0:num`; `e0:bvi_exp`;
                       `xs:(num#num#bvi_exp)list`] THEN
  STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`prog2:(num#num#bvi_exp)list`; `loc:num`; `exp:bvi_exp`;
                       `arity:num`] THEN
  REWRITE_TAC[fromAList_def; lookup_insert; MAP; ALL_DISTINCT; ALL; o_THM; FST] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `bvi_tmc_compile_each next (CONS (l0,a0,e0) xs) = next1,prog2` THEN
  REWRITE_TAC[bvi_tmc_compile_each_def] THEN
  CASES_ON `bvi_tmc_compile_exp l0 next a0 e0` THEN FS[] THEN
  REPEAT PAIRARG_TAC THEN FS[] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[fromAList_def; lookup_insert] THENL
   [CASES_ON `loc:num = l0` THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; PAIR_EQ]) THEN
      FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC o check (is_conj o concl)) THEN
      UNDISCH_TAC `bvi_tmc_compile_exp l0 next arity exp = SOME w` THEN
      ASM_REWRITE_TAC[option_DISTINCT]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`loc:num`; `exp:bvi_exp`; `arity:num`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN EXISTS_TAC `k:num` THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`wrap:bvi_exp`; `work:bvi_exp`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MATCH_MP BVITMCAUX_free_names_neq
      (ASSUME `bvi_tmcProof_free_names next l0`)];
    ALL_TAC] THEN
  CASES_ON `loc:num = l0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; PAIR_EQ]) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o
      check (fun th -> is_conj(concl th))) THEN
    SUBGOAL_THEN `w = (exp_wrapper:bvi_exp,exp_worker:bvi_exp)` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `bvi_tmc_compile_exp l0 next a0 e0 = SOME w` THEN
      ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; option_INJ; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM(MATCH_MP bvi_tmcProof_is_free_name
      (ASSUME `bvi_tmcProof_free_names next l0`))];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?w2. bvi_tmc_compile_exp loc (next + bvl_to_bvi_namespaces) arity exp = SOME w2`
   STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC compile_exp_SOME_irrel THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`loc:num`; `exp:bvi_exp`; `arity:num`]) THEN
  ASM_SIMP_TAC[bvi_tmcProof_more_free_names; bvi_tmcProof_EVERY_free_names_SUCSUC] THEN
  ANTS_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN EXISTS_TAC `k + 1` THEN
  REWRITE_TAC[ARITH_RULE `next + b * (k + 1) = (next + b) + b * k`] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`wrap:bvi_exp`; `work:bvi_exp`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(loc:num = next)` ASSUME_TAC THENL
   [ACCEPT_TAC(GSYM(MATCH_MP bvi_tmcProof_is_free_name
      (ASSUME `bvi_tmcProof_free_names next loc`))); ALL_TAC] THEN
  SUBGOAL_THEN
   `~((next + bvl_to_bvi_namespaces) + bvl_to_bvi_namespaces * k = l0) /\
    ~((next + bvl_to_bvi_namespaces) + bvl_to_bvi_namespaces * k = next)`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `(next + b) + b * k = next + b * (k + 1)`] THEN
      REWRITE_TAC[MATCH_MP BVITMCAUX_free_names_neq
        (ASSUME `bvi_tmcProof_free_names next l0`)];
      REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let bvi_tmcProof_compile_each_code_rel = prove
 (`bvi_tmc_compile_each next prog = (next1,prog2) /\ ALL_DISTINCT (MAP FST prog) /\
   ALL (bvi_tmcProof_free_names next o FST) prog /\
   ALL (no_mutcons o SND o SND) prog ==>
   bvi_tmcProof_code_rel (fromAList prog) (fromAList prog2)`,
  REWRITE_TAC[bvi_tmcProof_code_rel_def] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`loc:num`; `arity:num`; `exp:bvi_exp`] THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `lookup loc (fromAList prog) = SOME (arity:num,exp:bvi_exp)` THEN
    REWRITE_TAC[lookup_fromAList] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    UNDISCH_TAC `ALL (no_mutcons o SND o SND) (prog:(num#num#bvi_exp)list)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
    REWRITE_TAC[o_THM; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `bvi_tmcProof_free_names next loc` ASSUME_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:num#bvi_exp`,`:A`]
                  (GEN_ALL bvi_tmcProof_EVERY_free_names_thm)) THEN
    MAP_EVERY EXISTS_TAC [`prog:(num#num#bvi_exp)list`; `(arity:num,exp:bvi_exp)`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASES_ON `bvi_tmc_compile_exp loc next arity exp` THENL
   [EXISTS_TAC `next:num` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
    MATCH_MP_TAC(GEN_ALL bvi_tmcProof_compile_each_untouched) THEN
    MAP_EVERY EXISTS_TAC [`next1:num`; `next:num`; `prog:(num#num#bvi_exp)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`next:num`; `prog:(num#num#bvi_exp)list`;
                `prog2:(num#num#bvi_exp)list`; `loc:num`; `exp:bvi_exp`;
                `arity:num`] bvi_tmcProof_compile_each_touched) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  EXISTS_TAC `next + bvl_to_bvi_namespaces * k` THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(INST [`loc:num`,`loc:num`; `next:num`,`next:num`; `arity:num`,`args:num`;
               `exp:bvi_exp`,`exp:bvi_exp`; `a:bvi_exp#bvi_exp`,`w:bvi_exp#bvi_exp`;
               `next + bvl_to_bvi_namespaces * k`,`next2:num`]
          compile_exp_SOME_irrel) THEN
  ASM_REWRITE_TAC[option_DISTINCT]);;

(* HOL4 [simp] *)
let eor_rel_def = cake_def
 `(eor_rel f (Exn v1) (Exn v2) <=> bvi_tmcProof_v_rel f v1 v2) /\
  (eor_rel f (Ret vs1) (Ret vs2) <=> ALL2 (bvi_tmcProof_v_rel f) vs1 vs2) /\
  (eor_rel f _ _ <=> F)`;;
let _ = cake_add_simps [eor_rel_def];;

let opt_res_rel_def = cake_def
 `opt_res_rel f (r1:(bvl_v list,exn_or_ret)result)
                (r2:(bvl_v list,exn_or_ret)result) <=>
    match (r1,r2) with
      (Rval v1,Rval [bvl_Block 0 []]) -> T
    | (Rerr e1,Rerr e2) -> exc_rel (eor_rel f) e1 e2
    | _ -> F`;;

(* a theorem whose conclusion is an application of the constant s *)
let BVITMCAUX_head_is s th =
  try fst(dest_const(fst(strip_comb(concl th)))) = s with Failure _ -> false;;

let v_rel_submap = prove
 (`!f v1 v2 f'. bvi_tmcProof_v_rel f v1 v2 /\ f SUBMAP f' ==>
                bvi_tmcProof_v_rel f' v1 v2`,
  SUBGOAL_THEN
   `!f v1 v2. bvi_tmcProof_v_rel f v1 v2 ==>
              !f'. f SUBMAP f' ==> bvi_tmcProof_v_rel f' v1 v2`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC bvi_tmcProof_v_rel_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN BETA_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[bvi_tmcProof_v_rel_Number];
    REWRITE_TAC[bvi_tmcProof_v_rel_Word64];
    MATCH_MP_TAC bvi_tmcProof_v_rel_Block THEN
    FIRST_X_ASSUM(MP_TAC o check (BVITMCAUX_head_is "ALL2")) THEN
    MATCH_MP_TAC MONO_ALL2 THEN BETA_TAC THEN ASM_MESON_TAC[];
    REWRITE_TAC[bvi_tmcProof_v_rel_CodePtr];
    MATCH_MP_TAC bvi_tmcProof_v_rel_RefPtr THEN ASM_MESON_TAC[FLOOKUP_SUBMAP]]);;

let list_rel_submap = prove
 (`ALL2 (bvi_tmcProof_v_rel f) env1 env2 /\ f SUBMAP f' ==>
   ALL2 (bvi_tmcProof_v_rel f') env1 env2`,
  STRIP_TAC THEN UNDISCH_TAC `ALL2 (bvi_tmcProof_v_rel f) env1 env2` THEN
  MATCH_MP_TAC MONO_ALL2 THEN ASM_MESON_TAC[v_rel_submap]);;

let env_rel_submap = prove
 (`bvi_tmcProof_env_rel opt f env1 env2 /\ f SUBMAP f' ==>
   bvi_tmcProof_env_rel opt f' env1 env2`,
  REWRITE_TAC[bvi_tmcProof_env_rel_def] THEN MESON_TAC[list_rel_submap]);;

let env_rel_relax_opt = prove
 (`!opt f env1 env2.
     bvi_tmcProof_env_rel opt f env1 env2 ==> bvi_tmcProof_env_rel F f env1 env2`,
  REWRITE_TAC[bvi_tmcProof_env_rel_def] THEN MESON_TAC[]);;

let env_rel_cons = prove
 (`bvi_tmcProof_env_rel opt f env1 env2 /\ bvi_tmcProof_v_rel f a b ==>
   bvi_tmcProof_env_rel opt f (CONS a env1) (CONS b env2)`,
  REWRITE_TAC[bvi_tmcProof_env_rel_def] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`CONS (b:bvl_v) xs`; `ys:bvl_v list`] THEN
  ASM_REWRITE_TAC[APPEND; ALL2]);;

let bvi_tmcProof_env_rel_append = prove
 (`bvi_tmcProof_env_rel opt f env1 env2 /\ ALL2 (bvi_tmcProof_v_rel f) a b ==>
   bvi_tmcProof_env_rel opt f (APPEND a env1) (APPEND b env2)`,
  REWRITE_TAC[bvi_tmcProof_env_rel_def] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`APPEND (b:bvl_v list) xs`; `ys:bvl_v list`] THEN
  ASM_SIMP_TAC[APPEND_ASSOC; LIST_REL_APPEND_suff]);;

let env_rel_length_opt = prove
 (`!f env1 env2.
     bvi_tmcProof_env_rel T f env1 env2 ==> LENGTH env2 = LENGTH env1 + 2`,
  REWRITE_TAC[bvi_tmcProof_env_rel_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  ASM_REWRITE_TAC[LENGTH_APPEND]);;

(* not a strict equality anymore! *)
let env_rel_length_non_opt = prove
 (`!f env1 env2.
     bvi_tmcProof_env_rel F f env1 env2 ==> LENGTH env2 >= LENGTH env1`,
  REWRITE_TAC[bvi_tmcProof_env_rel_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC);;

let bvi_tmcProof_env_rel_length = prove
 (`!opt f env1 env2.
     bvi_tmcProof_env_rel opt f env1 env2 ==> LENGTH env2 >= LENGTH env1`,
  REWRITE_TAC[bvi_tmcProof_env_rel_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC);;

let env_rel_extras_opt = prove
 (`!f env env'.
     bvi_tmcProof_env_rel T f env env' ==>
     ?hole_ptr hole_idx.
       EL (LENGTH env) env' = bvl_RefPtr F hole_ptr /\
       EL (LENGTH env + 1) env' = bvl_Number hole_idx`,
  REWRITE_TAC[bvi_tmcProof_env_rel_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  ASM_REWRITE_TAC[EL_APPEND_EQN; LT_REFL; ARITH_RULE `~(n + 1 < n)`; SUB_REFL;
                  ARITH_RULE `(n + 1) - n = 1`] THEN
  ASM_MESON_TAC[]);;

let env_rel_el_v_rel = prove
 (`!opt f env1 env2 n.
     bvi_tmcProof_env_rel opt f env1 env2 /\ n < LENGTH env1 ==>
     bvi_tmcProof_v_rel f (EL n env1) (EL n env2)`,
  REWRITE_TAC[bvi_tmcProof_env_rel_def] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  ASM_REWRITE_TAC[EL_APPEND_EQN] THEN
  SUBGOAL_THEN `n < LENGTH (xs:bvl_v list)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[LIST_REL_EL_EQN]);;

let BVITMCAUX_LENGTH_EQ_2 = prove
 (`!l:A list. LENGTH l = 2 ==> l = [EL 0 l; EL 1 l]`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = 2)`; ARITH_RULE `SUC n = 2 <=> n = 1`] THEN
  STRUCT_CASES_TAC(ISPEC `t:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = 1)`; ARITH_RULE `SUC n = 1 <=> n = 0`;
              LENGTH_EQ_NIL] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EL; HD; TL; ONE]);;

let env_rel_strip_extras = prove
 (`!f env1 env2.
     bvi_tmcProof_env_rel T f env1 env2 ==>
     ?env2' hole_ptr hole_idx.
       bvi_tmcProof_env_rel F f env1 env2' /\
       env2 = APPEND env2' [bvl_RefPtr F hole_ptr; bvl_Number hole_idx] /\
       small_enough_int hole_idx`,
  REWRITE_TAC[bvi_tmcProof_env_rel_def] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`xs:bvl_v list`; `hole_ptr:num`; `hole_idx:int`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`xs:bvl_v list`; `[]:bvl_v list`] THEN
    ASM_REWRITE_TAC[APPEND_NIL]; ALL_TAC] THEN
  AP_TERM_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP BVITMCAUX_LENGTH_EQ_2) THEN
  ASM_REWRITE_TAC[]);;

let state_rel_dec = prove
 (`!n t f (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state).
     bvi_tmcProof_state_rel f s s' /\ bvi_state_clock s = SUC n /\
     bvi_state_clock s' = SUC n /\ SUC n >= t ==>
     bvi_tmcProof_state_rel f (bvi_dec_clock t s) (bvi_dec_clock t s')`,
  REWRITE_TAC[bvi_tmcProof_state_rel_def; bvi_dec_clock_def;
              bvi_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let bvi_tmcProof_state_rel_with_clock = prove
 (`!n f (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state).
     bvi_tmcProof_state_rel f s s' ==>
     bvi_tmcProof_state_rel f (bvi_state_clock_fupd (K n) s)
                              (bvi_state_clock_fupd (K n) s')`,
  REWRITE_TAC[bvi_tmcProof_state_rel_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let state_ref_rel_filled = prove
 (`!f refs refs' k v.
     state_ref_rel f refs refs' /\ ~(k IN FRANGE f) ==>
     state_ref_rel f refs (refs' |+ (k,v))`,
  REWRITE_TAC[state_ref_rel_def; FLOOKUP_UPDATE; FRANGE_FLOOKUP] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
  MAP_EVERY EXISTS_TAC [`j:num`; `w:(bvl_v)bvl_ref`] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let state_rel_filled = prove
 (`!f (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) k v.
     bvi_tmcProof_state_rel f s s' /\ ~(k IN FRANGE f) ==>
     bvi_tmcProof_state_rel f s
       (bvi_state_refs_fupd (K (bvi_state_refs s' |+ (k,v))) s')`,
  REWRITE_TAC[bvi_tmcProof_state_rel_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC state_ref_rel_filled THEN ASM_REWRITE_TAC[]);;

let hole_has_val_def = cake_def
 `hole_has_val (f:(num,num)fmap) (env1:bvl_v list) (env2:bvl_v list)
               (refs:(num,(bvl_v)bvl_ref)fmap) c <=>
    LENGTH env2 = LENGTH env1 + 2 /\
    ?hole_ptr tag finalised left right.
      EL (LENGTH env1) env2 = bvl_RefPtr F hole_ptr /\
      EL (LENGTH env1 + 1) env2 = bvl_Number (&(LENGTH left)) /\
      small_enough_int (&(LENGTH left)) /\
      ~(hole_ptr IN FRANGE f) /\
      FLOOKUP refs hole_ptr = SOME (MutBlock tag finalised left c right)`;;

let holes_unchanged_except_def = cake_def
 `holes_unchanged_except (f:(A,B)fmap) (refs:(B,(C)bvl_ref)fmap)
                         (refs':(B,(C)bvl_ref)fmap) changed <=>
    !ptr tag finalised left child right.
      ~(ptr IN FRANGE f) /\
      FLOOKUP refs ptr = SOME (MutBlock tag finalised left child right) ==>
      ?finalised' child'.
        FLOOKUP refs' ptr = SOME (MutBlock tag finalised' left child' right) /\
        (~(ptr IN changed) ==> child = child')`;;

let hole_not_finalised_def = cake_def
 `hole_not_finalised (refs:(A,(B)bvl_ref)fmap) ptr <=>
    ?tag left child right.
      FLOOKUP refs ptr = SOME (MutBlock tag F left child right)`;;

let holes_still_not_finalised_def = cake_def
 `holes_still_not_finalised (f:(A,B)fmap) (refs:(B,(C)bvl_ref)fmap)
                            (refs':(B,(C)bvl_ref)fmap) <=>
    !ptr. ~(ptr IN FRANGE f) /\ hole_not_finalised refs ptr ==>
          hole_not_finalised refs' ptr`;;

let holes_still_not_finalised_refl = prove
 (`!(f:(A,B)fmap) (refs:(B,(C)bvl_ref)fmap). holes_still_not_finalised f refs refs`,
  REWRITE_TAC[holes_still_not_finalised_def] THEN MESON_TAC[]);;

let holes_still_not_finalised_ins = prove
 (`!(f:(A,B)fmap) (refs:(B,(C)bvl_ref)fmap) refs' ptr tag l c r.
     holes_still_not_finalised f refs refs' ==>
     holes_still_not_finalised f refs (refs' |+ (ptr,MutBlock tag F l c r))`,
  REWRITE_TAC[holes_still_not_finalised_def; hole_not_finalised_def;
              FLOOKUP_UPDATE] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let holes_still_not_finalised_del = prove
 (`!(f:(A,B)fmap) (refs:(B,(C)bvl_ref)fmap) refs' ptr tag l c r.
     holes_still_not_finalised f (refs |+ (ptr,MutBlock tag F l c r)) refs' ==>
     holes_still_not_finalised f refs refs'`,
  REWRITE_TAC[holes_still_not_finalised_def; hole_not_finalised_def;
              FLOOKUP_UPDATE] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let only_fresh_def = cake_def
 `only_fresh (f:(num,num)fmap) (f':(num,num)fmap)
             (refs_old:(num,(bvl_v)bvl_ref)fmap) <=>
    !n. n IN FRANGE f' /\ ~(n IN FRANGE f) ==> ~(n IN FDOM refs_old)`;;

let holes_unchanged_except_refl = prove
 (`!(f:(A,B)fmap) (refs:(B,(C)bvl_ref)fmap) changed.
     holes_unchanged_except f refs refs changed`,
  REWRITE_TAC[holes_unchanged_except_def] THEN MESON_TAC[]);;

let holes_unchanged_except_submap = prove
 (`!(f:(A,B)fmap) f' (refs:(B,(C)bvl_ref)fmap) refs' changed.
     holes_unchanged_except f refs refs' changed /\ f SUBMAP f' ==>
     holes_unchanged_except f' refs refs' changed`,
  REWRITE_TAC[holes_unchanged_except_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SUBMAP_FRANGE; SUBSET]);;

let holes_unchanged_except_trans = prove
 (`!f f' refs refs' refs'' changed.
     holes_unchanged_except f refs refs' changed /\
     holes_unchanged_except f' refs' refs'' changed /\
     only_fresh f f' refs /\ f SUBMAP f' ==>
     holes_unchanged_except f refs refs'' changed`,
  REWRITE_TAC[holes_unchanged_except_def; only_fresh_def] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "a") (CONJUNCTS_THEN2 (LABEL_TAC "b")
    STRIP_ASSUME_TAC)) THEN
  REPEAT STRIP_TAC THEN
  REMOVE_THEN "a" (MP_TAC o SPECL [`ptr:num`; `tag:num`; `finalised:bool`;
    `left:bvl_v list`; `child:bvl_v`; `right:bvl_v list`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fin1:bool` (X_CHOOSE_THEN `ch1:bvl_v`
    STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "b" (MP_TAC o SPECL [`ptr:num`; `tag:num`; `fin1:bool`;
    `left:bvl_v list`; `ch1:bvl_v`; `right:bvl_v list`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `fin2:bool` (X_CHOOSE_THEN `ch2:bvl_v`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`fin2:bool`; `ch2:bvl_v`] THEN
  ASM_MESON_TAC[]);;

let holes_still_not_finalised_trans = prove
 (`!f f' refs refs' refs'' (changed:A).
     holes_still_not_finalised f refs refs' /\
     holes_still_not_finalised f' refs' refs'' /\
     only_fresh f f' refs /\ f SUBMAP f' ==>
     holes_still_not_finalised f refs refs''`,
  REWRITE_TAC[holes_still_not_finalised_def; only_fresh_def] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ptr IN FDOM (refs:(num,(bvl_v)bvl_ref)fmap)` ASSUME_TAC THENL
   [UNDISCH_TAC `hole_not_finalised (refs:(num,(bvl_v)bvl_ref)fmap) ptr` THEN
    REWRITE_TAC[hole_not_finalised_def; FLOOKUP_DEF] THEN
    MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
  SUBGOAL_THEN `~(ptr IN FRANGE (f':(num,num)fmap))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let holes_unchanged_except_subset = prove
 (`!(f:(A,B)fmap) (refs:(B,(C)bvl_ref)fmap) refs' changed changed'.
     holes_unchanged_except f refs refs' changed /\ changed SUBSET changed' ==>
     holes_unchanged_except f refs refs' changed'`,
  REWRITE_TAC[holes_unchanged_except_def; SUBSET] THEN MESON_TAC[]);;

let holes_unchanged_except_del = prove
 (`!(f:(A,B)fmap) (refs_old:(B,(C)bvl_ref)fmap) refs_new changed ptr v.
     holes_unchanged_except f (refs_old |+ (ptr,v)) refs_new changed /\
     ~(ptr IN FDOM refs_old) ==>
     holes_unchanged_except f refs_old refs_new (changed DIFF {ptr})`,
  REWRITE_TAC[holes_unchanged_except_def; FLOOKUP_UPDATE; IN_DIFF; IN_SING] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(ptr = ptr':B)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ptr':B`; `tag:num`; `finalised:bool`;
    `left:C list`; `child:C`; `right:C list`]) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let holes_unchanged_except_del_SING = prove
 (`!(f:(A,B)fmap) (refs_old:(B,(C)bvl_ref)fmap) refs_new (changed:D) ptr v.
     holes_unchanged_except f (refs_old |+ (ptr,v)) refs_new {ptr} /\
     ~(ptr IN FDOM refs_old) ==>
     holes_unchanged_except f refs_old refs_new {}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP holes_unchanged_except_del o
    CONJ (ASSUME `holes_unchanged_except (f:(A,B)fmap)
                    ((refs_old:(B,(C)bvl_ref)fmap) |+ (ptr,v)) refs_new {ptr}`)) THEN
  REWRITE_TAC[DIFF_EQ_EMPTY]);;

let holes_unchanged_except_changed = prove
 (`!(f:(A,B)fmap) (refs_old:(B,(C)bvl_ref)fmap) refs_new (changed:D)
     ptr tag fin l c r.
     holes_unchanged_except f (refs_old |+ (ptr,MutBlock tag fin l c r))
       refs_new {} /\
     FLOOKUP refs_old ptr = SOME (MutBlock tag fin' l c' r) ==>
     holes_unchanged_except f refs_old refs_new {ptr}`,
  REWRITE_TAC[holes_unchanged_except_def; FLOOKUP_UPDATE; NOT_IN_EMPTY;
              IN_SING] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ptr':B`) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `ptr:B = ptr'` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `FLOOKUP (refs_old:(B,(C)bvl_ref)fmap) ptr' =
                 SOME (MutBlock tag' finalised left child right)` THEN
    ASM_REWRITE_TAC[option_INJ; injectivity "bvl_ref"] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    DISCH_THEN(MP_TAC o SPECL [`tag':num`; `fin:bool`; `left:C list`;
                               `c:C`; `right:C list`]) THEN
    REWRITE_TAC[] THEN MESON_TAC[];
    MESON_TAC[]]);;

let holes_unchanged_except_filled = prove
 (`!(f:(A,B)fmap) (refs_old:(B,(C)bvl_ref)fmap) refs_new (changed:D)
     ptr tag fin l c r.
     holes_unchanged_except f refs_old refs_new {} /\
     FLOOKUP refs_old ptr = SOME (MutBlock tag fin' l c' r) ==>
     holes_unchanged_except f refs_old
       (refs_new |+ (ptr,MutBlock tag fin l c r)) {ptr}`,
  REWRITE_TAC[holes_unchanged_except_def; FLOOKUP_UPDATE; NOT_IN_EMPTY;
              IN_SING] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `ptr:B = ptr'` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `FLOOKUP (refs_old:(B,(C)bvl_ref)fmap) ptr' =
                 SOME (MutBlock tag' finalised left child right)` THEN
    ASM_REWRITE_TAC[option_INJ; injectivity "bvl_ref"] THEN
    STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[option_INJ; injectivity "bvl_ref"] THEN
    MESON_TAC[];
    ASM_MESON_TAC[]]);;

let BVITMCAUX_EL_01 = prove
 (`!a b:A. EL 0 [a; b] = a /\ EL 1 [a; b] = b`,
  REWRITE_TAC[EL; HD; TL; ONE]);;

(* hole_has_val for an environment that ends in the two extra values *)
let BVITMCAUX_hole_has_val_APPEND = prove
 (`!f env env' p i refs c.
     hole_has_val f env (APPEND env' [bvl_RefPtr F p; bvl_Number i]) refs c <=>
     LENGTH env' = LENGTH env /\
     ?tag finalised left right.
       i = &(LENGTH left) /\ small_enough_int (&(LENGTH left)) /\
       ~(p IN FRANGE f) /\
       FLOOKUP refs p = SOME (MutBlock tag finalised left c right)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hole_has_val_def; LENGTH_APPEND; LENGTH] THEN
  ASM_CASES_TAC `LENGTH (env':bvl_v list) = LENGTH (env:bvl_v list)` THENL
   [ASM_REWRITE_TAC[EL_APPEND_EQN; LT_REFL; SUB_REFL; ARITH_RULE `~(n + 1 < n)`;
                    ARITH_RULE `(n + 1) - n = 1`; BVITMCAUX_EL_01;
                    injectivity "bvl_v"] THEN
    REWRITE_TAC[ARITH_RULE `SUC (SUC 0) = 2`] THEN MESON_TAC[];
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let unchanged_hole_has_val = prove
 (`!f f' env env' hole_ptr hole_idx refs refs' c changed.
     hole_has_val f env (APPEND env' [bvl_RefPtr F hole_ptr; bvl_Number hole_idx])
       refs c /\
     only_fresh f f' refs /\
     holes_unchanged_except f refs refs' changed /\
     ~(hole_ptr IN changed) ==>
     hole_has_val f' env (APPEND env' [bvl_RefPtr F hole_ptr; bvl_Number hole_idx])
       refs' c`,
  REWRITE_TAC[BVITMCAUX_hole_has_val_APPEND; holes_unchanged_except_def;
              only_fresh_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`hole_ptr:num`; `tag:num`; `finalised:bool`;
    `left:bvl_v list`; `c:bvl_v`; `right:bvl_v list`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`tag:num`; `finalised':bool`; `left:bvl_v list`;
                        `right:bvl_v list`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT]);;

let hole_has_val_submap = prove
 (`!f f' env1 env2 refs c.
     hole_has_val f' env1 env2 refs c /\ f SUBMAP f' ==>
     hole_has_val f env1 env2 refs c`,
  REWRITE_TAC[hole_has_val_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`hole_ptr:num`; `tag:num`; `finalised:bool`;
                        `left:bvl_v list`; `right:bvl_v list`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBMAP_FRANGE; SUBSET]);;

let hole_has_val_append = prove
 (`!f env env' refs c vs vs'.
     hole_has_val f env env' refs c /\ ALL2 (bvi_tmcProof_v_rel f) vs vs' ==>
     hole_has_val f (APPEND vs env) (APPEND vs' env') refs c`,
  REWRITE_TAC[hole_has_val_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; EL_APPEND_EQN;
    ARITH_RULE `~(a + b < a:num) /\ ~((a + b) + 1 < a) /\
                (a + b) - a = b /\ ((a + b) + 1) - a = b + 1`] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[]);;

let hole_has_val_unappend = prove
 (`!f. hole_has_val f (APPEND vs env) (APPEND vs' env') refs c /\
       ALL2 (bvi_tmcProof_v_rel f) vs vs' ==>
       hole_has_val f env env' refs c`,
  REWRITE_TAC[hole_has_val_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; EL_APPEND_EQN;
    ARITH_RULE `~(a + b < a:num) /\ ~((a + b) + 1 < a) /\
                (a + b) - a = b /\ ((a + b) + 1) - a = b + 1`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH (vs:bvl_v list) = LENGTH (vs':bvl_v list)`;
    ARITH_RULE `~(a + b < a:num) /\ ~((a + b) + 1 < a) /\
                (a + b) - a = b /\ ((a + b) + 1) - a = b + 1`]) THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[]);;

let hole_has_val_dec = prove
 (`!f env env' (s:(C,FFI)bvi_state) c n.
     hole_has_val f env env' (bvi_state_refs s) c /\ bvi_state_clock s = SUC n ==>
     hole_has_val f env env' (bvi_state_refs (bvi_dec_clock 1 s)) c`,
  SIMP_TAC[bvi_dec_clock_def; bvi_state_INFO.ri_accfupds; K_THM]);;

let only_fresh_refl = prove
 (`!f refs. only_fresh f f refs`,
  REWRITE_TAC[only_fresh_def] THEN MESON_TAC[]);;

let only_fresh_trans = prove
 (`!f f' f'' refs refs'.
     only_fresh f f' refs /\ only_fresh f' f'' refs' /\
     FDOM refs SUBSET FDOM refs' ==>
     only_fresh f f'' refs`,
  REWRITE_TAC[only_fresh_def; SUBSET] THEN MESON_TAC[]);;

let only_fresh_submap = prove
 (`!f f' f'' refs.
     only_fresh f f'' refs /\ f' SUBMAP f'' ==> only_fresh f f' refs`,
  REWRITE_TAC[only_fresh_def] THEN MESON_TAC[SUBMAP_FRANGE; SUBSET]);;

let non_fresh_not_in_frange = prove
 (`ptr IN FDOM refs_old /\ ~(ptr IN FRANGE f) /\ only_fresh f f' refs_old ==>
   ~(ptr IN FRANGE f')`,
  REWRITE_TAC[only_fresh_def] THEN MESON_TAC[]);;

let fresh_ptr_fresh = prove
 (`!refs:(num,A)fmap. ~((minimal ptr. ~(ptr IN FDOM refs)) IN FDOM refs)`,
  REWRITE_TAC[LEAST_NOTIN_FDOM]);;

let fresh_not_in_range_f = prove
 (`!f s_refs t_refs.
     state_ref_rel f s_refs t_refs ==>
     ~((minimal ptr. ~(ptr IN FDOM t_refs)) IN FRANGE f)`,
  REWRITE_TAC[state_ref_rel_def; FRANGE_FLOOKUP] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `t_refs:(num,(bvl_v)bvl_ref)fmap` fresh_ptr_fresh) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `k IN FDOM (s_refs:(num,(bvl_v)bvl_ref)fmap)` MP_TAC THENL
   [ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT]; ALL_TAC] THEN
  REWRITE_TAC[FLOOKUP_DEF] THEN
  ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT; option_INJ]);;

let only_fresh_del = prove
 (`!f f' refs ptr v.
     only_fresh f f' (refs |+ (ptr,v)) /\ ~(ptr IN FRANGE f) ==>
     only_fresh f f' refs`,
  REWRITE_TAC[only_fresh_def; FDOM_FUPDATE; IN_INSERT] THEN MESON_TAC[]);;

let flookup_com_neq = prove
 (`!(m:(A,B)fmap) k1 v1 k2 v2.
     ~(k1 = k2) ==> m |+ (k1,v1) |+ (k2,v2) = m |+ (k2,v2) |+ (k1,v1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE] THEN
  GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 Termination: wf_rel_tac measure (CARD o FDOM o FST o SND o SND) *)
let mb_rel_def = sem1aux_def_wf
  `measure (\p:(num,num)fmap # (num,(bvl_v)bvl_ref)fmap #
               (num,(bvl_v)bvl_ref)fmap # bvl_v # bvl_v.
              CARD (FDOM (FST (SND (SND p)))))`
  (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
   RVEQ_TAC THEN REWRITE_TAC[measure_THM; SND; FST; FDOM_DOMSUB] THEN
   POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
   REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN
   REWRITE_TAC[option_DISTINCT] THEN DISCH_THEN(K ALL_TAC) THEN
   ASM_SIMP_TAC[CARD_DELETE; FDOM_FINITE] THEN
   MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> n - 1 < n`) THEN
   ASM_SIMP_TAC[CARD_EQ_0; FDOM_FINITE] THEN ASM SET_TAC[])
  `(mb_rel f (refs_old:(num,(bvl_v)bvl_ref)fmap) refs (bvl_Block tag xs)
          (bvl_RefPtr b ptr) <=>
      if b \/ ptr IN FRANGE f \/ ptr IN FDOM refs_old then F else
      match FLOOKUP refs ptr with
        SOME (MutBlock tag' fin' left' child' right') ->
          (tag = tag' /\ fin' = F /\
           ?left child right.
             xs = APPEND (APPEND left [child]) right /\
             ALL2 (bvi_tmcProof_v_rel f) left left' /\
             mb_rel f refs_old (refs \\ ptr) child child' /\
             ALL2 (bvi_tmcProof_v_rel f) right right')
      | _ -> F) /\
   (mb_rel f _ refs v1 v2 <=> bvi_tmcProof_v_rel f v1 v2)`;;

let mb_rel_ind = cake_ind "mb_rel";;

let mb_rel_cons = prove
 (`!refs_old refs ptr f tag left left' v v' right right'.
     mb_rel f refs_old (refs \\ ptr) v v' /\
     ALL2 (bvi_tmcProof_v_rel f) left left' /\
     ALL2 (bvi_tmcProof_v_rel f) right right' /\
     FLOOKUP refs ptr = SOME (MutBlock tag F left' v' right') /\
     ~(ptr IN FRANGE f) /\ ~(ptr IN FDOM refs_old) ==>
     mb_rel f refs_old refs (bvl_Block tag (APPEND (APPEND left [v]) right))
       (bvl_RefPtr F ptr)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mb_rel_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`left:bvl_v list`; `v:bvl_v`; `right:bvl_v list`] THEN
  ASM_REWRITE_TAC[]);;

(* no mutable block is related to a reference that is not allocated *)
let BVITMCAUX_mb_rel_fresh_ptr = prove
 (`!f refs_old refs v q'.
     ~(q' IN FDOM refs) /\ ~(q' IN FRANGE f) ==>
     ~mb_rel f refs_old refs v (bvl_RefPtr F q')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FLOOKUP (refs:(num,(bvl_v)bvl_ref)fmap) q' = NONE` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FLOOKUP_DEF]; ALL_TAC] THEN
  CASES_ON `v:bvl_v` THEN REWRITE_TAC[mb_rel_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[COND_ID] THEN
  ONCE_REWRITE_TAC[bvi_tmcProof_v_rel_cases] THEN
  REWRITE_TAC[distinctness "bvl_v"; injectivity "bvl_v"] THEN
  ASM_MESON_TAC[FRANGE_FLOOKUP]);;

let mb_rel_del = prove
 (`!f refs_old refs v1 v2 ptr tag left ptr' right.
     mb_rel f refs_old refs v1 v2 /\
     FLOOKUP refs ptr = SOME (MutBlock tag F left (bvl_RefPtr F ptr') right) /\
     ~(ptr' IN FDOM refs) /\ ~(ptr' IN FDOM refs_old) /\ ~(ptr' IN FRANGE f) ==>
     mb_rel f refs_old (refs \\ ptr) v1 v2`,
  MATCH_MP_TAC mb_rel_ind THEN REWRITE_TAC[mb_rel_def] THEN
  REPEAT CONJ_TAC THEN
  TRY(REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  MAP_EVERY X_GEN_TAC [`f:(num,num)fmap`; `refs_old:(num,(bvl_v)bvl_ref)fmap`;
    `refs:(num,(bvl_v)bvl_ref)fmap`; `tg:num`; `xs:bvl_v list`; `b:bool`;
    `p:num`] THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `tq:num`; `lq:bvl_v list`; `q':num`;
                       `rq:bvl_v list`] THEN
  ASM_CASES_TAC `b \/ p IN FRANGE (f:(num,num)fmap) \/
                 p IN FDOM (refs_old:(num,(bvl_v)bvl_ref)fmap)` THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (refs:(num,(bvl_v)bvl_ref)fmap) p` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a:(bvl_v)bvl_ref` THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `p:num = q` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `FLOOKUP (refs:(num,(bvl_v)bvl_ref)fmap) q =
      SOME (MutBlock a0 a1 a2 a3 a4)`; option_INJ; injectivity "bvl_ref"]) THEN
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    RVEQ_TAC THEN
    UNDISCH_TAC `mb_rel f refs_old (refs \\ q) child (bvl_RefPtr F q')` THEN
    REWRITE_TAC[DOMSUB_FLOOKUP] THEN CASE_REWRITE_TAC[] THEN
    MATCH_MP_TAC BVITMCAUX_mb_rel_fresh_ptr THEN
    ASM_REWRITE_TAC[FDOM_DOMSUB; IN_DELETE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DOMSUB_FLOOKUP_THM] THEN CASE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`left:bvl_v list`; `child:bvl_v`; `right:bvl_v list`] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[DOMSUB_COMMUTES] THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`a0:num`; `a1:bool`; `a2:bvl_v list`;
    `a4:bvl_v list`; `child:bvl_v`; `a3:bvl_v`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`q:num`; `tq:num`; `lq:bvl_v list`; `q':num`;
                             `rq:bvl_v list`]) THEN
  ASM_REWRITE_TAC[DOMSUB_FLOOKUP_THM; FDOM_DOMSUB; IN_DELETE]);;

let state_ref_rel_update = prove
 (`!f s_refs t_refs ptr ptr' v w.
     state_ref_rel f s_refs t_refs /\ fmap_inj f /\
     FLOOKUP f ptr = SOME ptr' /\ bvi_tmcProof_ref_rel f v w ==>
     state_ref_rel f (s_refs |+ (ptr,v)) (t_refs |+ (ptr',w))`,
  REWRITE_TAC[state_ref_rel_def; FLOOKUP_UPDATE; FDOM_FUPDATE] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `FLOOKUP (f:(num,num)fmap) ptr = SOME ptr'` THEN
    REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[option_DISTINCT] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `u:(bvl_v)bvl_ref`] THEN
  ASM_CASES_TAC `ptr:num = i` THEN ASM_REWRITE_TAC[option_INJ] THENL
   [DISCH_THEN(SUBST_ALL_TAC o SYM) THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`ptr':num`; `w:(bvl_v)bvl_ref`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `u:(bvl_v)bvl_ref`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `w':(bvl_v)bvl_ref`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`j:num`; `w':(bvl_v)bvl_ref`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(ptr':num = j)` (fun th -> REWRITE_TAC[th] THEN ASM_REWRITE_TAC[]) THEN
  ASM_MESON_TAC[fmap_inj_def]);;

let bvl_to_bvi_refs = prove
 (`!(s:(C,FFI)bvi_state) r.
     bvl_to_bvi (bvl_state_refs_fupd (K r) (bvi_to_bvl s)) s =
     bvi_state_refs_fupd (K r) s`,
  REWRITE_TAC[bvl_to_bvi_with_refs; bvl_to_bvi_id]);;

let holes_unchanged_except_frange_update = prove
 (`!(f:(A,B)fmap) p k v (refs:(B,(C)bvl_ref)fmap).
     FLOOKUP f p = SOME k ==>
     holes_unchanged_except f refs (refs |+ (k,v)) {}`,
  REWRITE_TAC[holes_unchanged_except_def; FLOOKUP_UPDATE; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(k:B = ptr)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[FRANGE_FLOOKUP]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let holes_still_not_finalised_frange_update = prove
 (`!(f:(A,B)fmap) p k v (refs:(B,(C)bvl_ref)fmap).
     FLOOKUP f p = SOME k ==>
     holes_still_not_finalised f refs (refs |+ (k,v))`,
  REWRITE_TAC[holes_still_not_finalised_def; hole_not_finalised_def;
              FLOOKUP_UPDATE] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(k:B = ptr)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[FRANGE_FLOOKUP]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let ref_rel_submap = prove
 (`!f f' v w. bvi_tmcProof_ref_rel f v w /\ f SUBMAP f' ==>
              bvi_tmcProof_ref_rel f' v w`,
  REWRITE_TAC[bvi_tmcProof_ref_rel_cases] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[injectivity "bvl_ref"; distinctness "bvl_ref"] THEN
  ASM_MESON_TAC[v_rel_submap; list_rel_submap]);;

let state_ref_rel_alloc = prove
 (`!f s_refs t_refs src tgt rv rw.
     state_ref_rel f s_refs t_refs /\
     ~(src IN FDOM s_refs) /\ ~(tgt IN FDOM t_refs) /\ ~(tgt IN FRANGE f) /\
     bvi_tmcProof_ref_rel (f |+ (src,tgt)) rv rw ==>
     state_ref_rel (f |+ (src,tgt)) (s_refs |+ (src,rv)) (t_refs |+ (tgt,rw))`,
  REWRITE_TAC[state_ref_rel_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:(num,num)fmap) SUBMAP (f |+ (src,tgt))` ASSUME_TAC THENL
   [REWRITE_TAC[SUBMAP_FUPDATE_FLOOKUP; FLOOKUP_DEF] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[FDOM_FUPDATE; FLOOKUP_UPDATE] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `u:(bvl_v)bvl_ref`] THEN
  ASM_CASES_TAC `src:num = i` THEN ASM_REWRITE_TAC[option_INJ] THENL
   [DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`tgt:num`; `rw:(bvl_v)bvl_ref`] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
      is_var(lhs(concl th)) && fst(dest_var(lhs(concl th))) = "src")) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `u:(bvl_v)bvl_ref`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `w:(bvl_v)bvl_ref`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`j:num`; `w:(bvl_v)bvl_ref`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ref_rel_submap THEN EXISTS_TAC `f:(num,num)fmap` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(tgt:num = j)` (fun th -> REWRITE_TAC[th] THEN ASM_REWRITE_TAC[]) THEN
  ASM_MESON_TAC[FRANGE_FLOOKUP]);;

let state_rel_alloc = prove
 (`!f (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) src tgt rv rw.
     bvi_tmcProof_state_rel f s s' /\
     ~(src IN FDOM (bvi_state_refs s)) /\ ~(tgt IN FDOM (bvi_state_refs s')) /\
     ~(tgt IN FRANGE f) /\
     bvi_tmcProof_ref_rel (f |+ (src,tgt)) rv rw ==>
     FLOOKUP (f |+ (src,tgt)) src = SOME tgt /\
     bvi_tmcProof_state_rel (f |+ (src,tgt))
       (bvi_state_refs_fupd (K (bvi_state_refs s |+ (src,rv))) s)
       (bvi_state_refs_fupd (K (bvi_state_refs s' |+ (tgt,rw))) s') /\
     f SUBMAP (f |+ (src,tgt)) /\
     only_fresh f (f |+ (src,tgt)) (bvi_state_refs s') /\
     holes_unchanged_except f (bvi_state_refs s')
       (bvi_state_refs s' |+ (tgt,rw)) {} /\
     holes_still_not_finalised f (bvi_state_refs s')
       (bvi_state_refs s' |+ (tgt,rw))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FLOOKUP (f:(num,num)fmap) src = NONE` ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_tmcProof_state_rel f (s:(num#C,FFI)bvi_state)
                   (s':(C,FFI)bvi_state)` THEN
    REWRITE_TAC[bvi_tmcProof_state_rel_def; state_ref_rel_def; FLOOKUP_DEF] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:(num,num)fmap) SUBMAP (f |+ (src,tgt))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBMAP_FUPDATE_FLOOKUP]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `bvi_tmcProof_state_rel f (s:(num#C,FFI)bvi_state)
                   (s':(C,FFI)bvi_state)` THEN
    REWRITE_TAC[bvi_tmcProof_state_rel_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC state_ref_rel_alloc THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `OPTREL (\p p'. FLOOKUP (f:(num,num)fmap) p = SOME p')
                     (bvi_state_global (s:(num#C,FFI)bvi_state))
                     (bvi_state_global (s':(C,FFI)bvi_state))` THEN
      MATCH_MP_TAC OPTREL_MONO THEN REWRITE_TAC[] THEN
      ASM_MESON_TAC[FLOOKUP_SUBMAP];
      MATCH_MP_TAC fmap_inj_update THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[only_fresh_def; FRANGE_FLOOKUP; FLOOKUP_UPDATE] THEN
    GEN_TAC THEN STRIP_TAC THEN UNDISCH_TAC
     `(if src = k then SOME (tgt:num) else FLOOKUP (f:(num,num)fmap) k) = SOME n` THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
    REWRITE_TAC[holes_unchanged_except_def; FLOOKUP_UPDATE] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
     [ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT]; ASM_MESON_TAC[]];
    REWRITE_TAC[holes_still_not_finalised_def; hole_not_finalised_def;
                FLOOKUP_UPDATE] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
     [ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT]; ASM_MESON_TAC[]]]);;

let state_ref_rel_lookup = prove
 (`!f n m refs t_refs.
     FLOOKUP f n = SOME m /\ state_ref_rel f refs t_refs ==>
     ?v w. FLOOKUP refs n = SOME v /\ FLOOKUP t_refs m = SOME w /\
           bvi_tmcProof_ref_rel f v w`,
  REWRITE_TAC[state_ref_rel_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?v. FLOOKUP (refs:(num,(bvl_v)bvl_ref)fmap) n = SOME v`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `FLOOKUP (f:(num,num)fmap) n = SOME m` THEN
    REWRITE_TAC[FLOOKUP_DEF] THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:(bvl_v)bvl_ref`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `FLOOKUP (f:(num,num)fmap) n = SOME m`;
                              option_INJ]) THEN
  RVEQ_TAC THEN ASM_MESON_TAC[]);;

let fmap_inj_flookup_eq = prove
 (`!f n m n' m'.
     fmap_inj f /\ FLOOKUP f n = SOME m /\ FLOOKUP f n' = SOME m' ==>
     (m = m' <=> n = n')`,
  REWRITE_TAC[fmap_inj_def] THEN REPEAT STRIP_TAC THEN EQ_TAC THEN
  DISCH_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN ASM_MESON_TAC[option_INJ]);;

let v_to_list_v_rel = prove
 (`!lv xs lw f.
     bvl_v_to_list lv = SOME xs /\ bvi_tmcProof_v_rel f lv lw ==>
     ?ys. bvl_v_to_list lw = SOME ys /\ ALL2 (bvi_tmcProof_v_rel f) xs ys`,
  MATCH_MP_TAC bvl_v_to_list_ind THEN REWRITE_TAC[bvl_v_to_list_def] THEN
  REWRITE_TAC[option_DISTINCT] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ONCE_REWRITE_TAC[bvi_tmcProof_v_rel_cases] THEN
    REWRITE_TAC[distinctness "bvl_v"; injectivity "bvl_v"] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (BVITMCAUX_head_is "ALL2")) THEN
    STRUCT_CASES_TAC(ISPEC `ys:bvl_v list` list_CASES) THEN
    REWRITE_TAC[ALL2; bvl_v_to_list_def] THEN
    EXISTS_TAC `[]:bvl_v list` THEN REWRITE_TAC[ALL2];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[bvi_tmcProof_v_rel_cases] THEN
    REWRITE_TAC[distinctness "bvl_v"; injectivity "bvl_v"] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    REWRITE_TAC[option_case_eq; option_DISTINCT; option_INJ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (BVITMCAUX_head_is "ALL2")) THEN
    STRUCT_CASES_TAC(ISPEC `ys:bvl_v list` list_CASES) THEN
    REWRITE_TAC[ALL2] THEN
    STRUCT_CASES_TAC(ISPEC `t:bvl_v list` list_CASES) THEN
    REWRITE_TAC[ALL2] THEN
    STRUCT_CASES_TAC(ISPEC `t':bvl_v list` list_CASES) THEN
    REWRITE_TAC[ALL2] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:bvl_v list`; `h'':bvl_v`; `f:(num,num)fmap`] o
      REWRITE_RULE[] o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `CONS (h':bvl_v) ys` THEN
    ASM_REWRITE_TAC[bvl_v_to_list_def; ALL2] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[]]);;

let bvi_tmcProof_list_to_v_v_rel = prove
 (`!xs ys f.
     ALL2 (bvi_tmcProof_v_rel f) xs ys ==>
     bvi_tmcProof_v_rel f (bvl_list_to_v xs) (bvl_list_to_v ys)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ys:bvl_v list` list_CASES) THEN
  REWRITE_TAC[ALL2; bvl_list_to_v_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC bvi_tmcProof_v_rel_Block THEN ASM_SIMP_TAC[ALL2]);;

(* inversion of v_rel and ref_rel on a known constructor (the effect of     *)
(* HOL4's gvs [v_rel_cases] and gvs [ref_rel_cases])                        *)
let BVITMCAUX_v_rel_simps = prove
 (`(!f i y. bvi_tmcProof_v_rel f (bvl_Number i) y <=> y = bvl_Number i) /\
   (!f w y. bvi_tmcProof_v_rel f (bvl_Word64 w) y <=> y = bvl_Word64 w) /\
   (!f n xs y. bvi_tmcProof_v_rel f (bvl_Block n xs) y <=>
               ?ys. y = bvl_Block n ys /\ ALL2 (bvi_tmcProof_v_rel f) xs ys) /\
   (!f n y. bvi_tmcProof_v_rel f (bvl_CodePtr n) y <=> y = bvl_CodePtr n) /\
   (!f b n y. bvi_tmcProof_v_rel f (bvl_RefPtr b n) y <=>
              ?m. y = bvl_RefPtr b m /\ FLOOKUP f n = SOME m) /\
   (!f i x. bvi_tmcProof_v_rel f x (bvl_Number i) <=> x = bvl_Number i) /\
   (!f w x. bvi_tmcProof_v_rel f x (bvl_Word64 w) <=> x = bvl_Word64 w) /\
   (!f n ys x. bvi_tmcProof_v_rel f x (bvl_Block n ys) <=>
               ?xs. x = bvl_Block n xs /\ ALL2 (bvi_tmcProof_v_rel f) xs ys) /\
   (!f n x. bvi_tmcProof_v_rel f x (bvl_CodePtr n) <=> x = bvl_CodePtr n) /\
   (!f b m x. bvi_tmcProof_v_rel f x (bvl_RefPtr b m) <=>
              ?n. x = bvl_RefPtr b n /\ FLOOKUP f n = SOME m)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [bvi_tmcProof_v_rel_cases] THEN
  REWRITE_TAC[distinctness "bvl_v"; injectivity "bvl_v"] THEN MESON_TAC[]);;

let BVITMCAUX_ref_rel_simps = prove
 (`(!f b bs y. bvi_tmcProof_ref_rel f (bvl_ByteArray b bs) y <=>
               y = bvl_ByteArray b bs) /\
   (!f xs y. bvi_tmcProof_ref_rel f (bvl_ValueArray xs) y <=>
             ?ys. y = bvl_ValueArray ys /\ ALL2 (bvi_tmcProof_v_rel f) xs ys) /\
   (!f tm x y. bvi_tmcProof_ref_rel f (bvl_Thunk tm x) y <=>
               ?y'. y = bvl_Thunk tm y' /\ bvi_tmcProof_v_rel f x y') /\
   (!f tag fin l c r y. ~bvi_tmcProof_ref_rel f (MutBlock tag fin l c r) y) /\
   (!f b bs x. bvi_tmcProof_ref_rel f x (bvl_ByteArray b bs) <=>
               x = bvl_ByteArray b bs) /\
   (!f ys x. bvi_tmcProof_ref_rel f x (bvl_ValueArray ys) <=>
             ?xs. x = bvl_ValueArray xs /\ ALL2 (bvi_tmcProof_v_rel f) xs ys) /\
   (!f tm y x. bvi_tmcProof_ref_rel f x (bvl_Thunk tm y) <=>
               ?x'. x = bvl_Thunk tm x' /\ bvi_tmcProof_v_rel f x' y) /\
   (!f tag fin l c r x. ~bvi_tmcProof_ref_rel f x (MutBlock tag fin l c r))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_tmcProof_ref_rel_cases] THEN
  REWRITE_TAC[distinctness "bvl_ref"; injectivity "bvl_ref"] THEN MESON_TAC[]);;

let BVITMCAUX_do_eq_ref = prove
 (`!f refs t_refs b1 n1 m1 b2 n2 m2.
     state_ref_rel f refs t_refs /\ fmap_inj f /\
     FLOOKUP f n1 = SOME m1 /\ FLOOKUP f n2 = SOME m2 ==>
     bvl_do_eq refs (bvl_RefPtr b1 n1) (bvl_RefPtr b2 n2) =
     bvl_do_eq t_refs (bvl_RefPtr b1 m1) (bvl_RefPtr b2 m2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`f:(num,num)fmap`; `n1:num`; `m1:num`;
                `refs:(num,(bvl_v)bvl_ref)fmap`;
                `t_refs:(num,(bvl_v)bvl_ref)fmap`] state_ref_rel_lookup) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:(bvl_v)bvl_ref` (X_CHOOSE_THEN `w1:(bvl_v)bvl_ref`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`f:(num,num)fmap`; `n2:num`; `m2:num`;
                `refs:(num,(bvl_v)bvl_ref)fmap`;
                `t_refs:(num,(bvl_v)bvl_ref)fmap`] state_ref_rel_lookup) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v2:(bvl_v)bvl_ref` (X_CHOOSE_THEN `w2:(bvl_v)bvl_ref`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `((m1:num) = m2) <=> ((n1:num) = n2)` ASSUME_TAC THENL
   [MATCH_MP_TAC fmap_inj_flookup_eq THEN EXISTS_TAC `f:(num,num)fmap` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[bvl_do_eq_def] THEN
  CASES_ON `v1:(bvl_v)bvl_ref` THEN CASES_ON `v2:(bvl_v)bvl_ref` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BVITMCAUX_ref_rel_simps]) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let BVITMCAUX_do_eq_block = prove
 (`!f (refs:(num,(A)bvl_ref)fmap) (t_refs:(num,(B)bvl_ref)fmap) t1 l1 ys1 t2 l2 ys2.
     ALL2 (bvi_tmcProof_v_rel f) l1 ys1 /\ ALL2 (bvi_tmcProof_v_rel f) l2 ys2 /\
     (~(bvl_isClos t1 l1 \/ bvl_isClos t2 l2) /\ t1 = t2 /\
      LENGTH l1 = LENGTH l2 ==>
      bvl_do_eq_list refs l1 l2 = bvl_do_eq_list t_refs ys1 ys2) ==>
     bvl_do_eq refs (bvl_Block t1 l1) (bvl_Block t2 l2) =
     bvl_do_eq t_refs (bvl_Block t1 ys1) (bvl_Block t2 ys2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH o
    check (BVITMCAUX_head_is "ALL2"))) THEN
  REWRITE_TAC[bvl_do_eq_def] THEN
  SUBGOAL_THEN `bvl_isClos t1 (ys1:bvl_v list) = bvl_isClos t1 (l1:bvl_v list) /\
                bvl_isClos t2 (ys2:bvl_v list) = bvl_isClos t2 (l2:bvl_v list)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[bvl_isClos_def; GSYM LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (ys1:bvl_v list) = LENGTH (ys2:bvl_v list) <=>
                LENGTH (l1:bvl_v list) = LENGTH (l2:bvl_v list)`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let BVITMCAUX_do_eq_list_cons = prove
 (`!refs t_refs v1 vs1 v2 vs2 w1 ws1 w2 ws2.
     bvl_do_eq refs v1 v2 = bvl_do_eq t_refs w1 w2 /\
     (bvl_do_eq refs v1 v2 = Eq_val T ==>
      bvl_do_eq_list refs vs1 vs2 = bvl_do_eq_list t_refs ws1 ws2) ==>
     bvl_do_eq_list (refs:(num,(A)bvl_ref)fmap) (CONS v1 vs1) (CONS v2 vs2) =
     bvl_do_eq_list (t_refs:(num,(B)bvl_ref)fmap) (CONS w1 ws1) (CONS w2 ws2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[bvl_do_eq_def] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    not (is_imp(concl th)))) THEN
  CASES_ON `bvl_do_eq (refs:(num,(A)bvl_ref)fmap) v1 v2` THEN
  CASE_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let do_eq_v_rel = prove
 (`(!refs x1 x2 t_refs y1 y2.
      bvi_tmcProof_v_rel f x1 y1 /\ bvi_tmcProof_v_rel f x2 y2 /\
      state_ref_rel f refs t_refs /\ fmap_inj f ==>
      bvl_do_eq refs x1 x2 = bvl_do_eq t_refs y1 y2) /\
   (!refs x1s x2s t_refs y1s y2s.
      ALL2 (bvi_tmcProof_v_rel f) x1s y1s /\ ALL2 (bvi_tmcProof_v_rel f) x2s y2s /\
      state_ref_rel f refs t_refs /\ fmap_inj f ==>
      bvl_do_eq_list refs x1s x2s = bvl_do_eq_list t_refs y1s y2s)`,
  MATCH_MP_TAC bvl_do_eq_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN
  (DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN STRIP_TAC ORELSE
   STRIP_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BVITMCAUX_v_rel_simps; LIST_REL_NIL; LIST_REL_CONS1]) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THEN
  FIRST
   [REWRITE_TAC[bvl_do_eq_def] THEN NO_TAC;
    MATCH_MP_TAC BVITMCAUX_do_eq_ref THEN EXISTS_TAC `f:(num,num)fmap` THEN
    ASM_REWRITE_TAC[] THEN NO_TAC;
    MATCH_MP_TAC BVITMCAUX_do_eq_block THEN EXISTS_TAC `f:(num,num)fmap` THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN REMOVE_THEN "ih" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    MATCH_MP_TAC BVITMCAUX_do_eq_list_cons THEN
    REMOVE_THEN "ih" (CONJUNCTS_THEN2 (LABEL_TAC "ihl") (LABEL_TAC "ihp")) THEN
    CONJ_TAC THENL
     [REMOVE_THEN "ihp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN REMOVE_THEN "ihl" (MP_TAC o SPEC `T`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* the arguments and the result of a word operation are numbers and words *)
let BVITMCAUX_do_word_app_args = prove
 (`!w vs res.
     bvl_do_word_app w vs = SOME res ==>
     ALL (\v. (?i. v = bvl_Number i) \/ (?w. v = bvl_Word64 w)) vs /\
     ((?i. res = bvl_Number i) \/ (?w. res = bvl_Word64 w) \/
      (?b. res = bvl_Boolv b))`,
  MATCH_MP_TAC bvl_do_word_app_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_do_word_app_def; option_DISTINCT] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; ALL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[distinctness "bvl_v"; injectivity "bvl_v";
              MESON[] `(!a:A. ?x. a = x) /\ (!x. ?b. bvl_Boolv x = bvl_Boolv b)`]);;

let BVITMCAUX_ALL2_flat = prove
 (`!vs vs' f.
     ALL (\v. (?i. v = bvl_Number i) \/ (?w. v = bvl_Word64 w)) vs /\
     ALL2 (bvi_tmcProof_v_rel f) vs vs' ==> vs' = vs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; LIST_REL_NIL; LIST_REL_CONS1] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BVITMCAUX_v_rel_simps]) THEN
  ASM_REWRITE_TAC[CONS_11] THEN ASM_MESON_TAC[]);;

let do_word_app_v_rel = prove
 (`!w vs res vs' f.
     bvl_do_word_app w vs = SOME res /\ ALL2 (bvi_tmcProof_v_rel f) vs vs' ==>
     vs' = vs`,
  MESON_TAC[BVITMCAUX_do_word_app_args; BVITMCAUX_ALL2_flat]);;

let do_word_app_v_rel_refl = prove
 (`!w vs res f.
     bvl_do_word_app w vs = SOME res ==> bvi_tmcProof_v_rel f res res`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2 o MATCH_MP BVITMCAUX_do_word_app_args) THEN
  ASM_REWRITE_TAC[bvl_Boolv_def; bvi_tmcProof_v_rel_Number;
                  bvi_tmcProof_v_rel_Word64] THEN
  MATCH_MP_TAC bvi_tmcProof_v_rel_Block THEN REWRITE_TAC[ALL2]);;

let no_mutblock = prove
 (`!f refs t_refs ptr tag fin l c r.
     state_ref_rel f refs t_refs /\
     FLOOKUP refs ptr = SOME (MutBlock tag fin l c r) ==> F`,
  REWRITE_TAC[state_ref_rel_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ptr:num`; `MutBlock tag fin l c r:(bvl_v)bvl_ref`]) THEN
  ASM_REWRITE_TAC[BVITMCAUX_ref_rel_simps]);;

(* Install reads byte/word vectors out of values; these are lists of Numbers *)
(* resp. Word64s, which v_rel relates exactly.                               *)

(* HOL4 [local] *)
let list_rel_v_rel_number = prove
 (`!g ns ys f.
     ALL2 (bvi_tmcProof_v_rel f) (MAP (bvl_Number o g) ns) ys ==>
     ys = MAP ((bvl_Number:int->bvl_v) o (g:A->int)) ns`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; LIST_REL_NIL; LIST_REL_CONS1; o_THM] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BVITMCAUX_v_rel_simps]) THEN
  ASM_REWRITE_TAC[CONS_11; o_THM] THEN ASM_MESON_TAC[]);;

(* HOL4 [local] *)
let list_rel_v_rel_word = prove
 (`!ns ys f.
     ALL2 (bvi_tmcProof_v_rel f) (MAP bvl_Word64 ns) ys ==> ys = MAP bvl_Word64 ns`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; LIST_REL_NIL; LIST_REL_CONS1] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BVITMCAUX_v_rel_simps]) THEN
  ASM_REWRITE_TAC[CONS_11] THEN ASM_MESON_TAC[]);;

(* HOL4 [local] *)
let bvi_tmcProof_v_to_bytes_eq = prove
 (`bvl_v_to_bytes lv = SOME bytes <=>
   bvl_v_to_list lv = SOME (MAP (bvl_Number o int_of_num o val) bytes)`,
  REWRITE_TAC[bvl_v_to_bytes_def; some_DEF] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN
  SPEC_TAC(`@ns:byte list. bvl_v_to_list lv =
              SOME (MAP (bvl_Number o int_of_num o val) ns)`,`ns:byte list`) THEN
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_INJ] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `bvl_Number o int_of_num o (val:byte->num)` INJ_MAP_EQ) THEN
  ASM_REWRITE_TAC[INJ; IN_UNIV; o_THM; injectivity "bvl_v"; INT_OF_NUM_EQ; VAL_EQ] THEN
  MESON_TAC[]);;

(* HOL4 [local] *)
let bvi_tmcProof_v_to_words_eq = prove
 (`bvl_v_to_words lv = SOME ws <=>
   bvl_v_to_list lv = SOME (MAP bvl_Word64 ws)`,
  REWRITE_TAC[bvl_v_to_words_def; some_DEF] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN
  SPEC_TAC(`@ns:int64 list. bvl_v_to_list lv = SOME (MAP bvl_Word64 ns)`,
           `ns:int64 list`) THEN
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_INJ] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC(ISPEC `bvl_Word64` INJ_MAP_EQ) THEN
  ASM_REWRITE_TAC[INJ; IN_UNIV; injectivity "bvl_v"] THEN MESON_TAC[]);;

let v_to_bytes_v_rel = prove
 (`bvl_v_to_bytes lv = SOME bytes /\ bvi_tmcProof_v_rel f lv lw ==>
   bvl_v_to_bytes lw = SOME bytes`,
  REWRITE_TAC[bvi_tmcProof_v_to_bytes_eq] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`lv:bvl_v`; `MAP (bvl_Number o int_of_num o val) (bytes:byte list)`;
                `lw:bvl_v`; `f:(num,num)fmap`] v_to_list_v_rel) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP list_rel_v_rel_number) THEN
  ASM_REWRITE_TAC[]);;

let v_to_words_v_rel = prove
 (`bvl_v_to_words lv = SOME ws /\ bvi_tmcProof_v_rel f lv lw ==>
   bvl_v_to_words lw = SOME ws`,
  REWRITE_TAC[bvi_tmcProof_v_to_words_eq] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`lv:bvl_v`; `MAP bvl_Word64 (ws:int64 list)`;
                `lw:bvl_v`; `f:(num,num)fmap`] v_to_list_v_rel) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP list_rel_v_rel_word) THEN
  ASM_REWRITE_TAC[]);;

let BVITMCAUX_v_rel_update = prove
 (`!f (m:num->bvl_v) m' i x x'.
     (!j. bvi_tmcProof_v_rel f (m j) (m' j)) /\ bvi_tmcProof_v_rel f x x' ==>
     !j. bvi_tmcProof_v_rel f ((i =+ x) m j) ((i =+ x') m' j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[APPLY_UPDATE_THM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* allocating at a fresh target pointer keeps the old holes *)
let BVITMCAUX_alloc_fresh = prove
 (`!f src tgt (rw:(bvl_v)bvl_ref) refs.
     ~(tgt IN FDOM refs) /\ ~(tgt IN FRANGE f) ==>
     only_fresh f (f |+ (src,tgt)) refs /\
     holes_unchanged_except f refs (refs |+ (tgt,rw)) {} /\
     holes_still_not_finalised f refs (refs |+ (tgt,rw))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[only_fresh_def; FRANGE_FLOOKUP; FLOOKUP_UPDATE] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `(if src = k then SOME (tgt:num) else FLOOKUP (f:(num,num)fmap) k) =
                 SOME n` THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THEN ASM_MESON_TAC[];
    REWRITE_TAC[holes_unchanged_except_def; FLOOKUP_UPDATE] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
     [ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT]; ASM_MESON_TAC[]];
    REWRITE_TAC[holes_still_not_finalised_def; hole_not_finalised_def;
                FLOOKUP_UPDATE] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
     [ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT]; ASM_MESON_TAC[]]]);;

let BVITMCAUX_ALL2_MAP = prove
 (`!(R:B->C->bool) (m:A->B) m' l.
     (!j. R (m j) (m' j)) ==> ALL2 R (MAP m l) (MAP m' l)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[MAP; ALL2]);;

let do_build_v_rel = prove
 (`!parts m i refs1 v refs1' f m' refs2.
     bvl_do_build m i parts refs1 = (v,refs1') /\ state_ref_rel f refs1 refs2 /\
     fmap_inj f /\ (!j. bvi_tmcProof_v_rel f (m j) (m' j)) ==>
     ?f' v' refs2'.
       bvl_do_build m' i parts refs2 = (v',refs2') /\
       bvi_tmcProof_v_rel f' v v' /\
       state_ref_rel f' refs1' refs2' /\ fmap_inj f' /\ f SUBMAP f' /\
       only_fresh f f' refs2 /\ holes_unchanged_except f refs2 refs2' {} /\
       holes_still_not_finalised f refs2 refs2'`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[bvl_do_build_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `(m':num->bvl_v) (i - 1)`;
                          `refs2:(num,(bvl_v)bvl_ref)fmap`] THEN
    ASM_REWRITE_TAC[SUBMAP_REFL; only_fresh_refl; holes_unchanged_except_refl;
                    holes_still_not_finalised_refl];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_build_def] THEN
  CASES_ON `h:const_part` THEN
  REWRITE_TAC[bvl_do_part_def; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`(i =+ bvl_Block a0 (MAP m a1)) (m:num->bvl_v)`;
                          `refs1:(num,(bvl_v)bvl_ref)fmap`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BVITMCAUX_v_rel_update THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC bvi_tmcProof_v_rel_Block THEN
    MATCH_MP_TAC BVITMCAUX_ALL2_MAP THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`(i =+ bvl_Number a) (m:num->bvl_v)`;
                          `refs1:(num,(bvl_v)bvl_ref)fmap`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BVITMCAUX_v_rel_update THEN
    ASM_REWRITE_TAC[BVITMCAUX_v_rel_simps];
    ALL_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`(i =+ bvl_Word64 a) (m:num->bvl_v)`;
                          `refs1:(num,(bvl_v)bvl_ref)fmap`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BVITMCAUX_v_rel_update THEN
    ASM_REWRITE_TAC[BVITMCAUX_v_rel_simps]] THEN
  (* Str: a fresh byte array on both sides *)
  ABBREV_TAC `src = minimal ptr. ~(ptr IN FDOM (refs1:(num,(bvl_v)bvl_ref)fmap))` THEN
  ABBREV_TAC `tgt = minimal ptr. ~(ptr IN FDOM (refs2:(num,(bvl_v)bvl_ref)fmap))` THEN
  ABBREV_TAC `ba = bvl_ByteArray T (MAP (word o ORD) (explode a)):(bvl_v)bvl_ref` THEN
  SUBGOAL_THEN `~(src IN FDOM (refs1:(num,(bvl_v)bvl_ref)fmap)) /\
                ~(tgt IN FDOM (refs2:(num,(bvl_v)bvl_ref)fmap)) /\
                ~(tgt IN FRANGE (f:(num,num)fmap))` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["src"; "tgt"] THEN REWRITE_TAC[fresh_ptr_fresh] THEN
    MATCH_MP_TAC fresh_not_in_range_f THEN
    EXISTS_TAC `refs1:(num,(bvl_v)bvl_ref)fmap` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FLOOKUP (f:(num,num)fmap) src = NONE` ASSUME_TAC THENL
   [UNDISCH_TAC `state_ref_rel f refs1 (refs2:(num,(bvl_v)bvl_ref)fmap)` THEN
    REWRITE_TAC[state_ref_rel_def; FLOOKUP_DEF] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:(num,num)fmap) SUBMAP (f |+ (src,tgt))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBMAP_FUPDATE_FLOOKUP]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`(i =+ bvl_RefPtr T src) (m:num->bvl_v)`; `i + 1`;
     `(refs1:(num,(bvl_v)bvl_ref)fmap) |+ (src,ba)`; `v:bvl_v`;
     `refs1':(num,(bvl_v)bvl_ref)fmap`; `(f:(num,num)fmap) |+ (src,tgt)`;
     `(i =+ bvl_RefPtr T tgt) (m':num->bvl_v)`;
     `(refs2:(num,(bvl_v)bvl_ref)fmap) |+ (tgt,ba)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC state_ref_rel_alloc THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "ba" THEN REWRITE_TAC[bvi_tmcProof_ref_rel_ByteArray];
      MATCH_MP_TAC fmap_inj_update THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC BVITMCAUX_v_rel_update THEN CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC v_rel_submap THEN
        EXISTS_TAC `f:(num,num)fmap` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC bvi_tmcProof_v_rel_RefPtr THEN
        REWRITE_TAC[FLOOKUP_UPDATE]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':(num,num)fmap` (X_CHOOSE_THEN `v':bvl_v`
    (X_CHOOSE_THEN `refs2':(num,(bvl_v)bvl_ref)fmap` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`f':(num,num)fmap`; `v':bvl_v`;
                        `refs2':(num,(bvl_v)bvl_ref)fmap`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`f:(num,num)fmap`; `src:num`; `tgt:num`; `ba:(bvl_v)bvl_ref`;
                `refs2:(num,(bvl_v)bvl_ref)fmap`] BVITMCAUX_alloc_fresh) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SUBMAP_TRANS];
    MATCH_MP_TAC only_fresh_trans THEN
    MAP_EVERY EXISTS_TAC [`(f:(num,num)fmap) |+ (src,tgt)`;
                          `(refs2:(num,(bvl_v)bvl_ref)fmap) |+ (tgt,ba)`] THEN
    ASM_REWRITE_TAC[FDOM_FUPDATE] THEN SET_TAC[];
    MATCH_MP_TAC holes_unchanged_except_trans THEN
    MAP_EVERY EXISTS_TAC [`(f:(num,num)fmap) |+ (src,tgt)`;
                          `(refs2:(num,(bvl_v)bvl_ref)fmap) |+ (tgt,ba)`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC holes_still_not_finalised_trans THEN
    MAP_EVERY EXISTS_TAC [`(f:(num,num)fmap) |+ (src,tgt)`;
                          `(refs2:(num,(bvl_v)bvl_ref)fmap) |+ (tgt,ba)`] THEN
    ASM_REWRITE_TAC[]]);;

let do_build_const_v_rel = prove
 (`!l refs1 v refs1' f refs2.
     bvl_do_build_const l refs1 = (v,refs1') /\ state_ref_rel f refs1 refs2 /\
     fmap_inj f ==>
     ?f' v' refs2'.
       bvl_do_build_const l refs2 = (v',refs2') /\ bvi_tmcProof_v_rel f' v v' /\
       state_ref_rel f' refs1' refs2' /\ fmap_inj f' /\ f SUBMAP f' /\
       only_fresh f f' refs2 /\ holes_unchanged_except f refs2 refs2' {} /\
       holes_still_not_finalised f refs2 refs2'`,
  REWRITE_TAC[bvl_do_build_const_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC do_build_v_rel THEN
  MAP_EVERY EXISTS_TAC [`\x:num. bvl_Number (&0)`;
                        `refs1:(num,(bvl_v)bvl_ref)fmap`] THEN
  ASM_REWRITE_TAC[bvi_tmcProof_v_rel_Number]);;

(* ------------------------------------------------------------------------- *)
(* do_app_op_rel: the operations of related values in related states.        *)
(* HOL4 proves it by cases on the operation (suspend/resume); here a few     *)
(* generic tactics and one lemma per family of operations.                   *)
(* ------------------------------------------------------------------------- *)

(* do_app: unfold the semantics of one concrete operation *)
let BVITMCAUX_DOAPP_CONV =
  REWRITE_CONV[bvi_do_app_def; bvi_do_app_aux_def; bvl_do_app_def] THENC
  CASE_REWRITE_CONV[];;

let BVITMCAUX_v_rel_refls = prove
 (`(!f i. bvi_tmcProof_v_rel f (bvl_Number i) (bvl_Number i)) /\
   (!f w. bvi_tmcProof_v_rel f (bvl_Word64 w) (bvl_Word64 w)) /\
   (!f n. bvi_tmcProof_v_rel f (bvl_CodePtr n) (bvl_CodePtr n)) /\
   (!f b. bvi_tmcProof_v_rel f (bvl_Boolv b) (bvl_Boolv b)) /\
   (!f. bvi_tmcProof_v_rel f bvl_Unit bvl_Unit) /\
   (!f n. bvi_tmcProof_v_rel f (bvl_Block n []) (bvl_Block n []))`,
  REWRITE_TAC[bvl_Boolv_def; bvl_Unit_def; bvi_tmcProof_v_rel_Number;
              bvi_tmcProof_v_rel_Word64; bvi_tmcProof_v_rel_CodePtr] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN MATCH_MP_TAC bvi_tmcProof_v_rel_Block THEN
  REWRITE_TAC[ALL2]);;

let BVITMCAUX_op_goal op =
  let tm = `!f vs vs' (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) t v.
    bvi_do_app OP vs s = Rval (v,t) /\
    no_mutcons_op OP /\
    ALL2 (bvi_tmcProof_v_rel f) vs vs' /\
    bvi_tmcProof_state_rel f s s' ==>
    ?f' v' t'.
      bvi_do_app OP vs' s' = Rval (v',t') /\
      bvi_tmcProof_v_rel f' v v' /\
      bvi_tmcProof_state_rel f' t t' /\
      f SUBMAP f' /\
      only_fresh f f' (bvi_state_refs s') /\
      holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t') {} /\
      holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t')` in
  vsubst [op, `OP:clos_op`] tm;;

let BVITMCAUX_CASE_EQS = [list_case_eq; option_case_eq; pair_case_eq; COND_CASE_EQ;
  case_eq "bvl_v"; case_eq "result"; case_eq "error_result"; case_eq "bvl_ref";
  case_eq "eq_result"; case_eq "const_part"; case_eq "thunk_mode";
  case_eq "ffi_result";
  injectivity "result"; distinctness "result"; injectivity "error_result";
  distinctness "error_result"; option_INJ; option_DISTINCT; PAIR_EQ;
  LET_DEF; LET_END_DEF];;

let BVITMCAUX_is_pair_eq th =
  let c = concl th in
  is_eq c && ((is_pair (lhs c) && is_pair (rhs c)) ||
              (try fst(dest_const(rator(lhs c))) = "SOME" &&
                   fst(dest_const(rator(rhs c))) = "SOME"
               with Failure _ -> false));;

(* unfold the source do_app and split it into its successful cases *)
let BVITMCAUX_OP_SPLIT_TAC : tactic =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE BVITMCAUX_CASE_EQS o
    CONV_RULE(LAND_CONV BVITMCAUX_DOAPP_CONV) o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
                         "bvi_do_app" with Failure _ -> false)) THEN
  RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    REWRITE_RULE[PAIR_EQ; option_INJ; option_DISTINCT] o
    check BVITMCAUX_is_pair_eq) THEN RVEQ_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NULL_EQ]) THEN RVEQ_TAC;;

(* the shape of the target arguments *)
let BVITMCAUX_CHANGED_RULE (r:thm->thm) th =
  let th' = r th in if concl th' = concl th then failwith "unchanged" else th';;

let BVITMCAUX_OP_VS_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    BVITMCAUX_CHANGED_RULE
      (REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL; BVITMCAUX_v_rel_simps]) o
    check (BVITMCAUX_head_is "ALL2"))) THEN
  RVEQ_TAC;;

(* for each FLOOKUP f n = SOME m and the state_ref_rel of a state_rel        *)
(* assumption: the related references of n and m                             *)
let BVITMCAUX_REFS_TAC : tactic = fun (asl,w as g) ->
  let srs = mapfilter (fun (_,th) ->
     if BVITMCAUX_head_is "bvi_tmcProof_state_rel" th
     then CONJUNCT1 (REWRITE_RULE[bvi_tmcProof_state_rel_def] th)
     else failwith "") asl in
  let is_fl th =
    let c = concl th in
    is_eq c && (try let l = lhs c in
                    fst(dest_const(fst(strip_comb l))) = "FLOOKUP" &&
                    type_of (rand(rator l)) = `:(num,num)fmap`
                with Failure _ -> false) in
  let fls = filter is_fl (map snd asl) in
  let ths = flat (map (fun sr -> mapfilter (fun fl ->
                MATCH_MP state_ref_rel_lookup (CONJ fl sr)) fls) srs) in
  EVERY (map STRIP_ASSUME_TAC ths) g;;

(* for each bvl_v_to_list x = SOME xs and v_rel f x y: the list of y *)
let BVITMCAUX_V2L_TAC : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  let v2ls = filter (fun th -> try let l = lhs(concl th) in
                       fst(dest_const(fst(strip_comb l))) = "bvl_v_to_list"
                     with Failure _ -> false) ths in
  let vrs = filter (BVITMCAUX_head_is "bvi_tmcProof_v_rel") ths in
  let res = flat (map (fun a -> mapfilter (fun b ->
              MATCH_MP v_to_list_v_rel (CONJ a b)) vrs) v2ls) in
  EVERY (map STRIP_ASSUME_TAC res) g;;

(* the lengths of related lists *)
let BVITMCAUX_LENGTHS_TAC : tactic = fun (asl,w as g) ->
  let ths = mapfilter (fun (_,th) ->
     if BVITMCAUX_head_is "ALL2" th then MATCH_MP LIST_REL_LENGTH th
     else failwith "") asl in
  EVERY (map ASSUME_TAC ths) g;;

let BVITMCAUX_v_rel_Boolv = prove
 (`(!f b y. bvi_tmcProof_v_rel f (bvl_Boolv b) y <=> y = bvl_Boolv b) /\
   (!f b x. bvi_tmcProof_v_rel f x (bvl_Boolv b) <=> x = bvl_Boolv b) /\
   (!f y. bvi_tmcProof_v_rel f bvl_Unit y <=> y = bvl_Unit) /\
   (!f x. bvi_tmcProof_v_rel f x bvl_Unit <=> x = bvl_Unit)`,
  REWRITE_TAC[bvl_Boolv_def; bvl_Unit_def; BVITMCAUX_v_rel_simps; LIST_REL_NIL] THEN
  MESON_TAC[]);;


let BVITMCAUX_EX_REFL = prove
 (`(!a:A. ?x. a = x) /\ (!a:A. ?x. x = a)`,
  MESON_TAC[]);;

let BVITMCAUX_ALL2_EL_INT = prove
 (`!(R:A->B->bool) l1 l2 i.
     ALL2 R l1 l2 /\ &0 <= i /\ i < &(LENGTH l1) ==>
     R (EL (num_of_int i) l1) (EL (num_of_int i) l2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LISTAUX_ALL2_EL THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
    try fst(dest_const(rator(rator(concl th)))) = "int_lt" with Failure _ -> false)) THEN
  UNDISCH_TAC `&0 <= (i:int)` THEN
  SPEC_TAC(`i:int`,`i:int`) THEN REWRITE_TAC[GSYM INT_FORALL_POS] THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM; INT_OF_NUM_LT]);;

(* a state_rel survives a change of the references and a larger renaming *)
let BVITMCAUX_state_rel_refs = prove
 (`!f f' (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) r r'.
     bvi_tmcProof_state_rel f s s' /\ state_ref_rel f' r r' /\ fmap_inj f' /\
     f SUBMAP f' ==>
     bvi_tmcProof_state_rel f' (bvi_state_refs_fupd (K r) s)
                               (bvi_state_refs_fupd (K r') s')`,
  REWRITE_TAC[bvi_tmcProof_state_rel_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `OPTREL (\p p'. FLOOKUP (f:(num,num)fmap) p = SOME p')
                 (bvi_state_global (s:(num#C,FFI)bvi_state))
                 (bvi_state_global (s':(C,FFI)bvi_state))` THEN
  MATCH_MP_TAC OPTREL_MONO THEN REWRITE_TAC[] THEN
  ASM_MESON_TAC[FLOOKUP_SUBMAP]);;


let BVITMCAUX_state_rel_global = prove
 (`!f (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) p.
     bvi_tmcProof_state_rel f s s' /\ bvi_state_global s = SOME p ==>
     ?p'. bvi_state_global s' = SOME p' /\ FLOOKUP f p = SOME p'`,
  REWRITE_TAC[bvi_tmcProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `OPTREL (\p p'. FLOOKUP (f:(num,num)fmap) p = SOME p')
                 (bvi_state_global (s:(num#C,FFI)bvi_state))
                 (bvi_state_global (s':(C,FFI)bvi_state))` THEN
  ASM_REWRITE_TAC[OPTREL_SOME] THEN MESON_TAC[]);;

let BVITMCAUX_state_rel_refs_same = prove
 (`!f (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) r r'.
     bvi_tmcProof_state_rel f s s' /\ state_ref_rel f r r' ==>
     bvi_tmcProof_state_rel f (bvi_state_refs_fupd (K r) s)
                              (bvi_state_refs_fupd (K r') s')`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BVITMCAUX_state_rel_refs THEN
  EXISTS_TAC `f:(num,num)fmap` THEN ASM_REWRITE_TAC[SUBMAP_REFL] THEN
  ASM_MESON_TAC[bvi_tmcProof_state_rel_def]);;

let BVITMCAUX_state_rel_global_fupd = prove
 (`!f (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) p p'.
     bvi_tmcProof_state_rel f s s' /\ FLOOKUP f p = SOME p' ==>
     bvi_tmcProof_state_rel f (bvi_state_global_fupd (K (SOME p)) s)
                              (bvi_state_global_fupd (K (SOME p')) s')`,
  REWRITE_TAC[bvi_tmcProof_state_rel_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[OPTREL_THM]);;

(* the global pointers of related states *)
let BVITMCAUX_GLOBAL_TAC : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  let srs = filter (BVITMCAUX_head_is "bvi_tmcProof_state_rel") ths in
  let gls = filter (fun th -> try let l = lhs(concl th) in
                       fst(dest_const(rator l)) = "bvi_state_global"
                     with Failure _ -> false) ths in
  let res = flat (map (fun a -> mapfilter (fun b ->
              MATCH_MP BVITMCAUX_state_rel_global (CONJ a b)) gls) srs) in
  EVERY (map STRIP_ASSUME_TAC res) g;;

(* updating a reference in the range of f keeps the holes *)
let BVITMCAUX_FRANGE_TAC : tactic = fun (asl,w as g) ->
  let is_fl th =
    let c = concl th in
    is_eq c && (try let l = lhs c in
                    fst(dest_const(fst(strip_comb l))) = "FLOOKUP" &&
                    type_of (rand(rator l)) = `:(num,num)fmap`
                with Failure _ -> false) in
  let fls = filter is_fl (map snd asl) in
  let ths = flat (map (fun fl ->
     [MATCH_MP (INST_TYPE [`:num`,`:A`; `:num`,`:B`; `:bvl_v`,`:C`]
                 holes_unchanged_except_frange_update) fl;
      MATCH_MP (INST_TYPE [`:num`,`:A`; `:num`,`:B`; `:bvl_v`,`:C`]
                 holes_still_not_finalised_frange_update) fl]) fls) in
  EVERY (map ASSUME_TAC ths) g;;


(* all components of a state_rel assumption *)
let BVITMCAUX_STATE_REL_TAC : tactic =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bvi_tmcProof_state_rel_def] o
    check (BVITMCAUX_head_is "bvi_tmcProof_state_rel"));;


let BVITMCAUX_refs_fupd_id = prove
 (`!s:(A,B)bvi_state. bvi_state_refs_fupd (K (bvi_state_refs s)) s = s`,
  REWRITE_TAC[bvi_state_component_equality; bvi_state_INFO.ri_accfupds; K_THM]);;

let do_app_op_finalise_rel = prove
 (`!v1 refs v1' v2 f (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state).
     bvi_finalise_cons v1 (bvi_state_refs s) = SOME (v2,refs) /\
     bvi_tmcProof_state_rel f s s' /\ bvi_tmcProof_v_rel f v1 v1' ==>
     ?f' v2' refs'.
       bvi_finalise_cons v1' (bvi_state_refs s') = SOME (v2',refs') /\
       f SUBMAP f' /\ bvi_tmcProof_v_rel f' v2 v2' /\
       bvi_tmcProof_state_rel f' (bvi_state_refs_fupd (K refs) s)
                                 (bvi_state_refs_fupd (K refs') s') /\
       only_fresh f f' (bvi_state_refs s') /\
       holes_unchanged_except f (bvi_state_refs s') refs' {} /\
       holes_still_not_finalised f (bvi_state_refs s') refs'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `f:(num,num)fmap` THEN
  REWRITE_TAC[SUBMAP_REFL; only_fresh_refl] THEN
  CASES_ON `v1:bvl_v` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BVITMCAUX_v_rel_simps]) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THENL
   (replicate
     (FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
        "bvi_finalise_cons" with Failure _ -> false)) THEN
      REWRITE_TAC[bvi_finalise_cons_def; option_INJ; PAIR_EQ] THEN
      STRIP_TAC THEN RVEQ_TAC THEN
      REWRITE_TAC[bvi_finalise_cons_def; option_INJ; PAIR_EQ] THEN
      REWRITE_TAC[MESON[] `!(a:A) (b:B) P. (?v t. (a = v /\ b = t) /\ P v t) <=> P a b`] THEN
      ASM_REWRITE_TAC[BVITMCAUX_refs_fupd_id; holes_unchanged_except_refl;
                      holes_still_not_finalised_refl; BVITMCAUX_v_rel_simps] THEN
      ASM_MESON_TAC[]) 4 @
    [FIRST_ASSUM(fun fl -> FIRST_ASSUM(fun sr ->
       STRIP_ASSUME_TAC (MATCH_MP state_ref_rel_lookup
         (CONJ fl (CONJUNCT1 (REWRITE_RULE[bvi_tmcProof_state_rel_def] sr)))))) THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
        "bvi_finalise_cons" with Failure _ -> false)) THEN
     ASM_REWRITE_TAC[bvi_finalise_cons_def] THEN
     UNDISCH_TAC `bvi_tmcProof_ref_rel f v w` THEN
     CASES_ON `v:(bvl_v)bvl_ref` THEN REWRITE_TAC[BVITMCAUX_ref_rel_simps] THEN
     STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
     REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
     REWRITE_TAC[MESON[] `!(a:A) (b:B) P. (?v t. (a = v /\ b = t) /\ P v t) <=> P a b`] THEN
     ASM_REWRITE_TAC[BVITMCAUX_refs_fupd_id; holes_unchanged_except_refl;
                     holes_still_not_finalised_refl; BVITMCAUX_v_rel_simps] THEN
     ASM_MESON_TAC[]]));;

let dest_thunk_not_thunk_rel = prove
 (`!v v' refs refs' f.
     bvl_dest_thunk v refs = bvl_NotThunk /\ bvi_tmcProof_v_rel f v v' /\
     state_ref_rel f refs refs' ==>
     bvl_dest_thunk v' refs' = bvl_NotThunk`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CASES_ON `v:bvl_v` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BVITMCAUX_v_rel_simps]) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THEN REWRITE_TAC[bvl_dest_thunk_def] THEN
  FIRST_ASSUM(fun fl -> FIRST_ASSUM(fun sr ->
    MP_TAC (MATCH_MP state_ref_rel_lookup (CONJ fl sr)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `rv:(bvl_v)bvl_ref` (X_CHOOSE_THEN `rw:(bvl_v)bvl_ref`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
     "bvl_dest_thunk" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[bvl_dest_thunk_def] THEN
  UNDISCH_TAC `bvi_tmcProof_ref_rel f rv rw` THEN
  CASES_ON `rv:(bvl_v)bvl_ref` THEN REWRITE_TAC[BVITMCAUX_ref_rel_simps] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REPEAT TOP_CASE_TAC THEN CASE_REWRITE_TAC[]);;

let BVITMCAUX_bad_thunk_rel = prove
 (`!m v v' refs refs' f.
     ~bvl_bad_thunk_update m v refs /\ bvi_tmcProof_v_rel f v v' /\
     state_ref_rel f refs refs' ==>
     ~bvl_bad_thunk_update m v' refs'`,
  REWRITE_TAC[bvl_bad_thunk_update_def; DE_MORGAN_THM] THEN
  MESON_TAC[dest_thunk_not_thunk_rel]);;

let BVITMCAUX_state_rel_ffi = prove
 (`!f (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) x.
     bvi_tmcProof_state_rel f s s' ==>
     bvi_tmcProof_state_rel f (bvi_state_ffi_fupd (K x) s)
                              (bvi_state_ffi_fupd (K x) s')`,
  REWRITE_TAC[bvi_tmcProof_state_rel_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* forward facts: thunk updates, labels *)
let BVITMCAUX_FWD_TAC : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  let srs = filter (BVITMCAUX_head_is "bvi_tmcProof_state_rel") ths in
  let vrs = filter (BVITMCAUX_head_is "bvi_tmcProof_v_rel") ths in
  let bads = filter (fun th -> is_neg(concl th) &&
               (try fst(dest_const(fst(strip_comb(rand(concl th))))) =
                    "bvl_bad_thunk_update" with Failure _ -> false)) ths in
  let doms = filter (fun th -> try let c = concl th in
               fst(dest_const(fst(strip_comb c))) = "IN" &&
               fst(dest_const(fst(strip_comb(rand c)))) = "domain"
               with Failure _ -> false) ths in
  let r1 = flat (map (fun sr ->
             let srr = CONJUNCT1 (REWRITE_RULE[bvi_tmcProof_state_rel_def] sr) in
             flat (map (fun b -> mapfilter (fun vr ->
               MATCH_MP BVITMCAUX_bad_thunk_rel (CONJ b (CONJ vr srr))) vrs) bads))
             srs) in
  let r2 = flat (map (fun sr ->
             let sub = REWRITE_RULE[SUBSET] (MATCH_MP bvi_tmcProof_code_rel_domain
                         (MATCH_MP bvi_tmcProof_state_rel_code_rel sr)) in
             mapfilter (fun d -> MATCH_MP sub d) doms) srs) in
  EVERY (map ASSUME_TAC (r1 @ r2)) g;;

let BVITMCAUX_OP_SIMPS =
  [bvl_to_bvi_id; bvl_to_bvi_refs; SUBMAP_REFL; only_fresh_refl;
   holes_unchanged_except_refl; holes_still_not_finalised_refl;
   BVITMCAUX_v_rel_Boolv; BVITMCAUX_v_rel_refls; BVITMCAUX_v_rel_simps;
   BVITMCAUX_ref_rel_simps; LIST_REL_NIL; LIST_REL_CONS1; bvi_bvi_to_bvl_refs;
   LISTAUX_ALL2_EL; bvi_tmcProof_list_to_v_v_rel; LIST_REL_APPEND_suff;
   EVERY2_TAKE; EVERY2_DROP; state_ref_rel_update; BVITMCAUX_state_rel_refs_same;
   EVERY2_LUPDATE_same; BVITMCAUX_state_rel_global_fupd; BVITMCAUX_EX_REFL;
   INT_OF_NUM_EQ; VAL_EQ; BVITMCAUX_ALL2_EL_INT; bvl_to_bvi_with_refs;
   bvi_to_bvl_to_bvi_with_ffi; BVITMCAUX_state_rel_ffi];;

(* the generic case: f' = f *)
let BVITMCAUX_OP_SAME_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[bvi_bvi_to_bvl_refs; DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
  BVITMCAUX_FWD_TAC THEN
  BVITMCAUX_GLOBAL_TAC THEN BVITMCAUX_REFS_TAC THEN BVITMCAUX_V2L_TAC THEN
  GVS BVITMCAUX_OP_SIMPS THEN BVITMCAUX_LENGTHS_TAC THEN GVS[] THEN
  BVITMCAUX_FRANGE_TAC THEN BVITMCAUX_STATE_REL_TAC THEN
  EXISTS_TAC `f:(num,num)fmap` THEN CONV_TAC BVITMCAUX_DOAPP_CONV THEN
  SIMP BVITMCAUX_OP_SIMPS;;

let BVITMCAUX_OP_EQUAL_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[bvi_bvi_to_bvl_refs]) THEN
  BVITMCAUX_STATE_REL_TAC THEN
  SUBGOAL_THEN `bvl_do_eq (bvi_state_refs (s':(C,FFI)bvi_state)) h' h'' = Eq_val a'`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "bvl_do_eq"
      with Failure _ -> false)) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC (CONJUNCT1 do_eq_v_rel) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `f:(num,num)fmap` THEN CONV_TAC BVITMCAUX_DOAPP_CONV THEN
  SIMP BVITMCAUX_OP_SIMPS;;

let BVITMCAUX_OP_BUILD_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[bvi_bvi_to_bvl_refs]) THEN
  BVITMCAUX_STATE_REL_TAC THEN
  FIRST_X_ASSUM(fun th ->
    if BVITMCAUX_head_is "=" th &&
       (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "bvl_do_build_const"
        with Failure _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(fun sr -> FIRST_ASSUM(fun fi ->
    MP_TAC (MATCH_MP do_build_const_v_rel (CONJ th (CONJ sr fi)))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `f':(num,num)fmap` (X_CHOOSE_THEN `v':bvl_v`
    (X_CHOOSE_THEN `refs2':(num,(bvl_v)bvl_ref)fmap` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `f':(num,num)fmap` THEN CONV_TAC BVITMCAUX_DOAPP_CONV THEN
  ASM_REWRITE_TAC[bvi_bvi_to_bvl_refs; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvl_to_bvi_refs; injectivity "result"; PAIR_EQ] THEN
  REWRITE_TAC[MESON[] `!(a:A) (b:B) P. (?v t. (a = v /\ b = t) /\ P v t) <=> P a b`] THEN
  ASM_REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM] THEN
  MATCH_MP_TAC BVITMCAUX_state_rel_refs THEN EXISTS_TAC `f:(num,num)fmap` THEN
  ASM_REWRITE_TAC[];;

let BVITMCAUX_do_int_app_v_rel = prove
 (`!op vs res vs' f.
     bvl_do_int_app op vs = SOME res /\ ALL2 (bvi_tmcProof_v_rel f) vs vs' ==>
     vs' = vs /\ bvi_tmcProof_v_rel f res res`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSSEMAUX_do_int_app_some) THEN
  RVEQ_TAC THEN REWRITE_TAC[BVITMCAUX_v_rel_refls] THEN
  MATCH_MP_TAC BVITMCAUX_ALL2_flat THEN EXISTS_TAC `f:(num,num)fmap` THEN
  ASM_REWRITE_TAC[ALL] THEN MESON_TAC[]);;

(* IntOp and WordOp: the arguments are numbers and words, related exactly *)
let BVITMCAUX_OP_INTWORD_TAC : tactic =
  (FIRST_ASSUM(fun ia -> FIRST_ASSUM(fun a2 ->
     STRIP_ASSUME_TAC (MATCH_MP BVITMCAUX_do_int_app_v_rel (CONJ ia a2)))) ORELSE
   FIRST_ASSUM(fun ia -> FIRST_ASSUM(fun a2 ->
     STRIP_ASSUME_TAC (MATCH_MP do_word_app_v_rel (CONJ ia a2)) THEN
     ASSUME_TAC (MATCH_MP do_word_app_v_rel_refl ia)))) THEN
  RVEQ_TAC THEN
  EXISTS_TAC `f:(num,num)fmap` THEN CONV_TAC BVITMCAUX_DOAPP_CONV THEN
  SIMP BVITMCAUX_OP_SIMPS THEN ASM_MESON_TAC[do_word_app_v_rel_refl];;

let BVITMCAUX_submap_fresh = prove
 (`!f (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) x.
     bvi_tmcProof_state_rel f s s' ==>
     f SUBMAP (f |+ ((minimal ptr. ~(ptr IN FDOM (bvi_state_refs s))),x))`,
  REWRITE_TAC[bvi_tmcProof_state_rel_def; state_ref_rel_def] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBMAP_FUPDATE_FLOOKUP; FLOOKUP_DEF] THEN
  ASM_REWRITE_TAC[LEAST_NOTIN_FDOM]);;

(* allocation of a new reference on both sides *)
let BVITMCAUX_alloc_goal = prove
 (`!f (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) b rv rw.
     bvi_tmcProof_state_rel f s s' /\
     bvi_tmcProof_ref_rel
       (f |+ ((minimal ptr. ~(ptr IN FDOM (bvi_state_refs s))),
              (minimal ptr. ~(ptr IN FDOM (bvi_state_refs s'))))) rv rw ==>
     ?f'.
       bvi_tmcProof_v_rel f'
         (bvl_RefPtr b (minimal ptr. ~(ptr IN FDOM (bvi_state_refs s))))
         (bvl_RefPtr b (minimal ptr. ~(ptr IN FDOM (bvi_state_refs s')))) /\
       bvi_tmcProof_state_rel f'
         (bvi_state_refs_fupd
            (K (bvi_state_refs s |+
                ((minimal ptr. ~(ptr IN FDOM (bvi_state_refs s))),rv))) s)
         (bvi_state_refs_fupd
            (K (bvi_state_refs s' |+
                ((minimal ptr. ~(ptr IN FDOM (bvi_state_refs s'))),rw))) s') /\
       f SUBMAP f' /\
       only_fresh f f' (bvi_state_refs s') /\
       holes_unchanged_except f (bvi_state_refs s')
         (bvi_state_refs s' |+ ((minimal ptr. ~(ptr IN FDOM (bvi_state_refs s'))),rw))
         {} /\
       holes_still_not_finalised f (bvi_state_refs s')
         (bvi_state_refs s' |+ ((minimal ptr. ~(ptr IN FDOM (bvi_state_refs s'))),rw))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `src = minimal ptr. ~(ptr IN FDOM (bvi_state_refs (s:(num#C,FFI)bvi_state)))` THEN
  ABBREV_TAC `tgt = minimal ptr. ~(ptr IN FDOM (bvi_state_refs (s':(C,FFI)bvi_state)))` THEN
  MP_TAC(SPECL [`f:(num,num)fmap`; `s:(num#C,FFI)bvi_state`; `s':(C,FFI)bvi_state`;
                `src:num`; `tgt:num`; `rv:(bvl_v)bvl_ref`; `rw:(bvl_v)bvl_ref`]
               state_rel_alloc) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["src"; "tgt"] THEN
    REWRITE_TAC[LEAST_NOTIN_FDOM] THEN MATCH_MP_TAC fresh_not_in_range_f THEN
    EXISTS_TAC `bvi_state_refs (s:(num#C,FFI)bvi_state)` THEN
    ASM_MESON_TAC[bvi_tmcProof_state_rel_def];
    ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `(f:(num,num)fmap) |+ (src,tgt)` THEN
  ASM_REWRITE_TAC[BVITMCAUX_v_rel_simps] THEN MESON_TAC[]);;

(* the arguments allocated are related under the extended renaming *)
let BVITMCAUX_OP_ALLOC_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[LET_DEF; LET_END_DEF; bvi_bvi_to_bvl_refs;
                              injectivity "result"; PAIR_EQ; option_INJ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN BVITMCAUX_FWD_TAC THEN
  REWRITE_TAC[bvl_to_bvi_refs; bvi_bvi_to_bvl_refs] THEN
  CONV_TAC BVITMCAUX_DOAPP_CONV THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; bvi_bvi_to_bvl_refs; bvl_to_bvi_refs;
                  INT_OF_NUM_EQ; VAL_EQ; BVITMCAUX_EX_REFL] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvi_bvi_to_bvl_refs; bvl_to_bvi_refs; bvi_state_INFO.ri_accfupds; K_THM;
    MESON[] `!(a:A) (b:B) P. (?v t. (a = v /\ b = t) /\ P v t) <=> P a b`] THEN
  MATCH_MP_TAC BVITMCAUX_alloc_goal THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BVITMCAUX_submap_fresh o
    check (BVITMCAUX_head_is "bvi_tmcProof_state_rel")) THEN
  REWRITE_TAC[BVITMCAUX_ref_rel_simps; injectivity "bvl_ref";
              LIST_REL_REPLICATE_same] THEN
  REWRITE_TAC[MESON[] `!(a:A) P. (?x. a = x /\ P x) <=> P a`] THEN
  REWRITE_TAC[LIST_REL_REPLICATE_same] THEN
  TRY(MATCH_MP_TAC (GEN_ALL list_rel_submap)) THEN
  TRY DISCH_TAC THEN TRY(MATCH_MP_TAC v_rel_submap) THEN
  EXISTS_TAC `f:(num,num)fmap` THEN ASM_REWRITE_TAC[];;

let BVITMCAUX_OP_MUTCONS_TAC : tactic =
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[no_mutcons_op_def] o
    check (BVITMCAUX_head_is "no_mutcons_op")) THEN
  MESON_TAC[];;

let BVITMCAUX_OP_FINALISE_TAC : tactic =
  FIRST_ASSUM(fun fc -> FIRST_ASSUM(fun sr -> FIRST_ASSUM(fun vr ->
    MP_TAC (MATCH_MP do_app_op_finalise_rel (CONJ fc (CONJ sr vr)))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `f':(num,num)fmap` (X_CHOOSE_THEN `v2':bvl_v`
    (X_CHOOSE_THEN `refs2':(num,(bvl_v)bvl_ref)fmap` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `f':(num,num)fmap` THEN CONV_TAC BVITMCAUX_DOAPP_CONV THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[MESON[] `!(a:A) (b:B) P. (?v t. (a = v /\ b = t) /\ P v t) <=> P a b`] THEN
  ASM_REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM];;

(* do_app_op_rel, one family of operations at a time (HOL4 suspends and     *)
(* resumes the cases of one proof)                                           *)

let BVITMCAUX_OP_ALL_TAC : tactic =
  BVITMCAUX_OP_SPLIT_TAC THEN BVITMCAUX_OP_VS_TAC THEN
  FIRST [BVITMCAUX_OP_SAME_TAC THEN NO_TAC; BVITMCAUX_OP_EQUAL_TAC THEN NO_TAC;
         BVITMCAUX_OP_BUILD_TAC THEN NO_TAC; BVITMCAUX_OP_INTWORD_TAC THEN NO_TAC;
         BVITMCAUX_OP_ALLOC_TAC THEN NO_TAC; BVITMCAUX_OP_MUTCONS_TAC THEN NO_TAC;
         BVITMCAUX_OP_FINALISE_TAC THEN NO_TAC];;

let BVITMCAUX_op_label = prove
 (BVITMCAUX_op_goal `clos_Label n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN BVITMCAUX_OP_ALL_TAC);;

let BVITMCAUX_op_ffi = prove
 (BVITMCAUX_op_goal `clos_FFI n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN BVITMCAUX_OP_ALL_TAC);;

let BVITMCAUX_op_int = prove
 (BVITMCAUX_op_goal `IntOp i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CASES_ON `i:int_op` THEN
  BVITMCAUX_OP_ALL_TAC);;

let BVITMCAUX_op_word = prove
 (BVITMCAUX_op_goal `WordOp w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CASES_ON `w:word_op` THEN
  BVITMCAUX_OP_ALL_TAC);;

let BVITMCAUX_op_block = prove
 (BVITMCAUX_op_goal `BlockOp b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CASES_ON `b:block_op` THEN
  BVITMCAUX_OP_ALL_TAC);;

let BVITMCAUX_op_glob = prove
 (BVITMCAUX_op_goal `GlobOp g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CASES_ON `g:glob_op` THEN
  BVITMCAUX_OP_ALL_TAC);;

let BVITMCAUX_op_mem = prove
 (BVITMCAUX_op_goal `MemOp m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CASES_ON `m:mem_op` THEN
  BVITMCAUX_OP_ALL_TAC);;

let BVITMCAUX_op_thunk = prove
 (BVITMCAUX_op_goal `clos_ThunkOp th`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CASES_ON `th:thunk_op` THEN
  BVITMCAUX_OP_ALL_TAC);;

let BVITMCAUX_compile_each_head = prove
 (`!n k (p:num#bvi_exp) rest n1 ys.
     bvi_tmc_compile_each n (CONS (k,p) rest) = (n1,ys) ==>
     ?w ys'. ys = CONS (k,w) ys'`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `p:num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `exp:bvi_exp` SUBST1_TAC)) THEN
  REWRITE_TAC[bvi_tmc_compile_each_def] THEN
  CASES_ON `bvi_tmc_compile_exp k n arity exp` THEN FS[] THEN
  REPEAT PAIRARG_TAC THEN FS[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[CONS_11] THEN MESON_TAC[]);;

let BVITMCAUX_state_co_shift = prove
 (`!f (co:num->(S#C)#P) k.
     shift_seq k (state_co (f:S->P->T#Q) co) = state_co f (shift_seq k co)`,
  REWRITE_TAC[FUN_EQ_THM; shift_seq_def; state_co_def]);;

(* the names of an input program at least bvl_num_stubs are not in the      *)
(* namespace of the generated workers                                        *)
let BVITMCAUX_input_names = prove
 (`!next (prog:(num#A#bvi_exp)list) nm.
     bvi_tmcProof_input_condition next prog /\
     nm MOD bvl_to_bvi_namespaces = 3 /\ bvl_num_stubs <= nm ==>
     ~MEM nm (MAP FST prog)`,
  REWRITE_TAC[bvi_tmcProof_input_condition_def; GSYM ALL_MEM; MEM_FILTER;
              o_THM; MEM_MAP] THEN
  MESON_TAC[]);;

let BVITMCAUX_install_disjoint = prove
 (`!c1:(num#bvi_exp)spt c2 state0 progs0 state1 progs1.
     bvi_tmcProof_namespace_rel c1 c2 /\
     (!n. n IN domain c2 /\ n MOD bvl_to_bvi_namespaces = 3 ==> n < state0) /\
     DISJOINT (domain c1) (set_of_list (MAP FST progs0)) /\
     bvi_tmcProof_input_condition state0 progs0 /\
     bvi_tmc_compile_each state0 progs0 = (state1,progs1) ==>
     DISJOINT (domain c2) (set_of_list (MAP FST progs1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IN_DISJOINT; IN_SET_OF_LIST; NOT_EXISTS_THM] THEN
  X_GEN_TAC `nn:num` THEN STRIP_TAC THEN
  MP_TAC(INST [`state0:num`,`n:num`; `progs0:(num#num#bvi_exp)list`,`xs:(num#num#bvi_exp)list`;
               `state1:num`,`n1:num`; `progs1:(num#num#bvi_exp)list`,`ys:(num#num#bvi_exp)list`;
               `nn:num`,`e:num`] bvi_tmcProof_compile_each_MEM) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bvi_tmcProof_input_condition_def] o
    check (BVITMCAUX_head_is "bvi_tmcProof_input_condition")) THEN
  ASM_CASES_TAC `nn MOD bvl_to_bvi_namespaces = 3 /\ bvl_num_stubs <= nn` THENL
   [SUBGOAL_THEN `~MEM nn (MAP FST (progs0:(num#num#bvi_exp)list))` ASSUME_TAC THENL
     [MATCH_MP_TAC BVITMCAUX_input_names THEN EXISTS_TAC `state0:num` THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `nn < state0` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `nn IN domain (c1:(num#bvi_exp)spt)` ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_tmcProof_namespace_rel (c1:(num#bvi_exp)spt) c2` THEN
    REWRITE_TAC[bvi_tmcProof_namespace_rel_def] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LE]) THEN
    ASM_MESON_TAC[NOT_LE]; ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `DISJOINT (domain (c1:(num#bvi_exp)spt))
                   (set_of_list (MAP FST (progs0:(num#num#bvi_exp)list)))` THEN
    REWRITE_TAC[IN_DISJOINT; IN_SET_OF_LIST] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `~(nn MOD bvl_to_bvi_namespaces = 3 /\ bvl_num_stubs <= nn)` THEN
    ASM_REWRITE_TAC[BVITMCAUX_MOD_NS] THEN
    UNDISCH_TAC `bvl_num_stubs <= state0` THEN UNDISCH_TAC `state0 <= nn` THEN
    ARITH_TAC]);;

let BVITMCAUX_install_bound = prove
 (`!c2:(num#bvi_exp)spt state0 progs0 state1 progs1.
     (!n. n IN domain c2 /\ n MOD bvl_to_bvi_namespaces = 3 ==> n < state0) /\
     bvi_tmcProof_input_condition state0 progs0 /\
     bvi_tmc_compile_each state0 progs0 = (state1,progs1) ==>
     !n. n IN domain (union c2 (fromAList progs1)) /\
         n MOD bvl_to_bvi_namespaces = 3 ==> n < state1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvi_tmcProof_compile_each_next_mono) THEN
  REWRITE_TAC[domain_union; IN_UNION; domain_fromAList; IN_SET_OF_LIST] THEN
  X_GEN_TAC `nn:num` THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `nn:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(INST [`state0:num`,`n:num`; `progs0:(num#num#bvi_exp)list`,`xs:(num#num#bvi_exp)list`;
               `state1:num`,`n1:num`; `progs1:(num#num#bvi_exp)list`,`ys:(num#num#bvi_exp)list`;
               `nn:num`,`e:num`] bvi_tmcProof_compile_each_MEM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `bvl_num_stubs <= nn` THENL
   [ASM_MESON_TAC[BVITMCAUX_input_names]; ALL_TAC] THEN
  UNDISCH_TAC `bvi_tmcProof_input_condition state0 (progs0:(num#num#bvi_exp)list)` THEN
  REWRITE_TAC[bvi_tmcProof_input_condition_def] THEN STRIP_TAC THEN
  UNDISCH_TAC `~(bvl_num_stubs <= nn)` THEN UNDISCH_TAC `bvl_num_stubs <= state0` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let BVITMCAUX_mentions s th =
  can (find_term (fun t -> try fst(dest_const t) = s with Failure _ -> false))
      (concl th);;

(* the source oracle after the split of an Install *)
let BVITMCAUX_ORACLE0 = `bvi_state_compile_oracle (s:(num#C,FFI)bvi_state) 0 =
  (state0,cfg0),CONS (x''':num,y''':num#bvi_exp) a1''''`;;

(* HOL4 Resume do_app_op_rel[Install] *)
let BVITMCAUX_op_install = prove
 (BVITMCAUX_op_goal `clos_Install`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o CONV_RULE(LAND_CONV (REWRITE_CONV[bvi_do_app_def; bvi_do_install_def]
     THENC CASE_REWRITE_CONV[])) o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
                         "bvi_do_app" with Failure _ -> false)) THEN
   DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE BVITMCAUX_CASE_EQS) THEN
   RVEQ_TAC THEN
   REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
     REWRITE_RULE[PAIR_EQ; option_INJ; option_DISTINCT] o
     check BVITMCAUX_is_pair_eq) THEN RVEQ_TAC) THEN
   BVITMCAUX_OP_VS_TAC) THEN
  (RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
   FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
   RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[BVITMCAUX_v_rel_simps]) THEN RVEQ_TAC THEN
   SUBGOAL_THEN `bvl_v_to_bytes h' = SOME (x':byte list) /\ bvl_v_to_words h'' = SOME (x'':int64 list)`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[v_to_bytes_v_rel; v_to_words_v_rel]; ALL_TAC] THEN
   BVITMCAUX_STATE_REL_TAC THEN
   MP_TAC(ISPEC `x:num#C` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `state0:num` (X_CHOOSE_THEN `cfg0:C` SUBST_ALL_TAC)) THEN
   MP_TAC(ISPECL [`state0:num`; `CONS (x''':num,y''':num#bvi_exp) a1''''`] (MESON[PAIR_SURJECTIVE]
     `!n p. ?n1 p1. bvi_tmc_compile_each n p = (n1,p1)`)) THEN
   DISCH_THEN(X_CHOOSE_THEN `state1:num` (X_CHOOSE_THEN `progs1:(num#num#bvi_exp)list`
     ASSUME_TAC))) THEN
  (SUBGOAL_THEN `?cfg1:C. bvi_state_compile (s':(C,FFI)bvi_state) cfg0 progs1 = SOME (x',x'',cfg1) /\
                 FST (shift_seq 1 (bvi_state_compile_oracle (s:(num#C,FFI)bvi_state)) 0) = (state1,cfg1)`
     STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `bvi_state_compile (s:(num#C,FFI)bvi_state) (state0,cfg0) (CONS (x''',y''') a1'''') =
                  SOME (x',x'',FST (shift_seq 1 (bvi_state_compile_oracle s) 0))` THEN
     ASM_REWRITE_TAC[state_cc_def] THEN CASE_REWRITE_TAC[] THEN
     REWRITE_TAC[option_case_eq; pair_case_eq; option_DISTINCT; option_INJ; PAIR_EQ] THEN
     STRIP_TAC THEN RVEQ_TAC THEN
     UNDISCH_TAC `bvi_tmc_compile_each state0 (CONS (x''',y''') a1'''') = x'''',y'` THEN
     ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
     EXISTS_TAC `y'''':C` THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `bvi_tmcProof_input_condition state0 (CONS (x''':num,y''':num#bvi_exp) a1'''')`
     ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
       BVITMCAUX_mentions "bvi_tmcProof_input_condition" th)) THEN
     REWRITE_TAC[ASSUME BVITMCAUX_ORACLE0] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `!n. n IN domain (bvi_state_code (s':(C,FFI)bvi_state)) /\
                     n MOD bvl_to_bvi_namespaces = 3 ==> n < state0` ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
       BVITMCAUX_mentions "bvi_state_compile_oracle" th &&
       BVITMCAUX_mentions "domain" th)) THEN
     REWRITE_TAC[ASSUME BVITMCAUX_ORACLE0; FST];
     ALL_TAC] THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP BVITMCAUX_compile_each_head o
     check (BVITMCAUX_mentions "bvi_tmc_compile_each")) THEN
   DISCH_THEN(X_CHOOSE_THEN `w:num#bvi_exp` (X_CHOOSE_THEN `rest1:(num#num#bvi_exp)list`
     SUBST_ALL_TAC))) THEN
  (SUBGOAL_THEN `DISJOINT (domain (bvi_state_code (s':(C,FFI)bvi_state)))
                   (set_of_list (MAP FST (CONS (x''':num,w:num#bvi_exp) rest1)))`
     ASSUME_TAC THENL
    [MATCH_MP_TAC BVITMCAUX_install_disjoint THEN
     MAP_EVERY EXISTS_TAC [`bvi_state_code (s:(num#C,FFI)bvi_state)`; `state0:num`;
       `CONS (x''':num,y''':num#bvi_exp) a1''''`; `state1:num`] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `ALL_DISTINCT (MAP FST (CONS (x''':num,w:num#bvi_exp) rest1)) /\
                 ALL (bvi_tmcProof_free_names state1 o FST) (CONS (x''',w) rest1)`
     STRIP_ASSUME_TAC THENL
    [MATCH_MP_TAC (INST [`state0:num`,`n:num`;
       `CONS (x''':num,y''':num#bvi_exp) a1''''`,`xs:(num#num#bvi_exp)list`;
       `state1:num`,`n1:num`] bvi_tmcProof_compile_each_ALL_DISTINCT) THEN
     ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `bvi_tmcProof_input_condition state0 (CONS (x''':num,y''':num#bvi_exp) a1'''')` THEN
     SIMP_TAC[bvi_tmcProof_input_condition_def];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `bvi_state_compile_oracle (s':(C,FFI)bvi_state) 0 =
                 (cfg0, CONS (x''':num,w:num#bvi_exp) rest1)` ASSUME_TAC THENL
    [FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
       lhs(concl th) = `bvi_state_compile_oracle (s':(C,FFI)bvi_state)`)) THEN
     REWRITE_TAC[state_co_def; ASSUME BVITMCAUX_ORACLE0] THEN CASE_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `FST (shift_seq 1 (bvi_state_compile_oracle (s':(C,FFI)bvi_state)) 0) = cfg1`
     ASSUME_TAC THENL
    [UNDISCH_TAC `FST (shift_seq 1 (bvi_state_compile_oracle (s:(num#C,FFI)bvi_state)) 0) =
                  state1,cfg1` THEN
     REWRITE_TAC[shift_seq_def] THEN
     FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
       lhs(concl th) = `bvi_state_compile_oracle (s':(C,FFI)bvi_state)`)) THEN
     REWRITE_TAC[FST_state_co] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SND];
     ALL_TAC]) THEN
  (EXISTS_TAC `f:(num,num)fmap` THEN
   REWRITE_TAC[bvi_do_app_def; bvi_do_install_def; LET_DEF; LET_END_DEF] THEN
   CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THEN
  (REWRITE_TAC[MESON[] `!(a:A) (b:B) P. (?v t. (a = v /\ b = t) /\ P v t) <=> P a b`] THEN
   REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM; BVITMCAUX_v_rel_refls; SUBMAP_REFL;
     only_fresh_refl; holes_unchanged_except_refl; holes_still_not_finalised_refl] THEN
   UNDISCH_TAC `bvi_tmcProof_input_condition state0 (CONS (x''':num,y''':num#bvi_exp) a1'''')` THEN
   DISCH_THEN(fun th -> ASSUME_TAC th THEN
     STRIP_ASSUME_TAC(REWRITE_RULE[bvi_tmcProof_input_condition_def] th)) THEN
   SUBGOAL_THEN `DISJOINT (domain (fromAList (CONS (x''':num,w:num#bvi_exp) rest1)))
                  (domain (bvi_state_code (s':(C,FFI)bvi_state)))` ASSUME_TAC THENL
    [ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[domain_fromAList]; ALL_TAC] THEN
   REWRITE_TAC[bvi_tmcProof_state_rel_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
   ASM_REWRITE_TAC[BVITMCAUX_state_co_shift] THEN REPEAT CONJ_TAC)
  THENL
   [(MATCH_MP_TAC bvi_tmcProof_code_rel_union THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC (INST [`state0:num`,`next:num`; `state1:num`,`next1:num`]
     bvi_tmcProof_compile_each_code_rel) THEN ASM_REWRITE_TAC[]);
    (MATCH_MP_TAC bvi_tmcProof_namespace_rel_union THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC (INST [`state0:num`,`next:num`; `state1:num`,`next1:num`]
     bvi_tmcProof_compile_each_namespace_rel) THEN ASM_REWRITE_TAC[]);
    (GEN_TAC THEN REWRITE_TAC[shift_seq_def] THEN
   FIRST_ASSUM(ACCEPT_TAC o SPEC `n + 1` o check (fun th -> is_forall(concl th) &&
       BVITMCAUX_mentions "bvi_tmcProof_input_condition" th)));
    (ASM_REWRITE_TAC[FST] THEN MATCH_MP_TAC BVITMCAUX_install_bound THEN
   MAP_EVERY EXISTS_TAC [`state0:num`; `CONS (x''':num,y''':num#bvi_exp) a1''''`] THEN
   ASM_REWRITE_TAC[])]);;

let do_app_op_rel = prove
 (`!f op vs vs' (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) t v.
     bvi_do_app op vs s = Rval (v,t) /\
     no_mutcons_op op /\
     ALL2 (bvi_tmcProof_v_rel f) vs vs' /\
     bvi_tmcProof_state_rel f s s' ==>
     ?f' v' t'.
       bvi_do_app op vs' s' = Rval (v',t') /\
       bvi_tmcProof_v_rel f' v v' /\
       bvi_tmcProof_state_rel f' t t' /\
       f SUBMAP f' /\
       only_fresh f f' (bvi_state_refs s') /\
       holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t') {} /\
       holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t')`,
  REPEAT GEN_TAC THEN CASES_ON `op:clos_op` THEN
  FIRST (map MATCH_ACCEPT_TAC
    [BVITMCAUX_op_label; BVITMCAUX_op_ffi; BVITMCAUX_op_int; BVITMCAUX_op_word;
     BVITMCAUX_op_block; BVITMCAUX_op_glob; BVITMCAUX_op_mem;
     BVITMCAUX_op_install; BVITMCAUX_op_thunk]));;

let do_app_op_err_rel = prove
 (`bvi_do_app (clos_FFI i) vs (u:(num#C,FFI)bvi_state) = Rerr (Rabort (Rffi_error e)) /\
   bvi_tmcProof_state_rel f u (u':(C,FFI)bvi_state) /\
   ALL2 (bvi_tmcProof_v_rel f) vs vs' ==>
   bvi_do_app (clos_FFI i) vs' u' = Rerr (Rabort (Rffi_error e))`,
  STRIP_TAC THEN BVITMCAUX_OP_SPLIT_TAC THEN BVITMCAUX_OP_VS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvi_bvi_to_bvl_refs]) THEN
  BVITMCAUX_REFS_TAC THEN GVS BVITMCAUX_OP_SIMPS THEN BVITMCAUX_STATE_REL_TAC THEN
  CONV_TAC BVITMCAUX_DOAPP_CONV THEN SIMP BVITMCAUX_OP_SIMPS);;

let wrapper_strip_if_then = prove
 (`rewrite_wrapper loc loc_opt n (bvi_If x1 x2 x3) = SOME w ==>
   ?w2 w3. w = bvi_If x1 w2 w3 /\
           (rewrite_wrapper loc loc_opt n x2 = SOME w2 \/ w2 = x2)`,
  REWRITE_TAC[rewrite_wrapper_def; LET_DEF; LET_END_DEF] THEN
  CASES_ON `rewrite_wrapper loc loc_opt n x2` THEN
  CASES_ON `rewrite_wrapper loc loc_opt n x3` THEN
  CASE_REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[injectivity "bvi_exp"] THEN
  MESON_TAC[]);;

let wrapper_strip_if_else = prove
 (`rewrite_wrapper loc loc_opt n (bvi_If x1 x2 x3) = SOME w ==>
   ?w2 w3. w = bvi_If x1 w2 w3 /\
           (rewrite_wrapper loc loc_opt n x3 = SOME w3 \/ w3 = x3)`,
  REWRITE_TAC[rewrite_wrapper_def; LET_DEF; LET_END_DEF] THEN
  CASES_ON `rewrite_wrapper loc loc_opt n x2` THEN
  CASES_ON `rewrite_wrapper loc loc_opt n x3` THEN
  CASE_REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[injectivity "bvi_exp"] THEN
  MESON_TAC[]);;

let wrapper_strip_let = prove
 (`!n loc loc_opt xs x w.
     rewrite_wrapper loc loc_opt n (bvi_Let xs x) = SOME w ==>
     ?w'. w = bvi_Let xs w' /\
          rewrite_wrapper loc loc_opt (n + LENGTH xs) x = SOME w'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rewrite_wrapper_def] THEN
  CASES_ON `rewrite_wrapper loc loc_opt (n + LENGTH (xs:bvi_exp list)) x` THEN
  CASE_REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MESON_TAC[]);;

let wrapper_strip_tick = prove
 (`!n loc loc_opt x w.
     rewrite_wrapper loc loc_opt n (bvi_Tick x) = SOME w ==>
     ?w'. w = bvi_Tick w' /\ rewrite_wrapper loc loc_opt n x = SOME w'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rewrite_wrapper_def] THEN
  CASES_ON `rewrite_wrapper loc loc_opt n x` THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MESON_TAC[]);;

let is_block_op_cons_def = cake_def
 `is_block_op_cons op <=> ?block_tag. op = BlockOp (clos_Cons block_tag)`;;

let bvi_tmcProof_bvi_to_bvl_refs = prove
 (`bvi_state_refs (bvl_to_bvi (s:(C,FFI)bvl_state) (t:(C,FFI)bvi_state)) =
   bvl_state_refs s`,
  REWRITE_TAC[bvl_to_bvi_def; bvi_state_INFO.ri_accfupds; K_THM]);;

let finalise_cons_refs_SUBSET = prove
 (`!v1 refs1 v2 refs2.
     bvi_finalise_cons v1 refs1 = SOME (v2,refs2) ==>
     FDOM refs1 SUBSET FDOM refs2`,
  MATCH_MP_TAC bvi_finalise_cons_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_finalise_cons_def] THEN
  TRY(REWRITE_TAC[option_INJ; PAIR_EQ] THEN MESON_TAC[SUBSET_REFL]) THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  REPEAT(TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[SUBSET_REFL; FDOM_FUPDATE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a0:num`; `a2:bvl_v list`; `a4:bvl_v list`; `F`;
    `a3:bvl_v`] o check (is_forall o concl)) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  REWRITE_TAC[FDOM_DOMSUB] THEN SET_TAC[]);;

let BVITMCAUX_do_app_aux_refs = prove
 (`!op vs (s:(C,FFI)bvi_state) v t.
     bvi_do_app_aux op vs s = SOME (SOME (v,t)) ==>
     FDOM (bvi_state_refs s) SUBSET FDOM (bvi_state_refs t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_do_app_aux_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM; SUBSET_REFL; FDOM_FUPDATE] THEN
  TRY(SET_TAC[]) THEN ASM_MESON_TAC[finalise_cons_refs_SUBSET]);;

let bvi_tmcProof_do_app_refs_SUBSET = prove
 (`bvi_do_app op a (r:(C,FFI)bvi_state) = Rval (q,t) ==>
   FDOM (bvi_state_refs r) SUBSET FDOM (bvi_state_refs t)`,
  REWRITE_TAC[bvi_do_app_def] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[bvi_do_install_def; LET_DEF; LET_END_DEF] THEN
    REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
    REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM; SUBSET_REFL];
    ALL_TAC] THEN
  REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  IMP_RES_TAC BVITMCAUX_do_app_aux_refs THEN
  IMP_RES_TAC bvl_do_app_refs_SUBSET THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvi_bvi_to_bvl_refs]) THEN
  ASM_REWRITE_TAC[bvi_tmcProof_bvi_to_bvl_refs]);;

let bvi_tmcProof_evaluate_refs_SUBSET = prove
 (`!xs env (s:(C,FFI)bvi_state) r t.
     bvi_evaluate (xs,env,s) = (r,t) ==>
     FDOM (bvi_state_refs s) SUBSET FDOM (bvi_state_refs t)`,
  MATCH_MP_TAC BVLPROPSAUX_bvi_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN BVLPROPSAUX_bvi_SPLIT_TAC THEN
  BVLPROPSAUX_bvi_RES_TAC THEN BVLPROPSAUX_bvi_RES_TAC THEN
  IMP_RES_TAC bvi_tmcProof_do_app_refs_SUBSET THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvi_dec_clock_def; bvi_state_INFO.ri_accfupds; K_THM]) THEN
  ASM_REWRITE_TAC[bvi_dec_clock_def; bvi_state_INFO.ri_accfupds; K_THM; SUBSET_REFL] THEN
  ASM_MESON_TAC[SUBSET_TRANS; SUBSET_REFL]);;

let list_rel_reverse = prove
 (`!r (l1:A list) (l2:B list). ALL2 r l1 l2 <=> ALL2 r (REVERSE l1) (REVERSE l2)`,
  REWRITE_TAC[LIST_REL_REVERSE_EQ]);;

let list_rel_last = prove
 (`!r (l1:A list) (l2:B list). ALL2 r l1 l2 /\ ~(l1 = []) ==> r (LAST l1) (LAST l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LIST_REL_CONS1] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[LAST] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  SUBGOAL_THEN `(t':B list = []) <=> (t:A list = [])` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let list_rel_front = prove
 (`!r (l1:A list) (l2:B list). ALL2 r l1 l2 ==> ALL2 r (BUTLAST l1) (BUTLAST l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LIST_REL_CONS1; LIST_REL_NIL] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[BUTLAST; ALL2] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  SUBGOAL_THEN `(t':B list = []) <=> (t:A list = [])` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ALL2] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let list_rel_env_rel = prove
 (`!f env1 env2.
     ALL2 (bvi_tmcProof_v_rel f) env1 env2 ==> bvi_tmcProof_env_rel F f env1 env2`,
  REWRITE_TAC[bvi_tmcProof_env_rel_def] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`env2:bvl_v list`; `[]:bvl_v list`] THEN
  ASM_REWRITE_TAC[APPEND_NIL]);;

let BVITMCAUX_v_rel_mb_rel = prove
 (`!f refs_old refs v1 v2.
     bvi_tmcProof_v_rel f v1 v2 ==> mb_rel f refs_old refs v1 v2`,
  REPEAT GEN_TAC THEN CASES_ON `v1:bvl_v` THEN
  REWRITE_TAC[BVITMCAUX_v_rel_simps] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[mb_rel_def; BVITMCAUX_v_rel_simps] THEN ASM_MESON_TAC[]);;

let BVITMCAUX_Unit_Block = prove
 (`bvl_Unit = bvl_Block 0 []`,
  REWRITE_TAC[bvl_Unit_def; tuple_tag_def]);;

let evaluate_fill_hole = prove
 (`!exp f f' env1 env2 (s:(num#C,FFI)bvi_state) t (s':(C,FFI)bvi_state) t' r r' c.
    bvi_evaluate ([exp],env1,s) = (r,t) /\
    bvi_evaluate ([exp],env2,s') = (r',t') /\
    bvi_tmcProof_env_rel T f env1 env2 /\ bvi_tmcProof_state_rel f s s' /\
    f SUBMAP f' /\
    result_rel (ALL2 (bvi_tmcProof_v_rel f')) (eor_rel f') r r' /\
    hole_has_val f env1 env2 (bvi_state_refs s') c /\
    hole_not_finalised (bvi_state_refs s') hole_ptr /\
    holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t') {} /\
    holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t') /\
    only_fresh f f' (bvi_state_refs s') /\
    bvi_tmcProof_state_rel f' t t' /\
    EL (LENGTH env1) env2 = bvl_RefPtr F hole_ptr ==>
    ?r_fill f_fill t_fill.
      bvi_evaluate ([fill_hole (LENGTH env1) (LENGTH env1 + 1) exp],env2,s') =
        (r_fill,t_fill) /\
      opt_res_rel f_fill r r_fill /\
      bvi_tmcProof_state_rel f_fill t t_fill /\
      f SUBMAP f_fill /\
      only_fresh f f_fill (bvi_state_refs s') /\
      holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t_fill) {hole_ptr} /\
      holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t_fill) /\
      (!v. r = Rval [v] ==>
           ?v_fill. mb_rel f_fill (bvi_state_refs s') (bvi_state_refs t_fill \\ hole_ptr)
                      v v_fill /\
                    hole_has_val f env1 env2 (bvi_state_refs t_fill) v_fill)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP env_rel_length_opt) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[hole_has_val_def] o
    check (BVITMCAUX_head_is "hole_has_val")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `hp:num`
     (X_CHOOSE_THEN `tag:num` (X_CHOOSE_THEN `fin:bool` (X_CHOOSE_THEN `left:bvl_v list`
     (X_CHOOSE_THEN `right:bvl_v list` STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `hp:num = hole_ptr` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `EL (LENGTH (env1:bvl_v list)) env2 = bvl_RefPtr F hp` THEN
    ASM_REWRITE_TAC[injectivity "bvl_v"] THEN DISCH_THEN(ACCEPT_TAC o SYM); ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`hole_ptr:num`; `tag:num`; `fin:bool`; `left:bvl_v list`;
     `c:bvl_v`; `right:bvl_v list`] o REWRITE_RULE[holes_unchanged_except_def] o
     check (BVITMCAUX_head_is "holes_unchanged_except")) THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `fin':bool` (X_CHOOSE_THEN `child':bvl_v` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `fin' = F` SUBST_ALL_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `hole_ptr:num` o
      REWRITE_RULE[holes_still_not_finalised_def] o
      check (BVITMCAUX_head_is "holes_still_not_finalised")) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[hole_not_finalised_def] THEN
    ASM_REWRITE_TAC[option_INJ; injectivity "bvl_ref"] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[fill_hole_def; bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `n < n + 2 /\ n + 1 < n + 2`] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(hole_ptr IN FRANGE (f':(num,num)fmap))` ASSUME_TAC THENL
   [SUBGOAL_THEN `hole_ptr IN FDOM (bvi_state_refs (s':(C,FFI)bvi_state))` MP_TAC THENL
     [REWRITE_TAC[FDOM_FLOOKUP] THEN ASM_REWRITE_TAC[option_DISTINCT]; ALL_TAC] THEN
    UNDISCH_TAC `~(hole_ptr IN FRANGE (f:(num,num)fmap))` THEN
    UNDISCH_TAC `only_fresh f f' (bvi_state_refs (s':(C,FFI)bvi_state))` THEN
    REWRITE_TAC[only_fresh_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  CASES_ON `r:(bvl_v list,exn_or_ret)result` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[result_rel_Rval; result_rel_Rerr1]) THEN
  REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [(FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP evaluate_SING_IMP o
     check (fun th -> is_eq(concl th) && is_pair(rhs(concl th)) &&
       (try fst(dest_const(rator(fst(dest_pair(rhs(concl th)))))) = "Rval"
        with Failure _ -> false) &&
       free_in `env1:bvl_v list` (concl th))) THEN
   RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
   REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
   RVEQ_TAC THEN
   REWRITE_TAC[HD; REVERSE; APPEND] THEN
   CONV_TAC BVITMCAUX_DOAPP_CONV THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[MESON[] `!(a:A) (b:B) P. (?v t. (a = v /\ b = t) /\ P v t) <=> P a b`] THEN
    MAP_EVERY EXISTS_TAC [`Rval [bvl_Unit]:(bvl_v list,exn_or_ret)result`; `f':(num,num)fmap`;
     `bvi_state_refs_fupd (K (bvi_state_refs (t':(C,FFI)bvi_state) |+
        (hole_ptr,MutBlock tag F left h' right))) t'`] THEN
   REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THENL
    [REWRITE_TAC[opt_res_rel_def; BVITMCAUX_Unit_Block] THEN CASE_REWRITE_TAC[];
     MATCH_MP_TAC state_rel_filled THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC (INST [`fin:bool`,`fin':bool`; `child':bvl_v`,`c':bvl_v`]
       (INST_TYPE [`:num`,`:A`; `:num`,`:B`; `:bvl_v`,`:C`]
          holes_unchanged_except_filled)) THEN
     ASM_REWRITE_TAC[];
     MATCH_MP_TAC holes_still_not_finalised_ins THEN ASM_REWRITE_TAC[];
     GEN_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN EXISTS_TAC `h':bvl_v` THEN
     CONJ_TAC THENL
      [MATCH_MP_TAC BVITMCAUX_v_rel_mb_rel THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[hole_has_val_def; FLOOKUP_UPDATE] THEN ASM_REWRITE_TAC[] THEN
       MAP_EVERY EXISTS_TAC [`hole_ptr:num`; `tag:num`; `F`; `left:bvl_v list`;
                             `right:bvl_v list`] THEN
       ASM_REWRITE_TAC[]]]);
    MAP_EVERY EXISTS_TAC [`Rerr e':(bvl_v list,exn_or_ret)result`; `f':(num,num)fmap`;
                          `t':(C,FFI)bvi_state`] THEN
    ASM_REWRITE_TAC[opt_res_rel_def; injectivity "result"; distinctness "result"] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC holes_unchanged_except_subset THEN
    EXISTS_TAC `{}:num->bool` THEN ASM_REWRITE_TAC[EMPTY_SUBSET]]);;

let evaluate_fill_hole_val = prove
 (`!exp f f' env1 env2 (s:(num#C,FFI)bvi_state) t (s':(C,FFI)bvi_state) t' v v' c.
    bvi_evaluate ([exp],env1,s) = (Rval [v],t) /\
    bvi_evaluate ([exp],env2,s') = (Rval [v'],t') /\
    bvi_tmcProof_env_rel T f env1 env2 /\ bvi_tmcProof_state_rel f s s' /\
    f SUBMAP f' /\ bvi_tmcProof_v_rel f' v v' /\
    hole_has_val f env1 env2 (bvi_state_refs s') c /\
    hole_not_finalised (bvi_state_refs s') hole_ptr /\
    holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t') {} /\
    holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t') /\
    only_fresh f f' (bvi_state_refs s') /\
    bvi_tmcProof_state_rel f' t t' /\
    EL (LENGTH env1) env2 = bvl_RefPtr F hole_ptr ==>
    ?r_fill f_fill t_fill.
      bvi_evaluate ([fill_hole (LENGTH env1) (LENGTH env1 + 1) exp],env2,s') =
        (r_fill,t_fill) /\
      opt_res_rel f_fill (Rval [v]) r_fill /\
      bvi_tmcProof_state_rel f_fill t t_fill /\
      f SUBMAP f_fill /\
      only_fresh f f_fill (bvi_state_refs s') /\
      holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t_fill) {hole_ptr} /\
      holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t_fill) /\
      ?v_fill. mb_rel f_fill (bvi_state_refs s') (bvi_state_refs t_fill \\ hole_ptr)
                 v v_fill /\
               hole_has_val f env1 env2 (bvi_state_refs t_fill) v_fill`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`exp:bvi_exp`; `f:(num,num)fmap`; `f':(num,num)fmap`;
                `env1:bvl_v list`; `env2:bvl_v list`; `s:(num#C,FFI)bvi_state`;
                `t:(num#C,FFI)bvi_state`; `s':(C,FFI)bvi_state`; `t':(C,FFI)bvi_state`;
                `Rval [v]:(bvl_v list,exn_or_ret)result`;
                `Rval [v']:(bvl_v list,exn_or_ret)result`; `c:bvl_v`]
         evaluate_fill_hole) THEN
  ASM_REWRITE_TAC[result_rel_def; ALL2] THEN MESON_TAC[]);;

(* the evaluation of a list of variables *)
let BVITMCAUX_evaluate_Vars = prove
 (`!vs env (s:(C,FFI)bvi_state).
     bvi_evaluate (MAP (\n. bvi_Var n) vs,env,s) =
     if ALL (\n. n < LENGTH env) vs then (Rval (MAP (\n. EL n env) vs),s)
     else (Rerr (Rabort Rtype_error),s)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL; bvi_evaluate_def] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN REWRITE_TAC[bvi_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD]);;

let evaluate_vars_source = prove
 (`!vs env (s:(num#C,FFI)bvi_state).
     wf_vars (LENGTH env) vs ==>
     bvi_evaluate (MAP (\n. bvi_Var n) vs,env,s) = (Rval (MAP (\n. EL n env) vs),s)`,
  SIMP_TAC[BVITMCAUX_evaluate_Vars; wf_vars_def]);;

let evaluate_vars_target = prove
 (`!vs n env (s:(C,FFI)bvi_state).
     wf_vars n vs /\ LENGTH env >= n ==>
     bvi_evaluate (MAP (\n. bvi_Var n) vs,env,s) = (Rval (MAP (\n. EL n env) vs),s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITMCAUX_evaluate_Vars; wf_vars_def; GSYM ALL_MEM] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[LTE_TRANS; GE]);;

let evaluate_vars_expand_env = prove
 (`!vs env (s:(C,FFI)bvi_state) v extras.
     bvi_evaluate (MAP (\n. bvi_Var n) vs,env,s) = (Rval v,s) ==>
     bvi_evaluate (MAP (\n. bvi_Var n) vs,APPEND env extras,s) = (Rval v,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITMCAUX_evaluate_Vars] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `ALL (\n. n < LENGTH (APPEND env extras:bvl_v list)) vs` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\n. n < LENGTH (env:bvl_v list)) vs` THEN
    MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[PAIR_EQ; injectivity "result"] THEN
  MATCH_MP_TAC MAP_EQ THEN
  UNDISCH_TAC `ALL (\n. n < LENGTH (env:bvl_v list)) vs` THEN
  MATCH_MP_TAC MONO_ALL THEN SIMP_TAC[EL_APPEND1]);;

let evaluate_var_list = prove
 (`!ns env (s:(C,FFI)bvi_state) t r.
     bvi_evaluate (MAP (\n. bvi_Var n) ns,env,s) = (r,t) /\
     ~(r = Rerr (Rabort Rtype_error)) ==>
     (r,t) = (Rval (MAP (\n. EL n env) ns),s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITMCAUX_evaluate_Vars] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let evaluate_var_list_binders = prove
 (`!ns extras env (s:(C,FFI)bvi_state) r t.
     bvi_evaluate (MAP (\n. bvi_Var n) ns,env,s) = (r,t) /\
     ~(r = Rerr (Rabort Rtype_error)) ==>
     bvi_evaluate (MAP (\n. bvi_Var (n + LENGTH extras)) ns,APPEND extras env,s) = (r,t)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `MAP (\n. bvi_Var (n + LENGTH (extras:bvl_v list))) ns =
                MAP (\n. bvi_Var n) (MAP (\n. n + LENGTH extras) ns)` SUBST1_TAC THENL
   [REWRITE_TAC[MAP_MAP_o; o_DEF]; ALL_TAC] THEN
  REWRITE_TAC[BVITMCAUX_evaluate_Vars] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "result"]) THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  REWRITE_TAC[ALL_MAP; o_DEF; LENGTH_APPEND] THEN
  SUBGOAL_THEN `ALL (\n. n + LENGTH (extras:bvl_v list) <
                       LENGTH extras + LENGTH (env:bvl_v list)) ns`
    (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `ALL (\n. n < LENGTH (env:bvl_v list)) ns` THEN
    MATCH_MP_TAC MONO_ALL THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; MAP_MAP_o; o_DEF] THEN
  MATCH_MP_TAC MAP_EQ THEN
  UNDISCH_TAC `ALL (\n. n < LENGTH (env:bvl_v list)) ns` THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[EL_APPEND_EQN] THEN
  REWRITE_TAC[ARITH_RULE `~(n + l < l:num) /\ (n + l) - l = n`]);;

let BVITMCAUX_bind_vars = prove
 (`!args n vs n' (ys:bvl_v list) avs.
     bind n (args:A list) = (vs,n') /\ LENGTH ys = n /\ LENGTH avs = LENGTH args ==>
     ALL (\k. k < LENGTH (APPEND ys avs)) vs /\
     MAP (\k. EL k (APPEND ys avs)) vs = avs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[bind_def; PAIR_EQ] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; LENGTH_EQ_NIL]) THEN
    ASM_REWRITE_TAC[ALL; MAP];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN
  CASES_ON `avs:bvl_v list` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; NOT_SUC; SUC_INJ; GSYM NOT_SUC]) THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`LENGTH (ys:bvl_v list) + 1`; `vs':num list`; `n':num`;
    `APPEND (ys:bvl_v list) [a0:bvl_v]`; `a1:bvl_v list`]) THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ONE; ADD_CLAUSES] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ALL; MAP; CONS_11; LENGTH_APPEND; LENGTH] THEN
  REWRITE_TAC[EL_APPEND_EQN; LT_REFL; SUB_REFL; EL; HD] THEN ARITH_TAC);;

let evaluate_binders = prove
 (`!args env (s:(C,FFI)bvi_state) t vs avs next next'.
     bvi_evaluate (args,env,s) = (Rval avs,t) /\ bind next args = (vs,next') ==>
     !ys. LENGTH ys = next ==>
          bvi_evaluate (MAP (\n. bvi_Var n) vs,APPEND ys avs,t) = (Rval avs,t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvi_evaluate_IMP_LENGTH) THEN
  MP_TAC(ISPECL [`args:bvi_exp list`; `next:num`; `vs:num list`; `next':num`;
                 `ys:bvl_v list`; `avs:bvl_v list`] BVITMCAUX_bind_vars) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[BVITMCAUX_evaluate_Vars]);;

let BVITMCAUX_shift_vars_MAP = prove
 (`!k vs. shift_vars k vs = MAP (\n. n + k) vs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[shift_vars_def; MAP]);;

let evaluate_shift_vars = prove
 (`!vs env (s:(C,FFI)bvi_state) bs.
     bvi_evaluate (MAP (\n. bvi_Var n) (shift_vars (LENGTH bs) vs),APPEND bs env,s) =
     bvi_evaluate (MAP (\n. bvi_Var n) vs,env,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITMCAUX_shift_vars_MAP; BVITMCAUX_evaluate_Vars] THEN
  REWRITE_TAC[ALL_MAP; MAP_MAP_o; o_DEF; LENGTH_APPEND] THEN
  REWRITE_TAC[ARITH_RULE `n + l < l + e <=> n < e:num`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ; injectivity "result"] THEN
  MATCH_MP_TAC MAP_EQ THEN
  UNDISCH_TAC `ALL (\n. n < LENGTH (env:bvl_v list)) vs` THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[EL_APPEND_EQN] THEN
  REWRITE_TAC[ARITH_RULE `~(n + l < l:num) /\ (n + l) - l = n`]);;

let evaluate_shift_vars_sing = prove
 (`!vs env (s:(C,FFI)bvi_state) b.
     bvi_evaluate (MAP (\n. bvi_Var n) (shift_vars 1 vs),CONS b env,s) =
     bvi_evaluate (MAP (\n. bvi_Var n) vs,env,s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`vs:num list`; `env:bvl_v list`; `s:(C,FFI)bvi_state`; `[b:bvl_v]`]
    evaluate_shift_vars) THEN
  REWRITE_TAC[LENGTH; ONE; APPEND]);;

let evaluate_shift_cb = prove
 (`!cb loc env (s:(C,FFI)bvi_state) bs.
     bvi_evaluate ([cb_to_bvi loc (shift_cb (LENGTH bs) cb)],APPEND bs env,s) =
     bvi_evaluate ([cb_to_bvi loc cb],env,s)`,
  MATCH_MP_TAC call_block_INDUCT THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[shift_cb_def; cb_to_bvi_def; LET_DEF; LET_END_DEF] THEN
    ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
    REWRITE_TAC[bvi_evaluate_APPEND] THEN
    ASM_REWRITE_TAC[evaluate_shift_vars];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[shift_cb_def; cb_to_bvi_def; LET_DEF; LET_END_DEF] THEN
    ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
    REWRITE_TAC[evaluate_shift_vars] THEN CASE_REWRITE_TAC[]]);;

let evaluate_shift_cb_sing = prove
 (`!cb loc env (s:(C,FFI)bvi_state) b.
     bvi_evaluate ([cb_to_bvi loc (shift_cb 1 cb)],CONS b env,s) =
     bvi_evaluate ([cb_to_bvi loc cb],env,s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`cb:call_block`; `loc:num`; `env:bvl_v list`; `s:(C,FFI)bvi_state`;
                `[b:bvl_v]`] evaluate_shift_cb) THEN
  REWRITE_TAC[LENGTH; ONE; APPEND]);;

let BVITMCAUX_CASES_TY ty : tactic = fun (asl,w as g) ->
  let v = find (fun v -> type_of v = ty) (frees w) in
  STRUCT_CASES_TAC (ISPEC v (cases (fst(dest_type ty)))) g;;

(* HOL4 [local] *)
let evaluate_pure_exp_lemma = prove
 (`(!e n. pure_exp n e ==>
          !env. n <= LENGTH env ==>
                ?v. !s:(C,FFI)bvi_state. bvi_evaluate ([e],env,s) = (Rval v,s)) /\
   (!x:bvi_exp option. T) /\
   (!xs n. pure_exps n xs ==>
           !env. n <= LENGTH env ==>
                 ?v. !s:(C,FFI)bvi_state. bvi_evaluate (xs,env,s) = (Rval v,s))`,
  let ih tm env nm =
    FIRST_ASSUM(MP_TAC o SPEC env o C MP (ASSUME tm) o SPEC `n:num`) THEN
    REWRITE_TAC[LENGTH_APPEND] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC nm)] in
  SUBGOAL_THEN
   `(!e n. pure_exp n e ==>
           !env. n <= LENGTH env ==>
                 ?v. !s:(C,FFI)bvi_state. bvi_evaluate ([e],env,s) = (Rval v,s)) /\
    (!xs n. pure_exps n xs ==>
            !env. n <= LENGTH env ==>
                  ?v. !s:(C,FFI)bvi_state. bvi_evaluate (xs,env,s) = (Rval v,s)) /\
    (!x:bvi_exp option. T)`
   (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC bvi_exp_INDUCT THEN REWRITE_TAC[pure_exp_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT STRIP_TAC THENL
   [(* Var *)
    EXISTS_TAC `[EL a (env:bvl_v list)]` THEN REWRITE_TAC[bvi_evaluate_def] THEN
    SUBGOAL_THEN `a < LENGTH (env:bvl_v list)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    (* Let *)
    ih `pure_exps n (a0:bvi_exp list)` `env:bvl_v list` `vs:bvl_v list` THEN
    ih `pure_exp n (a1:bvi_exp)` `APPEND vs (env:bvl_v list)` `v:bvl_v list` THEN
    EXISTS_TAC `v:bvl_v list` THEN GEN_TAC THEN
    REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[];
    (* Op *)
    ih `pure_exps n (a1:bvi_exp list)` `env:bvl_v list` `vs:bvl_v list` THEN
    REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(?i. a0 = IntOp (clos_Const i) /\ a1 = []:bvi_exp list /\ small_enough_int i) \/
      (?tag. a0 = BlockOp (clos_Cons tag))` MP_TAC THENL
     [UNDISCH_TAC `bvi_tmc_pure_op a0 (a1:bvi_exp list)` THEN
      BVITMCAUX_CASES_TY `:clos_op` THEN
      REWRITE_TAC[bvi_tmc_pure_op_def; distinctness "clos_op"; injectivity "clos_op"] THEN
      TRY(BVITMCAUX_CASES_TY `:int_op`) THEN TRY(BVITMCAUX_CASES_TY `:block_op`) THEN
      REWRITE_TAC[bvi_tmc_pure_op_def; distinctness "int_op"; injectivity "int_op";
                  distinctness "block_op"; injectivity "block_op"] THEN
      TRY(STRUCT_CASES_TAC(ISPEC `a1:bvi_exp list` list_CASES)) THEN
      REWRITE_TAC[bvi_tmc_pure_op_def; NOT_CONS_NIL] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th))))) THENL
     [SUBGOAL_THEN `vs:bvl_v list = []` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `ARB:(C,FFI)bvi_state` o
          check (fun th -> free_in `vs:bvl_v list` (concl th))) THEN
        REWRITE_TAC[bvi_evaluate_def; PAIR_EQ; injectivity "result"] THEN MESON_TAC[];
        ALL_TAC] THEN
      CONV_TAC(ONCE_DEPTH_CONV BVITMCAUX_DOAPP_CONV) THEN ASM_REWRITE_TAC[REVERSE; NULL] THEN
      CASE_REWRITE_TAC[] THEN MESON_TAC[];
      CONV_TAC(ONCE_DEPTH_CONV BVITMCAUX_DOAPP_CONV) THEN
      REWRITE_TAC[bvl_to_bvi_id] THEN CASE_REWRITE_TAC[] THEN MESON_TAC[]];
    (* Nil *)
    EXISTS_TAC `[]:bvl_v list` THEN REWRITE_TAC[bvi_evaluate_def];
    (* Cons *)
    ih `pure_exp n (a0:bvi_exp)` `env:bvl_v list` `v0:bvl_v list` THEN
    ih `pure_exps n (a1:bvi_exp list)` `env:bvl_v list` `vs:bvl_v list` THEN
    EXISTS_TAC `CONS (HD v0) vs:bvl_v list` THEN GEN_TAC THEN
    ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[]]);;

let evaluate_pure_exps = prove
 (`!n xs. pure_exps n xs ==>
          !env. n <= LENGTH env ==>
                ?v. !s:(C,FFI)bvi_state. bvi_evaluate (xs,env,s) = (Rval v,s)`,
  MESON_TAC[evaluate_pure_exp_lemma]);;

let BVITMCAUX_cb_aux_sing_inl = prove
 (`!n loc tag exp bs vs.
     bvi_to_cb_aux_sing n loc tag exp = SOME (bs,INL vs) ==>
     pure_exp n exp /\ bs = [exp] /\ vs = [0]`,
  REPEAT GEN_TAC THEN CASES_ON `exp:bvi_exp` THEN
  REWRITE_TAC[bvi_to_cb_aux_def; call_to_cb_def] THEN
  GVS[option_case_eq; sum_case_eq; pair_case_eq; COND_CASE_EQ] THEN
  MESON_TAC[]);;

let BVITMCAUX_inl_sing = prove
 (`!n loc tag exp bs vs.
     bvi_to_cb_aux_sing n loc tag exp = SOME (bs,INL vs) ==>
     bs = [exp] /\
     !env. n <= LENGTH env ==>
           ?v. !s:(C,FFI)bvi_state.
                 bvi_evaluate ([exp],env,s) = (Rval v,s) /\
                 bvi_evaluate (MAP (\n. bvi_Var n) vs,v,s) = (Rval v,s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP BVITMCAUX_cb_aux_sing_inl) THEN
  ASM_REWRITE_TAC[MAP] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `[exp:bvi_exp]`] evaluate_pure_exps) THEN
  ASM_REWRITE_TAC[pure_exps_sing] THEN
  DISCH_THEN(MP_TAC o SPEC `env:bvl_v list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `v:bvl_v list`) THEN
  MP_TAC(SPECL [`exp:bvi_exp`; `env:bvl_v list`; `ARB:(C,FFI)bvi_state`;
                `v:bvl_v list`; `ARB:(C,FFI)bvi_state`] evaluate_SING_IMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:bvl_v` SUBST_ALL_TAC) THEN
  EXISTS_TAC `[w:bvl_v]` THEN
  ASM_REWRITE_TAC[bvi_evaluate_def; LENGTH; EL; HD; LT_0]);;

let BVITMCAUX_cb_aux_cons_inl_inv = prove
 (`!n loc tag h v6 v7 bs vs.
     bvi_to_cb_aux n loc tag (CONS h (CONS v6 v7)) = SOME (bs,INL vs) ==>
     ?bs1 vs1 bs2 vs2.
       bvi_to_cb_aux n loc tag (CONS v6 v7) = SOME (bs2,INL vs2) /\
       bvi_to_cb_aux_sing n loc tag h = SOME (bs1,INL vs1) /\
       bs = APPEND bs1 bs2 /\ vs = APPEND vs1 (shift_vars (LENGTH bs1) vs2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_to_cb_aux_def] THEN
  REWRITE_TAC[option_case_eq; sum_case_eq; pair_case_eq; case_eq "call_block";
              list_case_eq; COND_CASE_EQ; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[distinctness "option"; option_INJ; PAIR_EQ; distinctness "sum";
              injectivity "sum"] THEN
  MESON_TAC[]);;

(* HOL4 [local] *)
let evaluate_bvi_to_cb_aux_inl_lemma = prove
 (`(!n loc tag exp bs vs.
      bvi_to_cb_aux_sing n loc tag exp = SOME (bs,INL vs) ==>
      bs = [exp] /\
      !env. n <= LENGTH env ==>
            ?v. !s:(C,FFI)bvi_state.
                  bvi_evaluate ([exp],env,s) = (Rval v,s) /\
                  bvi_evaluate (MAP (\n. bvi_Var n) vs,v,s) = (Rval v,s)) /\
   (!n loc tag args bs vs.
      bvi_to_cb_aux n loc tag args = SOME (bs,INL vs) ==>
      bs = args /\
      !env. n <= LENGTH env ==>
            ?v. !s:(C,FFI)bvi_state.
                  bvi_evaluate (args,env,s) = (Rval v,s) /\
                  bvi_evaluate (MAP (\n. bvi_Var n) vs,v,s) = (Rval v,s))`,
  MATCH_MP_TAC bvi_to_cb_aux_ind THEN REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[BVITMCAUX_inl_sing] THEN NO_TAC) THENL
   [(* [] *)
    REPEAT GEN_TAC THEN
    REWRITE_TAC[bvi_to_cb_aux_def; option_INJ; PAIR_EQ; injectivity "sum"] THEN
    DISCH_THEN(CONJUNCTS_THEN(SUBST1_TAC o SYM)) THEN REWRITE_TAC[MAP] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `[]:bvl_v list` THEN
    REWRITE_TAC[bvi_evaluate_def];
    (* [exp] *)
    REWRITE_TAC[bvi_to_cb_aux_def];
    (* CONS h (CONS v6 v7) *)
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "iht") (LABEL_TAC "ihh")) THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `bs1:bvi_exp list` (X_CHOOSE_THEN `vs1:num list`
      (X_CHOOSE_THEN `bs2:bvi_exp list` (X_CHOOSE_THEN `vs2:num list`
        STRIP_ASSUME_TAC))) o MATCH_MP BVITMCAUX_cb_aux_cons_inl_inv) THEN
    REMOVE_THEN "iht" (MP_TAC o SPECL [`bs2:bvi_exp list`; `vs2:num list`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (LABEL_TAC "et")) THEN
    REMOVE_THEN "ihh" (MP_TAC o SPECL [`CONS v6 v7:bvi_exp list`; `vs2:num list`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`bs1:bvi_exp list`; `vs1:num list`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (LABEL_TAC "eh")) THEN
    ASM_REWRITE_TAC[APPEND; LENGTH; GSYM ONE] THEN
    X_GEN_TAC `env:bvl_v list` THEN DISCH_TAC THEN
    REMOVE_THEN "et" (MP_TAC o SPEC `env:bvl_v list`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `v':bvl_v list`) THEN
    REMOVE_THEN "eh" (MP_TAC o SPEC `env:bvl_v list`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `v:bvl_v list`) THEN
    MP_TAC(SPECL [`h:bvi_exp`; `env:bvl_v list`; `ARB:(C,FFI)bvi_state`;
                  `v:bvl_v list`; `ARB:(C,FFI)bvi_state`] evaluate_SING_IMP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:bvl_v` SUBST_ALL_TAC) THEN
    EXISTS_TAC `CONS (w:bvl_v) v'` THEN X_GEN_TAC `s:(C,FFI)bvi_state` THEN
    SUBGOAL_THEN
     `bvi_evaluate (MAP (\n. bvi_Var n) vs1,CONS w v',s:(C,FFI)bvi_state) =
      (Rval [w],s)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`vs1:num list`; `[w:bvl_v]`; `s:(C,FFI)bvi_state`;
                     `[w:bvl_v]`; `v':bvl_v list`] evaluate_vars_expand_env) THEN
      ASM_REWRITE_TAC[APPEND];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
    ASM_REWRITE_TAC[HD; MAP_APPEND; bvi_evaluate_APPEND; evaluate_shift_vars_sing] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND; HD]]);;

let evaluate_bvi_to_cb_aux_inl = CONJUNCT2 evaluate_bvi_to_cb_aux_inl_lemma;;

let BVITMCAUX_evaluate_Cons = prove
 (CASE_TERM `!tag xs env (s:(C,FFI)bvi_state).
     bvi_evaluate ([bvi_Op (BlockOp (clos_Cons tag)) xs],env,s) =
     match bvi_evaluate (xs,env,s) with
       (Rval vs,s1) -> (Rval [bvl_Block tag (REVERSE vs)],s1)
     | (Rerr e,s1) -> (Rerr e,s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_evaluate_def] THEN
  MP_TAC(ISPEC `bvi_evaluate (xs,env,s:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `s1:(C,FFI)bvi_state` SUBST1_TAC)) THEN
  CASES_ON `r:(bvl_v list,exn_or_ret)result` THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BVITMCAUX_DOAPP_CONV) THEN
  REWRITE_TAC[bvl_to_bvi_id] THEN CASE_REWRITE_TAC[]);;

let BVITMCAUX_evaluate_Cons_eq = prove
 (`!tag xs ys env env' (s:(C,FFI)bvi_state) s'.
     bvi_evaluate ([bvi_Op (BlockOp (clos_Cons tag)) xs],env,s) =
     bvi_evaluate ([bvi_Op (BlockOp (clos_Cons tag)) ys],env',s') <=>
     bvi_evaluate (xs,env,s) = bvi_evaluate (ys,env',s')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITMCAUX_evaluate_Cons] THEN
  MP_TAC(ISPEC `bvi_evaluate (xs,env,s:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `s1:(C,FFI)bvi_state` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `bvi_evaluate (ys,env',s':(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `s2:(C,FFI)bvi_state` SUBST1_TAC)) THEN
  CASES_ON `r1:(bvl_v list,exn_or_ret)result` THEN
  CASES_ON `r2:(bvl_v list,exn_or_ret)result` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"; CONS_11;
              injectivity "bvl_v"] THEN
  MESON_TAC[REVERSE_REVERSE]);;

let BVITMCAUX_evaluate_Cons_Rerr = prove
 (`!tag xs env (s:(C,FFI)bvi_state) e u.
     bvi_evaluate ([bvi_Op (BlockOp (clos_Cons tag)) xs],env,s) = (Rerr e,u) <=>
     bvi_evaluate (xs,env,s) = (Rerr e,u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITMCAUX_evaluate_Cons] THEN
  MP_TAC(ISPEC `bvi_evaluate (xs,env,s:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `s1:(C,FFI)bvi_state` SUBST1_TAC)) THEN
  CASES_ON `r1:(bvl_v list,exn_or_ret)result` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"]);;

let BVITMCAUX_evaluate_Call_cong = prove
 (`!ts dest xs ys env env' (s:(C,FFI)bvi_state) s'.
     bvi_evaluate (xs,env,s) = bvi_evaluate (ys,env',s') ==>
     bvi_evaluate ([bvi_Call ts dest xs NONE],env,s) =
     bvi_evaluate ([bvi_Call ts dest ys NONE],env',s')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[bvi_evaluate_def] THEN
  ASM_REWRITE_TAC[IS_SOME_DEF] THEN CASE_REWRITE_TAC[]);;

let BVITMCAUX_inr_call = prove
 (`!n loc tag ts loc' args h' env (s:(C,FFI)bvi_state) t r bs cb.
     bvi_to_cb_aux_sing n loc tag (bvi_Call ts loc' args h') = SOME (bs,INR cb) /\
     bvi_evaluate ([bvi_Op (BlockOp (clos_Cons tag)) [bvi_Call ts loc' args h']],env,s) =
       (r,t) /\
     n <= LENGTH env ==>
     ?as u.
       bvi_evaluate (bs,env,s) = (as,u) /\
       (!vs. as = Rval vs ==>
             bvi_evaluate ([cb_to_bvi loc cb],vs,u) = (r,t) /\
             !extras. bvi_evaluate ([cb_to_bvi loc cb],APPEND vs extras,u) = (r,t)) /\
       (!e. as = Rerr e ==> (as,u) = (r,t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_to_cb_aux_def; call_to_cb_def] THEN
  ASM_CASES_TAC `loc' = SOME (loc:num) /\ h' = NONE:bvi_exp option` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN SUBST1_TAC) THEN
  MP_TAC(ISPEC `bind 0 (args:bvi_exp list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `vs':num list` (X_CHOOSE_THEN `n':num` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ; PAIR_EQ; injectivity "sum"] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[cb_to_bvi_def; LET_DEF; LET_END_DEF; MAP; APPEND] THEN
  MP_TAC(ISPEC `bvi_evaluate (args,env,s:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `as:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `u:(C,FFI)bvi_state` ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`as:(bvl_v list,exn_or_ret)result`; `u:(C,FFI)bvi_state`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `avs:bvl_v list` THEN DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN
     `!extras. bvi_evaluate (MAP (\n. bvi_Var n) vs',APPEND avs extras,u) =
               (Rval avs,u:(C,FFI)bvi_state)`
     ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC evaluate_vars_expand_env THEN
      MP_TAC(ISPECL [`args:bvi_exp list`; `env:bvl_v list`; `s:(C,FFI)bvi_state`;
        `u:(C,FFI)bvi_state`; `vs':num list`; `avs:bvl_v list`; `0`; `n':num`]
        evaluate_binders) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `[]:bvl_v list`) THEN
      REWRITE_TAC[LENGTH; APPEND];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      free_in `r:(bvl_v list,exn_or_ret)result` (concl th))) THEN
    REWRITE_TAC[BVITMCAUX_evaluate_Cons_eq] THEN
    CONJ_TAC THENL [ALL_TAC; GEN_TAC] THEN
    MATCH_MP_TAC BVITMCAUX_evaluate_Call_cong THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `[]:bvl_v list`) THEN REWRITE_TAC[APPEND_NIL];
    X_GEN_TAC `e:(exn_or_ret)error_result` THEN DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC[GSYM PAIR_EQ] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      free_in `r:(bvl_v list,exn_or_ret)result` (concl th))) THEN
    REWRITE_TAC[BVITMCAUX_evaluate_Cons] THEN
    REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[IS_SOME_DEF] THEN CASE_REWRITE_TAC[]]);;

let BVITMCAUX_cb_aux_sing_op_inr_inv = prove
 (`!n loc tag op args bs cb.
     bvi_to_cb_aux_sing n loc tag (bvi_Op op args) = SOME (bs,INR cb) ==>
     ?tag' cb0. op = BlockOp (clos_Cons tag') /\
                bvi_to_cb_aux n loc tag' args = SOME (bs,INR cb0) /\
                cb = CallBlock tag [] cb0 []`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_to_cb_aux_def; option_case_eq; sum_case_eq; pair_case_eq;
              COND_CASE_EQ; distinctness "option"; option_INJ; PAIR_EQ;
              distinctness "sum"; injectivity "sum"; BVIPAUX_TMC_dest_Cons_SOME] THEN
  MESON_TAC[]);;

let BVITMCAUX_inr_op = prove
 (`!n loc tag op args env (s:(C,FFI)bvi_state) t r bs cb.
     (!tag'. bvi_tmc_dest_Cons op = SOME tag' ==>
        !env (s:(C,FFI)bvi_state) t r bs cb.
          bvi_to_cb_aux n loc tag' args = SOME (bs,INR cb) /\
          bvi_evaluate ([bvi_Op (BlockOp (clos_Cons tag')) args],env,s) = (r,t) /\
          n <= LENGTH env ==>
          ?as u.
            bvi_evaluate (bs,env,s) = (as,u) /\
            (!vs. as = Rval vs ==>
                  bvi_evaluate ([cb_to_bvi loc cb],vs,u) = (r,t) /\
                  !extras. bvi_evaluate ([cb_to_bvi loc cb],APPEND vs extras,u) = (r,t)) /\
            (!e. as = Rerr e ==> (as,u) = (r,t))) /\
     bvi_to_cb_aux_sing n loc tag (bvi_Op op args) = SOME (bs,INR cb) /\
     bvi_evaluate ([bvi_Op (BlockOp (clos_Cons tag)) [bvi_Op op args]],env,s) = (r,t) /\
     n <= LENGTH env ==>
     ?as u.
       bvi_evaluate (bs,env,s) = (as,u) /\
       (!vs. as = Rval vs ==>
             bvi_evaluate ([cb_to_bvi loc cb],vs,u) = (r,t) /\
             !extras. bvi_evaluate ([cb_to_bvi loc cb],APPEND vs extras,u) = (r,t)) /\
       (!e. as = Rerr e ==> (as,u) = (r,t))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `tag':num` (X_CHOOSE_THEN `cb0:call_block`
    STRIP_ASSUME_TAC) o MATCH_MP BVITMCAUX_cb_aux_sing_op_inr_inv) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th))))) THEN
  MP_TAC(ISPEC `bvi_evaluate ([bvi_Op (BlockOp (clos_Cons tag')) args],env,
                               s:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r':(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `t':(C,FFI)bvi_state` ASSUME_TAC)) THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `tag':num`) THEN REWRITE_TAC[bvi_tmc_dest_Cons_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`env:bvl_v list`; `s:(C,FFI)bvi_state`;
    `t':(C,FFI)bvi_state`; `r':(bvl_v list,exn_or_ret)result`; `bs:bvi_exp list`;
    `cb0:call_block`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `as:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `u:(C,FFI)bvi_state` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`as:(bvl_v list,exn_or_ret)result`; `u:(C,FFI)bvi_state`] THEN
  ASM_REWRITE_TAC[cb_to_bvi_def; LET_DEF; LET_END_DEF; MAP; APPEND] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    free_in `r:(bvl_v list,exn_or_ret)result` (concl th))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `vs:bvl_v list` THEN DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC[BVITMCAUX_evaluate_Cons_eq] THEN ASM_SIMP_TAC[];
    X_GEN_TAC `e:(exn_or_ret)error_result` THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:(exn_or_ret)error_result` o check (fun th ->
      free_in `t':(C,FFI)bvi_state` (concl th) && is_forall (concl th))) THEN
    REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[BVITMCAUX_evaluate_Cons_Rerr] THEN
    ASM_REWRITE_TAC[]]);;

let BVITMCAUX_cb_aux_cons_inr_inv = prove
 (`!n loc tag h v6 v7 bs cb.
     bvi_to_cb_aux n loc tag (CONS h (CONS v6 v7)) = SOME (bs,INR cb) ==>
     (?bs1 bs2 vs2 child.
        bvi_to_cb_aux n loc tag (CONS v6 v7) = SOME (bs2,INL vs2) /\
        bvi_to_cb_aux_sing n loc tag h = SOME (bs1,INR (CallBlock tag [] child [])) /\
        bs = APPEND bs1 bs2 /\
        cb = CallBlock tag [] child (shift_vars (LENGTH bs1) vs2)) \/
     (?bs2 l child rr.
        bvi_to_cb_aux n loc tag (CONS v6 v7) = SOME (bs2,INR (CallBlock tag l child rr)) /\
        bs = CONS h bs2 /\
        cb = CallBlock tag (CONS 0 (shift_vars 1 l)) (shift_cb 1 child) (shift_vars 1 rr))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_to_cb_aux_def] THEN
  REWRITE_TAC[option_case_eq; sum_case_eq; pair_case_eq; case_eq "call_block";
              list_case_eq; COND_CASE_EQ; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[distinctness "option"; option_INJ; PAIR_EQ; distinctness "sum";
              injectivity "sum"] THEN
  STRIP_TAC THEN RVEQ_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT2 o
      MATCH_MP (CONJUNCT1 bvi_to_cb_aux_wf_inr_lemma)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "call_block"]) THEN
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    RVEQ_TAC THEN ASM_MESON_TAC[];
    FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT2 o
      MATCH_MP (CONJUNCT2 bvi_to_cb_aux_wf_inr_lemma)) THEN
    RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[shift_cb_def; LET_DEF; LET_END_DEF;
                                injectivity "call_block"]) THEN
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    RVEQ_TAC THEN ASM_MESON_TAC[]]);;

let BVITMCAUX_inr_cons_inl_val = prove
 (`!loc child h v6 v7 env (s:(C,FFI)bvi_state) a E u1 vs2 v'.
     (!s:(C,FFI)bvi_state. bvi_evaluate (CONS v6 v7,env,s) = (Rval v',s)) /\
     (!s:(C,FFI)bvi_state. bvi_evaluate (MAP (\n. bvi_Var n) vs2,E,s) = (Rval v',s)) /\
     bvi_evaluate ([cb_to_bvi loc child],APPEND a E,u1) = bvi_evaluate ([h],env,s) ==>
     bvi_evaluate (CONS (cb_to_bvi loc child)
                     (MAP (\n. bvi_Var n) (shift_vars (LENGTH a) vs2)),APPEND a E,u1) =
     bvi_evaluate (CONS h (CONS v6 v7),env,s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
  ASM_REWRITE_TAC[evaluate_shift_vars]);;

let BVITMCAUX_inr_cons_inl = prove
 (`!n loc tag h v6 v7 env (s:(C,FFI)bvi_state) t r bs1 bs2 vs2 child.
     (!env (s:(C,FFI)bvi_state) t r bs cb.
        bvi_to_cb_aux_sing n loc tag h = SOME (bs,INR cb) /\
        bvi_evaluate ([bvi_Op (BlockOp (clos_Cons tag)) [h]],env,s) = (r,t) /\
        n <= LENGTH env ==>
        ?as u.
          bvi_evaluate (bs,env,s) = (as,u) /\
          (!vs. as = Rval vs ==>
                bvi_evaluate ([cb_to_bvi loc cb],vs,u) = (r,t) /\
                !extras. bvi_evaluate ([cb_to_bvi loc cb],APPEND vs extras,u) = (r,t)) /\
          (!e. as = Rerr e ==> (as,u) = (r,t))) /\
     bvi_to_cb_aux n loc tag (CONS v6 v7) = SOME (bs2,INL vs2) /\
     bvi_to_cb_aux_sing n loc tag h = SOME (bs1,INR (CallBlock tag [] child [])) /\
     bvi_evaluate ([bvi_Op (BlockOp (clos_Cons tag)) (CONS h (CONS v6 v7))],env,s) =
       (r,t) /\
     n <= LENGTH env ==>
     ?as u.
       bvi_evaluate (APPEND bs1 bs2,env,s) = (as,u) /\
       (!vs. as = Rval vs ==>
             bvi_evaluate ([cb_to_bvi loc (CallBlock tag [] child
                              (shift_vars (LENGTH bs1) vs2))],vs,u) = (r,t) /\
             !extras.
               bvi_evaluate ([cb_to_bvi loc (CallBlock tag [] child
                                (shift_vars (LENGTH bs1) vs2))],APPEND vs extras,u) =
               (r,t)) /\
       (!e. as = Rerr e ==> (as,u) = (r,t))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_bvi_to_cb_aux_inl) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (MP_TAC o SPEC `env:bvl_v list`)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v':bvl_v list` STRIP_ASSUME_TAC o
             REWRITE_RULE[FORALL_AND_THM]) THEN
  MP_TAC(ISPEC `bvi_evaluate ([bvi_Op (BlockOp (clos_Cons tag)) [h]],env,
                               s:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `t1:(C,FFI)bvi_state` ASSUME_TAC)) THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`env:bvl_v list`; `s:(C,FFI)bvi_state`;
    `t1:(C,FFI)bvi_state`; `r1:(bvl_v list,exn_or_ret)result`; `bs1:bvi_exp list`;
    `CallBlock tag [] child []`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `as1:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `u1:(C,FFI)bvi_state` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    free_in `r:(bvl_v list,exn_or_ret)result` (concl th))) THEN
  DISJ_CASES_THEN2
    (X_CHOOSE_THEN `a:bvl_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)
    (ISPEC `as1:(bvl_v list,exn_or_ret)result` (cases "result")) THENL
   [SUBGOAL_THEN `bvi_evaluate (APPEND bs1 (CONS v6 v7),env,s:(C,FFI)bvi_state) =
                  (Rval (APPEND a v'),u1)` SUBST1_TAC THENL
     [REWRITE_TAC[bvi_evaluate_APPEND] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`Rval (APPEND a v'):(bvl_v list,exn_or_ret)result`;
                          `u1:(C,FFI)bvi_state`] THEN
    REWRITE_TAC[injectivity "result"; distinctness "result"] THEN
    X_GEN_TAC `vs:bvl_v list` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:bvl_v list` o check (fun th ->
      is_forall (concl th) && free_in `t1:(C,FFI)bvi_state` (concl th) &&
      free_in `u1:(C,FFI)bvi_state` (concl th) &&
      not (free_in `e:(exn_or_ret)error_result` (concl th)) &&
      (try ignore(find_term (fun t -> t = `Rval:bvl_v list->(bvl_v list,exn_or_ret)result`)
                    (concl th)); true with Failure _ -> false))) THEN
    REWRITE_TAC[cb_to_bvi_def; LET_DEF; LET_END_DEF; MAP; APPEND] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      free_in `t1:(C,FFI)bvi_state` (concl th) && is_eq (concl th) &&
      not (is_forall (concl th)))) THEN
    REWRITE_TAC[BVITMCAUX_evaluate_Cons_eq] THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP bvi_evaluate_IMP_LENGTH o check (fun th ->
      free_in `bs1:bvi_exp list` (concl th) && free_in `a:bvl_v list` (concl th))) THEN
    CONJ_TAC THENL [ALL_TAC; X_GEN_TAC `extras:bvl_v list` THEN
                    REWRITE_TAC[GSYM APPEND_ASSOC]] THEN
    MATCH_MP_TAC BVITMCAUX_inr_cons_inl_val THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[evaluate_vars_expand_env];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[] o SPEC `e:(exn_or_ret)error_result` o
    check (fun th -> is_forall(concl th) &&
      type_of(fst(dest_forall(concl th))) = `:(exn_or_ret)error_result`)) THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[BVITMCAUX_evaluate_Cons_Rerr] o
    check (fun th -> (try fst(dest_const(rator(lhs(concl th)))) = "bvi_evaluate"
                      with Failure _ -> false) && free_in `h:bvi_exp` (concl th))) THEN
  SUBGOAL_THEN `bvi_evaluate (APPEND bs1 (CONS v6 v7),env,s:(C,FFI)bvi_state) =
                (Rerr e,u1)` SUBST1_TAC THENL
   [REWRITE_TAC[bvi_evaluate_APPEND] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Rerr e:(bvl_v list,exn_or_ret)result`;
                        `u1:(C,FFI)bvi_state`] THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"] THEN
  GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[BVITMCAUX_evaluate_Cons_Rerr] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

let BVITMCAUX_evaluate_shift_args = prove
 (`!l child rr loc b E (s:(C,FFI)bvi_state).
     bvi_evaluate (APPEND (APPEND (MAP (\n. bvi_Var n) (shift_vars 1 l))
                                  [cb_to_bvi loc (shift_cb 1 child)])
                          (MAP (\n. bvi_Var n) (shift_vars 1 rr)),CONS b E,s) =
     bvi_evaluate (APPEND (APPEND (MAP (\n. bvi_Var n) l) [cb_to_bvi loc child])
                          (MAP (\n. bvi_Var n) rr),E,s)`,
  REWRITE_TAC[bvi_evaluate_APPEND; evaluate_shift_vars_sing; evaluate_shift_cb_sing]);;

let BVITMCAUX_inr_cons_inr = prove
 (`!n loc tag h v6 v7 env (s:(C,FFI)bvi_state) t r bs2 l child rr.
     (!env (s:(C,FFI)bvi_state) t r bs cb.
        bvi_to_cb_aux n loc tag (CONS v6 v7) = SOME (bs,INR cb) /\
        bvi_evaluate ([bvi_Op (BlockOp (clos_Cons tag)) (CONS v6 v7)],env,s) = (r,t) /\
        n <= LENGTH env ==>
        ?as u.
          bvi_evaluate (bs,env,s) = (as,u) /\
          (!vs. as = Rval vs ==>
                bvi_evaluate ([cb_to_bvi loc cb],vs,u) = (r,t) /\
                !extras. bvi_evaluate ([cb_to_bvi loc cb],APPEND vs extras,u) = (r,t)) /\
          (!e. as = Rerr e ==> (as,u) = (r,t))) /\
     bvi_to_cb_aux n loc tag (CONS v6 v7) = SOME (bs2,INR (CallBlock tag l child rr)) /\
     bvi_evaluate ([bvi_Op (BlockOp (clos_Cons tag)) (CONS h (CONS v6 v7))],env,s) =
       (r,t) /\
     n <= LENGTH env ==>
     ?as u.
       bvi_evaluate (CONS h bs2,env,s) = (as,u) /\
       (!vs. as = Rval vs ==>
             bvi_evaluate ([cb_to_bvi loc (CallBlock tag (CONS 0 (shift_vars 1 l))
                              (shift_cb 1 child) (shift_vars 1 rr))],vs,u) = (r,t) /\
             !extras.
               bvi_evaluate ([cb_to_bvi loc (CallBlock tag (CONS 0 (shift_vars 1 l))
                                (shift_cb 1 child) (shift_vars 1 rr))],
                             APPEND vs extras,u) = (r,t)) /\
       (!e. as = Rerr e ==> (as,u) = (r,t))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    free_in `r:(bvl_v list,exn_or_ret)result` (concl th))) THEN
  MP_TAC(ISPEC `bvi_evaluate ([h],env,s:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `rh:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `sh:(C,FFI)bvi_state` ASSUME_TAC)) THEN
  DISJ_CASES_THEN2
    (X_CHOOSE_THEN `v1:bvl_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)
    (ISPEC `rh:(bvl_v list,exn_or_ret)result` (cases "result")) THENL
   [ALL_TAC;
    (* head raises *)
    MAP_EVERY EXISTS_TAC [`Rerr e:(bvl_v list,exn_or_ret)result`;
                          `sh:(C,FFI)bvi_state`] THEN
    REWRITE_TAC[injectivity "result"; distinctness "result"] THEN
    SUBST1_TAC(ISPECL [`h:bvi_exp`; `bs2:bvi_exp list`; `env:bvl_v list`;
                       `s:(C,FFI)bvi_state`] bvi_evaluate_CONS) THEN
    ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
    CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[BVITMCAUX_evaluate_Cons_Rerr] THEN
    SUBST1_TAC(ISPECL [`h:bvi_exp`; `CONS v6 v7:bvi_exp list`; `env:bvl_v list`;
                       `s:(C,FFI)bvi_state`] bvi_evaluate_CONS) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]] THEN
  MP_TAC(ISPEC `bvi_evaluate ([bvi_Op (BlockOp (clos_Cons tag)) (CONS v6 v7)],env,
                               sh:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `t2:(C,FFI)bvi_state` ASSUME_TAC)) THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`env:bvl_v list`; `sh:(C,FFI)bvi_state`;
    `t2:(C,FFI)bvi_state`; `r2:(bvl_v list,exn_or_ret)result`; `bs2:bvi_exp list`;
    `CallBlock tag l child rr`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `as2:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `u2:(C,FFI)bvi_state` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    free_in `t2:(C,FFI)bvi_state` (concl th) && is_eq (concl th) &&
    not (is_forall (concl th)))) THEN
  DISJ_CASES_THEN2
    (X_CHOOSE_THEN `a2:bvl_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)
    (ISPEC `as2:(bvl_v list,exn_or_ret)result` (cases "result")) THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `a2:bvl_v list` o check (fun th ->
      is_forall(concl th) && type_of(fst(dest_forall(concl th))) = `:bvl_v list`)) THEN
    REWRITE_TAC[cb_to_bvi_def; LET_DEF; LET_END_DEF; BVITMCAUX_evaluate_Cons_eq] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `bvi_evaluate (CONS h bs2,env,s:(C,FFI)bvi_state) =
                  (Rval (CONS (HD v1) a2),u2)` SUBST1_TAC THENL
     [SUBST1_TAC(ISPECL [`h:bvi_exp`; `bs2:bvi_exp list`; `env:bvl_v list`;
                         `s:(C,FFI)bvi_state`] bvi_evaluate_CONS) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`Rval (CONS (HD v1) a2):(bvl_v list,exn_or_ret)result`;
                          `u2:(C,FFI)bvi_state`] THEN
    REWRITE_TAC[injectivity "result"; distinctness "result"] THEN
    X_GEN_TAC `vs:bvl_v list` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[cb_to_bvi_def; LET_DEF; LET_END_DEF; BVITMCAUX_evaluate_Cons_eq;
                MAP; APPEND] THEN
    CONJ_TAC THENL [ALL_TAC; X_GEN_TAC `extras:bvl_v list`] THEN
    GEN_REWRITE_TAC LAND_CONV [bvi_evaluate_CONS] THEN
    GEN_REWRITE_TAC RAND_CONV [bvi_evaluate_CONS] THEN
    REWRITE_TAC[bvi_evaluate_def; LENGTH; LT_0; EL; HD] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[BVITMCAUX_evaluate_shift_args; HD] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[HD] THEN CASE_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[] o SPEC `e:(exn_or_ret)error_result` o
      check (fun th -> is_forall(concl th) &&
        type_of(fst(dest_forall(concl th))) = `:(exn_or_ret)error_result`)) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[BVITMCAUX_evaluate_Cons_Rerr] o SYM) THEN
    SUBGOAL_THEN `bvi_evaluate (CONS h bs2,env,s:(C,FFI)bvi_state) = (Rerr e,u2)`
      SUBST1_TAC THENL
     [SUBST1_TAC(ISPECL [`h:bvi_exp`; `bs2:bvi_exp list`; `env:bvl_v list`;
                         `s:(C,FFI)bvi_state`] bvi_evaluate_CONS) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`Rerr e:(bvl_v list,exn_or_ret)result`;
                          `u2:(C,FFI)bvi_state`] THEN
    REWRITE_TAC[injectivity "result"; distinctness "result"] THEN
    GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
    CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[BVITMCAUX_evaluate_Cons_Rerr] THEN
    SUBST1_TAC(ISPECL [`h:bvi_exp`; `CONS v6 v7:bvi_exp list`; `env:bvl_v list`;
                       `s:(C,FFI)bvi_state`] bvi_evaluate_CONS) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]]);;

(* HOL4 [local] *)
let evaluate_bvi_to_cb_aux_inr_lemma = prove
 (`(!n loc tag exp env (s:(C,FFI)bvi_state) t r bs cb.
      bvi_to_cb_aux_sing n loc tag exp = SOME (bs,INR cb) /\
      bvi_evaluate ([bvi_Op (BlockOp (clos_Cons tag)) [exp]],env,s) = (r,t) /\
      n <= LENGTH env ==>
      ?as u.
        bvi_evaluate (bs,env,s) = (as,u) /\
        (!vs. as = Rval vs ==>
              bvi_evaluate ([cb_to_bvi loc cb],vs,u) = (r,t) /\
              !extras. bvi_evaluate ([cb_to_bvi loc cb],APPEND vs extras,u) = (r,t)) /\
        (!e. as = Rerr e ==> (as,u) = (r,t))) /\
   (!n loc tag args env (s:(C,FFI)bvi_state) t r bs cb.
      bvi_to_cb_aux n loc tag args = SOME (bs,INR cb) /\
      bvi_evaluate ([bvi_Op (BlockOp (clos_Cons tag)) args],env,s) = (r,t) /\
      n <= LENGTH env ==>
      ?as u.
        bvi_evaluate (bs,env,s) = (as,u) /\
        (!vs. as = Rval vs ==>
              bvi_evaluate ([cb_to_bvi loc cb],vs,u) = (r,t) /\
              !extras. bvi_evaluate ([cb_to_bvi loc cb],APPEND vs extras,u) = (r,t)) /\
        (!e. as = Rerr e ==> (as,u) = (r,t)))`,
  MATCH_MP_TAC bvi_to_cb_aux_ind THEN REPEAT CONJ_TAC THENL
   [(* Call *)
    REPEAT GEN_TAC THEN DISCH_THEN(ACCEPT_TAC o MATCH_MP BVITMCAUX_inr_call);
    (* Op *)
    REPEAT GEN_TAC THEN DISCH_THEN(fun ih -> REPEAT GEN_TAC THEN
      DISCH_THEN(fun h -> ACCEPT_TAC(MATCH_MP BVITMCAUX_inr_op (CONJ ih h))));
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;
    (* [exp] *)
    REWRITE_TAC[bvi_to_cb_aux_def];
    (* CONS h (CONS v6 v7) *)
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "iht") (LABEL_TAC "ihh")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o
                  MATCH_MP BVITMCAUX_cb_aux_cons_inr_inv) THEN
    RVEQ_TAC THENL
     [REMOVE_THEN "ihh" (MP_TAC o SPECL [`bs2:bvi_exp list`; `vs2:num list`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`n:num`; `loc:num`; `tag:num`; `h:bvi_exp`; `v6:bvi_exp`;
        `v7:bvi_exp list`; `env:bvl_v list`; `s:(C,FFI)bvi_state`;
        `t:(C,FFI)bvi_state`; `r:(bvl_v list,exn_or_ret)result`; `bs1:bvi_exp list`;
        `bs2:bvi_exp list`; `vs2:num list`; `child:call_block`]
        BVITMCAUX_inr_cons_inl) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`n:num`; `loc:num`; `tag:num`; `h:bvi_exp`; `v6:bvi_exp`;
        `v7:bvi_exp list`; `env:bvl_v list`; `s:(C,FFI)bvi_state`;
        `t:(C,FFI)bvi_state`; `r:(bvl_v list,exn_or_ret)result`; `bs2:bvi_exp list`;
        `l:num list`; `child:call_block`; `rr:num list`]
        BVITMCAUX_inr_cons_inr) THEN
      ASM_REWRITE_TAC[]]] THEN
  (* the remaining sing cases and [] give no INR *)
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_to_cb_aux_def] THEN TRY COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "option"; option_INJ; PAIR_EQ; distinctness "sum"]);;

let evaluate_bvi_to_cb_aux_inr = CONJUNCT2 evaluate_bvi_to_cb_aux_inr_lemma;;

let evaluate_bvi_to_cb = prove
 (`!cb n loc x env (s:(C,FFI)bvi_state) t r bs.
     bvi_evaluate ([x],env,s) = (r,t) /\
     bvi_to_cb n loc x = SOME (bs,cb) /\
     n <= LENGTH env ==>
     bvi_evaluate ([bvi_Let bs (cb_to_bvi loc cb)],env,s) = (r,t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_THEN MP_TAC o MATCH_MP bvi_to_cb_cases) THENL
   [DISCH_THEN(X_CHOOSE_THEN `tag:num` (X_CHOOSE_THEN `args:bvi_exp list`
      (X_CHOOSE_THEN `l:num list` (X_CHOOSE_THEN `child:call_block`
        (X_CHOOSE_THEN `rr:num list` (CONJUNCTS_THEN SUBST_ALL_TAC)))))) THEN
    SUBGOAL_THEN `bvi_to_cb_aux n loc tag args = SOME (bs,INR (CallBlock tag l child rr))`
      ASSUME_TAC THENL
     [UNDISCH_TAC `bvi_to_cb n loc (bvi_Op (BlockOp (clos_Cons tag)) args) =
                   SOME (bs,CallBlock tag l child rr)` THEN
      REWRITE_TAC[bvi_to_cb_def; bvi_tmc_dest_Cons_def] THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[option_case_eq; pair_case_eq; sum_case_eq; distinctness "option";
                  option_INJ; PAIR_EQ] THEN
      STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`n:num`; `loc:num`; `tag:num`; `args:bvi_exp list`; `env:bvl_v list`;
      `s:(C,FFI)bvi_state`; `t:(C,FFI)bvi_state`; `r:(bvl_v list,exn_or_ret)result`;
      `bs:bvi_exp list`; `CallBlock tag l child rr`] evaluate_bvi_to_cb_aux_inr) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `as:(bvl_v list,exn_or_ret)result`
      (X_CHOOSE_THEN `u:(C,FFI)bvi_state` STRIP_ASSUME_TAC)) THEN
    GEN_REWRITE_TAC LAND_CONV [bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
    DISJ_CASES_THEN2
      (X_CHOOSE_THEN `vs:bvl_v list` SUBST_ALL_TAC)
      (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)
      (ISPEC `as:(bvl_v list,exn_or_ret)result` (cases "result")) THEN
    CASE_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "result"; distinctness "result"]) THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `vs:bvl_v list` o check (is_forall o concl)) THEN
      REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SPEC `env:bvl_v list` o CONJUNCT2);
      FIRST_X_ASSUM(MP_TAC o SPEC `e:(exn_or_ret)error_result` o
                    check (is_forall o concl)) THEN
      REWRITE_TAC[PAIR_EQ]];
    DISCH_THEN(X_CHOOSE_THEN `ts:num` (X_CHOOSE_THEN `args:bvi_exp list`
      (X_CHOOSE_THEN `vs:num list` (CONJUNCTS_THEN SUBST_ALL_TAC)))) THEN
    UNDISCH_TAC `bvi_to_cb n loc (bvi_Call ts (SOME loc) args NONE) =
                 SOME (bs,RCall ts vs)` THEN
    REWRITE_TAC[bvi_to_cb_def; call_to_cb_def] THEN
    MP_TAC(ISPEC `bind 0 (args:bvi_exp list)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `vs':num list` (X_CHOOSE_THEN `n':num` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_INJ; PAIR_EQ; injectivity "call_block"] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[cb_to_bvi_def; LET_DEF; LET_END_DEF] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      free_in `r:(bvl_v list,exn_or_ret)result` (concl th))) THEN
    GEN_REWRITE_TAC LAND_CONV [bvi_evaluate_def] THEN
    MP_TAC(ISPEC `bvi_evaluate (args,env,s:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `as:(bvl_v list,exn_or_ret)result`
      (X_CHOOSE_THEN `u:(C,FFI)bvi_state` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    DISJ_CASES_THEN2
      (X_CHOOSE_THEN `avs:bvl_v list` SUBST_ALL_TAC)
      (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)
      (ISPEC `as:(bvl_v list,exn_or_ret)result` (cases "result")) THEN
    CASE_REWRITE_TAC[] THENL
     [MATCH_MP_TAC BVITMCAUX_evaluate_Call_cong THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC evaluate_vars_expand_env THEN
      MP_TAC(ISPECL [`args:bvi_exp list`; `env:bvl_v list`; `s:(C,FFI)bvi_state`;
        `u:(C,FFI)bvi_state`; `vs':num list`; `avs:bvl_v list`; `0`; `n':num`]
        evaluate_binders) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `[]:bvl_v list`) THEN
      REWRITE_TAC[LENGTH; APPEND];
      REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN
      CASE_REWRITE_TAC[]]]);;

(* HOL4 [local] *)
let WF_I_I = prove
 (`WF (measure (I:num->num) LEX measure (I:num->num))`,
  MATCH_MP_TAC WF_LEX_HOL4 THEN REWRITE_TAC[WF_measure]);;

let optimised_code_def = cake_def
 `optimised_code loc loc_opt (c1:(num#bvi_exp)spt) (c2:(num#bvi_exp)spt) <=>
    ?arity body body_wrap body_work.
      lookup loc c1 = SOME (arity,body) /\
      lookup loc c2 = SOME (arity,body_wrap) /\
      lookup loc_opt c2 = SOME (arity + 2,body_work) /\
      rewrite_wrapper loc loc_opt arity body = SOME body_wrap /\
      rewrite_worker loc loc_opt arity (arity + 1) arity body = body_work`;;

(* evaluate_rewrite_tmc (HOL4: stated here, proved in pieces with suspend and *)
(* resume) is proved below, at the place of HOL4's Finalise, from one lemma  *)
(* per case.                                                                 *)

let hypothesis_def = cake_def
 `hypothesis xs' (s'':(num#C,FFI)bvi_state) clock <=>
    bvi_state_clock s'' < clock ==>
    !env1' r' t' opt' f' s''' env2' loc'.
      bvi_evaluate (xs',env1',s'') = (r',t') /\
      bvi_tmcProof_env_rel opt' f' env1' env2' /\ ALL (\x. no_mutcons x) xs' /\
      bvi_tmcProof_state_rel f' s'' s''' /\
      (opt' ==> LENGTH xs' = 1) /\
      ~(r' = Rerr (Rabort Rtype_error)) ==>
      ?t'' f'' r''.
        bvi_evaluate (xs',env2',s''') = (r'',t'') /\
        result_rel (ALL2 (bvi_tmcProof_v_rel f'')) (eor_rel f'') r' r'' /\
        bvi_tmcProof_state_rel f'' t' t'' /\ f' SUBMAP f'' /\
        only_fresh f' f'' (bvi_state_refs s''') /\
        holes_unchanged_except f' (bvi_state_refs s''') (bvi_state_refs t'') {} /\
        holes_still_not_finalised f' (bvi_state_refs s''') (bvi_state_refs t'') /\
        !loc_opt.
          optimised_code loc' loc_opt (bvi_state_code s'') (bvi_state_code s''') ==>
          (!wrap.
             LENGTH xs' = 1 /\
             rewrite_wrapper loc' loc_opt (LENGTH env1') (HD xs') = SOME wrap ==>
             ?t_wrap f_wrap r_wrap.
               bvi_evaluate ([wrap],env2',s''') = (r_wrap,t_wrap) /\
               result_rel (ALL2 (bvi_tmcProof_v_rel f_wrap)) (eor_rel f_wrap) r' r_wrap /\
               bvi_tmcProof_state_rel f_wrap t' t_wrap /\ f' SUBMAP f_wrap /\
               only_fresh f' f_wrap (bvi_state_refs s''') /\
               holes_unchanged_except f' (bvi_state_refs s''') (bvi_state_refs t_wrap) {} /\
               holes_still_not_finalised f' (bvi_state_refs s''') (bvi_state_refs t_wrap)) /\
          (opt' ==>
           !hole_ptr.
             (?c. hole_has_val f' env1' env2' (bvi_state_refs s''') c) /\
             hole_not_finalised (bvi_state_refs s''') hole_ptr /\
             EL (LENGTH env1') env2' = bvl_RefPtr F hole_ptr ==>
             ?r_work f_work t_work.
               bvi_evaluate
                 ([rewrite_worker loc' loc_opt (LENGTH env1') (LENGTH env1' + 1)
                     (LENGTH env1') (HD xs')],env2',s''') = (r_work,t_work) /\
               opt_res_rel f_work r' r_work /\
               bvi_tmcProof_state_rel f_work t' t_work /\ f' SUBMAP f_work /\
               only_fresh f' f_work (bvi_state_refs s''') /\
               holes_unchanged_except f' (bvi_state_refs s''') (bvi_state_refs t_work)
                 {hole_ptr} /\
               holes_still_not_finalised f' (bvi_state_refs s''') (bvi_state_refs t_work) /\
               !res_v.
                 r' = Rval [res_v] ==>
                 ?res_v'.
                   mb_rel f_work (bvi_state_refs s''') (bvi_state_refs t_work \\ hole_ptr)
                     res_v res_v' /\
                   hole_has_val f' env1' env2' (bvi_state_refs t_work) res_v')`;;

let alloc_hole_has_val_def = cake_def
 `alloc_hole_has_val (f:(num,num)fmap) (refs:(num,(bvl_v)bvl_ref)fmap) extras i_ptr
                     c_idx c <=>
    ?hole_ptr tag left right.
      i_ptr < LENGTH extras /\
      EL i_ptr extras = bvl_RefPtr F hole_ptr /\
      c_idx = LENGTH left /\
      small_enough_int (&(LENGTH left)) /\
      ~(hole_ptr IN FRANGE f) /\
      FLOOKUP refs hole_ptr = SOME (MutBlock tag F left c right)`;;

let wf_vars_list_rel = prove
 (`!vars opt f env1 env2.
     bvi_tmcProof_env_rel opt f env1 env2 /\ wf_vars (LENGTH env1) vars ==>
     ALL2 (bvi_tmcProof_v_rel f) (MAP (\n. EL n env1) vars) (MAP (\n. EL n env2) vars)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL2; wf_vars_def; ALL] THEN
  REWRITE_TAC[GSYM wf_vars_def] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[env_rel_el_v_rel]; ASM_MESON_TAC[]]);;

let wf_vars_env_rel = prove
 (`!vars opt f env1 env2.
     bvi_tmcProof_env_rel opt f env1 env2 /\ wf_vars (LENGTH env1) vars ==>
     bvi_tmcProof_env_rel F f (MAP (\n. EL n env1) vars) (MAP (\n. EL n env2) vars)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC list_rel_env_rel THEN
  MATCH_MP_TAC wf_vars_list_rel THEN ASM_MESON_TAC[]);;

let wf_vars_env_rel_opt = prove
 (`!vars opt f env1 env2 ptr idx.
     bvi_tmcProof_env_rel opt f env1 env2 /\
     wf_vars (LENGTH env1) vars /\
     small_enough_int idx ==>
     bvi_tmcProof_env_rel T f (MAP (\n. EL n env1) vars)
       (APPEND (MAP (\n. EL n env2) vars) [bvl_RefPtr F ptr; bvl_Number idx])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvi_tmcProof_env_rel_def] THEN
  MAP_EVERY EXISTS_TAC [`MAP (\n. EL n env2) vars:bvl_v list`;
                        `[bvl_RefPtr F ptr; bvl_Number idx]`] THEN
  REWRITE_TAC[LENGTH; BVITMCAUX_EL_01; ARITH_RULE `SUC (SUC 0) = 2`] THEN
  CONJ_TAC THENL [MATCH_MP_TAC wf_vars_list_rel THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let state_ref_rel_sub = prove
 (`!ptr f s_refs t_refs.
     ~(ptr IN FRANGE f) /\ state_ref_rel f s_refs t_refs ==>
     state_ref_rel f s_refs (t_refs \\ ptr)`,
  REWRITE_TAC[state_ref_rel_def; DOMSUB_FLOOKUP_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `v:(bvl_v)bvl_ref`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`j:num`; `w:(bvl_v)bvl_ref`] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `~(ptr IN FRANGE (f:(num,num)fmap))` THEN
  REWRITE_TAC[FRANGE_FLOOKUP] THEN ASM_MESON_TAC[]);;

let holes_unchanged_except_finalised = prove
 (`!(f:(A,B)fmap) (p:D) ptr (r1:(B,(C)bvl_ref)fmap) r2 tag fin1 left child right fin2.
     holes_unchanged_except f (r1 \\ ptr) r2 {} /\
     FLOOKUP r1 ptr = SOME (MutBlock tag fin1 left child right) /\
     ~(ptr IN FRANGE f) ==>
     holes_unchanged_except f r1 (r2 |+ (ptr,MutBlock tag fin2 left child right)) {}`,
  REWRITE_TAC[holes_unchanged_except_def; DOMSUB_FLOOKUP_THM; FLOOKUP_UPDATE;
              NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `ptr:B = ptr'` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `FLOOKUP (r1:(B,(C)bvl_ref)fmap) ptr =
                 SOME (MutBlock tag' finalised left' child' right')` THEN
    ASM_REWRITE_TAC[option_INJ; injectivity "bvl_ref"] THEN MESON_TAC[];
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let holes_still_not_finalised_sub = prove
 (`!ptr (refs:(B,(C)bvl_ref)fmap) (f:(A,B)fmap) refs'.
     ~(ptr IN FDOM refs) /\ holes_still_not_finalised f refs refs' ==>
     holes_still_not_finalised f refs (refs' \\ ptr)`,
  REWRITE_TAC[holes_still_not_finalised_def; hole_not_finalised_def;
              DOMSUB_FLOOKUP_THM] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `~(ptr IN FDOM (refs:(B,(C)bvl_ref)fmap))` THEN
    ASM_REWRITE_TAC[FDOM_FLOOKUP; option_DISTINCT];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let holes_still_not_finalised_non_dom = prove
 (`!(f:(A,B)fmap) (refs:(B,(C)bvl_ref)fmap) refs' ptr tag l c r.
     holes_still_not_finalised f refs refs' /\ ~(ptr IN FDOM refs) ==>
     holes_still_not_finalised f refs (refs' |+ (ptr,MutBlock tag T l c r))`,
  REWRITE_TAC[holes_still_not_finalised_def; hole_not_finalised_def;
              FLOOKUP_UPDATE] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `~(ptr IN FDOM (refs:(B,(C)bvl_ref)fmap))` THEN
    ASM_REWRITE_TAC[FDOM_FLOOKUP; option_DISTINCT];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let BVITMCAUX_mb_rel_Block_RefPtr = prove
 (`!f r1 r2 tag xs b ptr.
     mb_rel f r1 r2 (bvl_Block tag xs) (bvl_RefPtr b ptr) <=>
     ~b /\ ~(ptr IN FRANGE f) /\ ~(ptr IN FDOM r1) /\
     ?left' child' right' left child right.
       FLOOKUP r2 ptr = SOME (MutBlock tag F left' child' right') /\
       xs = APPEND (APPEND left [child]) right /\
       ALL2 (bvi_tmcProof_v_rel f) left left' /\
       mb_rel f r1 (r2 \\ ptr) child child' /\
       ALL2 (bvi_tmcProof_v_rel f) right right'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mb_rel_def] THEN
  ASM_CASES_TAC `b \/ ptr IN FRANGE (f:(num,num)fmap) \/
                 ptr IN FDOM (r1:(num,(bvl_v)bvl_ref)fmap)` THEN
  ASM_REWRITE_TAC[] THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[DISJ_ASSOC]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (r2:(num,(bvl_v)bvl_ref)fmap) ptr` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; option_INJ] THEN
  CASES_ON `a:(bvl_v)bvl_ref` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "bvl_ref"; injectivity "bvl_ref"] THEN MESON_TAC[]);;

let BVITMCAUX_mb_rel_v_rel = prove
 (`!f r1 r2 v1 v2.
     ~((?tag xs. v1 = bvl_Block tag xs) /\ (?b ptr. v2 = bvl_RefPtr b ptr)) ==>
     (mb_rel f r1 r2 v1 v2 <=> bvi_tmcProof_v_rel f v1 v2)`,
  REPEAT GEN_TAC THEN CASES_ON `v1:bvl_v` THEN CASES_ON `v2:bvl_v` THEN
  REWRITE_TAC[mb_rel_def; distinctness "bvl_v"; injectivity "bvl_v"] THEN
  MESON_TAC[]);;

let evaluate_finalise_cons = prove
 (`!v2 (t_refs:(num,(bvl_v)bvl_ref)fmap) (f:(num,num)fmap) f' u_refs v1
    (s_refs:(num,(bvl_v)bvl_ref)fmap).
     state_ref_rel f' u_refs t_refs /\
     mb_rel f' s_refs t_refs v1 v2 /\
     holes_still_not_finalised f s_refs t_refs ==>
     ?v3 t_refs'.
       bvi_finalise_cons v2 t_refs = SOME (v3,t_refs') /\
       bvi_tmcProof_v_rel f' v1 v3 /\
       state_ref_rel f' u_refs t_refs' /\
       holes_unchanged_except f' t_refs t_refs' {} /\
       holes_still_not_finalised f s_refs t_refs'`,
  let EXX = MESON[] `!(a:A) (b:B) P. (?x y. (a = x /\ b = y) /\ P x y) <=> P a b` in
  MATCH_MP_TAC bvi_finalise_cons_ind THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`b:bool`; `ptr:num`; `refs:(num,(bvl_v)bvl_ref)fmap`] THEN
    DISCH_THEN(LABEL_TAC "ih") THEN
    MAP_EVERY X_GEN_TAC [`f:(num,num)fmap`; `f':(num,num)fmap`;
      `u_refs:(num,(bvl_v)bvl_ref)fmap`; `v1:bvl_v`;
      `s_refs:(num,(bvl_v)bvl_ref)fmap`] THEN
    ASM_CASES_TAC `?tag xs. v1 = bvl_Block tag xs` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `tag:num` (X_CHOOSE_THEN `xs:bvl_v list`
        SUBST_ALL_TAC)) THEN
      REWRITE_TAC[BVITMCAUX_mb_rel_Block_RefPtr] THEN STRIP_TAC THEN
      REMOVE_THEN "ih" (MP_TAC o SPECL [`tag:num`; `left':bvl_v list`;
        `right':bvl_v list`; `F`; `child':bvl_v`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`f:(num,num)fmap`; `f':(num,num)fmap`;
        `u_refs:(num,(bvl_v)bvl_ref)fmap`; `child:bvl_v`;
        `s_refs:(num,(bvl_v)bvl_ref)fmap`]) THEN
      ASM_SIMP_TAC[state_ref_rel_sub; holes_still_not_finalised_sub] THEN
      DISCH_THEN(X_CHOOSE_THEN `v3:bvl_v` (X_CHOOSE_THEN
        `t_refs':(num,(bvl_v)bvl_ref)fmap` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[bvi_finalise_cons_def] THEN CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[option_INJ; PAIR_EQ; EXX] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[BVITMCAUX_v_rel_simps; injectivity "bvl_v"; UNWIND_THM1] THEN
        REPEAT(MATCH_MP_TAC LIST_REL_APPEND_suff THEN CONJ_TAC) THEN
        ASM_REWRITE_TAC[ALL2];
        MATCH_MP_TAC state_ref_rel_filled THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC holes_unchanged_except_finalised THEN
        EXISTS_TAC `F` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC holes_still_not_finalised_non_dom THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `mb_rel f' s_refs refs v1 (bvl_RefPtr b ptr) <=>
                  bvi_tmcProof_v_rel f' v1 (bvl_RefPtr b ptr)` SUBST1_TAC THENL
     [MATCH_MP_TAC BVITMCAUX_mb_rel_v_rel THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[BVITMCAUX_v_rel_simps] THEN STRIP_TAC THEN RVEQ_TAC THEN
    SUBGOAL_THEN `?v w. FLOOKUP (u_refs:(num,(bvl_v)bvl_ref)fmap) n = SOME v /\
                        bvi_tmcProof_ref_rel f' v w /\
                        FLOOKUP (refs:(num,(bvl_v)bvl_ref)fmap) ptr = SOME w`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `state_ref_rel f' u_refs (refs:(num,(bvl_v)bvl_ref)fmap)` THEN
      REWRITE_TAC[state_ref_rel_def] THEN STRIP_TAC THEN
      SUBGOAL_THEN `?v. FLOOKUP (u_refs:(num,(bvl_v)bvl_ref)fmap) n = SOME v`
        STRIP_ASSUME_TAC THENL
       [MP_TAC(ISPEC `FLOOKUP (u_refs:(num,(bvl_v)bvl_ref)fmap) n` option_nchotomy) THEN
        REWRITE_TAC[flookup_thm] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
        ASM_REWRITE_TAC[FDOM_FLOOKUP; option_DISTINCT];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:(bvl_v)bvl_ref`]) THEN
      ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`bvl_RefPtr b ptr`; `refs:(num,(bvl_v)bvl_ref)fmap`] THEN
    ASM_REWRITE_TAC[bvi_finalise_cons_def; holes_unchanged_except_refl;
                    BVITMCAUX_v_rel_simps] THEN
    CASE_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    CASES_ON `w:(bvl_v)bvl_ref` THEN CASE_REWRITE_TAC[] THEN
    ASM_MESON_TAC[BVITMCAUX_ref_rel_simps];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bvi_finalise_cons_def; option_INJ; PAIR_EQ; EXX; holes_unchanged_except_refl] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (BVITMCAUX_head_is "mb_rel")) THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC BVITMCAUX_mb_rel_v_rel THEN
  REWRITE_TAC[distinctness "bvl_v"]);;

let code_rel_cases = prove
 (`!loc arity body1 c1 c2.
     lookup loc c1 = SOME (arity,body1) /\ bvi_tmcProof_code_rel c1 c2 ==>
     no_mutcons body1 /\
     ?loc_opt body2.
       lookup loc c2 = SOME (arity,body2) /\
       (~(body1 = body2) ==>
        optimised_code loc loc_opt c1 c2 /\
        rewrite_wrapper loc loc_opt arity body1 = SOME body2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_tmcProof_code_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`loc:num`; `arity:num`; `body1:bvi_exp`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `bvi_tmc_compile_exp loc n arity body1 = NONE` THENL
   [MAP_EVERY EXISTS_TAC [`n:num`; `body1:bvi_exp`] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(bvi_tmc_compile_exp loc n arity body1 = NONE)` THEN
  REWRITE_TAC[bvi_tmc_compile_exp_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPEC `rewrite_wrapper loc n arity body1` option_nchotomy) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_TAC `wrap:bvi_exp`)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`wrap:bvi_exp`;
    `rewrite_worker loc n arity (arity + 1) arity body1`] o check (is_forall o concl)) THEN
  REWRITE_TAC[bvi_tmc_compile_exp_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `wrap:bvi_exp`] THEN
  ASM_REWRITE_TAC[optimised_code_def] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`arity:num`; `body1:bvi_exp`; `wrap:bvi_exp`;
    `rewrite_worker loc n arity (arity + 1) arity body1`] THEN
  ASM_REWRITE_TAC[]);;

let cons_append = prove
 (`!(v:A) l. CONS v l = APPEND [v] l`,
  REWRITE_TAC[APPEND]);;

let rw_block_args = prove
 (`!left (child:B) right (f:A->B).
     REVERSE (APPEND (APPEND (MAP f left) [child]) (MAP f right)) =
     APPEND (APPEND (MAP f (REVERSE right)) [child]) (MAP f (REVERSE left))`,
  REWRITE_TAC[REVERSE_APPEND; MAP_REVERSE; REVERSE; APPEND; GSYM APPEND_ASSOC]);;

let shift_cb_suc = prove
 (`!n cb. shift_cb (SUC (SUC n)) cb = shift_cb (n + 2) cb`,
  REWRITE_TAC[ARITH_RULE `SUC (SUC n) = n + 2`]);;

let mb_rel_refs_old_subset = prove
 (`!f r2 r3 v1 v2 (r1:(num,(bvl_v)bvl_ref)fmap).
     mb_rel f r2 r3 v1 v2 /\ FDOM r1 SUBSET FDOM r2 ==> mb_rel f r1 r3 v1 v2`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  MATCH_MP_TAC mb_rel_ind THEN CONJ_TAC THENL
   [ALL_TAC; REPEAT CONJ_TAC THEN REWRITE_TAC[mb_rel_def] THEN MESON_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`f:(num,num)fmap`; `r2:(num,(bvl_v)bvl_ref)fmap`;
    `r3:(num,(bvl_v)bvl_ref)fmap`; `tag:num`; `xs:bvl_v list`; `b:bool`; `ptr:num`] THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  REWRITE_TAC[BVITMCAUX_mb_rel_Block_RefPtr] THEN STRIP_TAC THEN
  X_GEN_TAC `r1:(num,(bvl_v)bvl_ref)fmap` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`left':bvl_v list`; `child':bvl_v`; `right':bvl_v list`;
    `left:bvl_v list`; `child:bvl_v`; `right:bvl_v list`] THEN
  ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`tag:num`; `F`; `left':bvl_v list`;
    `right':bvl_v list`; `child:bvl_v`; `child':bvl_v`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let BVITMCAUX_call_post_def = cake_def
 `BVITMCAUX_call_post ((x:(bvl_v list,exn_or_ret)result),(s:(A,B)bvi_state)) =
    match x with
      Rval a -> (x,s)
    | Rerr (Rraise (Exn v)) -> (Rerr (Rraise (Exn v)),s)
    | Rerr (Rraise (Ret a)) -> (Rerr (Rabort Rtype_error),s)
    | Rerr (Rabort a) -> (x,s)`;;

let BVITMCAUX_evaluate_Call_NONE = prove
 (CASE_TERM `!ts dest xs env (s:(C,FFI)bvi_state).
     bvi_evaluate ([bvi_Call ts dest xs NONE],env,s) =
     match bvi_evaluate (xs,env,s) with
       (Rval vs,s1) ->
         (match bvl_find_code dest vs (bvi_state_code s1) with
            NONE -> (Rerr (Rabort Rtype_error),s1)
          | SOME (args,exp) ->
              if bvi_state_clock s1 < ts + 1
              then (Rerr (Rabort Rtimeout_error),bvi_state_clock_fupd (K 0) s1)
              else BVITMCAUX_call_post
                     (bvi_evaluate ([exp],args,bvi_dec_clock (ts + 1) s1)))
     | (Rerr e,s1) -> (Rerr e,s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_evaluate_def; IS_SOME_DEF] THEN
  MP_TAC(ISPEC `bvi_evaluate (xs,env,s:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `s1:(C,FFI)bvi_state` SUBST1_TAC)) THEN
  CASES_ON `r:(bvl_v list,exn_or_ret)result` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `bvl_find_code dest a (bvi_state_code (s1:(C,FFI)bvi_state))` THEN
  CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `a':bvl_v list#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `args:bvl_v list` (X_CHOOSE_THEN `exp:bvi_exp`
    SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPEC `bvi_evaluate ([exp],args,bvi_dec_clock (ts + 1) (s1:(C,FFI)bvi_state))`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `s2:(C,FFI)bvi_state` SUBST1_TAC)) THEN
  REWRITE_TAC[BVITMCAUX_call_post_def] THEN
  CASES_ON `r2:(bvl_v list,exn_or_ret)result` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a'':(exn_or_ret)error_result` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a''':exn_or_ret` THEN CASE_REWRITE_TAC[]);;

let BVITMCAUX_call_post_id = prove
 (`!(r:(bvl_v list,exn_or_ret)result) (s:(A,B)bvi_state).
     ~(?vs. r = Rerr (Rraise (Ret vs))) ==> BVITMCAUX_call_post (r,s) = (r,s)`,
  GEN_TAC THEN CASES_ON `r:(bvl_v list,exn_or_ret)result` THEN
  REWRITE_TAC[BVITMCAUX_call_post_def] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a:(exn_or_ret)error_result` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a':exn_or_ret` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "result"; injectivity "error_result"; injectivity "exn_or_ret";
              distinctness "result"; distinctness "error_result";
              distinctness "exn_or_ret"] THEN
  MESON_TAC[]);;

let BVITMCAUX_call_post_Ret = prove
 (`!vs (s:(A,B)bvi_state).
     BVITMCAUX_call_post (Rerr (Rraise (Ret vs)),s) = (Rerr (Rabort Rtype_error),s)`,
  REWRITE_TAC[BVITMCAUX_call_post_def] THEN CASE_REWRITE_TAC[]);;

let BVITMCAUX_result_rel_Ret = prove
 (`!f (r1:(bvl_v list,exn_or_ret)result) r2.
     result_rel (ALL2 (bvi_tmcProof_v_rel f)) (eor_rel f) r1 r2 ==>
     ((?vs. r1 = Rerr (Rraise (Ret vs))) <=> (?vs. r2 = Rerr (Rraise (Ret vs))))`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `r1:(bvl_v list,exn_or_ret)result` THEN
  REWRITE_TAC[result_rel_Rval; result_rel_Rerr1] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[distinctness "result"; injectivity "result"] THEN
  POP_ASSUM MP_TAC THEN
  CASES_ON `a:(exn_or_ret)error_result` THEN
  REWRITE_TAC[exc_rel_raise1; exc_rel_type_error1] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[injectivity "error_result"; distinctness "error_result"] THEN
  POP_ASSUM MP_TAC THEN CASES_ON `a':exn_or_ret` THEN
  CASES_ON `v':exn_or_ret` THEN
  REWRITE_TAC[eor_rel_def; injectivity "exn_or_ret"; distinctness "exn_or_ret"] THEN
  MESON_TAC[]);;

let BVITMCAUX_opt_res_rel_thm = prove
 (`!f (r1:(bvl_v list,exn_or_ret)result) r2.
     opt_res_rel f r1 r2 <=>
     (?v1. r1 = Rval v1 /\ r2 = Rval [bvl_Block 0 []]) \/
     (?e1 e2. r1 = Rerr e1 /\ r2 = Rerr e2 /\ exc_rel (eor_rel f) e1 e2)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[opt_res_rel_def] THEN
  CASES_ON `r1:(bvl_v list,exn_or_ret)result` THEN
  CASES_ON `r2:(bvl_v list,exn_or_ret)result` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "result"; injectivity "result"; UNWIND_THM1;
              UNWIND_THM2; RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; EXISTS_REFL] THEN
  CASES_ON `a':bvl_v list` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN
  CASES_ON `a0:bvl_v` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "bvl_v"; injectivity "bvl_v"; CONS_11] THEN
  CASES_ON `a1:bvl_v list` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN
  ASM_CASES_TAC `a0' = 0` THEN ASM_REWRITE_TAC[] THEN
  TRY(CASES_ON `a1':bvl_v list`) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11]);;

let BVITMCAUX_opt_res_rel_Ret = prove
 (`!f (r1:(bvl_v list,exn_or_ret)result) r2.
     opt_res_rel f r1 r2 ==>
     ((?vs. r1 = Rerr (Rraise (Ret vs))) <=> (?vs. r2 = Rerr (Rraise (Ret vs))))`,
  REWRITE_TAC[BVITMCAUX_opt_res_rel_thm] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[distinctness "result"; injectivity "result"] THEN
  POP_ASSUM MP_TAC THEN
  CASES_ON `e1:(exn_or_ret)error_result` THEN
  REWRITE_TAC[exc_rel_raise1; exc_rel_type_error1] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[injectivity "error_result"; distinctness "error_result"] THEN
  POP_ASSUM MP_TAC THEN CASES_ON `a:exn_or_ret` THEN
  CASES_ON `v':exn_or_ret` THEN
  REWRITE_TAC[eor_rel_def; injectivity "exn_or_ret"; distinctness "exn_or_ret"] THEN
  MESON_TAC[]);;

let BVITMCAUX_state_rel_dec_clock = prove
 (`!x f (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state).
     bvi_tmcProof_state_rel f s s' ==>
     bvi_tmcProof_state_rel f (bvi_dec_clock x s) (bvi_dec_clock x s')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvi_dec_clock_def] THEN
  SUBGOAL_THEN `bvi_state_clock (s':(C,FFI)bvi_state) = bvi_state_clock (s:(num#C,FFI)bvi_state)`
    SUBST1_TAC THENL
   [ASM_MESON_TAC[bvi_tmcProof_state_rel_def]; ALL_TAC] THEN
  MATCH_MP_TAC bvi_tmcProof_state_rel_with_clock THEN ASM_REWRITE_TAC[]);;

let BVITMCAUX_dec_clock_simps = prove
 (`!x (s:(C,FFI)bvi_state).
     bvi_state_code (bvi_dec_clock x s) = bvi_state_code s /\
     bvi_state_refs (bvi_dec_clock x s) = bvi_state_refs s /\
     bvi_state_clock (bvi_dec_clock x s) = bvi_state_clock s - x`,
  REWRITE_TAC[bvi_dec_clock_def; bvi_state_INFO.ri_accfupds; K_THM]);;

let BVITMCAUX_find_code_SOME = prove
 (CASE_TERM `!p (args:bvl_v list) (code:(num#bvi_exp)spt).
     bvl_find_code (SOME p) args code =
     match lookup p code with
       NONE -> NONE
     | SOME (arity,exp) -> if LENGTH args = arity then SOME (args,exp) else NONE`,
  REWRITE_TAC[bvl_find_code_def]);;

let BVITMCAUX_cb_rcall_main = prove
 (`!ts args loc f opt env env2 (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) t r
    clock.
     bvi_evaluate ([cb_to_bvi loc (RCall ts args)],env,s) = (r,t) /\
     wf_cb (LENGTH env) (RCall ts args) /\
     bvi_tmcProof_env_rel opt f env env2 /\
     bvi_tmcProof_state_rel f s s' /\
     bvi_state_clock s <= clock /\
     ~(r = Rerr (Rabort Rtype_error)) /\
     (!xs' (s'':(num#C,FFI)bvi_state). hypothesis xs' s'' clock) ==>
     ?r' t' f'.
       bvi_evaluate ([cb_to_bvi loc (RCall ts args)],env2,s') = (r',t') /\
       result_rel (ALL2 (bvi_tmcProof_v_rel f')) (eor_rel f') r r' /\
       bvi_tmcProof_state_rel f' t t' /\ f SUBMAP f' /\
       only_fresh f f' (bvi_state_refs s') /\
       holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t') {} /\
       holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t')`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wf_cb_def; cb_to_bvi_def; LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  SUBGOAL_THEN `bvi_evaluate (MAP (\n. bvi_Var n) args,env,s:(num#C,FFI)bvi_state) =
                (Rval (MAP (\n. EL n env) args),s)` ASSUME_TAC THENL
   [MATCH_MP_TAC evaluate_vars_source THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `bvi_evaluate (MAP (\n. bvi_Var n) args,env2,s':(C,FFI)bvi_state) =
                (Rval (MAP (\n. EL n env2) args),s')` ASSUME_TAC THENL
   [MATCH_MP_TAC evaluate_vars_target THEN EXISTS_TAC `LENGTH (env:bvl_v list)` THEN
    ASM_MESON_TAC[bvi_tmcProof_env_rel_length]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL2 (bvi_tmcProof_v_rel f) (MAP (\n. EL n env) args)
                     (MAP (\n. EL n env2) args)` ASSUME_TAC THENL
   [MATCH_MP_TAC wf_vars_list_rel THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    free_in `r:(bvl_v list,exn_or_ret)result` (concl th) && is_eq (concl th))) THEN
  ASM_REWRITE_TAC[BVITMCAUX_evaluate_Call_NONE; BVITMCAUX_find_code_SOME] THEN
  CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `lookup loc (bvi_state_code (s:(num#C,FFI)bvi_state))` option_nchotomy) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `ae:num#bvi_exp`
    (fun th -> ASSUME_TAC th THEN SUBST1_TAC th))) THEN
  CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `ae:num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `exp:bvi_exp` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `LENGTH (MAP (\n. EL n (env:bvl_v list)) args) = arity` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]] THEN
  MP_TAC(SPECL [`loc:num`; `arity:num`; `exp:bvi_exp`;
    `bvi_state_code (s:(num#C,FFI)bvi_state)`; `bvi_state_code (s':(C,FFI)bvi_state)`]
    code_rel_cases) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[bvi_tmcProof_state_rel_def]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `loc_opt:num`
    (X_CHOOSE_THEN `body2:bvi_exp` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (MAP (\n. EL n (env2:bvl_v list)) args) = arity`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[LENGTH_MAP]; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bvi_state_clock (s':(C,FFI)bvi_state) =
                bvi_state_clock (s:(num#C,FFI)bvi_state)` SUBST1_TAC THENL
   [ASM_MESON_TAC[bvi_tmcProof_state_rel_def]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`Rerr (Rabort Rtimeout_error):(bvl_v list,exn_or_ret)result`;
      `bvi_state_clock_fupd (K 0) (s':(C,FFI)bvi_state)`; `f:(num,num)fmap`] THEN
    ASM_SIMP_TAC[bvi_tmcProof_state_rel_with_clock; SUBMAP_REFL; only_fresh_refl;
      holes_unchanged_except_refl; holes_still_not_finalised_refl;
      bvi_state_INFO.ri_accfupds; result_rel_def; exc_rel_def];
    ALL_TAC] THEN
  MP_TAC(ISPEC `bvi_evaluate ([exp],MAP (\n. EL n env) args,
                              bvi_dec_clock (ts + 1) (s:(num#C,FFI)bvi_state))`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `t1:(num#C,FFI)bvi_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `?vs. r1 = Rerr (Rraise (Ret vs)):(bvl_v list,exn_or_ret)result` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `vs:bvl_v list` SUBST_ALL_TAC) THEN
    REWRITE_TAC[BVITMCAUX_call_post_Ret; PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[BVITMCAUX_call_post_id] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`[exp:bvi_exp]`;
    `bvi_dec_clock (ts + 1) (s:(num#C,FFI)bvi_state)`] o
    check (fun th -> try fst(dest_const(fst(strip_comb(snd(strip_forall(concl th)))))) =
                         "hypothesis" with Failure _ -> false)) THEN
  REWRITE_TAC[hypothesis_def; BVITMCAUX_dec_clock_simps] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`MAP (\n. EL n env) args:bvl_v list`;
    `r:(bvl_v list,exn_or_ret)result`; `t:(num#C,FFI)bvi_state`; `F`;
    `f:(num,num)fmap`; `bvi_dec_clock (ts + 1) (s':(C,FFI)bvi_state)`;
    `MAP (\n. EL n env2) args:bvl_v list`; `loc:num`]) THEN
  ASM_REWRITE_TAC[ALL; LENGTH; BVITMCAUX_dec_clock_simps; HD] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[list_rel_env_rel; BVITMCAUX_state_rel_dec_clock]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)bvi_state` (X_CHOOSE_THEN `f2:(num,num)fmap`
    (X_CHOOSE_THEN `r2:(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
  ASM_CASES_TAC `exp:bvi_exp = body2` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(?vs. r2 = Rerr (Rraise (Ret vs)):(bvl_v list,exn_or_ret)result)`
      ASSUME_TAC THENL [ASM_MESON_TAC[BVITMCAUX_result_rel_Ret]; ALL_TAC] THEN
    ASM_SIMP_TAC[BVITMCAUX_call_post_id] THEN
    MAP_EVERY EXISTS_TAC [`r2:(bvl_v list,exn_or_ret)result`; `t2:(C,FFI)bvi_state`;
                          `f2:(num,num)fmap`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_var(fst(dest_forall(concl th)))) =
                                              "loc_opt" with Failure _ -> false)) THEN
  DISCH_THEN(MP_TAC o SPEC `loc_opt:num`) THEN
  REWRITE_TAC[BVITMCAUX_dec_clock_simps] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `body2:bvi_exp`) THEN
  ASM_REWRITE_TAC[LENGTH; HD; ONE] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tw:(C,FFI)bvi_state` (X_CHOOSE_THEN `fw:(num,num)fmap`
    (X_CHOOSE_THEN `rw:(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(?vs. rw = Rerr (Rraise (Ret vs)):(bvl_v list,exn_or_ret)result)`
    ASSUME_TAC THENL [ASM_MESON_TAC[BVITMCAUX_result_rel_Ret]; ALL_TAC] THEN
  ASM_SIMP_TAC[BVITMCAUX_call_post_id] THEN
  MAP_EVERY EXISTS_TAC [`rw:(bvl_v list,exn_or_ret)result`; `tw:(C,FFI)bvi_state`;
                        `fw:(num,num)fmap`] THEN
  ASM_REWRITE_TAC[]);;

let BVITMCAUX_rcall_work_core = prove
 (`!ts loc loc_opt f (s:(num#C,FFI)bvi_state) (s2:(C,FFI)bvi_state) t r clock vs vs'
    exp arity hp tag left c right xs env2.
     lookup loc (bvi_state_code s) = SOME (arity,exp) /\ LENGTH vs = arity /\
     (if bvi_state_clock s < ts + 1
      then (Rerr (Rabort Rtimeout_error),bvi_state_clock_fupd (K 0) s)
      else BVITMCAUX_call_post (bvi_evaluate ([exp],vs,bvi_dec_clock (ts + 1) s))) =
       (r,t) /\
     ~(r = Rerr (Rabort Rtype_error)) /\ no_mutcons exp /\
     bvi_state_clock s <= clock /\
     (!xs' (s'':(num#C,FFI)bvi_state). hypothesis xs' s'' clock) /\
     bvi_tmcProof_state_rel f s s2 /\
     optimised_code loc loc_opt (bvi_state_code s) (bvi_state_code s2) /\
     ALL2 (bvi_tmcProof_v_rel f) vs vs' /\
     ~(hp IN FRANGE f) /\
     FLOOKUP (bvi_state_refs s2) hp = SOME (MutBlock tag F left c right) /\
     small_enough_int (&(LENGTH left)) /\
     bvi_evaluate (xs,env2,s2) =
       (Rval (APPEND vs' [bvl_RefPtr F hp; bvl_Number (&(LENGTH left))]),s2) ==>
     ?r_work t_work f_work.
       bvi_evaluate ([bvi_Call ts (SOME loc_opt) xs NONE],env2,s2) = (r_work,t_work) /\
       opt_res_rel f_work r r_work /\
       bvi_tmcProof_state_rel f_work t t_work /\ f SUBMAP f_work /\
       only_fresh f f_work (bvi_state_refs s2) /\
       holes_unchanged_except f (bvi_state_refs s2) (bvi_state_refs t_work) {hp} /\
       holes_still_not_finalised f (bvi_state_refs s2) (bvi_state_refs t_work) /\
       !res_v. r = Rval [res_v] ==>
         ?res_v'.
           mb_rel f_work (bvi_state_refs s2) (bvi_state_refs t_work \\ hp) res_v res_v' /\
           ?tag' left' right'.
             FLOOKUP (bvi_state_refs t_work) hp =
               SOME (MutBlock tag' F left' res_v' right') /\
             LENGTH left' = LENGTH left`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[optimised_code_def] o
              check (BVITMCAUX_head_is "optimised_code")) THEN
  ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `arity':num` (X_CHOOSE_THEN `body:bvi_exp`
    (X_CHOOSE_THEN `body_wrap:bvi_exp` (X_CHOOSE_THEN `body_work:bvi_exp`
      STRIP_ASSUME_TAC)))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    (rhs(concl th) = `arity':num` || rhs(concl th) = `body:bvi_exp`)))) THEN
  SUBGOAL_THEN `LENGTH (vs':bvl_v list) = arity` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP LIST_REL_LENGTH o check (BVITMCAUX_head_is "ALL2")) THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[BVITMCAUX_evaluate_Call_NONE] THEN
  ASM_REWRITE_TAC[BVITMCAUX_find_code_SOME] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ARITH_RULE `a + SUC (SUC 0) = a + 2`] THEN
  CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bvi_state_clock (s2:(C,FFI)bvi_state) =
                bvi_state_clock (s:(num#C,FFI)bvi_state)` SUBST1_TAC THENL
   [ASM_MESON_TAC[bvi_tmcProof_state_rel_def]; ALL_TAC] THEN
  UNDISCH_TAC `(if bvi_state_clock (s:(num#C,FFI)bvi_state) < ts + 1
      then (Rerr (Rabort Rtimeout_error),bvi_state_clock_fupd (K 0) s)
      else BVITMCAUX_call_post (bvi_evaluate ([exp],vs,bvi_dec_clock (ts + 1) s))) =
       (r,t)` THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`Rerr (Rabort Rtimeout_error):(bvl_v list,exn_or_ret)result`;
      `bvi_state_clock_fupd (K 0) (s2:(C,FFI)bvi_state)`; `f:(num,num)fmap`] THEN
    ASM_SIMP_TAC[bvi_tmcProof_state_rel_with_clock; SUBMAP_REFL; only_fresh_refl;
      holes_unchanged_except_refl; holes_still_not_finalised_refl;
      bvi_state_INFO.ri_accfupds; BVITMCAUX_opt_res_rel_thm; exc_rel_def;
      distinctness "result"] THEN
    MAP_EVERY EXISTS_TAC [`Rabort Rtimeout_error:(exn_or_ret)error_result`;
                          `Rabort Rtimeout_error:(exn_or_ret)error_result`] THEN
    REWRITE_TAC[exc_rel_def];
    ALL_TAC] THEN
  MP_TAC(ISPEC `bvi_evaluate ([exp],vs,bvi_dec_clock (ts + 1) (s:(num#C,FFI)bvi_state))`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `t1:(num#C,FFI)bvi_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `?vs. r1 = Rerr (Rraise (Ret vs)):(bvl_v list,exn_or_ret)result` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `vr:bvl_v list` SUBST_ALL_TAC) THEN
    REWRITE_TAC[BVITMCAUX_call_post_Ret; PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[BVITMCAUX_call_post_id] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  ABBREV_TAC `env2' = APPEND (vs':bvl_v list) [bvl_RefPtr F hp; bvl_Number (&(LENGTH (left:bvl_v list)))]` THEN
  SUBGOAL_THEN `EL arity env2' = bvl_RefPtr F hp /\
                EL (arity + 1) env2' = bvl_Number (&(LENGTH (left:bvl_v list))) /\
                LENGTH env2' = arity + 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "env2'" THEN
    ASM_REWRITE_TAC[EL_APPEND_EQN; LT_REFL; ARITH_RULE `~(n + 1 < n)`; SUB_REFL;
                    ARITH_RULE `(n + 1) - n = 1`; LENGTH_APPEND] THEN
    REWRITE_TAC[EL; HD; TL; ONE; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`[exp:bvi_exp]`;
    `bvi_dec_clock (ts + 1) (s:(num#C,FFI)bvi_state)`] o
    check (fun th -> try fst(dest_const(fst(strip_comb(snd(strip_forall(concl th)))))) =
                         "hypothesis" with Failure _ -> false)) THEN
  REWRITE_TAC[hypothesis_def; BVITMCAUX_dec_clock_simps] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`vs:bvl_v list`;
    `r:(bvl_v list,exn_or_ret)result`; `t:(num#C,FFI)bvi_state`; `T`;
    `f:(num,num)fmap`; `bvi_dec_clock (ts + 1) (s2:(C,FFI)bvi_state)`;
    `env2':bvl_v list`; `loc:num`]) THEN
  ASM_REWRITE_TAC[ALL; LENGTH; BVITMCAUX_dec_clock_simps; HD;
                  ARITH_RULE `SUC 0 = 1`] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[BVITMCAUX_state_rel_dec_clock] THEN
    EXPAND_TAC "env2'" THEN REWRITE_TAC[bvi_tmcProof_env_rel_def] THEN
    MAP_EVERY EXISTS_TAC [`vs':bvl_v list`;
      `[bvl_RefPtr F hp; bvl_Number (&(LENGTH (left:bvl_v list)))]`] THEN
    ASM_REWRITE_TAC[LENGTH; EL; HD; TL; ONE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXISTS_TAC [`hp:num`; `&(LENGTH (left:bvl_v list)):int`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)bvi_state` (X_CHOOSE_THEN `f3:(num,num)fmap`
    (X_CHOOSE_THEN `r3:(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `loc_opt:num` o
    check (fun th -> try fst(dest_var(fst(dest_forall(concl th)))) = "loc_opt"
                     with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `hp:num` o CONJUNCT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[hole_not_finalised_def; hole_has_val_def] THEN CONJ_TAC THENL
     [EXISTS_TAC `c:bvl_v` THEN
      MAP_EVERY EXISTS_TAC [`hp:num`; `tag:num`; `F`; `left:bvl_v list`;
                            `right:bvl_v list`] THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rw:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `fw:(num,num)fmap` (X_CHOOSE_THEN `tw:(C,FFI)bvi_state`
      STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(?vs. rw = Rerr (Rraise (Ret vs)):(bvl_v list,exn_or_ret)result)`
    ASSUME_TAC THENL [ASM_MESON_TAC[BVITMCAUX_opt_res_rel_Ret]; ALL_TAC] THEN
  ASM_SIMP_TAC[BVITMCAUX_call_post_id] THEN
  MAP_EVERY EXISTS_TAC [`rw:(bvl_v list,exn_or_ret)result`; `tw:(C,FFI)bvi_state`;
                        `fw:(num,num)fmap`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `res_v:bvl_v` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `res_v:bvl_v` o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "res_v" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `res_v':bvl_v` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `res_v':bvl_v` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[hole_has_val_def] o
                check (BVITMCAUX_head_is "hole_has_val")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `hp2:num`
    (X_CHOOSE_THEN `tag2:num` (X_CHOOSE_THEN `fin2:bool`
      (X_CHOOSE_THEN `left2:bvl_v list` (X_CHOOSE_THEN `right2:bvl_v list`
        STRIP_ASSUME_TAC)))))) THEN
  UNDISCH_TAC `EL (LENGTH (vs:bvl_v list)) env2' = bvl_RefPtr F hp2` THEN
  ASM_REWRITE_TAC[injectivity "bvl_v"] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `EL (LENGTH (vs:bvl_v list) + 1) env2' =
               bvl_Number (&(LENGTH (left2:bvl_v list)))` THEN
  ASM_REWRITE_TAC[injectivity "bvl_v"; INT_OF_NUM_EQ] THEN DISCH_TAC THEN
  SUBGOAL_THEN `hole_not_finalised (bvi_state_refs (tw:(C,FFI)bvi_state)) hp` MP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[holes_still_not_finalised_def] o
      check (fun th -> BVITMCAUX_head_is "holes_still_not_finalised" th &&
                       free_in `tw:(C,FFI)bvi_state` (concl th))) THEN
    ASM_REWRITE_TAC[hole_not_finalised_def] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[hole_not_finalised_def] THEN ASM_REWRITE_TAC[option_INJ] THEN
  REWRITE_TAC[injectivity "bvl_ref"] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`tag2:num`; `left2:bvl_v list`; `right2:bvl_v list`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let BVITMCAUX_rcall_source = prove
 (`!ts args loc env (s:(num#C,FFI)bvi_state) r t.
     bvi_evaluate ([cb_to_bvi loc (RCall ts args)],env,s) = (r,t) /\
     wf_vars (LENGTH env) args /\ ~(r = Rerr (Rabort Rtype_error)) ==>
     ?arity exp.
       lookup loc (bvi_state_code s) = SOME (arity,exp) /\
       LENGTH (MAP (\n. EL n env) args) = arity /\
       (if bvi_state_clock s < ts + 1
        then (Rerr (Rabort Rtimeout_error),bvi_state_clock_fupd (K 0) s)
        else BVITMCAUX_call_post
               (bvi_evaluate ([exp],MAP (\n. EL n env) args,bvi_dec_clock (ts + 1) s))) =
       (r,t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cb_to_bvi_def; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `bvi_evaluate (MAP (\n. bvi_Var n) args,env,s:(num#C,FFI)bvi_state) =
                (Rval (MAP (\n. EL n env) args),s)` ASSUME_TAC THENL
   [MATCH_MP_TAC evaluate_vars_source THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    free_in `r:(bvl_v list,exn_or_ret)result` (concl th) && is_eq (concl th))) THEN
  ASM_REWRITE_TAC[BVITMCAUX_evaluate_Call_NONE; BVITMCAUX_find_code_SOME] THEN
  CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `lookup loc (bvi_state_code (s:(num#C,FFI)bvi_state))` option_nchotomy) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `ae:num#bvi_exp`
    (fun th -> ASSUME_TAC th THEN SUBST1_TAC th))) THEN
  CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `ae:num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `exp:bvi_exp` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `LENGTH (MAP (\n. EL n (env:bvl_v list)) args) = arity` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`arity:num`; `exp:bvi_exp`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]]);;

let BVITMCAUX_eval_Var_Const = prove
 (`!p i env (s:(C,FFI)bvi_state).
     p < LENGTH env /\ small_enough_int i ==>
     bvi_evaluate ([bvi_Var p; bvi_Op (IntOp (clos_Const i)) []],env,s) =
     (Rval [EL p env; bvl_Number i],s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV BVITMCAUX_DOAPP_CONV) THEN
  ASM_REWRITE_TAC[REVERSE; NULL] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD]);;

let BVITMCAUX_eval_Var_Var = prove
 (`!p q env (s:(C,FFI)bvi_state).
     p < LENGTH env /\ q < LENGTH env ==>
     bvi_evaluate ([bvi_Var p; bvi_Var q],env,s) = (Rval [EL p env; EL q env],s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD]);;

let BVITMCAUX_cb_rcall_aux = prove
 (`!ts args loc f opt env env2 (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) t r
    clock loc_opt refs extras ptr idx hole_ptr.
     bvi_evaluate ([cb_to_bvi loc (RCall ts args)],env,s) = (r,t) /\
     wf_cb (LENGTH env) (RCall ts args) /\
     bvi_tmcProof_env_rel opt f env env2 /\
     bvi_tmcProof_state_rel f s s' /\
     bvi_state_clock s <= clock /\
     ~(r = Rerr (Rabort Rtype_error)) /\
     (!xs' (s'':(num#C,FFI)bvi_state). hypothesis xs' s'' clock) /\
     optimised_code loc loc_opt (bvi_state_code s) (bvi_state_code s') /\
     state_ref_rel f (bvi_state_refs s) refs /\
     (?c. alloc_hole_has_val f refs extras ptr idx c) /\
     FDOM (bvi_state_refs s') SUBSET FDOM refs /\
     EL ptr extras = bvl_RefPtr F hole_ptr ==>
     ?r_aux t_aux f_aux.
       bvi_evaluate ([cb_to_bvi_worker_aux (shift_cb (LENGTH extras) (RCall ts args))
                        loc_opt ptr idx],
                     APPEND extras env2,bvi_state_refs_fupd (K refs) s') =
         (r_aux,t_aux) /\
       opt_res_rel f_aux r r_aux /\
       bvi_tmcProof_state_rel f_aux t t_aux /\
       f SUBMAP f_aux /\
       only_fresh f f_aux refs /\
       holes_unchanged_except f refs (bvi_state_refs t_aux) {hole_ptr} /\
       holes_still_not_finalised f refs (bvi_state_refs t_aux) /\
       !res_v. r = Rval [res_v] ==>
         ?res_v'.
           mb_rel f_aux (bvi_state_refs s') (bvi_state_refs t_aux \\ hole_ptr)
             res_v res_v' /\
           alloc_hole_has_val f (bvi_state_refs t_aux) extras ptr idx res_v'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wf_cb_def] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ts:num`; `args:num list`; `loc:num`; `env:bvl_v list`;
    `s:(num#C,FFI)bvi_state`; `r:(bvl_v list,exn_or_ret)result`;
    `t:(num#C,FFI)bvi_state`] BVITMCAUX_rcall_source) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `exp:bvi_exp`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`loc:num`; `arity:num`; `exp:bvi_exp`;
    `bvi_state_code (s:(num#C,FFI)bvi_state)`; `bvi_state_code (s':(C,FFI)bvi_state)`]
    code_rel_cases) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[bvi_tmcProof_state_rel_def]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  FIRST_X_ASSUM(MP_TAC o check (BVITMCAUX_head_is "alloc_hole_has_val")) THEN
  REWRITE_TAC[alloc_hole_has_val_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `hp:num` (X_CHOOSE_THEN `tag:num`
    (X_CHOOSE_THEN `left:bvl_v list` (X_CHOOSE_THEN `right:bvl_v list`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `hp:num = hole_ptr` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `EL ptr extras = bvl_RefPtr F hp` THEN
    ASM_REWRITE_TAC[injectivity "bvl_v"] THEN MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
                                                 lhs (concl th) = `idx:num`)) THEN
  REWRITE_TAC[shift_cb_def; cb_to_bvi_worker_aux_def; optimise_call_def; LET_DEF;
              LET_END_DEF] THEN
  MP_TAC(SPECL [`ts:num`; `loc:num`; `loc_opt:num`; `f:(num,num)fmap`;
    `s:(num#C,FFI)bvi_state`; `bvi_state_refs_fupd (K refs) (s':(C,FFI)bvi_state)`;
    `t:(num#C,FFI)bvi_state`; `r:(bvl_v list,exn_or_ret)result`; `clock:num`;
    `MAP (\n. EL n env) args:bvl_v list`; `MAP (\n. EL n env2) args:bvl_v list`;
    `exp:bvi_exp`; `arity:num`; `hole_ptr:num`; `tag:num`; `left:bvl_v list`;
    `c:bvl_v`; `right:bvl_v list`;
    `APPEND (MAP (\n. bvi_Var n) (shift_vars (LENGTH (extras:bvl_v list)) args))
       [bvi_Var ptr; bvi_Op (IntOp (clos_Const (&(LENGTH (left:bvl_v list))))) []]`;
    `APPEND (extras:bvl_v list) env2`] BVITMCAUX_rcall_work_core) THEN
  REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`f:(num,num)fmap`; `f:(num,num)fmap`; `s:(num#C,FFI)bvi_state`;
        `s':(C,FFI)bvi_state`; `bvi_state_refs (s:(num#C,FFI)bvi_state)`;
        `refs:(num,(bvl_v)bvl_ref)fmap`] BVITMCAUX_state_rel_refs) THEN
      ASM_REWRITE_TAC[SUBMAP_REFL; BVITMCAUX_refs_fupd_id] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[bvi_tmcProof_state_rel_def];
      MATCH_MP_TAC wf_vars_list_rel THEN ASM_MESON_TAC[];
      REWRITE_TAC[bvi_evaluate_APPEND; evaluate_shift_vars] THEN
      SUBGOAL_THEN `bvi_evaluate (MAP (\n. bvi_Var n) args,env2,
                      bvi_state_refs_fupd (K refs) (s':(C,FFI)bvi_state)) =
                    (Rval (MAP (\n. EL n env2) args),bvi_state_refs_fupd (K refs) s')`
        SUBST1_TAC THENL
       [MATCH_MP_TAC evaluate_vars_target THEN EXISTS_TAC `LENGTH (env:bvl_v list)` THEN
        ASM_MESON_TAC[bvi_tmcProof_env_rel_length]; ALL_TAC] THEN
      CASE_REWRITE_TAC[] THEN
      SUBGOAL_THEN `ptr < LENGTH (APPEND (extras:bvl_v list) env2)` ASSUME_TAC THENL
       [REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[BVITMCAUX_eval_Var_Const] THEN CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[EL_APPEND_EQN]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rw:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `tw:(C,FFI)bvi_state` (X_CHOOSE_THEN `fw:(num,num)fmap`
      STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`rw:(bvl_v list,exn_or_ret)result`; `tw:(C,FFI)bvi_state`;
                        `fw:(num,num)fmap`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `res_v:bvl_v` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `res_v:bvl_v` o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "res_v" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `res_v':bvl_v` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `tag':num` (X_CHOOSE_THEN `left':bvl_v list`
      (X_CHOOSE_THEN `right':bvl_v list` STRIP_ASSUME_TAC))))) THEN
  EXISTS_TAC `res_v':bvl_v` THEN CONJ_TAC THENL
   [MATCH_MP_TAC mb_rel_refs_old_subset THEN EXISTS_TAC `refs:(num,(bvl_v)bvl_ref)fmap` THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`hole_ptr:num`; `tag':num`; `left':bvl_v list`;
                          `right':bvl_v list`] THEN
    ASM_REWRITE_TAC[]]);;

let BVITMCAUX_cb_rcall_worker = prove
 (`!ts args loc f env env2 (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) t r clock
    loc_opt ptr idx (work:bvi_exp) hole_ptr.
     bvi_evaluate ([cb_to_bvi loc (RCall ts args)],env,s) = (r,t) /\
     wf_cb (LENGTH env) (RCall ts args) /\
     bvi_tmcProof_env_rel T f env env2 /\
     bvi_tmcProof_state_rel f s s' /\
     bvi_state_clock s <= clock /\
     ~(r = Rerr (Rabort Rtype_error)) /\
     (!xs' (s'':(num#C,FFI)bvi_state). hypothesis xs' s'' clock) /\
     optimised_code loc loc_opt (bvi_state_code s) (bvi_state_code s') /\
     ptr = LENGTH env /\ idx = LENGTH env + 1 /\
     (?c. hole_has_val f env env2 (bvi_state_refs s') c) /\
     hole_not_finalised (bvi_state_refs s') hole_ptr /\
     EL ptr env2 = bvl_RefPtr F hole_ptr ==>
     ?r_work f_work t_work.
       bvi_evaluate ([cb_to_bvi_worker (RCall ts args) loc_opt ptr idx],env2,s') =
         (r_work,t_work) /\
       opt_res_rel f_work r r_work /\
       bvi_tmcProof_state_rel f_work t t_work /\
       f SUBMAP f_work /\
       only_fresh f f_work (bvi_state_refs s') /\
       holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t_work) {hole_ptr} /\
       holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t_work) /\
       !res_v. r = Rval [res_v] ==>
         ?res_v'.
           mb_rel f_work (bvi_state_refs s') (bvi_state_refs t_work \\ hole_ptr)
             res_v res_v' /\
           hole_has_val f env env2 (bvi_state_refs t_work) res_v'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wf_cb_def] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ts:num`; `args:num list`; `loc:num`; `env:bvl_v list`;
    `s:(num#C,FFI)bvi_state`; `r:(bvl_v list,exn_or_ret)result`;
    `t:(num#C,FFI)bvi_state`] BVITMCAUX_rcall_source) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `exp:bvi_exp`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`loc:num`; `arity:num`; `exp:bvi_exp`;
    `bvi_state_code (s:(num#C,FFI)bvi_state)`; `bvi_state_code (s':(C,FFI)bvi_state)`]
    code_rel_cases) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[bvi_tmcProof_state_rel_def]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  FIRST_X_ASSUM(MP_TAC o check (BVITMCAUX_head_is "hole_has_val")) THEN
  REWRITE_TAC[hole_has_val_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `hp:num`
    (X_CHOOSE_THEN `tag:num` (X_CHOOSE_THEN `fin:bool`
      (X_CHOOSE_THEN `left:bvl_v list` (X_CHOOSE_THEN `right:bvl_v list`
        STRIP_ASSUME_TAC)))))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    (lhs (concl th) = `ptr:num` || lhs (concl th) = `idx:num`)))) THEN
  SUBGOAL_THEN `hp:num = hole_ptr` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `EL (LENGTH (env:bvl_v list)) env2 = bvl_RefPtr F hp` THEN
    ASM_REWRITE_TAC[injectivity "bvl_v"] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `fin = F` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `hole_not_finalised (bvi_state_refs (s':(C,FFI)bvi_state)) hole_ptr` THEN
    ASM_REWRITE_TAC[hole_not_finalised_def; option_INJ; injectivity "bvl_ref"] THEN
    MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[cb_to_bvi_worker_def; optimise_call_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(SPECL [`ts:num`; `loc:num`; `loc_opt:num`; `f:(num,num)fmap`;
    `s:(num#C,FFI)bvi_state`; `s':(C,FFI)bvi_state`;
    `t:(num#C,FFI)bvi_state`; `r:(bvl_v list,exn_or_ret)result`; `clock:num`;
    `MAP (\n. EL n env) args:bvl_v list`; `MAP (\n. EL n env2) args:bvl_v list`;
    `exp:bvi_exp`; `arity:num`; `hole_ptr:num`; `tag:num`; `left:bvl_v list`;
    `c:bvl_v`; `right:bvl_v list`;
    `APPEND (MAP (\n. bvi_Var n) args)
       [bvi_Var (LENGTH (env:bvl_v list)); bvi_Var (LENGTH env + 1)]`;
    `env2:bvl_v list`] BVITMCAUX_rcall_work_core) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC wf_vars_list_rel THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[bvi_evaluate_APPEND] THEN
    SUBGOAL_THEN `bvi_evaluate (MAP (\n. bvi_Var n) args,env2,(s':(C,FFI)bvi_state)) =
                  (Rval (MAP (\n. EL n env2) args),s')` SUBST1_TAC THENL
     [MATCH_MP_TAC evaluate_vars_target THEN EXISTS_TAC `LENGTH (env:bvl_v list)` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    CASE_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[BVITMCAUX_eval_Var_Var; ARITH_RULE `n < n + 2 /\ n + 1 < n + 2`] THEN
    CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rw:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `tw:(C,FFI)bvi_state` (X_CHOOSE_THEN `fw:(num,num)fmap`
      STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`rw:(bvl_v list,exn_or_ret)result`; `fw:(num,num)fmap`;
                        `tw:(C,FFI)bvi_state`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `res_v:bvl_v` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `res_v:bvl_v` o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "res_v" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `res_v':bvl_v` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `tag':num` (X_CHOOSE_THEN `left':bvl_v list`
      (X_CHOOSE_THEN `right':bvl_v list` STRIP_ASSUME_TAC))))) THEN
  EXISTS_TAC `res_v':bvl_v` THEN ASM_REWRITE_TAC[hole_has_val_def] THEN
  MAP_EVERY EXISTS_TAC [`hole_ptr:num`; `tag':num`; `F`; `left':bvl_v list`;
                        `right':bvl_v list`] THEN
  ASM_REWRITE_TAC[]);;

let BVITMCAUX_DROP_SUC_APPEND = prove
 (`!(l1:A list) h t. DROP (LENGTH l1 + 1) (APPEND l1 (CONS h t)) = t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; APPEND; ADD_CLAUSES; DROP_DEF] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DROP_0; NOT_SUC; SUC_SUB1] THEN
  ASM_REWRITE_TAC[GSYM ADD1]);;

let BVITMCAUX_eval_Const = prove
 (`!i env (s:(C,FFI)bvi_state).
     small_enough_int i ==>
     bvi_evaluate ([bvi_Op (IntOp (clos_Const i)) []],env,s) = (Rval [bvl_Number i],s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvi_evaluate_def] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BVITMCAUX_DOAPP_CONV) THEN
  ASM_REWRITE_TAC[REVERSE; NULL] THEN CASE_REWRITE_TAC[]);;

let BVITMCAUX_eval_mut_cons = prove
 (`!tag left right env (s:(C,FFI)bvi_state) n.
     wf_vars n left /\ wf_vars n right /\ LENGTH env >= n ==>
     bvi_evaluate ([mut_cons tag left right],env,s) =
     (Rval [bvl_RefPtr F (minimal ptr. ~(ptr IN FDOM (bvi_state_refs s)))],
      bvi_state_refs_fupd (K (bvi_state_refs s |+
        ((minimal ptr. ~(ptr IN FDOM (bvi_state_refs s))),
         MutBlock tag F (REVERSE (MAP (\n. EL n env) right)) (bvl_Number (&0))
           (REVERSE (MAP (\n. EL n env) left))))) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mut_cons_def; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN
   `bvi_evaluate (APPEND (APPEND (MAP (\n. bvi_Var n) left)
                                 [bvi_Op (IntOp (clos_Const (&0))) []])
                         (MAP (\n. bvi_Var n) right),env,s:(C,FFI)bvi_state) =
    (Rval (APPEND (APPEND (MAP (\n. EL n env) left) [bvl_Number (&0)])
                  (MAP (\n. EL n env) right)),s)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `bvi_evaluate (MAP (\n. bvi_Var n) left,env,s:(C,FFI)bvi_state) =
        (Rval (MAP (\n. EL n env) left),s) /\
      bvi_evaluate (MAP (\n. bvi_Var n) right,env,s) =
        (Rval (MAP (\n. EL n env) right),s)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC evaluate_vars_target THEN
      EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `bvi_evaluate ([bvi_Op (IntOp (clos_Const (&0))) []],env,
                                s:(C,FFI)bvi_state) = (Rval [bvl_Number (&0)],s)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC BVITMCAUX_eval_Const THEN REWRITE_TAC[small_enough_int_def] THEN
      CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[bvi_evaluate_APPEND] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BVITMCAUX_DOAPP_CONV) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[REVERSE_APPEND; REVERSE; APPEND; LENGTH_APPEND; LENGTH_REVERSE; LENGTH;
              LENGTH_MAP] THEN
  REWRITE_TAC[ARITH_RULE `~(b >= (a + SUC 0) + b)`] THEN
  SUBGOAL_THEN
   `!X. TAKE (LENGTH (right:num list)) (APPEND (REVERSE (MAP (\n. EL n env) right)) X) =
        REVERSE (MAP (\n. EL n (env:bvl_v list)) right) /\
        EL (LENGTH right) (APPEND (REVERSE (MAP (\n. EL n env) right))
                            (CONS (bvl_Number (&0)) X)) = bvl_Number (&0) /\
        DROP (LENGTH right + 1) (APPEND (REVERSE (MAP (\n. EL n env) right))
                                  (CONS (bvl_Number (&0)) X)) = X`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `LENGTH (right:num list) =
                  LENGTH (REVERSE (MAP (\n. EL n (env:bvl_v list)) right))`
      SUBST1_TAC THENL [REWRITE_TAC[LENGTH_REVERSE; LENGTH_MAP]; ALL_TAC] THEN
    REWRITE_TAC[TAKE_LENGTH_APPEND; BVITMCAUX_DROP_SUC_APPEND] THEN
    SIMP_TAC[EL_LENGTH_APPEND; NULL; HD];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[]);;

let BVITMCAUX_eval_update_cons = prove
 (`!e_ptr e_idx e_val env (s:(C,FFI)bvi_state) x i hp tag l c r.
     bvi_evaluate ([e_val; e_idx; e_ptr],env,s) =
       (Rval [x; bvl_Number i; bvl_RefPtr F hp],s) /\
     FLOOKUP (bvi_state_refs s) hp = SOME (MutBlock tag F l c r) /\
     i = &(LENGTH l) ==>
     bvi_evaluate ([update_cons e_ptr e_idx e_val],env,s) =
     (Rval [bvl_Unit],
      bvi_state_refs_fupd (K (bvi_state_refs s |+ (hp,MutBlock tag F l x r))) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[update_cons_def] THEN
  GEN_REWRITE_TAC LAND_CONV [bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[REVERSE; APPEND] THEN
  CONV_TAC(ONCE_DEPTH_CONV BVITMCAUX_DOAPP_CONV) THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[]);;

let BVITMCAUX_cb_hyps_def = cake_def
 `BVITMCAUX_cb_hyps cb loc f opt env env2 (s:(num#C,FFI)bvi_state)
                    (s':(C,FFI)bvi_state) t r clock <=>
    bvi_evaluate ([cb_to_bvi loc cb],env,s) = (r,t) /\
    wf_cb (LENGTH env) cb /\
    bvi_tmcProof_env_rel opt f env env2 /\
    bvi_tmcProof_state_rel f s s' /\
    bvi_state_clock s <= clock /\
    ~(r = Rerr (Rabort Rtype_error)) /\
    (!xs' (s'':(num#C,FFI)bvi_state). hypothesis xs' s'' clock)`;;

let BVITMCAUX_cb_main_def = cake_def
 `BVITMCAUX_cb_main cb loc f env2 (s':(C,FFI)bvi_state) (t:(num#C,FFI)bvi_state) r <=>
    ?r' t' f'.
      bvi_evaluate ([cb_to_bvi loc cb],env2,s') = (r',t') /\
      result_rel (ALL2 (bvi_tmcProof_v_rel f')) (eor_rel f') r r' /\
      bvi_tmcProof_state_rel f' t t' /\ f SUBMAP f' /\
      only_fresh f f' (bvi_state_refs s') /\
      holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t') {} /\
      holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t')`;;

let BVITMCAUX_cb_aux_def = cake_def
 `BVITMCAUX_cb_aux cb loc_opt f (s:(num#C,FFI)bvi_state) env2 (s':(C,FFI)bvi_state)
                   (t:(num#C,FFI)bvi_state) r <=>
    !refs extras ptr idx hole_ptr.
      state_ref_rel f (bvi_state_refs s) refs /\
      (?c. alloc_hole_has_val f refs extras ptr idx c) /\
      FDOM (bvi_state_refs s') SUBSET FDOM refs /\
      EL ptr extras = bvl_RefPtr F hole_ptr ==>
      ?r_aux t_aux f_aux.
        bvi_evaluate ([cb_to_bvi_worker_aux (shift_cb (LENGTH extras) cb) loc_opt ptr idx],
                      APPEND extras env2,bvi_state_refs_fupd (K refs) s') =
          (r_aux,t_aux) /\
        opt_res_rel f_aux r r_aux /\
        bvi_tmcProof_state_rel f_aux t t_aux /\
        f SUBMAP f_aux /\
        only_fresh f f_aux refs /\
        holes_unchanged_except f refs (bvi_state_refs t_aux) {hole_ptr} /\
        holes_still_not_finalised f refs (bvi_state_refs t_aux) /\
        !res_v. r = Rval [res_v] ==>
          ?res_v'.
            mb_rel f_aux (bvi_state_refs s') (bvi_state_refs t_aux \\ hole_ptr)
              res_v res_v' /\
            alloc_hole_has_val f (bvi_state_refs t_aux) extras ptr idx res_v'`;;

let BVITMCAUX_cb_cb_source = prove
 (`!tag left child right loc env (s:(num#C,FFI)bvi_state) r t.
     bvi_evaluate ([cb_to_bvi loc (CallBlock tag left child right)],env,s) = (r,t) /\
     wf_cb (LENGTH env) (CallBlock tag left child right) ==>
     ?rc sc.
       bvi_evaluate ([cb_to_bvi loc child],env,s) = (rc,sc) /\
       ((?c. rc = Rval [c] /\
             r = Rval [bvl_Block tag (REVERSE (APPEND (APPEND (MAP (\n. EL n env) left)
                                       [c]) (MAP (\n. EL n env) right)))] /\
             t = sc) \/
        (?e. rc = Rerr e /\ r = Rerr e /\ t = sc))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wf_cb_def] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `bvi_evaluate ([cb_to_bvi loc child],env,s:(num#C,FFI)bvi_state)`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `rc:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `sc:(num#C,FFI)bvi_state` ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`rc:(bvl_v list,exn_or_ret)result`;
                        `sc:(num#C,FFI)bvi_state`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!vs st. wf_vars (LENGTH env) vs ==>
      bvi_evaluate (MAP (\n. bvi_Var n) vs,env,st:(num#C,FFI)bvi_state) =
      (Rval (MAP (\n. EL n env) vs),st)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC evaluate_vars_source THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    free_in `r:(bvl_v list,exn_or_ret)result` (concl th) && is_eq (concl th))) THEN
  REWRITE_TAC[cb_to_bvi_def; LET_DEF; LET_END_DEF; BVITMCAUX_evaluate_Cons;
              bvi_evaluate_APPEND] THEN
  ASM_SIMP_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  DISJ_CASES_THEN2
    (X_CHOOSE_THEN `vs:bvl_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)
    (ISPEC `rc:(bvl_v list,exn_or_ret)result` (cases "result")) THEN
  CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"] THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP evaluate_SING_IMP) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN MESON_TAC[];
    MESON_TAC[]]);;

let BVITMCAUX_cb_cb_main = prove
 (`!tag left child right.
     (!loc f opt env env2 (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) t r clock.
        BVITMCAUX_cb_hyps child loc f opt env env2 s s' t r clock ==>
        BVITMCAUX_cb_main child loc f env2 s' t r) ==>
     !loc f opt env env2 (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) t r clock.
        BVITMCAUX_cb_hyps (CallBlock tag left child right) loc f opt env env2 s s' t r
          clock ==>
        BVITMCAUX_cb_main (CallBlock tag left child right) loc f env2 s' t r`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[BVITMCAUX_cb_hyps_def] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tag:num`; `left:num list`; `child:call_block`; `right:num list`;
    `loc:num`; `env:bvl_v list`; `s:(num#C,FFI)bvi_state`;
    `r:(bvl_v list,exn_or_ret)result`; `t:(num#C,FFI)bvi_state`]
    BVITMCAUX_cb_cb_source) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rc:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `sc:(num#C,FFI)bvi_state` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "res")))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wf_cb_def]) THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`loc:num`; `f:(num,num)fmap`; `opt:bool`;
    `env:bvl_v list`; `env2:bvl_v list`; `s:(num#C,FFI)bvi_state`;
    `s':(C,FFI)bvi_state`; `sc:(num#C,FFI)bvi_state`;
    `rc:(bvl_v list,exn_or_ret)result`; `clock:num`]) THEN
  REWRITE_TAC[BVITMCAUX_cb_hyps_def; BVITMCAUX_cb_main_def] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REMOVE_THEN "res" MP_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[distinctness "result"] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rc':(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `sc':(C,FFI)bvi_state` (X_CHOOSE_THEN `f':(num,num)fmap`
      STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!vs st. wf_vars (LENGTH (env:bvl_v list)) vs ==>
      bvi_evaluate (MAP (\n. bvi_Var n) vs,env2:bvl_v list,st:(C,FFI)bvi_state) =
      (Rval (MAP (\n. EL n env2) vs),st)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC evaluate_vars_target THEN
    EXISTS_TAC `LENGTH (env:bvl_v list)` THEN
    ASM_MESON_TAC[bvi_tmcProof_env_rel_length]; ALL_TAC] THEN
  REWRITE_TAC[cb_to_bvi_def; LET_DEF; LET_END_DEF; BVITMCAUX_evaluate_Cons;
              bvi_evaluate_APPEND] THEN
  ASM_SIMP_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REMOVE_THEN "res" (DISJ_CASES_THEN2
    (X_CHOOSE_THEN `c:bvl_v` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `e:(exn_or_ret)error_result` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[result_rel_Rval; result_rel_Rerr1; LIST_REL_CONS1;
                              LIST_REL_NIL]) THEN
  REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[MESON[] `!(a:A) (b:B) P. (?x y z:C. (a = x /\ b = y) /\ P x y z) <=>
                                       (?z. P a b z)`] THEN
  EXISTS_TAC `f':(num,num)fmap` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[result_rel_def; ALL2; BVITMCAUX_v_rel_simps; injectivity "bvl_v";
              UNWIND_THM1] THEN
  ONCE_REWRITE_TAC[GSYM list_rel_reverse] THEN
  REPEAT(MATCH_MP_TAC LIST_REL_APPEND_suff THEN CONJ_TAC) THEN
  ASM_REWRITE_TAC[ALL2] THEN MATCH_MP_TAC (GEN_ALL list_rel_submap) THEN
  EXISTS_TAC `f:(num,num)fmap` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC wf_vars_list_rel THEN ASM_MESON_TAC[]);;

let BVITMCAUX_MAP_EL_shift = prove
 (`!(extras:bvl_v list) env2 vs.
     MAP (\n. EL n (APPEND extras env2)) (shift_vars (LENGTH extras) vs) =
     MAP (\n. EL n env2) vs`,
  REWRITE_TAC[BVITMCAUX_shift_vars_MAP; GSYM MAP_o; o_DEF; EL_APPEND_EQN] THEN
  REWRITE_TAC[ARITH_RULE `~(n + l < l:num) /\ (n + l) - l = n`]);;

let BVITMCAUX_eval_upd_args = prove
 (`!e i p env (s:(C,FFI)bvi_state).
     p < LENGTH env /\ small_enough_int i ==>
     bvi_evaluate ([bvi_Var 0; bvi_Op (IntOp (clos_Const i)) []; bvi_Var (p + 1)],
                   CONS e env,s) =
     (Rval [e; bvl_Number i; EL p env],s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvi_evaluate_def] THEN
  ASM_REWRITE_TAC[LENGTH; LT_0; EL; HD; ARITH_RULE `p + 1 < SUC n <=> p < n`] THEN
  CASE_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BVITMCAUX_DOAPP_CONV) THEN
  ASM_REWRITE_TAC[REVERSE; NULL] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[HD; GSYM ADD1; EL; TL]);;

let BVITMCAUX_eval_upd_vars = prove
 (`!e q p env (s:(C,FFI)bvi_state).
     p < LENGTH env /\ q < LENGTH env ==>
     bvi_evaluate ([bvi_Var 0; bvi_Var (q + 1); bvi_Var (p + 1)],CONS e env,s) =
     (Rval [e; EL q env; EL p env],s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvi_evaluate_def] THEN
  ASM_REWRITE_TAC[LENGTH; LT_0; EL; HD; ARITH_RULE `p + 1 < SUC n <=> p < n`] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD; GSYM ADD1; EL; TL]);;

let BVITMCAUX_hue_at = prove
 (`!(f:(A,B)fmap) (refs:(B,(C)bvl_ref)fmap) refs' changed ptr tag fin l c r.
     holes_unchanged_except f refs refs' changed /\ ~(ptr IN FRANGE f) /\
     FLOOKUP refs ptr = SOME (MutBlock tag fin l c r) ==>
     ?fin' c'. FLOOKUP refs' ptr = SOME (MutBlock tag fin' l c' r) /\
               (~(ptr IN changed) ==> c = c')`,
  REWRITE_TAC[holes_unchanged_except_def] THEN MESON_TAC[]);;

let BVITMCAUX_hsnf_at = prove
 (`!(f:(A,B)fmap) (refs:(B,(C)bvl_ref)fmap) refs' ptr tag l c r.
     holes_still_not_finalised f refs refs' /\ ~(ptr IN FRANGE f) /\
     FLOOKUP refs ptr = SOME (MutBlock tag F l c r) ==>
     ?tag' l' c' r'. FLOOKUP refs' ptr = SOME (MutBlock tag' F l' c' r')`,
  REWRITE_TAC[holes_still_not_finalised_def; hole_not_finalised_def] THEN
  MESON_TAC[]);;

let BVITMCAUX_hole_after = prove
 (`!(f:(A,B)fmap) (refs:(B,(C)bvl_ref)fmap) refs' changed ptr tag l c r.
     holes_unchanged_except f refs refs' changed /\
     holes_still_not_finalised f refs refs' /\ ~(ptr IN FRANGE f) /\
     FLOOKUP refs ptr = SOME (MutBlock tag F l c r) ==>
     ?c'. FLOOKUP refs' ptr = SOME (MutBlock tag F l c' r) /\
          (~(ptr IN changed) ==> c = c')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:(A,B)fmap`; `refs:(B,(C)bvl_ref)fmap`; `refs':(B,(C)bvl_ref)fmap`;
    `changed:B->bool`; `ptr:B`; `tag:num`; `F`; `l:(C)list`; `c:C`; `r:(C)list`]
    BVITMCAUX_hue_at) THEN
  MP_TAC(ISPECL [`f:(A,B)fmap`; `refs:(B,(C)bvl_ref)fmap`; `refs':(B,(C)bvl_ref)fmap`;
    `ptr:B`; `tag:num`; `l:(C)list`; `c:C`; `r:(C)list`] BVITMCAUX_hsnf_at) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `FLOOKUP (refs':(B,(C)bvl_ref)fmap) ptr = SOME (MutBlock tag' F l' c' r')` THEN
  ASM_REWRITE_TAC[option_INJ; injectivity "bvl_ref"] THEN STRIP_TAC THEN
  RVEQ_TAC THEN ASM_MESON_TAC[]);;

let BVITMCAUX_refs_fupd_fupd = prove
 (`!a b (s:(A,B)bvi_state).
     bvi_state_refs_fupd (K a) (bvi_state_refs_fupd (K b) s) = bvi_state_refs_fupd (K a) s`,
  REWRITE_TAC[bvi_state_INFO.ri_fupdfupds] THEN
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; K_THM]);;

let BVITMCAUX_cb_cb_aux = prove
 (`!tag left child right.
     (!loc f opt env env2 (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) t r clock.
        BVITMCAUX_cb_hyps child loc f opt env env2 s s' t r clock ==>
        !loc_opt. optimised_code loc loc_opt (bvi_state_code s) (bvi_state_code s') ==>
                  BVITMCAUX_cb_aux child loc_opt f s env2 s' t r) ==>
     !loc f opt env env2 (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) t r clock loc_opt.
        BVITMCAUX_cb_hyps (CallBlock tag left child right) loc f opt env env2 s s' t r
          clock /\
        optimised_code loc loc_opt (bvi_state_code s) (bvi_state_code s') ==>
        BVITMCAUX_cb_aux (CallBlock tag left child right) loc_opt f s env2 s' t r`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> LABEL_TAC "hyps" th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[BVITMCAUX_cb_hyps_def] th)) ASSUME_TAC) THEN
  REWRITE_TAC[BVITMCAUX_cb_aux_def] THEN
  MAP_EVERY X_GEN_TAC [`refs:(num,(bvl_v)bvl_ref)fmap`; `extras:bvl_v list`;
    `ptr:num`; `idx:num`; `hole_ptr:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `c0:bvl_v` MP_TAC) STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[alloc_hole_has_val_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `hp:num` (X_CHOOSE_THEN `tag':num`
    (X_CHOOSE_THEN `left':bvl_v list` (X_CHOOSE_THEN `right':bvl_v list`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `hp:num = hole_ptr` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `EL ptr extras = bvl_RefPtr F hp` THEN
    ASM_REWRITE_TAC[injectivity "bvl_v"] THEN MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
                                                 lhs (concl th) = `idx:num`)) THEN
  MP_TAC(SPECL [`tag:num`; `left:num list`; `child:call_block`; `right:num list`;
    `loc:num`; `env:bvl_v list`; `s:(num#C,FFI)bvi_state`;
    `r:(bvl_v list,exn_or_ret)result`; `t:(num#C,FFI)bvi_state`]
    BVITMCAUX_cb_cb_source) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rc:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `sc:(num#C,FFI)bvi_state` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "res")))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wf_cb_def]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th ->
    is_conj (concl th) && BVITMCAUX_head_is "wf_vars" (CONJUNCT1 th))) THEN
  ABBREV_TAC `p2 = minimal ptr. ~(ptr IN FDOM (refs:(num,(bvl_v)bvl_ref)fmap))` THEN
  SUBGOAL_THEN `~(p2 IN FDOM (refs:(num,(bvl_v)bvl_ref)fmap))` ASSUME_TAC THENL
   [EXPAND_TAC "p2" THEN REWRITE_TAC[fresh_ptr_fresh]; ALL_TAC] THEN
  SUBGOAL_THEN `~(p2 IN FRANGE (f:(num,num)fmap))` ASSUME_TAC THENL
   [EXPAND_TAC "p2" THEN MATCH_MP_TAC fresh_not_in_range_f THEN
    EXISTS_TAC `bvi_state_refs (s:(num#C,FFI)bvi_state)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p2:num = hole_ptr)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(hole_ptr IN FDOM (refs:(num,(bvl_v)bvl_ref)fmap))` THEN
    ASM_REWRITE_TAC[FDOM_FLOOKUP; option_DISTINCT]; ALL_TAC] THEN
  REWRITE_TAC[shift_cb_def; LET_DEF; LET_END_DEF; cb_to_bvi_worker_aux_def;
              length_shift_vars] THEN
  ABBREV_TAC `refs3 = (refs:(num,(bvl_v)bvl_ref)fmap) |+
    (p2,MutBlock tag F (REVERSE (MAP (\n. EL n env2) right)) (bvl_Number (&0))
                       (REVERSE (MAP (\n. EL n env2) left))) |+
    (hole_ptr,MutBlock tag' F left' (bvl_RefPtr F p2) right')` THEN
  SUBGOAL_THEN
   `bvi_evaluate ([bvi_Let [mut_cons tag (shift_vars (LENGTH (extras:bvl_v list)) left)
                              (shift_vars (LENGTH extras) right)]
       (bvi_Let [update_cons (bvi_Var (ptr + 1))
                  (bvi_Op (IntOp (clos_Const (&(LENGTH (left':bvl_v list))))) [])
                  (bvi_Var 0)]
          (cb_to_bvi_worker_aux (shift_cb 2 (shift_cb (LENGTH extras) child)) loc_opt 1
             (LENGTH (right:num list))))],
      APPEND extras env2,bvi_state_refs_fupd (K refs) (s':(C,FFI)bvi_state)) =
    bvi_evaluate ([cb_to_bvi_worker_aux (shift_cb (2 + LENGTH extras) child) loc_opt 1
                    (LENGTH right)],
      CONS bvl_Unit (CONS (bvl_RefPtr F p2) (APPEND extras env2)),
      bvi_state_refs_fupd (K refs3) s')`
   SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
    MP_TAC(ISPECL [`tag:num`; `shift_vars (LENGTH (extras:bvl_v list)) left`;
      `shift_vars (LENGTH (extras:bvl_v list)) right`; `APPEND (extras:bvl_v list) env2`;
      `bvi_state_refs_fupd (K refs) (s':(C,FFI)bvi_state)`;
      `LENGTH (extras:bvl_v list) + LENGTH (env:bvl_v list)`] BVITMCAUX_eval_mut_cons) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[wf_vars_shift; LENGTH_APPEND] THEN
      MATCH_MP_TAC(ARITH_RULE `b <= c ==> a + c >= a + b`) THEN
      ASM_MESON_TAC[bvi_tmcProof_env_rel_length; GE]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM; BVITMCAUX_MAP_EL_shift] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[bvi_evaluate_def] THEN REWRITE_TAC[APPEND] THEN
    REWRITE_TAC[BVITMCAUX_refs_fupd_fupd] THEN
    MP_TAC(ISPECL [`bvi_Var (ptr + 1)`;
      `bvi_Op (IntOp (clos_Const (&(LENGTH (left':bvl_v list))))) []`; `bvi_Var 0`;
      `CONS (bvl_RefPtr F p2) (APPEND (extras:bvl_v list) env2)`;
      `bvi_state_refs_fupd (K ((refs:(num,(bvl_v)bvl_ref)fmap) |+
         (p2,MutBlock tag F (REVERSE (MAP (\n. EL n env2) right)) (bvl_Number (&0))
                            (REVERSE (MAP (\n. EL n env2) left))))) (s':(C,FFI)bvi_state)`;
      `bvl_RefPtr F p2`; `&(LENGTH (left':bvl_v list)):int`; `hole_ptr:num`;
      `tag':num`; `left':bvl_v list`; `c0:bvl_v`; `right':bvl_v list`]
      BVITMCAUX_eval_update_cons) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[] THEN CONJ_TAC THENL
       [W(fun (_,w) -> MP_TAC(PART_MATCH (lhs o rand) (SPEC_ALL BVITMCAUX_eval_upd_args)
          (lhs w))) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[EL_APPEND_EQN];
        REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE] THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[APPEND; shift_cb_dist; bvi_state_INFO.ri_accfupds; K_THM;
                BVITMCAUX_refs_fupd_fupd] THEN
    EXPAND_TAC "refs3" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`loc:num`; `f:(num,num)fmap`; `opt:bool`;
    `env:bvl_v list`; `env2:bvl_v list`; `s:(num#C,FFI)bvi_state`;
    `s':(C,FFI)bvi_state`; `sc:(num#C,FFI)bvi_state`;
    `rc:(bvl_v list,exn_or_ret)result`; `clock:num`]) THEN
  REWRITE_TAC[BVITMCAUX_cb_hyps_def] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [USE_THEN "res" MP_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[distinctness "result"] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `loc_opt:num`) THEN
  ASM_REWRITE_TAC[BVITMCAUX_cb_aux_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`refs3:(num,(bvl_v)bvl_ref)fmap`;
    `CONS bvl_Unit (CONS (bvl_RefPtr F p2) extras)`; `1`; `LENGTH (right:num list)`;
    `p2:num`]) THEN
  REWRITE_TAC[LENGTH; APPEND; ARITH_RULE `SUC (SUC n) = 2 + n`; EL; HD; TL; ONE] THEN
  REWRITE_TAC[GSYM ONE] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "refs3" THEN REPEAT(MATCH_MP_TAC state_ref_rel_filled THEN
                                     ASM_REWRITE_TAC[]);
      EXISTS_TAC `bvl_Number (&0)` THEN REWRITE_TAC[alloc_hole_has_val_def] THEN
      MAP_EVERY EXISTS_TAC [`p2:num`; `tag:num`;
        `REVERSE (MAP (\n. EL n (env2:bvl_v list)) right)`;
        `REVERSE (MAP (\n. EL n (env2:bvl_v list)) left)`] THEN
      EXPAND_TAC "refs3" THEN
      ASM_REWRITE_TAC[LENGTH; EL; HD; TL; ONE; LENGTH_REVERSE; LENGTH_MAP;
                      FLOOKUP_UPDATE] THEN
      ARITH_TAC;
      EXPAND_TAC "refs3" THEN REWRITE_TAC[FDOM_FUPDATE] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r_aux:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `t_aux:(C,FFI)bvi_state` (X_CHOOSE_THEN `f_aux:(num,num)fmap`
      STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`r_aux:(bvl_v list,exn_or_ret)result`;
    `t_aux:(C,FFI)bvi_state`; `f_aux:(num,num)fmap`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M2 = MutBlock tag F (REVERSE (MAP (\n. EL n (env2:bvl_v list)) right))
                     (bvl_Number (&0)) (REVERSE (MAP (\n. EL n env2) left))` THEN
  ABBREV_TAC `X2 = MutBlock tag' F left' (bvl_RefPtr F p2) right'` THEN
  SUBGOAL_THEN `refs3 = ((refs:(num,(bvl_v)bvl_ref)fmap) |+ (hole_ptr,X2)) |+ (p2,M2)`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `refs3:(num,(bvl_v)bvl_ref)fmap`)) THEN
    MATCH_MP_TAC flookup_com_neq THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `only_fresh f f_aux (refs:(num,(bvl_v)bvl_ref)fmap)` ASSUME_TAC THENL
   [MATCH_MP_TAC only_fresh_del THEN
    MAP_EVERY EXISTS_TAC [`hole_ptr:num`; `X2:(bvl_v)bvl_ref`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC only_fresh_del THEN
    MAP_EVERY EXISTS_TAC [`p2:num`; `M2:(bvl_v)bvl_ref`] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `holes_still_not_finalised (f:(num,num)fmap) (refs:(num,(bvl_v)bvl_ref)fmap)
                  (bvi_state_refs (t_aux:(C,FFI)bvi_state))` ASSUME_TAC THENL
   [MATCH_MP_TAC holes_still_not_finalised_del THEN
    MAP_EVERY EXISTS_TAC [`hole_ptr:num`; `tag':num`; `left':bvl_v list`;
                          `bvl_RefPtr F p2`; `right':bvl_v list`] THEN
    MATCH_MP_TAC holes_still_not_finalised_del THEN
    MAP_EVERY EXISTS_TAC [`p2:num`; `tag:num`;
      `REVERSE (MAP (\n. EL n (env2:bvl_v list)) right)`; `bvl_Number (&0)`;
      `REVERSE (MAP (\n. EL n (env2:bvl_v list)) left)`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `holes_unchanged_except (f:(num,num)fmap) (refs:(num,(bvl_v)bvl_ref)fmap)
                  (bvi_state_refs (t_aux:(C,FFI)bvi_state)) {hole_ptr}` ASSUME_TAC THENL
   [MP_TAC(INST [`F`,`fin':bool`; `c0:bvl_v`,`c':bvl_v`]
      (ISPECL [`f:(num,num)fmap`; `refs:(num,(bvl_v)bvl_ref)fmap`;
        `bvi_state_refs (t_aux:(C,FFI)bvi_state)`; `ARB:num`; `hole_ptr:num`;
        `tag':num`; `F`; `left':bvl_v list`; `bvl_RefPtr F p2`; `right':bvl_v list`]
        holes_unchanged_except_changed)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC holes_unchanged_except_del_SING THEN
    MAP_EVERY EXISTS_TAC [`p2:num`; `M2:(bvl_v)bvl_ref`] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[FDOM_FUPDATE; IN_INSERT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FLOOKUP (refs3:(num,(bvl_v)bvl_ref)fmap) hole_ptr = SOME (X2:(bvl_v)bvl_ref) /\
                FLOOKUP refs3 p2 = SOME (M2:(bvl_v)bvl_ref)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
        rhs (concl th) = `refs3:(num,(bvl_v)bvl_ref)fmap`)) THEN
      REWRITE_TAC[FLOOKUP_UPDATE];
      ASM_REWRITE_TAC[FLOOKUP_UPDATE]];
    ALL_TAC] THEN
  REMOVE_THEN "res" (DISJ_CASES_THEN2 (X_CHOOSE_THEN `c:bvl_v` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `e:(exn_or_ret)error_result` STRIP_ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    (lhs (concl th) = `rc:(bvl_v list,exn_or_ret)result` ||
     lhs (concl th) = `r:(bvl_v list,exn_or_ret)result` ||
     lhs (concl th) = `t:(num#C,FFI)bvi_state`)))) THEN
  ASM_REWRITE_TAC[distinctness "result"] THEN
  UNDISCH_TAC `opt_res_rel f_aux (Rval [c]) r_aux` THEN
  REWRITE_TAC[BVITMCAUX_opt_res_rel_thm; distinctness "result"; injectivity "result"] THEN
  DISCH_THEN(CHOOSE_THEN (SUBST_ALL_TAC o CONJUNCT2)) THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CONS_11] THEN X_GEN_TAC `res_v:bvl_v` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:bvl_v` o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "res_v" with Failure _ -> false)) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `res':bvl_v` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[alloc_hole_has_val_def; LENGTH; EL; HD; TL; ONE] THEN
  DISCH_THEN(X_CHOOSE_THEN `hq:num` (X_CHOOSE_THEN `tq:num`
    (X_CHOOSE_THEN `lq:bvl_v list` (X_CHOOSE_THEN `rq:bvl_v list` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o REWRITE_RULE[injectivity "bvl_v"] o
    check (fun th -> is_eq (concl th) && rhs (concl th) = `bvl_RefPtr F hq`)) THEN
  SUBGOAL_THEN `~(p2 IN FRANGE (f_aux:(num,num)fmap))` ASSUME_TAC THENL
   [MATCH_MP_TAC (GEN_ALL non_fresh_not_in_frange) THEN
    MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `refs3:(num,(bvl_v)bvl_ref)fmap`] THEN
    ASM_REWRITE_TAC[FDOM_FLOOKUP; option_DISTINCT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:(num,num)fmap`; `refs3:(num,(bvl_v)bvl_ref)fmap`;
    `bvi_state_refs (t_aux:(C,FFI)bvi_state)`; `{p2:num}`; `hole_ptr:num`; `tag':num`;
    `left':bvl_v list`; `bvl_RefPtr F p2`; `right':bvl_v list`] BVITMCAUX_hole_after) THEN
  EXPAND_TAC "X2" THEN ASM_REWRITE_TAC[IN_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `ch:bvl_v` (CONJUNCTS_THEN2 ASSUME_TAC
    (SUBST_ALL_TAC o SYM))) THEN
  MP_TAC(ISPECL [`f:(num,num)fmap`; `refs3:(num,(bvl_v)bvl_ref)fmap`;
    `bvi_state_refs (t_aux:(C,FFI)bvi_state)`; `{p2:num}`; `p2:num`; `tag:num`; `F`;
    `REVERSE (MAP (\n. EL n (env2:bvl_v list)) right)`; `bvl_Number (&0)`;
    `REVERSE (MAP (\n. EL n (env2:bvl_v list)) left)`] BVITMCAUX_hue_at) THEN
  EXPAND_TAC "M2" THEN ASM_REWRITE_TAC[IN_SING] THEN
  REWRITE_TAC[option_INJ; injectivity "bvl_ref"] THEN
  DISCH_THEN(X_CHOOSE_THEN `fq:bool` (X_CHOOSE_THEN `cq:bvl_v` STRIP_ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    (lhs (concl th) = `tq:num` || lhs (concl th) = `lq:bvl_v list` ||
     lhs (concl th) = `rq:bvl_v list`)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `res':bvl_v`)) THEN
  EXISTS_TAC `bvl_RefPtr F p2` THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`hole_ptr:num`; `tag':num`; `left':bvl_v list`;
                          `right':bvl_v list`] THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[rw_block_args] THEN
  MATCH_MP_TAC mb_rel_cons THEN
  MAP_EVERY EXISTS_TAC [`REVERSE (MAP (\n. EL n (env2:bvl_v list)) right)`;
    `res':bvl_v`; `REVERSE (MAP (\n. EL n (env2:bvl_v list)) left)`] THEN
  SUBGOAL_THEN `~(p2 IN FDOM (bvi_state_refs (s':(C,FFI)bvi_state)))` ASSUME_TAC THENL
   [UNDISCH_TAC `FDOM (bvi_state_refs (s':(C,FFI)bvi_state)) SUBSET
                 FDOM (refs:(num,(bvl_v)bvl_ref)fmap)` THEN
    UNDISCH_TAC `~(p2 IN FDOM (refs:(num,(bvl_v)bvl_ref)fmap))` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DOMSUB_FLOOKUP_THM] THEN REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[DOMSUB_COMMUTES] THEN MATCH_MP_TAC mb_rel_del THEN
    MAP_EVERY EXISTS_TAC [`tag':num`; `left':bvl_v list`; `p2:num`;
                          `right':bvl_v list`] THEN
    ASM_REWRITE_TAC[DOMSUB_FLOOKUP_THM; FDOM_DOMSUB; IN_DELETE];
    REWRITE_TAC[GSYM MAP_REVERSE] THEN ONCE_REWRITE_TAC[GSYM list_rel_reverse] THEN
    MATCH_MP_TAC (GEN_ALL list_rel_submap) THEN EXISTS_TAC `f:(num,num)fmap` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC wf_vars_list_rel THEN ASM_MESON_TAC[];
    REWRITE_TAC[GSYM MAP_REVERSE] THEN ONCE_REWRITE_TAC[GSYM list_rel_reverse] THEN
    MATCH_MP_TAC (GEN_ALL list_rel_submap) THEN EXISTS_TAC `f:(num,num)fmap` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC wf_vars_list_rel THEN ASM_MESON_TAC[]]);;

let BVITMCAUX_cb_cb_work = prove
 (`!tag left child right.
     (!loc f opt env env2 (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) t r clock.
        BVITMCAUX_cb_hyps child loc f opt env env2 s s' t r clock ==>
        !loc_opt. optimised_code loc loc_opt (bvi_state_code s) (bvi_state_code s') ==>
                  BVITMCAUX_cb_aux child loc_opt f s env2 s' t r) ==>
     !loc f env env2 (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) t r clock loc_opt
      ptr idx (work:bvi_exp) hole_ptr.
        BVITMCAUX_cb_hyps (CallBlock tag left child right) loc f T env env2 s s' t r
          clock /\
        optimised_code loc loc_opt (bvi_state_code s) (bvi_state_code s') /\
        ptr = LENGTH env /\ idx = LENGTH env + 1 /\
        (?c. hole_has_val f env env2 (bvi_state_refs s') c) /\
        hole_not_finalised (bvi_state_refs s') hole_ptr /\
        EL ptr env2 = bvl_RefPtr F hole_ptr ==>
        ?r_work f_work t_work.
          bvi_evaluate ([cb_to_bvi_worker (CallBlock tag left child right) loc_opt ptr idx],
                        env2,s') = (r_work,t_work) /\
          opt_res_rel f_work r r_work /\
          bvi_tmcProof_state_rel f_work t t_work /\
          f SUBMAP f_work /\
          only_fresh f f_work (bvi_state_refs s') /\
          holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t_work)
            {hole_ptr} /\
          holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t_work) /\
          !res_v. r = Rval [res_v] ==>
            ?res_v'.
              mb_rel f_work (bvi_state_refs s') (bvi_state_refs t_work \\ hole_ptr)
                res_v res_v' /\
              hole_has_val f env env2 (bvi_state_refs t_work) res_v'`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> LABEL_TAC "hyps" th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[BVITMCAUX_cb_hyps_def] th)) STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (BVITMCAUX_head_is "hole_has_val")) THEN
  REWRITE_TAC[hole_has_val_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `hp:num`
    (X_CHOOSE_THEN `tag':num` (X_CHOOSE_THEN `fin:bool`
      (X_CHOOSE_THEN `left':bvl_v list` (X_CHOOSE_THEN `right':bvl_v list`
        STRIP_ASSUME_TAC)))))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    (lhs (concl th) = `ptr:num` || lhs (concl th) = `idx:num`)))) THEN
  SUBGOAL_THEN `hp:num = hole_ptr` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `EL (LENGTH (env:bvl_v list)) env2 = bvl_RefPtr F hp` THEN
    ASM_REWRITE_TAC[injectivity "bvl_v"] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `fin = F` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `hole_not_finalised (bvi_state_refs (s':(C,FFI)bvi_state)) hole_ptr` THEN
    ASM_REWRITE_TAC[hole_not_finalised_def; option_INJ; injectivity "bvl_ref"] THEN
    MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`tag:num`; `left:num list`; `child:call_block`; `right:num list`;
    `loc:num`; `env:bvl_v list`; `s:(num#C,FFI)bvi_state`;
    `r:(bvl_v list,exn_or_ret)result`; `t:(num#C,FFI)bvi_state`]
    BVITMCAUX_cb_cb_source) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rc:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `sc:(num#C,FFI)bvi_state` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "res")))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wf_cb_def]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th ->
    is_conj (concl th) && BVITMCAUX_head_is "wf_vars" (CONJUNCT1 th))) THEN
  SUBGOAL_THEN `state_ref_rel f (bvi_state_refs (s:(num#C,FFI)bvi_state))
                  (bvi_state_refs (s':(C,FFI)bvi_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[bvi_tmcProof_state_rel_def]; ALL_TAC] THEN
  ABBREV_TAC `refs = bvi_state_refs (s':(C,FFI)bvi_state)` THEN
  ABBREV_TAC `p2 = minimal ptr. ~(ptr IN FDOM (refs:(num,(bvl_v)bvl_ref)fmap))` THEN
  SUBGOAL_THEN `~(p2 IN FDOM (refs:(num,(bvl_v)bvl_ref)fmap))` ASSUME_TAC THENL
   [EXPAND_TAC "p2" THEN REWRITE_TAC[fresh_ptr_fresh]; ALL_TAC] THEN
  SUBGOAL_THEN `~(p2 IN FRANGE (f:(num,num)fmap))` ASSUME_TAC THENL
   [EXPAND_TAC "p2" THEN MATCH_MP_TAC fresh_not_in_range_f THEN
    EXISTS_TAC `bvi_state_refs (s:(num#C,FFI)bvi_state)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p2:num = hole_ptr)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(hole_ptr IN FDOM (refs:(num,(bvl_v)bvl_ref)fmap))` THEN
    ASM_REWRITE_TAC[FDOM_FLOOKUP; option_DISTINCT]; ALL_TAC] THEN
  REWRITE_TAC[cb_to_bvi_worker_def; LET_DEF; LET_END_DEF] THEN
  ABBREV_TAC `refs3 = (refs:(num,(bvl_v)bvl_ref)fmap) |+
    (p2,MutBlock tag F (REVERSE (MAP (\n. EL n env2) right)) (bvl_Number (&0))
                       (REVERSE (MAP (\n. EL n env2) left))) |+
    (hole_ptr,MutBlock tag' F left' (bvl_RefPtr F p2) right')` THEN
  SUBGOAL_THEN
   `bvi_evaluate ([bvi_Let [mut_cons tag left right]
       (bvi_Let [update_cons (bvi_Var (LENGTH (env:bvl_v list) + 1))
                  (bvi_Var ((LENGTH env + 1) + 1)) (bvi_Var 0)]
          (cb_to_bvi_worker_aux (shift_cb 2 child) loc_opt 1
             (LENGTH (right:num list))))],
      env2,(s':(C,FFI)bvi_state)) =
    bvi_evaluate ([cb_to_bvi_worker_aux (shift_cb 2 child) loc_opt 1 (LENGTH right)],
      CONS bvl_Unit (CONS (bvl_RefPtr F p2) env2),
      bvi_state_refs_fupd (K refs3) s')`
   SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
    MP_TAC(ISPECL [`tag:num`; `left:num list`; `right:num list`; `env2:bvl_v list`;
      `s':(C,FFI)bvi_state`; `LENGTH (env:bvl_v list)`] BVITMCAUX_eval_mut_cons) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[bvi_evaluate_def] THEN REWRITE_TAC[APPEND] THEN
    MP_TAC(ISPECL [`bvi_Var (LENGTH (env:bvl_v list) + 1)`;
      `bvi_Var ((LENGTH (env:bvl_v list) + 1) + 1)`; `bvi_Var 0`;
      `CONS (bvl_RefPtr F p2) (env2:bvl_v list)`;
      `bvi_state_refs_fupd (K ((refs:(num,(bvl_v)bvl_ref)fmap) |+
         (p2,MutBlock tag F (REVERSE (MAP (\n. EL n env2) right)) (bvl_Number (&0))
                            (REVERSE (MAP (\n. EL n env2) left))))) (s':(C,FFI)bvi_state)`;
      `bvl_RefPtr F p2`; `&(LENGTH (left':bvl_v list)):int`; `hole_ptr:num`;
      `tag':num`; `left':bvl_v list`; `c:bvl_v`; `right':bvl_v list`]
      BVITMCAUX_eval_update_cons) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[] THEN CONJ_TAC THENL
       [W(fun (_,w) -> MP_TAC(PART_MATCH (lhs o rand) (SPEC_ALL BVITMCAUX_eval_upd_vars)
          (lhs w))) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE] THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[APPEND; bvi_state_INFO.ri_accfupds; K_THM; BVITMCAUX_refs_fupd_fupd] THEN
    EXPAND_TAC "refs3" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`loc:num`; `f:(num,num)fmap`; `T`;
    `env:bvl_v list`; `env2:bvl_v list`; `s:(num#C,FFI)bvi_state`;
    `s':(C,FFI)bvi_state`; `sc:(num#C,FFI)bvi_state`;
    `rc:(bvl_v list,exn_or_ret)result`; `clock:num`]) THEN
  REWRITE_TAC[BVITMCAUX_cb_hyps_def] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [USE_THEN "res" MP_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[distinctness "result"] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `loc_opt:num`) THEN
  ASM_REWRITE_TAC[BVITMCAUX_cb_aux_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`refs3:(num,(bvl_v)bvl_ref)fmap`;
    `[bvl_Unit; bvl_RefPtr F p2]`; `1`; `LENGTH (right:num list)`; `p2:num`]) THEN
  REWRITE_TAC[LENGTH; APPEND; ARITH_RULE `SUC (SUC 0) = 2`; EL; HD; TL; ONE] THEN
  REWRITE_TAC[GSYM ONE] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "refs3" THEN REPEAT(MATCH_MP_TAC state_ref_rel_filled THEN
                                     ASM_REWRITE_TAC[]);
      EXISTS_TAC `bvl_Number (&0)` THEN REWRITE_TAC[alloc_hole_has_val_def] THEN
      MAP_EVERY EXISTS_TAC [`p2:num`; `tag:num`;
        `REVERSE (MAP (\n. EL n (env2:bvl_v list)) right)`;
        `REVERSE (MAP (\n. EL n (env2:bvl_v list)) left)`] THEN
      EXPAND_TAC "refs3" THEN
      ASM_REWRITE_TAC[LENGTH; EL; HD; TL; ONE; LENGTH_REVERSE; LENGTH_MAP;
                      FLOOKUP_UPDATE] THEN
      ARITH_TAC;
      EXPAND_TAC "refs3" THEN REWRITE_TAC[FDOM_FUPDATE] THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r_aux:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `t_aux:(C,FFI)bvi_state` (X_CHOOSE_THEN `f_aux:(num,num)fmap`
      STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`r_aux:(bvl_v list,exn_or_ret)result`;
    `f_aux:(num,num)fmap`; `t_aux:(C,FFI)bvi_state`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M2 = MutBlock tag F (REVERSE (MAP (\n. EL n (env2:bvl_v list)) right))
                     (bvl_Number (&0)) (REVERSE (MAP (\n. EL n env2) left))` THEN
  ABBREV_TAC `X2 = MutBlock tag' F left' (bvl_RefPtr F p2) right'` THEN
  SUBGOAL_THEN `refs3 = ((refs:(num,(bvl_v)bvl_ref)fmap) |+ (hole_ptr,X2)) |+ (p2,M2)`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `refs3:(num,(bvl_v)bvl_ref)fmap`)) THEN
    MATCH_MP_TAC flookup_com_neq THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `only_fresh f f_aux (refs:(num,(bvl_v)bvl_ref)fmap)` ASSUME_TAC THENL
   [MATCH_MP_TAC only_fresh_del THEN
    MAP_EVERY EXISTS_TAC [`hole_ptr:num`; `X2:(bvl_v)bvl_ref`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC only_fresh_del THEN
    MAP_EVERY EXISTS_TAC [`p2:num`; `M2:(bvl_v)bvl_ref`] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `holes_still_not_finalised (f:(num,num)fmap) (refs:(num,(bvl_v)bvl_ref)fmap)
                  (bvi_state_refs (t_aux:(C,FFI)bvi_state))` ASSUME_TAC THENL
   [MATCH_MP_TAC holes_still_not_finalised_del THEN
    MAP_EVERY EXISTS_TAC [`hole_ptr:num`; `tag':num`; `left':bvl_v list`;
                          `bvl_RefPtr F p2`; `right':bvl_v list`] THEN
    MATCH_MP_TAC holes_still_not_finalised_del THEN
    MAP_EVERY EXISTS_TAC [`p2:num`; `tag:num`;
      `REVERSE (MAP (\n. EL n (env2:bvl_v list)) right)`; `bvl_Number (&0)`;
      `REVERSE (MAP (\n. EL n (env2:bvl_v list)) left)`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `holes_unchanged_except (f:(num,num)fmap) (refs:(num,(bvl_v)bvl_ref)fmap)
                  (bvi_state_refs (t_aux:(C,FFI)bvi_state)) {hole_ptr}` ASSUME_TAC THENL
   [MP_TAC(INST [`F`,`fin':bool`; `c:bvl_v`,`c':bvl_v`]
      (ISPECL [`f:(num,num)fmap`; `refs:(num,(bvl_v)bvl_ref)fmap`;
        `bvi_state_refs (t_aux:(C,FFI)bvi_state)`; `ARB:num`; `hole_ptr:num`;
        `tag':num`; `F`; `left':bvl_v list`; `bvl_RefPtr F p2`; `right':bvl_v list`]
        holes_unchanged_except_changed)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC holes_unchanged_except_del_SING THEN
    MAP_EVERY EXISTS_TAC [`p2:num`; `M2:(bvl_v)bvl_ref`] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[FDOM_FUPDATE; IN_INSERT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FLOOKUP (refs3:(num,(bvl_v)bvl_ref)fmap) hole_ptr =
                  SOME (X2:(bvl_v)bvl_ref) /\
                FLOOKUP refs3 p2 = SOME (M2:(bvl_v)bvl_ref)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
        rhs (concl th) = `refs3:(num,(bvl_v)bvl_ref)fmap`)) THEN
      REWRITE_TAC[FLOOKUP_UPDATE];
      ASM_REWRITE_TAC[FLOOKUP_UPDATE]];
    ALL_TAC] THEN
  REMOVE_THEN "res" (DISJ_CASES_THEN2 (X_CHOOSE_THEN `cc:bvl_v` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `e:(exn_or_ret)error_result` STRIP_ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    (lhs (concl th) = `rc:(bvl_v list,exn_or_ret)result` ||
     lhs (concl th) = `r:(bvl_v list,exn_or_ret)result` ||
     lhs (concl th) = `t:(num#C,FFI)bvi_state`)))) THEN
  ASM_REWRITE_TAC[distinctness "result"] THEN
  UNDISCH_TAC `opt_res_rel f_aux (Rval [cc]) r_aux` THEN
  REWRITE_TAC[BVITMCAUX_opt_res_rel_thm; distinctness "result"; injectivity "result"] THEN
  DISCH_THEN(CHOOSE_THEN (SUBST_ALL_TAC o CONJUNCT2)) THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CONS_11; injectivity "result"] THEN X_GEN_TAC `res_v:bvl_v` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `cc:bvl_v` o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "res_v" with Failure _ -> false)) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `res':bvl_v` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[alloc_hole_has_val_def; LENGTH; EL; HD; TL; ONE] THEN
  DISCH_THEN(X_CHOOSE_THEN `hq:num` (X_CHOOSE_THEN `tq:num`
    (X_CHOOSE_THEN `lq:bvl_v list` (X_CHOOSE_THEN `rq:bvl_v list` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o REWRITE_RULE[injectivity "bvl_v"] o
    check (fun th -> is_eq (concl th) && rhs (concl th) = `bvl_RefPtr F hq`)) THEN
  SUBGOAL_THEN `~(p2 IN FRANGE (f_aux:(num,num)fmap))` ASSUME_TAC THENL
   [MATCH_MP_TAC (GEN_ALL non_fresh_not_in_frange) THEN
    MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `refs3:(num,(bvl_v)bvl_ref)fmap`] THEN
    ASM_REWRITE_TAC[FDOM_FLOOKUP; option_DISTINCT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:(num,num)fmap`; `refs3:(num,(bvl_v)bvl_ref)fmap`;
    `bvi_state_refs (t_aux:(C,FFI)bvi_state)`; `{p2:num}`; `hole_ptr:num`; `tag':num`;
    `left':bvl_v list`; `bvl_RefPtr F p2`; `right':bvl_v list`] BVITMCAUX_hole_after) THEN
  EXPAND_TAC "X2" THEN ASM_REWRITE_TAC[IN_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `ch:bvl_v` (CONJUNCTS_THEN2 ASSUME_TAC
    (SUBST_ALL_TAC o SYM))) THEN
  MP_TAC(ISPECL [`f:(num,num)fmap`; `refs3:(num,(bvl_v)bvl_ref)fmap`;
    `bvi_state_refs (t_aux:(C,FFI)bvi_state)`; `{p2:num}`; `p2:num`; `tag:num`; `F`;
    `REVERSE (MAP (\n. EL n (env2:bvl_v list)) right)`; `bvl_Number (&0)`;
    `REVERSE (MAP (\n. EL n (env2:bvl_v list)) left)`] BVITMCAUX_hue_at) THEN
  EXPAND_TAC "M2" THEN ASM_REWRITE_TAC[IN_SING] THEN
  REWRITE_TAC[option_INJ; injectivity "bvl_ref"] THEN
  DISCH_THEN(X_CHOOSE_THEN `fq:bool` (X_CHOOSE_THEN `cq:bvl_v` STRIP_ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    (lhs (concl th) = `tq:num` || lhs (concl th) = `lq:bvl_v list` ||
     lhs (concl th) = `rq:bvl_v list`)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `res':bvl_v`)) THEN
  EXISTS_TAC `bvl_RefPtr F p2` THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`hole_ptr:num`; `tag':num`; `F`; `left':bvl_v list`;
                          `right':bvl_v list`] THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[rw_block_args] THEN
  MATCH_MP_TAC mb_rel_cons THEN
  MAP_EVERY EXISTS_TAC [`REVERSE (MAP (\n. EL n (env2:bvl_v list)) right)`;
    `res':bvl_v`; `REVERSE (MAP (\n. EL n (env2:bvl_v list)) left)`] THEN
  ASM_REWRITE_TAC[DOMSUB_FLOOKUP_THM] THEN REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[DOMSUB_COMMUTES] THEN MATCH_MP_TAC mb_rel_del THEN
    MAP_EVERY EXISTS_TAC [`tag':num`; `left':bvl_v list`; `p2:num`;
                          `right':bvl_v list`] THEN
    ASM_REWRITE_TAC[DOMSUB_FLOOKUP_THM; FDOM_DOMSUB; IN_DELETE];
    REWRITE_TAC[GSYM MAP_REVERSE] THEN ONCE_REWRITE_TAC[GSYM list_rel_reverse] THEN
    MATCH_MP_TAC (GEN_ALL list_rel_submap) THEN EXISTS_TAC `f:(num,num)fmap` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC wf_vars_list_rel THEN ASM_MESON_TAC[];
    REWRITE_TAC[GSYM MAP_REVERSE] THEN ONCE_REWRITE_TAC[GSYM list_rel_reverse] THEN
    MATCH_MP_TAC (GEN_ALL list_rel_submap) THEN EXISTS_TAC `f:(num,num)fmap` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC wf_vars_list_rel THEN ASM_MESON_TAC[]]);;

let BVITMCAUX_eval_finalise = prove
 (`!e x env (s:(C,FFI)bvi_state) v refs'.
     bvi_finalise_cons x (bvi_state_refs s) = SOME (v,refs') ==>
     bvi_evaluate ([bvi_tmc_finalise_cons 1],CONS e (CONS x env),s) =
     (Rval [v],bvi_state_refs_fupd (K refs') s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvi_tmc_finalise_cons_def] THEN
  REWRITE_TAC[bvi_evaluate_def; LENGTH; ARITH_RULE `1 < SUC (SUC n)`] THEN
  REWRITE_TAC[ONE; EL; HD; TL] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; APPEND] THEN
  CONV_TAC(ONCE_DEPTH_CONV BVITMCAUX_DOAPP_CONV) THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

let BVITMCAUX_cb_cb_wrap = prove
 (`!tag left child right.
     (!loc f opt env env2 (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) t r clock.
        BVITMCAUX_cb_hyps child loc f opt env env2 s s' t r clock ==>
        !loc_opt. optimised_code loc loc_opt (bvi_state_code s) (bvi_state_code s') ==>
                  BVITMCAUX_cb_aux child loc_opt f s env2 s' t r) ==>
     !loc f opt env env2 (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) t r clock loc_opt.
        BVITMCAUX_cb_hyps (CallBlock tag left child right) loc f opt env env2 s s' t r
          clock /\
        optimised_code loc loc_opt (bvi_state_code s) (bvi_state_code s') ==>
        ?t_wrap f_wrap r_wrap.
          bvi_evaluate ([cb_to_bvi_wrapper tag left child right loc_opt],env2,s') =
            (r_wrap,t_wrap) /\
          result_rel (ALL2 (bvi_tmcProof_v_rel f_wrap)) (eor_rel f_wrap) r r_wrap /\
          bvi_tmcProof_state_rel f_wrap t t_wrap /\
          f SUBMAP f_wrap /\
          only_fresh f f_wrap (bvi_state_refs s') /\
          holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t_wrap) {} /\
          holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t_wrap)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> LABEL_TAC "hyps" th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[BVITMCAUX_cb_hyps_def] th)) STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`tag:num`; `left:num list`; `child:call_block`; `right:num list`;
    `loc:num`; `env:bvl_v list`; `s:(num#C,FFI)bvi_state`;
    `r:(bvl_v list,exn_or_ret)result`; `t:(num#C,FFI)bvi_state`]
    BVITMCAUX_cb_cb_source) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rc:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `sc:(num#C,FFI)bvi_state` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "res")))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wf_cb_def]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th ->
    is_conj (concl th) && BVITMCAUX_head_is "wf_vars" (CONJUNCT1 th))) THEN
  SUBGOAL_THEN `state_ref_rel f (bvi_state_refs (s:(num#C,FFI)bvi_state))
                  (bvi_state_refs (s':(C,FFI)bvi_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[bvi_tmcProof_state_rel_def]; ALL_TAC] THEN
  ABBREV_TAC `refs = bvi_state_refs (s':(C,FFI)bvi_state)` THEN
  ABBREV_TAC `p2 = minimal ptr. ~(ptr IN FDOM (refs:(num,(bvl_v)bvl_ref)fmap))` THEN
  SUBGOAL_THEN `~(p2 IN FDOM (refs:(num,(bvl_v)bvl_ref)fmap))` ASSUME_TAC THENL
   [EXPAND_TAC "p2" THEN REWRITE_TAC[fresh_ptr_fresh]; ALL_TAC] THEN
  SUBGOAL_THEN `~(p2 IN FRANGE (f:(num,num)fmap))` ASSUME_TAC THENL
   [EXPAND_TAC "p2" THEN MATCH_MP_TAC fresh_not_in_range_f THEN
    EXISTS_TAC `bvi_state_refs (s:(num#C,FFI)bvi_state)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `M2 = MutBlock tag F (REVERSE (MAP (\n. EL n (env2:bvl_v list)) right))
                     (bvl_Number (&0)) (REVERSE (MAP (\n. EL n env2) left))` THEN
  ABBREV_TAC `refs2 = (refs:(num,(bvl_v)bvl_ref)fmap) |+ (p2,M2)` THEN
  REWRITE_TAC[cb_to_bvi_wrapper_def] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  MP_TAC(ISPECL [`tag:num`; `left:num list`; `right:num list`; `env2:bvl_v list`;
    `s':(C,FFI)bvi_state`; `LENGTH (env:bvl_v list)`] BVITMCAUX_eval_mut_cons) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[bvi_tmcProof_env_rel_length]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN REWRITE_TAC[APPEND] THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`loc:num`; `f:(num,num)fmap`; `opt:bool`;
    `env:bvl_v list`; `env2:bvl_v list`; `s:(num#C,FFI)bvi_state`;
    `s':(C,FFI)bvi_state`; `sc:(num#C,FFI)bvi_state`;
    `rc:(bvl_v list,exn_or_ret)result`; `clock:num`]) THEN
  REWRITE_TAC[BVITMCAUX_cb_hyps_def] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [USE_THEN "res" MP_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[distinctness "result"] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `loc_opt:num`) THEN
  ASM_REWRITE_TAC[BVITMCAUX_cb_aux_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`refs2:(num,(bvl_v)bvl_ref)fmap`;
    `[bvl_RefPtr F p2]`; `0`; `LENGTH (right:num list)`; `p2:num`]) THEN
  REWRITE_TAC[LENGTH; APPEND; GSYM ONE; EL; HD] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "refs2" THEN MATCH_MP_TAC state_ref_rel_filled THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `bvl_Number (&0)` THEN REWRITE_TAC[alloc_hole_has_val_def] THEN
      MAP_EVERY EXISTS_TAC [`p2:num`; `tag:num`;
        `REVERSE (MAP (\n. EL n (env2:bvl_v list)) right)`;
        `REVERSE (MAP (\n. EL n (env2:bvl_v list)) left)`] THEN
      EXPAND_TAC "refs2" THEN EXPAND_TAC "M2" THEN
      ASM_REWRITE_TAC[LENGTH; EL; HD; LENGTH_REVERSE; LENGTH_MAP; FLOOKUP_UPDATE] THEN
      ARITH_TAC;
      EXPAND_TAC "refs2" THEN REWRITE_TAC[FDOM_FUPDATE] THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r_aux:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `t_aux:(C,FFI)bvi_state` (X_CHOOSE_THEN `f_aux:(num,num)fmap`
      STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `only_fresh f f_aux (refs:(num,(bvl_v)bvl_ref)fmap)` ASSUME_TAC THENL
   [MATCH_MP_TAC only_fresh_del THEN
    MAP_EVERY EXISTS_TAC [`p2:num`; `M2:(bvl_v)bvl_ref`] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `holes_still_not_finalised (f:(num,num)fmap) (refs:(num,(bvl_v)bvl_ref)fmap)
                  (bvi_state_refs (t_aux:(C,FFI)bvi_state))` ASSUME_TAC THENL
   [MATCH_MP_TAC holes_still_not_finalised_del THEN
    MAP_EVERY EXISTS_TAC [`p2:num`; `tag:num`;
      `REVERSE (MAP (\n. EL n (env2:bvl_v list)) right)`; `bvl_Number (&0)`;
      `REVERSE (MAP (\n. EL n (env2:bvl_v list)) left)`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `holes_unchanged_except (f:(num,num)fmap) (refs:(num,(bvl_v)bvl_ref)fmap)
                  (bvi_state_refs (t_aux:(C,FFI)bvi_state)) {}` ASSUME_TAC THENL
   [MATCH_MP_TAC holes_unchanged_except_del_SING THEN
    MAP_EVERY EXISTS_TAC [`p2:num`; `M2:(bvl_v)bvl_ref`] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "res" (DISJ_CASES_THEN2 (X_CHOOSE_THEN `cc:bvl_v` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `e:(exn_or_ret)error_result` STRIP_ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    (lhs (concl th) = `rc:(bvl_v list,exn_or_ret)result` ||
     lhs (concl th) = `r:(bvl_v list,exn_or_ret)result` ||
     lhs (concl th) = `t:(num#C,FFI)bvi_state`)))) THENL
   [ALL_TAC;
    UNDISCH_TAC `opt_res_rel f_aux (Rerr e) r_aux` THEN
    REWRITE_TAC[BVITMCAUX_opt_res_rel_thm; distinctness "result"; injectivity "result"] THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:(exn_or_ret)error_result`
      (X_CHOOSE_THEN `e2:(exn_or_ret)error_result` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`t_aux:(C,FFI)bvi_state`; `f_aux:(num,num)fmap`;
      `Rerr e2:(bvl_v list,exn_or_ret)result`] THEN
    ASM_REWRITE_TAC[result_rel_def]] THEN
  UNDISCH_TAC `opt_res_rel f_aux (Rval [cc]) r_aux` THEN
  REWRITE_TAC[BVITMCAUX_opt_res_rel_thm; distinctness "result"; injectivity "result"] THEN
  DISCH_THEN(CHOOSE_THEN (SUBST_ALL_TAC o CONJUNCT2)) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `cc:bvl_v` o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "res_v" with Failure _ -> false)) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `res':bvl_v` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[alloc_hole_has_val_def; LENGTH; EL; HD] THEN
  DISCH_THEN(X_CHOOSE_THEN `hq:num` (X_CHOOSE_THEN `tq:num`
    (X_CHOOSE_THEN `lq:bvl_v list` (X_CHOOSE_THEN `rq:bvl_v list` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o REWRITE_RULE[injectivity "bvl_v"] o
    check (fun th -> is_eq (concl th) && rhs (concl th) = `bvl_RefPtr F hq`)) THEN
  SUBGOAL_THEN `FLOOKUP (refs2:(num,(bvl_v)bvl_ref)fmap) p2 = SOME (M2:(bvl_v)bvl_ref)`
    ASSUME_TAC THENL
   [EXPAND_TAC "refs2" THEN REWRITE_TAC[FLOOKUP_UPDATE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(p2 IN FRANGE (f_aux:(num,num)fmap))` ASSUME_TAC THENL
   [MATCH_MP_TAC (GEN_ALL non_fresh_not_in_frange) THEN
    MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `refs2:(num,(bvl_v)bvl_ref)fmap`] THEN
    ASM_REWRITE_TAC[FDOM_FLOOKUP; option_DISTINCT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:(num,num)fmap`; `refs2:(num,(bvl_v)bvl_ref)fmap`;
    `bvi_state_refs (t_aux:(C,FFI)bvi_state)`; `{p2:num}`; `p2:num`; `tag:num`; `F`;
    `REVERSE (MAP (\n. EL n (env2:bvl_v list)) right)`; `bvl_Number (&0)`;
    `REVERSE (MAP (\n. EL n (env2:bvl_v list)) left)`] BVITMCAUX_hue_at) THEN
  EXPAND_TAC "M2" THEN ASM_REWRITE_TAC[IN_SING] THEN
  REWRITE_TAC[option_INJ; injectivity "bvl_ref"] THEN
  DISCH_THEN(X_CHOOSE_THEN `fq:bool` (X_CHOOSE_THEN `cq:bvl_v` STRIP_ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    (lhs (concl th) = `tq:num` || lhs (concl th) = `lq:bvl_v list` ||
     lhs (concl th) = `rq:bvl_v list`)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `res':bvl_v`)) THEN
  SUBGOAL_THEN
   `mb_rel f_aux refs (bvi_state_refs (t_aux:(C,FFI)bvi_state))
      (bvl_Block tag (REVERSE (APPEND (APPEND (MAP (\n. EL n env) left) [cc])
                                      (MAP (\n. EL n env) right))))
      (bvl_RefPtr F p2)` ASSUME_TAC THENL
   [REWRITE_TAC[rw_block_args] THEN MATCH_MP_TAC mb_rel_cons THEN
    MAP_EVERY EXISTS_TAC [`REVERSE (MAP (\n. EL n (env2:bvl_v list)) right)`;
      `res':bvl_v`; `REVERSE (MAP (\n. EL n (env2:bvl_v list)) left)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    REWRITE_TAC[GSYM MAP_REVERSE] THEN ONCE_REWRITE_TAC[GSYM list_rel_reverse] THEN
    MATCH_MP_TAC (GEN_ALL list_rel_submap) THEN EXISTS_TAC `f:(num,num)fmap` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC wf_vars_list_rel THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bvl_RefPtr F p2`; `bvi_state_refs (t_aux:(C,FFI)bvi_state)`;
    `f:(num,num)fmap`; `f_aux:(num,num)fmap`; `bvi_state_refs (sc:(num#C,FFI)bvi_state)`;
    `bvl_Block tag (REVERSE (APPEND (APPEND (MAP (\n. EL n env) left) [cc])
                                    (MAP (\n. EL n env) right)))`;
    `refs:(num,(bvl_v)bvl_ref)fmap`] evaluate_finalise_cons) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[bvi_tmcProof_state_rel_def]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v3:bvl_v` (X_CHOOSE_THEN `t_refs':(num,(bvl_v)bvl_ref)fmap`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`bvi_state_refs_fupd (K t_refs') (t_aux:(C,FFI)bvi_state)`;
    `f_aux:(num,num)fmap`; `Rval [v3]:(bvl_v list,exn_or_ret)result`] THEN
  ASM_REWRITE_TAC[result_rel_def; ALL2; bvi_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BVITMCAUX_eval_finalise THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`f_aux:(num,num)fmap`; `f_aux:(num,num)fmap`;
      `sc:(num#C,FFI)bvi_state`; `t_aux:(C,FFI)bvi_state`;
      `bvi_state_refs (sc:(num#C,FFI)bvi_state)`; `t_refs':(num,(bvl_v)bvl_ref)fmap`]
      BVITMCAUX_state_rel_refs) THEN
    ASM_REWRITE_TAC[SUBMAP_REFL; BVITMCAUX_refs_fupd_id] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[bvi_tmcProof_state_rel_def];
    MATCH_MP_TAC holes_unchanged_except_trans THEN
    MAP_EVERY EXISTS_TAC [`f_aux:(num,num)fmap`;
                          `bvi_state_refs (t_aux:(C,FFI)bvi_state)`] THEN
    ASM_REWRITE_TAC[]]);;

let BVITMCAUX_cb_main_aux = prove
 (`!cb loc f opt env env2 (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) t r clock.
     BVITMCAUX_cb_hyps cb loc f opt env env2 s s' t r clock ==>
     BVITMCAUX_cb_main cb loc f env2 s' t r /\
     !loc_opt. optimised_code loc loc_opt (bvi_state_code s) (bvi_state_code s') ==>
               BVITMCAUX_cb_aux cb loc_opt f s env2 s' t r`,
  MATCH_MP_TAC call_block_INDUCT THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`tag:num`; `left:num list`; `child:call_block`;
                         `right:num list`] THEN
    DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`tag:num`; `left:num list`; `child:call_block`; `right:num list`]
        BVITMCAUX_cb_cb_main) THEN
      ANTS_TAC THENL [USE_THEN "ih" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
      X_GEN_TAC `loc_opt:num` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`tag:num`; `left:num list`; `child:call_block`; `right:num list`]
        BVITMCAUX_cb_cb_aux) THEN
      ANTS_TAC THENL [USE_THEN "ih" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]];
    MAP_EVERY X_GEN_TAC [`ts:num`; `args:num list`] THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[BVITMCAUX_cb_hyps_def; BVITMCAUX_cb_main_def; BVITMCAUX_cb_aux_def] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC BVITMCAUX_cb_rcall_main THEN
      MAP_EVERY EXISTS_TAC [`opt:bool`; `env:bvl_v list`; `s:(num#C,FFI)bvi_state`;
                            `clock:num`] THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC BVITMCAUX_cb_rcall_aux THEN
      MAP_EVERY EXISTS_TAC [`loc:num`; `opt:bool`; `env:bvl_v list`;
                            `s:(num#C,FFI)bvi_state`; `clock:num`] THEN
      ASM_MESON_TAC[]]]);;

let evaluate_cb = prove
 (`!cb loc f opt env env2 (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) t r clock.
     bvi_evaluate ([cb_to_bvi loc cb],env,s) = (r,t) /\
     wf_cb (LENGTH env) cb /\
     bvi_tmcProof_env_rel opt f env env2 /\
     bvi_tmcProof_state_rel f s s' /\
     bvi_state_clock s <= clock /\
     ~(r = Rerr (Rabort Rtype_error)) /\
     (!xs' (s'':(num#C,FFI)bvi_state). hypothesis xs' s'' clock) ==>
     (?r' t' f'.
        bvi_evaluate ([cb_to_bvi loc cb],env2,s') = (r',t') /\
        result_rel (ALL2 (bvi_tmcProof_v_rel f')) (eor_rel f') r r' /\
        bvi_tmcProof_state_rel f' t t' /\
        f SUBMAP f' /\
        only_fresh f f' (bvi_state_refs s') /\
        holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t') {} /\
        holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t')) /\
     !loc_opt.
       optimised_code loc loc_opt (bvi_state_code s) (bvi_state_code s') ==>
       (!tag left child right.
          cb = CallBlock tag left child right ==>
          ?t_wrap f_wrap r_wrap.
            bvi_evaluate ([cb_to_bvi_wrapper tag left child right loc_opt],env2,s') =
              (r_wrap,t_wrap) /\
            result_rel (ALL2 (bvi_tmcProof_v_rel f_wrap)) (eor_rel f_wrap) r r_wrap /\
            bvi_tmcProof_state_rel f_wrap t t_wrap /\
            f SUBMAP f_wrap /\
            only_fresh f f_wrap (bvi_state_refs s') /\
            holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t_wrap) {} /\
            holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t_wrap)) /\
       (!refs extras ptr idx hole_ptr.
          state_ref_rel f (bvi_state_refs s) refs /\
          (?c. alloc_hole_has_val f refs extras ptr idx c) /\
          FDOM (bvi_state_refs s') SUBSET FDOM refs /\
          EL ptr extras = bvl_RefPtr F hole_ptr ==>
          ?r_aux t_aux f_aux.
            bvi_evaluate ([cb_to_bvi_worker_aux (shift_cb (LENGTH extras) cb) loc_opt ptr
                             idx],
                          APPEND extras env2,bvi_state_refs_fupd (K refs) s') =
              (r_aux,t_aux) /\
            opt_res_rel f_aux r r_aux /\
            bvi_tmcProof_state_rel f_aux t t_aux /\
            f SUBMAP f_aux /\
            only_fresh f f_aux refs /\
            holes_unchanged_except f refs (bvi_state_refs t_aux) {hole_ptr} /\
            holes_still_not_finalised f refs (bvi_state_refs t_aux) /\
            !res_v.
              r = Rval [res_v] ==>
              ?res_v'.
                mb_rel f_aux (bvi_state_refs s') (bvi_state_refs t_aux \\ hole_ptr)
                  res_v res_v' /\
                alloc_hole_has_val f (bvi_state_refs t_aux) extras ptr idx res_v') /\
       (opt ==>
        (!ptr idx (work:bvi_exp) hole_ptr.
           ptr = LENGTH env /\
           idx = LENGTH env + 1 /\
           (?c. hole_has_val f env env2 (bvi_state_refs s') c) /\
           hole_not_finalised (bvi_state_refs s') hole_ptr /\
           EL ptr env2 = bvl_RefPtr F hole_ptr ==>
           ?r_work f_work t_work.
             bvi_evaluate ([cb_to_bvi_worker cb loc_opt ptr idx],env2,s') =
               (r_work,t_work) /\
             opt_res_rel f_work r r_work /\
             bvi_tmcProof_state_rel f_work t t_work /\
             f SUBMAP f_work /\
             only_fresh f f_work (bvi_state_refs s') /\
             holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t_work)
               {hole_ptr} /\
             holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t_work) /\
             !res_v.
               r = Rval [res_v] ==>
               ?res_v'.
                 mb_rel f_work (bvi_state_refs s') (bvi_state_refs t_work \\ hole_ptr)
                   res_v res_v' /\
                 hole_has_val f env env2 (bvi_state_refs t_work) res_v'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `BVITMCAUX_cb_hyps cb loc f opt env env2 (s:(num#C,FFI)bvi_state)
                  (s':(C,FFI)bvi_state) t r clock` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[BVITMCAUX_cb_hyps_def]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BVITMCAUX_cb_main_aux) THEN
  REWRITE_TAC[BVITMCAUX_cb_main_def; BVITMCAUX_cb_aux_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) (LABEL_TAC "aux")) THEN
  X_GEN_TAC `loc_opt:num` THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`tag:num`; `left:num list`; `child:call_block`;
                         `right:num list`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`tag:num`; `left:num list`; `child:call_block`; `right:num list`]
      BVITMCAUX_cb_cb_wrap) THEN
    ANTS_TAC THENL
     [REPEAT GEN_TAC THEN
      DISCH_THEN(ACCEPT_TAC o CONJUNCT2 o MATCH_MP BVITMCAUX_cb_main_aux); ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`loc:num`; `opt:bool`; `env:bvl_v list`;
                          `s:(num#C,FFI)bvi_state`; `clock:num`] THEN
    ASM_REWRITE_TAC[];
    REMOVE_THEN "aux" (MP_TAC o SPEC `loc_opt:num`) THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o EQT_INTRO o check (fun th -> concl th = `opt:bool`)) THEN
    CASES_ON `cb:call_block` THENL
     [REPEAT GEN_TAC THEN DISCH_TAC THEN
      MP_TAC(SPECL [`a0:num`; `a1:num list`; `a2:call_block`; `a3:num list`]
        BVITMCAUX_cb_cb_work) THEN
      ANTS_TAC THENL
     [REPEAT GEN_TAC THEN
      DISCH_THEN(ACCEPT_TAC o CONJUNCT2 o MATCH_MP BVITMCAUX_cb_main_aux); ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`loc:num`; `s:(num#C,FFI)bvi_state`; `clock:num`] THEN
      ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC BVITMCAUX_cb_rcall_worker THEN
      MAP_EVERY EXISTS_TAC [`loc:num`; `s:(num#C,FFI)bvi_state`; `clock:num`] THEN
      ASM_REWRITE_TAC[]]]);;

let evaluate_pres_opt_code = prove
 (`!loc loc_opt (s1:(num#C,FFI)bvi_state) (s2:(C,FFI)bvi_state) xs env1 env2 r1 u1 r2 u2.
     optimised_code loc loc_opt (bvi_state_code s1) (bvi_state_code s2) /\
     bvi_evaluate (xs,env1,s1) = (r1,u1) /\
     bvi_evaluate (xs,env2,s2) = (r2,u2) ==>
     optimised_code loc loc_opt (bvi_state_code u1) (bvi_state_code u2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP evaluate_code_mono) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP evaluate_code_mono) THEN
  UNDISCH_TAC `optimised_code loc loc_opt (bvi_state_code (s1:(num#C,FFI)bvi_state))
                 (bvi_state_code (s2:(C,FFI)bvi_state))` THEN
  REWRITE_TAC[optimised_code_def] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`arity:num`; `body:bvi_exp`; `body_wrap:bvi_exp`;
                        `body_work:bvi_exp`] THEN
  ASM_MESON_TAC[subspt_lookup]);;

let BVITMCAUX_no_mutcons_Cons = prove
 (`!tag xs. no_mutcons (bvi_Op (BlockOp (clos_Cons tag)) xs) <=>
            ALL (\x. no_mutcons x) xs`,
  REWRITE_TAC[no_mutcons_def; no_mutcons_op_def; distinctness "clos_op"; ETA_AX]);;

(* HOL4 [local] *)
let bvi_to_cb_aux_no_mutcons_lemma = prove
 (`(!n loc tag exp cb bs.
      bvi_to_cb_aux_sing n loc tag exp = SOME (bs,cb) /\
      no_mutcons (bvi_Op (BlockOp (clos_Cons tag)) [exp]) ==>
      ALL (\x. no_mutcons x) bs) /\
   (!n loc tag args cb bs.
      bvi_to_cb_aux n loc tag args = SOME (bs,cb) /\
      no_mutcons (bvi_Op (BlockOp (clos_Cons tag)) args) ==>
      ALL (\x. no_mutcons x) bs)`,
  REWRITE_TAC[BVITMCAUX_no_mutcons_Cons] THEN
  MATCH_MP_TAC bvi_to_cb_aux_ind THEN REPEAT CONJ_TAC THENL
   [(* Call *)
    REPEAT GEN_TAC THEN REWRITE_TAC[bvi_to_cb_aux_def; call_to_cb_def] THEN
    COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "option"] THEN
    MP_TAC(ISPEC `bind 0 (args:bvi_exp list)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `vs:num list` (X_CHOOSE_THEN `k:num` SUBST1_TAC)) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC))
      MP_TAC) THEN
    REWRITE_TAC[ALL; no_mutcons_def; ETA_AX] THEN SIMP_TAC[];
    (* Op *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[bvi_to_cb_aux_def; option_case_eq; sum_case_eq; pair_case_eq;
                COND_CASE_EQ; distinctness "option"; option_INJ; PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(fun dc -> MP_TAC(MATCH_MP ih dc))) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[BVIPAUX_TMC_dest_Cons_SOME] o
      check (BVITMCAUX_head_is "=" ) o check (fun th ->
        try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "bvi_tmc_dest_Cons"
        with Failure _ -> false)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL; no_mutcons_def; no_mutcons_op_def;
                                distinctness "clos_op"; ETA_AX]) THEN
    REWRITE_TAC[ETA_AX] THEN ASM_MESON_TAC[];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;
    (* [] *)
    REWRITE_TAC[bvi_to_cb_aux_def; option_INJ; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[ALL];
    (* [exp] *)
    REWRITE_TAC[bvi_to_cb_aux_def];
    (* CONS *)
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "iht") (LABEL_TAC "ihh")) THEN
    REPEAT GEN_TAC THEN
    DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs:num list` SUBST1_TAC)
                     (X_CHOOSE_THEN `cb':call_block` SUBST1_TAC)
      (ISPEC `cb:num list + call_block` (cases "sum")) THEN
    REWRITE_TAC[ALL] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `bs1:bvi_exp list` (X_CHOOSE_THEN `vs1:num list`
        (X_CHOOSE_THEN `bs2:bvi_exp list` (X_CHOOSE_THEN `vs2:num list`
          STRIP_ASSUME_TAC))) o MATCH_MP BVITMCAUX_cb_aux_cons_inl_inv) THEN
      REMOVE_THEN "ihh" (MP_TAC o SPECL [`bs2:bvi_exp list`; `vs2:num list`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`INL vs1:num list + call_block`; `bs1:bvi_exp list`]) THEN
      REMOVE_THEN "iht" (MP_TAC o SPECL [`INL vs2:num list + call_block`;
                                         `bs2:bvi_exp list`]) THEN
      ASM_REWRITE_TAC[ALL] THEN SIMP_TAC[ALL_APPEND];
      FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o
                    MATCH_MP BVITMCAUX_cb_aux_cons_inr_inv) THEN
      RVEQ_TAC THENL
       [REMOVE_THEN "ihh" (MP_TAC o SPECL [`bs2:bvi_exp list`; `vs2:num list`]) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPECL [`INR (CallBlock tag [] child []):num list + call_block`;
                                   `bs1:bvi_exp list`]) THEN
        REMOVE_THEN "iht" (MP_TAC o SPECL [`INL vs2:num list + call_block`;
                                           `bs2:bvi_exp list`]) THEN
        ASM_REWRITE_TAC[ALL] THEN SIMP_TAC[ALL_APPEND];
        REMOVE_THEN "iht" (MP_TAC o SPECL
          [`INR (CallBlock tag l child rr):num list + call_block`; `bs2:bvi_exp list`]) THEN
        ASM_REWRITE_TAC[ALL] THEN SIMP_TAC[ALL]]]] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_to_cb_aux_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "option"; option_INJ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[]);;

let bvi_to_cb_aux_no_mutcons = CONJUNCT2 bvi_to_cb_aux_no_mutcons_lemma;;

let bvi_to_cb_no_mutcons = prove
 (`!cb bs n loc x.
     bvi_to_cb n loc x = SOME (bs,cb) /\ no_mutcons x ==>
     ALL (\x. no_mutcons x) bs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_THEN MP_TAC o MATCH_MP bvi_to_cb_cases) THENL
   [DISCH_THEN(X_CHOOSE_THEN `tag:num` (X_CHOOSE_THEN `args:bvi_exp list`
      (X_CHOOSE_THEN `l:num list` (X_CHOOSE_THEN `child:call_block`
        (X_CHOOSE_THEN `rr:num list` (CONJUNCTS_THEN SUBST_ALL_TAC)))))) THEN
    MATCH_MP_TAC bvi_to_cb_aux_no_mutcons THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `loc:num`; `tag:num`; `args:bvi_exp list`;
      `INR (CallBlock tag l child rr):num list + call_block`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `bvi_to_cb n loc (bvi_Op (BlockOp (clos_Cons tag)) args) =
                 SOME (bs,CallBlock tag l child rr)` THEN
    REWRITE_TAC[bvi_to_cb_def; bvi_tmc_dest_Cons_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_case_eq; pair_case_eq; sum_case_eq; distinctness "option";
                option_INJ; PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `ts:num` (X_CHOOSE_THEN `args:bvi_exp list`
      (X_CHOOSE_THEN `vs:num list` (CONJUNCTS_THEN SUBST_ALL_TAC)))) THEN
    UNDISCH_TAC `bvi_to_cb n loc (bvi_Call ts (SOME loc) args NONE) =
                 SOME (bs,RCall ts vs)` THEN
    REWRITE_TAC[bvi_to_cb_def; call_to_cb_def] THEN
    MP_TAC(ISPEC `bind 0 (args:bvi_exp list)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `vs':num list` (X_CHOOSE_THEN `n':num` SUBST1_TAC)) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ; PAIR_EQ] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT1) THEN
    UNDISCH_TAC `no_mutcons (bvi_Call ts (SOME loc) args NONE)` THEN
    REWRITE_TAC[no_mutcons_def; ETA_AX] THEN CASE_REWRITE_TAC[] THEN SIMP_TAC[]]);;

let BVITMCAUX_tmc_hyps_def = cake_def
 `BVITMCAUX_tmc_hyps xs env1 (s:(num#C,FFI)bvi_state) r t opt f (s':(C,FFI)bvi_state)
                     env2 <=>
    bvi_evaluate (xs,env1,s) = (r,t) /\
    bvi_tmcProof_env_rel opt f env1 env2 /\ ALL (\x. no_mutcons x) xs /\
    bvi_tmcProof_state_rel f s s' /\
    (opt ==> LENGTH xs = 1) /\
    ~(r = Rerr (Rabort Rtype_error))`;;

let BVITMCAUX_tmc_concl_def = cake_def
 `BVITMCAUX_tmc_concl xs env1 (s:(num#C,FFI)bvi_state) r (t:(num#C,FFI)bvi_state) opt f
                      (s':(C,FFI)bvi_state) env2 loc <=>
    ?t' f' r'.
      bvi_evaluate (xs,env2,s') = (r',t') /\
      result_rel (ALL2 (bvi_tmcProof_v_rel f')) (eor_rel f') r r' /\
      bvi_tmcProof_state_rel f' t t' /\ f SUBMAP f' /\
      only_fresh f f' (bvi_state_refs s') /\
      holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t') {} /\
      holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t') /\
      !loc_opt.
        optimised_code loc loc_opt (bvi_state_code s) (bvi_state_code s') ==>
        (!wrap.
           LENGTH xs = 1 /\
           rewrite_wrapper loc loc_opt (LENGTH env1) (HD xs) = SOME wrap ==>
           ?t_wrap f_wrap r_wrap.
             bvi_evaluate ([wrap],env2,s') = (r_wrap,t_wrap) /\
             result_rel (ALL2 (bvi_tmcProof_v_rel f_wrap)) (eor_rel f_wrap) r r_wrap /\
             bvi_tmcProof_state_rel f_wrap t t_wrap /\ f SUBMAP f_wrap /\
             only_fresh f f_wrap (bvi_state_refs s') /\
             holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t_wrap) {} /\
             holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t_wrap)) /\
        (opt ==>
         !hole_ptr.
           (?c. hole_has_val f env1 env2 (bvi_state_refs s') c) /\
           hole_not_finalised (bvi_state_refs s') hole_ptr /\
           EL (LENGTH env1) env2 = bvl_RefPtr F hole_ptr ==>
           ?r_work f_work t_work.
             bvi_evaluate
               ([rewrite_worker loc loc_opt (LENGTH env1) (LENGTH env1 + 1)
                   (LENGTH env1) (HD xs)],env2,s') = (r_work,t_work) /\
             opt_res_rel f_work r r_work /\
             bvi_tmcProof_state_rel f_work t t_work /\ f SUBMAP f_work /\
             only_fresh f f_work (bvi_state_refs s') /\
             holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t_work)
               {hole_ptr} /\
             holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t_work) /\
             !res_v.
               r = Rval [res_v] ==>
               ?res_v'.
                 mb_rel f_work (bvi_state_refs s') (bvi_state_refs t_work \\ hole_ptr)
                   res_v res_v' /\
                 hole_has_val f env1 env2 (bvi_state_refs t_work) res_v')`;;

let BVITMCAUX_tmc_ih_def = cake_def
 `BVITMCAUX_tmc_ih xs (s:(num#C,FFI)bvi_state) <=>
    !xs' (s0:(num#C,FFI)bvi_state) env1 r t opt f (s':(C,FFI)bvi_state) env2 loc.
      (bvi_state_clock s0 < bvi_state_clock s \/
       (bvi_state_clock s0 <= bvi_state_clock s /\
        list_size bvi_exp_size xs' < list_size bvi_exp_size xs)) /\
      BVITMCAUX_tmc_hyps xs' env1 s0 r t opt f s' env2 ==>
      BVITMCAUX_tmc_concl xs' env1 s0 r t opt f s' env2 loc`;;

let BVITMCAUX_tmc_ih_hypothesis = prove
 (`!xs (s:(num#C,FFI)bvi_state).
     BVITMCAUX_tmc_ih xs s ==>
     !xs' (s'':(num#C,FFI)bvi_state). hypothesis xs' s'' (bvi_state_clock s)`,
  REWRITE_TAC[BVITMCAUX_tmc_ih_def; hypothesis_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`xs':bvi_exp list`; `s'':(num#C,FFI)bvi_state`;
    `env1':bvl_v list`; `r':(bvl_v list,exn_or_ret)result`; `t':(num#C,FFI)bvi_state`;
    `opt':bool`; `f':(num,num)fmap`; `s''':(C,FFI)bvi_state`; `env2':bvl_v list`;
    `loc':num`]) THEN
  ASM_REWRITE_TAC[BVITMCAUX_tmc_hyps_def; BVITMCAUX_tmc_concl_def]);;

let BVITMCAUX_tmc_nil = prove
 (`!env1 (s:(num#C,FFI)bvi_state) r t opt f (s':(C,FFI)bvi_state) env2 loc.
     BVITMCAUX_tmc_hyps [] env1 s r t opt f s' env2 ==>
     BVITMCAUX_tmc_concl [] env1 s r t opt f s' env2 loc`,
  REWRITE_TAC[BVITMCAUX_tmc_hyps_def; BVITMCAUX_tmc_concl_def; bvi_evaluate_def;
              PAIR_EQ; LENGTH; ARITH_RULE `~(0 = 1)`] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`s':(C,FFI)bvi_state`; `f:(num,num)fmap`;
                        `Rval []:(bvl_v list,exn_or_ret)result`] THEN
  ASM_REWRITE_TAC[result_rel_def; ALL2; SUBMAP_REFL; only_fresh_refl;
                  holes_unchanged_except_refl; holes_still_not_finalised_refl]);;

let BVITMCAUX_tmc_wf = prove
 (`(!xs (s:(num#C,FFI)bvi_state) env1 r t opt f (s':(C,FFI)bvi_state) env2 loc.
      BVITMCAUX_tmc_ih xs s /\ BVITMCAUX_tmc_hyps xs env1 s r t opt f s' env2 ==>
      BVITMCAUX_tmc_concl xs env1 s r t opt f s' env2 loc) ==>
   !xs (s:(num#C,FFI)bvi_state) env1 r t opt f (s':(C,FFI)bvi_state) env2 loc.
      BVITMCAUX_tmc_hyps xs env1 s r t opt f s' env2 ==>
      BVITMCAUX_tmc_concl xs env1 s r t opt f s' env2 loc`,
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!n xs (s:(num#C,FFI)bvi_state) env1 r t opt f (s':(C,FFI)bvi_state) env2 loc.
      n = (bvi_state_clock s,list_size bvi_exp_size xs) /\
      BVITMCAUX_tmc_hyps xs env1 s r t opt f s' env2 ==>
      BVITMCAUX_tmc_concl xs env1 s r t opt f s' env2 loc`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC(REWRITE_RULE[WF_IND] WF_I_I) THEN
  X_GEN_TAC `n:num#num` THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[BVITMCAUX_tmc_ih_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(bvi_state_clock (s0:(num#C,FFI)bvi_state),
                                list_size bvi_exp_size xs')` o
    check (fun th -> is_forall (concl th) &&
      type_of(fst(dest_forall(concl th))) = `:num#num`)) THEN
  ASM_REWRITE_TAC[LEX_THM; measure_THM; I_THM] THEN
  TRY(ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let BVITMCAUX_worker_fill = prove
 (`!e f f' env1 env2 (s:(num#C,FFI)bvi_state) t (s':(C,FFI)bvi_state) t' r r' hole_ptr.
     bvi_evaluate ([e],env1,s) = (r,t) /\ bvi_evaluate ([e],env2,s') = (r',t') /\
     bvi_tmcProof_env_rel T f env1 env2 /\ bvi_tmcProof_state_rel f s s' /\
     f SUBMAP f' /\
     result_rel (ALL2 (bvi_tmcProof_v_rel f')) (eor_rel f') r r' /\
     holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t') {} /\
     holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t') /\
     only_fresh f f' (bvi_state_refs s') /\ bvi_tmcProof_state_rel f' t t' /\
     (?c. hole_has_val f env1 env2 (bvi_state_refs s') c) /\
     hole_not_finalised (bvi_state_refs s') hole_ptr /\
     EL (LENGTH env1) env2 = bvl_RefPtr F hole_ptr ==>
     ?r_work f_work t_work.
       bvi_evaluate ([fill_hole (LENGTH env1) (LENGTH env1 + 1) e],env2,s') =
         (r_work,t_work) /\
       opt_res_rel f_work r r_work /\
       bvi_tmcProof_state_rel f_work t t_work /\ f SUBMAP f_work /\
       only_fresh f f_work (bvi_state_refs s') /\
       holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t_work) {hole_ptr} /\
       holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t_work) /\
       !res_v. r = Rval [res_v] ==>
         ?res_v'.
           mb_rel f_work (bvi_state_refs s') (bvi_state_refs t_work \\ hole_ptr)
             res_v res_v' /\
           hole_has_val f env1 env2 (bvi_state_refs t_work) res_v'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e:bvi_exp`; `f:(num,num)fmap`; `f':(num,num)fmap`;
    `env1:bvl_v list`; `env2:bvl_v list`; `s:(num#C,FFI)bvi_state`;
    `t:(num#C,FFI)bvi_state`; `s':(C,FFI)bvi_state`; `t':(C,FFI)bvi_state`;
    `r:(bvl_v list,exn_or_ret)result`; `r':(bvl_v list,exn_or_ret)result`; `c:bvl_v`]
    (INST [`hole_ptr:num`,`hole_ptr:num`] evaluate_fill_hole)) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let BVITMCAUX_tmc_var = prove
 (`!v env1 (s:(num#C,FFI)bvi_state) r t opt f (s':(C,FFI)bvi_state) env2 loc.
     BVITMCAUX_tmc_hyps [bvi_Var v] env1 s r t opt f s' env2 ==>
     BVITMCAUX_tmc_concl [bvi_Var v] env1 s r t opt f s' env2 loc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITMCAUX_tmc_hyps_def; BVITMCAUX_tmc_concl_def] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `v < LENGTH (env1:bvl_v list)` ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_evaluate ([bvi_Var v],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[bvi_evaluate_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `bvi_evaluate ([bvi_Var v],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
  ASM_REWRITE_TAC[bvi_evaluate_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  SUBGOAL_THEN `v < LENGTH (env2:bvl_v list)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP bvi_tmcProof_env_rel_length) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`s':(C,FFI)bvi_state`; `f:(num,num)fmap`;
                        `Rval [EL v env2]:(bvl_v list,exn_or_ret)result`] THEN
  ASM_REWRITE_TAC[bvi_evaluate_def; result_rel_def; ALL2; SUBMAP_REFL; only_fresh_refl;
    holes_unchanged_except_refl; holes_still_not_finalised_refl; rewrite_wrapper_def;
    rewrite_worker_def; HD; distinctness "option"] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[env_rel_el_v_rel]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BVITMCAUX_worker_fill THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `s:(num#C,FFI)bvi_state`;
    `s':(C,FFI)bvi_state`; `Rval [EL v env2]:(bvl_v list,exn_or_ret)result`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o EQT_INTRO o check (fun th -> concl th = `opt:bool`)) THEN
  ASM_REWRITE_TAC[bvi_evaluate_def; result_rel_def; ALL2; SUBMAP_REFL; only_fresh_refl;
    holes_unchanged_except_refl; holes_still_not_finalised_refl] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[env_rel_el_v_rel]; ASM_MESON_TAC[]]);;

let BVITMCAUX_SIZE_TAC =
  REWRITE_TAC(list_size :: type_size_def "bvi_exp" :: size_aux_eqs "bvi_exp") THEN
  ARITH_TAC;;

let BVITMCAUX_tmc_raise = prove
 (`!x env1 (s:(num#C,FFI)bvi_state) r t opt f (s':(C,FFI)bvi_state) env2 loc.
     BVITMCAUX_tmc_ih [bvi_Raise x] s /\
     BVITMCAUX_tmc_hyps [bvi_Raise x] env1 s r t opt f s' env2 ==>
     BVITMCAUX_tmc_concl [bvi_Raise x] env1 s r t opt f s' env2 loc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITMCAUX_tmc_hyps_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `bvi_evaluate ([x],env1,s:(num#C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `rx:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `tx:(num#C,FFI)bvi_state` ASSUME_TAC)) THEN
  SUBGOAL_THEN `(?v. rx = Rval [v] /\ r = Rerr (Rraise (Exn v)) /\
                    t:(num#C,FFI)bvi_state = tx) \/
                (?e. rx = Rerr e /\ r:(bvl_v list,exn_or_ret)result = Rerr e /\
                     t:(num#C,FFI)bvi_state = tx)`
    (LABEL_TAC "res") THENL
   [UNDISCH_TAC `bvi_evaluate ([bvi_Raise x],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
    ASM_REWRITE_TAC[bvi_evaluate_def] THEN
    DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs:bvl_v list` SUBST_ALL_TAC)
      (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)
      (ISPEC `rx:(bvl_v list,exn_or_ret)result` (cases "result")) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THENL
     [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP evaluate_SING_IMP) THEN
      RVEQ_TAC THEN REWRITE_TAC[HD; injectivity "result"] THEN MESON_TAC[];
      RVEQ_TAC THEN MESON_TAC[]];
    ALL_TAC] THEN
  USE_THEN "ih" (MP_TAC o SPECL [`[x:bvi_exp]`; `s:(num#C,FFI)bvi_state`;
    `env1:bvl_v list`; `rx:(bvl_v list,exn_or_ret)result`; `tx:(num#C,FFI)bvi_state`;
    `F`; `f:(num,num)fmap`; `s':(C,FFI)bvi_state`; `env2:bvl_v list`; `loc:num`] o
    REWRITE_RULE[BVITMCAUX_tmc_ih_def]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LE_REFL; BVITMCAUX_tmc_hyps_def] THEN REPEAT CONJ_TAC THENL
     [DISJ2_TAC THEN BVITMCAUX_SIZE_TAC;
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[env_rel_relax_opt];
      UNDISCH_TAC `ALL (\x. no_mutcons x) [bvi_Raise x]` THEN
      REWRITE_TAC[ALL; no_mutcons_def];
      ASM_REWRITE_TAC[];
      REMOVE_THEN "res" MP_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[distinctness "result"] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[BVITMCAUX_tmc_concl_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `tx':(C,FFI)bvi_state` (X_CHOOSE_THEN `f':(num,num)fmap`
    (X_CHOOSE_THEN `rx':(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
  REMOVE_THEN "res" (DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:bvl_v` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `e:(exn_or_ret)error_result` STRIP_ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    (lhs (concl th) = `rx:(bvl_v list,exn_or_ret)result` ||
     lhs (concl th) = `r:(bvl_v list,exn_or_ret)result` ||
     lhs (concl th) = `t:(num#C,FFI)bvi_state`)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[result_rel_Rval; result_rel_Rerr1; LIST_REL_CONS1;
                              LIST_REL_NIL]) THEN
  REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THEN
  REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[HD] THEN
  MAP_EVERY EXISTS_TAC [`tx':(C,FFI)bvi_state`; `f':(num,num)fmap`] THEN
  REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
  ASM_REWRITE_TAC[result_rel_def; exc_rel_def; eor_rel_def; rewrite_wrapper_def;
                  rewrite_worker_def; HD; distinctness "option"] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[bvi_evaluate_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[HD; PAIR_EQ] THEN
  REWRITE_TAC[MESON[] `!(a:A) (b:B) (P:A->C->B->bool).
                         (?x z y. (a = x /\ b = y) /\ P x z y) <=> (?z. P a z b)`] THEN
  EXISTS_TAC `f':(num,num)fmap` THEN
  ASM_REWRITE_TAC[BVITMCAUX_opt_res_rel_thm; distinctness "result"; injectivity "result"] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1; exc_rel_def; eor_rel_def] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC holes_unchanged_except_subset THEN EXISTS_TAC `{}:num->bool` THEN
  ASM_REWRITE_TAC[EMPTY_SUBSET]);;

let BVITMCAUX_tmc_plain = prove
 (`!e env1 (s:(num#C,FFI)bvi_state) r t opt f (s':(C,FFI)bvi_state) env2 loc.
     BVITMCAUX_tmc_hyps [e] env1 s r t opt f s' env2 /\
     (!loc_opt. rewrite_wrapper loc loc_opt (LENGTH env1) e = NONE) /\
     (!loc_opt. rewrite_worker loc loc_opt (LENGTH env1) (LENGTH env1 + 1) (LENGTH env1) e =
                fill_hole (LENGTH env1) (LENGTH env1 + 1) e) /\
     (?t' f' r'.
        bvi_evaluate ([e],env2,s') = (r',t') /\
        result_rel (ALL2 (bvi_tmcProof_v_rel f')) (eor_rel f') r r' /\
        bvi_tmcProof_state_rel f' t t' /\ f SUBMAP f' /\
        only_fresh f f' (bvi_state_refs s') /\
        holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t') {} /\
        holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t')) ==>
     BVITMCAUX_tmc_concl [e] env1 s r t opt f s' env2 loc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITMCAUX_tmc_hyps_def; BVITMCAUX_tmc_concl_def] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t':(C,FFI)bvi_state`; `f':(num,num)fmap`;
                        `r':(bvl_v list,exn_or_ret)result`] THEN
  ASM_REWRITE_TAC[HD; distinctness "option"] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BVITMCAUX_worker_fill THEN
  MAP_EVERY EXISTS_TAC [`f':(num,num)fmap`; `s:(num#C,FFI)bvi_state`;
    `t':(C,FFI)bvi_state`; `r':(bvl_v list,exn_or_ret)result`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o EQT_INTRO o check (fun th -> concl th = `opt:bool`)) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let BVITMCAUX_tmc_return = prove
 (`!es env1 (s:(num#C,FFI)bvi_state) r t opt f (s':(C,FFI)bvi_state) env2 loc.
     BVITMCAUX_tmc_ih [bvi_Return es] s /\
     BVITMCAUX_tmc_hyps [bvi_Return es] env1 s r t opt f s' env2 ==>
     BVITMCAUX_tmc_concl [bvi_Return es] env1 s r t opt f s' env2 loc`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") ASSUME_TAC) THEN
  MATCH_MP_TAC BVITMCAUX_tmc_plain THEN ASM_REWRITE_TAC[rewrite_wrapper_def;
    rewrite_worker_def] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[BVITMCAUX_tmc_hyps_def]) THEN
  MP_TAC(ISPEC `bvi_evaluate (es,env1,s:(num#C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `rx:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `tx:(num#C,FFI)bvi_state` ASSUME_TAC)) THEN
  SUBGOAL_THEN `(?vs. rx = Rval vs /\ r = Rerr (Rraise (Ret vs)) /\
                      t:(num#C,FFI)bvi_state = tx) \/
                (?e. rx = Rerr e /\ r:(bvl_v list,exn_or_ret)result = Rerr e /\
                     t:(num#C,FFI)bvi_state = tx)`
    (LABEL_TAC "res") THENL
   [UNDISCH_TAC `bvi_evaluate ([bvi_Return es],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
    ASM_REWRITE_TAC[bvi_evaluate_def] THEN
    DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs:bvl_v list` SUBST_ALL_TAC)
      (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)
      (ISPEC `rx:(bvl_v list,exn_or_ret)result` (cases "result")) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "ih" (MP_TAC o SPECL [`es:bvi_exp list`; `s:(num#C,FFI)bvi_state`;
    `env1:bvl_v list`; `rx:(bvl_v list,exn_or_ret)result`; `tx:(num#C,FFI)bvi_state`;
    `F`; `f:(num,num)fmap`; `s':(C,FFI)bvi_state`; `env2:bvl_v list`; `loc:num`] o
    REWRITE_RULE[BVITMCAUX_tmc_ih_def]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LE_REFL; BVITMCAUX_tmc_hyps_def] THEN REPEAT CONJ_TAC THENL
     [DISJ2_TAC THEN BVITMCAUX_SIZE_TAC;
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[env_rel_relax_opt];
      UNDISCH_TAC `ALL (\x. no_mutcons x) [bvi_Return es]` THEN
      REWRITE_TAC[ALL; no_mutcons_def; ETA_AX] THEN SIMP_TAC[];
      ASM_REWRITE_TAC[];
      REMOVE_THEN "res" MP_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[distinctness "result"] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[BVITMCAUX_tmc_concl_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `tx':(C,FFI)bvi_state` (X_CHOOSE_THEN `f':(num,num)fmap`
    (X_CHOOSE_THEN `rx':(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`tx':(C,FFI)bvi_state`; `f':(num,num)fmap`] THEN
  REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "res" (DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs:bvl_v list` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `e:(exn_or_ret)error_result` STRIP_ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    (lhs (concl th) = `rx:(bvl_v list,exn_or_ret)result` ||
     lhs (concl th) = `r:(bvl_v list,exn_or_ret)result` ||
     lhs (concl th) = `t:(num#C,FFI)bvi_state`)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[result_rel_Rval; result_rel_Rerr1]) THEN
  REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
  ASM_REWRITE_TAC[result_rel_def; exc_rel_def; eor_rel_def]);;

let BVITMCAUX_tmc_op = prove
 (`!op args env1 (s:(num#C,FFI)bvi_state) r t opt f (s':(C,FFI)bvi_state) env2 loc.
     BVITMCAUX_tmc_ih [bvi_Op op args] s /\
     BVITMCAUX_tmc_hyps [bvi_Op op args] env1 s r t opt f s' env2 /\
     bvi_to_cb (LENGTH env1) loc (bvi_Op op args) = NONE ==>
     BVITMCAUX_tmc_concl [bvi_Op op args] env1 s r t opt f s' env2 loc`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MATCH_MP_TAC BVITMCAUX_tmc_plain THEN
  ASM_REWRITE_TAC[rewrite_wrapper_def; rewrite_worker_def] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[BVITMCAUX_tmc_hyps_def] o
    check (BVITMCAUX_head_is "BVITMCAUX_tmc_hyps")) THEN
  MP_TAC(ISPEC `bvi_evaluate (args,env1,s:(num#C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ra:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `ta:(num#C,FFI)bvi_state` ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(ra = Rerr (Rabort Rtype_error):(bvl_v list,exn_or_ret)result)`
    ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `bvi_evaluate ([bvi_Op op args],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
    ASM_REWRITE_TAC[bvi_evaluate_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "ih" (MP_TAC o SPECL [`args:bvi_exp list`; `s:(num#C,FFI)bvi_state`;
    `env1:bvl_v list`; `ra:(bvl_v list,exn_or_ret)result`; `ta:(num#C,FFI)bvi_state`;
    `F`; `f:(num,num)fmap`; `s':(C,FFI)bvi_state`; `env2:bvl_v list`; `loc:num`] o
    REWRITE_RULE[BVITMCAUX_tmc_ih_def]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LE_REFL; BVITMCAUX_tmc_hyps_def] THEN REPEAT CONJ_TAC THENL
     [DISJ2_TAC THEN BVITMCAUX_SIZE_TAC;
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[env_rel_relax_opt];
      UNDISCH_TAC `ALL (\x. no_mutcons x) [bvi_Op op args]` THEN
      REWRITE_TAC[ALL; no_mutcons_def; ETA_AX] THEN SIMP_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[BVITMCAUX_tmc_concl_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `ta':(C,FFI)bvi_state` (X_CHOOSE_THEN `f':(num,num)fmap`
    (X_CHOOSE_THEN `ra':(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `bvi_evaluate ([bvi_Op op args],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
  REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs:bvl_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)
    (ISPEC `ra:(bvl_v list,exn_or_ret)result` (cases "result")) THEN
  CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[result_rel_Rval; result_rel_Rerr1]) THEN
  REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`ta':(C,FFI)bvi_state`; `f':(num,num)fmap`] THEN
    ASM_REWRITE_TAC[PAIR_EQ; UNWIND_THM1; result_rel_def]] THEN
  MP_TAC(ISPEC `bvi_do_app op (REVERSE vs) (ta:(num#C,FFI)bvi_state)` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `vt:bvl_v#(num#C,FFI)bvi_state`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))
    (X_CHOOSE_THEN `e:(exn_or_ret)error_result` (fun th -> SUBST1_TAC th THEN
      ASSUME_TAC th))) THEN
  CASE_REWRITE_TAC[] THENL
   [MP_TAC(ISPEC `vt:bvl_v#(num#C,FFI)bvi_state` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:bvl_v` (X_CHOOSE_THEN `t2:(num#C,FFI)bvi_state`
      SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MP_TAC(ISPECL [`f':(num,num)fmap`; `op:clos_op`; `REVERSE vs:bvl_v list`;
      `REVERSE v':bvl_v list`; `ta:(num#C,FFI)bvi_state`; `ta':(C,FFI)bvi_state`;
      `t2:(num#C,FFI)bvi_state`; `v:bvl_v`] do_app_op_rel) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `ALL (\x. no_mutcons x) [bvi_Op op args]` THEN
        REWRITE_TAC[ALL; no_mutcons_def] THEN SIMP_TAC[];
        ONCE_REWRITE_TAC[GSYM list_rel_reverse] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f'':(num,num)fmap` (X_CHOOSE_THEN `v2:bvl_v`
      (X_CHOOSE_THEN `t2':(C,FFI)bvi_state` STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`t2':(C,FFI)bvi_state`; `f'':(num,num)fmap`;
                          `Rval [v2]:(bvl_v list,exn_or_ret)result`] THEN
    ASM_REWRITE_TAC[result_rel_def; ALL2] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SUBMAP_TRANS];
      MATCH_MP_TAC only_fresh_trans THEN
      MAP_EVERY EXISTS_TAC [`f':(num,num)fmap`; `bvi_state_refs (ta':(C,FFI)bvi_state)`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[bvi_tmcProof_evaluate_refs_SUBSET];
      MATCH_MP_TAC holes_unchanged_except_trans THEN
      MAP_EVERY EXISTS_TAC [`f':(num,num)fmap`; `bvi_state_refs (ta':(C,FFI)bvi_state)`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC holes_still_not_finalised_trans THEN
      MAP_EVERY EXISTS_TAC [`f':(num,num)fmap`; `bvi_state_refs (ta':(C,FFI)bvi_state)`] THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP bvi_do_app_err o check (fun th -> is_eq (concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "bvi_do_app"
       with Failure _ -> false))) THEN
    STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    RVEQ_TAC THEN
    SUBGOAL_THEN `ALL2 (bvi_tmcProof_v_rel f') (REVERSE vs) (REVERSE v')` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[GSYM list_rel_reverse] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 -> FIRST_ASSUM(fun th3 ->
      ASSUME_TAC (MATCH_MP do_app_op_err_rel (CONJ th1 (CONJ th2 th3)))))) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`ta':(C,FFI)bvi_state`; `f':(num,num)fmap`] THEN
    ASM_REWRITE_TAC[PAIR_EQ; UNWIND_THM1; result_rel_def; exc_rel_def]]);;

let BVITMCAUX_tmc_tick = prove
 (`!x env1 (s:(num#C,FFI)bvi_state) r t opt f (s':(C,FFI)bvi_state) env2 loc.
     BVITMCAUX_tmc_ih [bvi_Tick x] s /\
     BVITMCAUX_tmc_hyps [bvi_Tick x] env1 s r t opt f s' env2 ==>
     BVITMCAUX_tmc_concl [bvi_Tick x] env1 s r t opt f s' env2 loc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITMCAUX_tmc_hyps_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `bvi_state_clock (s':(C,FFI)bvi_state) =
                bvi_state_clock (s:(num#C,FFI)bvi_state)` ASSUME_TAC THENL
   [ASM_MESON_TAC[bvi_tmcProof_state_rel_def]; ALL_TAC] THEN
  REWRITE_TAC[BVITMCAUX_tmc_concl_def; rewrite_wrapper_def; rewrite_worker_def; HD;
              LENGTH; OPTION_MAP_EQ_SOME; ARITH_RULE `SUC 0 = 1`] THEN
  ASM_CASES_TAC `bvi_state_clock (s:(num#C,FFI)bvi_state) = 0` THENL
   [UNDISCH_TAC `bvi_evaluate ([bvi_Tick x],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
    ASM_REWRITE_TAC[bvi_evaluate_def; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`s':(C,FFI)bvi_state`; `f:(num,num)fmap`;
      `Rerr (Rabort Rtimeout_error):(bvl_v list,exn_or_ret)result`] THEN
    ASM_REWRITE_TAC[result_rel_def; exc_rel_def; SUBMAP_REFL; only_fresh_refl;
      holes_unchanged_except_refl; holes_still_not_finalised_refl] THEN
    REPEAT STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`s':(C,FFI)bvi_state`; `f:(num,num)fmap`;
        `Rerr (Rabort Rtimeout_error):(bvl_v list,exn_or_ret)result`] THEN
      ASM_REWRITE_TAC[bvi_evaluate_def; result_rel_def; exc_rel_def; SUBMAP_REFL;
        only_fresh_refl; holes_unchanged_except_refl; holes_still_not_finalised_refl];
      MAP_EVERY EXISTS_TAC [`Rerr (Rabort Rtimeout_error):(bvl_v list,exn_or_ret)result`;
        `f:(num,num)fmap`; `s':(C,FFI)bvi_state`] THEN
      ASM_REWRITE_TAC[bvi_evaluate_def; BVITMCAUX_opt_res_rel_thm; exc_rel_def;
        SUBMAP_REFL; only_fresh_refl; holes_unchanged_except_refl;
        holes_still_not_finalised_refl; distinctness "result"; injectivity "result"] THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1; exc_rel_def]];
    ALL_TAC] THEN
  UNDISCH_TAC `bvi_evaluate ([bvi_Tick x],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
  ASM_REWRITE_TAC[bvi_evaluate_def] THEN DISCH_TAC THEN
  USE_THEN "ih" (MP_TAC o SPECL [`[x:bvi_exp]`; `bvi_dec_clock 1 (s:(num#C,FFI)bvi_state)`;
    `env1:bvl_v list`; `r:(bvl_v list,exn_or_ret)result`; `t:(num#C,FFI)bvi_state`;
    `opt:bool`; `f:(num,num)fmap`; `bvi_dec_clock 1 (s':(C,FFI)bvi_state)`;
    `env2:bvl_v list`; `loc:num`] o REWRITE_RULE[BVITMCAUX_tmc_ih_def]) THEN
  REWRITE_TAC[BVITMCAUX_dec_clock_simps; BVITMCAUX_tmc_hyps_def; BVITMCAUX_tmc_concl_def;
              LENGTH; HD; ARITH_RULE `SUC 0 = 1`] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      UNDISCH_TAC `ALL (\x. no_mutcons x) [bvi_Tick x]` THEN
      REWRITE_TAC[ALL; no_mutcons_def];
      ASM_SIMP_TAC[BVITMCAUX_state_rel_dec_clock]];
    ALL_TAC] THEN
  REWRITE_TAC[bvi_dec_clock_def] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(C,FFI)bvi_state` (X_CHOOSE_THEN `f1:(num,num)fmap`
    (X_CHOOSE_THEN `r1:(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`t1:(C,FFI)bvi_state`; `f1:(num,num)fmap`;
                        `r1:(bvl_v list,exn_or_ret)result`] THEN
  ASM_REWRITE_TAC[bvi_evaluate_def; bvi_dec_clock_def] THEN
  X_GEN_TAC `loc_opt:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `loc_opt:num` o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "loc_opt" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `wrap:bvi_exp` THEN
    DISCH_THEN(X_CHOOSE_THEN `z:bvi_exp` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `wrap:bvi_exp`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:bvi_exp`) THEN
    ASM_REWRITE_TAC[bvi_evaluate_def; bvi_dec_clock_def];
    DISCH_TAC THEN X_GEN_TAC `hole_ptr:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `hole_ptr:num` o REWRITE_RULE[ASSUME `opt:bool`] o
      check (fun th -> is_imp (concl th) && lhand (concl th) = `opt:bool`)) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[bvi_evaluate_def; bvi_dec_clock_def] THEN ASM_REWRITE_TAC[]]);;

let BVITMCAUX_compose = prove
 (`!f f1 f2 (r0:(num,(bvl_v)bvl_ref)fmap) r1 r2 ch.
     f SUBMAP f1 /\ only_fresh f f1 r0 /\ holes_unchanged_except f r0 r1 {} /\
     holes_still_not_finalised f r0 r1 /\
     f1 SUBMAP f2 /\ only_fresh f1 f2 r1 /\ holes_unchanged_except f1 r1 r2 ch /\
     holes_still_not_finalised f1 r1 r2 /\
     FDOM r0 SUBSET FDOM r1 ==>
     f SUBMAP f2 /\ only_fresh f f2 r0 /\ holes_unchanged_except f r0 r2 ch /\
     holes_still_not_finalised f r0 r2`,
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[SUBMAP_TRANS];
    MATCH_MP_TAC only_fresh_trans THEN
    MAP_EVERY EXISTS_TAC [`f1:(num,num)fmap`; `r1:(num,(bvl_v)bvl_ref)fmap`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC holes_unchanged_except_trans THEN
    MAP_EVERY EXISTS_TAC [`f1:(num,num)fmap`; `r1:(num,(bvl_v)bvl_ref)fmap`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC holes_unchanged_except_subset THEN
    EXISTS_TAC `{}:num->bool` THEN ASM_REWRITE_TAC[EMPTY_SUBSET];
    MATCH_MP_TAC holes_still_not_finalised_trans THEN
    MAP_EVERY EXISTS_TAC [`f1:(num,num)fmap`; `r1:(num,(bvl_v)bvl_ref)fmap`] THEN
    ASM_REWRITE_TAC[]]);;

let BVITMCAUX_tmc_list = prove
 (`!x y xs env1 (s:(num#C,FFI)bvi_state) r t opt f (s':(C,FFI)bvi_state) env2 loc.
     BVITMCAUX_tmc_ih (CONS x (CONS y xs)) s /\
     BVITMCAUX_tmc_hyps (CONS x (CONS y xs)) env1 s r t opt f s' env2 ==>
     BVITMCAUX_tmc_concl (CONS x (CONS y xs)) env1 s r t opt f s' env2 loc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITMCAUX_tmc_hyps_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~opt` (SUBST_ALL_TAC o EQF_INTRO) THENL
   [UNDISCH_TAC `opt ==> LENGTH (CONS (x:bvi_exp) (CONS y xs)) = 1` THEN
    REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC (SUC n) = 1)`]; ALL_TAC] THEN
  REWRITE_TAC[BVITMCAUX_tmc_concl_def; LENGTH; ARITH_RULE `~(SUC (SUC n) = 1)`] THEN
  SUBGOAL_THEN `bvi_tmcProof_env_rel F f env1 env2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `bvi_evaluate ([x],env1,s:(num#C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `rx:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `tx:(num#C,FFI)bvi_state` ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(rx = Rerr (Rabort Rtype_error):(bvl_v list,exn_or_ret)result)`
    ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `bvi_evaluate (CONS x (CONS y xs),env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
    ASM_REWRITE_TAC[bvi_evaluate_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "ih" (MP_TAC o SPECL [`[x:bvi_exp]`; `s:(num#C,FFI)bvi_state`;
    `env1:bvl_v list`; `rx:(bvl_v list,exn_or_ret)result`; `tx:(num#C,FFI)bvi_state`;
    `F`; `f:(num,num)fmap`; `s':(C,FFI)bvi_state`; `env2:bvl_v list`; `loc:num`] o
    REWRITE_RULE[BVITMCAUX_tmc_ih_def]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LE_REFL; BVITMCAUX_tmc_hyps_def] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [DISJ2_TAC THEN BVITMCAUX_SIZE_TAC; ALL_TAC] THEN
    UNDISCH_TAC `ALL (\x. no_mutcons x) (CONS x (CONS y xs))` THEN
    REWRITE_TAC[ALL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[BVITMCAUX_tmc_concl_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `tx':(C,FFI)bvi_state` (X_CHOOSE_THEN `f1:(num,num)fmap`
    (X_CHOOSE_THEN `rx':(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `FDOM (bvi_state_refs (s':(C,FFI)bvi_state)) SUBSET
                FDOM (bvi_state_refs (tx':(C,FFI)bvi_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[bvi_tmcProof_evaluate_refs_SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `bvi_evaluate (CONS x (CONS y xs),env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
  REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `v1:bvl_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)
    (ISPEC `rx:(bvl_v list,exn_or_ret)result` (cases "result")) THEN
  CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[result_rel_Rval; result_rel_Rerr1]) THEN
  REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`tx':(C,FFI)bvi_state`; `f1:(num,num)fmap`] THEN
    ASM_REWRITE_TAC[PAIR_EQ; UNWIND_THM1; result_rel_def]] THEN
  MP_TAC(ISPEC `bvi_evaluate (CONS y xs,env1,tx:(num#C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ry:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `ty:(num#C,FFI)bvi_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(ry = Rerr (Rabort Rtype_error):(bvl_v list,exn_or_ret)result)`
    ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `(r:(bvl_v list,exn_or_ret)result,t:(num#C,FFI)bvi_state)`)) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "ih" (MP_TAC o SPECL [`CONS (y:bvi_exp) xs`; `tx:(num#C,FFI)bvi_state`;
    `env1:bvl_v list`; `ry:(bvl_v list,exn_or_ret)result`; `ty:(num#C,FFI)bvi_state`;
    `F`; `f1:(num,num)fmap`; `tx':(C,FFI)bvi_state`; `env2:bvl_v list`; `loc:num`] o
    REWRITE_RULE[BVITMCAUX_tmc_ih_def]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[BVITMCAUX_tmc_hyps_def] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [DISJ2_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[bvi_evaluate_clock]; BVITMCAUX_SIZE_TAC];
      MATCH_MP_TAC (GEN_ALL env_rel_submap) THEN EXISTS_TAC `f:(num,num)fmap` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `ALL (\x. no_mutcons x) (CONS x (CONS y xs))` THEN
      REWRITE_TAC[ALL] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[BVITMCAUX_tmc_concl_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `ty':(C,FFI)bvi_state` (X_CHOOSE_THEN `f2:(num,num)fmap`
    (X_CHOOSE_THEN `ry':(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`f:(num,num)fmap`; `f1:(num,num)fmap`; `f2:(num,num)fmap`;
    `bvi_state_refs (s':(C,FFI)bvi_state)`; `bvi_state_refs (tx':(C,FFI)bvi_state)`;
    `bvi_state_refs (ty':(C,FFI)bvi_state)`; `{}:num->bool`] BVITMCAUX_compose) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(r:(bvl_v list,exn_or_ret)result,t:(num#C,FFI)bvi_state)`)) THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `vy:bvl_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `ey:(exn_or_ret)error_result` SUBST_ALL_TAC)
    (ISPEC `ry:(bvl_v list,exn_or_ret)result` (cases "result")) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[result_rel_Rval; result_rel_Rerr1]) THEN
  REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`ty':(C,FFI)bvi_state`; `f2:(num,num)fmap`] THEN
  ASM_REWRITE_TAC[PAIR_EQ; UNWIND_THM1; result_rel_def] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP evaluate_SING_IMP o check (fun th ->
    is_eq (concl th) && free_in `env1:bvl_v list` (concl th) &&
    free_in `x:bvi_exp` (concl th))) THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
  REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[HD; ALL2] THEN
  MATCH_MP_TAC v_rel_submap THEN EXISTS_TAC `f1:(num,num)fmap` THEN
  ASM_REWRITE_TAC[]);;

let BVITMCAUX_hole_transport = prove
 (`!f f1 env1 env2 (r0:(num,(bvl_v)bvl_ref)fmap) r1 c hole_ptr.
     bvi_tmcProof_env_rel T f env1 env2 /\
     hole_has_val f env1 env2 r0 c /\ hole_not_finalised r0 hole_ptr /\
     EL (LENGTH env1) env2 = bvl_RefPtr F hole_ptr /\
     only_fresh f f1 r0 /\ holes_unchanged_except f r0 r1 {} /\
     holes_still_not_finalised f r0 r1 ==>
     hole_has_val f1 env1 env2 r1 c /\ hole_not_finalised r1 hole_ptr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `env2':bvl_v list` (X_CHOOSE_THEN `hp:num`
      (X_CHOOSE_THEN `hidx:int` STRIP_ASSUME_TAC)) o MATCH_MP env_rel_strip_extras) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC unchanged_hole_has_val THEN
    MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `r0:(num,(bvl_v)bvl_ref)fmap`;
                          `{}:num->bool`] THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY];
    UNDISCH_TAC `holes_still_not_finalised (f:(num,num)fmap)
                   (r0:(num,(bvl_v)bvl_ref)fmap) r1` THEN
    REWRITE_TAC[holes_still_not_finalised_def] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `hole_has_val f env1 env2 (r0:(num,(bvl_v)bvl_ref)fmap) c` THEN
    REWRITE_TAC[hole_has_val_def] THEN ASM_REWRITE_TAC[injectivity "bvl_v"] THEN
    MESON_TAC[]]);;

let BVITMCAUX_eval_If_Boolv = prove
 (`!x1 x2 x3 b env (s:(C,FFI)bvi_state) u.
     bvi_evaluate ([x1],env,s) = (Rval [bvl_Boolv b],u) ==>
     bvi_evaluate ([bvi_If x1 x2 x3],env,s) =
     bvi_evaluate ([if b then x2 else x3],env,u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD; bvl_Boolv_11] THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

let BVITMCAUX_tmc_if_branch = prove
 (`!x1 x2 x3 b env1 (s:(num#C,FFI)bvi_state) u r t opt f f1 (s':(C,FFI)bvi_state) u'
    env2 loc.
     bvi_evaluate ([x1],env1,s) = (Rval [bvl_Boolv b],u) /\
     bvi_evaluate ([x1],env2,s') = (Rval [bvl_Boolv b],u') /\
     bvi_tmcProof_env_rel opt f env1 env2 /\
     bvi_tmcProof_state_rel f1 u u' /\ f SUBMAP f1 /\
     only_fresh f f1 (bvi_state_refs s') /\
     holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs u') {} /\
     holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs u') /\
     BVITMCAUX_tmc_concl [if b then x2 else x3] env1 u r t opt f1 u' env2 loc ==>
     BVITMCAUX_tmc_concl [bvi_If x1 x2 x3] env1 s r t opt f s' env2 loc`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
        ASSUME_TAC MP_TAC)))))))) THEN
  REWRITE_TAC[BVITMCAUX_tmc_concl_def; HD; LENGTH; ARITH_RULE `SUC 0 = 1`] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(C,FFI)bvi_state` (X_CHOOSE_THEN `f2:(num,num)fmap`
    (X_CHOOSE_THEN `r1:(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(LABEL_TAC "br" o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "loc_opt" with Failure _ -> false)) THEN
  SUBGOAL_THEN `FDOM (bvi_state_refs (s':(C,FFI)bvi_state)) SUBSET
                FDOM (bvi_state_refs (u':(C,FFI)bvi_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[bvi_tmcProof_evaluate_refs_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:(num,num)fmap`; `f1:(num,num)fmap`; `f2:(num,num)fmap`;
    `bvi_state_refs (s':(C,FFI)bvi_state)`; `bvi_state_refs (u':(C,FFI)bvi_state)`;
    `bvi_state_refs (t1:(C,FFI)bvi_state)`; `{}:num->bool`] BVITMCAUX_compose) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t1:(C,FFI)bvi_state`; `f2:(num,num)fmap`;
                        `r1:(bvl_v list,exn_or_ret)result`] THEN
  SUBGOAL_THEN `bvi_evaluate ([bvi_If x1 x2 x3],env2,s':(C,FFI)bvi_state) =
                bvi_evaluate ([if b then x2 else x3],env2,u')` SUBST1_TAC THENL
   [MATCH_MP_TAC BVITMCAUX_eval_If_Boolv THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `loc_opt:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `optimised_code loc loc_opt (bvi_state_code (u:(num#C,FFI)bvi_state))
                  (bvi_state_code (u':(C,FFI)bvi_state))` ASSUME_TAC THENL
   [MATCH_MP_TAC evaluate_pres_opt_code THEN
    MAP_EVERY EXISTS_TAC [`s:(num#C,FFI)bvi_state`; `s':(C,FFI)bvi_state`;
      `[x1:bvi_exp]`; `env1:bvl_v list`; `env2:bvl_v list`;
      `Rval [bvl_Boolv b]:(bvl_v list,exn_or_ret)result`;
      `Rval [bvl_Boolv b]:(bvl_v list,exn_or_ret)result`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "br" (MP_TAC o SPEC `loc_opt:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "brw") (LABEL_TAC "brk")) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `wrap:bvi_exp` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `?w2 w3. wrap = bvi_If x1 w2 w3 /\
              (rewrite_wrapper loc loc_opt (LENGTH (env1:bvl_v list))
                 (if b then x2 else x3) = SOME (if b then w2 else w3) \/
               (if b then w2 else w3) = (if b then x2 else x3))`
      (X_CHOOSE_THEN `w2:bvi_exp` (X_CHOOSE_THEN `w3:bvi_exp`
         (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THENL
     [BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[] THENL
       [FIRST_ASSUM(MP_TAC o MATCH_MP wrapper_strip_if_then);
        FIRST_ASSUM(MP_TAC o MATCH_MP wrapper_strip_if_else)] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `bvi_evaluate ([bvi_If x1 w2 w3],env2,s':(C,FFI)bvi_state) =
                  bvi_evaluate ([if b then w2 else w3],env2,u')` SUBST1_TAC THENL
     [MATCH_MP_TAC BVITMCAUX_eval_If_Boolv THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [REMOVE_THEN "brw" (MP_TAC o SPEC `if b then w2 else w3:bvi_exp`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `tw:(C,FFI)bvi_state` (X_CHOOSE_THEN `fw:(num,num)fmap`
        (X_CHOOSE_THEN `rw:(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
      MP_TAC(ISPECL [`f:(num,num)fmap`; `f1:(num,num)fmap`; `fw:(num,num)fmap`;
        `bvi_state_refs (s':(C,FFI)bvi_state)`; `bvi_state_refs (u':(C,FFI)bvi_state)`;
        `bvi_state_refs (tw:(C,FFI)bvi_state)`; `{}:num->bool`] BVITMCAUX_compose) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`tw:(C,FFI)bvi_state`; `fw:(num,num)fmap`;
                            `rw:(bvl_v list,exn_or_ret)result`] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`t1:(C,FFI)bvi_state`; `f2:(num,num)fmap`;
                            `r1:(bvl_v list,exn_or_ret)result`] THEN
      ASM_REWRITE_TAC[]];
    DISCH_TAC THEN X_GEN_TAC `hole_ptr:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o EQT_INTRO o check (fun th -> concl th = `opt:bool`)) THEN
    REWRITE_TAC[rewrite_worker_def; LET_DEF; LET_END_DEF] THEN
    W(fun (_,w) ->
      SUBGOAL_THEN (mk_eq(`bvi_evaluate ([bvi_If x1 (rewrite_worker loc loc_opt
          (LENGTH (env1:bvl_v list)) (LENGTH env1 + 1) (LENGTH env1) x2)
          (rewrite_worker loc loc_opt (LENGTH env1) (LENGTH env1 + 1) (LENGTH env1) x3)],
          env2,s':(C,FFI)bvi_state)`,
          `bvi_evaluate ([rewrite_worker loc loc_opt (LENGTH (env1:bvl_v list))
             (LENGTH env1 + 1) (LENGTH env1) (if b then x2 else x3)],env2,
             u':(C,FFI)bvi_state)`)) SUBST1_TAC) THENL
     [MP_TAC(ISPECL [`x1:bvi_exp`;
        `rewrite_worker loc loc_opt (LENGTH (env1:bvl_v list)) (LENGTH env1 + 1)
           (LENGTH env1) x2`;
        `rewrite_worker loc loc_opt (LENGTH (env1:bvl_v list)) (LENGTH env1 + 1)
           (LENGTH env1) x3`;
        `b:bool`; `env2:bvl_v list`; `s':(C,FFI)bvi_state`; `u':(C,FFI)bvi_state`]
        BVITMCAUX_eval_If_Boolv) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`f:(num,num)fmap`; `f1:(num,num)fmap`; `env1:bvl_v list`;
      `env2:bvl_v list`; `bvi_state_refs (s':(C,FFI)bvi_state)`;
      `bvi_state_refs (u':(C,FFI)bvi_state)`; `c:bvl_v`; `hole_ptr:num`]
      BVITMCAUX_hole_transport) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REMOVE_THEN "brk" (MP_TAC o SPEC `hole_ptr:num` o REWRITE_RULE[]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `rw:(bvl_v list,exn_or_ret)result`
      (X_CHOOSE_THEN `fw:(num,num)fmap` (X_CHOOSE_THEN `tw:(C,FFI)bvi_state`
        STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`f:(num,num)fmap`; `f1:(num,num)fmap`; `fw:(num,num)fmap`;
      `bvi_state_refs (s':(C,FFI)bvi_state)`; `bvi_state_refs (u':(C,FFI)bvi_state)`;
      `bvi_state_refs (tw:(C,FFI)bvi_state)`; `{hole_ptr:num}`] BVITMCAUX_compose) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`rw:(bvl_v list,exn_or_ret)result`; `fw:(num,num)fmap`;
                          `tw:(C,FFI)bvi_state`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `res_v:bvl_v` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `res_v:bvl_v` o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "res_v" with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `res_v':bvl_v` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `res_v':bvl_v` THEN CONJ_TAC THENL
     [MATCH_MP_TAC mb_rel_refs_old_subset THEN
      EXISTS_TAC `bvi_state_refs (u':(C,FFI)bvi_state)` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC hole_has_val_submap THEN EXISTS_TAC `f1:(num,num)fmap` THEN
      ASM_REWRITE_TAC[]]]);;

let BVITMCAUX_eval_If_Rerr = prove
 (`!x1 env (s:(C,FFI)bvi_state) e u.
     bvi_evaluate ([x1],env,s) = (Rerr e,u) ==>
     !x2 x3. bvi_evaluate ([bvi_If x1 x2 x3],env,s) = (Rerr e,u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

let BVITMCAUX_tmc_if = prove
 (`!x1 x2 x3 env1 (s:(num#C,FFI)bvi_state) r t opt f (s':(C,FFI)bvi_state) env2 loc.
     BVITMCAUX_tmc_ih [bvi_If x1 x2 x3] s /\
     BVITMCAUX_tmc_hyps [bvi_If x1 x2 x3] env1 s r t opt f s' env2 ==>
     BVITMCAUX_tmc_concl [bvi_If x1 x2 x3] env1 s r t opt f s' env2 loc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITMCAUX_tmc_hyps_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `bvi_evaluate ([x1],env1,s:(num#C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `u:(num#C,FFI)bvi_state` ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(bvl_v list,exn_or_ret)result)`
    ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `bvi_evaluate ([bvi_If x1 x2 x3],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_If_Rerr th]) o
      check (fun th -> is_eq (concl th) && free_in `env1:bvl_v list` (concl th) &&
                       free_in `x1:bvi_exp` (concl th) &&
                       not (free_in `x2:bvi_exp` (concl th)))) THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "ih" (MP_TAC o SPECL [`[x1:bvi_exp]`; `s:(num#C,FFI)bvi_state`;
    `env1:bvl_v list`; `r1:(bvl_v list,exn_or_ret)result`; `u:(num#C,FFI)bvi_state`;
    `F`; `f:(num,num)fmap`; `s':(C,FFI)bvi_state`; `env2:bvl_v list`; `loc:num`] o
    REWRITE_RULE[BVITMCAUX_tmc_ih_def]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LE_REFL; BVITMCAUX_tmc_hyps_def] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [DISJ2_TAC THEN BVITMCAUX_SIZE_TAC;
      ASM_MESON_TAC[env_rel_relax_opt];
      UNDISCH_TAC `ALL (\x. no_mutcons x) [bvi_If x1 x2 x3]` THEN
      REWRITE_TAC[ALL; no_mutcons_def] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':(C,FFI)bvi_state` (X_CHOOSE_THEN `f1:(num,num)fmap`
    (X_CHOOSE_THEN `r1':(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC)) o
    REWRITE_RULE[BVITMCAUX_tmc_concl_def]) THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs:bvl_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)
    (ISPEC `r1:(bvl_v list,exn_or_ret)result` (cases "result")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[result_rel_Rval; result_rel_Rerr1]) THEN
  REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP evaluate_SING_IMP o check (fun th ->
      is_eq (concl th) && free_in `env1:bvl_v list` (concl th) &&
      free_in `x1:bvi_exp` (concl th) && not (free_in `x2:bvi_exp` (concl th)))) THEN
    RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
    REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
    RVEQ_TAC THEN
    ASM_CASES_TAC `?b. w = bvl_Boolv b` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `b:bool` SUBST_ALL_TAC) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[BVITMCAUX_v_rel_Boolv]) THEN RVEQ_TAC THEN
      MATCH_MP_TAC BVITMCAUX_tmc_if_branch THEN
      MAP_EVERY EXISTS_TAC [`b:bool`; `u:(num#C,FFI)bvi_state`; `f1:(num,num)fmap`;
                            `u':(C,FFI)bvi_state`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `bvi_evaluate ([if b then x2 else x3],env1,u:(num#C,FFI)bvi_state) =
                    (r,t)` ASSUME_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
          rhs (concl th) = `(r:(bvl_v list,exn_or_ret)result,t:(num#C,FFI)bvi_state)`)) THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC BVITMCAUX_eval_If_Boolv THEN
        ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "ih" (MP_TAC o SPECL [`[if b then x2 else x3:bvi_exp]`;
        `u:(num#C,FFI)bvi_state`; `env1:bvl_v list`; `r:(bvl_v list,exn_or_ret)result`;
        `t:(num#C,FFI)bvi_state`; `opt:bool`; `f1:(num,num)fmap`;
        `u':(C,FFI)bvi_state`; `env2:bvl_v list`; `loc:num`] o
        REWRITE_RULE[BVITMCAUX_tmc_ih_def]) THEN
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[BVITMCAUX_tmc_hyps_def] THEN
      ASM_REWRITE_TAC[LENGTH; ARITH_RULE `SUC 0 = 1`] THEN REPEAT CONJ_TAC THENL
       [DISJ2_TAC THEN CONJ_TAC THENL
         [ASM_MESON_TAC[bvi_evaluate_clock];
          BOOL_CASES_TAC `b:bool` THEN BVITMCAUX_SIZE_TAC];
        MATCH_MP_TAC (GEN_ALL env_rel_submap) THEN EXISTS_TAC `f:(num,num)fmap` THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `ALL (\x. no_mutcons x) [bvi_If x1 x2 x3]` THEN
        REWRITE_TAC[ALL; no_mutcons_def] THEN BOOL_CASES_TAC `b:bool` THEN
        SIMP_TAC[]];
      UNDISCH_TAC `bvi_evaluate ([bvi_If x1 x2 x3],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
      REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[HD] THEN
      SUBGOAL_THEN `~(bvl_Boolv T = w) /\ ~(bvl_Boolv F = w)` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]];
    (* condition raised *)
    REWRITE_TAC[BVITMCAUX_tmc_concl_def] THEN
    UNDISCH_TAC `bvi_evaluate ([bvi_If x1 x2 x3],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_If_Rerr th]) o
      check (fun th -> is_eq (concl th) && free_in `env1:bvl_v list` (concl th) &&
                       free_in `x1:bvi_exp` (concl th) &&
                       not (free_in `x2:bvi_exp` (concl th)))) THEN
    REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_If_Rerr th]) o
      check (fun th -> is_eq (concl th) && free_in `env2:bvl_v list` (concl th) &&
                       free_in `x1:bvi_exp` (concl th) &&
                       not (free_in `x2:bvi_exp` (concl th)))) THEN
    MAP_EVERY EXISTS_TAC [`u':(C,FFI)bvi_state`; `f1:(num,num)fmap`;
                          `Rerr e':(bvl_v list,exn_or_ret)result`] THEN
    ASM_REWRITE_TAC[result_rel_Rerr1; injectivity "result"; RIGHT_EXISTS_AND_THM;
                    UNWIND_THM1] THEN
    X_GEN_TAC `loc_opt:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `wrap:bvi_exp` THEN REWRITE_TAC[HD] THEN
      DISCH_THEN(MP_TAC o MATCH_MP wrapper_strip_if_then o CONJUNCT2) THEN
      DISCH_THEN(X_CHOOSE_THEN `w2:bvi_exp` (X_CHOOSE_THEN `w3:bvi_exp`
        (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC)))) THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_If_Rerr th]) o
        check (fun th -> is_eq (concl th) && free_in `env2:bvl_v list` (concl th) &&
                         free_in `x1:bvi_exp` (concl th) &&
                         not (free_in `x2:bvi_exp` (concl th)))) THEN
      MAP_EVERY EXISTS_TAC [`u':(C,FFI)bvi_state`; `f1:(num,num)fmap`;
                            `Rerr e':(bvl_v list,exn_or_ret)result`] THEN
      ASM_REWRITE_TAC[result_rel_Rerr1; injectivity "result"; RIGHT_EXISTS_AND_THM;
                      UNWIND_THM1];
      DISCH_TAC THEN X_GEN_TAC `hole_ptr:num` THEN STRIP_TAC THEN
      REWRITE_TAC[HD; rewrite_worker_def; LET_DEF; LET_END_DEF] THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_If_Rerr th]) o
        check (fun th -> is_eq (concl th) && free_in `env2:bvl_v list` (concl th) &&
                         free_in `x1:bvi_exp` (concl th) &&
                         not (free_in `x2:bvi_exp` (concl th)))) THEN
      MAP_EVERY EXISTS_TAC [`Rerr e':(bvl_v list,exn_or_ret)result`; `f1:(num,num)fmap`;
                            `u':(C,FFI)bvi_state`] THEN
      ASM_REWRITE_TAC[opt_res_rel_def; injectivity "result"; distinctness "result"] THEN
      CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC holes_unchanged_except_subset THEN
      EXISTS_TAC `{}:num->bool` THEN ASM_REWRITE_TAC[EMPTY_SUBSET]]]);;

let BVITMCAUX_eval_Let_Rval = prove
 (`!xs x2 env (s:(C,FFI)bvi_state) vs u.
     bvi_evaluate (xs,env,s) = (Rval vs,u) ==>
     bvi_evaluate ([bvi_Let xs x2],env,s) = bvi_evaluate ([x2],APPEND vs env,u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

let BVITMCAUX_eval_Let_Rerr = prove
 (`!xs env (s:(C,FFI)bvi_state) e u.
     bvi_evaluate (xs,env,s) = (Rerr e,u) ==>
     !x2. bvi_evaluate ([bvi_Let xs x2],env,s) = (Rerr e,u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

let BVITMCAUX_tmc_let_val = prove
 (`!xs x2 vs vs' env1 (s:(num#C,FFI)bvi_state) u r t opt f f1 (s':(C,FFI)bvi_state) u'
    env2 loc.
     bvi_evaluate (xs,env1,s) = (Rval vs,u) /\
     bvi_evaluate (xs,env2,s') = (Rval vs',u') /\
     ALL2 (bvi_tmcProof_v_rel f1) vs vs' /\
     bvi_tmcProof_env_rel opt f env1 env2 /\ f SUBMAP f1 /\
     only_fresh f f1 (bvi_state_refs s') /\
     holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs u') {} /\
     holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs u') /\
     BVITMCAUX_tmc_concl [x2] (APPEND vs env1) u r t opt f1 u' (APPEND vs' env2) loc ==>
     BVITMCAUX_tmc_concl [bvi_Let xs x2] env1 s r t opt f s' env2 loc`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
        ASSUME_TAC MP_TAC)))))))) THEN
  REWRITE_TAC[BVITMCAUX_tmc_concl_def; HD; LENGTH; ARITH_RULE `SUC 0 = 1`] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(C,FFI)bvi_state` (X_CHOOSE_THEN `f2:(num,num)fmap`
    (X_CHOOSE_THEN `r1:(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(LABEL_TAC "br" o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "loc_opt" with Failure _ -> false)) THEN
  SUBGOAL_THEN `FDOM (bvi_state_refs (s':(C,FFI)bvi_state)) SUBSET
                FDOM (bvi_state_refs (u':(C,FFI)bvi_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[bvi_tmcProof_evaluate_refs_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (env1:bvl_v list) + LENGTH (xs:bvi_exp list) =
                LENGTH (APPEND (vs:bvl_v list) env1) /\
                (LENGTH env1 + 1) + LENGTH xs = LENGTH (APPEND vs env1) + 1`
    (CONJUNCTS_THEN2 (LABEL_TAC "len1") (LABEL_TAC "len2")) THENL
   [MP_TAC(ISPECL [`xs:bvi_exp list`; `env1:bvl_v list`; `s:(num#C,FFI)bvi_state`;
      `vs:bvl_v list`; `u:(num#C,FFI)bvi_state`] bvi_evaluate_IMP_LENGTH) THEN
    ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:(num,num)fmap`; `f1:(num,num)fmap`; `f2:(num,num)fmap`;
    `bvi_state_refs (s':(C,FFI)bvi_state)`; `bvi_state_refs (u':(C,FFI)bvi_state)`;
    `bvi_state_refs (t1:(C,FFI)bvi_state)`; `{}:num->bool`] BVITMCAUX_compose) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t1:(C,FFI)bvi_state`; `f2:(num,num)fmap`;
                        `r1:(bvl_v list,exn_or_ret)result`] THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_Let_Rval th]) o
    check (fun th -> is_eq (concl th) && free_in `env2:bvl_v list` (concl th) &&
                     free_in `xs:bvi_exp list` (concl th) &&
                     not (free_in `x2:bvi_exp` (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `loc_opt:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `optimised_code loc loc_opt (bvi_state_code (u:(num#C,FFI)bvi_state))
                  (bvi_state_code (u':(C,FFI)bvi_state))` ASSUME_TAC THENL
   [MATCH_MP_TAC evaluate_pres_opt_code THEN
    MAP_EVERY EXISTS_TAC [`s:(num#C,FFI)bvi_state`; `s':(C,FFI)bvi_state`;
      `xs:bvi_exp list`; `env1:bvl_v list`; `env2:bvl_v list`;
      `Rval vs:(bvl_v list,exn_or_ret)result`;
      `Rval vs':(bvl_v list,exn_or_ret)result`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "br" (MP_TAC o SPEC `loc_opt:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "brw") (LABEL_TAC "brk")) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `wrap:bvi_exp` THEN
    DISCH_THEN(MP_TAC o MATCH_MP wrapper_strip_let) THEN
    DISCH_THEN(X_CHOOSE_THEN `w':bvi_exp` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
    USE_THEN "len1" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_Let_Rval th]) o
      check (fun th -> is_eq (concl th) && free_in `env2:bvl_v list` (concl th) &&
                       free_in `xs:bvi_exp list` (concl th) &&
                       not (free_in `x2:bvi_exp` (concl th)))) THEN
    REMOVE_THEN "brw" (MP_TAC o SPEC `w':bvi_exp`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `tw:(C,FFI)bvi_state` (X_CHOOSE_THEN `fw:(num,num)fmap`
      (X_CHOOSE_THEN `rw:(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`f:(num,num)fmap`; `f1:(num,num)fmap`; `fw:(num,num)fmap`;
      `bvi_state_refs (s':(C,FFI)bvi_state)`; `bvi_state_refs (u':(C,FFI)bvi_state)`;
      `bvi_state_refs (tw:(C,FFI)bvi_state)`; `{}:num->bool`] BVITMCAUX_compose) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`tw:(C,FFI)bvi_state`; `fw:(num,num)fmap`;
                          `rw:(bvl_v list,exn_or_ret)result`] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN X_GEN_TAC `hole_ptr:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o EQT_INTRO o check (fun th -> concl th = `opt:bool`)) THEN
    REWRITE_TAC[rewrite_worker_def; LET_DEF; LET_END_DEF] THEN
    USE_THEN "len1" (fun th1 -> USE_THEN "len2" (fun th2 -> REWRITE_TAC[th1; th2])) THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_Let_Rval th]) o
      check (fun th -> is_eq (concl th) && free_in `env2:bvl_v list` (concl th) &&
                       free_in `xs:bvi_exp list` (concl th) &&
                       not (free_in `x2:bvi_exp` (concl th)))) THEN
    MP_TAC(ISPECL [`f:(num,num)fmap`; `f1:(num,num)fmap`; `env1:bvl_v list`;
      `env2:bvl_v list`; `bvi_state_refs (s':(C,FFI)bvi_state)`;
      `bvi_state_refs (u':(C,FFI)bvi_state)`; `c:bvl_v`; `hole_ptr:num`]
      BVITMCAUX_hole_transport) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REMOVE_THEN "brk" (MP_TAC o SPEC `hole_ptr:num` o REWRITE_RULE[]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [EXISTS_TAC `c:bvl_v` THEN MATCH_MP_TAC hole_has_val_append THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        MP_TAC(MATCH_MP LIST_REL_LENGTH
          (ASSUME `ALL2 (bvi_tmcProof_v_rel f1) vs vs'`)) THEN
        REWRITE_TAC[LENGTH_APPEND; EL_APPEND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        ASM_REWRITE_TAC[ARITH_RULE `~(a + b < a:num) /\ (a + b) - a = b`]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `rw:(bvl_v list,exn_or_ret)result`
      (X_CHOOSE_THEN `fw:(num,num)fmap` (X_CHOOSE_THEN `tw:(C,FFI)bvi_state`
        STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`f:(num,num)fmap`; `f1:(num,num)fmap`; `fw:(num,num)fmap`;
      `bvi_state_refs (s':(C,FFI)bvi_state)`; `bvi_state_refs (u':(C,FFI)bvi_state)`;
      `bvi_state_refs (tw:(C,FFI)bvi_state)`; `{hole_ptr:num}`] BVITMCAUX_compose) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`rw:(bvl_v list,exn_or_ret)result`; `fw:(num,num)fmap`;
                          `tw:(C,FFI)bvi_state`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `res_v:bvl_v` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `res_v:bvl_v` o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "res_v" with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `res_v':bvl_v` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `res_v':bvl_v` THEN CONJ_TAC THENL
     [MATCH_MP_TAC mb_rel_refs_old_subset THEN
      EXISTS_TAC `bvi_state_refs (u':(C,FFI)bvi_state)` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC hole_has_val_submap THEN EXISTS_TAC `f1:(num,num)fmap` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC (MATCH_MP hole_has_val_unappend
        (CONJ th (ASSUME `ALL2 (bvi_tmcProof_v_rel f1) vs vs'`))))]]);;

let BVITMCAUX_tmc_let = prove
 (`!xs x2 env1 (s:(num#C,FFI)bvi_state) r t opt f (s':(C,FFI)bvi_state) env2 loc.
     BVITMCAUX_tmc_ih [bvi_Let xs x2] s /\
     BVITMCAUX_tmc_hyps [bvi_Let xs x2] env1 s r t opt f s' env2 ==>
     BVITMCAUX_tmc_concl [bvi_Let xs x2] env1 s r t opt f s' env2 loc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITMCAUX_tmc_hyps_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `bvi_evaluate (xs,env1,s:(num#C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `rs:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `u:(num#C,FFI)bvi_state` ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(rs = Rerr (Rabort Rtype_error):(bvl_v list,exn_or_ret)result)`
    ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `bvi_evaluate ([bvi_Let xs x2],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_Let_Rerr th]) o
      check (fun th -> is_eq (concl th) && free_in `env1:bvl_v list` (concl th) &&
                       free_in `xs:bvi_exp list` (concl th) &&
                       not (free_in `x2:bvi_exp` (concl th)))) THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "ih" (MP_TAC o SPECL [`xs:bvi_exp list`; `s:(num#C,FFI)bvi_state`;
    `env1:bvl_v list`; `rs:(bvl_v list,exn_or_ret)result`; `u:(num#C,FFI)bvi_state`;
    `F`; `f:(num,num)fmap`; `s':(C,FFI)bvi_state`; `env2:bvl_v list`; `loc:num`] o
    REWRITE_RULE[BVITMCAUX_tmc_ih_def]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LE_REFL; BVITMCAUX_tmc_hyps_def] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [DISJ2_TAC THEN BVITMCAUX_SIZE_TAC;
      ASM_MESON_TAC[env_rel_relax_opt];
      UNDISCH_TAC `ALL (\x. no_mutcons x) [bvi_Let xs x2]` THEN
      REWRITE_TAC[ALL; no_mutcons_def; ETA_AX] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':(C,FFI)bvi_state` (X_CHOOSE_THEN `f1:(num,num)fmap`
    (X_CHOOSE_THEN `rs':(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC)) o
    REWRITE_RULE[BVITMCAUX_tmc_concl_def]) THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs:bvl_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)
    (ISPEC `rs:(bvl_v list,exn_or_ret)result` (cases "result")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[result_rel_Rval; result_rel_Rerr1]) THEN
  REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THENL
   [MATCH_MP_TAC BVITMCAUX_tmc_let_val THEN
    MAP_EVERY EXISTS_TAC [`vs:bvl_v list`; `v':bvl_v list`; `u:(num#C,FFI)bvi_state`;
                          `f1:(num,num)fmap`; `u':(C,FFI)bvi_state`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `bvi_evaluate ([x2],APPEND vs env1,u:(num#C,FFI)bvi_state) = (r,t)`
      ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
        rhs (concl th) = `(r:(bvl_v list,exn_or_ret)result,t:(num#C,FFI)bvi_state)`)) THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC BVITMCAUX_eval_Let_Rval THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "ih" (MP_TAC o SPECL [`[x2:bvi_exp]`;
      `u:(num#C,FFI)bvi_state`; `APPEND vs env1:bvl_v list`;
      `r:(bvl_v list,exn_or_ret)result`; `t:(num#C,FFI)bvi_state`; `opt:bool`;
      `f1:(num,num)fmap`; `u':(C,FFI)bvi_state`; `APPEND v' env2:bvl_v list`;
      `loc:num`] o REWRITE_RULE[BVITMCAUX_tmc_ih_def]) THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[BVITMCAUX_tmc_hyps_def] THEN
    ASM_REWRITE_TAC[LENGTH; ARITH_RULE `SUC 0 = 1`] THEN REPEAT CONJ_TAC THENL
     [DISJ2_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[bvi_evaluate_clock]; BVITMCAUX_SIZE_TAC];
      MATCH_MP_TAC bvi_tmcProof_env_rel_append THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC (GEN_ALL env_rel_submap) THEN EXISTS_TAC `f:(num,num)fmap` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `ALL (\x. no_mutcons x) [bvi_Let xs x2]` THEN
      REWRITE_TAC[ALL; no_mutcons_def] THEN SIMP_TAC[]];
    (* the bindings raised *)
    REWRITE_TAC[BVITMCAUX_tmc_concl_def] THEN
    UNDISCH_TAC `bvi_evaluate ([bvi_Let xs x2],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_Let_Rerr th]) o
      check (fun th -> is_eq (concl th) && free_in `env1:bvl_v list` (concl th) &&
                       free_in `xs:bvi_exp list` (concl th) &&
                       not (free_in `x2:bvi_exp` (concl th)))) THEN
    REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_Let_Rerr th]) o
      check (fun th -> is_eq (concl th) && free_in `env2:bvl_v list` (concl th) &&
                       free_in `xs:bvi_exp list` (concl th) &&
                       not (free_in `x2:bvi_exp` (concl th)))) THEN
    MAP_EVERY EXISTS_TAC [`u':(C,FFI)bvi_state`; `f1:(num,num)fmap`;
                          `Rerr e':(bvl_v list,exn_or_ret)result`] THEN
    ASM_REWRITE_TAC[result_rel_Rerr1; injectivity "result"; RIGHT_EXISTS_AND_THM;
                    UNWIND_THM1] THEN
    X_GEN_TAC `loc_opt:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `wrap:bvi_exp` THEN REWRITE_TAC[HD] THEN
      DISCH_THEN(MP_TAC o MATCH_MP wrapper_strip_let o CONJUNCT2) THEN
      DISCH_THEN(X_CHOOSE_THEN `w':bvi_exp` (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC))) THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_Let_Rerr th]) o
        check (fun th -> is_eq (concl th) && free_in `env2:bvl_v list` (concl th) &&
                         free_in `xs:bvi_exp list` (concl th) &&
                         not (free_in `x2:bvi_exp` (concl th)))) THEN
      MAP_EVERY EXISTS_TAC [`u':(C,FFI)bvi_state`; `f1:(num,num)fmap`;
                            `Rerr e':(bvl_v list,exn_or_ret)result`] THEN
      ASM_REWRITE_TAC[result_rel_Rerr1; injectivity "result"; RIGHT_EXISTS_AND_THM;
                      UNWIND_THM1];
      DISCH_TAC THEN X_GEN_TAC `hole_ptr:num` THEN STRIP_TAC THEN
      REWRITE_TAC[HD; rewrite_worker_def; LET_DEF; LET_END_DEF] THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_Let_Rerr th]) o
        check (fun th -> is_eq (concl th) && free_in `env2:bvl_v list` (concl th) &&
                         free_in `xs:bvi_exp list` (concl th) &&
                         not (free_in `x2:bvi_exp` (concl th)))) THEN
      MAP_EVERY EXISTS_TAC [`Rerr e':(bvl_v list,exn_or_ret)result`; `f1:(num,num)fmap`;
                            `u':(C,FFI)bvi_state`] THEN
      ASM_REWRITE_TAC[opt_res_rel_def; injectivity "result"; distinctness "result"] THEN
      CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC holes_unchanged_except_subset THEN
      EXISTS_TAC `{}:num->bool` THEN ASM_REWRITE_TAC[EMPTY_SUBSET]]]);;

let BVITMCAUX_find_code_cases = prove
 (`!dest (vs:bvl_v list) (c:(num#A)spt) args body.
     bvl_find_code dest vs c = SOME (args,body) <=>
     (?p. dest = SOME p /\ lookup p c = SOME (LENGTH vs,body) /\ args = vs) \/
     (?loc arity. dest = NONE /\ ~(vs = []) /\ LAST vs = bvl_CodePtr loc /\
                  lookup loc c = SOME (arity,body) /\ LENGTH vs = arity + 1 /\
                  args = BUTLAST vs)`,
  GEN_TAC THEN CASES_ON `dest:num option` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_find_code_def; option_DISTINCT; option_INJ; UNWIND_THM1] THEN
  REWRITE_TAC[case_eq "option"; case_eq "prod"; COND_CASE_EQ; case_eq "bvl_v"] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  MESON_TAC[]);;

(* HOL4 line 5028 *)
let find_code_rel = prove
 (`!f vs vs' (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state) dest args body.
     bvl_find_code dest vs (bvi_state_code s) = SOME (args,body) /\
     ALL2 (bvi_tmcProof_v_rel f) vs vs' /\
     bvi_tmcProof_state_rel f s s' ==>
     no_mutcons body /\
     ?args' body' loc.
       bvl_find_code dest vs' (bvi_state_code s') = SOME (args',body') /\
       bvi_tmcProof_env_rel F f args args' /\
       LENGTH args = LENGTH args' /\
       (~(body = body') ==>
        ?loc_opt.
          optimised_code loc loc_opt (bvi_state_code s) (bvi_state_code s') /\
          rewrite_wrapper loc loc_opt (LENGTH args) body = SOME body')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `bvi_tmcProof_code_rel (bvi_state_code (s:(num#C,FFI)bvi_state))
                  (bvi_state_code (s':(C,FFI)bvi_state))` ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_tmcProof_state_rel f (s:(num#C,FFI)bvi_state) (s':(C,FFI)bvi_state)` THEN
    REWRITE_TAC[bvi_tmcProof_state_rel_def] THEN SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  UNDISCH_TAC `bvl_find_code dest vs (bvi_state_code (s:(num#C,FFI)bvi_state)) =
               SOME (args,body)` THEN
  REWRITE_TAC[BVITMCAUX_find_code_cases] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [MP_TAC(ISPECL [`p:num`; `LENGTH (vs:bvl_v list)`; `body:bvi_exp`;
      `bvi_state_code (s:(num#C,FFI)bvi_state)`; `bvi_state_code (s':(C,FFI)bvi_state)`]
      code_rel_cases) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `loc_opt:num`
      (X_CHOOSE_THEN `body2:bvi_exp` STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`vs':bvl_v list`; `body2:bvi_exp`; `p:num`] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[BVITMCAUX_find_code_cases; option_INJ; option_DISTINCT; UNWIND_THM1;
                  distinctness "option"] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC list_rel_env_rel THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    MP_TAC(ISPECL [`loc:num`; `arity:num`; `body:bvi_exp`;
      `bvi_state_code (s:(num#C,FFI)bvi_state)`; `bvi_state_code (s':(C,FFI)bvi_state)`]
      code_rel_cases) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `loc_opt:num`
      (X_CHOOSE_THEN `body2:bvi_exp` STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(vs':bvl_v list = [])` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `LAST (vs':bvl_v list) = bvl_CodePtr loc` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`bvi_tmcProof_v_rel f`; `vs:bvl_v list`; `vs':bvl_v list`]
        list_rel_last) THEN
      ASM_REWRITE_TAC[BVITMCAUX_v_rel_simps] THEN MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`BUTLAST (vs':bvl_v list)`; `body2:bvi_exp`; `loc:num`] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[BVITMCAUX_find_code_cases; option_DISTINCT; distinctness "option"] THEN
      MAP_EVERY EXISTS_TAC [`loc:num`; `arity:num`] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC list_rel_env_rel THEN MATCH_MP_TAC list_rel_front THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[LENGTH_FRONT];
      DISCH_TAC THEN EXISTS_TAC `loc_opt:num` THEN
      SUBGOAL_THEN `LENGTH (BUTLAST (vs:bvl_v list)) = arity` SUBST1_TAC THENL
       [ASM_SIMP_TAC[LENGTH_FRONT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[]]]);;

(* HOL4 line 5447 *)
let dest_thunk_ret_rel_def = cake_def
 `dest_thunk_ret_rel f (t1:bvi_dest_thunk_ret) (t2:bvi_dest_thunk_ret) <=>
    (t1 = bvi_BadRef /\ t2 = bvi_BadRef) \/
    (t1 = bvi_NotThunk /\ t2 = bvi_NotThunk) \/
    ?tm1 tm2 v1 v2.
      t1 = bvi_IsThunk tm1 v1 /\ t2 = bvi_IsThunk tm2 v2 /\
      tm1 = tm2 /\
      bvi_tmcProof_v_rel f v1 v2`;;

let bvi_tmcProof_env_rel_el = prove
 (`!opt f env1 env2 n.
     bvi_tmcProof_env_rel opt f env1 env2 /\
     n < LENGTH env1 ==>
     bvi_tmcProof_v_rel f (EL n env1) (EL n env2)`,
  MATCH_ACCEPT_TAC env_rel_el_v_rel);;

let BVITMCAUX_dtrr_simps = prove
 (`(!f. dest_thunk_ret_rel f bvi_BadRef bvi_BadRef) /\
   (!f. dest_thunk_ret_rel f bvi_NotThunk bvi_NotThunk) /\
   (!f tm1 tm2 v1 v2.
      dest_thunk_ret_rel f (bvi_IsThunk tm1 v1) (bvi_IsThunk tm2 v2) <=>
      tm1 = tm2 /\ bvi_tmcProof_v_rel f v1 v2)`,
  REWRITE_TAC[dest_thunk_ret_rel_def; distinctness "bvi_dest_thunk_ret";
              injectivity "bvi_dest_thunk_ret"] THEN
  MESON_TAC[]);;

let dest_thunk_rel = prove
 (`!opt f env1 env2 (s1:(num#C,FFI)bvi_state) (s2:(C,FFI)bvi_state) n.
     bvi_tmcProof_env_rel opt f env1 env2 /\
     bvi_tmcProof_state_rel f s1 s2 /\
     n < LENGTH env1 ==>
     dest_thunk_ret_rel f (bvi_dest_thunk (EL n env1) (bvi_state_refs s1))
                          (bvi_dest_thunk (EL n env2) (bvi_state_refs s2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`opt:bool`; `f:(num,num)fmap`; `env1:bvl_v list`; `env2:bvl_v list`;
                 `n:num`] bvi_tmcProof_env_rel_el) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(CONJUNCT1(REWRITE_RULE[bvi_tmcProof_state_rel_def]
    (ASSUME `bvi_tmcProof_state_rel f (s1:(num#C,FFI)bvi_state) (s2:(C,FFI)bvi_state)`))) THEN
  SPEC_TAC(`bvi_state_refs (s2:(C,FFI)bvi_state)`,`refs2:(num,(bvl_v)bvl_ref)fmap`) THEN
  SPEC_TAC(`bvi_state_refs (s1:(num#C,FFI)bvi_state)`,`refs1:(num,(bvl_v)bvl_ref)fmap`) THEN
  SPEC_TAC(`EL n env2:bvl_v`,`v2:bvl_v`) THEN SPEC_TAC(`EL n env1:bvl_v`,`v1:bvl_v`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `v1:bvl_v` THEN REWRITE_TAC[BVITMCAUX_v_rel_simps] THEN STRIP_TAC THEN
  RVEQ_TAC THEN REWRITE_TAC[bvi_dest_thunk_def; BVITMCAUX_dtrr_simps] THEN
  FIRST_ASSUM(fun fl -> FIRST_ASSUM(fun sr ->
    MP_TAC (MATCH_MP state_ref_rel_lookup (CONJ fl sr)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `rv:(bvl_v)bvl_ref` (X_CHOOSE_THEN `rw:(bvl_v)bvl_ref`
    STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `bvi_tmcProof_ref_rel f rv rw` THEN
  CASES_ON `rv:(bvl_v)bvl_ref` THEN REWRITE_TAC[BVITMCAUX_ref_rel_simps] THEN
  STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[BVITMCAUX_dtrr_simps] THEN
  REPEAT TOP_CASE_TAC THEN ASM_REWRITE_TAC[BVITMCAUX_dtrr_simps]);;

let BVITMCAUX_eval_Force = prove
 (CASE_TERM `!fl n env (s:(C,FFI)bvi_state).
     bvi_evaluate ([bvi_Force fl n],env,s) =
     if ~(n < LENGTH env) then (Rerr (Rabort Rtype_error),s) else
       match bvi_dest_thunk (EL n env) (bvi_state_refs s) with
         bvi_BadRef -> (Rerr (Rabort Rtype_error),s)
       | bvi_NotThunk -> (Rerr (Rabort Rtype_error),s)
       | bvi_IsThunk Evaluated v -> (Rval [v],s)
       | bvi_IsThunk NotEvaluated g ->
           (match bvl_find_code (SOME fl) [EL n env; g] (bvi_state_code s) with
              NONE -> (Rerr (Rabort Rtype_error),s)
            | SOME (args,exp) ->
                if bvi_state_clock s = 0 then
                  (Rerr (Rabort Rtimeout_error),bvi_state_clock_fupd (K 0) s)
                else BVITMCAUX_call_post (bvi_evaluate ([exp],args,bvi_dec_clock 1 s)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_evaluate_def; LET_DEF; LET_END_DEF] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[BVITMCAUX_call_post_def] THEN
  CASE_REWRITE_TAC[]);;

(* rewrite with the assumptions and reduce the case expressions, twice *)
let BVITMCAUX_ACR_TAC =
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];;

let BVITMCAUX_tmc_force = prove
 (`!fl n env1 (s:(num#C,FFI)bvi_state) r t opt f (s':(C,FFI)bvi_state) env2 loc.
     BVITMCAUX_tmc_ih [bvi_Force fl n] s /\
     BVITMCAUX_tmc_hyps [bvi_Force fl n] env1 s r t opt f s' env2 ==>
     BVITMCAUX_tmc_concl [bvi_Force fl n] env1 s r t opt f s' env2 loc`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") (LABEL_TAC "hyps")) THEN
  MATCH_MP_TAC BVITMCAUX_tmc_plain THEN
  ASM_REWRITE_TAC[rewrite_wrapper_def; rewrite_worker_def] THEN
  REMOVE_THEN "hyps" (STRIP_ASSUME_TAC o REWRITE_RULE[BVITMCAUX_tmc_hyps_def]) THEN
  SUBGOAL_THEN `n < LENGTH (env1:bvl_v list)` ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_evaluate ([bvi_Force fl n],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[BVITMCAUX_eval_Force] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `n < LENGTH (env2:bvl_v list)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP bvi_tmcProof_env_rel_length) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`opt:bool`; `f:(num,num)fmap`; `env1:bvl_v list`; `env2:bvl_v list`;
    `s:(num#C,FFI)bvi_state`; `s':(C,FFI)bvi_state`; `n:num`] dest_thunk_rel) THEN
  ASM_REWRITE_TAC[dest_thunk_ret_rel_def] THEN
  DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC (DISJ_CASES_THEN2 STRIP_ASSUME_TAC
    (X_CHOOSE_THEN `tm:thunk_mode` (X_CHOOSE_THEN `tm2:thunk_mode`
      (X_CHOOSE_THEN `v1:bvl_v` (X_CHOOSE_THEN `v2:bvl_v` STRIP_ASSUME_TAC)))))) THENL
   [UNDISCH_TAC `bvi_evaluate ([bvi_Force fl n],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[BVITMCAUX_eval_Force] THEN BVITMCAUX_ACR_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `bvi_evaluate ([bvi_Force fl n],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[BVITMCAUX_eval_Force] THEN BVITMCAUX_ACR_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `tm:thunk_mode = tm2`)) THEN
  CASES_ON `tm2:thunk_mode` THENL
   [UNDISCH_TAC `bvi_evaluate ([bvi_Force fl n],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[BVITMCAUX_eval_Force] THEN BVITMCAUX_ACR_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`s':(C,FFI)bvi_state`; `f:(num,num)fmap`;
                          `Rval [v2]:(bvl_v list,exn_or_ret)result`] THEN
    REWRITE_TAC[BVITMCAUX_eval_Force] THEN BVITMCAUX_ACR_TAC THEN
    ASM_REWRITE_TAC[result_rel_def; ALL2; SUBMAP_REFL; only_fresh_refl;
      holes_unchanged_except_refl; holes_still_not_finalised_refl];
    ALL_TAC] THEN
  MP_TAC(ISPEC `bvl_find_code (SOME fl) [EL n env1; v1]
                  (bvi_state_code (s:(num#C,FFI)bvi_state))` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:bvl_v list#bvi_exp` MP_TAC)) THENL
   [UNDISCH_TAC `bvi_evaluate ([bvi_Force fl n],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[BVITMCAUX_eval_Force] THEN BVITMCAUX_ACR_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `p:bvl_v list#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `args:bvl_v list` (X_CHOOSE_THEN `exp:bvi_exp` SUBST1_TAC)) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`f:(num,num)fmap`; `[EL n env1; v1]:bvl_v list`;
    `[EL n env2; v2]:bvl_v list`; `s:(num#C,FFI)bvi_state`; `s':(C,FFI)bvi_state`;
    `SOME fl:num option`; `args:bvl_v list`; `exp:bvi_exp`] find_code_rel) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ALL2] THEN MATCH_MP_TAC bvi_tmcProof_env_rel_el THEN
    EXISTS_TAC `opt:bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `args':bvl_v list`
    (X_CHOOSE_THEN `body':bvi_exp` (X_CHOOSE_THEN `loc':num` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `bvi_state_clock (s':(C,FFI)bvi_state) =
                bvi_state_clock (s:(num#C,FFI)bvi_state)` ASSUME_TAC THENL
   [ASM_MESON_TAC[bvi_tmcProof_state_rel_def]; ALL_TAC] THEN
  ASM_CASES_TAC `bvi_state_clock (s:(num#C,FFI)bvi_state) = 0` THENL
   [UNDISCH_TAC `bvi_evaluate ([bvi_Force fl n],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[BVITMCAUX_eval_Force] THEN BVITMCAUX_ACR_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`bvi_state_clock_fupd (K 0) (s':(C,FFI)bvi_state)`;
      `f:(num,num)fmap`; `Rerr (Rabort Rtimeout_error):(bvl_v list,exn_or_ret)result`] THEN
    REWRITE_TAC[BVITMCAUX_eval_Force] THEN BVITMCAUX_ACR_TAC THEN
    ASM_SIMP_TAC[bvi_tmcProof_state_rel_with_clock; SUBMAP_REFL; only_fresh_refl;
      holes_unchanged_except_refl; holes_still_not_finalised_refl;
      bvi_state_INFO.ri_accfupds; result_rel_def; exc_rel_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `bvi_evaluate ([exp],args,bvi_dec_clock 1 (s:(num#C,FFI)bvi_state)) = (r,t) /\
                ~(?vs. r = Rerr (Rraise (Ret vs)):(bvl_v list,exn_or_ret)result)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_evaluate ([bvi_Force fl n],env1,s:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[BVITMCAUX_eval_Force] THEN BVITMCAUX_ACR_TAC THEN
    MP_TAC(ISPEC `bvi_evaluate ([exp],args,bvi_dec_clock 1 (s:(num#C,FFI)bvi_state))`
      PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `q:(bvl_v list,exn_or_ret)result`
      (X_CHOOSE_THEN `u:(num#C,FFI)bvi_state` SUBST1_TAC)) THEN
    ASM_CASES_TAC `?vs. q = Rerr (Rraise (Ret vs)):(bvl_v list,exn_or_ret)result` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `vs:bvl_v list` SUBST_ALL_TAC) THEN
      REWRITE_TAC[BVITMCAUX_call_post_Ret; PAIR_EQ] THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[BVITMCAUX_call_post_id] THEN REWRITE_TAC[PAIR_EQ] THEN
      DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "ih" (MP_TAC o SPECL [`[exp:bvi_exp]`; `bvi_dec_clock 1 (s:(num#C,FFI)bvi_state)`;
    `args:bvl_v list`; `r:(bvl_v list,exn_or_ret)result`; `t:(num#C,FFI)bvi_state`; `F`;
    `f:(num,num)fmap`; `bvi_dec_clock 1 (s':(C,FFI)bvi_state)`; `args':bvl_v list`;
    `loc':num`] o REWRITE_RULE[BVITMCAUX_tmc_ih_def]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[BVITMCAUX_tmc_hyps_def; BVITMCAUX_dec_clock_simps] THEN
    ASM_REWRITE_TAC[ALL] THEN REPEAT CONJ_TAC THEN
    TRY(DISJ1_TAC THEN ASM_ARITH_TAC) THEN
    MATCH_MP_TAC BVITMCAUX_state_rel_dec_clock THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':(C,FFI)bvi_state` (X_CHOOSE_THEN `f':(num,num)fmap`
    (X_CHOOSE_THEN `r':(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC)) o
    REWRITE_RULE[BVITMCAUX_tmc_concl_def; BVITMCAUX_dec_clock_simps; HD; LENGTH;
                 ARITH_RULE `SUC 0 = 1`]) THEN
  SUBGOAL_THEN `~(?vs. r' = Rerr (Rraise (Ret vs)):(bvl_v list,exn_or_ret)result)`
    ASSUME_TAC THENL [ASM_MESON_TAC[BVITMCAUX_result_rel_Ret]; ALL_TAC] THEN
  ASM_CASES_TAC `exp:bvi_exp = body'` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`t':(C,FFI)bvi_state`; `f':(num,num)fmap`;
                          `r':(bvl_v list,exn_or_ret)result`] THEN
    REWRITE_TAC[BVITMCAUX_eval_Force] THEN BVITMCAUX_ACR_TAC THEN
    ASM_SIMP_TAC[BVITMCAUX_call_post_id];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC (MP th (ASSUME `~(exp:bvi_exp = body')`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `loc_opt:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `loc_opt:num` o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "loc_opt" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `body':bvi_exp`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tw:(C,FFI)bvi_state` (X_CHOOSE_THEN `fw:(num,num)fmap`
    (X_CHOOSE_THEN `rw:(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~(?vs. rw = Rerr (Rraise (Ret vs)):(bvl_v list,exn_or_ret)result)`
    ASSUME_TAC THENL [ASM_MESON_TAC[BVITMCAUX_result_rel_Ret]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`tw:(C,FFI)bvi_state`; `fw:(num,num)fmap`;
                        `rw:(bvl_v list,exn_or_ret)result`] THEN
  REWRITE_TAC[BVITMCAUX_eval_Force] THEN BVITMCAUX_ACR_TAC THEN
  ASM_SIMP_TAC[BVITMCAUX_call_post_id]);;

(* the result of a call after its body has been evaluated *)
let BVITMCAUX_handle_def = cake_def
 `BVITMCAUX_handle handler env ((x:(bvl_v list,exn_or_ret)result),(s:(C,FFI)bvi_state)) =
    match x with
      Rerr (Rraise (Exn v)) ->
        (match handler with
           SOME h -> BVITMCAUX_call_post (bvi_evaluate ([h],CONS v env,s))
         | NONE -> (Rerr (Rraise (Exn v)),s))
    | Rerr (Rraise (Ret a)) -> (Rerr (Rabort Rtype_error),s)
    | _ -> (x,s)`;;

let BVITMCAUX_eval_Call = prove
 (CASE_TERM `!ts dest xs handler env (s:(C,FFI)bvi_state).
     bvi_evaluate ([bvi_Call ts dest xs handler],env,s) =
     if IS_NONE dest /\ IS_SOME handler then (Rerr (Rabort Rtype_error),s) else
     match bvi_evaluate (xs,env,s) with
       (Rval vs,s1) ->
         (match bvl_find_code dest vs (bvi_state_code s1) with
            NONE -> (Rerr (Rabort Rtype_error),s1)
          | SOME (args,exp) ->
              if bvi_state_clock s1 < ts + 1
              then (Rerr (Rabort Rtimeout_error),bvi_state_clock_fupd (K 0) s1)
              else BVITMCAUX_handle handler env
                     (bvi_evaluate ([exp],args,bvi_dec_clock (ts + 1) s1)))
     | (Rerr e,s1) -> (Rerr e,s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_evaluate_def] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[BVITMCAUX_handle_def; BVITMCAUX_call_post_def] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[BVITMCAUX_call_post_def] THEN
  CASE_REWRITE_TAC[]);;

let BVITMCAUX_eor_rel_inv = prove
 (`(!f v y. eor_rel f (Exn v) y <=> ?v'. y = Exn v' /\ bvi_tmcProof_v_rel f v v') /\
   (!f vs y. eor_rel f (Ret vs) y <=>
             ?vs'. y = Ret vs' /\ ALL2 (bvi_tmcProof_v_rel f) vs vs')`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN CASES_ON `y:exn_or_ret` THEN
  REWRITE_TAC[eor_rel_def; injectivity "exn_or_ret"; distinctness "exn_or_ret"] THEN
  MESON_TAC[]);;

let BVITMCAUX_result_rel_Exn = prove
 (`!f v (r2:(bvl_v list,exn_or_ret)result).
     result_rel (ALL2 (bvi_tmcProof_v_rel f)) (eor_rel f) (Rerr (Rraise (Exn v))) r2 <=>
     ?v'. r2 = Rerr (Rraise (Exn v')) /\ bvi_tmcProof_v_rel f v v'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[result_rel_Rerr1; exc_rel_raise1; BVITMCAUX_eor_rel_inv] THEN
  MESON_TAC[]);;

let BVITMCAUX_result_rel_Exn_iff = prove
 (`!f (r1:(bvl_v list,exn_or_ret)result) r2.
     result_rel (ALL2 (bvi_tmcProof_v_rel f)) (eor_rel f) r1 r2 ==>
     ((?v. r1 = Rerr (Rraise (Exn v))) <=> (?v. r2 = Rerr (Rraise (Exn v))))`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `r1:(bvl_v list,exn_or_ret)result` THEN
  REWRITE_TAC[result_rel_Rval; result_rel_Rerr1] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[distinctness "result"; injectivity "result"] THEN
  POP_ASSUM MP_TAC THEN
  CASES_ON `a:(exn_or_ret)error_result` THEN
  REWRITE_TAC[exc_rel_raise1; exc_rel_type_error1] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[injectivity "error_result"; distinctness "error_result"] THEN
  POP_ASSUM MP_TAC THEN CASES_ON `a':exn_or_ret` THEN
  CASES_ON `v':exn_or_ret` THEN
  REWRITE_TAC[eor_rel_def; injectivity "exn_or_ret"; distinctness "exn_or_ret"] THEN
  MESON_TAC[]);;

let BVITMCAUX_handle_nonexn = prove
 (`!handler env (x:(bvl_v list,exn_or_ret)result) (s:(C,FFI)bvi_state).
     ~(?v. x = Rerr (Rraise (Exn v))) ==>
     BVITMCAUX_handle handler env (x,s) = BVITMCAUX_call_post (x,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITMCAUX_handle_def; BVITMCAUX_call_post_def] THEN
  REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[injectivity "result"; injectivity "error_result"; injectivity "exn_or_ret";
              distinctness "result"; distinctness "error_result";
              distinctness "exn_or_ret"] THEN
  MESON_TAC[]);;

let BVITMCAUX_call_finish = prove
 (`!xs0 handler env1 env2 (s:(num#C,FFI)bvi_state) (s2:(num#C,FFI)bvi_state)
    (s':(C,FFI)bvi_state) (t2:(C,FFI)bvi_state) cres r2 r t f f2.
     BVITMCAUX_tmc_ih xs0 s /\ bvi_state_clock s2 < bvi_state_clock s /\
     BVITMCAUX_handle handler env1 (cres,s2) = (r,t) /\
     ~(r = Rerr (Rabort Rtype_error)) /\
     result_rel (ALL2 (bvi_tmcProof_v_rel f2)) (eor_rel f2) cres r2 /\
     bvi_tmcProof_state_rel f2 s2 t2 /\
     bvi_tmcProof_env_rel F f env1 env2 /\
     (!h. handler = SOME h ==> no_mutcons h) /\
     f SUBMAP f2 /\ only_fresh f f2 (bvi_state_refs s') /\
     holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t2) {} /\
     holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t2) /\
     FDOM (bvi_state_refs s') SUBSET FDOM (bvi_state_refs t2) ==>
     ?t' f' r'. BVITMCAUX_handle handler env2 (r2,t2) = (r',t') /\
       result_rel (ALL2 (bvi_tmcProof_v_rel f')) (eor_rel f') r r' /\
       bvi_tmcProof_state_rel f' t t' /\ f SUBMAP f' /\
       only_fresh f f' (bvi_state_refs s') /\
       holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t') {} /\
       holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `?v. cres = Rerr (Rraise (Exn v)):(bvl_v list,exn_or_ret)result` THENL
   [ALL_TAC;
    SUBGOAL_THEN `~(?v. r2 = Rerr (Rraise (Exn v)):(bvl_v list,exn_or_ret)result)`
      ASSUME_TAC THENL [ASM_MESON_TAC[BVITMCAUX_result_rel_Exn_iff]; ALL_TAC] THEN
    SUBGOAL_THEN `~(?vs. cres = Rerr (Rraise (Ret vs)):(bvl_v list,exn_or_ret)result)`
      ASSUME_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `vs:bvl_v list` SUBST_ALL_TAC) THEN
      UNDISCH_TAC `BVITMCAUX_handle handler env1
         (Rerr (Rraise (Ret vs)),s2:(num#C,FFI)bvi_state) = (r,t)` THEN
      ASM_SIMP_TAC[BVITMCAUX_handle_nonexn; BVITMCAUX_call_post_Ret; PAIR_EQ] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(?vs. r2 = Rerr (Rraise (Ret vs)):(bvl_v list,exn_or_ret)result)`
      ASSUME_TAC THENL [ASM_MESON_TAC[BVITMCAUX_result_rel_Ret]; ALL_TAC] THEN
    UNDISCH_TAC `BVITMCAUX_handle handler env1 (cres,s2:(num#C,FFI)bvi_state) = (r,t)` THEN
    ASM_SIMP_TAC[BVITMCAUX_handle_nonexn; BVITMCAUX_call_post_id; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`t2:(C,FFI)bvi_state`; `f2:(num,num)fmap`;
                          `r2:(bvl_v list,exn_or_ret)result`] THEN
    ASM_SIMP_TAC[BVITMCAUX_handle_nonexn; BVITMCAUX_call_post_id]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `v:bvl_v` SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `v':bvl_v` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) o
    REWRITE_RULE[BVITMCAUX_result_rel_Exn] o check (BVITMCAUX_head_is "result_rel")) THEN
  MP_TAC(ISPEC `handler:bvi_exp option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `h:bvi_exp` SUBST_ALL_TAC)) THENL
   [UNDISCH_TAC `BVITMCAUX_handle NONE env1
      (Rerr (Rraise (Exn v)),s2:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[BVITMCAUX_handle_def] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`t2:(C,FFI)bvi_state`; `f2:(num,num)fmap`;
                          `Rerr (Rraise (Exn v')):(bvl_v list,exn_or_ret)result`] THEN
    REWRITE_TAC[BVITMCAUX_handle_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[BVITMCAUX_result_rel_Exn; injectivity "result";
      injectivity "error_result"; injectivity "exn_or_ret"; UNWIND_THM1] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `BVITMCAUX_handle (SOME h) env1
    (Rerr (Rraise (Exn v)),s2:(num#C,FFI)bvi_state) = (r,t)` THEN
  REWRITE_TAC[BVITMCAUX_handle_def] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `bvi_evaluate ([h],CONS v env1,s2:(num#C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `k:(num#C,FFI)bvi_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `?vs. q = Rerr (Rraise (Ret vs)):(bvl_v list,exn_or_ret)result` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `vs:bvl_v list` SUBST_ALL_TAC) THEN
    REWRITE_TAC[BVITMCAUX_call_post_Ret; PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[BVITMCAUX_call_post_id; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  USE_THEN "ih" (MP_TAC o SPECL [`[h:bvi_exp]`; `s2:(num#C,FFI)bvi_state`;
    `CONS v env1:bvl_v list`; `q:(bvl_v list,exn_or_ret)result`; `k:(num#C,FFI)bvi_state`;
    `F`; `f2:(num,num)fmap`; `t2:(C,FFI)bvi_state`; `CONS v' env2:bvl_v list`; `0`] o
    REWRITE_RULE[BVITMCAUX_tmc_ih_def]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[BVITMCAUX_tmc_hyps_def] THEN ASM_REWRITE_TAC[ALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC env_rel_cons THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC (GEN_ALL env_rel_submap) THEN EXISTS_TAC `f:(num,num)fmap` THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)bvi_state` (X_CHOOSE_THEN `f3:(num,num)fmap`
    (X_CHOOSE_THEN `r3:(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC)) o
    REWRITE_RULE[BVITMCAUX_tmc_concl_def]) THEN
  SUBGOAL_THEN `~(?vs. r3 = Rerr (Rraise (Ret vs)):(bvl_v list,exn_or_ret)result)`
    ASSUME_TAC THENL [ASM_MESON_TAC[BVITMCAUX_result_rel_Ret]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:(num,num)fmap`; `f2:(num,num)fmap`; `f3:(num,num)fmap`;
    `bvi_state_refs (s':(C,FFI)bvi_state)`; `bvi_state_refs (t2:(C,FFI)bvi_state)`;
    `bvi_state_refs (t3:(C,FFI)bvi_state)`; `{}:num->bool`] BVITMCAUX_compose) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t3:(C,FFI)bvi_state`; `f3:(num,num)fmap`;
                        `r3:(bvl_v list,exn_or_ret)result`] THEN
  REWRITE_TAC[BVITMCAUX_handle_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[BVITMCAUX_call_post_id]);;

let BVITMCAUX_tmc_call = prove
 (`!ts dest xs handler env1 (s:(num#C,FFI)bvi_state) r t opt f (s':(C,FFI)bvi_state)
    env2 loc.
     BVITMCAUX_tmc_ih [bvi_Call ts dest xs handler] s /\
     BVITMCAUX_tmc_hyps [bvi_Call ts dest xs handler] env1 s r t opt f s' env2 /\
     bvi_to_cb (LENGTH env1) loc (bvi_Call ts dest xs handler) = NONE ==>
     BVITMCAUX_tmc_concl [bvi_Call ts dest xs handler] env1 s r t opt f s' env2 loc`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MATCH_MP_TAC BVITMCAUX_tmc_plain THEN
  ASM_REWRITE_TAC[rewrite_wrapper_def; rewrite_worker_def] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[BVITMCAUX_tmc_hyps_def] o
    check (BVITMCAUX_head_is "BVITMCAUX_tmc_hyps")) THEN
  SUBGOAL_THEN `~(IS_NONE (dest:num option) /\ IS_SOME (handler:bvi_exp option))`
    ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `bvi_evaluate ([bvi_Call ts dest xs handler],env1,
                               s:(num#C,FFI)bvi_state) = (r,t)` THEN
    ASM_REWRITE_TAC[BVITMCAUX_eval_Call; PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!h. handler = SOME h ==> no_mutcons h` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\x. no_mutcons x) [bvi_Call ts dest xs handler]` THEN
    REWRITE_TAC[ALL; no_mutcons_def] THEN
    MP_TAC(ISPEC `handler:bvi_exp option` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `h0:bvi_exp` SUBST1_TAC)) THEN
    CASE_REWRITE_TAC[option_INJ; distinctness "option"] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `bvi_evaluate (xs,env1,s:(num#C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `rx:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `u:(num#C,FFI)bvi_state` ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(rx = Rerr (Rabort Rtype_error):(bvl_v list,exn_or_ret)result)`
    ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `bvi_evaluate ([bvi_Call ts dest xs handler],env1,
                               s:(num#C,FFI)bvi_state) = (r,t)` THEN
    ASM_REWRITE_TAC[BVITMCAUX_eval_Call] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `bvi_state_clock (u:(num#C,FFI)bvi_state) <=
                bvi_state_clock (s:(num#C,FFI)bvi_state)` ASSUME_TAC THENL
   [ASM_MESON_TAC[bvi_evaluate_clock]; ALL_TAC] THEN
  USE_THEN "ih" (MP_TAC o SPECL [`xs:bvi_exp list`; `s:(num#C,FFI)bvi_state`;
    `env1:bvl_v list`; `rx:(bvl_v list,exn_or_ret)result`; `u:(num#C,FFI)bvi_state`;
    `F`; `f:(num,num)fmap`; `s':(C,FFI)bvi_state`; `env2:bvl_v list`; `loc:num`] o
    REWRITE_RULE[BVITMCAUX_tmc_ih_def]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LE_REFL; BVITMCAUX_tmc_hyps_def] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [DISJ2_TAC THEN BVITMCAUX_SIZE_TAC;
      ASM_MESON_TAC[env_rel_relax_opt];
      UNDISCH_TAC `ALL (\x. no_mutcons x) [bvi_Call ts dest xs handler]` THEN
      REWRITE_TAC[ALL; no_mutcons_def; ETA_AX] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':(C,FFI)bvi_state` (X_CHOOSE_THEN `f1:(num,num)fmap`
    (X_CHOOSE_THEN `rx':(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC)) o
    REWRITE_RULE[BVITMCAUX_tmc_concl_def]) THEN
  SUBGOAL_THEN `FDOM (bvi_state_refs (s':(C,FFI)bvi_state)) SUBSET
                FDOM (bvi_state_refs (u':(C,FFI)bvi_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[bvi_tmcProof_evaluate_refs_SUBSET]; ALL_TAC] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs:bvl_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)
    (ISPEC `rx:(bvl_v list,exn_or_ret)result` (cases "result")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[result_rel_Rval; result_rel_Rerr1]) THEN
  REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `bvi_evaluate ([bvi_Call ts dest xs handler],env1,
                               s:(num#C,FFI)bvi_state) = (r,t)` THEN
    ASM_REWRITE_TAC[BVITMCAUX_eval_Call] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`u':(C,FFI)bvi_state`; `f1:(num,num)fmap`;
                          `Rerr e':(bvl_v list,exn_or_ret)result`] THEN
    ASM_REWRITE_TAC[BVITMCAUX_eval_Call] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[result_rel_Rerr1; injectivity "result"; RIGHT_EXISTS_AND_THM;
                    UNWIND_THM1]] THEN
  MP_TAC(ISPEC `bvl_find_code dest vs (bvi_state_code (u:(num#C,FFI)bvi_state))`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:bvl_v list#bvi_exp` MP_TAC)) THENL
   [UNDISCH_TAC `bvi_evaluate ([bvi_Call ts dest xs handler],env1,
                               s:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[BVITMCAUX_eval_Call] THEN BVITMCAUX_ACR_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `p:bvl_v list#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `args:bvl_v list` (X_CHOOSE_THEN `exp:bvi_exp` SUBST1_TAC)) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`f1:(num,num)fmap`; `vs:bvl_v list`; `v':bvl_v list`;
    `u:(num#C,FFI)bvi_state`; `u':(C,FFI)bvi_state`; `dest:num option`;
    `args:bvl_v list`; `exp:bvi_exp`] find_code_rel) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `args':bvl_v list`
    (X_CHOOSE_THEN `body':bvi_exp` (X_CHOOSE_THEN `loc':num` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `bvi_state_clock (u':(C,FFI)bvi_state) =
                bvi_state_clock (u:(num#C,FFI)bvi_state)` ASSUME_TAC THENL
   [ASM_MESON_TAC[bvi_tmcProof_state_rel_def]; ALL_TAC] THEN
  ASM_CASES_TAC `bvi_state_clock (u:(num#C,FFI)bvi_state) < ts + 1` THENL
   [UNDISCH_TAC `bvi_evaluate ([bvi_Call ts dest xs handler],env1,
                               s:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[BVITMCAUX_eval_Call] THEN BVITMCAUX_ACR_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`bvi_state_clock_fupd (K 0) (u':(C,FFI)bvi_state)`;
      `f1:(num,num)fmap`; `Rerr (Rabort Rtimeout_error):(bvl_v list,exn_or_ret)result`] THEN
    REWRITE_TAC[BVITMCAUX_eval_Call] THEN BVITMCAUX_ACR_TAC THEN
    ASM_SIMP_TAC[bvi_tmcProof_state_rel_with_clock; bvi_state_INFO.ri_accfupds;
                 result_rel_def; exc_rel_def];
    ALL_TAC] THEN
  MP_TAC(ISPEC `bvi_evaluate ([exp],args,bvi_dec_clock (ts + 1) (u:(num#C,FFI)bvi_state))`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cres:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `s2:(num#C,FFI)bvi_state` ASSUME_TAC)) THEN
  SUBGOAL_THEN `BVITMCAUX_handle handler env1 (cres,s2:(num#C,FFI)bvi_state) = (r,t)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_evaluate ([bvi_Call ts dest xs handler],env1,
                               s:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[BVITMCAUX_eval_Call] THEN BVITMCAUX_ACR_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(cres = Rerr (Rabort Rtype_error):(bvl_v list,exn_or_ret)result)`
    ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `BVITMCAUX_handle handler env1
      (Rerr (Rabort Rtype_error),s2:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[BVITMCAUX_handle_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?t2 f2 r2. bvi_evaluate ([body'],args',bvi_dec_clock (ts + 1) (u':(C,FFI)bvi_state)) =
               (r2,t2) /\
               result_rel (ALL2 (bvi_tmcProof_v_rel f2)) (eor_rel f2) cres r2 /\
               bvi_tmcProof_state_rel f2 s2 t2 /\ f1 SUBMAP f2 /\
               only_fresh f1 f2 (bvi_state_refs u') /\
               holes_unchanged_except f1 (bvi_state_refs u') (bvi_state_refs t2) {} /\
               holes_still_not_finalised f1 (bvi_state_refs u') (bvi_state_refs t2)`
    STRIP_ASSUME_TAC THENL
   [USE_THEN "ih" (MP_TAC o SPECL [`[exp:bvi_exp]`;
      `bvi_dec_clock (ts + 1) (u:(num#C,FFI)bvi_state)`; `args:bvl_v list`;
      `cres:(bvl_v list,exn_or_ret)result`; `s2:(num#C,FFI)bvi_state`; `F`;
      `f1:(num,num)fmap`; `bvi_dec_clock (ts + 1) (u':(C,FFI)bvi_state)`;
      `args':bvl_v list`; `loc':num`] o REWRITE_RULE[BVITMCAUX_tmc_ih_def]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[BVITMCAUX_tmc_hyps_def; BVITMCAUX_dec_clock_simps] THEN
      ASM_REWRITE_TAC[ALL] THEN REPEAT CONJ_TAC THEN
      TRY(DISJ1_TAC THEN ASM_ARITH_TAC) THEN
      MATCH_MP_TAC BVITMCAUX_state_rel_dec_clock THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)bvi_state` (X_CHOOSE_THEN `f3:(num,num)fmap`
      (X_CHOOSE_THEN `r3:(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC)) o
      REWRITE_RULE[BVITMCAUX_tmc_concl_def; BVITMCAUX_dec_clock_simps; HD; LENGTH;
                   ARITH_RULE `SUC 0 = 1`]) THEN
    ASM_CASES_TAC `exp:bvi_exp = body'` THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
      MAP_EVERY EXISTS_TAC [`t3:(C,FFI)bvi_state`; `f3:(num,num)fmap`;
                            `r3:(bvl_v list,exn_or_ret)result`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC (MP th (ASSUME `~(exp:bvi_exp = body')`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `loc_opt:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `loc_opt:num` o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "loc_opt" with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `body':bvi_exp`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `tw:(C,FFI)bvi_state` (X_CHOOSE_THEN `fw:(num,num)fmap`
      (X_CHOOSE_THEN `rw:(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`tw:(C,FFI)bvi_state`; `fw:(num,num)fmap`;
                          `rw:(bvl_v list,exn_or_ret)result`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:(num,num)fmap`; `f1:(num,num)fmap`; `f2:(num,num)fmap`;
    `bvi_state_refs (s':(C,FFI)bvi_state)`; `bvi_state_refs (u':(C,FFI)bvi_state)`;
    `bvi_state_refs (t2:(C,FFI)bvi_state)`; `{}:num->bool`] BVITMCAUX_compose) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FDOM (bvi_state_refs (s':(C,FFI)bvi_state)) SUBSET
                FDOM (bvi_state_refs (t2:(C,FFI)bvi_state))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `FDOM (bvi_state_refs (u':(C,FFI)bvi_state))` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`[body':bvi_exp]`; `args':bvl_v list`;
      `bvi_dec_clock (ts + 1) (u':(C,FFI)bvi_state)`;
      `r2:(bvl_v list,exn_or_ret)result`; `t2:(C,FFI)bvi_state`]
      bvi_tmcProof_evaluate_refs_SUBSET) THEN
    ASM_REWRITE_TAC[BVITMCAUX_dec_clock_simps]; ALL_TAC] THEN
  MP_TAC(ISPECL [`[bvi_Call ts dest xs handler]`; `handler:bvi_exp option`;
    `env1:bvl_v list`; `env2:bvl_v list`; `s:(num#C,FFI)bvi_state`;
    `s2:(num#C,FFI)bvi_state`; `s':(C,FFI)bvi_state`; `t2:(C,FFI)bvi_state`;
    `cres:(bvl_v list,exn_or_ret)result`; `r2:(bvl_v list,exn_or_ret)result`;
    `r:(bvl_v list,exn_or_ret)result`; `t:(num#C,FFI)bvi_state`; `f:(num,num)fmap`;
    `f2:(num,num)fmap`] BVITMCAUX_call_finish) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`[exp:bvi_exp]`; `args:bvl_v list`;
        `bvi_dec_clock (ts + 1) (u:(num#C,FFI)bvi_state)`;
        `cres:(bvl_v list,exn_or_ret)result`; `s2:(num#C,FFI)bvi_state`]
        bvi_evaluate_clock) THEN
      ASM_REWRITE_TAC[BVITMCAUX_dec_clock_simps] THEN ASM_ARITH_TAC;
      ASM_MESON_TAC[env_rel_relax_opt]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':(C,FFI)bvi_state` (X_CHOOSE_THEN `f':(num,num)fmap`
    (X_CHOOSE_THEN `r':(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`t':(C,FFI)bvi_state`; `f':(num,num)fmap`;
                        `r':(bvl_v list,exn_or_ret)result`] THEN
  REWRITE_TAC[BVITMCAUX_eval_Call] THEN BVITMCAUX_ACR_TAC);;

(* the result of a LetCall after the body of the callee has been evaluated *)
let BVITMCAUX_lc_post_def = cake_def
 `BVITMCAUX_lc_post rets y env ((x:(bvl_v list,exn_or_ret)result),(s:(C,FFI)bvi_state)) =
    match x with
      Rval a -> (Rerr (Rabort Rtype_error),s)
    | Rerr (Rraise (Ret ret_vs)) ->
        if LENGTH ret_vs = rets then bvi_evaluate ([y],APPEND ret_vs env,s)
        else (Rerr (Rabort Rtype_error),s)
    | _ -> (x,s)`;;

let BVITMCAUX_eval_LetCall = prove
 (CASE_TERM `!rets ts dest xs y env (s:(C,FFI)bvi_state).
     bvi_evaluate ([LetCall rets ts dest xs y],env,s) =
     match bvi_evaluate (xs,env,s) with
       (Rval vs,s1) ->
         (match bvl_find_code (SOME dest) vs (bvi_state_code s1) with
            NONE -> (Rerr (Rabort Rtype_error),s1)
          | SOME (args,exp) ->
              if bvi_state_clock s1 < ts + 1
              then (Rerr (Rabort Rtimeout_error),bvi_state_clock_fupd (K 0) s1)
              else BVITMCAUX_lc_post rets y env
                     (bvi_evaluate ([exp],args,bvi_dec_clock (ts + 1) s1)))
     | (Rerr e,s1) -> (Rerr e,s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_evaluate_def] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[BVITMCAUX_lc_post_def] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let BVITMCAUX_result_rel_Ret_inv = prove
 (`!f vs (r2:(bvl_v list,exn_or_ret)result).
     result_rel (ALL2 (bvi_tmcProof_v_rel f)) (eor_rel f) (Rerr (Rraise (Ret vs))) r2 <=>
     ?vs'. r2 = Rerr (Rraise (Ret vs')) /\ ALL2 (bvi_tmcProof_v_rel f) vs vs'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[result_rel_Rerr1; exc_rel_raise1; BVITMCAUX_eor_rel_inv] THEN
  MESON_TAC[]);;

let BVITMCAUX_lc_post_err = prove
 (`!rets y env e (s:(C,FFI)bvi_state).
     ~(?vs. e = Rraise (Ret vs)) ==>
     BVITMCAUX_lc_post rets y env (Rerr e,s) = (Rerr e,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVITMCAUX_lc_post_def] THEN
  REPEAT TOP_CASE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "result"; distinctness "result"]) THEN
  ASM_MESON_TAC[]);;

let BVITMCAUX_letcall_finish = prove
 (`!xs0 rets y env1 env2 (s:(num#C,FFI)bvi_state) (s2:(num#C,FFI)bvi_state)
    (s':(C,FFI)bvi_state) (t2:(C,FFI)bvi_state) cres r2 r t f f2.
     BVITMCAUX_tmc_ih xs0 s /\ bvi_state_clock s2 < bvi_state_clock s /\
     BVITMCAUX_lc_post rets y env1 (cres,s2) = (r,t) /\
     ~(r = Rerr (Rabort Rtype_error)) /\
     result_rel (ALL2 (bvi_tmcProof_v_rel f2)) (eor_rel f2) cres r2 /\
     bvi_tmcProof_state_rel f2 s2 t2 /\
     bvi_tmcProof_env_rel F f env1 env2 /\ no_mutcons y /\
     f SUBMAP f2 /\ only_fresh f f2 (bvi_state_refs s') /\
     holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t2) {} /\
     holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t2) /\
     FDOM (bvi_state_refs s') SUBSET FDOM (bvi_state_refs t2) ==>
     ?t' f' r'. BVITMCAUX_lc_post rets y env2 (r2,t2) = (r',t') /\
       result_rel (ALL2 (bvi_tmcProof_v_rel f')) (eor_rel f') r r' /\
       bvi_tmcProof_state_rel f' t t' /\ f SUBMAP f' /\
       only_fresh f f' (bvi_state_refs s') /\
       holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t') {} /\
       holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:bvl_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)
    (ISPEC `cres:(bvl_v list,exn_or_ret)result` (cases "result")) THENL
   [UNDISCH_TAC `BVITMCAUX_lc_post rets y env1
      (Rval a,s2:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[BVITMCAUX_lc_post_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `?vs. e = Rraise (Ret vs):(exn_or_ret)error_result` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(X_CHOOSE_THEN `e':(exn_or_ret)error_result` STRIP_ASSUME_TAC o
      REWRITE_RULE[result_rel_Rerr1] o check (BVITMCAUX_head_is "result_rel")) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `~(?vs. e' = Rraise (Ret vs):(exn_or_ret)error_result)` ASSUME_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `vs:bvl_v list` SUBST_ALL_TAC) THEN
      UNDISCH_TAC `exc_rel (eor_rel f2) e (Rraise (Ret vs))` THEN
      REWRITE_TAC[exc_rel_raise2] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:exn_or_ret` (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
      CASES_ON `w:exn_or_ret` THEN REWRITE_TAC[eor_rel_def] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `BVITMCAUX_lc_post rets y env1 (Rerr e,s2:(num#C,FFI)bvi_state) = (r,t)` THEN
    ASM_SIMP_TAC[BVITMCAUX_lc_post_err; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`t2:(C,FFI)bvi_state`; `f2:(num,num)fmap`;
                          `Rerr e':(bvl_v list,exn_or_ret)result`] THEN
    ASM_SIMP_TAC[BVITMCAUX_lc_post_err; result_rel_Rerr1; injectivity "result";
                 UNWIND_THM1]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `vs:bvl_v list` SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `vs':bvl_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) o
    REWRITE_RULE[BVITMCAUX_result_rel_Ret_inv] o check (BVITMCAUX_head_is "result_rel")) THEN
  SUBGOAL_THEN `LENGTH (vs:bvl_v list) = rets` ASSUME_TAC THENL
   [UNDISCH_TAC `BVITMCAUX_lc_post rets y env1
      (Rerr (Rraise (Ret vs)),s2:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[BVITMCAUX_lc_post_def] THEN CASE_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bvi_evaluate ([y],APPEND vs env1,s2:(num#C,FFI)bvi_state) = (r,t)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `BVITMCAUX_lc_post rets y env1
      (Rerr (Rraise (Ret vs)),s2:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[BVITMCAUX_lc_post_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "ih" (MP_TAC o SPECL [`[y:bvi_exp]`; `s2:(num#C,FFI)bvi_state`;
    `APPEND vs env1:bvl_v list`; `r:(bvl_v list,exn_or_ret)result`;
    `t:(num#C,FFI)bvi_state`; `F`; `f2:(num,num)fmap`; `t2:(C,FFI)bvi_state`;
    `APPEND vs' env2:bvl_v list`; `0`] o REWRITE_RULE[BVITMCAUX_tmc_ih_def]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[BVITMCAUX_tmc_hyps_def] THEN ASM_REWRITE_TAC[ALL] THEN
    MATCH_MP_TAC bvi_tmcProof_env_rel_append THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC (GEN_ALL env_rel_submap) THEN EXISTS_TAC `f:(num,num)fmap` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)bvi_state` (X_CHOOSE_THEN `f3:(num,num)fmap`
    (X_CHOOSE_THEN `r3:(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC)) o
    REWRITE_RULE[BVITMCAUX_tmc_concl_def]) THEN
  MP_TAC(ISPECL [`f:(num,num)fmap`; `f2:(num,num)fmap`; `f3:(num,num)fmap`;
    `bvi_state_refs (s':(C,FFI)bvi_state)`; `bvi_state_refs (t2:(C,FFI)bvi_state)`;
    `bvi_state_refs (t3:(C,FFI)bvi_state)`; `{}:num->bool`] BVITMCAUX_compose) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t3:(C,FFI)bvi_state`; `f3:(num,num)fmap`;
                        `r3:(bvl_v list,exn_or_ret)result`] THEN
  SUBGOAL_THEN `LENGTH (vs':bvl_v list) = rets` ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC] THEN
  REWRITE_TAC[BVITMCAUX_lc_post_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let BVITMCAUX_tmc_letcall = prove
 (`!rets ts dest xs y env1 (s:(num#C,FFI)bvi_state) r t opt f (s':(C,FFI)bvi_state)
    env2 loc.
     BVITMCAUX_tmc_ih [LetCall rets ts dest xs y] s /\
     BVITMCAUX_tmc_hyps [LetCall rets ts dest xs y] env1 s r t opt f s' env2 ==>
     BVITMCAUX_tmc_concl [LetCall rets ts dest xs y] env1 s r t opt f s' env2 loc`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") ASSUME_TAC) THEN
  MATCH_MP_TAC BVITMCAUX_tmc_plain THEN
  ASM_REWRITE_TAC[rewrite_wrapper_def; rewrite_worker_def] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[BVITMCAUX_tmc_hyps_def] o
    check (BVITMCAUX_head_is "BVITMCAUX_tmc_hyps")) THEN
  SUBGOAL_THEN `no_mutcons y` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\x. no_mutcons x) [LetCall rets ts dest xs y]` THEN
    REWRITE_TAC[ALL; no_mutcons_def] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `bvi_evaluate (xs,env1,s:(num#C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `rx:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `u:(num#C,FFI)bvi_state` ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(rx = Rerr (Rabort Rtype_error):(bvl_v list,exn_or_ret)result)`
    ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `bvi_evaluate ([LetCall rets ts dest xs y],env1,
                               s:(num#C,FFI)bvi_state) = (r,t)` THEN
    ASM_REWRITE_TAC[BVITMCAUX_eval_LetCall] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `bvi_state_clock (u:(num#C,FFI)bvi_state) <=
                bvi_state_clock (s:(num#C,FFI)bvi_state)` ASSUME_TAC THENL
   [ASM_MESON_TAC[bvi_evaluate_clock]; ALL_TAC] THEN
  USE_THEN "ih" (MP_TAC o SPECL [`xs:bvi_exp list`; `s:(num#C,FFI)bvi_state`;
    `env1:bvl_v list`; `rx:(bvl_v list,exn_or_ret)result`; `u:(num#C,FFI)bvi_state`;
    `F`; `f:(num,num)fmap`; `s':(C,FFI)bvi_state`; `env2:bvl_v list`; `loc:num`] o
    REWRITE_RULE[BVITMCAUX_tmc_ih_def]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LE_REFL; BVITMCAUX_tmc_hyps_def] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [DISJ2_TAC THEN BVITMCAUX_SIZE_TAC;
      ASM_MESON_TAC[env_rel_relax_opt];
      UNDISCH_TAC `ALL (\x. no_mutcons x) [LetCall rets ts dest xs y]` THEN
      REWRITE_TAC[ALL; no_mutcons_def; ETA_AX] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':(C,FFI)bvi_state` (X_CHOOSE_THEN `f1:(num,num)fmap`
    (X_CHOOSE_THEN `rx':(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC)) o
    REWRITE_RULE[BVITMCAUX_tmc_concl_def]) THEN
  SUBGOAL_THEN `FDOM (bvi_state_refs (s':(C,FFI)bvi_state)) SUBSET
                FDOM (bvi_state_refs (u':(C,FFI)bvi_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[bvi_tmcProof_evaluate_refs_SUBSET]; ALL_TAC] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs:bvl_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)
    (ISPEC `rx:(bvl_v list,exn_or_ret)result` (cases "result")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[result_rel_Rval; result_rel_Rerr1]) THEN
  REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `bvi_evaluate ([LetCall rets ts dest xs y],env1,
                               s:(num#C,FFI)bvi_state) = (r,t)` THEN
    ASM_REWRITE_TAC[BVITMCAUX_eval_LetCall] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`u':(C,FFI)bvi_state`; `f1:(num,num)fmap`;
                          `Rerr e':(bvl_v list,exn_or_ret)result`] THEN
    ASM_REWRITE_TAC[BVITMCAUX_eval_LetCall] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[result_rel_Rerr1; injectivity "result"; RIGHT_EXISTS_AND_THM;
                    UNWIND_THM1]] THEN
  MP_TAC(ISPEC `bvl_find_code (SOME dest) vs (bvi_state_code (u:(num#C,FFI)bvi_state))`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:bvl_v list#bvi_exp` MP_TAC)) THENL
   [UNDISCH_TAC `bvi_evaluate ([LetCall rets ts dest xs y],env1,
                               s:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[BVITMCAUX_eval_LetCall] THEN BVITMCAUX_ACR_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `p:bvl_v list#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `args:bvl_v list` (X_CHOOSE_THEN `exp:bvi_exp` SUBST1_TAC)) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`f1:(num,num)fmap`; `vs:bvl_v list`; `v':bvl_v list`;
    `u:(num#C,FFI)bvi_state`; `u':(C,FFI)bvi_state`; `SOME dest:num option`;
    `args:bvl_v list`; `exp:bvi_exp`] find_code_rel) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `args':bvl_v list`
    (X_CHOOSE_THEN `body':bvi_exp` (X_CHOOSE_THEN `loc':num` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `bvi_state_clock (u':(C,FFI)bvi_state) =
                bvi_state_clock (u:(num#C,FFI)bvi_state)` ASSUME_TAC THENL
   [ASM_MESON_TAC[bvi_tmcProof_state_rel_def]; ALL_TAC] THEN
  ASM_CASES_TAC `bvi_state_clock (u:(num#C,FFI)bvi_state) < ts + 1` THENL
   [UNDISCH_TAC `bvi_evaluate ([LetCall rets ts dest xs y],env1,
                               s:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[BVITMCAUX_eval_LetCall] THEN BVITMCAUX_ACR_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`bvi_state_clock_fupd (K 0) (u':(C,FFI)bvi_state)`;
      `f1:(num,num)fmap`; `Rerr (Rabort Rtimeout_error):(bvl_v list,exn_or_ret)result`] THEN
    REWRITE_TAC[BVITMCAUX_eval_LetCall] THEN BVITMCAUX_ACR_TAC THEN
    ASM_SIMP_TAC[bvi_tmcProof_state_rel_with_clock; bvi_state_INFO.ri_accfupds;
                 result_rel_def; exc_rel_def];
    ALL_TAC] THEN
  MP_TAC(ISPEC `bvi_evaluate ([exp],args,bvi_dec_clock (ts + 1) (u:(num#C,FFI)bvi_state))`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cres:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `s2:(num#C,FFI)bvi_state` ASSUME_TAC)) THEN
  SUBGOAL_THEN `BVITMCAUX_lc_post rets y env1 (cres,s2:(num#C,FFI)bvi_state) = (r,t)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_evaluate ([LetCall rets ts dest xs y],env1,
                               s:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[BVITMCAUX_eval_LetCall] THEN BVITMCAUX_ACR_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(cres = Rerr (Rabort Rtype_error):(bvl_v list,exn_or_ret)result)`
    ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `BVITMCAUX_lc_post rets y env1
      (Rerr (Rabort Rtype_error),s2:(num#C,FFI)bvi_state) = (r,t)` THEN
    REWRITE_TAC[BVITMCAUX_lc_post_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?t2 f2 r2. bvi_evaluate ([body'],args',bvi_dec_clock (ts + 1) (u':(C,FFI)bvi_state)) =
               (r2,t2) /\
               result_rel (ALL2 (bvi_tmcProof_v_rel f2)) (eor_rel f2) cres r2 /\
               bvi_tmcProof_state_rel f2 s2 t2 /\ f1 SUBMAP f2 /\
               only_fresh f1 f2 (bvi_state_refs u') /\
               holes_unchanged_except f1 (bvi_state_refs u') (bvi_state_refs t2) {} /\
               holes_still_not_finalised f1 (bvi_state_refs u') (bvi_state_refs t2)`
    STRIP_ASSUME_TAC THENL
   [USE_THEN "ih" (MP_TAC o SPECL [`[exp:bvi_exp]`;
      `bvi_dec_clock (ts + 1) (u:(num#C,FFI)bvi_state)`; `args:bvl_v list`;
      `cres:(bvl_v list,exn_or_ret)result`; `s2:(num#C,FFI)bvi_state`; `F`;
      `f1:(num,num)fmap`; `bvi_dec_clock (ts + 1) (u':(C,FFI)bvi_state)`;
      `args':bvl_v list`; `loc':num`] o REWRITE_RULE[BVITMCAUX_tmc_ih_def]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[BVITMCAUX_tmc_hyps_def; BVITMCAUX_dec_clock_simps] THEN
      ASM_REWRITE_TAC[ALL] THEN REPEAT CONJ_TAC THEN
      TRY(DISJ1_TAC THEN ASM_ARITH_TAC) THEN
      MATCH_MP_TAC BVITMCAUX_state_rel_dec_clock THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)bvi_state` (X_CHOOSE_THEN `f3:(num,num)fmap`
      (X_CHOOSE_THEN `r3:(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC)) o
      REWRITE_RULE[BVITMCAUX_tmc_concl_def; BVITMCAUX_dec_clock_simps; HD; LENGTH;
                   ARITH_RULE `SUC 0 = 1`]) THEN
    ASM_CASES_TAC `exp:bvi_exp = body'` THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
      MAP_EVERY EXISTS_TAC [`t3:(C,FFI)bvi_state`; `f3:(num,num)fmap`;
                            `r3:(bvl_v list,exn_or_ret)result`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC (MP th (ASSUME `~(exp:bvi_exp = body')`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `loc_opt:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `loc_opt:num` o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "loc_opt" with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `body':bvi_exp`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `tw:(C,FFI)bvi_state` (X_CHOOSE_THEN `fw:(num,num)fmap`
      (X_CHOOSE_THEN `rw:(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`tw:(C,FFI)bvi_state`; `fw:(num,num)fmap`;
                          `rw:(bvl_v list,exn_or_ret)result`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:(num,num)fmap`; `f1:(num,num)fmap`; `f2:(num,num)fmap`;
    `bvi_state_refs (s':(C,FFI)bvi_state)`; `bvi_state_refs (u':(C,FFI)bvi_state)`;
    `bvi_state_refs (t2:(C,FFI)bvi_state)`; `{}:num->bool`] BVITMCAUX_compose) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FDOM (bvi_state_refs (s':(C,FFI)bvi_state)) SUBSET
                FDOM (bvi_state_refs (t2:(C,FFI)bvi_state))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `FDOM (bvi_state_refs (u':(C,FFI)bvi_state))` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`[body':bvi_exp]`; `args':bvl_v list`;
      `bvi_dec_clock (ts + 1) (u':(C,FFI)bvi_state)`;
      `r2:(bvl_v list,exn_or_ret)result`; `t2:(C,FFI)bvi_state`]
      bvi_tmcProof_evaluate_refs_SUBSET) THEN
    ASM_REWRITE_TAC[BVITMCAUX_dec_clock_simps]; ALL_TAC] THEN
  MP_TAC(ISPECL [`[LetCall rets ts dest xs y]`; `rets:num`; `y:bvi_exp`;
    `env1:bvl_v list`; `env2:bvl_v list`; `s:(num#C,FFI)bvi_state`;
    `s2:(num#C,FFI)bvi_state`; `s':(C,FFI)bvi_state`; `t2:(C,FFI)bvi_state`;
    `cres:(bvl_v list,exn_or_ret)result`; `r2:(bvl_v list,exn_or_ret)result`;
    `r:(bvl_v list,exn_or_ret)result`; `t:(num#C,FFI)bvi_state`; `f:(num,num)fmap`;
    `f2:(num,num)fmap`] BVITMCAUX_letcall_finish) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`[exp:bvi_exp]`; `args:bvl_v list`;
        `bvi_dec_clock (ts + 1) (u:(num#C,FFI)bvi_state)`;
        `cres:(bvl_v list,exn_or_ret)result`; `s2:(num#C,FFI)bvi_state`]
        bvi_evaluate_clock) THEN
      ASM_REWRITE_TAC[BVITMCAUX_dec_clock_simps] THEN ASM_ARITH_TAC;
      ASM_MESON_TAC[env_rel_relax_opt]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':(C,FFI)bvi_state` (X_CHOOSE_THEN `f':(num,num)fmap`
    (X_CHOOSE_THEN `r':(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`t':(C,FFI)bvi_state`; `f':(num,num)fmap`;
                        `r':(bvl_v list,exn_or_ret)result`] THEN
  REWRITE_TAC[BVITMCAUX_eval_LetCall] THEN BVITMCAUX_ACR_TAC);;

let BVITMCAUX_eval_to_cb = prove
 (`!cb n loc x env (s:(C,FFI)bvi_state) bs.
     bvi_to_cb n loc x = SOME (bs,cb) /\ n <= LENGTH env ==>
     bvi_evaluate ([x],env,s) = bvi_evaluate ([bvi_Let bs (cb_to_bvi loc cb)],env,s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `bvi_evaluate ([x],env,s:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `t:(C,FFI)bvi_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC evaluate_bvi_to_cb THEN MAP_EVERY EXISTS_TAC [`n:num`; `x:bvi_exp`] THEN
  ASM_REWRITE_TAC[]);;

let BVITMCAUX_worker_to_cb = prove
 (`!n loc x bs cb loc_opt i j.
     bvi_to_cb n loc x = SOME (bs,cb) ==>
     rewrite_worker loc loc_opt i j n x =
     bvi_Let bs (cb_to_bvi_worker cb loc_opt (LENGTH bs + i) (LENGTH bs + j))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN
    (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC)) o MATCH_MP bvi_to_cb_cases) THEN
  ASM_REWRITE_TAC[rewrite_worker_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF]);;

let BVITMCAUX_wrapper_to_cb = prove
 (`!n loc x bs cb loc_opt w.
     bvi_to_cb n loc x = SOME (bs,cb) /\ rewrite_wrapper loc loc_opt n x = SOME w ==>
     ?tag left child right.
       cb = CallBlock tag left child right /\
       w = bvi_Let bs (cb_to_bvi_wrapper tag left child right loc_opt)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN
    (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC)) o MATCH_MP bvi_to_cb_cases) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `w:bvi_exp` (concl th))) THEN
  ASM_REWRITE_TAC[rewrite_wrapper_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ; distinctness "option"; injectivity "call_block"] THEN
  MESON_TAC[]);;

let BVITMCAUX_tmc_cb_val = prove
 (`!x bs cb av av' env1 (s:(num#C,FFI)bvi_state) u r t opt f f1 (s':(C,FFI)bvi_state) u'
    env2 loc.
     bvi_to_cb (LENGTH env1) loc x = SOME (bs,cb) /\
     bvi_evaluate (bs,env1,s) = (Rval av,u) /\
     bvi_evaluate (bs,env2,s') = (Rval av',u') /\
     bvi_evaluate ([cb_to_bvi loc cb],APPEND av env1,u) = (r,t) /\
     ~(r = Rerr (Rabort Rtype_error)) /\
     ALL2 (bvi_tmcProof_v_rel f1) av av' /\
     bvi_tmcProof_env_rel opt f env1 env2 /\
     bvi_tmcProof_state_rel f1 u u' /\
     f SUBMAP f1 /\ only_fresh f f1 (bvi_state_refs s') /\
     holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs u') {} /\
     holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs u') /\
     bvi_state_clock u <= bvi_state_clock s /\
     (!xs' (s'':(num#C,FFI)bvi_state). hypothesis xs' s'' (bvi_state_clock s)) ==>
     BVITMCAUX_tmc_concl [x] env1 s r t opt f s' env2 loc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (bs:bvi_exp list) = LENGTH (av:bvl_v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[bvi_evaluate_IMP_LENGTH]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (av':bvl_v list) = LENGTH (av:bvl_v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`cb:call_block`; `loc:num`; `f1:(num,num)fmap`; `opt:bool`;
    `APPEND av env1:bvl_v list`; `APPEND av' env2:bvl_v list`; `u:(num#C,FFI)bvi_state`;
    `u':(C,FFI)bvi_state`; `t:(num#C,FFI)bvi_state`; `r:(bvl_v list,exn_or_ret)result`;
    `bvi_state_clock (s:(num#C,FFI)bvi_state)`] evaluate_cb) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC wf_cb_expand THEN EXISTS_TAC `LENGTH (bs:bvi_exp list)` THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[bvi_to_cb_wf];
        ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC];
      MATCH_MP_TAC bvi_tmcProof_env_rel_append THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC (GEN_ALL env_rel_submap) THEN EXISTS_TAC `f:(num,num)fmap` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `r2:(bvl_v list,exn_or_ret)result` (X_CHOOSE_THEN `t2:(C,FFI)bvi_state`
      (X_CHOOSE_THEN `f2:(num,num)fmap` STRIP_ASSUME_TAC)))
    (LABEL_TAC "cbopt")) THEN
  SUBGOAL_THEN `FDOM (bvi_state_refs (s':(C,FFI)bvi_state)) SUBSET
                FDOM (bvi_state_refs (u':(C,FFI)bvi_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[bvi_tmcProof_evaluate_refs_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:(num,num)fmap`; `f1:(num,num)fmap`; `f2:(num,num)fmap`;
    `bvi_state_refs (s':(C,FFI)bvi_state)`; `bvi_state_refs (u':(C,FFI)bvi_state)`;
    `bvi_state_refs (t2:(C,FFI)bvi_state)`; `{}:num->bool`] BVITMCAUX_compose) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (env1:bvl_v list) <= LENGTH (env2:bvl_v list)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP bvi_tmcProof_env_rel_length) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[BVITMCAUX_tmc_concl_def; HD; LENGTH; ARITH_RULE `SUC 0 = 1`] THEN
  MAP_EVERY EXISTS_TAC [`t2:(C,FFI)bvi_state`; `f2:(num,num)fmap`;
                        `r2:(bvl_v list,exn_or_ret)result`] THEN
  MP_TAC(ISPECL [`cb:call_block`; `LENGTH (env1:bvl_v list)`; `loc:num`; `x:bvi_exp`;
    `env2:bvl_v list`; `s':(C,FFI)bvi_state`; `bs:bvi_exp list`] BVITMCAUX_eval_to_cb) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_Let_Rval th]) o
    check (fun th -> is_eq (concl th) && free_in `env2:bvl_v list` (concl th) &&
                     free_in `bs:bvi_exp list` (concl th) &&
                     not (free_in `cb:call_block` (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `loc_opt:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `optimised_code loc loc_opt (bvi_state_code (u:(num#C,FFI)bvi_state))
                  (bvi_state_code (u':(C,FFI)bvi_state))` ASSUME_TAC THENL
   [MATCH_MP_TAC evaluate_pres_opt_code THEN
    MAP_EVERY EXISTS_TAC [`s:(num#C,FFI)bvi_state`; `s':(C,FFI)bvi_state`;
      `bs:bvi_exp list`; `env1:bvl_v list`; `env2:bvl_v list`;
      `Rval av:(bvl_v list,exn_or_ret)result`;
      `Rval av':(bvl_v list,exn_or_ret)result`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "cbopt" (MP_TAC o SPEC `loc_opt:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cbw")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "cbk"))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `wrap:bvi_exp` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`LENGTH (env1:bvl_v list)`; `loc:num`; `x:bvi_exp`; `bs:bvi_exp list`;
      `cb:call_block`; `loc_opt:num`; `wrap:bvi_exp`] BVITMCAUX_wrapper_to_cb) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `tag:num` (X_CHOOSE_THEN `left:num list`
      (X_CHOOSE_THEN `child:call_block` (X_CHOOSE_THEN `right:num list`
        (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC))))) THEN
    REMOVE_THEN "cbw" (MP_TAC o SPECL [`tag:num`; `left:num list`; `child:call_block`;
                                       `right:num list`]) THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `tw:(C,FFI)bvi_state` (X_CHOOSE_THEN `fw:(num,num)fmap`
      (X_CHOOSE_THEN `rw:(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`f:(num,num)fmap`; `f1:(num,num)fmap`; `fw:(num,num)fmap`;
      `bvi_state_refs (s':(C,FFI)bvi_state)`; `bvi_state_refs (u':(C,FFI)bvi_state)`;
      `bvi_state_refs (tw:(C,FFI)bvi_state)`; `{}:num->bool`] BVITMCAUX_compose) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`tw:(C,FFI)bvi_state`; `fw:(num,num)fmap`;
                          `rw:(bvl_v list,exn_or_ret)result`] THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_Let_Rval th]) o
      check (fun th -> is_eq (concl th) && free_in `env2:bvl_v list` (concl th) &&
                       free_in `bs:bvi_exp list` (concl th) &&
                       not (free_in `tag:num` (concl th)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `hole_ptr:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o EQT_INTRO o check (fun th -> concl th = `opt:bool`)) THEN
  MP_TAC(ISPECL [`LENGTH (env1:bvl_v list)`; `loc:num`; `x:bvi_exp`; `bs:bvi_exp list`;
    `cb:call_block`; `loc_opt:num`; `LENGTH (env1:bvl_v list)`;
    `LENGTH (env1:bvl_v list) + 1`] BVITMCAUX_worker_to_cb) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_Let_Rval th]) o
    check (fun th -> is_eq (concl th) && free_in `env2:bvl_v list` (concl th) &&
                     free_in `bs:bvi_exp list` (concl th) &&
                     not (free_in `cb:call_block` (concl th)))) THEN
  MP_TAC(ISPECL [`f:(num,num)fmap`; `f1:(num,num)fmap`; `env1:bvl_v list`;
    `env2:bvl_v list`; `bvi_state_refs (s':(C,FFI)bvi_state)`;
    `bvi_state_refs (u':(C,FFI)bvi_state)`; `c:bvl_v`; `hole_ptr:num`]
    BVITMCAUX_hole_transport) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "cbk" (MP_TAC o SPECL [`LENGTH (av:bvl_v list) + LENGTH (env1:bvl_v list)`;
    `LENGTH (av:bvl_v list) + LENGTH (env1:bvl_v list) + 1`;
    `hole_ptr:num`] o REWRITE_RULE[]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_APPEND];
      ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
      EXISTS_TAC `c:bvl_v` THEN MATCH_MP_TAC hole_has_val_append THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[EL_APPEND; ARITH_RULE `~(a + b < a:num) /\ (a + b) - a = b`]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rw:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `fw:(num,num)fmap` (X_CHOOSE_THEN `tw:(C,FFI)bvi_state`
      STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`f:(num,num)fmap`; `f1:(num,num)fmap`; `fw:(num,num)fmap`;
    `bvi_state_refs (s':(C,FFI)bvi_state)`; `bvi_state_refs (u':(C,FFI)bvi_state)`;
    `bvi_state_refs (tw:(C,FFI)bvi_state)`; `{hole_ptr:num}`] BVITMCAUX_compose) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`rw:(bvl_v list,exn_or_ret)result`; `fw:(num,num)fmap`;
                        `tw:(C,FFI)bvi_state`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `res_v:bvl_v` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `res_v:bvl_v` o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "res_v" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `res_v':bvl_v` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `res_v':bvl_v` THEN CONJ_TAC THENL
   [MATCH_MP_TAC mb_rel_refs_old_subset THEN
    EXISTS_TAC `bvi_state_refs (u':(C,FFI)bvi_state)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC hole_has_val_submap THEN EXISTS_TAC `f1:(num,num)fmap` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC (MATCH_MP hole_has_val_unappend
      (CONJ th (ASSUME `ALL2 (bvi_tmcProof_v_rel f1) av av'`))))]);;

let BVITMCAUX_tmc_cb = prove
 (`!x bs cb env1 (s:(num#C,FFI)bvi_state) r t opt f (s':(C,FFI)bvi_state) env2 loc.
     BVITMCAUX_tmc_ih [x] s /\
     BVITMCAUX_tmc_hyps [x] env1 s r t opt f s' env2 /\
     bvi_to_cb (LENGTH env1) loc x = SOME (bs,cb) ==>
     BVITMCAUX_tmc_concl [x] env1 s r t opt f s' env2 loc`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[BVITMCAUX_tmc_hyps_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `bvi_evaluate ([bvi_Let bs (cb_to_bvi loc cb)],env1,
                              s:(num#C,FFI)bvi_state) = (r,t)` ASSUME_TAC THENL
   [MATCH_MP_TAC evaluate_bvi_to_cb THEN
    MAP_EVERY EXISTS_TAC [`LENGTH (env1:bvl_v list)`; `x:bvi_exp`] THEN
    ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  MP_TAC(ISPEC `bvi_evaluate (bs,env1,s:(num#C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `rb:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `u:(num#C,FFI)bvi_state` ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(rb = Rerr (Rabort Rtype_error):(bvl_v list,exn_or_ret)result)`
    ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `bvi_evaluate ([bvi_Let bs (cb_to_bvi loc cb)],env1,
                               s:(num#C,FFI)bvi_state) = (r,t)` THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_Let_Rerr th]) o
      check (fun th -> is_eq (concl th) && free_in `env1:bvl_v list` (concl th) &&
                       free_in `bs:bvi_exp list` (concl th) &&
                       not (free_in `cb:call_block` (concl th)))) THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\x. no_mutcons x) (bs:bvi_exp list)` ASSUME_TAC THENL
   [MATCH_MP_TAC bvi_to_cb_no_mutcons THEN
    MAP_EVERY EXISTS_TAC [`cb:call_block`; `LENGTH (env1:bvl_v list)`; `loc:num`;
                          `x:bvi_exp`] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `ALL (\x. no_mutcons x) [x:bvi_exp]` THEN
    REWRITE_TAC[ALL] THEN SIMP_TAC[]; ALL_TAC] THEN
  USE_THEN "ih" (MP_TAC o SPECL [`bs:bvi_exp list`; `s:(num#C,FFI)bvi_state`;
    `env1:bvl_v list`; `rb:(bvl_v list,exn_or_ret)result`; `u:(num#C,FFI)bvi_state`;
    `F`; `f:(num,num)fmap`; `s':(C,FFI)bvi_state`; `env2:bvl_v list`; `loc:num`] o
    REWRITE_RULE[BVITMCAUX_tmc_ih_def]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LE_REFL; BVITMCAUX_tmc_hyps_def] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [DISJ2_TAC THEN
      MP_TAC(ISPECL [`LENGTH (env1:bvl_v list)`; `loc:num`; `x:bvi_exp`;
        `bs:bvi_exp list`; `cb:call_block`] bvi_to_cb_size) THEN
      ASM_REWRITE_TAC[list_size] THEN ARITH_TAC;
      ASM_MESON_TAC[env_rel_relax_opt]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':(C,FFI)bvi_state` (X_CHOOSE_THEN `f1:(num,num)fmap`
    (X_CHOOSE_THEN `rb':(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC)) o
    REWRITE_RULE[BVITMCAUX_tmc_concl_def]) THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `av:bvl_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)
    (ISPEC `rb:(bvl_v list,exn_or_ret)result` (cases "result")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[result_rel_Rval; result_rel_Rerr1]) THEN
  REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THENL
   [SUBGOAL_THEN `bvi_evaluate ([cb_to_bvi loc cb],APPEND av env1,
                                u:(num#C,FFI)bvi_state) = (r,t)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
        rhs (concl th) = `(r:(bvl_v list,exn_or_ret)result,t:(num#C,FFI)bvi_state)` &&
        free_in `cb:call_block` (concl th))) THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC BVITMCAUX_eval_Let_Rval THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `bvi_state_clock (u:(num#C,FFI)bvi_state) <=
                  bvi_state_clock (s:(num#C,FFI)bvi_state)` ASSUME_TAC THENL
     [ASM_MESON_TAC[bvi_evaluate_clock]; ALL_TAC] THEN
    MP_TAC(MATCH_MP BVITMCAUX_tmc_ih_hypothesis
      (ASSUME `BVITMCAUX_tmc_ih [x:bvi_exp] (s:(num#C,FFI)bvi_state)`)) THEN
    DISCH_TAC THEN
    MATCH_MP_TAC BVITMCAUX_tmc_cb_val THEN
    MAP_EVERY EXISTS_TAC [`bs:bvi_exp list`; `cb:call_block`; `av:bvl_v list`;
      `v':bvl_v list`; `u:(num#C,FFI)bvi_state`; `f1:(num,num)fmap`;
      `u':(C,FFI)bvi_state`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `bvi_evaluate ([bvi_Let bs (cb_to_bvi loc cb)],env1,
                             s:(num#C,FFI)bvi_state) = (r,t)` THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_Let_Rerr th]) o
    check (fun th -> is_eq (concl th) && free_in `env1:bvl_v list` (concl th) &&
                     free_in `bs:bvi_exp list` (concl th) &&
                     not (free_in `cb:call_block` (concl th)))) THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  SUBGOAL_THEN `LENGTH (env1:bvl_v list) <= LENGTH (env2:bvl_v list)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP bvi_tmcProof_env_rel_length) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[BVITMCAUX_tmc_concl_def; HD; LENGTH; ARITH_RULE `SUC 0 = 1`] THEN
  MP_TAC(ISPECL [`cb:call_block`; `LENGTH (env1:bvl_v list)`; `loc:num`; `x:bvi_exp`;
    `env2:bvl_v list`; `s':(C,FFI)bvi_state`; `bs:bvi_exp list`] BVITMCAUX_eval_to_cb) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_Let_Rerr th]) o
    check (fun th -> is_eq (concl th) && free_in `env2:bvl_v list` (concl th) &&
                     free_in `bs:bvi_exp list` (concl th) &&
                     not (free_in `cb:call_block` (concl th)))) THEN
  MAP_EVERY EXISTS_TAC [`u':(C,FFI)bvi_state`; `f1:(num,num)fmap`;
                        `Rerr e':(bvl_v list,exn_or_ret)result`] THEN
  ASM_REWRITE_TAC[result_rel_Rerr1; injectivity "result"; RIGHT_EXISTS_AND_THM;
                  UNWIND_THM1] THEN
  X_GEN_TAC `loc_opt:num` THEN DISCH_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `wrap:bvi_exp` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`LENGTH (env1:bvl_v list)`; `loc:num`; `x:bvi_exp`; `bs:bvi_exp list`;
      `cb:call_block`; `loc_opt:num`; `wrap:bvi_exp`] BVITMCAUX_wrapper_to_cb) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `tag:num` (X_CHOOSE_THEN `left:num list`
      (X_CHOOSE_THEN `child:call_block` (X_CHOOSE_THEN `right:num list`
        (CONJUNCTS_THEN2 (K ALL_TAC) SUBST1_TAC))))) THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_Let_Rerr th]) o
      check (fun th -> is_eq (concl th) && free_in `env2:bvl_v list` (concl th) &&
                       free_in `bs:bvi_exp list` (concl th) &&
                       not (free_in `cb:call_block` (concl th)))) THEN
    MAP_EVERY EXISTS_TAC [`u':(C,FFI)bvi_state`; `f1:(num,num)fmap`;
                          `Rerr e':(bvl_v list,exn_or_ret)result`] THEN
    ASM_REWRITE_TAC[result_rel_Rerr1; injectivity "result"; RIGHT_EXISTS_AND_THM;
                    UNWIND_THM1];
    DISCH_TAC THEN X_GEN_TAC `hole_ptr:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`LENGTH (env1:bvl_v list)`; `loc:num`; `x:bvi_exp`; `bs:bvi_exp list`;
      `cb:call_block`; `loc_opt:num`; `LENGTH (env1:bvl_v list)`;
      `LENGTH (env1:bvl_v list) + 1`] BVITMCAUX_worker_to_cb) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP BVITMCAUX_eval_Let_Rerr th]) o
      check (fun th -> is_eq (concl th) && free_in `env2:bvl_v list` (concl th) &&
                       free_in `bs:bvi_exp list` (concl th) &&
                       not (free_in `cb:call_block` (concl th)))) THEN
    MAP_EVERY EXISTS_TAC [`Rerr e':(bvl_v list,exn_or_ret)result`; `f1:(num,num)fmap`;
                          `u':(C,FFI)bvi_state`] THEN
    ASM_REWRITE_TAC[opt_res_rel_def; injectivity "result"; distinctness "result"] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC holes_unchanged_except_subset THEN
    EXISTS_TAC `{}:num->bool` THEN ASM_REWRITE_TAC[EMPTY_SUBSET]]);;

let BVITMCAUX_tmc_cases = prove
 (`!xs (s:(num#C,FFI)bvi_state) env1 r t opt f (s':(C,FFI)bvi_state) env2 loc.
     BVITMCAUX_tmc_ih xs s /\ BVITMCAUX_tmc_hyps xs env1 s r t opt f s' env2 ==>
     BVITMCAUX_tmc_concl xs env1 s r t opt f s' env2 loc`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `xs:bvi_exp list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `h:bvi_exp`
    (X_CHOOSE_THEN `tl:bvi_exp list` SUBST1_TAC))) THENL
   [MESON_TAC[BVITMCAUX_tmc_nil]; ALL_TAC] THEN
  MP_TAC(ISPEC `tl:bvi_exp list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `h2:bvi_exp`
    (X_CHOOSE_THEN `tl2:bvi_exp list` SUBST1_TAC))) THENL
   [ALL_TAC; MATCH_ACCEPT_TAC BVITMCAUX_tmc_list] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `?bs cb. bvi_to_cb (LENGTH (env1:bvl_v list)) loc h = SOME (bs,cb)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `bs:bvi_exp list` (X_CHOOSE_TAC `cb:call_block`)) THEN
    MATCH_MP_TAC BVITMCAUX_tmc_cb THEN
    MAP_EVERY EXISTS_TAC [`bs:bvi_exp list`; `cb:call_block`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bvi_to_cb (LENGTH (env1:bvl_v list)) loc h = NONE` ASSUME_TAC THENL
   [MP_TAC(ISPEC `bvi_to_cb (LENGTH (env1:bvl_v list)) loc h` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[PAIR_SURJECTIVE];
    ALL_TAC] THEN
  CASES_ON `h:bvi_exp` THEN
  FIRST (map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC)
    [BVITMCAUX_tmc_var; BVITMCAUX_tmc_if; BVITMCAUX_tmc_let; BVITMCAUX_tmc_raise;
     BVITMCAUX_tmc_tick; BVITMCAUX_tmc_call; BVITMCAUX_tmc_force; BVITMCAUX_tmc_op;
     BVITMCAUX_tmc_letcall; BVITMCAUX_tmc_return]));;

let BVITMCAUX_tmc_all = MATCH_MP BVITMCAUX_tmc_wf BVITMCAUX_tmc_cases;;

(* HOL4 line 2945; proved here at the place of its Finalise (HOL4 line 5871) *)
let evaluate_rewrite_tmc = prove
 (`!n xs (s:(num#C,FFI)bvi_state) env1 r t opt f (s':(C,FFI)bvi_state) env2 loc.
     bvi_evaluate (xs,env1,s) = (r,t) /\
     n = (bvi_state_clock s,list_size bvi_exp_size xs) /\
     bvi_tmcProof_env_rel opt f env1 env2 /\ ALL (\x. no_mutcons x) xs /\
     bvi_tmcProof_state_rel f s s' /\
     (opt ==> LENGTH xs = 1) /\
     ~(r = Rerr (Rabort Rtype_error)) ==>
     ?t' f' r'.
       bvi_evaluate (xs,env2,s') = (r',t') /\
       result_rel (ALL2 (bvi_tmcProof_v_rel f')) (eor_rel f') r r' /\
       bvi_tmcProof_state_rel f' t t' /\
       f SUBMAP f' /\
       only_fresh f f' (bvi_state_refs s') /\
       holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t') {} /\
       holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t') /\
       (!loc_opt.
          optimised_code loc loc_opt (bvi_state_code s) (bvi_state_code s') ==>
          (!wrap.
             LENGTH xs = 1 /\
             rewrite_wrapper loc loc_opt (LENGTH env1) (HD xs) = SOME wrap ==>
             ?t_wrap f_wrap r_wrap.
               bvi_evaluate ([wrap],env2,s') = (r_wrap,t_wrap) /\
               result_rel (ALL2 (bvi_tmcProof_v_rel f_wrap)) (eor_rel f_wrap) r r_wrap /\
               bvi_tmcProof_state_rel f_wrap t t_wrap /\
               f SUBMAP f_wrap /\
               only_fresh f f_wrap (bvi_state_refs s') /\
               holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t_wrap) {} /\
               holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t_wrap)) /\
          (opt ==>
           (!i j hole_ptr work.
              i = LENGTH env1 /\
              j = LENGTH env1 + 1 /\
              (?c. hole_has_val f env1 env2 (bvi_state_refs s') c) /\
              hole_not_finalised (bvi_state_refs s') hole_ptr /\
              rewrite_worker loc loc_opt i j (LENGTH env1) (HD xs) = work /\
              EL i env2 = bvl_RefPtr F hole_ptr ==>
              ?r_work f_work t_work.
                bvi_evaluate ([work],env2,s') = (r_work,t_work) /\
                opt_res_rel f_work r r_work /\
                bvi_tmcProof_state_rel f_work t t_work /\
                f SUBMAP f_work /\
                only_fresh f f_work (bvi_state_refs s') /\
                holes_unchanged_except f (bvi_state_refs s') (bvi_state_refs t_work)
                  {hole_ptr} /\
                holes_still_not_finalised f (bvi_state_refs s') (bvi_state_refs t_work) /\
                !res_v.
                  r = Rval [res_v] ==>
                  ?res_v'.
                    mb_rel f_work (bvi_state_refs s') (bvi_state_refs t_work \\ hole_ptr)
                      res_v res_v' /\
                    hole_has_val f env1 env2 (bvi_state_refs t_work) res_v')))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`xs:bvi_exp list`; `s:(num#C,FFI)bvi_state`; `env1:bvl_v list`;
    `r:(bvl_v list,exn_or_ret)result`; `t:(num#C,FFI)bvi_state`; `opt:bool`;
    `f:(num,num)fmap`; `s':(C,FFI)bvi_state`; `env2:bvl_v list`; `loc:num`]
    BVITMCAUX_tmc_all) THEN
  ASM_REWRITE_TAC[BVITMCAUX_tmc_hyps_def; BVITMCAUX_tmc_concl_def] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t':(C,FFI)bvi_state` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f':(num,num)fmap` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r':(bvl_v list,exn_or_ret)result` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `loc_opt:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `loc_opt:num` o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "loc_opt" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `hole_ptr:num`; `work:bvi_exp`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `hole_ptr:num` o C MP (ASSUME `opt:bool`)) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 5873 *)
let bvi_tmcProof_evaluate_compile_each = prove
 (`!next prog (co:num -> (num#C) # (num#num#bvi_exp) list) start (ffi0:(FFI)ffi_state)
    (cc:C -> (num#num#bvi_exp) list -> (byte list # int64 list # C) option) k r
    (s:(num#C,FFI)bvi_state).
     bvi_tmcProof_input_condition next prog /\
     (!n next cfg prog. co n = ((next,cfg),prog) ==>
                        bvi_tmcProof_input_condition next prog) /\
     (!n. MEM n (MAP FST (SND (bvi_tmc_compile_each next prog))) /\
          n MOD bvl_to_bvi_namespaces = 3 ==> n < FST (FST (co 0))) /\
     bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                   bvi_initial_state ffi0 (fromAList prog) co
                     (state_cc bvi_tmc_compile_each cc) k) = (r,s) /\
     ~(r = Rerr (Rabort Rtype_error)) ==>
     ?f s2 r2.
       bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                     bvi_initial_state ffi0 (fromAList (SND (bvi_tmc_compile_each next prog)))
                       (state_co bvi_tmc_compile_each co) cc k) = (r2,s2) /\
       result_rel (ALL2 (bvi_tmcProof_v_rel f)) (eor_rel f) r r2 /\
       bvi_tmcProof_state_rel f s s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `bvi_tmc_compile_each next prog` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:num` (X_CHOOSE_THEN `prog2:(num#num#bvi_exp)list`
    ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "MEM")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bvi_tmcProof_input_condition_def] o
    check (fun th ->
      concl th = `bvi_tmcProof_input_condition next (prog:(num#num#bvi_exp)list)`)) THEN
  SUBGOAL_THEN
   `bvi_tmcProof_state_rel FEMPTY
      (bvi_initial_state (ffi0:(FFI)ffi_state) (fromAList prog)
         (co:num -> (num#C) # (num#num#bvi_exp) list)
         (state_cc bvi_tmc_compile_each
           (cc:C -> (num#num#bvi_exp) list -> (byte list # int64 list # C) option)) k)
      (bvi_initial_state ffi0 (fromAList prog2) (state_co bvi_tmc_compile_each co) cc k)`
    ASSUME_TAC THENL
   [REWRITE_TAC[bvi_tmcProof_state_rel_def; bvi_initial_state_def;
                bvi_state_INFO.ri_accessors] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF; pair_CASE_def] THEN BETA_TAC THEN
    REWRITE_TAC[state_ref_rel_def; FDOM_FEMPTY; FLOOKUP_EMPTY; distinctness "option";
                OPTREL_THM; fmap_inj_FEMPTY] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(INST [`n2:num`,`next1:num`] bvi_tmcProof_compile_each_code_rel) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(INST [`n2:num`,`next1:num`]
                        bvi_tmcProof_compile_each_namespace_rel) THEN
      ASM_REWRITE_TAC[];
      GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC
        [`n:num`; `SND (FST ((co:num -> (num#C) # (num#num#bvi_exp) list) n))`] THEN
      REWRITE_TAC[PAIR];
      ASM_REWRITE_TAC[domain_fromAList; IN_SET_OF_LIST]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(bvi_state_clock (bvi_initial_state (ffi0:(FFI)ffi_state) (fromAList prog)
         (co:num -> (num#C) # (num#num#bvi_exp) list)
         (state_cc bvi_tmc_compile_each
           (cc:C -> (num#num#bvi_exp) list -> (byte list # int64 list # C) option)) k),
      list_size bvi_exp_size [bvi_Call 0 (SOME start) [] NONE])`;
    `[bvi_Call 0 (SOME start) [] NONE]`;
    `bvi_initial_state (ffi0:(FFI)ffi_state) (fromAList prog)
         (co:num -> (num#C) # (num#num#bvi_exp) list)
         (state_cc bvi_tmc_compile_each
           (cc:C -> (num#num#bvi_exp) list -> (byte list # int64 list # C) option)) k`;
    `[]:bvl_v list`; `r:(bvl_v list,exn_or_ret)result`; `s:(num#C,FFI)bvi_state`; `F`;
    `FEMPTY:(num,num)fmap`;
    `bvi_initial_state (ffi0:(FFI)ffi_state) (fromAList prog2)
         (state_co bvi_tmc_compile_each (co:num -> (num#C) # (num#num#bvi_exp) list))
         (cc:C -> (num#num#bvi_exp) list -> (byte list # int64 list # C) option) k`;
    `[]:bvl_v list`; `start:num`] evaluate_rewrite_tmc) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ALL; no_mutcons_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[bvi_tmcProof_env_rel_def] THEN
    MAP_EVERY EXISTS_TAC [`[]:bvl_v list`; `[]:bvl_v list`] THEN REWRITE_TAC[APPEND; ALL2];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(C,FFI)bvi_state` (X_CHOOSE_THEN `f2:(num,num)fmap`
    (X_CHOOSE_THEN `r2:(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`f2:(num,num)fmap`; `s2:(C,FFI)bvi_state`;
                        `r2:(bvl_v list,exn_or_ret)result`] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 5923 *)
let bvi_tmcProof_state_rel_const = prove
 (`!f (s:(num#C,FFI)bvi_state) (t:(C,FFI)bvi_state).
     bvi_tmcProof_state_rel f s t ==>
     bvi_state_clock t = bvi_state_clock s /\ bvi_state_ffi t = bvi_state_ffi s`,
  SIMP_TAC[bvi_tmcProof_state_rel_def]);;

(* local helpers for the semantics theorems *)

let BVITMCAUX_triv_rel_cases = prove
 (`!(r1:(bvl_v list,exn_or_ret)result) r2.
     result_rel (\x:bvl_v list y:bvl_v list. T) (\x:exn_or_ret y:exn_or_ret. T) r1 r2 <=>
     (?a b. r1 = Rval a /\ r2 = Rval b) \/
     (?x y. r1 = Rerr (Rraise x) /\ r2 = Rerr (Rraise y)) \/
     (?a. r1 = Rerr (Rabort a) /\ r2 = Rerr (Rabort a))`,
  GEN_TAC THEN CASES_ON `r1:(bvl_v list,exn_or_ret)result` THEN GEN_TAC THEN
  REWRITE_TAC[result_rel_Rval; result_rel_Rerr1; injectivity "result";
              distinctness "result"] THENL
   [MESON_TAC[];
    CASES_ON `a:(exn_or_ret)error_result` THEN
    REWRITE_TAC[exc_rel_raise1; exc_rel_type_error1; injectivity "error_result";
                distinctness "error_result"] THEN
    MESON_TAC[]]);;

let BVITMCAUX_result_rel_triv = prove
 (`!f (r1:(bvl_v list,exn_or_ret)result) r2.
     result_rel (ALL2 (bvi_tmcProof_v_rel f)) (eor_rel f) r1 r2 ==>
     result_rel (\x:bvl_v list y:bvl_v list. T) (\x:exn_or_ret y:exn_or_ret. T) r1 r2`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `r1:(bvl_v list,exn_or_ret)result` THEN GEN_TAC THEN
  REWRITE_TAC[result_rel_Rval; result_rel_Rerr1] THENL
   [MESON_TAC[];
    CASES_ON `a:(exn_or_ret)error_result` THEN
    REWRITE_TAC[exc_rel_raise1; exc_rel_type_error1] THEN MESON_TAC[]]);;

let BVITMCAUX_sem_body_eq = prove
 (CASE_TERM
  `!(M:(bvl_v list,exn_or_ret)result -> outcome -> bool)
     (e1:num -> (bvl_v list,exn_or_ret)result # (D,FFI)bvi_state)
     (e2:num -> (bvl_v list,exn_or_ret)result # (C,FFI)bvi_state).
     (!r1 r2 outcome.
        result_rel (\x:bvl_v list y:bvl_v list. T) (\x:exn_or_ret y:exn_or_ret. T) r1 r2
        ==> (M r1 outcome <=> M r2 outcome)) /\
     (!k. result_rel (\x:bvl_v list y:bvl_v list. T) (\x:exn_or_ret y:exn_or_ret. T)
            (FST (e1 k)) (FST (e2 k)) /\
          bvi_state_ffi (SND (e2 k)) = bvi_state_ffi (SND (e1 k))) ==>
     (if ?k e. FST (e2 k) = Rerr e /\
               ~(e = Rabort Rtimeout_error) /\ (!f. ~(e = Rabort (Rffi_error f)))
      then Fail
      else
      (match some res.
         ?k s r outcome.
           e2 k = (r,s) /\ M r outcome /\
           res = Terminate outcome (ffi_state_io_events (bvi_state_ffi s))
       with
         SOME res -> res
       | NONE ->
           Diverge
             (build_lprefix_lub
               (IMAGE (\k. llist_fromList
                         (ffi_state_io_events (bvi_state_ffi (SND (e2 k)))))
                      UNIV)))) =
     (if ?k e. FST (e1 k) = Rerr e /\
               ~(e = Rabort Rtimeout_error) /\ (!f. ~(e = Rabort (Rffi_error f)))
      then Fail
      else
      (match some res.
         ?k s r outcome.
           e1 k = (r,s) /\ M r outcome /\
           res = Terminate outcome (ffi_state_io_events (bvi_state_ffi s))
       with
         SOME res -> res
       | NONE ->
           Diverge
             (build_lprefix_lub
               (IMAGE (\k. llist_fromList
                         (ffi_state_io_events (bvi_state_ffi (SND (e1 k)))))
                      UNIV))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "mc") (LABEL_TAC "rel")) THEN
  SUBGOAL_THEN
   `!k. (?e. FST ((e2:num -> (bvl_v list,exn_or_ret)result # (C,FFI)bvi_state) k) =
             Rerr e /\
             ~(e = Rabort Rtimeout_error) /\ (!f. ~(e = Rabort (Rffi_error f)))) <=>
        (?e. FST ((e1:num -> (bvl_v list,exn_or_ret)result # (D,FFI)bvi_state) k) =
             Rerr e /\
             ~(e = Rabort Rtimeout_error) /\ (!f. ~(e = Rabort (Rffi_error f))))`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN USE_THEN "rel" (MP_TAC o CONJUNCT1 o SPEC `k:num`) THEN
    REWRITE_TAC[BVITMCAUX_triv_rel_cases] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[distinctness "result"; injectivity "result"; distinctness "error_result";
                    UNWIND_THM1];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!k. bvi_state_ffi (SND ((e2:num -> (bvl_v list,exn_or_ret)result # (C,FFI)bvi_state) k)) =
        bvi_state_ffi (SND ((e1:num -> (bvl_v list,exn_or_ret)result # (D,FFI)bvi_state) k))`
    ASSUME_TAC THENL
   [USE_THEN "rel" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN
   `!k outcome.
      (M:(bvl_v list,exn_or_ret)result -> outcome -> bool)
        (FST ((e2:num -> (bvl_v list,exn_or_ret)result # (C,FFI)bvi_state) k)) outcome <=>
      M (FST ((e1:num -> (bvl_v list,exn_or_ret)result # (D,FFI)bvi_state) k)) outcome`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "mc" MATCH_MP_TAC THEN
    USE_THEN "rel" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  REWRITE_TAC[BVLPROPSAUX_PAIR_EQ_FST_SND] THEN CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN
  ASM_REWRITE_TAC[]);;

(* both runs from the same clock have results of the same kind and the same *)
(* ffi state: then the semantics agree                                      *)
let BVITMCAUX_semantics_eq = prove
 (`!(ffi:(FFI)ffi_state) p1 (o1:num -> D # (num#num#bvi_exp) list)
     (c1:D->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#D)option) p2
     (o2:num -> C # (num#num#bvi_exp) list)
     (c2:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option) start.
     (!k. result_rel (\x:bvl_v list y:bvl_v list. T) (\x:exn_or_ret y:exn_or_ret. T)
            (FST (bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                                bvi_initial_state ffi p1 o1 c1 k)))
            (FST (bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                                bvi_initial_state ffi p2 o2 c2 k))) /\
          bvi_state_ffi (SND (bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                                            bvi_initial_state ffi p2 o2 c2 k))) =
          bvi_state_ffi (SND (bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                                            bvi_initial_state ffi p1 o1 c1 k)))) ==>
     bvi_semantics ffi p2 o2 c2 start = bvi_semantics ffi p1 o1 c1 start`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[bvi_semantics_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  MATCH_MP_TAC BVITMCAUX_sem_body_eq THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN BETA_TAC THEN REWRITE_TAC[BVITMCAUX_triv_rel_cases] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 5933 *)
let bvi_tmcProof_compile_each_semantics = prove
 (`!n prog (co:num -> (num#C) # (num#num#bvi_exp) list) prog2 (ffi:(FFI)ffi_state)
    (cc:C -> (num#num#bvi_exp) list -> (byte list # int64 list # C) option) start.
     bvi_tmcProof_input_condition n prog /\
     (!k n cfg prog. co k = ((n,cfg),prog) ==> bvi_tmcProof_input_condition n prog) /\
     (!k. MEM k (MAP FST prog2) /\ k MOD bvl_to_bvi_namespaces = 3 ==>
          k < FST (FST (co 0))) /\
     SND (bvi_tmc_compile_each n prog) = prog2 /\
     ~(bvi_semantics ffi (fromAList prog) co (state_cc bvi_tmc_compile_each cc) start =
       Fail) ==>
     bvi_semantics ffi (fromAList prog) co (state_cc bvi_tmc_compile_each cc) start =
     bvi_semantics ffi (fromAList prog2) (state_co bvi_tmc_compile_each co) cc start`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC BVITMCAUX_semantics_eq THEN X_GEN_TAC `k:num` THEN
  MP_TAC(ISPEC `bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                  bvi_initial_state (ffi:(FFI)ffi_state) (fromAList prog)
                    (co:num -> (num#C) # (num#num#bvi_exp) list)
                    (state_cc bvi_tmc_compile_each
                      (cc:C -> (num#num#bvi_exp) list -> (byte list # int64 list # C) option))
                    k)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,exn_or_ret)result`
    (X_CHOOSE_THEN `s1:(num#C,FFI)bvi_state` ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(r1:(bvl_v list,exn_or_ret)result = Rerr (Rabort Rtype_error))`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CLOSSEMAUX_bvi_semantics_not_Fail_cond) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPECL [`k:num`;
      `Rabort Rtype_error:(exn_or_ret)error_result`]) THEN
    ASM_REWRITE_TAC[FST] THEN REWRITE_TAC BVLPROPSAUX_bvi_eval_simps;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `prog:(num#num#bvi_exp)list`;
                 `co:num -> (num#C) # (num#num#bvi_exp) list`; `start:num`;
                 `ffi:(FFI)ffi_state`;
                 `cc:C -> (num#num#bvi_exp) list -> (byte list # int64 list # C) option`;
                 `k:num`; `r1:(bvl_v list,exn_or_ret)result`; `s1:(num#C,FFI)bvi_state`]
                bvi_tmcProof_evaluate_compile_each) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(num,num)fmap` (X_CHOOSE_THEN `s2:(C,FFI)bvi_state`
    (X_CHOOSE_THEN `r2:(bvl_v list,exn_or_ret)result` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[FST; SND] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BVITMCAUX_result_rel_triv THEN EXISTS_TAC `f:(num,num)fmap` THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP bvi_tmcProof_state_rel_const) THEN SIMP_TAC[]]);;

(* HOL4 line 6103 *)
let bvi_tmcProof_compile_prog_semantics = prove
 (`!b n prog (co:num -> (num#C) # (num#num#bvi_exp) list) prog2 (ffi:(FFI)ffi_state)
    (cc:C -> (num#num#bvi_exp) list -> (byte list # int64 list # C) option) start.
     bvi_tmcProof_input_condition n prog /\
     (!k n cfg prog. co k = ((n,cfg),prog) ==> bvi_tmcProof_input_condition n prog) /\
     (!k. MEM k (MAP FST prog2) /\ k MOD bvl_to_bvi_namespaces = 3 ==>
          k < FST (FST (co 0))) /\
     SND (bvi_tmc_compile_prog b n prog) = prog2 /\
     ~(bvi_semantics ffi (fromAList prog) co (state_cc (bvi_tmc_compile_prog b) cc) start =
       Fail) ==>
     bvi_semantics ffi (fromAList prog) co (state_cc (bvi_tmc_compile_prog b) cc) start =
     bvi_semantics ffi (fromAList prog2) (state_co (bvi_tmc_compile_prog b) co) cc start`,
  GEN_TAC THEN CASES_ON `b:bool` THENL
   [SUBGOAL_THEN `bvi_tmc_compile_prog T = bvi_tmc_compile_each` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; bvi_tmc_compile_prog_def]; ALL_TAC] THEN
    MATCH_ACCEPT_TAC bvi_tmcProof_compile_each_semantics;
    SUBGOAL_THEN `bvi_tmc_compile_prog F = CURRY I` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; bvi_tmc_compile_prog_def; CURRY_DEF; I_THM]; ALL_TAC] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[CURRY_DEF; I_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      rhs (concl th) = `prog2:(num#num#bvi_exp)list`)) THEN
    REWRITE_TAC[SND] THEN MATCH_MP_TAC bvi_semantics_CURRY_I THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Code labels: the pass only introduces calls to the fresh worker names it  *)
(* allocates, so every label of the output is a label of the input or one   *)
(* of the names strictly below the final next-name.                          *)
(* ------------------------------------------------------------------------- *)

(* HOL4 [local,simp] *)
let get_code_labels_MAP_Var = prove
 (`!vs. UNIONS (set_of_list (MAP bvi_get_code_labels (MAP (\n. bvi_Var n) vs))) = {}`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; set_of_list; UNIONS_0; UNIONS_INSERT; bvi_get_code_labels_def;
                  UNION_EMPTY]);;

let BVITMCAUX_LABELS = [bvi_get_code_labels_def; MAP; MAP_APPEND; set_of_list;
  SET_OF_LIST_APPEND; UNIONS_UNION; UNIONS_INSERT; UNIONS_0; UNION_EMPTY;
  EMPTY_UNION; assign_get_code_label_def; get_code_labels_MAP_Var; LET_DEF;
  LET_END_DEF];;

(* HOL4 [local] *)
let cb_to_bvi_worker_aux_code_labels = prove
 (`!cb loc_opt ptr idx.
     bvi_get_code_labels (cb_to_bvi_worker_aux cb loc_opt ptr idx) = {loc_opt}`,
  MATCH_MP_TAC cb_to_bvi_worker_aux_ind THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[cb_to_bvi_worker_aux_def] THEN
  ASM_REWRITE_TAC(optimise_call_def :: mut_cons_def :: update_cons_def :: BVITMCAUX_LABELS) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC BVITMCAUX_LABELS);;

(* HOL4 [local] *)
let cb_to_bvi_worker_code_labels = prove
 (`!cb loc_opt ptr idx.
     bvi_get_code_labels (cb_to_bvi_worker cb loc_opt ptr idx) = {loc_opt}`,
  GEN_TAC THEN CASES_ON `cb:call_block` THEN
  REWRITE_TAC[cb_to_bvi_worker_def] THEN
  REWRITE_TAC(optimise_call_def :: mut_cons_def :: update_cons_def ::
              cb_to_bvi_worker_aux_code_labels :: BVITMCAUX_LABELS) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC BVITMCAUX_LABELS);;

(* HOL4 [local] *)
let cb_to_bvi_wrapper_code_labels = prove
 (`!tag left child right loc_opt.
     bvi_get_code_labels (cb_to_bvi_wrapper tag left child right loc_opt) = {loc_opt}`,
  REWRITE_TAC(cb_to_bvi_wrapper_def :: mut_cons_def :: bvi_tmc_finalise_cons_def ::
              cb_to_bvi_worker_aux_code_labels :: BVITMCAUX_LABELS));;

let BVITMCAUX_UNIONS_SING = prove
 (`!(g:A->B->bool) x. UNIONS (set_of_list (MAP g [x])) = g x`,
  REWRITE_TAC[MAP; set_of_list; UNIONS_INSERT; UNIONS_0; UNION_EMPTY]);;

(* HOL4 [local] *)
let bvi_to_cb_aux_code_labels_lemma = prove
 (`(!n loc tag exp bs r.
      bvi_to_cb_aux_sing n loc tag exp = SOME (bs,r) ==>
      UNIONS (set_of_list (MAP bvi_get_code_labels bs)) SUBSET bvi_get_code_labels exp) /\
   (!n loc tag args bs r.
      bvi_to_cb_aux n loc tag args = SOME (bs,r) ==>
      UNIONS (set_of_list (MAP bvi_get_code_labels bs)) SUBSET
      UNIONS (set_of_list (MAP bvi_get_code_labels args)))`,
  MATCH_MP_TAC bvi_to_cb_aux_ind THEN REPEAT CONJ_TAC THENL
   [(* Call *)
    REPEAT GEN_TAC THEN REWRITE_TAC[bvi_to_cb_aux_def; call_to_cb_def] THEN
    COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "option"] THEN
    MP_TAC(ISPEC `bind 0 (args:bvi_exp list)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `vs:num list` (X_CHOOSE_THEN `k:num` SUBST1_TAC)) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ; PAIR_EQ] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
    REWRITE_TAC[bvi_get_code_labels_def; SUBSET_UNION];
    (* Op *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[bvi_to_cb_aux_def; option_case_eq; sum_case_eq; pair_case_eq;
                COND_CASE_EQ; distinctness "option"; option_INJ; PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[BVITMCAUX_UNIONS_SING; SUBSET_REFL] THEN
    FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(fun dc -> MP_TAC(MATCH_MP ih dc))) THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
    REWRITE_TAC[bvi_get_code_labels_def] THEN SET_TAC[];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;
    (* [] *)
    REWRITE_TAC[bvi_to_cb_aux_def; option_INJ; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[SUBSET_REFL];
    (* [exp] *)
    REWRITE_TAC[bvi_to_cb_aux_def; BVITMCAUX_UNIONS_SING];
    (* CONS *)
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "iht") (LABEL_TAC "ihh")) THEN
    REPEAT GEN_TAC THEN
    DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs:num list` SUBST1_TAC)
                     (X_CHOOSE_THEN `cb:call_block` SUBST1_TAC)
      (ISPEC `r:num list + call_block` (cases "sum")) THENL
     [DISCH_THEN(X_CHOOSE_THEN `bs1:bvi_exp list` (X_CHOOSE_THEN `vs1:num list`
        (X_CHOOSE_THEN `bs2:bvi_exp list` (X_CHOOSE_THEN `vs2:num list`
          STRIP_ASSUME_TAC))) o MATCH_MP BVITMCAUX_cb_aux_cons_inl_inv) THEN
      REMOVE_THEN "ihh" (MP_TAC o SPECL [`bs2:bvi_exp list`; `vs2:num list`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`bs1:bvi_exp list`; `INL vs1:num list + call_block`]) THEN
      REMOVE_THEN "iht" (MP_TAC o SPECL [`bs2:bvi_exp list`; `INL vs2:num list + call_block`]) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MAP; MAP_APPEND; set_of_list; SET_OF_LIST_APPEND; UNIONS_UNION;
                  UNIONS_INSERT] THEN SET_TAC[];
      DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC o MATCH_MP BVITMCAUX_cb_aux_cons_inr_inv) THEN
      RVEQ_TAC THENL
       [REMOVE_THEN "ihh" (MP_TAC o SPECL [`bs2:bvi_exp list`; `vs2:num list`]) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPECL [`bs1:bvi_exp list`;
          `INR (CallBlock tag [] child []):num list + call_block`]) THEN
        REMOVE_THEN "iht" (MP_TAC o SPECL [`bs2:bvi_exp list`;
          `INL vs2:num list + call_block`]) THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[MAP; MAP_APPEND; set_of_list; SET_OF_LIST_APPEND; UNIONS_UNION;
                    UNIONS_INSERT] THEN SET_TAC[];
        REMOVE_THEN "iht" (MP_TAC o SPECL [`bs2:bvi_exp list`;
          `INR (CallBlock tag l child rr):num list + call_block`]) THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[MAP; MAP_APPEND; set_of_list; SET_OF_LIST_APPEND; UNIONS_UNION;
                    UNIONS_INSERT] THEN SET_TAC[]]]] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_to_cb_aux_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "option"; option_INJ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[BVITMCAUX_UNIONS_SING; SUBSET_REFL]);;
(* HOL4 [local] *)
let bvi_to_cb_code_labels = prove
 (`!n loc exp bs cb.
     bvi_to_cb n loc exp = SOME (bs,cb) ==>
     UNIONS (set_of_list (MAP bvi_get_code_labels bs)) SUBSET bvi_get_code_labels exp`,
  REPEAT GEN_TAC THEN CASES_ON `exp:bvi_exp` THEN
  REWRITE_TAC[bvi_to_cb_def; call_to_cb_def] THEN
  GVS[option_case_eq; pair_case_eq; sum_case_eq; COND_CASE_EQ;
      BVIPAUX_TMC_dest_Cons_SOME] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[bvi_get_code_labels_def; SUBSET_UNION] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT2 bvi_to_cb_aux_code_labels_lemma)) THEN
  SET_TAC[]);;

(* HOL4 [local] *)
let rewrite_wrapper_code_labels = prove
 (`!loc loc_opt n exp y.
     rewrite_wrapper loc loc_opt n exp = SOME y ==>
     bvi_get_code_labels y SUBSET bvi_get_code_labels exp UNION {loc_opt}`,
  MATCH_MP_TAC rewrite_wrapper_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[rewrite_wrapper_def; LET_DEF; LET_END_DEF; distinctness "option"] THEN
  REWRITE_TAC[option_case_eq; pair_case_eq; case_eq "call_block"; OPTION_MAP_EQ_SOME;
              distinctness "option"; option_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[bvi_get_code_labels_def; cb_to_bvi_wrapper_code_labels] THEN
  TRY(FIRST_ASSUM(MP_TAC o MATCH_MP bvi_to_cb_code_labels) THEN
      REWRITE_TAC[bvi_get_code_labels_def] THEN SET_TAC[] THEN NO_TAC) THEN
  REPEAT(FIRST_X_ASSUM(fun ih ->
    if is_forall (concl ih) then FIRST_ASSUM(fun eq -> MP_TAC(MATCH_MP ih eq))
    else failwith "")) THEN
  SET_TAC[]);;

let BVITMCAUX_fill_hole_labels = prove
 (`!p i e. bvi_get_code_labels (fill_hole p i e) = bvi_get_code_labels e`,
  REWRITE_TAC[fill_hole_def; bvi_get_code_labels_def; MAP; set_of_list; UNIONS_INSERT;
              UNIONS_0; UNION_EMPTY; EMPTY_UNION; assign_get_code_label_def]);;

let BVITMCAUX_worker_cb_labels = prove
 (CASE_TERM `!n loc e loc_opt p i.
     bvi_get_code_labels
       (match bvi_to_cb n loc e with
          NONE -> fill_hole p i e
        | SOME (bs,cb) -> bvi_Let bs (cb_to_bvi_worker cb loc_opt (LENGTH bs + p)
                                        (LENGTH bs + i))) SUBSET
     bvi_get_code_labels e UNION {loc_opt}`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `bvi_to_cb n loc e` option_nchotomy) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `q:bvi_exp list#call_block`
    (fun th -> ASSUME_TAC th THEN SUBST1_TAC th))) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[BVITMCAUX_fill_hole_labels; SUBSET_UNION] THEN
  MP_TAC(ISPEC `q:bvi_exp list#call_block` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `bs:bvi_exp list` (X_CHOOSE_THEN `cb:call_block`
    SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvi_get_code_labels_def; cb_to_bvi_worker_code_labels] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP bvi_to_cb_code_labels) THEN SET_TAC[]);;

(* HOL4 [local] *)
let rewrite_worker_code_labels = prove
 (`!loc loc_opt p i n exp.
     bvi_get_code_labels (rewrite_worker loc loc_opt p i n exp) SUBSET
     bvi_get_code_labels exp UNION {loc_opt}`,
  MATCH_MP_TAC rewrite_worker_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[rewrite_worker_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[BVITMCAUX_fill_hole_labels; SUBSET_UNION; BVITMCAUX_worker_cb_labels] THEN
  TRY(FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH (xs:bvi_exp list)`)) THEN
  REPEAT(FIRST_X_ASSUM MP_TAC) THEN
  REWRITE_TAC[bvi_get_code_labels_def] THEN SET_TAC[]);;

(* HOL4 [local] *)
let bvi_tmcProof_compile_exp_code_labels = prove
 (`!loc next arity exp exp_w exp_k.
     bvi_tmc_compile_exp loc next arity exp = SOME (exp_w,exp_k) ==>
     bvi_get_code_labels exp_w SUBSET bvi_get_code_labels exp UNION {next} /\
     bvi_get_code_labels exp_k SUBSET bvi_get_code_labels exp UNION {next}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_tmc_compile_exp_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPEC `rewrite_wrapper loc next arity exp` option_nchotomy) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `w:bvi_exp`
    (fun th -> ASSUME_TAC th THEN SUBST1_TAC th))) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"; option_INJ; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[rewrite_worker_code_labels] THEN
  FIRST_ASSUM(ACCEPT_TAC o MATCH_MP rewrite_wrapper_code_labels));;
let bvi_tmcProof_compile_each_good_code_labels = prove
 (`!n c n2 c2.
     bvi_tmc_compile_each n c = (n2,c2) /\
     UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) c)) SUBSET all /\
     {n + k * bvl_to_bvi_namespaces | k | n + k * bvl_to_bvi_namespaces < n2}
       SUBSET all ==>
     UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) c2)) SUBSET all`,
  MATCH_MP_TAC bvi_tmc_compile_each_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[bvi_tmc_compile_each_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  BVITMCAUX_EACH_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; set_of_list; UNIONS_INSERT; o_THM; UNION_SUBSET]) THEN
  REWRITE_TAC[MAP; set_of_list; UNIONS_INSERT; o_THM; UNION_SUBSET] THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvi_tmcProof_compile_exp_code_labels) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvi_tmcProof_compile_each_next_mono) THEN
  SUBGOAL_THEN `(next:num) IN all` ASSUME_TAC THENL
   [UNDISCH_TAC `{next + k * bvl_to_bvi_namespaces | k |
                  next + k * bvl_to_bvi_namespaces < n2} SUBSET all` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `next:num`) THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `bvi_get_code_labels exp UNION {next}` THEN
    ASM_REWRITE_TAC[UNION_SUBSET; SING_SUBSET];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `bvi_get_code_labels exp UNION {next}` THEN
    ASM_REWRITE_TAC[UNION_SUBSET; SING_SUBSET];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `{next + k * bvl_to_bvi_namespaces | k |
                next + k * bvl_to_bvi_namespaces < n2} SUBSET all` THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `k' + 1` THEN
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[bvl_to_bvi_namespaces_def]) THEN
  REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN ASM_ARITH_TAC);;

let bvi_tmcProof_compile_prog_good_code_labels = prove
 (`!b n c n2 c2.
     bvi_tmc_compile_prog b n c = (n2,c2) /\
     UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) c)) SUBSET all /\
     {n + k * bvl_to_bvi_namespaces | k | n + k * bvl_to_bvi_namespaces < n2}
       SUBSET all ==>
     UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) c2)) SUBSET all`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_tmc_compile_prog_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [MESON_TAC[bvi_tmcProof_compile_each_good_code_labels];
    STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[]]);;

let bvi_tmcProof_compile_each_keeps_names = prove
 (`!next xs next' ys.
     bvi_tmc_compile_each next xs = (next',ys) /\ MEM x (MAP FST xs) ==>
     MEM x (MAP FST ys)`,
  MATCH_MP_TAC bvi_tmc_compile_each_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[MAP; MEM]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  BVITMCAUX_EACH_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; MEM]) THEN REWRITE_TAC[MAP; MEM] THEN
  ASM_MESON_TAC[]);;

let bvi_tmcProof_compile_prog_keeps_names = prove
 (`!b next xs next' ys.
     bvi_tmc_compile_prog b next xs = (next',ys) /\ MEM x (MAP FST xs) ==>
     MEM x (MAP FST ys)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_tmc_compile_prog_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [MESON_TAC[bvi_tmcProof_compile_each_keeps_names];
    STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[]]);;
