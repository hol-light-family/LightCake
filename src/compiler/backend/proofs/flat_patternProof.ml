(* ========================================================================= *)
(* flat_patternProof: port of HOL4 compiler/backend/proofs/                  *)
(* flat_patternProofScript.sml (CakeML v3479).  Correctness proof for        *)
(* flat_pattern.                                                             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/bag.ml";;
needs "hol4/sptree.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/pattern_matching/pattern_common.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/pattern_matching/pattern_comp.ml";;
needs "compiler/backend/flat_pattern.ml";;
needs "compiler/backend/semantics/flatSem.ml";;
needs "compiler/backend/semantics/flatProps.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "basis/pure/mlstring.ml";;

type_invention_error := true;;

(* simple properties *)

let op_sets_globals_gbag = prove
 (`!op. op_sets_globals op <=> ~(flat_op_gbag op = EMPTY_BAG)`,
  GEN_TAC THEN CASES_ON `op:flat_op` THEN
  REWRITE_TAC[op_sets_globals_def; flat_op_gbag_def; BAG_INSERT_NOT_EMPTY]);;

let compile_exp_set_globals_FST_SND = prove
 (`(!cfg x. FST (SND (flat_pattern_compile_exp cfg x)) <=>
            ~(flat_set_globals x = EMPTY_BAG)) /\
   (!cfg xs. FST (SND (flat_pattern_compile_exps cfg xs)) <=>
             ~(flat_elist_globals xs = EMPTY_BAG)) /\
   (!cfg ps. FST (SND (compile_match cfg ps)) <=>
             ~(flat_elist_globals (MAP SND ps) = EMPTY_BAG))`,
  MATCH_MP_TAC flat_pattern_compile_exp_ind THEN REWRITE_TAC[flat_pattern_compile_exp_def] THEN
  REPEAT STRIP_TAC THEN REPEAT PAIRARG_TAC THEN FS[] THEN
  FS[elist_globals_REVERSE; op_sets_globals_gbag; DE_MORGAN_THM; DISJ_ACI] THEN
  SIMP[GSYM EX_MEM; elist_globals_eq_empty; MEM_MAP; EXISTS_PAIR_THM; PAIR_FST_SND_EQ] THEN
  ASM_MESON_TAC[]);;

let compile_exp_set_globals_tup = prove
 (`(!cfg x i sg y. flat_pattern_compile_exp cfg x = (i,sg,y)
                   ==> (sg <=> ~(flat_set_globals x = EMPTY_BAG))) /\
   (!cfg xs i sg ys. flat_pattern_compile_exps cfg xs = (i,sg,ys)
                     ==> (sg <=> ~(flat_elist_globals xs = EMPTY_BAG))) /\
   (!cfg ps i sg ps2. compile_match cfg ps = (i,sg,ps2)
                      ==> (sg <=> ~(flat_elist_globals (MAP SND ps) = EMPTY_BAG)))`,
  MESON_TAC[compile_exp_set_globals_FST_SND; FST; SND]);;

(* decoding the encoded names *)

let sum_string_ords_eq = prove
 (`!i s. sum_string_ords i s = SUM (MAP (\c. ORD c - 35) (DROP i (explode s)))`,
  MATCH_MP_TAC sum_string_ords_ind THEN MAP_EVERY X_GEN_TAC [`i:num`; `s:mlstring`] THEN
  CASES_ON `s:mlstring` THEN DISCH_TAC THEN ONCE_REWRITE_TAC[sum_string_ords_def] THEN
  RW[strlen_def; strsub_def; explode_thm; DROP_EL_CONS] THEN FS[NOT_LT; DROP_LENGTH_TOO_LONG]);;

let dec_enc_aux = prove
 (`!i xs. dec_name_to_num (implode (enc_num_to_name_aux i xs)) =
          i + SUM (MAP (\c. ORD c - 35) xs)`,
  MATCH_MP_TAC (cake_ind "enc_num_to_name_aux") THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[enc_num_to_name_aux_def] THEN COND_CASES_TAC THEN
  FS[dec_name_to_num_def; sum_string_ords_eq; strlen_def; strsub_def; explode_thm; ORD_CHR_RWT;
     ARITH_RULE `~(SUC (SUC (SUC n)) < 2)`; NOT_LT] THENL
   [SUBGOAL_THEN `ORD (CHR (i + 35)) = i + 35` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM ORD_CHR] THEN DECIDE_TAC; ARITH_TAC];
    UNDISCH_TAC `90 <= i` THEN ARITH_TAC]);;

let dec_enc = prove
 (`!i. dec_name_to_num (enc_num_to_name i) = i`,
  SIMP[enc_num_to_name_def; dec_enc_aux]);;

let enc_num_to_name_inj = prove
 (`!i j. enc_num_to_name i = enc_num_to_name j <=> i = j`,
  MESON_TAC[dec_enc]);;

(* lists and lookups *)

let LIST_REL_ALOOKUP_OPTREL = prove
 (`!xs ys. ALL2 (R:A#B->A#C->bool) xs ys /\
     (!x y. R x y /\ MEM x xs /\ MEM y ys /\ (v = FST x \/ v = FST y)
            ==> FST x = FST y /\ (R2:B->C->bool) (SND x) (SND y))
     ==> OPTREL R2 (ALOOKUP xs v) (ALOOKUP ys v)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN CASES_ON `ys:(A#C)list` THEN SIMP[ALL2] THEN
  CASES_ON `h:A#B` THEN CASES_ON `a0:A#C` THEN SIMP[ALOOKUP_DEF] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a1:(A#C)list`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(x:A,y:B)`; `(x':A,y':C)`]) THEN RW[] THEN FS[]);;

let LIST_REL_ALOOKUP = prove
 (`!xs ys. ALL2 (R:A#B->A#B->bool) xs ys /\
     (!x y. R x y /\ MEM x xs /\ MEM y ys /\ (v = FST x \/ v = FST y) ==> x = y)
     ==> ALOOKUP xs v = ALOOKUP ys v`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM OPTREL_eq] THEN
  MATCH_MP_TAC LIST_REL_ALOOKUP_OPTREL THEN
  ASM_MESON_TAC[]);;

let LIST_REL_FILTER_MONO = prove
 (`!xs ys. ALL2 (R:A->B->bool) (FILTER P1 xs) (FILTER P2 ys) /\
     (!x. MEM x xs /\ P3 x ==> P1 x) /\
     (!y. MEM y ys /\ P4 y ==> P2 y) /\
     (!x y. MEM x xs /\ MEM y ys /\ R x y ==> (P3 x <=> P4 y))
     ==> ALL2 R (FILTER P3 xs) (FILTER P4 ys)`,
  LIST_INDUCT_TAC THENL
   [SIMP[FILTER; ALL2; FILTER_EQ_NIL; GSYM ALL_MEM; LIST_REL_NIL] THEN MESON_TAC[];
    ALL_TAC] THEN
  GEN_TAC THEN SIMP[FILTER] THEN COND_CASES_TAC THENL
   [ALL_TAC; COND_CASES_TAC THEN RW[] THEN ASM_MESON_TAC[]] THEN
  REPEAT STRIP_TAC THEN FS[FILTER_EQ_CONS; LIST_REL_CONS1] THEN RVEQ_TAC THEN
  SUBGOAL_THEN `FILTER (P4:B->bool) l1 = []` ASSUME_TAC THENL
   [FS[FILTER_EQ_NIL; GSYM ALL_MEM; MEM_APPEND] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(DRULE_THEN MP_TAC) THEN SIMP[FILTER_APPEND; FILTER; MEM_APPEND] THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM_APPEND];
    COND_CASES_TAC THEN SIMP[ALL2; APPEND]]);;

let COND_false = prove
 (`!P (x:A) y. ~P ==> (if P then x else y) = y`,
  SIMP_TAC[]);;

let COND_true = prove
 (`!P (x:A) y. P ==> (if P then x else y) = x`,
  SIMP_TAC[]);;

let FILTER_EQ_MONO =
  REWRITE_RULE[LIST_REL_eq] (ISPEC `(=):A->A->bool`
    (GEN `R:A->B->bool` LIST_REL_FILTER_MONO));;

let FILTER_EQ_MONO_TRANS =
  REWRITE_RULE[FILTER_T]
    (INST [`\x:A. T`,`P2:A->bool`; `P3:A->bool`,`P4:A->bool`] FILTER_EQ_MONO);;

let FILTER_EQ_ALOOKUP_EQ = prove
 (`!xs ys. FILTER (P:A#B->bool) xs = ys /\ (!z. P (x,z))
           ==> ALOOKUP xs x = ALOOKUP ys x`,
  LIST_INDUCT_TAC THEN SIMP[FILTER] THEN CASES_ON `h:A#B` THEN RW[ALOOKUP_DEF] THEN RFS[]);;

let ALOOKUP_FILTER_EQ = prove
 (`!xs. (!z. P ((x:A),(z:B))) ==> ALOOKUP (FILTER P xs) x = ALOOKUP xs x`,
  MESON_TAC[FILTER_EQ_ALOOKUP_EQ]);;

let MEM_enumerate_EL = prove
 (`!xs i (x:num#A). MEM x (enumerate i xs) <=>
                    ?j. j < LENGTH xs /\ x = (i + j,EL j xs)`,
  LIST_INDUCT_TAC THEN RW[ARITH_ss; enumerate_def; LT] THEN EQ_TAC THEN RW[] THENL
   [EXISTS_TAC `0` THEN SIMP[EL; HD];
    EXISTS_TAC `SUC j` THEN SIMP[EL; TL] THEN ARITH_TAC;
    CASES_ON `j:num` THEN FS[EL; HD; TL] THEN EXISTS_TAC `n:num` THEN
    SIMP[] THEN ASM_ARITH_TAC]);;

let ALL_DISTINCT_enumerate = prove
 (`!xs i. ALL_DISTINCT (enumerate i (xs:A list))`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[enumerate_def; ALL_DISTINCT; MEM_enumerate_EL] THEN
  REWRITE_TAC[PAIR_EQ] THEN ARITH_TAC);;

let pure_eval_to_def = cake_def
  `pure_eval_to (s:(C,FFI)flat_state) env exp v <=>
     flat_evaluate env s [exp] = (s,Rval [v])`;;

let pmatch_list_Match_IMP_LENGTH = prove
 (`!xs ys env env' (s:(C,FFI)flat_state).
     flat_pmatch_list s xs ys env = Match env' ==> LENGTH xs = LENGTH ys`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN CASES_ON `ys:flat_v list` THEN
  SIMP[flat_pmatch_def; case_eq "match_result"] THEN ASM_MESON_TAC[]);;

(* HOL4: APPEND_LENGTH_EQ (list.ml binds that name to a weaker statement) *)
let flat_patternProof_APPEND_LENGTH_EQ = prove
 (`!xs xs' (ys:A list) ys'. LENGTH xs = LENGTH xs'
       ==> (APPEND xs ys = APPEND xs' ys' <=> xs = xs' /\ ys = ys')`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; APPEND; NOT_SUC; SUC_INJ; CONS_11] THEN
  ASM_MESON_TAC[]);;

let pmatch_list_append_Match_exists = prove
 (`!(s:(C,FFI)flat_state) xs ys vs pre_bindings bindings.
     flat_pmatch_list s (APPEND xs ys) vs pre_bindings = Match bindings <=>
     ?vs1 vs2 bindings1. vs = APPEND vs1 vs2 /\
       flat_pmatch_list s xs vs1 pre_bindings = Match bindings1 /\
       flat_pmatch_list s ys vs2 bindings1 = Match bindings`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `LENGTH (vs:flat_v list) = LENGTH (xs:flat_pat list) + LENGTH (ys:flat_pat list)`
  THENL
   [ALL_TAC;
    EQ_TAC THEN RW[] THEN IMP_RES_TAC pmatch_list_Match_IMP_LENGTH THEN RFS[LENGTH_APPEND]] THEN
  FS[LENGTH_EQ_SUM] THEN SIMP[flat_pmatch_list_append; case_eq "match_result"] THEN
  EQ_TAC THEN RW[] THEN IMP_RES_TAC pmatch_list_Match_IMP_LENGTH THEN
  RFS[] THEN FS[flat_patternProof_APPEND_LENGTH_EQ] THEN ASM_MESON_TAC[]);;

let ALOOKUP_rel_def = cake_def
  `ALOOKUP_rel (P:A->bool) (R:B->C->bool) env1 env2 <=>
     !x. P x ==> OPTREL R (ALOOKUP env1 x) (ALOOKUP env2 x)`;;

let ALOOKUP_rel_empty = prove
 (`ALOOKUP_rel (P:A->bool) (R:B->C->bool) [] []`,
  REWRITE_TAC[ALOOKUP_rel_def; ALOOKUP_DEF; OPTREL_DEF]);;

let ALOOKUP_rel_cons_false = prove
 (`(~P x ==> (ALOOKUP_rel (P:A->bool) (R:B->C->bool) (CONS (x,y) env1) env2 <=>
              ALOOKUP_rel P R env1 env2)) /\
   (~P x ==> (ALOOKUP_rel (P:A->bool) (R:B->C->bool) env1 (CONS (x,z) env2) <=>
              ALOOKUP_rel P R env1 env2))`,
  SIMP[ALOOKUP_rel_def; ALOOKUP_DEF] THEN MESON_TAC[]);;

let ALOOKUP_rel_APPEND_L_false = prove
 (`ALL ((~) o (P:A->bool) o FST) (xs:(A#B)list)
   ==> (ALOOKUP_rel P (R:B->C->bool) (APPEND xs ys) zs <=> ALOOKUP_rel P R ys zs)`,
  RW[ALOOKUP_rel_def; ALOOKUP_APPEND] THEN EQ_TAC THEN RW[] THEN
  FIRST_X_ASSUM(DRULE_THEN MP_TAC) THEN CASE_TAC THEN SIMP[] THEN
  DRULE ALOOKUP_MEM THEN FS[GSYM ALL_MEM; FORALL_PAIR_THM] THEN ASM_MESON_TAC[]);;

let ALOOKUP_rel_refl = prove
 (`(!x y. P x /\ MEM (x,y) xs ==> (R:B->B->bool) y y)
   ==> ALOOKUP_rel (P:A->bool) R xs xs`,
  RW[ALOOKUP_rel_def] THEN CASES_ON `ALOOKUP (xs:(A#B)list) x` THEN SIMP[] THEN
  ASM_MESON_TAC[ALOOKUP_MEM]);;

let ALOOKUP_rel_cons = prove
 (`(P x ==> (R:B->C->bool) y z) /\ ALOOKUP_rel (P:A->bool) R ys zs
   ==> ALOOKUP_rel P R (CONS (x,y) ys) (CONS (x,z) zs)`,
  RW[ALOOKUP_rel_def; ALOOKUP_DEF] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[OPTREL_THM]);;

let ALOOKUP_rel_mono = prove
 (`ALOOKUP_rel (P:A->bool) (R:B->C->bool) xs ys /\
   (!x (y:B) (z:C). P' x ==> P x) /\
   (!x y z. P' x /\ R y z ==> R' y z)
   ==> ALOOKUP_rel P' R' xs ys`,
  REWRITE_TAC[ALOOKUP_rel_def; OPTREL_DEF] THEN MESON_TAC[]);;

let ALOOKUP_rel_mono_rel = prove
 (`(!y z. (R:B->C->bool) y z ==> R' y z)
   ==> ALOOKUP_rel (P:A->bool) R xs ys ==> ALOOKUP_rel P R' xs ys`,
  REWRITE_TAC[ALOOKUP_rel_def; OPTREL_DEF] THEN MESON_TAC[]);;

let ALOOKUP_rel_append_suff = prove
 (`ALOOKUP_rel (P:A->bool) (R:B->C->bool) xs1 xs3 /\ ALOOKUP_rel P R xs2 xs4
   ==> ALOOKUP_rel P R (APPEND xs1 xs2) (APPEND xs3 xs4)`,
  RW[ALOOKUP_rel_def; ALOOKUP_APPEND] THEN RES_TAC THEN EVERY_CASE_TAC THEN FS[]);;

let ALOOKUP_rel_EQ_ALOOKUP = prove
 (`ALOOKUP_rel (P:A->bool) (=) (xs:(A#B)list) ys /\ P x
   ==> ALOOKUP xs x = ALOOKUP ys x`,
  REWRITE_TAC[ALOOKUP_rel_def; OPTREL_eq] THEN MESON_TAC[]);;

let ALOOKUP_rel_eq_fst = prove
 (`!xs ys. ALL2 (\x y. FST x = FST y /\ ((P:A->bool) (FST x) ==> (R:B->C->bool) (SND x) (SND y)))
                xs ys
           ==> ALOOKUP_rel P R xs ys`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN CASES_ON `ys:(A#C)list` THEN
  SIMP[ALL2; ALOOKUP_rel_empty] THEN CASES_ON `h:A#B` THEN CASES_ON `a0:A#C` THEN RW[] THEN
  MATCH_MP_TAC ALOOKUP_rel_cons THEN ASM_SIMP_TAC[]);;

let env_set_v_noop = prove
 (`flat_environment_v_fupd (K (flat_environment_v env)) (an_env:(V)flat_environment) = env`,
  REWRITE_TAC[flat_environment_component_equality; flat_environment_INFO.ri_accfupds;
              K_THM]);;

let pat_bindings_evaluate_FOLDR_lemma = prove
 (`!(h:A->flat_v) xs.
     (!x. MEM x xs ==> IS_SOME ((f:A->mlstring option) x)) /\
     IMAGE (THE o f) (set_of_list xs) SUBSET new_names /\
     (!x. MEM x xs
          ==> !env2. ALOOKUP_rel (\x. ~(x IN new_names)) (=)
                       (flat_environment_v env2)
                       (flat_environment_v (env:(flat_v)flat_environment))
                     ==> flat_evaluate env2 (s:(C,FFI)flat_state) [g x] =
                         (s,Rval [h x]))
     ==> !env2. ALOOKUP_rel (\x. ~(x IN new_names)) (=)
                  (flat_environment_v env2) (flat_environment_v env)
                ==> flat_evaluate env2 s
                      [ITLIST (\x exp. flat_Let t (f x) (g x) exp) xs exp] =
                    flat_evaluate
                      (flat_environment_v_fupd
                         (K (APPEND (MAP (\x. (THE (f x),h x)) (REVERSE xs))
                                    (flat_environment_v env2))) env2)
                      s [exp]`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN SIMP[env_set_v_noop] THEN RW[] THEN
  SIMP[flat_evaluate_def] THEN
  RFS[DISJ_IMP_THM; FORALL_AND_THM; IS_SOME_EXISTS; IMAGE_CLAUSES; INSERT_SUBSET] THEN
  FS[] THEN SIMP[opt_bind_def; ALOOKUP_rel_cons_false] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

let EVERY_MAPi_simple = prove
 (`(!i j x. (P:B->bool) ((f:num->A->B) i x) = P (f j x))
   ==> (ALL P (MAPi f xs) <=> ALL P (MAP (f 0) xs))`,
  SIMP_TAC[EVERY_EL; EL_MAP; EL_MAPi; LENGTH_MAP; LENGTH_MAPi] THEN
  MESON_TAC[]);;

(* HOL4's ELIM_UNCURRY for HOL Light's paired lambdas: \(x,(y,z)). t is  *)
(* rewritten to \p. t[FST p/x, FST (SND p)/y, SND (SND p)/z]               *)

let FLATPAUX_PAIRED_ABS_CONV : conv = fun tm ->
  if is_abs tm then failwith "FLATPAUX_PAIRED_ABS_CONV" else
  let vstr,bod = dest_gabs tm in
  let p = variant (frees tm) (mk_var("p",type_of vstr)) in
  let rec projs v t =
    if is_pair v then
      let l,r = dest_pair v in
      projs l (mk_icomb(mk_const("FST",[]),t)) @ projs r (mk_icomb(mk_const("SND",[]),t))
    else [t,v] in
  prove(mk_eq(tm,mk_abs(p,vsubst (projs vstr p) bod)),
        REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; FST; SND]);;

let FLATPAUX_ALOOKUP_unique = prove
 (`!(l:(A#B)list) x v. MEM (x,v) l /\ (!w. MEM (x,w) l ==> w = v) ==> ALOOKUP l x = SOME v`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN CASES_ON `h:A#B` THEN
  REWRITE_TAC[ALOOKUP_THM; PAIR_EQ] THEN ASM_MESON_TAC[]);;

(* the clauses of flat_do_app_def for the operations of the compiled patterns *)
(* (simplifying with the whole definition is slow)                            *)
let FLATPAUX_do_app_simps = prove
 (CASE_TERM `(flat_do_app (s:(C,FFI)flat_state) (flat_TagLenEq n l) [flat_Conv (SOME (tag,ty)) xs] =
      SOME (s,Rval (flat_Boolv (tag = n /\ LENGTH xs = l)))) /\
   (flat_do_app s (flat_LenEq l) [flat_Conv x xs] = SOME (s,Rval (flat_Boolv (LENGTH xs = l)))) /\
   (flat_do_app s (flat_El n) [flat_Conv x vs] =
      if n < LENGTH vs then SOME (s,Rval (EL n vs)) else NONE) /\
   (flat_do_app s (flat_El n) [flat_Loc b p] =
      if ~(n = 0) then NONE else
      match store_lookup p (flat_state_refs s) with
        SOME (Refv v) -> SOME (s,Rval v)
      | _ -> NONE) /\
   (flat_do_app s (Src Equality) [v1; v2] =
      match flat_do_eq v1 v2 with
        Eq_type_error -> NONE
      | Eq_val b -> SOME (s,Rval (flat_Boolv b)))`,
  REWRITE_TAC[flat_do_app_def] THEN SIMP[]);;

(* the lets of the El projections that compile_pat_bindings makes for a Pcon *)
(* (pat_bindings_evaluate_FOLDR_lemma, as HOL4's DEP_REWRITE_TAC uses it)    *)

let FLATPAUX_FOLDR_El = prove
 (`!con_vs stmp (used:((num#mlstring)#flat_pat#num#flat_exp)list) x t exp env
    (s:(C,FFI)flat_state).
     (!y. MEM y used
          ==> FST (FST y) < LENGTH con_vs /\ i <= dec_name_to_num (SND (FST y)) /\
              !env2. ALOOKUP_rel (\nm. dec_name_to_num nm < i) (=) (flat_environment_v env2)
                       (flat_environment_v env)
                     ==> flat_evaluate env2 s [x] = (s,Rval [flat_Conv stmp con_vs]))
     ==> flat_evaluate env s
           [ITLIST (\((j,nm),r) exp. flat_Let t (SOME nm) (flat_App t (flat_El j) [x]) exp)
                   used exp] =
         flat_evaluate (flat_environment_v_fupd (K (APPEND
             (MAP (\y. SND (FST y),EL (FST (FST y)) con_vs) (REVERSE used))
             (flat_environment_v env))) env) s [exp]`,
  REPEAT STRIP_TAC THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV FLATPAUX_PAIRED_ABS_CONV)) THEN
  W(fun (_,w) -> MP_TAC(INST [`{nm:mlstring | ~(dec_name_to_num nm < i)}`,`new_names:mlstring->bool`]
    (PART_MATCH (lhs o rand) (REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM]
      (ISPEC `\y:(num#mlstring)#flat_pat#num#flat_exp. EL (FST (FST y)) (con_vs:flat_v list)`
         pat_bindings_evaluate_FOLDR_lemma)) (lhs w)))) THEN
  SIMP[ALOOKUP_rel_refl; IN_ELIM_THM; SUBSET; FORALL_IN_IMAGE; IN_SET_OF_LIST] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP[]] THEN CONJ_TAC THENL [ASM_MESON_TAC[NOT_LT]; ALL_TAC] THEN
  RW[] THEN RES_TAC THEN FS[flat_evaluate_def; FLATPAUX_do_app_simps]);;

(* HOL4: the free variables j and base_vs are left free, as in HOL4; the  *)
(* unused quantified variable vset is dropped.  The induction hypothesis  *)
(* is kept out of the assumptions (DISCH_THEN), which keeps the            *)
(* simplification of the other assumptions fast.                           *)

let compile_pat_bindings_simulation = prove
 (`!t i n_bindings exp exp2 spt (s:(C,FFI)flat_state) vs pre_bindings bindings
      env s2 (res:(flat_v list,flat_v)result).
       compile_pat_bindings t i n_bindings exp = (spt,exp2) /\
       flat_pmatch_list s (MAP FST n_bindings) vs pre_bindings = Match bindings /\
       flat_evaluate env s [exp2] = (s2,res) /\
       ALL2 (\(p0,k,v_exp) v.
               !env2. k IN domain spt /\
                      ALOOKUP_rel ((\k. k > j /\ k < i) o dec_name_to_num) (=)
                        (flat_environment_v env2) (flat_environment_v env)
                      ==> pure_eval_to s env2 v_exp v)
         n_bindings vs /\
       ALL ((\k. k < j) o dec_name_to_num o FST) pre_bindings /\
       j < i /\
       ALOOKUP_rel ((\k. k < j) o dec_name_to_num) (=) (flat_environment_v env)
         (APPEND pre_bindings base_vs) /\
       ALL (\(p,k,x0). ALL (\nm. dec_name_to_num nm < j) (flat_pat_bindings p) /\
                       j < k /\ k < i) n_bindings
       ==> ?env2. flat_evaluate env2 s [exp] = (s2,res) /\
                  ALOOKUP_rel ((\k. k < j) o dec_name_to_num) (=)
                    (flat_environment_v env2) (APPEND bindings base_vs)`,
  let open_tac = REPEAT STRIP_TAC THEN RFS[] THEN RVEQ_TAC THEN RFS[flat_pmatch_def] in
  (* the end of the Pas and Pref cases: the new binding enc_num_to_name (i + 1) *)
  let new_var_tac =
    REPEAT CONJ_TAC THENL
     [RW[pure_eval_to_def; flat_evaluate_def] THEN
      DRULE_THEN (fun th -> IMP_REWRITE_TAC[th]) ALOOKUP_rel_EQ_ALOOKUP THEN
      SIMP[o_THM; dec_enc; ALOOKUP_DEF] THEN DECIDE_TAC;
      FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC MONO_ALL2) THEN SIMP[FORALL_PAIR_THM] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (is_comb o concl)) THEN
      REWRITE_TAC[ALOOKUP_rel_def; ALOOKUP_DEF; o_THM; OPTREL_eq] THEN DISCH_TAC THEN
      X_GEN_TAC `y:mlstring` THEN STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:mlstring`) THEN
      RW[ARITH_ss; dec_enc] THEN FS[dec_enc] THEN DECIDE_TAC;
      FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC MONO_ALL) THEN
      SIMP[FORALL_PAIR_THM] THEN ARITH_TAC] in
  MATCH_MP_TAC compile_pat_bindings_ind THEN
  REWRITE_TAC[compile_pat_bindings_def; flat_pmatch_def; MAP; ALL; LIST_REL_NIL;
              LIST_REL_CONS1; PAIR_EQ; LEFT_IMP_EXISTS_THM] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [(* [] *)
    open_tac THEN ASM_MESON_TAC[];
    (* Pany *)
    DISCH_THEN(fun ih -> open_tac THEN IRULE ih THEN ASM_EXISTS_TAC);
    (* Pvar *)
    DISCH_THEN(fun ih -> open_tac THEN PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `env:(flat_v)flat_environment`) THEN
      SIMP[pure_eval_to_def; ALOOKUP_rel_refl; domain_insert; IN_INSERT] THEN DISCH_TAC THEN
      RFS[flat_evaluate_def; flat_pat_bindings_def] THEN
      DRULE_THEN (DRULE_THEN (DRULE_THEN MP_TAC)) ih THEN SIMP[opt_bind_def] THEN
      DISCH_THEN(IRULE o REWRITE_RULE[IMP_IMP]) THEN SIMP[ALOOKUP_rel_cons] THEN
      FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC MONO_ALL2) THEN
      (* here s is the variable of the Pvar pattern (the state was renamed) *)
      SUBGOAL_THEN `~(dec_name_to_num s > j)` ASSUME_TAC THENL [DECIDE_TAC; ALL_TAC] THEN
      SIMP[FORALL_PAIR_THM; ALOOKUP_rel_cons_false]);
    (* Plit *)
    DISCH_THEN(fun ih -> open_tac THEN
      QPAT_X_ASSUM "_ = Match _" MP_TAC THEN CASES_ON `h':flat_v` THEN
      SIMP[flat_pmatch_def; case_eq "match_result"; COND_CASE_EQ] THEN RW[] THEN
      IRULE ih THEN ASM_EXISTS_TAC);
    (* Pcon *)
    DISCH_THEN(fun ih -> open_tac THEN
      PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN DRULE_THEN (fun ih ->
      FS[case_eq "match_result"] THEN
      QPAT_X_ASSUM "flat_pmatch _ _ _ _ = _" MP_TAC THEN CASES_ON `h':flat_v` THEN
      SIMP[flat_pmatch_def; COND_CASE_EQ] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(fun th -> MP_TAC th THEN MP_TAC(PART_MATCH (lhs o rand)
        (ISPECL [`a1:flat_v list`; `a0:(ctor_id#type_id)option`] FLATPAUX_FOLDR_El)
        (lhs(concl th)))) THEN
      ANTS_TAC THENL
       [RW[MEM_FILTER] THEN FS[MAP_enumerate_MAPi; MEM_MAPi; dec_enc] THEN RVEQ_TAC THEN
        FS[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `env2:(flat_v)flat_environment`) THEN
        REWRITE_TAC[pure_eval_to_def] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
         [COND_CASES_TAC THEN SIMP[domain_insert; IN_INSERT] THEN
          GVS[NULL_FILTER; MAP_enumerate_MAPi; MEM_MAPi; LEFT_IMP_EXISTS_THM];
          DRULE_THEN (IRULE o REWRITE_RULE[IMP_IMP]) ALOOKUP_rel_mono THEN
          SIMP[o_THM; ARITH_ss]];
        DISCH_THEN SUBST1_TAC THEN DISCH_TAC] THEN
      IRULE (REWRITE_RULE[IMP_IMP] ih) THEN ASM_EXISTS_TAC THEN
      EXISTS_TAC `APPEND a1 t':flat_v list` THEN
      REWRITE_TAC[MAP_APPEND; MAP_enumerate_MAPi; REWRITE_RULE[o_DEF] MAP_MAPi; MAPi_EQ_MAP;
                  MAP_ID] THEN
      SIMP[LENGTH_MAPi; flat_pmatch_list_append; ALL_APPEND] THEN REPEAT CONJ_TAC THENL
       [(* the bindings *)
        MATCH_MP_TAC LIST_REL_APPEND_suff THEN CONJ_TAC THENL
         [SIMP[LIST_REL_EL_EQN; LENGTH_MAPi; EL_MAPi; pure_eval_to_def; flat_evaluate_def] THEN
          REPEAT STRIP_TAC THEN
          DRULE_THEN (fun th -> IMP_REWRITE_TAC[th]) ALOOKUP_rel_EQ_ALOOKUP THEN
          SIMP[ARITH_ss; o_THM; dec_enc; ALOOKUP_APPEND] THEN
          IMP_REWRITE_TAC[ISPEC `MAP (h:(num#mlstring)#flat_pat#num#flat_exp->mlstring#flat_v) zs`
            FLATPAUX_ALOOKUP_unique] THEN EXISTS_TAC `EL n (a1:flat_v list)` THEN
          FS[MEM_MAP; MEM_REVERSE; MEM_FILTER; MEM_MAPi; domain_lookup; EXISTS_PAIR_THM;
             enc_num_to_name_inj; EQ_ADD_LCANCEL];
          FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC MONO_ALL2) THEN
          SIMP[FORALL_PAIR_THM] THEN
          REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
           [COND_CASES_TAC THEN SIMP[domain_insert; IN_INSERT]; ALL_TAC] THEN
          RW[ALOOKUP_rel_def] THEN
          DRULE_THEN (fun th -> IMP_REWRITE_TAC[th]) ALOOKUP_rel_EQ_ALOOKUP THEN
          SIMP[ALOOKUP_APPEND; o_THM; case_eq "option"; ALOOKUP_NONE; MEM_MAP; MEM_REVERSE;
               MEM_FILTER; MEM_MAPi; EXISTS_PAIR_THM] THEN
          CONJ_TAC THENL
           [DISJ1_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN FS[dec_enc] THEN DECIDE_TAC; DECIDE_TAC]];
        DECIDE_TAC;
        IMP_REWRITE_TAC[ALOOKUP_rel_APPEND_L_false] THEN
        SIMP[GSYM ALL_MEM; MEM_MAP; MEM_REVERSE; MEM_FILTER; MEM_MAPi; LEFT_IMP_EXISTS_THM] THEN
        RW[] THEN FS[dec_enc] THEN DECIDE_TAC;
        ONCE_REWRITE_TAC[GSYM ALL_EL] THEN SIMP[LENGTH_MAPi; EL_MAPi] THEN
        REPEAT STRIP_TAC THENL
         [FS[flat_pat_bindings_def; pats_bindings_FLAT_MAP; EVERY_FLAT; EVERY_REVERSE; ALL_MAP;
             o_DEF] THEN FS[GSYM ALL_EL];
          DECIDE_TAC; DECIDE_TAC];
        FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC MONO_ALL) THEN
        SIMP[FORALL_PAIR_THM] THEN ARITH_TAC]) ih);
    (* Pas *)
    DISCH_THEN(fun ih -> open_tac THEN
      FS[flat_pat_bindings_def; ALL_APPEND] THEN GVS[case_eq "match_result"] THEN
      PAIRARG_TAC THEN GVS[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `env:(flat_v)flat_environment`) THEN
      SIMP[pure_eval_to_def; ALOOKUP_rel_refl] THEN DISCH_TAC THEN
      RFS[flat_evaluate_def; opt_bind_def; ALOOKUP_DEF] THEN
      DRULE_THEN (IRULE o REWRITE_RULE[IMP_IMP]) ih THEN
      EXISTS_INST_TAC [`CONS (h':flat_v) t'`,`vs:flat_v list`;
        `CONS (v:varN,h':flat_v) pre_bindings`,`pre_bindings:(varN#flat_v)list`] THEN
      ASM_EXISTS_TAC THEN
      SUBGOAL_THEN `j < i + 1 /\ j < i + 2 /\ ~(i + 1 < j)` STRIP_ASSUME_TAC THENL
       [DECIDE_TAC; ALL_TAC] THEN
      SIMP[flat_pmatch_def; opt_bind_def; o_THM; dec_enc; ALOOKUP_rel_cons_false;
           ALOOKUP_rel_cons] THEN
      new_var_tac);
    (* Pref *)
    DISCH_THEN(fun ih -> open_tac THEN
      QPAT_X_ASSUM "_ = Match _" MP_TAC THEN CASES_ON `h':flat_v` THEN SIMP[flat_pmatch_def] THEN
      RW[case_eq "match_result"; case_eq "option"; case_eq "store_v"] THEN
      PAIRARG_TAC THEN GVS[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `env:(flat_v)flat_environment`) THEN
      SIMP[pure_eval_to_def; ALOOKUP_rel_refl] THEN DISCH_TAC THEN
      RFS[flat_evaluate_def; FLATPAUX_do_app_simps] THEN FS[opt_bind_def; flat_pat_bindings_def] THEN
      DRULE_THEN (IRULE o REWRITE_RULE[IMP_IMP]) ih THEN
      EXISTS_INST_TAC [`CONS (a:flat_v) t'`,`vs:flat_v list`] THEN ASM_EXISTS_TAC THEN
      SUBGOAL_THEN `j < i + 1 /\ j < i + 2 /\ ~(i + 1 < j)` STRIP_ASSUME_TAC THENL
       [DECIDE_TAC; ALL_TAC] THEN
      SIMP[flat_pmatch_def; opt_bind_def; dec_enc; ALOOKUP_rel_cons_false] THEN
      new_var_tac)]);;

(* HOL4 add_mono_thm: ALOOKUP_rel_mono_rel is a monotonicity theorem for    *)
(* inductive definitions                                                     *)
let () = monotonicity_theorems :=
  SPEC_ALL ALOOKUP_rel_mono_rel :: !monotonicity_theorems;;

let flat_patternProof_v_rel_rules,flat_patternProof_v_rel_ind,
    flat_patternProof_v_rel_cases,flat_patternProof_v_rel_strongind =
  cake_inductive
  `(!v v'. simple_basic_val_rel v v' /\
           ALL2 flat_patternProof_v_rel (v_container_xs v) (v_container_xs v')
           ==> flat_patternProof_v_rel v v') /\
   (!N env1 n x env2 cfg.
      flat_patternProof_env_rel N env1 env2 /\
      FST (flat_pattern_compile_exp cfg x) < N
      ==> flat_patternProof_v_rel (flat_Closure env1 n x)
            (flat_Closure env2 n (SND (SND (flat_pattern_compile_exp cfg x))))) /\
   (!N env1 fs x env2 cfg.
      flat_patternProof_env_rel N env1 env2 /\
      ALL (\(n,m,e). FST (flat_pattern_compile_exp cfg e) < N) fs
      ==> flat_patternProof_v_rel (flat_Recclosure env1 fs x)
            (flat_Recclosure env2
               (MAP (\(n,m,e). (n,m,SND (SND (flat_pattern_compile_exp cfg e))))
                    fs) x)) /\
   (!N env1 env2.
      ALOOKUP_rel (\x. dec_name_to_num x < N) flat_patternProof_v_rel
        (flat_environment_v env1) (flat_environment_v env2)
      ==> flat_patternProof_env_rel N env1 env2)`;;
(* HOL4: v_rel_l_cases is computed from the nchotomy of v and v_rel_cases;  *)
(* here it is stated (one conjunct per constructor of flat_v)               *)

let v_rel_l_cases = prove
 (`(flat_patternProof_v_rel (flat_Litv l) v2 <=> v2 = flat_Litv l) /\
   (flat_patternProof_v_rel (flat_Conv stmp vs) v2 <=>
      ?vs2. v2 = flat_Conv stmp vs2 /\ ALL2 flat_patternProof_v_rel vs vs2) /\
   (flat_patternProof_v_rel (flat_Closure env n e) v2 <=>
      ?N env2 cfg.
        v2 = flat_Closure env2 n (SND (SND (flat_pattern_compile_exp cfg e))) /\
        flat_patternProof_env_rel N env env2 /\
        FST (flat_pattern_compile_exp cfg e) < N) /\
   (flat_patternProof_v_rel (flat_Recclosure env fs n) v2 <=>
      ?N env2 cfg.
        v2 = flat_Recclosure env2
               (MAP (\(n,m,e). (n,m,SND (SND (flat_pattern_compile_exp cfg e))))
                    fs) n /\
        flat_patternProof_env_rel N env env2 /\
        ALL (\(n,m,e). FST (flat_pattern_compile_exp cfg e) < N) fs) /\
   (flat_patternProof_v_rel (flat_Loc b lnum) v2 <=> v2 = flat_Loc b lnum) /\
   (flat_patternProof_v_rel (flat_Vectorv vs) v2 <=>
      ?vs2. v2 = flat_Vectorv vs2 /\ ALL2 flat_patternProof_v_rel vs vs2)`,
  REPEAT CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 flat_patternProof_v_rel_cases] THEN
  RW[simple_basic_val_rel_def; v_container_xs_def] THEN EQ_TAC THEN RW[] THEN FS[v_container_xs_def]);;
(* HOL4: val env_rel_def (an ML binding, not a stored theorem) *)
let FLATPAUX_env_rel_def = prove
 (`!N env1 env2.
     flat_patternProof_env_rel N env1 env2 <=>
     ALOOKUP_rel (\x. dec_name_to_num x < N) flat_patternProof_v_rel
       (flat_environment_v env1) (flat_environment_v env2)`,
  REWRITE_TAC[CONJUNCT2 flat_patternProof_v_rel_cases]);;

let install_conf_rel_def = cake_def
  `install_conf_rel pat_cfg (ic1:(C)install_config) (ic2:(C)install_config) <=>
     install_config_compile_oracle ic2 =
       pure_co (MAP (compile_dec pat_cfg)) o install_config_compile_oracle ic1 /\
     install_config_compile ic1 =
       pure_cc (MAP (compile_dec pat_cfg)) (install_config_compile ic2)`;;

let flat_patternProof_state_rel_def = cake_def
  `flat_patternProof_state_rel cfg (s:(C,FFI)flat_state) (t:(C,FFI)flat_state) <=>
     flat_state_clock t = flat_state_clock s /\
     ALL2 (sv_rel flat_patternProof_v_rel) (flat_state_refs s) (flat_state_refs t) /\
     flat_state_ffi t = flat_state_ffi s /\
     ALL2 (OPTREL flat_patternProof_v_rel) (flat_state_globals s)
       (flat_state_globals t) /\
     install_conf_rel cfg (flat_state_eval_config s) (flat_state_eval_config t)`;;

let flat_patternProof_state_rel_initial_state = prove
 (`install_conf_rel cfg (ic1:(C)install_config) ic2
   ==> flat_patternProof_state_rel cfg (flat_initial_state (ffi:(FFI)ffi_state) k ic1)
         (flat_initial_state ffi k ic2)`,
  REWRITE_TAC[flat_patternProof_state_rel_def; flat_initial_state_def;
              flat_state_INFO.ri_accessors; ALL2] THEN MESON_TAC[]);;

(* HOL4 [local] *)
let flat_patternProof_state_rel_IMP_clock = prove
 (`flat_patternProof_state_rel cfg (s:(C,FFI)flat_state) t
   ==> flat_state_clock t = flat_state_clock s`,
  SIMP_TAC[flat_patternProof_state_rel_def]);;

(* HOL4: the [local] overload nv_rel N is written out:                       *)
(* ALOOKUP_rel (\x. dec_name_to_num x < N) flat_patternProof_v_rel          *)

let match_rel_def = sem1aux_def
  `(match_rel N (Match env1) (Match env2) <=>
      ALOOKUP_rel (\x. dec_name_to_num x < N) flat_patternProof_v_rel env1 env2) /\
   (match_rel N No_match No_match <=> T) /\
   (match_rel N Match_type_error Match_type_error <=> T) /\
   (match_rel N _ _ <=> F)`;;

let match_rel_thms = prove
 (`(match_rel N Match_type_error e <=> e = Match_type_error) /\
   (match_rel N e Match_type_error <=> e = Match_type_error) /\
   (match_rel N No_match e <=> e = No_match) /\
   (match_rel N e No_match <=> e = No_match)`,
  CASES_ON `e:((varN#flat_v)list)match_result` THEN SIMP[match_rel_def]);;
let _ = cake_add_simps [match_rel_thms];;

let match_rel_IMP = prove
 (`match_rel N e e'
   ==> (e = No_match /\ e = e') \/
       (e = Match_type_error /\ e = e') \/
       (?env1 env2. e = Match env1 /\ e' = Match env2 /\
                    ALOOKUP_rel (\x. dec_name_to_num x < N)
                      flat_patternProof_v_rel env1 env2)`,
  CASES_ON `e:((varN#flat_v)list)match_result` THEN SIMP[] THEN
  CASES_ON `e':((varN#flat_v)list)match_result` THEN SIMP[match_rel_def]);;

let MAX_ADD_LESS = prove
 (`MAX i j + k < l <=> i + k < l /\ j + k < l`,
  ARITH_TAC);;

let LESS_MAX_ADD = prove
 (`l < MAX i j + k <=> l < i + k \/ l < j + k`,
  ARITH_TAC);;

let MAX_ADD_LE = prove
 (`MAX i j + k <= l <=> i + k <= l /\ j + k <= l`,
  ARITH_TAC);;

let flat_patternProof_env_rel_mono = prove
 (`flat_patternProof_env_rel i env1 env2 /\ j <= i
   ==> flat_patternProof_env_rel j env1 env2`,
  RW[FLATPAUX_env_rel_def] THEN DRULE_THEN (IRULE o REWRITE_RULE[IMP_IMP]) ALOOKUP_rel_mono THEN
  SIMP[ARITH_ss]);;

let env_rel_ALOOKUP = prove
 (`flat_patternProof_env_rel N env1 env2 /\ dec_name_to_num n < N
   ==> OPTREL flat_patternProof_v_rel (ALOOKUP (flat_environment_v env1) n)
         (ALOOKUP (flat_environment_v env2) n)`,
  REWRITE_TAC[FLATPAUX_env_rel_def; ALOOKUP_rel_def] THEN MESON_TAC[]);;
let flat_patternProof_ALOOKUP_MAP_3 = prove
 (`(!x. MEM x xs ==> FST ((f:A#B->A#C) x) = FST x)
   ==> ALOOKUP (MAP f xs) x = OPTION_MAP (\y. SND (f (x,y))) (ALOOKUP xs x)`,
  SPEC_TAC(`xs:(A#B)list`,`xs:(A#B)list`) THEN LIST_INDUCT_TAC THEN
  RW[MAP; ALOOKUP_DEF] THEN FS[DISJ_IMP_THM; FORALL_AND_THM] THEN
  CASES_ON `(f:A#B->A#C) h` THEN CASES_ON `h:A#B` THEN RFS[]);;

let ALOOKUP_rel_MAP_same = prove
 (`(!x. MEM x xs ==> FST ((f:D->A#B) x) = FST ((g:D->A#C) x) /\
                     (P (FST (g x)) ==> R (SND (f x)) (SND (g x))))
   ==> ALOOKUP_rel P R (MAP f xs) (MAP g xs)`,
  SPEC_TAC(`xs:D list`,`xs:D list`) THEN LIST_INDUCT_TAC THEN
  RW[MAP; ALOOKUP_rel_empty] THEN FS[DISJ_IMP_THM; FORALL_AND_THM] THEN
  CASES_ON `(f:D->A#B) h` THEN CASES_ON `(g:D->A#C) h` THEN FS[ALOOKUP_rel_cons]);;
let do_opapp_thm = prove
 (`flat_do_opapp vs1 = SOME (env1,exp) /\ ALL2 flat_patternProof_v_rel vs1 vs2
   ==> ?i sg exp' env2 cfg. flat_pattern_compile_exp cfg exp = (i,sg,exp') /\
         flat_patternProof_env_rel (i + 1) env1 env2 /\
         flat_do_opapp vs2 = SOME (env2,exp')`,
  REWRITE_TAC[flat_do_opapp_def; case_eq "list"; case_eq "flat_v"; case_eq "option"; pair_case_eq;
       COND_CASE_EQ] THEN
  RW[] THEN GVS[LIST_REL_CONS1; v_rel_l_cases] THEN SIMP[PAIR_FST_SND_EQ] THENL
   [EXISTS_TAC `cfg:flat_pattern_config` THEN FS[FLATPAUX_env_rel_def] THEN
    IRULE ALOOKUP_rel_cons THEN SIMP[] THEN
    DRULE_THEN (IRULE o REWRITE_RULE[IMP_IMP]) ALOOKUP_rel_mono THEN SIMP[ARITH_ss];
    EXISTS_INST_TAC [`cfg:flat_pattern_config`,`cfg':flat_pattern_config`] THEN
    FS[find_recfun_ALOOKUP; flat_patternProof_ALOOKUP_MAP_3; FORALL_PAIR_THM] THEN
    CONJ_TAC THENL
     [SIMP[FLATPAUX_env_rel_def; build_rec_env_eq_MAP] THEN
      IRULE ALOOKUP_rel_cons THEN SIMP[] THEN IRULE ALOOKUP_rel_append_suff THENL
       [REWRITE_TAC[GSYM MAP_o] THEN IRULE ALOOKUP_rel_MAP_same THEN
        SIMP[FORALL_PAIR_THM; o_THM; v_rel_l_cases] THEN ASM_MESON_TAC[];
        FS[GSYM FLATPAUX_env_rel_def] THEN IMP_RES_TAC ALOOKUP_MEM THEN
        FS[GSYM ALL_MEM; FORALL_PAIR_THM] THEN RES_TAC THEN
        IRULE flat_patternProof_env_rel_mono THEN ASM_EXISTS_TAC THEN DECIDE_TAC];
      CONV_TAC(ONCE_DEPTH_CONV FLATPAUX_PAIRED_ABS_CONV) THEN
      ASM_SIMP_TAC[GSYM MAP_o; o_DEF; ETA_AX]]]);;

let do_opapp_thm_REVERSE = prove
 (`flat_do_opapp (REVERSE vs1) = SOME (env1,exp) /\
   ALL2 flat_patternProof_v_rel vs1 vs2
   ==> ?i sg exp' env2 cfg. flat_pattern_compile_exp cfg exp = (i,sg,exp') /\
         flat_patternProof_env_rel (i + 1) env1 env2 /\
         flat_do_opapp (REVERSE vs2) = SOME (env2,exp')`,
  RW[] THEN DRULE_THEN IRULE do_opapp_thm THEN SIMP[EVERY2_REVERSE]);;

(* before pmatch_thm, which uses it for Pref (HOL4 proves it after) *)
let flat_patternProof_simple_state_rel = prove
 (`flat_simple_state_rel flat_patternProof_v_rel
     (flat_patternProof_state_rel cfg:(C,FFI)flat_state->(C,FFI)flat_state->bool)`,
  REWRITE_TAC[flat_simple_state_rel_def; flat_patternProof_state_rel_def;
              flat_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[]);;

(* HOL4: the overload nv_rel N is written out; cfg and N are free *)
let pmatch_thm = prove
 (`(!(s:(C,FFI)flat_state) p v vs r s1 v1 vs1.
      flat_pmatch s p v vs = r /\ ~(r = Match_type_error) /\
      flat_patternProof_state_rel cfg s s1 /\ flat_patternProof_v_rel v v1 /\
      ALOOKUP_rel (\x. dec_name_to_num x < N) flat_patternProof_v_rel vs vs1
      ==> ?r1. flat_pmatch s1 p v1 vs1 = r1 /\ match_rel N r r1) /\
   (!(s:(C,FFI)flat_state) ps v vs r s1 v1 vs1.
      flat_pmatch_list s ps v vs = r /\ ~(r = Match_type_error) /\
      flat_patternProof_state_rel cfg s s1 /\ ALL2 flat_patternProof_v_rel v v1 /\
      ALOOKUP_rel (\x. dec_name_to_num x < N) flat_patternProof_v_rel vs vs1
      ==> ?r1. flat_pmatch_list s1 ps v1 vs1 = r1 /\ match_rel N r r1)`,
  SIMP[] THEN MATCH_MP_TAC flat_pmatch_ind THEN REWRITE_TAC[flat_pmatch_def] THEN
  SIMP[match_rel_def; v_rel_l_cases] THEN REPEAT CONJ_TAC THENL
   [(* Pvar *)
    RW[] THEN MATCH_MP_TAC ALOOKUP_rel_cons THEN ASM_REWRITE_TAC[];
    (* Plit *)
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN FS[match_rel_def; flat_pmatch_def] THEN
    COND_CASES_TAC THEN FS[match_rel_def; flat_pmatch_def];
    (* Pcon *)
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN IMP_RES_TAC LIST_REL_LENGTH THEN FS[flat_pmatch_def] THEN
    COND_CASES_TAC THEN FS[] THEN COND_CASES_TAC THEN RFS[match_rel_def];
    (* Pas *)
    REPEAT STRIP_TAC THEN FS[flat_pmatch_def] THEN FIRST_X_ASSUM IRULE THEN FS[] THEN
    IRULE ALOOKUP_rel_cons THEN FS[];
    (* Pref *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[flat_pmatch_def] THEN
    CASES_ON `store_lookup lnum (flat_state_refs (s:(C,FFI)flat_state))` THEN FS[] THEN
    DRULE_THEN DRULE (MATCH_MP_CURRIED simple_state_rel_store_lookup
      flat_patternProof_simple_state_rel) THEN
    RW[sv_rel_cases] THEN FS[] THEN FIRST_X_ASSUM IRULE THEN ASM_SIMP_TAC[];
    (* pmatch_list on [] *)
    SIMP[flat_pmatch_def; match_rel_def];
    (* pmatch_list on a cons *)
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN FS[flat_pmatch_def] THEN
    CASES_ON `flat_pmatch (s:(C,FFI)flat_state) p v bindings` THEN RFS[] THEN
    REPEAT ((FIRST_X_ASSUM DRULE ORELSE CASE_TAC) THEN RW[] THEN FS[match_rel_def])]);;

let simple_val_rel_step_isClosure = prove
 (`simple_basic_val_rel x y ==> ~isClosure x /\ ~isClosure y`,
  CASES_ON `x:flat_v` THEN RW[simple_basic_val_rel_def] THEN FS[isClosure_simps]);;
let flat_patternProof_simple_val_rel = prove
 (`flat_simple_val_rel flat_patternProof_v_rel`,
  REWRITE_TAC[flat_simple_val_rel_def] THEN ONCE_REWRITE_TAC[CONJUNCT1 flat_patternProof_v_rel_cases] THEN
  RW[] THEN EQ_TAC THEN RW[] THEN FS[] THEN ASM_MESON_TAC[simple_val_rel_step_isClosure]);;

(* HOL4: do_app_thm = MATCH_MP simple_do_app_thm (CONJ simple_val_rel      *)
(* simple_state_rel)                                                         *)
let flat_patternProof_do_app_thm =
  MATCH_MP simple_do_app_thm
    (CONJ flat_patternProof_simple_val_rel flat_patternProof_simple_state_rel);;

let do_app_thm_REVERSE = prove
 (`flat_do_app s1 op (REVERSE vs1) = SOME (t1,r1) /\
   flat_patternProof_state_rel cfg (s1:(C,FFI)flat_state) s2 /\
   ALL2 flat_patternProof_v_rel vs1 vs2
   ==> ?t2 r2. result_rel flat_patternProof_v_rel flat_patternProof_v_rel r1 r2 /\
               flat_patternProof_state_rel cfg t1 t2 /\
               flat_do_app s2 op (REVERSE vs2) = SOME (t2,r2)`,
  RW[] THEN DRULE_THEN (IRULE o REWRITE_RULE[IMP_IMP]) flat_patternProof_do_app_thm THEN
  SIMP[EVERY2_REVERSE]);;

let do_if_helper = prove
 (`flat_do_if b x y = SOME e /\ flat_patternProof_v_rel b b'
   ==> ((b' = flat_Boolv T) <=> (b = flat_Boolv T)) /\
       ((b' = flat_Boolv F) <=> (b = flat_Boolv F))`,
  CASES_ON `b:flat_v` THEN RW[flat_Boolv_def; v_rel_l_cases] THEN EQ_TAC THEN RW[] THEN FS[]);;

let FLATPAUX_MAX_LT = prove
 (`!a b c. MAX a b < c <=> a < c /\ b < c`,
  REWRITE_TAC[MAX] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let MAX_LIST_LESS_EVERY = prove
 (`!xs. MAX_LIST xs < N <=> 0 < N /\ ALL (\x. x < N) xs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAX_LIST; ALL; FLATPAUX_MAX_LT] THEN
  REWRITE_TAC[CONJ_ACI]);;

let max_dec_name_LESS_EVERY = prove
 (`!ns. max_dec_name ns < N <=>
        0 < N /\ ALL (\n. dec_name_to_num n < N) ns`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[max_dec_name_def; ALL; FLATPAUX_MAX_LT] THEN
  REWRITE_TAC[CONJ_ACI]);;

let encode_val_def = cake_def_wf
  `MEASURE flat_v_size`
  TERM_TAC
  `(encode_val (flat_Litv l) = pattern_semantics_Litv l) /\
   (encode_val (flat_Conv stmp xs) =
      Term (match stmp with NONE -> NONE | SOME (i,_) -> SOME i)
           (MAP encode_val xs)) /\
   (encode_val (flat_Loc _ n) = pattern_semantics_RefPtr n) /\
   (encode_val _ = pattern_semantics_Other)`;;

let encode_val_ind = cake_ind "encode_val";;
let FLATPAUX_option_DISTINCT = CONJ option_DISTINCT (distinctness "option");;

let decode_test_simulation = prove
 (`dt_test test enc_v = SOME b /\
   pure_eval_to (s:(C,FFI)flat_state) env x v /\ enc_v = encode_val v
   ==> pure_eval_to s env (flat_pattern_decode_test tr test x) (flat_Boolv b)`,
  CASES_ON `test:dTest` THEN CASES_ON `v:flat_v` THEN REWRITE_TAC[encode_val_def] THEN
  EVERY_CASE_TAC THEN RW[] THEN FS[dt_test_def] THEN
  FS[flat_pattern_decode_test_def; pure_eval_to_def; flat_evaluate_def] THEN
  SIMP[FLATPAUX_do_app_simps; flat_do_eq_def; lit_same_type_sym] THEN RW[flat_Boolv_def] THEN FS[]);;

let app_pos_Term_IMP = prove
 (`!xs n. app_pos refs (Pos n pos) (Term c xs) = SOME y
          ==> n < LENGTH xs /\ app_pos refs pos (EL n xs) = SOME y`,
  LIST_INDUCT_TAC THEN SIMP[app_pos_def] THEN RW[] THEN CASES_ON `n:num` THEN
  FS[app_pos_def; EL; HD; TL]);;

let encode_refs_def = cake_def
  `encode_refs (s:(C,FFI)flat_state) =
     FUN_FMAP (\i. encode_val (match EL i (flat_state_refs s) with Refv v -> v))
       (pred_set_count (LENGTH (flat_state_refs s)) INTER
        {i | ?v. EL i (flat_state_refs s) = Refv v})`;;

let FLOOKUP_encode_refs = prove
 (CASE_TERM
  `FLOOKUP (encode_refs (s:(C,FFI)flat_state)) n =
     if n < LENGTH (flat_state_refs s)
     then (match EL n (flat_state_refs s) with
             Refv v -> SOME (encode_val v)
           | _ -> NONE)
     else NONE`,
  SIMP[encode_refs_def; FLOOKUP_FUN_FMAP; FINITE_INTER; pred_set_count_DEF; FINITE_NUMSEG_LT; IN_INTER;
       IN_ELIM_THM] THEN
  EVERY_CASE_TAC THEN FS[]);;

let decode_pos_simulation = prove
 (`!pos exp x.
     app_pos (encode_refs (s:(C,FFI)flat_state)) pos (encode_val x) = SOME enc_y /\
     pure_eval_to s env exp x
     ==> ?y. enc_y = encode_val y /\ pure_eval_to s env (decode_pos tr exp pos) y`,
  MATCH_MP_TAC position_INDUCT THEN SIMP[app_pos_def; decode_pos_def] THEN RW[] THEN
  FS[pure_eval_to_def] THEN FIRST_X_ASSUM IRULE THEN
  CASES_ON `a0:num` THEN CASES_ON `x:flat_v` THEN FS[app_pos_def; encode_val_def] THENL
   [CASES_ON `a1':flat_v list` THEN FS[app_pos_def] THEN
    SIMP[flat_evaluate_def; FLATPAUX_do_app_simps];
    FS[case_eq "option"] THEN SIMP[flat_evaluate_def; FLATPAUX_do_app_simps] THEN
    FS[store_lookup_def; FLOOKUP_encode_refs; COND_CASE_EQ; case_eq "store_v"; case_eq "option"];
    SIMP[flat_evaluate_def; FLATPAUX_do_app_simps] THEN CASES_ON `a1':flat_v list` THEN
    FS[app_pos_def] THEN DRULE app_pos_Term_IMP THEN STRIP_TAC THEN FS[EL_MAP]]);;
let fold_Boolv = GSYM (CONJ (REWRITE_RULE[GSYM bool_to_tag_def] flat_Boolv_def)
                             bool_to_tag_def);;

let flat_patternProof_do_eq_Boolv = prove
 (`flat_do_eq (flat_Boolv x) (flat_Boolv y) = Eq_val (x = y)`,
  SIMP[flat_Boolv_def; flat_do_eq_def; flat_ctor_same_type_def] THEN EVERY_CASE_TAC THEN
  FS[true_tag_def; false_tag_def]);;

let do_if_Boolv = prove
 (`flat_do_if (flat_Boolv x) y z = SOME (if x then y else z)`,
  SIMP[flat_Boolv_def; flat_do_if_def] THEN EVERY_CASE_TAC THEN FS[true_tag_def; false_tag_def]);;

let flat_patternProof_evaluate_Bool = prove
 (`flat_evaluate (env:(flat_v)flat_environment) (s:(C,FFI)flat_state)
     [flat_Bool t b] = (s,Rval [flat_Boolv b])`,
  RW[flat_evaluate_def; flat_Boolv_def; flat_Bool_def; bool_to_tag_def]);;

let SmartIf_thm = prove
 (`SmartIf t e p q =
     if ?t. e = flat_Bool t T then p else
     if ?t. e = flat_Bool t F then q else
     flat_If t e p q`,
  SIMP[SmartIf_def; flat_Bool_def; bool_to_tag_def] THEN RW[] THEN FS[] THEN
  REPEAT CASE_TAC THEN FS[true_tag_def; false_tag_def]);;

let evaluate_SmartIf = prove
 (`flat_evaluate (env:(flat_v)flat_environment) (s:(C,FFI)flat_state)
     [SmartIf t x y z] =
   flat_evaluate env s [flat_If t x y z]`,
  SIMP[SmartIf_thm] THEN RW[] THEN
  RW[flat_evaluate_def; flat_patternProof_evaluate_Bool; do_if_Boolv]);;

let decode_guard_simulation = prove
 (`!gd b. dt_eval_guard (encode_refs (s:(C,FFI)flat_state)) (encode_val y) gd =
            SOME b /\
          pure_eval_to s env x y
          ==> pure_eval_to s env (decode_guard tr x gd) (flat_Boolv b)`,
  MATCH_MP_TAC dGuard_INDUCT THEN REWRITE_TAC[decode_guard_def; dt_eval_guard_def] THEN
  FS[pure_eval_to_def; flat_evaluate_def; case_eq "option"] THEN RW[] THEN
  SIMP[evaluate_SmartIf] THEN
  RFS[flat_Bool_def; flat_evaluate_def; fold_Boolv; FLATPAUX_do_app_simps;
      flat_patternProof_do_eq_Boolv; do_if_Boolv; COND_CASE_EQ] THEN
  DRULE decode_pos_simulation THEN SIMP[pure_eval_to_def] THEN
  DISCH_THEN(DRULE_THEN STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  DRULE decode_test_simulation THEN SIMP[pure_eval_to_def] THEN
  DISCH_THEN(IRULE o REWRITE_RULE[IMP_IMP]) THEN ASM_MESON_TAC[]);;
(* the induction hypotheses are used by IMP_RES_TAC and kept out of the    *)
(* assumptions: simplified with simp_guard x = True they would become      *)
(* rewrites with a bare variable on the left (!b. P b ==> b), which make   *)
(* the simplifier loop                                                       *)
let simp_guard_thm = prove
 (`!gd x. dt_eval_guard r v gd = SOME x
          ==> dt_eval_guard r v (simp_guard gd) = SOME x`,
  let ih_tac =
    DISCH_THEN(fun ih -> REPEAT STRIP_TAC THEN
      FS[dt_eval_guard_def; case_eq "option"; COND_CASE_EQ] THEN
      MAP_EVERY IMP_RES_TAC (CONJUNCTS ih)) THEN
    RW[simp_guard_def] THEN GVS[dt_eval_guard_def; case_eq "option"; COND_CASE_EQ] THEN
    REPEAT CASE_TAC THEN GVS[dt_eval_guard_def; case_eq "option"; COND_CASE_EQ] in
  MATCH_MP_TAC simp_guard_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ih_tac; ih_tac; ih_tac; RW[simp_guard_def]; RW[simp_guard_def]]);;
let decode_dtree_simulation = prove
 (CASE_TERM
  `dt_eval (encode_refs (s:(C,FFI)flat_state)) (encode_val y) dtree = SOME v /\
   pure_eval_to s env x y
   ==> flat_evaluate env s [decode_dtree tr exps x default_x dtree] =
       flat_evaluate env s [match v with
                              MatchSuccess i -> (match lookup i exps with
                                                   SOME exp -> exp
                                                 | NONE -> default_x)
                            | _ -> default_x]`,
  SPEC_TAC(`v:dt_result`,`v:dt_result`) THEN SPEC_TAC(`dtree:dTree`,`dtree:dTree`) THEN
  MATCH_MP_TAC dTree_INDUCT THEN REWRITE_TAC[dt_eval_def; decode_dtree_def] THEN
  RW[flat_evaluate_def] THEN FS[case_eq "option"] THEN
  IMP_RES_TAC simp_guard_thm THEN DRULE_THEN (DRULE_THEN MP_TAC) decode_guard_simulation THEN
  FS[dt_eval_guard_def] THEN RW[pure_eval_to_def] THEN
  GVS[evaluate_SmartIf; flat_evaluate_def; do_if_Boolv] THEN COND_CASES_TAC THEN GVS[]);;

let encode_pat_match_simulation = prove
 (`(!(s:(C,FFI)flat_state) pat v pre_bindings res.
      flat_pmatch s pat v pre_bindings = res /\ ~(res = Match_type_error)
      ==> pattern_semantics_pmatch (encode_refs s) (encode_pat pat)
            (encode_val v) =
          (if res = No_match then PMatchFailure else PMatchSuccess)) /\
   (!(s:(C,FFI)flat_state) ps vs pre_bindings res.
      flat_pmatch_list s ps vs pre_bindings = res /\ ~(res = Match_type_error)
      ==> pattern_semantics_pmatch_list (encode_refs s) (MAP encode_pat ps)
            (MAP encode_val vs) =
          (if res = No_match then PMatchFailure else PMatchSuccess))`,
  SIMP[] THEN MATCH_MP_TAC flat_pmatch_ind THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[encode_pat_def; encode_val_def; ETA_AX] THEN
  FS[flat_pmatch_def; pattern_semantics_pmatch_def] THEN
  TRY (FS[COND_CASE_EQ] THEN RVEQ_TAC THEN FS[] THEN NO_TAC) THENL
   [(* Plit *)
    ASM_CASES_TAC `l:lit = l'` THEN FS[lit_same_type_refl] THEN COND_CASES_TAC THEN RFS[];
    (* Pcon *)
    GVS[pmatch_stamps_ok_cases] THEN
    SIMP[pattern_semantics_pmatch_def; is_sibling_def] THEN RFS[] THEN EVERY_CASE_TAC THEN
    FS[pattern_semantics_pmatch_def; is_sibling_def];
    (* Pref *)
    FS[store_lookup_def] THEN
    ASM_CASES_TAC `lnum < LENGTH (flat_state_refs (s:(C,FFI)flat_state))` THEN FS[] THEN
    CASES_ON `EL lnum (flat_state_refs (s:(C,FFI)flat_state))` THEN RFS[FLOOKUP_encode_refs];
    (* pmatch_list on a cons *)
    CASES_ON `flat_pmatch (s:(C,FFI)flat_state) p v bindings` THEN FS[] THEN
    CASES_ON `flat_pmatch_list (s:(C,FFI)flat_state) ps vs bindings` THEN RFS[]]);;
let pmatch_rows_encode = prove
 (CASE_TERM `!(pats:(flat_pat#A)list) j_offs.
     ~(pmatch_rows pats (s:(C,FFI)flat_state) v = Match_type_error)
     ==> (match pattern_semantics_match (encode_refs s)
                  (MAPi (\j (p,x). (encode_pat p, j + j_offs)) pats)
                  (encode_val v) with
            NONE -> F
          | SOME (MatchSuccess n) ->
              ?i env. n = i + j_offs /\ i < LENGTH pats /\
                      flat_pmatch s (FST (EL i pats)) v [] = Match env /\
                      pmatch_rows pats s v = Match (env, EL i pats)
          | _ -> pmatch_rows pats s v = No_match)`,
  LIST_INDUCT_TAC THEN SIMP[MAPi_DEF; pmatch_rows_def; pattern_semantics_match_def] THEN
  CASES_ON `h:flat_pat#A` THEN
  SIMP[MAPi_DEF; pmatch_rows_def; pattern_semantics_match_def; o_DEF] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `SUC j_offs`) THEN SIMP[ADD_CLAUSES] THEN
  CASES_ON `flat_pmatch (s:(C,FFI)flat_state) x v []` THEN FS[] THEN
  IMP_RES_TAC (CONJUNCT1 (SIMP_RULE[] encode_pat_match_simulation)) THEN FS[] THEN
  REPEAT (CASE_TAC THEN FS[]) THENL
   [STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`SUC i`; `env:(varN#flat_v)list`] THEN
    ASM_SIMP_TAC[EL; TL; ADD_CLAUSES; LE_SUC_LT];
    CASES_ON `pmatch_rows (t:(flat_pat#A)list) (s:(C,FFI)flat_state) v` THEN FS[];
    STRIP_TAC THEN EXISTS_TAC `0` THEN ASM_SIMP_TAC[EL; HD; ADD_CLAUSES; LE_0];
    EXISTS_TAC `0` THEN ASM_SIMP_TAC[EL; HD; ADD_CLAUSES; LE_0]]);;

(* the evaluation of the arguments of a constructor value *)
(* the induction hypotheses are DISCH_THEN arguments, not assumptions (with  *)
(* them in the assumptions RFS on the Pcon cases overflows the stack)        *)
let naive_pattern_match_correct = prove
 (`!t mats vs bindings exp res.
     ALL2 (pure_eval_to (s:(C,FFI)flat_state) env) (MAP SND mats) vs /\
     flat_pmatch_list s (MAP FST mats) vs bindings = res /\
     ~(res = Match_type_error) /\
     naive_pattern_match t mats = exp
     ==> pure_eval_to s env exp (flat_Boolv (~(res = No_match)))`,
  let open_tac = RW[] THEN
    FS[pure_eval_to_def; flat_evaluate_def; flat_Bool_def; fold_Boolv; flat_pmatch_def;
       evaluate_SmartIf] in
  (* the arguments of a constructor pattern: the induction hypothesis for   *)
  (* the values a1 of the constructor followed by the others ys             *)
  let args_tac ih =
    QSPECL_THEN ["APPEND a1 ys"; "bindings"] MP_TAC ih THEN
    REWRITE_TAC[MAP_APPEND; MAP_MAPi; o_DEF; MAPi_EQ_MAP; MAP_ID] THEN
    ASM_SIMP_TAC[flat_pmatch_list_append; LIST_REL_APPEND_EQ; LENGTH_MAPi; pure_eval_to_def] THEN
    SIMP[LIST_REL_EL_EQN; LENGTH_MAPi; EL_MAPi; pure_eval_to_def; flat_evaluate_def;
         FLATPAUX_do_app_simps] in
  SIMP[] THEN MATCH_MP_TAC naive_pattern_match_ind THEN REWRITE_TAC[naive_pattern_match_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [(* [] *)
    open_tac;
    (* Pany *)
    DISCH_THEN(fun ih -> open_tac THEN IRULE (REWRITE_RULE[pure_eval_to_def] ih) THEN
      ASM_REWRITE_TAC[]);
    (* Pvar *)
    DISCH_THEN(fun ih -> open_tac THEN IRULE (REWRITE_RULE[pure_eval_to_def] ih) THEN
      ASM_REWRITE_TAC[]);
    (* Plit *)
    DISCH_THEN(fun ih -> open_tac THEN CASES_ON `y:flat_v` THEN FS[flat_pmatch_def] THEN
      FS[FLATPAUX_do_app_simps; flat_do_eq_def] THEN RW[] THEN FS[lit_same_type_sym; do_if_Boolv] THEN
      EVERY_CASE_TAC THEN FS[] THEN SIMP[flat_evaluate_def; flat_Bool_def; fold_Boolv] THEN
      TRY (IRULE (REWRITE_RULE[pure_eval_to_def] ih) THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      ASM_MESON_TAC[lit_same_type_sym]);
    (* Pcon NONE *)
    DISCH_THEN(fun ih -> open_tac THEN
      CASES_ON `y:flat_v` THEN FS[flat_pmatch_def] THEN RW[] THEN FS[pmatch_stamps_ok_cases] THEN
      RFS[] THEN args_tac ih);
    (* Pas *)
    DISCH_THEN(fun ih -> open_tac THEN
      QSPECL_THEN ["CONS y ys"; "CONS (nm,y) bindings"] MP_TAC ih THEN
      ASM_SIMP_TAC[pure_eval_to_def; flat_pmatch_def; ALL2; MAP] THEN
      CASES_ON `flat_pmatch (s:(C,FFI)flat_state) p y (CONS (nm,y) bindings)` THEN FS[] THEN
      CASES_ON `flat_pmatch_list (s:(C,FFI)flat_state) (MAP FST (mats:(flat_pat#flat_exp)list))
                  ys bindings` THEN FS[] THEN
      MAP_EVERY IMP_RES_TAC (CONJUNCTS pmatch_any_no_match @ CONJUNCTS pmatch_any_match) THEN
      FS[] THEN FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `CONS (nm:varN,y:flat_v) bindings`) THEN FS[]);
    (* Pcon SOME *)
    DISCH_THEN(fun ih -> open_tac THEN
      CASES_ON `y:flat_v` THEN FS[flat_pmatch_def] THEN RW[] THEN FS[pmatch_stamps_ok_cases] THEN
      RFS[] THEN RVEQ_TAC THEN FS[FLATPAUX_do_app_simps; do_if_Boolv] THEN RW[] THEN
      FS[flat_evaluate_def; fold_Boolv] THEN TRY (EVERY_CASE_TAC THEN FS[] THEN NO_TAC) THEN
      args_tac ih);
    (* Pref *)
    DISCH_THEN(fun ih -> open_tac THEN
      CASES_ON `y:flat_v` THEN FS[flat_pmatch_def] THEN
      CASES_ON `store_lookup a1 (flat_state_refs (s:(C,FFI)flat_state))` THEN FS[] THEN
      CASES_ON `a:(flat_v)store_v` THEN FS[] THEN
      QSPECL_THEN ["CONS a' ys"; "bindings"] MP_TAC ih THEN
      SIMP[pure_eval_to_def; flat_pmatch_def; ALL2; MAP; flat_evaluate_def; FLATPAUX_do_app_simps])]);;
(* HOL4: an ML-derived instance of naive_pattern_match_correct *)
let naive_pattern_match_correct_inst =
  GEN_ALL (REWRITE_RULE[MAP; ALL2; pure_eval_to_def]
    (SPECL [`t:tra`; `[p:flat_pat,x:flat_exp]`; `[v:flat_v]`;
            `[]:(varN#flat_v)list`] naive_pattern_match_correct));;

let naive_pattern_matches_correct = prove
 (CASE_TERM `!t x mats dflt exp v res.
     naive_pattern_matches t x mats dflt = exp /\
     pure_eval_to (s:(C,FFI)flat_state) env x v /\
     pmatch_rows mats s v = res /\ ~(res = Match_type_error)
     ==> flat_evaluate env s [exp] =
         (match res with
            Match (_,_,exp) -> flat_evaluate env s [exp]
          | _ -> flat_evaluate env s [dflt])`,
  SIMP[] THEN MATCH_MP_TAC naive_pattern_matches_ind THEN
  REWRITE_TAC[naive_pattern_matches_def; pmatch_rows_def] THEN RW[] THEN
  SIMP[evaluate_SmartIf; flat_evaluate_def] THEN FS[pure_eval_to_def] THEN
  DRULE_THEN (fun th -> IMP_REWRITE_TAC[th]) (CAKE_SIMP_RULE[] naive_pattern_match_correct_inst) THEN
  SIMP[flat_pmatch_def; do_if_Boolv] THEN
  CASES_ON `flat_pmatch (s:(C,FFI)flat_state) p v' []` THEN RFS[] THEN
  CASES_ON `pmatch_rows (ps:(flat_pat#flat_exp)list) (s:(C,FFI)flat_state) v'` THEN RFS[]);;

let pmatch_rows_same_FST = prove
 (CASE_TERM `!(pats:(flat_pat#A)list) (pats2:(flat_pat#B)list).
     MAP FST pats = MAP FST pats2
     ==> (match pmatch_rows pats (s:(C,FFI)flat_state) v with
            Match_type_error -> pmatch_rows pats2 s v = Match_type_error
          | No_match -> pmatch_rows pats2 s v = No_match
          | Match (env,p,e) ->
              ?i. i < LENGTH pats2 /\ EL i pats = (p,e) /\
                  pmatch_rows pats2 s v = Match (env,EL i pats2))`,
  LIST_INDUCT_TAC THEN SIMP[pmatch_rows_def] THEN GEN_TAC THEN CASES_ON `pats2:(flat_pat#B)list` THEN
  SIMP[pmatch_rows_def] THEN CASES_ON `h:flat_pat#A` THEN CASES_ON `a0:flat_pat#B` THEN
  SIMP[pmatch_rows_def] THEN RW[] THEN FIRST_X_ASSUM DRULE THEN
  REPEAT (CASE_TAC THEN FS[]) THEN RW[] THEN
  TRY (EXISTS_TAC `0` THEN SIMP[EL; HD] THEN NO_TAC) THEN
  EXISTS_TAC `SUC i` THEN SIMP[EL; TL]);;

(* HOL4 [local]: pattern_comp's comp_thm with IS_SOME *)
let flat_patternProof_comp_thm = prove
 (`!refs rows v x. pattern_semantics_match refs rows v = SOME x
     ==> dt_eval refs v (pattern_comp_comp rows) = pattern_semantics_match refs rows v`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC pattern_comp_comp_thm THEN
  ASM_REWRITE_TAC[FLATPAUX_option_DISTINCT]);;

let evaluate_compile_pats = prove
 (CASE_TERM `~(pmatch_rows (pats:(flat_pat#flat_exp)list) (s:(C,FFI)flat_state) v =
     Match_type_error) /\
   pure_eval_to s env exp v
   ==> flat_evaluate env s [compile_pats cfg naive t N exp default_x pats] =
       flat_evaluate env s [match pmatch_rows pats s v with
                              Match (env',p',e') -> compile_pat_rhs t N exp (p',e')
                            | _ -> default_x]`,
  RW[compile_pats_def] THENL
   [DRULE_THEN (fun th -> IMP_REWRITE_TAC[th]) (CAKE_SIMP_RULE[] naive_pattern_matches_correct) THEN
    MP_TAC(ISPECL [`pats:(flat_pat#flat_exp)list`;
      `ZIP (MAP FST (pats:(flat_pat#flat_exp)list)) (MAP (compile_pat_rhs t N exp) pats)`]
      pmatch_rows_same_FST) THEN
    SIMP[MAP_ZIP; LENGTH_MAP] THEN REPEAT (CASE_TAC THEN FS[]) THEN RW[] THEN
    FS[EL_ZIP; EL_MAP; LENGTH_MAP];
    DRULE (ISPECL [`pats:(flat_pat#flat_exp)list`; `0`] pmatch_rows_encode) THEN SIMP[ADD_CLAUSES] THEN
    TOP_CASE_TAC THEN SIMP[] THEN IMP_RES_TAC flat_patternProof_comp_thm THEN FS[] THEN
    DRULE_THEN DRULE decode_dtree_simulation THEN SIMP[lookup_fromList] THEN
    EVERY_CASE_TAC THEN FS[] THEN SIMP[EL_MAP]]);;

let compile_match_pmatch_rows = prove
 (CASE_TERM `!pats k sg pats2 res.
   compile_match cfg pats = (k,sg,pats2) /\
   flat_patternProof_state_rel s_cfg (s:(C,FFI)flat_state) t /\
   flat_patternProof_v_rel v v' /\ k <= N /\
   pmatch_rows pats s v = res
   ==> (match res with
          Match_type_error -> T
        | No_match -> pmatch_rows pats2 t v' = No_match
        | Match (env,p,e) ->
            ?i env'. i < LENGTH pats /\ i < LENGTH pats2 /\ (p,e) = EL i pats /\
                     ALOOKUP_rel (\x. dec_name_to_num x < N) flat_patternProof_v_rel
                       env env' /\
                     pmatch_rows pats2 t v' = Match (env',EL i pats2))`,
  LIST_INDUCT_TAC THEN TRY (CASES_ON `h:flat_pat#flat_exp`) THEN
  SIMP[flat_pattern_compile_exp_def; pmatch_rows_def] THEN
  RW[] THEN REPEAT PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN
  CASES_ON `flat_pmatch (s:(C,FFI)flat_state) x v []` THEN FS[] THEN
  DRULE (CONJUNCT1 pmatch_thm) THEN SIMP[] THEN DISCH_THEN (DRULE_THEN DRULE) THEN
  SIMP[] THEN DISCH_THEN (QSPECL_THEN ["N"; "[]"] MP_TAC) THEN
  SIMP[ALOOKUP_rel_empty] THEN RW[] THEN RFS[ARITH_ss; pmatch_rows_def] THEN
  EVERY_CASE_TAC THEN FS[match_rel_def] THEN
  TRY (EXISTS_TAC `0` THEN SIMP[] THEN NO_TAC) THEN
  EXISTS_TAC `SUC i'` THEN SIMP[]);;

let compile_match_EL = prove
 (`!pats pats2 k sg i.
     compile_match cfg pats = (k,sg,pats2) /\ i < LENGTH pats /\
     EL i pats = (pat,exp)
     ==> ?exp_i sg exp'. flat_pattern_compile_exp cfg exp = (exp_i,sg,exp') /\
                         EL i pats2 = (pat,exp') /\ exp_i <= k /\
                         max_dec_name (flat_pat_bindings pat) <= k`,
  LIST_INDUCT_TAC THEN TRY (CASES_ON `h:flat_pat#flat_exp`) THEN REWRITE_TAC[flat_pattern_compile_exp_def] THEN
  RW[] THEN REPEAT PAIRARG_TAC THEN FS[] THEN IMP_RES_TAC LENGTH_compile_exps_IMP THEN
  CASES_ON `i:num` THEN FS[ARITH_ss] THEN RVEQ_TAC THEN FS[ARITH_ss] THEN FIRST_X_ASSUM DRULE THEN RW[] THEN
  SIMP[ARITH_ss]);;

let evaluate_compile_pat_rhs = prove
 (`flat_evaluate (flat_environment_v_fupd f env3) (s:(C,FFI)flat_state)
     [compile_pat_rhs tr N (Var_local tr (enc_num_to_name N)) (p,exp)] = (t,res) /\
   flat_pmatch s p v [] = Match bindings /\
   flat_patternProof_env_rel M env1 env2 /\
   ALOOKUP_rel (\x. dec_name_to_num x < M) flat_patternProof_v_rel l_bindings
     bindings /\
   f (flat_environment_v env3) =
     CONS (enc_num_to_name N,v) (flat_environment_v env2) /\
   N <= M /\ max_dec_name (flat_pat_bindings p) < N - 1
   ==> ?ext_env. flat_evaluate ext_env s [exp] = (t,res) /\
         flat_patternProof_env_rel (N - 1)
           (flat_environment_v_fupd
              (K (APPEND l_bindings (flat_environment_v env1))) env1) ext_env`,
  SIMP[compile_pat_rhs_def; max_dec_name_LESS_EVERY] THEN
  CASES_ON `compile_pat_bindings tr (N + 1) [p,N,Var_local tr (enc_num_to_name N)] exp` THEN
  RW[] THEN
  DRULE (SPEC `[v:flat_v]` (GEN `vs:flat_v list` (SPEC_ALL compile_pat_bindings_simulation))) THEN
  SIMP[MAP; flat_pmatch_def; case_eq "match_result"] THEN
  REPEAT (DISCH_THEN DRULE) THEN
  DISCH_THEN (QSPECL_THEN ["N - 1"; "flat_environment_v env2"] MP_TAC) THEN
  SIMP[ARITH_ss] THEN REWRITE_TAC[IMP_IMP] THEN ANTS_TAC THENL
   [SUBGOAL_THEN `N > N - 1 /\ N < N + 1` STRIP_ASSUME_TAC THENL [DECIDE_TAC; ALL_TAC] THEN
    SIMP[ALOOKUP_rel_def; pure_eval_to_def; flat_evaluate_def; dec_enc] THEN RW[] THEN
    FS[dec_enc] THEN DECIDE_TAC;
    ALL_TAC] THEN
  RW[] THEN ASM_EXISTS_TAC THEN FS[FLATPAUX_env_rel_def; ALOOKUP_rel_def; ALOOKUP_APPEND] THEN
  X_GEN_TAC `nm:varN` THEN DISCH_TAC THEN REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC `nm:varN`)) THEN
  SIMP[ARITH_ss; OPTREL_def; case_eq "option"] THEN RW[] THEN FS[]);;

let flat_patternProof_state_rel_dec_clock = prove
 (`flat_patternProof_state_rel cfg (s1:(C,FFI)flat_state) s2
   ==> flat_patternProof_state_rel cfg (flat_dec_clock s1) (flat_dec_clock s2)`,
  SIMP[flat_patternProof_state_rel_def; flat_dec_clock_def]);;

let OPTION_ALL_FORALL = prove
 (`OPTION_ALL (P:A->bool) x <=> (!y. x = SOME y ==> P y)`,
  CASES_ON `x:A option` THEN SIMP[OPTION_ALL_def]);;

let do_eval_thm = prove
 (`flat_do_eval xs (flat_state_eval_config (s:(C,FFI)flat_state)) =
     SOME (decs,eval_config,rv) /\
   flat_patternProof_state_rel cfg s t /\ ALL2 flat_patternProof_v_rel xs ys
   ==> ?rv' decs' eval_config'.
         flat_do_eval ys (flat_state_eval_config t) = SOME (decs',eval_config',rv') /\
         flat_patternProof_state_rel cfg
           (flat_state_eval_config_fupd (K eval_config) s)
           (flat_state_eval_config_fupd (K eval_config') t) /\
         flat_patternProof_v_rel rv rv' /\
         decs' = MAP (compile_dec cfg) decs`,
  RW[flat_patternProof_state_rel_def] THEN RULE_ASSUM_TAC (REWRITE_RULE[flat_do_eval_def]) THEN
  FS[case_eq "list"; case_eq "option"; case_eq "prod"; COND_CASE_EQ] THEN RVEQ_TAC THEN
  FS[LIST_REL_CONS1] THEN RVEQ_TAC THEN FS[] THEN
  DRULE_THEN DRULE (MATCH_MP flat_simple_val_rel_v_to_bytes flat_patternProof_simple_val_rel) THEN
  DRULE_THEN DRULE (MATCH_MP flat_simple_val_rel_v_to_words flat_patternProof_simple_val_rel) THEN
  RW[] THEN FS[install_conf_rel_def] THEN FS[pure_cc_def] THEN RFS[] THEN FS[pure_co_def] THEN
  RVEQ_TAC THEN FS[flat_do_eval_def] THEN
  SIMP[shift_seq_def; FUN_EQ_THM; o_THM; FST_PAIR_MAP; SND_PAIR_MAP; I_THM] THEN
  SIMP[flat_Unitv_def; v_rel_l_cases]);;


let flat_patternProof_evaluate_decs_sing = prove
 (`flat_evaluate_decs (s:(C,FFI)flat_state) [d] = evaluate_dec s d`,
  SIMP[flat_evaluate_def] THEN EVERY_CASE_TAC THEN SIMP[]);;

(* ------------------------------------------------------------------------- *)
(* compile_exps_evaluate                                                      *)
(* ------------------------------------------------------------------------- *)

(* The induction predicates of compile_exps_evaluate, as constants: the      *)
(* induction hypotheses are then small atoms in the assumptions, which keeps *)
(* the simplifier fast, and FLATPAUX_CE_IH unfolds one where it is used.     *)
(* flat_evaluate_ind has a predicate for evaluate_dec too (HOL4's has not).  *)

let FLATPAUX_ce_P_def = new_definition
 `FLATPAUX_ce_P s_cfg env1 (s1:(C,FFI)flat_state) xs <=>
    !t1 r1 i sg ys N env2 s2 cfg.
      flat_evaluate env1 s1 xs = (t1,r1) /\
      flat_pattern_compile_exps cfg xs = (i,sg,ys) /\
      flat_patternProof_env_rel N env1 env2 /\
      flat_patternProof_state_rel s_cfg s1 s2 /\ i < N /\
      ~(r1 = Rerr (Rabort Rtype_error))
      ==> ?t2 r2. result_rel (ALL2 flat_patternProof_v_rel) flat_patternProof_v_rel
                    r1 r2 /\
                  flat_patternProof_state_rel s_cfg t1 t2 /\
                  flat_evaluate env2 s2 ys = (t2,r2)`;;

let FLATPAUX_ce_Pdec_def = new_definition
 `FLATPAUX_ce_Pdec s_cfg (s1:(C,FFI)flat_state) d <=>
    !t1 res s2 cfg.
      evaluate_dec s1 d = (t1,res) /\
      flat_patternProof_state_rel s_cfg s1 s2 /\
      ~(res = SOME (Rabort Rtype_error))
      ==> ?t2 res'. evaluate_dec s2 (compile_dec cfg d) = (t2,res') /\
                    OPTREL (exc_rel flat_patternProof_v_rel) res res' /\
                    flat_patternProof_state_rel s_cfg t1 t2`;;

let FLATPAUX_ce_Pdecs_def = new_definition
 `FLATPAUX_ce_Pdecs s_cfg (s1:(C,FFI)flat_state) decs <=>
    !t1 res s2 cfg decs'.
      flat_evaluate_decs s1 decs = (t1,res) /\
      decs' = MAP (compile_dec cfg) decs /\
      flat_patternProof_state_rel s_cfg s1 s2 /\
      ~(res = SOME (Rabort Rtype_error))
      ==> ?t2 res'. flat_evaluate_decs s2 decs' = (t2,res') /\
                    OPTREL (exc_rel flat_patternProof_v_rel) res res' /\
                    flat_patternProof_state_rel s_cfg t1 t2`;;

let FLATPAUX_compile_exps_sing_eq = prove
 (`!cfg e i sg ys. flat_pattern_compile_exps cfg [e] = (i,sg,ys) <=>
     ?y. flat_pattern_compile_exp cfg e = (i,sg,y) /\ ys = [y]`,
  REPEAT GEN_TAC THEN SIMP[flat_pattern_compile_exp_def] THEN PAIRARG_TAC THEN
  PAIRARG_TAC THEN SIMP[ARITH_ss] THEN MESON_TAC[]);;

(* flat_evaluate_def without its clause for evaluate_dec (which applies to   *)
(* every declaration), and that clause                                        *)
let FLATPAUX_evaluate_nodec_def, FLATPAUX_evaluate_dec_clause =
  let is_dec th = can (find_term (fun t -> is_const t && fst(dest_const t) = "evaluate_dec"))
                      (lhs(snd(strip_forall(concl th)))) in
  let dec,nodec = partition is_dec (CONJUNCTS flat_evaluate_def) in
  end_itlist CONJ nodec, hd dec;;

(* an induction hypothesis of FLATPAUX_ce_all, unfolded as the goals are by  *)
(* FLATPAUX_CE_PRE_TAC (fails on the other assumptions)                       *)
let FLATPAUX_CE_IH =
  let rule = CAKE_SIMP_RULE[case_eq "prod"; PULL_EXISTS; FLATPAUX_MAX_LT] o
    REWRITE_RULE[FLATPAUX_ce_P_def; FLATPAUX_ce_Pdec_def; FLATPAUX_ce_Pdecs_def;
      flat_patternProof_evaluate_decs_sing; FLATPAUX_compile_exps_sing_eq;
      flat_pattern_compile_exp_def; PULL_EXISTS] in
  let is_P t = is_const t &&
    mem (fst(dest_const t)) ["FLATPAUX_ce_P"; "FLATPAUX_ce_Pdec"; "FLATPAUX_ce_Pdecs"] in
  fun th -> if can (find_term is_P) (concl th) then rule th else failwith "FLATPAUX_CE_IH";;

(* HOL4's last_x_assum drule \\ rpt (disch_then drule) \\ rw [] *)
let FLATPAUX_CE_IH_TAC =
  FIRST_X_ASSUM (DRULE o FLATPAUX_CE_IH) THEN REPEAT (DISCH_THEN DRULE) THEN RW[ARITH_ss];;

(* HOL4's fs [case_eq_thms] \\ rveq \\ fs [] on the result *)
let FLATPAUX_CE_RES_TAC = FS[case_eq "result"] THEN RVEQ_TAC THEN FS[];;

(* HOL4's first steps, common to all the cases *)
let FLATPAUX_CE_PRE_TAC =
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[FLATPAUX_ce_P_def; FLATPAUX_ce_Pdec_def; FLATPAUX_ce_Pdecs_def] THEN
  REWRITE_TAC[flat_patternProof_evaluate_decs_sing; FLATPAUX_compile_exps_sing_eq; PULL_EXISTS] THEN
  REWRITE_TAC[FLATPAUX_evaluate_nodec_def; flat_pattern_compile_exp_def] THEN
  REPEAT (GEN_TAC ORELSE DISCH_TAC ORELSE CONJ_TAC) THEN
  SIMP[flat_patternProof_v_rel_rules] THEN REPEAT PAIRARG_TAC THEN FS[] THEN
  RVEQ_TAC THEN REWRITE_TAC[evaluate_SmartIf; FLATPAUX_evaluate_nodec_def] THEN
  FS[flat_patternProof_v_rel_rules; FLATPAUX_MAX_LT];;

(* the compiled functions of a Letrec: HOL4 simp [MAP_MAP_o, o_DEF, UNCURRY] *)
let FLATPAUX_letrec_compile = prove
 (CASE_TERM `!(fs:(varN#varN#flat_exp)list) cfg N.
     MAP (\(a,b,(j,sg,e)). (a,b,e))
       (MAP (\fn. match fn with (a,b,c) -> (a,b,flat_pattern_compile_exp cfg c)) fs) =
     MAP (\(n,m,e). (n,m,SND (SND (flat_pattern_compile_exp cfg e)))) fs /\
     (MAX_LIST (MAP (\(a,b,(j,sg,e)). j)
       (MAP (\fn. match fn with (a,b,c) -> (a,b,flat_pattern_compile_exp cfg c)) fs)) < N <=>
      0 < N /\ ALL (\(n,m,e). FST (flat_pattern_compile_exp cfg e) < N) fs) /\
     MAP FST (MAP (\(n,m,e). (n,m,SND (SND (flat_pattern_compile_exp cfg e)))) fs) = MAP FST fs`,
  let pair_case_proj = prove
   (`pair_CASE (p:A#B) (f:A->B->C) = f (FST p) (SND p)`, CASES_ON `p:A#B` THEN SIMP[]) in
  REWRITE_TAC[MAX_LIST_LESS_EVERY; ALL_MAP; MAP_MAP_o; o_DEF; pair_case_proj] THEN
  CONV_TAC(DEPTH_CONV FLATPAUX_PAIRED_ABS_CONV) THEN REWRITE_TAC[FST; SND; ETA_AX]);;

let FLATPAUX_EL_PAIR_SYM = prove
 (`!(a:A) (b:B) i l. (a,b) = EL i l <=> EL i l = (a,b)`, MESON_TAC[]);;

(* the compiled patterns of a Mat or Handle (the common part of HOL4's two   *)
(* cases): the scrutinee value v1 (w1 compiled) is bound to k in env3 by f    *)
let FLATPAUX_ce_pats = prove
 (CASE_TERM `!env1 env2 env3 f (s':(C,FFI)flat_state) t2a v1 w1 pes ps2 j sgp N cfg tr k
      dflt d1 d2 t1 r1.
   (!p env' e'. pmatch_rows pes s' v1 = Match (env',p,e') /\ ALL_DISTINCT (flat_pat_bindings p)
      ==> FLATPAUX_ce_P s_cfg
            (flat_environment_v_fupd (K (APPEND env' (flat_environment_v env1))) env1) s' [e']) /\
   compile_match cfg pes = (j,sgp,ps2) /\ flat_patternProof_env_rel N env1 env2 /\
   (match pmatch_rows pes s' v1 with
      Match_type_error -> (s',Rerr (Rabort Rtype_error))
    | No_match -> (s',Rerr (Rraise d1))
    | Match (env',p',e') ->
        if ALL_DISTINCT (flat_pat_bindings p')
        then flat_evaluate (flat_environment_v_fupd
                              (K (APPEND env' (flat_environment_v env1))) env1) s' [e']
        else (s',Rerr (Rabort Rtype_error))) = (t1,r1) /\
   ~(r1 = Rerr (Rabort Rtype_error)) /\ j + 2 <= k /\ k <= N /\
   f (flat_environment_v env3) = CONS (enc_num_to_name k,w1) (flat_environment_v env2) /\
   flat_evaluate (flat_environment_v_fupd f env3) t2a [dflt] = (t2a,Rerr (Rraise d2)) /\
   flat_patternProof_v_rel d1 d2 /\
   flat_patternProof_state_rel s_cfg s' t2a /\ flat_patternProof_v_rel v1 w1
   ==> ?t2 r2. result_rel (ALL2 flat_patternProof_v_rel) flat_patternProof_v_rel r1 r2 /\
               flat_patternProof_state_rel s_cfg t1 t2 /\
               flat_evaluate (flat_environment_v_fupd f env3) t2a
                 [compile_pats cfg sgp tr k (Var_local tr (enc_num_to_name k)) dflt ps2] =
               (t2,r2)`,
  RW[] THEN IMP_REWRITE_TAC[INST [`w1:flat_v`,`v:flat_v`] evaluate_compile_pats] THEN
  SIMP[pure_eval_to_def; FLATPAUX_evaluate_nodec_def] THEN
  SUBGOAL_THEN `j <= N` ASSUME_TAC THENL [DECIDE_TAC; ALL_TAC] THEN
  DRULE_THEN DRULE compile_match_pmatch_rows THEN REPEAT (DISCH_THEN DRULE) THEN SIMP[] THEN
  QCASES_ON "pmatch_rows pes s' v1" THEN FS[COND_CASE_EQ] THEN REPEAT PAIRARG_TAC THEN
  FS[COND_CASE_EQ] THEN RVEQ_TAC THEN FS[] THEN
  RW[FLATPAUX_EL_PAIR_SYM] THEN DRULE_THEN (DRULE_THEN DRULE) compile_match_EL THEN RW[] THEN RFS[] THEN
  IMP_RES_TAC pmatch_rows_IMP_pmatch THEN
  QCASES_ON "flat_evaluate (flat_environment_v_fupd f env3) t2a
               [compile_pat_rhs tr k (Var_local tr (enc_num_to_name k)) (p,exp')]" THEN
  DRULE_THEN DRULE evaluate_compile_pat_rhs THEN REPEAT (DISCH_THEN DRULE) THEN RW[ARITH_ss] THEN
  FLATPAUX_CE_IH_TAC THEN FS[]);;

(* thunks: HOL4 inlines these in the ForceThunk case *)
let FLATPAUX_dest_thunk_IsThunk_IMP = prove
 (`!vs (st:(flat_v store_v)list) m v.
     flat_dest_thunk vs st = flat_IsThunk m v
     ==> ?n. vs = [flat_Loc F n] /\ n < LENGTH st /\ EL n st = Thunk m v`,
  GEN_TAC THEN QCASES_ON "vs" THEN SIMP[flat_dest_thunk_def] THEN QCASES_ON "a0" THEN
  SIMP[flat_dest_thunk_def] THEN QCASES_ON "a1" THEN SIMP[flat_dest_thunk_def; store_lookup_def] THEN
  SIMP[case_eq "option"; case_eq "store_v"; case_eq "thunk_mode"; COND_CASE_EQ] THEN RW[] THEN FS[]);;

let FLATPAUX_dest_thunk_rel = prove
 (`!vs vs' (s:(C,FFI)flat_state) t m v cfg.
     flat_dest_thunk vs (flat_state_refs s) = flat_IsThunk m v /\
     ALL2 flat_patternProof_v_rel vs vs' /\ flat_patternProof_state_rel cfg s t
     ==> ?v'. flat_dest_thunk vs' (flat_state_refs t) = flat_IsThunk m v' /\
              flat_patternProof_v_rel v v'`,
  RW[flat_patternProof_state_rel_def] THEN IMP_RES_TAC FLATPAUX_dest_thunk_IsThunk_IMP THEN
  RVEQ_TAC THEN FS[LIST_REL_CONS1; v_rel_l_cases] THEN RVEQ_TAC THEN FS[LIST_REL_EL_EQN] THEN
  QPAT_X_ASSUM "!n. n < LENGTH (flat_state_refs s) ==> _" (QSPEC_THEN "n" MP_TAC) THEN
  FS[sv_rel_cases] THEN RW[] THEN
  SIMP[flat_dest_thunk_def; store_lookup_def] THEN QCASES_ON "m" THEN SIMP[]);;

let FLATPAUX_update_thunk_SOME_IMP = prove
 (`!vs (st:(flat_v store_v)list) ws st1.
     flat_update_thunk vs st ws = SOME st1
     ==> ?n w. vs = [flat_Loc F n] /\ ws = [w] /\ flat_dest_thunk [w] st = flat_NotThunk /\
               store_assign n (Thunk Evaluated w) st = SOME st1`,
  REPEAT GEN_TAC THEN QCASES_ON "vs" THEN SIMP[flat_update_thunk_def] THEN QCASES_ON "a0" THEN
  SIMP[flat_update_thunk_def] THEN QCASES_ON "a1" THEN SIMP[flat_update_thunk_def] THEN
  QCASES_ON "ws" THEN SIMP[flat_update_thunk_def] THEN QCASES_ON "a1" THEN
  SIMP[flat_update_thunk_def; COND_CASE_EQ; case_eq "flat_dest_thunk_ret"] THEN RW[] THEN FS[]);;

let FLATPAUX_update_thunk_rel = prove
 (`!vs vs' (s:(C,FFI)flat_state) t ws ws' refs cfg.
     flat_update_thunk vs (flat_state_refs s) ws = SOME refs /\
     ALL2 flat_patternProof_v_rel vs vs' /\ ALL2 flat_patternProof_v_rel ws ws' /\
     flat_patternProof_state_rel cfg s t
     ==> ?refs'. flat_update_thunk vs' (flat_state_refs t) ws' = SOME refs' /\
                 flat_patternProof_state_rel cfg (flat_state_refs_fupd (K refs) s)
                   (flat_state_refs_fupd (K refs') t)`,
  RW[] THEN IMP_RES_TAC FLATPAUX_update_thunk_SOME_IMP THEN RVEQ_TAC THEN
  FS[LIST_REL_CONS1; v_rel_l_cases] THEN RVEQ_TAC THEN
  DRULE_THEN DRULE (MATCH_MP_CURRIED simple_state_rel_store_assign flat_patternProof_simple_state_rel) THEN
  DISCH_THEN (QSPEC_THEN "Thunk Evaluated y" MP_TAC) THEN SIMP[sv_rel_def] THEN RW[] THEN
  SIMP[flat_update_thunk_def] THEN
  QPAT_ASSUM "flat_patternProof_state_rel cfg s t"
    (STRIP_ASSUME_TAC o REWRITE_RULE[flat_patternProof_state_rel_def]) THEN
  DRULE_THEN DRULE (MATCH_MP_CURRIED FLATSEMAUX_bad_thunk_update_rel flat_patternProof_simple_val_rel) THEN
  DISCH_THEN (QSPEC_THEN "Evaluated" MP_TAC) THEN RFS[flat_bad_thunk_update_def]);;

let FLATPAUX_compile_AppUnit = prove
 (`flat_pattern_compile_exp cfg (flat_AppUnit (Var_local t nm)) =
     (dec_name_to_num nm,F,flat_AppUnit (Var_local t nm))`,
  SIMP[flat_AppUnit_def; flat_pattern_compile_exp_def; op_sets_globals_def; ARITH_ss]);;

let FLATPAUX_result_rel_list_result = prove
 (`!(R:A->B->bool) (Q:C->D->bool) r1 r2.
     result_rel (ALL2 R) Q (list_result r1) (list_result r2) <=> result_rel R Q r1 r2`,
  REPEAT GEN_TAC THEN QCASES_ON "r1" THEN QCASES_ON "r2" THEN SIMP[list_result_def; result_rel_def]);;

(* HOL4: compile_exps_evaluate, by ho_match_mp_tac evaluate_ind2 *)
let FLATPAUX_ce_all = prove
 (`(!env s xs. FLATPAUX_ce_P s_cfg env (s:(C,FFI)flat_state) xs) /\
   (!s d. FLATPAUX_ce_Pdec s_cfg (s:(C,FFI)flat_state) d) /\
   (!s ds. FLATPAUX_ce_Pdecs s_cfg (s:(C,FFI)flat_state) ds)`,
  MATCH_MP_TAC flat_evaluate_ind THEN REPEAT CONJ_TAC THEN FLATPAUX_CE_PRE_TAC THENL
   [(* [e1; e2; ...] *)
    FLATPAUX_CE_IH_TAC THEN FLATPAUX_CE_RES_TAC THEN IMP_RES_TAC flat_evaluate_length THEN
    RFS[] THEN FS[] THEN FLATPAUX_CE_IH_TAC THEN FS[LENGTH_EQ_NUM_compute] THEN RVEQ_TAC THEN FS[];
    (* Raise *)
    FLATPAUX_CE_IH_TAC THEN FLATPAUX_CE_RES_TAC THEN IMP_RES_TAC flat_evaluate_length THEN
    FS[LENGTH_EQ_NUM_compute] THEN RVEQ_TAC THEN FS[];
    (* Handle *)
    FLATPAUX_CE_IH_TAC THEN FS[pmatch_rows_def; flat_pmatch_def; flat_pat_bindings_def] THEN
    FS[case_eq "result"; case_eq "error_result"] THEN RVEQ_TAC THEN FS[] THEN RVEQ_TAC THEN FS[] THEN
    IRULE FLATPAUX_ce_pats THEN ASM_EXISTS_TAC THEN
    SIMP[ARITH_ss; FLATPAUX_evaluate_nodec_def; ALOOKUP_DEF];
    (* Con, no tag *)
    FLATPAUX_CE_IH_TAC THEN FLATPAUX_CE_RES_TAC THEN SIMP[v_rel_l_cases; EVERY2_REVERSE];
    (* Con with a tag *)
    FLATPAUX_CE_IH_TAC THEN FLATPAUX_CE_RES_TAC THEN SIMP[v_rel_l_cases; EVERY2_REVERSE];
    (* Var_local *)
    DRULE_THEN DRULE env_rel_ALOOKUP THEN STRIP_TAC THEN FS[OPTREL_def];
    (* Fun *)
    SIMP[v_rel_l_cases] THEN MAP_EVERY EXISTS_TAC [`N:num`; `cfg:flat_pattern_config`] THEN SIMP[];
    (* App *)
    FLATPAUX_CE_IH_TAC THEN
    QCASES_ON "op = Src Opapp" THEN TRY (QCASES_ON "op = Src Eval") THEN
    TRY (QCASES_ON "op = Src (ThunkOp ForceThunk)") THEN FS[] THEN FLATPAUX_CE_RES_TAC THENL
     [(* Opapp *)
      QCASES_ON "flat_do_opapp (REVERSE a)" THEN FS[] THEN REPEAT PAIRARG_TAC THEN FS[] THEN
      DRULE_THEN DRULE do_opapp_thm_REVERSE THEN RW[] THEN
      IMP_RES_TAC flat_patternProof_state_rel_IMP_clock THEN FS[COND_CASE_EQ] THEN RVEQ_TAC THEN
      FS[] THEN IMP_RES_TAC flat_patternProof_state_rel_dec_clock THEN FLATPAUX_CE_IH_TAC;
      (* Eval *)
      QCASES_ON "flat_do_eval (REVERSE a) (flat_state_eval_config s')" THEN FS[] THEN
      REPEAT PAIRARG_TAC THEN FS[] THEN IMP_RES_TAC EVERY2_REVERSE THEN
      DRULE_THEN DRULE do_eval_thm THEN REPEAT (DISCH_THEN DRULE) THEN RW[] THEN
      IMP_RES_TAC flat_patternProof_state_rel_IMP_clock THEN FS[COND_CASE_EQ] THEN RVEQ_TAC THEN
      FS[] THEN IMP_RES_TAC flat_patternProof_state_rel_dec_clock THEN
      FIRST_X_ASSUM (DRULE o FLATPAUX_CE_IH) THEN REPEAT (DISCH_THEN DRULE) THEN
      DISCH_THEN (MP_TAC o SPEC `s_cfg:flat_pattern_config`) THEN ANTS_TAC THENL
       [DISCH_TAC THEN RFS[]; ALL_TAC] THEN
      RW[] THEN FS[case_eq "option"] THEN RVEQ_TAC THEN RFS[OPTREL_def];
      (* ThunkOp ForceThunk *)
      QCASES_ON "flat_dest_thunk a (flat_state_refs s')" THEN FS[] THEN
      DRULE_THEN DRULE FLATPAUX_dest_thunk_rel THEN DISCH_THEN DRULE THEN STRIP_TAC THEN FS[] THEN
      QCASES_ON "a0" THEN FS[] THEN REPEAT PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN FS[] THEN
      FIRST_X_ASSUM (DRULE o CAKE_SIMP_RULE[FLATPAUX_compile_AppUnit] o FLATPAUX_CE_IH) THEN
      DISCH_THEN (QSPECL_THEN ["F"; "1"; "flat_environment_REC [implode \"f\",v'']"; "t2"]
        MP_TAC) THEN
      SIMP[FLATPAUX_env_rel_def; ALOOKUP_rel_cons; ALOOKUP_rel_empty; dec_name_to_num_def;
           strlen_implode] THEN
      RW[] THEN FS[case_eq "result"; case_eq "option"] THEN RVEQ_TAC THEN FS[] THEN RVEQ_TAC THEN
      FS[] THEN DRULE_THEN DRULE FLATPAUX_update_thunk_rel THEN REPEAT (DISCH_THEN DRULE) THEN
      RW[] THEN FS[];
      (* the other primitives *)
      QCASES_ON "flat_do_app s' op (REVERSE a)" THEN FS[] THEN REPEAT PAIRARG_TAC THEN FS[] THEN
      DRULE_THEN (DRULE_THEN DRULE) do_app_thm_REVERSE THEN RW[] THEN
      FS[FLATPAUX_result_rel_list_result]];
    (* If *)
    FLATPAUX_CE_IH_TAC THEN FS[case_eq "result"; case_eq "option"] THEN RVEQ_TAC THEN FS[] THEN
    RVEQ_TAC THEN FS[] THEN RFS[] THEN IMP_RES_TAC flat_evaluate_sing THEN RVEQ_TAC THEN FS[] THEN
    DRULE_THEN DRULE do_if_helper THEN RW[] THEN FS[flat_do_if_def; COND_CASE_EQ] THEN RVEQ_TAC THEN
    FS[] THEN FLATPAUX_CE_IH_TAC THEN FS[];
    (* Mat *)
    FLATPAUX_CE_IH_TAC THEN FLATPAUX_CE_RES_TAC THEN IMP_RES_TAC flat_evaluate_sing THEN
    RVEQ_TAC THEN FS[] THEN IRULE FLATPAUX_ce_pats THEN ASM_EXISTS_TAC THEN
    SIMP[ARITH_ss; opt_bind_def; FLATPAUX_evaluate_nodec_def; flat_bind_exn_v_def; v_rel_l_cases];
    (* Let *)
    FLATPAUX_CE_IH_TAC THEN FLATPAUX_CE_RES_TAC THEN RFS[] THEN FS[] THEN
    FIRST_X_ASSUM (DRULE o FLATPAUX_CE_IH) THEN REPEAT (DISCH_THEN DRULE) THEN
    DISCH_THEN (IRULE o REWRITE_RULE[IMP_IMP]) THEN EXISTS_TAC `N:num` THEN
    IMP_RES_TAC flat_evaluate_sing THEN RVEQ_TAC THEN FS[FLATPAUX_env_rel_def; opt_bind_def] THEN
    CASE_TAC THEN FS[ALOOKUP_rel_cons];
    (* Letrec *)
    FS[FLATPAUX_letrec_compile; COND_CASE_EQ] THEN RFS[] THEN
    FIRST_X_ASSUM (DRULE o FLATPAUX_CE_IH) THEN REPEAT (DISCH_THEN DRULE) THEN
    DISCH_THEN (IRULE o REWRITE_RULE[IMP_IMP]) THEN EXISTS_TAC `N:num` THEN
    FS[FLATPAUX_env_rel_def; build_rec_env_eq_MAP] THEN IRULE ALOOKUP_rel_append_suff THEN
    SIMP[] THEN IRULE ALOOKUP_rel_eq_fst THEN REWRITE_TAC[MAP_MAP_o] THEN
    REWRITE_TAC[ALL2_MAP2; ALL2_ALL; GSYM ALL_MEM; FORALL_PAIR_THM; o_DEF] THEN
    SIMP[v_rel_l_cases] THEN RW[] THEN
    MAP_EVERY EXISTS_TAC [`N:num`; `cfg:flat_pattern_config`] THEN SIMP[FLATPAUX_env_rel_def];
    (* a declaration *)
    FS[FLATPAUX_evaluate_dec_clause; compile_dec_def] THEN REPEAT PAIRARG_TAC THEN FS[] THEN
    SUBGOAL_THEN `?i sg y. flat_pattern_compile_exp cfg (e:flat_exp) = (i,sg,y)`
      STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN RFS[] THEN
    FIRST_X_ASSUM (DRULE o FLATPAUX_CE_IH) THEN REPEAT (DISCH_THEN DRULE) THEN
    DISCH_THEN (QSPECL_THEN ["i + 1"; "flat_environment_REC []"] MP_TAC) THEN
    SIMP[FLATPAUX_env_rel_def; ALOOKUP_rel_empty; ARITH_ss] THEN DISCH_THEN DRULE THEN
    ANTS_TAC THENL [DISCH_TAC THEN FS[]; ALL_TAC] THEN
    RW[] THEN FS[flat_Unitv_def; case_eq "result"; COND_CASE_EQ] THEN RVEQ_TAC THEN
    FS[v_rel_l_cases] THEN RVEQ_TAC THEN FS[OPTREL_def];
    (* d :: ds *)
    FIRST_X_ASSUM (DRULE o FLATPAUX_CE_IH) THEN REPEAT (DISCH_THEN DRULE) THEN
    DISCH_THEN (MP_TAC o SPEC `cfg:flat_pattern_config`) THEN ANTS_TAC THENL
     [DISCH_TAC THEN RFS[]; ALL_TAC] THEN
    STRIP_TAC THEN FS[OPTREL_def] THEN RVEQ_TAC THEN FS[] THEN RVEQ_TAC THEN FS[] THEN
    FIRST_X_ASSUM (DRULE o FLATPAUX_CE_IH) THEN REPEAT (DISCH_THEN DRULE) THEN
    DISCH_THEN (MP_TAC o SPEC `cfg:flat_pattern_config`) THEN RW[] THEN FS[OPTREL_def]]);;

let compile_exps_evaluate = prove
 (`(!env1 (s1:(C,FFI)flat_state) xs t1 r1 i sg ys N env2 s2 cfg.
      flat_evaluate env1 s1 xs = (t1,r1) /\
      flat_pattern_compile_exps cfg xs = (i,sg,ys) /\
      flat_patternProof_env_rel N env1 env2 /\ flat_patternProof_state_rel s_cfg s1 s2 /\
      i < N /\ ~(r1 = Rerr (Rabort Rtype_error))
      ==> ?t2 r2. result_rel (ALL2 flat_patternProof_v_rel) flat_patternProof_v_rel
                    r1 r2 /\
                  flat_patternProof_state_rel s_cfg t1 t2 /\
                  flat_evaluate env2 s2 ys = (t2,r2)) /\
   (!(s1:(C,FFI)flat_state) decs s2 t1 cfg decs' res.
      flat_evaluate_decs s1 decs = (t1,res) /\
      decs' = MAP (compile_dec cfg) decs /\
      flat_patternProof_state_rel s_cfg s1 s2 /\
      ~(res = SOME (Rabort Rtype_error))
      ==> ?t2 res'. flat_evaluate_decs s2 decs' = (t2,res') /\
                    OPTREL (exc_rel flat_patternProof_v_rel) res res' /\
                    flat_patternProof_state_rel s_cfg t1 t2)`,
  REWRITE_TAC[REWRITE_RULE[FLATPAUX_ce_P_def; FLATPAUX_ce_Pdecs_def] FLATPAUX_ce_all]);;

let compile_decs_eval_sim = prove
 (`install_conf_rel cfg (ic1:(C)install_config) ic2
   ==> flat_eval_sim (ffi:(FFI)ffi_state) prog prog' ic1 ic2
         (\decs decs'. MAP (compile_dec cfg2) decs = decs') F`,
  SIMP[flat_eval_sim_def] THEN REPEAT STRIP_TAC THEN QEXISTS_TAC "0" THEN SIMP[] THEN
  DRULE (last (CONJUNCTS compile_exps_evaluate)) THEN SIMP[] THEN
  IMP_RES_TAC flat_patternProof_state_rel_initial_state THEN
  DISCH_THEN (QSPECL_THEN ["cfg"; "flat_initial_state ffi k ic2"; "cfg2"] MP_TAC) THEN
  SIMP[flat_patternProof_state_rel_initial_state] THEN RW[] THEN FS[OPTREL_def] THEN RW[] THEN
  FS[flat_patternProof_state_rel_def]);;

let compile_decs_semantics = prove
 (`install_conf_rel cfg (ic1:(C)install_config) ic2 /\
   ~(flat_semantics ic1 (ffi:(FFI)ffi_state) prog = Fail)
   ==> flat_semantics ic1 ffi prog =
       flat_semantics ic2 ffi (MAP (compile_dec cfg1) prog)`,
  RW[] THEN IRULE (REWRITE_RULE[IMP_IMP] flat_IMP_semantics_eq) THEN
  QEXISTS_TAC "\\decs decs'. MAP (compile_dec cfg1) decs = decs'" THEN
  SIMP[] THEN IRULE compile_decs_eval_sim THEN ASM_MESON_TAC[]);;

(* set_globals and esgc properties *)

(* HOL4's bagSimps.BAG_ss for these goals: the bags pointwise, then arithmetic *)
let FLATPAUX_BAG_TAC : tactic =
  let rws = [flat_set_globals_def; SUB_BAG_LEQ; BAG_UNION; EMPTY_BAG_alt; FUN_EQ_THM] in
  RULE_ASSUM_TAC(REWRITE_RULE rws) THEN REWRITE_TAC rws THEN
  (X_GEN_TAC `bx:num` ORELSE ALL_TAC) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall (concl th) then MP_TAC (SPEC `bx:num` th) else failwith "bag")) THEN
  ARITH_TAC;;

(* !N sg exp'. compile_exp cfg e = (N,sg,exp') ==> P exp' is P of the compiled *)
(* expression                                                                   *)
let FLATPAUX_FORALL_TRIPLE = prove
 (`!(X:A#B#C) P. (!a b c. X = (a,b,c) ==> P c) <=> P (SND (SND X))`,
  REPEAT GEN_TAC THEN QCASES_ON "X" THEN QCASES_ON "y" THEN SIMP[]);;

let set_globals_decode_pos = prove
 (`!p exp. flat_set_globals exp = EMPTY_BAG
           ==> flat_set_globals (decode_pos t exp p) = EMPTY_BAG`,
  MATCH_MP_TAC position_INDUCT THEN SIMP[decode_pos_def; flat_op_gbag_def]);;

let set_globals_decode_test = prove
 (`flat_set_globals exp = EMPTY_BAG
   ==> flat_set_globals (flat_pattern_decode_test t d exp) = EMPTY_BAG`,
  QCASES_ON "d" THEN SIMP[flat_pattern_decode_test_def; flat_op_gbag_def]);;

let set_globals_decode_guard = prove
 (`flat_set_globals exp = EMPTY_BAG
   ==> flat_set_globals (decode_guard t exp gd) = EMPTY_BAG`,
  INDUCT_ON `gd:dGuard` THEN SIMP[decode_guard_def; flat_Bool_def; flat_op_gbag_def] THEN
  RW[SmartIf_thm] THEN SIMP[set_globals_decode_test; set_globals_decode_pos]);;

let set_globals_decode_dtree_empty = prove
 (`flat_set_globals x = EMPTY_BAG /\ flat_set_globals dflt = EMPTY_BAG /\
   ALL (\y. flat_set_globals y = EMPTY_BAG) (toList br_spt)
   ==> flat_set_globals (decode_dtree t br_spt x dflt dtree) = EMPTY_BAG`,
  INDUCT_ON `dtree:dTree` THEN SIMP[decode_dtree_def; SmartIf_thm] THEN REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[set_globals_decode_guard; flat_set_globals_def; BAG_UNION_EMPTY] THEN CASE_TAC THEN
  FS[GSYM ALL_MEM; FORALL_PAIR_THM; MEM_toList] THEN ASM_MESON_TAC[]);;

let inv_on_FOLDR = prove
 (`!f:B->C. (!x v. MEM (x:A) xs ==> f (g x v) = f v) ==> f (ITLIST g xs v) = f v`,
  GEN_TAC THEN INDUCT_ON `xs:A list` THEN SIMP[ITLIST; MEM]);;

(* HOL4's proof of set_globals_compile_pat_bindings, also used for the        *)
(* esgc_free and no_Mat versions: f is the invariant                          *)
let FLATPAUX_CPB_TAC f =
  MATCH_MP_TAC compile_pat_bindings_ind THEN RW[compile_pat_bindings_def] THEN
  REPEAT (PAIRARG_TAC THEN FS[]) THEN FS[flat_op_gbag_def] THEN
  IMP_REWRITE_TAC[ISPEC f inv_on_FOLDR] THEN SIMP[FORALL_PAIR_THM; flat_op_gbag_def; no_Mat_def] THEN
  TRY (SIMP[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; MAP_MAP_o; o_DEF; no_Mat_def]);;

let set_globals_compile_pat_bindings = prove
 (`!t i n_bindings exp.
     ALL (\(p:flat_pat,k:num,v_exp). flat_set_globals v_exp = EMPTY_BAG) n_bindings
     ==> flat_set_globals (SND (compile_pat_bindings t i n_bindings exp)) =
         flat_set_globals exp`,
  FLATPAUX_CPB_TAC `flat_set_globals`);;

let set_globals_naive_pattern_match = prove
 (`!t xs. ALL (\v. flat_set_globals (SND v) = EMPTY_BAG) xs
          ==> flat_set_globals (naive_pattern_match t xs) = EMPTY_BAG`,
  MATCH_MP_TAC naive_pattern_match_ind THEN
  REWRITE_TAC[naive_pattern_match_def; flat_op_gbag_def; flat_Bool_def; SmartIf_thm] THEN
  RW[] THEN FS[] THEN FS[EVERY_EL; flat_op_gbag_def; LENGTH_MAPi; EL_MAPi]);;

let set_globals_naive_pattern_matches = prove
 (`flat_set_globals x = EMPTY_BAG
   ==> SUB_BAG (flat_set_globals (naive_pattern_matches t x ps dflt))
               (flat_elist_globals (CONS dflt (MAP SND ps)))`,
  DISCH_TAC THEN INDUCT_ON `ps:(flat_pat#flat_exp)list` THEN
  SIMP[FORALL_PAIR_THM; naive_pattern_matches_def; SUB_BAG_REFL] THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `flat_set_globals (naive_pattern_match t [p1,(x:flat_exp)]) = EMPTY_BAG`
    ASSUME_TAC THENL [IRULE set_globals_naive_pattern_match THEN SIMP[]; ALL_TAC] THEN
  RW[SmartIf_thm] THEN FLATPAUX_BAG_TAC);;

let set_toList_fromList = prove
 (`set_of_list (toList (fromList (xs:A list))) = set_of_list xs`,
  SIMP[EXTENSION; IN_SET_OF_LIST; MEM_toList; lookup_fromList; MEM_EXISTS_EL; COND_CASE_EQ] THEN
  MESON_TAC[]);;

let FLATPAUX_MEM_toList_fromList = REWRITE_RULE[EXTENSION; IN_SET_OF_LIST] set_toList_fromList;;

let set_globals_compile_pats = prove
 (`(~naive ==> flat_elist_globals (CONS dflt (MAP SND ps)) = EMPTY_BAG) /\
   flat_set_globals x = EMPTY_BAG
   ==> SUB_BAG (flat_set_globals (compile_pats cfg naive t N x dflt ps))
               (flat_elist_globals (CONS dflt (MAP SND ps)))`,
  RW[compile_pats_def] THENL
   [IRULE SUB_BAG_TRANS THEN DRULE set_globals_naive_pattern_matches THEN DISCH_THEN (IRULE_AT Any) THEN
    SIMP[MAP_ZIP; LENGTH_MAP] THEN
    QSUFF_TAC "flat_elist_globals (MAP (compile_pat_rhs t N x) ps) = flat_elist_globals (MAP SND ps)" THEN
    SIMP[SUB_BAG_REFL] THEN INDUCT_ON `ps:(flat_pat#flat_exp)list` THEN
    SIMP[FORALL_PAIR_THM; compile_pat_rhs_def; set_globals_compile_pat_bindings];
    IMP_REWRITE_TAC[set_globals_decode_dtree_empty] THEN
    FS[GSYM ALL_MEM; FLATPAUX_MEM_toList_fromList; elist_globals_eq_empty; MEM_MAP;
       LEFT_IMP_EXISTS_THM; FORALL_PAIR_THM] THEN
    SIMP[compile_pat_rhs_def; set_globals_compile_pat_bindings] THEN ASM_MESON_TAC[]]);;

let SUB_BAG_2 = prove
 (`SUB_BAG x (y:A->num) /\ SUB_BAG x' y'
   ==> SUB_BAG (BAG_UNION x x') (BAG_UNION y y')`,
  REWRITE_TAC[SUB_BAG_LEQ; BAG_UNION] THEN MESON_TAC[LE_ADD2]);;

let FLATPAUX_letrec_bag = prove
 (`!fs:(varN#varN#flat_exp)list.
     (!a b c. MEM (a,b,c) fs
              ==> SUB_BAG (flat_set_globals (SND (SND (flat_pattern_compile_exp cfg c))))
                          (flat_set_globals c))
     ==> SUB_BAG (flat_elist_globals (MAP (SND o SND)
                    (MAP (\(n,m,e). (n,m,SND (SND (flat_pattern_compile_exp cfg e)))) fs)))
                 (flat_elist_globals (MAP (SND o SND) fs))`,
  LIST_INDUCT_TAC THEN TRY (QCASES_ON "h" THEN QCASES_ON "y") THEN SIMP[MEM; SUB_BAG_REFL] THEN
  RW[] THEN IRULE SUB_BAG_2 THEN ASM_MESON_TAC[]);;

(* HOL4: ho_match_mp_tac compile_exp_ind, the first steps of the three      *)
(* compile_exp theorems below                                                *)
let FLATPAUX_CE_IND_TAC (thl:thm list) =
  MATCH_MP_TAC flat_pattern_compile_exp_ind THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[flat_pattern_compile_exp_def] THEN REPEAT STRIP_TAC THEN REPEAT PAIRARG_TAC THEN FS[] THEN
  RVEQ_TAC THEN FS[] THEN IMP_RES_TAC LENGTH_compile_exps_IMP THEN
  FS(LENGTH_EQ_NUM_compute :: thl) THEN RVEQ_TAC THEN FS[];;

let compile_exp_set_globals = prove
 (`(!cfg exp N sg exp'. flat_pattern_compile_exp cfg exp = (N,sg,exp')
      ==> SUB_BAG (flat_set_globals exp') (flat_set_globals exp)) /\
   (!cfg exps N sg exps'. flat_pattern_compile_exps cfg exps = (N,sg,exps')
      ==> SUB_BAG (flat_elist_globals exps') (flat_elist_globals exps)) /\
   (!cfg m N sg m'. compile_match cfg m = (N,sg,m')
      ==> SUB_BAG (flat_elist_globals (MAP SND m')) (flat_elist_globals (MAP SND m)))`,
  FLATPAUX_CE_IND_TAC [elist_globals_REVERSE] THEN TRY (FLATPAUX_BAG_TAC THEN NO_TAC) THEN
  TRY (RW[SmartIf_thm] THEN FLATPAUX_BAG_TAC THEN NO_TAC) THEN
  IRULE SUB_BAG_2 THEN SIMP[] THENL
   [IRULE SUB_BAG_TRANS THEN IRULE_AT Any (GEN_ALL set_globals_compile_pats) THEN SIMP[] THEN
    RW[] THEN IMP_RES_TAC (CONJUNCT2 (CONJUNCT2 compile_exp_set_globals_tup)) THEN RFS[SUB_BAG_EMPTY];
    IRULE SUB_BAG_TRANS THEN IRULE_AT Any (GEN_ALL set_globals_compile_pats) THEN SIMP[] THEN
    RW[] THEN IMP_RES_TAC (CONJUNCT2 (CONJUNCT2 compile_exp_set_globals_tup)) THEN RFS[SUB_BAG_EMPTY];
    SIMP[FLATPAUX_letrec_compile] THEN IRULE FLATPAUX_letrec_bag THEN FS[FLATPAUX_FORALL_TRIPLE] THEN
    ASM_REWRITE_TAC[]]);;

let flat_patternProof_FST_SND_EQ_CASE = prove
 (`FST = (\(a:A,b:B). a) /\ SND = (\(a:A,b:B). b)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; FST; SND]);;

let flat_patternProof_compile_decs_elist_globals = prove
 (`!decs. SUB_BAG (flat_elist_globals (MAP (compile_dec cfg) decs))
                  (flat_elist_globals decs)`,
  LIST_INDUCT_TAC THEN SIMP[SUB_BAG_REFL] THEN IRULE SUB_BAG_2 THEN
  SIMP[compile_dec_def; REWRITE_RULE[FLATPAUX_FORALL_TRIPLE] (CONJUNCT1 compile_exp_set_globals)]);;

let esgc_free_decode_pos = prove
 (`!p exp. flat_esgc_free exp ==> flat_esgc_free (decode_pos t exp p)`,
  MATCH_MP_TAC position_INDUCT THEN SIMP[decode_pos_def]);;

let esgc_free_decode_test = prove
 (`flat_esgc_free exp ==> flat_esgc_free (flat_pattern_decode_test t d exp)`,
  QCASES_ON "d" THEN SIMP[flat_pattern_decode_test_def]);;

let esgc_free_decode_guard = prove
 (`flat_esgc_free exp ==> flat_esgc_free (decode_guard t exp gd)`,
  INDUCT_ON `gd:dGuard` THEN SIMP[decode_guard_def; flat_Bool_def] THEN
  RW[SmartIf_thm] THEN SIMP[esgc_free_decode_test; esgc_free_decode_pos]);;

let esgc_free_decode_dtree = prove
 (`flat_esgc_free v_exp /\ flat_esgc_free dflt /\
   ALL (\y. flat_esgc_free y) (toList br_spt)
   ==> flat_esgc_free (decode_dtree t br_spt v_exp dflt dtree)`,
  INDUCT_ON `dtree:dTree` THEN SIMP[decode_dtree_def; SmartIf_thm] THEN REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[esgc_free_decode_guard; flat_esgc_free_def] THEN CASE_TAC THEN FS[GSYM ALL_MEM; MEM_toList] THEN ASM_MESON_TAC[]);;

let esgc_free_compile_pat_bindings = prove
 (`!t i n_bindings exp.
     flat_esgc_free exp /\
     ALL (\(p:flat_pat,k:num,v_exp). flat_esgc_free v_exp) n_bindings
     ==> flat_esgc_free (SND (compile_pat_bindings t i n_bindings exp))`,
  FLATPAUX_CPB_TAC `flat_esgc_free`);;

let esgc_free_naive_pattern_match = prove
 (`!t xs. ALL flat_esgc_free (MAP SND xs)
          ==> flat_esgc_free (naive_pattern_match t xs)`,
  MATCH_MP_TAC naive_pattern_match_ind THEN REWRITE_TAC[naive_pattern_match_def; flat_Bool_def] THEN
  RW[SmartIf_thm] THEN FS[EVERY_EL; LENGTH_MAPi; EL_MAPi; EL_MAP; LENGTH_MAP]);;

let esgc_free_naive_pattern_matches = prove
 (`!t x xs dflt. ALL flat_esgc_free (CONS x (CONS dflt (MAP SND xs)))
                 ==> flat_esgc_free (naive_pattern_matches t x xs dflt)`,
  MATCH_MP_TAC naive_pattern_matches_ind THEN RW[SmartIf_thm; naive_pattern_matches_def] THEN
  SIMP[esgc_free_naive_pattern_match]);;

let esgc_free_compile_pats = prove
 (`flat_esgc_free dflt /\ ALL flat_esgc_free (MAP SND ps)
   ==> flat_esgc_free (compile_pats cfg naive t N (Var_local t' nm) dflt ps)`,
  RW[compile_pats_def] THEN IMP_REWRITE_TAC[esgc_free_decode_dtree; esgc_free_naive_pattern_matches] THEN
  SIMP[MAP_ZIP; LENGTH_MAP] THEN
  FS[GSYM ALL_MEM; FLATPAUX_MEM_toList_fromList; MEM_MAP; LEFT_IMP_EXISTS_THM; FORALL_PAIR_THM] THEN
  RW[compile_pat_rhs_def] THEN IRULE esgc_free_compile_pat_bindings THEN SIMP[] THEN ASM_MESON_TAC[]);;

let flat_patternProof_compile_exp_esgc_free = prove
 (`(!cfg exp N sg exp'. flat_pattern_compile_exp cfg exp = (N,sg,exp') /\
                        flat_esgc_free exp
      ==> flat_esgc_free exp') /\
   (!cfg exps N sg exps'. flat_pattern_compile_exps cfg exps = (N,sg,exps') /\
                          ALL flat_esgc_free exps
      ==> ALL flat_esgc_free exps') /\
   (!cfg m N sg m'. compile_match cfg m = (N,sg,m') /\ ALL (flat_esgc_free o SND) m
      ==> ALL (flat_esgc_free o SND) m')`,
  FLATPAUX_CE_IND_TAC [EVERY_REVERSE] THEN TRY (RW[SmartIf_thm] THEN NO_TAC) THEN
  TRY (IRULE esgc_free_compile_pats THEN FS[ALL_MAP; o_DEF] THEN NO_TAC) THEN
  TRY (IMP_RES_TAC (CONJUNCT1 compile_exp_set_globals) THEN FS[SUB_BAG_EMPTY] THEN NO_TAC) THEN
  SIMP[FLATPAUX_letrec_compile] THEN
  FS[elist_globals_eq_empty; MEM_MAP; LEFT_IMP_EXISTS_THM; FORALL_PAIR_THM] THEN RW[] THEN
  RES_TAC THEN QSPECL_THEN ["cfg"; "p2"] MP_TAC
    (REWRITE_RULE[FLATPAUX_FORALL_TRIPLE] (CONJUNCT1 compile_exp_set_globals)) THEN
  FS[SUB_BAG_EMPTY]);;

let flat_patternProof_compile_decs_esgc_free = prove
 (`!decs. ALL flat_esgc_free decs ==> ALL flat_esgc_free (MAP (compile_dec cfg) decs)`,
  LIST_INDUCT_TAC THEN RW[compile_dec_def] THEN
  IRULE (REWRITE_RULE[IMP_CONJ; FLATPAUX_FORALL_TRIPLE]
           (CONJUNCT1 flat_patternProof_compile_exp_esgc_free)) THEN SIMP[]);;

(* the no_Mat results *)

let naive_pattern_match_no_Mat = prove
 (`!t xs. ALL (no_Mat o SND) xs ==> no_Mat (naive_pattern_match t xs)`,
  MATCH_MP_TAC naive_pattern_match_ind THEN REWRITE_TAC[naive_pattern_match_def; flat_Bool_def; SmartIf_thm] THEN
  RW[] THEN FS[] THEN FS[EVERY_EL; LENGTH_MAPi; EL_MAPi; no_Mat_def]);;

let naive_pattern_matches_no_Mat = prove
 (`!t x xs dflt. ALL no_Mat (CONS x (CONS dflt (MAP SND xs)))
                 ==> no_Mat (naive_pattern_matches t x xs dflt)`,
  MATCH_MP_TAC naive_pattern_matches_ind THEN RW[SmartIf_thm; naive_pattern_matches_def; no_Mat_def] THEN
  SIMP[naive_pattern_match_no_Mat; o_DEF]);;

let compile_pat_bindings_no_Mat = prove
 (`!t i n_bindings exp.
     no_Mat exp /\ ALL (\(p:flat_pat,k:num,v_exp). no_Mat v_exp) n_bindings
     ==> no_Mat (SND (compile_pat_bindings t i n_bindings exp))`,
  FLATPAUX_CPB_TAC `no_Mat`);;

let decode_pos_no_Mat = prove
 (`!p exp. no_Mat exp ==> no_Mat (decode_pos t exp p)`,
  MATCH_MP_TAC position_INDUCT THEN SIMP[decode_pos_def; no_Mat_def]);;

let decode_test_no_Mat = prove
 (`no_Mat exp ==> no_Mat (flat_pattern_decode_test t d exp)`,
  QCASES_ON "d" THEN SIMP[flat_pattern_decode_test_def; no_Mat_def]);;

let decode_guard_no_Mat = prove
 (`no_Mat exp ==> no_Mat (decode_guard t exp gd)`,
  INDUCT_ON `gd:dGuard` THEN SIMP[decode_guard_def; flat_Bool_def; no_Mat_def] THEN
  RW[SmartIf_thm] THEN SIMP[decode_test_no_Mat; decode_pos_no_Mat; no_Mat_def]);;

let decode_dtree_no_Mat = prove
 (`no_Mat v_exp /\ no_Mat dflt /\ ALL no_Mat (toList br_spt)
   ==> no_Mat (decode_dtree t br_spt v_exp dflt dtree)`,
  INDUCT_ON `dtree:dTree` THEN SIMP[decode_dtree_def; SmartIf_thm; no_Mat_def] THEN REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[decode_guard_no_Mat; no_Mat_def] THEN CASE_TAC THEN FS[GSYM ALL_MEM; MEM_toList] THEN
  ASM_MESON_TAC[]);;

let compile_pats_no_Mat = prove
 (`no_Mat dflt /\ no_Mat x /\ ALL no_Mat (MAP SND ps)
   ==> no_Mat (compile_pats cfg naive t N x dflt ps)`,
  RW[compile_pats_def] THEN IMP_REWRITE_TAC[naive_pattern_matches_no_Mat; decode_dtree_no_Mat] THEN
  SIMP[MAP_ZIP; LENGTH_MAP] THEN
  FS[GSYM ALL_MEM; FLATPAUX_MEM_toList_fromList; MEM_MAP; LEFT_IMP_EXISTS_THM; FORALL_PAIR_THM] THEN
  RW[compile_pat_rhs_def] THEN IRULE compile_pat_bindings_no_Mat THEN SIMP[] THEN ASM_MESON_TAC[]);;

let compile_exp_no_Mat = prove
 (`(!cfg exp N sg exp'. flat_pattern_compile_exp cfg exp = (N,sg,exp')
      ==> no_Mat exp') /\
   (!cfg exps N sg exps'. flat_pattern_compile_exps cfg exps = (N,sg,exps')
      ==> ALL no_Mat exps') /\
   (!cfg pats N sg pats'. compile_match cfg pats = (N,sg,pats')
      ==> ALL no_Mat (MAP SND pats'))`,
  FLATPAUX_CE_IND_TAC [] THEN TRY (RW[SmartIf_thm] THEN FS[no_Mat_def] THEN NO_TAC) THEN
  TRY (IRULE compile_pats_no_Mat THEN SIMP[no_Mat_def] THEN NO_TAC) THEN
  SIMP[FLATPAUX_letrec_compile; GSYM ALL_MEM; MEM_MAP; EXISTS_PAIR_THM; LEFT_IMP_EXISTS_THM] THEN
  RW[] THEN RES_TAC THEN FIRST_X_ASSUM IRULE THEN ASM_MESON_TAC[]);;

let compile_decs_no_Mat = prove
 (`!decs. no_Mat_decs (MAP (compile_dec cfg) decs)`,
  LIST_INDUCT_TAC THEN
  SIMP[no_Mat_decs_def; compile_dec_def; REWRITE_RULE[FLATPAUX_FORALL_TRIPLE] (CONJUNCT1 compile_exp_no_Mat)]);;
