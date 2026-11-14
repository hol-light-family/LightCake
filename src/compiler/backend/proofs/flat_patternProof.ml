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
needs "compiler/backend/il1aux_mutual.ml";;
needs "compiler/backend/flat_pattern.ml";;
needs "compiler/backend/semantics/flatSem.ml";;
needs "compiler/backend/semantics/flatProps.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "basis/pure/mlstring.ml";;

type_invention_error := true;;

(* simple properties *)

let op_sets_globals_gbag = prove
 (`!op. op_sets_globals op <=> ~(flat_op_gbag op = EMPTY_BAG)`,
  MATCH_MP_TAC flat_op_INDUCT THEN
  REWRITE_TAC[op_sets_globals_def; flat_op_gbag_def] THEN
  REWRITE_TAC[BAG_INSERT_NOT_EMPTY]);;

let FLATPAUX_TRIPLE_EXISTS = prove
 (`!t:A#B#C. ?a b c. t = (a,b,c)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* the sets-globals flag of the functions of a Letrec *)

let FLATPAUX_letrec_sg = prove
 (CASE_TERM
  `!cfg (fs:(varN#varN#flat_exp)list).
     (!a b c. MEM (a,b,c) fs
              ==> (FST (SND (flat_pattern_compile_exp cfg c)) <=>
                   ~(flat_set_globals c = EMPTY_BAG)))
     ==> (EX (\(a,b,(j,sg,e)). sg)
            (MAP (\fn. match fn with
                         (a,b,c) -> (a, b, flat_pattern_compile_exp cfg c)) fs) <=>
          ~(flat_elist_globals (MAP (SND o SND) fs) = EMPTY_BAG))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; EX; flat_set_globals_def] THEN
  SPEC_TAC(`h:varN#varN#flat_exp`,`h:varN#varN#flat_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; MEM; PAIR_EQ; pair_CASE; o_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`a:varN`; `b:varN`; `c:flat_exp`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:varN`; `b:varN`; `c:flat_exp`]) THEN
  REWRITE_TAC[] THEN
  X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `sg:bool` (X_CHOOSE_THEN `e:flat_exp` SUBST1_TAC))
    (ISPEC `flat_pattern_compile_exp cfg c` FLATPAUX_TRIPLE_EXISTS) THEN
  REWRITE_TAC[FST; SND] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[BAG_UNION_EMPTY; DE_MORGAN_THM] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[]);;

let compile_exp_set_globals_FST_SND = prove
 (`(!cfg x. FST (SND (flat_pattern_compile_exp cfg x)) <=>
            ~(flat_set_globals x = EMPTY_BAG)) /\
   (!cfg xs. FST (SND (flat_pattern_compile_exps cfg xs)) <=>
             ~(flat_elist_globals xs = EMPTY_BAG)) /\
   (!cfg ps. FST (SND (compile_match cfg ps)) <=>
             ~(flat_elist_globals (MAP SND ps) = EMPTY_BAG))`,
  MATCH_MP_TAC flat_pattern_compile_exp_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  REWRITE_TAC[flat_pattern_compile_exp_def] THEN
  REPEAT IL1AUX_PAIRARG_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RES_TAC THEN
  GVS[flat_set_globals_def; elist_globals_REVERSE; op_sets_globals_gbag;
      BAG_UNION_EMPTY; DE_MORGAN_THM; MAP] THEN
  TRY(FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FLATPAUX_letrec_sg th])) THEN
  REWRITE_TAC[DISJ_ACI]);;

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
  MATCH_MP_TAC sum_string_ords_ind THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `s:mlstring`] THEN
  STRUCT_CASES_TAC(SPEC `s:mlstring` (cases "mlstring")) THEN
  REWRITE_TAC[strlen_def; explode_thm] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[sum_string_ords_def] THEN
  REWRITE_TAC[strlen_def; strsub_def; explode_thm] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[DROP_EL_CONS; MAP; SUM];
    ASM_SIMP_TAC[DROP_LENGTH_TOO_LONG; ARITH_RULE `~(i < n) ==> n <= i`; MAP; SUM]]);;

let dec_enc_aux = prove
 (`!i xs. dec_name_to_num (implode (enc_num_to_name_aux i xs)) =
          i + SUM (MAP (\c. ORD c - 35) xs)`,
  MATCH_MP_TAC (cake_ind "enc_num_to_name_aux") THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `xs:char list`] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[enc_num_to_name_aux_def] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[dec_name_to_num_def; strlen_def; strsub_def; LENGTH;
                sum_string_ords_eq; explode_thm; EL_CONS; DROP_DEF] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `~(SUC (SUC (SUC n)) < 2)`; MAP; SUM] THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
    SUBGOAL_THEN `ORD (CHR (i + 35)) = i + 35` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM ORD_CHR] THEN ASM_ARITH_TAC; ARITH_TAC];
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MAP; SUM] THEN
    SUBGOAL_THEN `ORD (CHR 125) = 125` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM ORD_CHR] THEN ARITH_TAC; ASM_ARITH_TAC]]);;

let dec_enc = prove
 (`!i. dec_name_to_num (enc_num_to_name i) = i`,
  REWRITE_TAC[enc_num_to_name_def; dec_enc_aux; MAP; SUM; ADD_CLAUSES]);;

let enc_num_to_name_inj = prove
 (`!i j. enc_num_to_name i = enc_num_to_name j <=> i = j`,
  MESON_TAC[dec_enc]);;

(* lists and lookups *)

let LIST_REL_ALOOKUP_OPTREL = prove
 (`!xs ys. ALL2 (R:A#B->A#C->bool) xs ys /\
     (!x y. R x y /\ MEM x xs /\ MEM y ys /\ (v = FST x \/ v = FST y)
            ==> FST x = FST y /\ (R2:B->C->bool) (SND x) (SND y))
     ==> OPTREL R2 (ALOOKUP xs v) (ALOOKUP ys v)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; ALOOKUP_DEF; OPTREL_DEF; MEM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(v = FST (h:A#B) \/ v = FST (h':A#C))
                ==> FST h = FST h' /\ (R2:B->C->bool) (SND h) (SND h')`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `FST (h:A#B) = v` THEN ASM_CASES_TAC `FST (h':A#C) = v` THEN
  ASM_REWRITE_TAC[option_INJ; option_DISTINCT] THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM OPTREL_DEF] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `t':(A#C)list`) THEN ASM_MESON_TAC[]);;

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
  SUBGOAL_THEN `!l:B list. ALL2 (R:A->B->bool) [] l <=> l = []` ASSUME_TAC THENL
   [GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `l:B list` list_CASES) THEN
    REWRITE_TAC[ALL2; NOT_CONS_NIL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!(h:A) t l:B list. ALL2 (R:A->B->bool) (CONS h t) l <=>
                  ?y rest. l = CONS y rest /\ R h y /\ ALL2 R t rest`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `l:B list` list_CASES) THEN
    REWRITE_TAC[ALL2; NOT_CONS_NIL; CONS_11] THEN MESON_TAC[];
    ALL_TAC] THEN
  LIST_INDUCT_TAC THENL
   [ASM_REWRITE_TAC[FILTER; MEM] THEN GEN_TAC THEN
    REWRITE_TAC[FILTER_EQ_NIL; GSYM ALL_MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `ys:B list` THEN REWRITE_TAC[MEM] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(P1:A->bool) h` THENL
   [ALL_TAC;
    SUBGOAL_THEN `~(P3:A->bool) h` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `ALL2 (R:A->B->bool) (FILTER P1 (CONS h t)) (FILTER P2 ys)` THEN
    ASM_REWRITE_TAC[FILTER] THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]] THEN
  UNDISCH_TAC `ALL2 (R:A->B->bool) (FILTER P1 (CONS h t)) (FILTER P2 ys)` THEN
  ASM_REWRITE_TAC[FILTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:B` (X_CHOOSE_THEN `rest:B list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FILTER_EQ_CONS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:B list` (X_CHOOSE_THEN `l2:B list` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `FILTER (P4:B->bool) l1 = []` ASSUME_TAC THENL
   [UNDISCH_TAC `FILTER (P2:B->bool) l1 = []` THEN
    REWRITE_TAC[FILTER_EQ_NIL; GSYM ALL_MEM] THEN
    ASM_MESON_TAC[MEM_APPEND; MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P3:A->bool) h <=> (P4:B->bool) y` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM_APPEND; MEM]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l2:B list`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MEM_APPEND; MEM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FILTER_APPEND; FILTER; APPEND] THEN
  COND_CASES_TAC THEN REWRITE_TAC[APPEND; ALL2] THEN ASM_REWRITE_TAC[]);;

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
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  REWRITE_TAC[FILTER; ALOOKUP_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `FILTER (P:A#B->bool) t`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`k:A`; `w:B`] THEN
  ASM_CASES_TAC `k:A = x` THEN ASM_REWRITE_TAC[] THEN
  TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[ALOOKUP_DEF; FST; SND]);;

let ALOOKUP_FILTER_EQ = prove
 (`!xs. (!z. P ((x:A),(z:B))) ==> ALOOKUP (FILTER P xs) x = ALOOKUP xs x`,
  MESON_TAC[FILTER_EQ_ALOOKUP_EQ]);;

let MEM_enumerate_EL = prove
 (`!xs i (x:num#A). MEM x (enumerate i xs) <=>
                    ?j. j < LENGTH xs /\ x = (i + j,EL j xs)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[enumerate_def; MEM; LENGTH; ARITH_RULE `~(j < 0)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[EL; HD; ADD_CLAUSES; LT_0];
      EXISTS_TAC `SUC j` THEN ASM_REWRITE_TAC[EL; TL; LT_SUC; PAIR_EQ] THEN ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    POP_ASSUM SUBST1_TAC THEN POP_ASSUM MP_TAC THEN
    STRUCT_CASES_TAC(SPEC `j:num` num_CASES) THEN
    REWRITE_TAC[EL; HD; TL; ADD_CLAUSES; LT_SUC] THEN DISCH_TAC THEN DISJ2_TAC THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[PAIR_EQ] THEN ARITH_TAC]);;

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
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[flat_pmatch_def; LENGTH; distinctness "match_result"; SUC_INJ] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[case_eq "match_result"] THEN
  REWRITE_TAC[distinctness "match_result"; injectivity "match_result"] THEN
  ASM_MESON_TAC[]);;

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
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP pmatch_list_Match_IMP_LENGTH) THEN
    REWRITE_TAC[LENGTH_APPEND] THEN
    DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [LENGTH_EQ_SUM] o SYM) THEN
    DISCH_THEN(X_CHOOSE_THEN `l1:flat_v list` (X_CHOOSE_THEN `l2:flat_v list`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `flat_pmatch_list (s:(C,FFI)flat_state) (APPEND xs ys)
                   (APPEND l1 l2) pre_bindings = Match bindings` THEN
    MP_TAC(ISPECL [`xs:flat_pat list`; `l1:flat_v list`; `ys:flat_pat list`;
                   `l2:flat_v list`; `s:(C,FFI)flat_state`; `pre_bindings:(varN#flat_v)list`]
                  flat_pmatch_list_append) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[case_eq "match_result"; distinctness "match_result"] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`l1:flat_v list`; `l2:flat_v list`] THEN
    ASM_MESON_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASSUM_LIST(fun ths -> MAP_EVERY (ASSUME_TAC o MATCH_MP pmatch_list_Match_IMP_LENGTH)
      (filter (can (MATCH_MP pmatch_list_Match_IMP_LENGTH)) ths)) THEN
    ASM_SIMP_TAC[flat_pmatch_list_append] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]]);;

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
  REWRITE_TAC[ALOOKUP_rel_def; ALOOKUP_DEF] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x':A`) THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `x:A = x'` THEN ASM_MESON_TAC[]);;

let ALOOKUP_rel_APPEND_L_false = prove
 (`ALL ((~) o (P:A->bool) o FST) (xs:(A#B)list)
   ==> (ALOOKUP_rel P (R:B->C->bool) (APPEND xs ys) zs <=> ALOOKUP_rel P R ys zs)`,
  REWRITE_TAC[ALOOKUP_rel_def; ALOOKUP_APPEND; GSYM ALL_MEM; o_THM] THEN
  STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ALOOKUP (xs:(A#B)list) x = NONE` (fun th -> REWRITE_TAC[th; option_CASE]) THEN
  REWRITE_TAC[ALOOKUP_NONE; MEM_MAP] THEN ASM_MESON_TAC[]);;

let ALOOKUP_rel_refl = prove
 (`(!x y. P x /\ MEM (x,y) xs ==> (R:B->B->bool) y y)
   ==> ALOOKUP_rel (P:A->bool) R xs xs`,
  REWRITE_TAC[ALOOKUP_rel_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `ALOOKUP (xs:(A#B)list) x` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[OPTREL_DEF; option_INJ; option_DISTINCT] THEN
  ASM_MESON_TAC[ALOOKUP_MEM]);;

let ALOOKUP_rel_cons = prove
 (`(P x ==> (R:B->C->bool) y z) /\ ALOOKUP_rel (P:A->bool) R ys zs
   ==> ALOOKUP_rel P R (CONS (x,y) ys) (CONS (x,z) zs)`,
  REWRITE_TAC[ALOOKUP_rel_def; ALOOKUP_DEF; FST; SND] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[OPTREL_DEF; option_INJ] THEN
  ASM_MESON_TAC[OPTREL_DEF]);;

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
  REWRITE_TAC[ALOOKUP_rel_def; ALOOKUP_APPEND] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:A`)) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[OPTREL_DEF] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[option_CASE; option_INJ; option_DISTINCT] THEN
  DISCH_THEN(K ALL_TAC) THEN ASM_MESON_TAC[]);;

let ALOOKUP_rel_EQ_ALOOKUP = prove
 (`ALOOKUP_rel (P:A->bool) (=) (xs:(A#B)list) ys /\ P x
   ==> ALOOKUP xs x = ALOOKUP ys x`,
  REWRITE_TAC[ALOOKUP_rel_def; OPTREL_eq] THEN MESON_TAC[]);;

let ALOOKUP_rel_eq_fst = prove
 (`!xs ys. ALL2 (\x y. FST x = FST y /\ ((P:A->bool) (FST x) ==> (R:B->C->bool) (SND x) (SND y)))
                xs ys
           ==> ALOOKUP_rel P R xs ys`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; ALOOKUP_rel_empty] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN SPEC_TAC(`h':A#C`,`h':A#C`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC ALOOKUP_rel_cons THEN
  ASM_SIMP_TAC[]);;

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
  GEN_TAC THEN LIST_INDUCT_TAC THENL
  [REWRITE_TAC[ITLIST; REVERSE; MAP; APPEND] THEN REPEAT STRIP_TAC THEN
   AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[flat_environment_component_equality;
               flat_environment_INFO.ri_accfupds; K_THM];
   ALL_TAC] THEN
  REWRITE_TAC[MEM; ITLIST; set_of_list; IMAGE_CLAUSES; INSERT_SUBSET;
              DISJ_IMP_THM; FORALL_AND_THM; o_THM; FORALL_UNWIND_THM2] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "ih")] THEN
  X_GEN_TAC `env2:(flat_v)flat_environment` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_exists o concl) o
    REWRITE_RULE[IS_SOME_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_TAC `nm:mlstring`) THEN
  SUBGOAL_THEN `(nm:mlstring) IN new_names` ASSUME_TAC THENL
  [UNDISCH_TAC `THE ((f:A->mlstring option) h') IN new_names` THEN
   ASM_REWRITE_TAC[THE_DEF];
   ALL_TAC] THEN
  ASM_SIMP_TAC[flat_evaluate_def; pair_CASE; case_def "result"; HD] THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC
    `flat_environment_v_fupd (opt_bind (SOME (nm:mlstring)) ((h:A->flat_v) h'))
       (env2:(flat_v)flat_environment)`) THEN
  REWRITE_TAC[flat_environment_INFO.ri_accfupds; opt_bind_def; option_CASE] THEN
  ASM_SIMP_TAC[ALOOKUP_rel_cons_false] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[flat_environment_INFO.ri_fupdfupds;
              flat_environment_component_equality;
              flat_environment_INFO.ri_accfupds; K_THM; o_THM; opt_bind_def;
              option_CASE] THEN
  ASM_REWRITE_TAC[REVERSE; MAP_APPEND; MAP; GSYM APPEND_ASSOC; APPEND; THE_DEF]);;

let EVERY_MAPi_simple = prove
 (`(!i j x. (P:B->bool) ((f:num->A->B) i x) = P (f j x))
   ==> (ALL P (MAPi f xs) <=> ALL P (MAP (f 0) xs))`,
  SIMP_TAC[EVERY_EL; EL_MAP; EL_MAPi; LENGTH_MAP; LENGTH_MAPi] THEN
  MESON_TAC[]);;

(* compile_pat_bindings_simulation: local helpers (FLATPAUX_), one tactic  *)
(* per clause of compile_pat_bindings                                       *)

let FLATPAUX_LIST_REL_CONS1 = prove
 (`ALL2 (R:A->B->bool) (CONS h t) xs <=>
   ?hv tvs. xs = CONS hv tvs /\ R h hv /\ ALL2 R t tvs`,
  REWRITE_TAC[LIST_REL_CONS1]);;

let FLATPAUX_SUBST_VAR_TAC s =
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    let l = lhs(concl th) in is_var l && fst(dest_var l) = s));;

let FLATPAUX_UNDISCH_PAT pat =
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] pat) (concl th) then MP_TAC th else failwith "pat");;

let FLATPAUX_PAIR_EQ_SUBST_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_conj c && is_eq (lhand c) && is_var (rhs (lhand c)) &&
       is_eq (rand c) && is_var (rhs (rand c)) &&
       type_of (rhs (lhand c)) = `:num_set`
    then CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) th else failwith "pair eq");;

let FLATPAUX_cpbs_intro_tac outer =
  MAP_EVERY X_GEN_TAC outer THEN DISCH_THEN(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`exp2:flat_exp`; `spt:num_set`; `s:(C,FFI)flat_state`;
    `vs:flat_v list`; `pre_bindings:(varN#flat_v)list`;
    `bindings:(varN#flat_v)list`; `env:(flat_v)flat_environment`;
    `s2:(C,FFI)flat_state`; `res:(flat_v list,flat_v)result`] THEN
  REWRITE_TAC[MAP; FLATPAUX_LIST_REL_CONS1; ALL] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  STRIP_TAC THEN FLATPAUX_SUBST_VAR_TAC "vs" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_pmatch_def; flat_pat_bindings_def; ALL;
                              APPEND; ALL_APPEND]) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[compile_pat_bindings_def]);;

let FLATPAUX_cpbs_rel_mono = prove
 (`!(s:(C,FFI)flat_state) (spt:num_set) (spt':num_set) ev ev' i i'
    (m:(flat_pat#num#flat_exp)list) (vs:flat_v list).
     domain spt' SUBSET domain spt /\
     (!env2:(flat_v)flat_environment.
        ALOOKUP_rel ((\k. k > j /\ k < i') o dec_name_to_num) (=)
          (flat_environment_v env2) ev'
        ==> ALOOKUP_rel ((\k. k > j /\ k < i) o dec_name_to_num) (=)
              (flat_environment_v env2) ev) /\
     ALL2 (\(p0,k,v_exp) v.
             !env2. k IN domain spt /\
                    ALOOKUP_rel ((\k. k > j /\ k < i) o dec_name_to_num) (=)
                      (flat_environment_v env2) ev
                    ==> pure_eval_to s env2 v_exp v) m vs
     ==> ALL2 (\(p0,k,v_exp) v.
             !env2. k IN domain spt' /\
                    ALOOKUP_rel ((\k. k > j /\ k < i') o dec_name_to_num) (=)
                      (flat_environment_v env2) ev'
                    ==> pure_eval_to s env2 v_exp v) m vs`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC MONO_ALL2 THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[SUBSET]);;

let FLATPAUX_cpbs_ih_tac exp2 spt vs pre env =
  REMOVE_THEN "ih" (MP_TAC o SPECL [exp2; spt;
    `s:(C,FFI)flat_state`; vs; pre; `bindings:(varN#flat_v)list`; env;
    `s2:(C,FFI)flat_state`; `res:(flat_v list,flat_v)result`]);;

let FLATPAUX_cpbs_pvar_tac =
  FLATPAUX_cpbs_intro_tac [`t:tra`; `i:num`; `nm:mlstring`; `k:num`;
    `x:flat_exp`; `m:(flat_pat#num#flat_exp)list`; `exp:flat_exp`] THEN
  IL1AUX_PAIRARG_TAC THEN FLATPAUX_PAIR_EQ_SUBST_TAC THEN
  SUBGOAL_THEN `flat_evaluate env (s:(C,FFI)flat_state) [x] = (s,Rval [hv])`
    ASSUME_TAC THENL
  [REWRITE_TAC[GSYM pure_eval_to_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   REWRITE_TAC[domain_insert; IN_INSERT] THEN MATCH_MP_TAC ALOOKUP_rel_refl THEN
   REWRITE_TAC[];
   ALL_TAC] THEN
  FLATPAUX_UNDISCH_PAT `flat_evaluate (env:(flat_v)flat_environment)
     (s:(C,FFI)flat_state) [flat_Let a b c d] = r` THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[HD] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(((\k. k > j /\ k < i) o dec_name_to_num) (nm:mlstring))`
    ASSUME_TAC THENL [REWRITE_TAC[o_THM] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FLATPAUX_cpbs_ih_tac `exp2':flat_exp` `spt':num_set` `tvs:flat_v list`
    `CONS (nm:mlstring,hv:flat_v) pre_bindings`
    `flat_environment_v_fupd (opt_bind (SOME (nm:mlstring)) (hv:flat_v)) env` THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[ALL; o_THM; APPEND; flat_environment_INFO.ri_accfupds;
                  opt_bind_def] THEN
  CASE_REWRITE_TAC[] THEN CONJ_TAC THENL
  [MATCH_MP_TAC FLATPAUX_cpbs_rel_mono THEN
   MAP_EVERY EXISTS_TAC [`insert k one spt'`;
     `flat_environment_v (env:(flat_v)flat_environment)`; `i:num`] THEN
   ASM_REWRITE_TAC[flat_environment_INFO.ri_accfupds; opt_bind_def;
                   domain_insert] THEN
   CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[MATCH_MP (CONJUNCT2 ALOOKUP_rel_cons_false)
     (ASSUME `~(((\k. k > j /\ k < i) o dec_name_to_num) (nm:mlstring))`)] THEN
   SET_TAC[];
   MATCH_MP_TAC ALOOKUP_rel_cons THEN ASM_REWRITE_TAC[]];;

let FLATPAUX_cpbs_nil_tac =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[compile_pat_bindings_def; MAP; PAIR_EQ; LIST_REL_NIL] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl) o
    check (fun th -> type_of (rhs (concl th)) = `:flat_exp`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_pmatch_def; injectivity "match_result"]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o rhs o concl) o
    check (fun th -> type_of (rhs (concl th)) = `:(varN#flat_v)list`)) THEN
  EXISTS_TAC `env:(flat_v)flat_environment` THEN ASM_REWRITE_TAC[];;
let FLATPAUX_cpbs_pany_tac =
  FLATPAUX_cpbs_intro_tac [`t:tra`; `i:num`; `x:num`; `x':flat_exp`;
    `m:(flat_pat#num#flat_exp)list`; `exp:flat_exp`] THEN
  FLATPAUX_cpbs_ih_tac `exp2:flat_exp` `spt:num_set`
    `tvs:flat_v list` `pre_bindings:(varN#flat_v)list`
    `env:(flat_v)flat_environment` THEN
  ASM_REWRITE_TAC[];;


let FLATPAUX_pmatch_Plit_Match = prove
 (`!(s:(C,FFI)flat_state) l v bs a.
     flat_pmatch s (flat_Plit l) v bs = Match a <=> v = flat_Litv l /\ a = bs`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `v:flat_v` (CONJUNCT1 (cases "flat_v"))) THEN
  REWRITE_TAC[flat_pmatch_def; distinctness "match_result";
              distinctness "flat_v"; injectivity "flat_v"] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[distinctness "match_result"; injectivity "match_result"] THEN
  ASM_MESON_TAC[]);;

let FLATPAUX_cpbs_plit_tac =
  FLATPAUX_cpbs_intro_tac [`t:tra`; `i:num`; `l:lit`; `k:num`;
    `x:flat_exp`; `m:(flat_pat#num#flat_exp)list`; `exp:flat_exp`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_eq "match_result";
    distinctness "match_result"; FLATPAUX_pmatch_Plit_Match]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `b1:(varN#flat_v)list` STRIP_ASSUME_TAC o
    check (is_exists o concl)) THEN
  FLATPAUX_SUBST_VAR_TAC "b1" THEN
  FLATPAUX_cpbs_ih_tac `exp2:flat_exp` `spt:num_set`
    `tvs:flat_v list` `pre_bindings:(varN#flat_v)list`
    `env:(flat_v)flat_environment` THEN
  ASM_REWRITE_TAC[];;

let FLATPAUX_eval_El = prove
 (`!(env:(flat_v)flat_environment) (s:(C,FFI)flat_state) x t j w r.
     flat_evaluate env s [x] = (s,Rval [w]) /\
     flat_do_app s (flat_El j) [w] = SOME (s,Rval r)
     ==> flat_evaluate env s [flat_App t (flat_El j) [x]] = (s,Rval [r])`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[flat_evaluate_def; REVERSE; APPEND] THEN
  CASE_REWRITE_TAC[distinctness "flat_op"] THEN
  ASM_REWRITE_TAC[REVERSE; APPEND] THEN
  CASE_REWRITE_TAC[list_result_def]);;

let FLATPAUX_do_app_El_Conv = prove
 (`!(s:(C,FFI)flat_state) j stmp vs.
     j < LENGTH vs
     ==> flat_do_app s (flat_El j) [flat_Conv stmp vs] = SOME (s,Rval (EL j vs))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[flat_do_app_def] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let FLATPAUX_do_app_El_Loc = prove
 (`!(s:(C,FFI)flat_state) b lnum v.
     store_lookup lnum (flat_state_refs s) = SOME (Refv v)
     ==> flat_do_app s (flat_El 0) [flat_Loc b lnum] = SOME (s,Rval v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[flat_do_app_def] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let FLATPAUX_env_opt_bind = prove
 (`!n (v:flat_v) (env:(flat_v)flat_environment).
     flat_environment_v_fupd (opt_bind (SOME n) v) env =
     flat_environment_v_fupd (K (CONS (n,v) (flat_environment_v env))) env`,
  REWRITE_TAC[flat_environment_component_equality;
              flat_environment_INFO.ri_accfupds; opt_bind_def; K_THM] THEN
  CASE_REWRITE_TAC[]);;

let FLATPAUX_env_fupd_K = prove
 (`!f l (env:(flat_v)flat_environment).
     flat_environment_v_fupd f (flat_environment_v_fupd (K l) env) =
     flat_environment_v_fupd (K (f l)) env`,
  REWRITE_TAC[flat_environment_component_equality;
              flat_environment_INFO.ri_accfupds; K_THM]);;

let FLATPAUX_env_simps =
  [FLATPAUX_env_opt_bind; FLATPAUX_env_fupd_K; flat_environment_INFO.ri_accfupds;
   K_THM; opt_bind_def];;

let FLATPAUX_cpbs_every_mono = prove
 (`!(m:(flat_pat#num#flat_exp)list) i i'.
     i <= i' /\
     ALL (\(p,k,x0). ALL (\nm. dec_name_to_num nm < j) (flat_pat_bindings p) /\
                     j < k /\ k < i) m
     ==> ALL (\(p,k,x0). ALL (\nm. dec_name_to_num nm < j) (flat_pat_bindings p) /\
                         j < k /\ k < i') m`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
let FLATPAUX_ALOOKUP_rel_drop = prove
 (`!(P1:A->bool) P2 (R:B->C->bool) xs new ys.
     ALOOKUP_rel P2 R xs (APPEND new ys) /\ (!x. P1 x ==> P2 x) /\
     (!x. P1 x ==> ~MEM x (MAP FST new))
     ==> ALOOKUP_rel P1 R xs ys`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALOOKUP_rel_def; ALOOKUP_APPEND] THEN
  DISCH_THEN(fun th -> X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC (SPEC `x:A` (CONJUNCT1 th)) THEN
    MP_TAC (SPEC `x:A` (CONJUNCT1 (CONJUNCT2 th))) THEN
    MP_TAC (SPEC `x:A` (CONJUNCT2 (CONJUNCT2 th)))) THEN
  ASM_REWRITE_TAC[GSYM ALOOKUP_NONE] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[option_CASE]);;

let FLATPAUX_cpbs_hd_tac =
  SUBGOAL_THEN `flat_evaluate env (s:(C,FFI)flat_state) [x] = (s,Rval [hv])`
    ASSUME_TAC THENL
  [REWRITE_TAC[GSYM pure_eval_to_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   REWRITE_TAC[domain_insert; IN_INSERT] THEN MATCH_MP_TAC ALOOKUP_rel_refl THEN
   REWRITE_TAC[];
   ALL_TAC];;

let FLATPAUX_cpbs_eval_tac =
  FLATPAUX_UNDISCH_PAT `flat_evaluate (env:(flat_v)flat_environment)
     (s:(C,FFI)flat_state) [flat_Let a b c d] = r` THEN
  REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  REPEAT(CHANGED_TAC(CASE_REWRITE_TAC[HD] THEN
    REWRITE_TAC(ALOOKUP_THM :: FLATPAUX_env_simps))) THEN DISCH_TAC;;

let FLATPAUX_win1 = prove
 (`!i j. j < i
         ==> ((\k. k > j /\ k < i + 2) o dec_name_to_num) (enc_num_to_name (i + 1))`,
  REWRITE_TAC[o_THM; dec_enc] THEN ARITH_TAC);;

(* the head binding of the recursive call is a fresh variable *)
let FLATPAUX_cpbs_fresh_hd_tac =
  X_GEN_TAC `env2:(flat_v)flat_environment` THEN STRIP_TAC THEN
  REWRITE_TAC[pure_eval_to_def; flat_evaluate_def] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP ALOOKUP_rel_EQ_ALOOKUP
    (CONJ th (MATCH_MP FLATPAUX_win1 (ASSUME `j < i`))))) THEN
  REWRITE_TAC[ALOOKUP_THM] THEN DISCH_THEN SUBST1_TAC THEN
  CASE_REWRITE_TAC[];;

let FLATPAUX_win2 = prove
 (`!i j. j < i
         ==> ~(((\k. k < j) o dec_name_to_num) (enc_num_to_name (i + 1)))`,
  REWRITE_TAC[o_THM; dec_enc] THEN ARITH_TAC);;

(* the tail bindings: drop the new names from the environment *)
let FLATPAUX_cpbs_tail_tac spt0 news =
  MATCH_MP_TAC FLATPAUX_cpbs_rel_mono THEN
  MAP_EVERY EXISTS_TAC [spt0;
    `flat_environment_v (env:(flat_v)flat_environment)`; `i:num`] THEN
  ASM_REWRITE_TAC[domain_insert; SUBSET; IN_INSERT] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `env2:(flat_v)flat_environment` THEN DISCH_TAC THEN
  MATCH_MP_TAC FLATPAUX_ALOOKUP_rel_drop THEN
  EXISTS_TAC `(\k. k > j /\ k < i + 2) o dec_name_to_num` THEN
  EXISTS_TAC news THEN ASM_REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[o_THM; MAP; MEM; FST] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[DE_MORGAN_THM] THEN
  REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dec_enc]) THEN ASM_ARITH_TAC;;

let FLATPAUX_cpbs_pas_tac =
  FLATPAUX_cpbs_intro_tac [`t:tra`; `i:num`; `p:flat_pat`; `v:mlstring`;
    `k:num`; `x:flat_exp`; `m:(flat_pat#num#flat_exp)list`; `exp:flat_exp`] THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  IL1AUX_PAIRARG_TAC THEN FLATPAUX_PAIR_EQ_SUBST_TAC THEN
  FLATPAUX_cpbs_hd_tac THEN FLATPAUX_cpbs_eval_tac THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_eq "match_result";
                              distinctness "match_result"]) THEN
  FLATPAUX_cpbs_ih_tac `exp2':flat_exp` `spt':num_set`
    `CONS (hv:flat_v) tvs` `CONS (v:mlstring,hv:flat_v) pre_bindings`
    `flat_environment_v_fupd
       (K (CONS (enc_num_to_name (i + 1),hv:flat_v)
             (CONS (v,hv) (flat_environment_v env)))) env` THEN
  REWRITE_TAC[MAP; flat_pmatch_def; case_eq "match_result";
              distinctness "match_result"] THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[ALL2; ALL; o_THM; APPEND; flat_environment_INFO.ri_accfupds;
                  K_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[MATCH_MP (CONJUNCT1 ALOOKUP_rel_cons_false)
                (MATCH_MP FLATPAUX_win2 (ASSUME `j < i`))] THEN
  REPEAT CONJ_TAC THEN
  FIRST [ASM_ARITH_TAC;
         FLATPAUX_cpbs_fresh_hd_tac THEN NO_TAC;
         FLATPAUX_cpbs_tail_tac `insert k one spt'`
           `[enc_num_to_name (i + 1),hv:flat_v; v,hv]` THEN NO_TAC;
         MATCH_MP_TAC ALOOKUP_rel_cons THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         MATCH_MP_TAC FLATPAUX_cpbs_every_mono THEN EXISTS_TAC `i:num` THEN
         ASM_REWRITE_TAC[] THEN ARITH_TAC];;

let FLATPAUX_pmatch_Pref_Match = prove
 (`!(s:(C,FFI)flat_state) p v bs a.
     flat_pmatch s (flat_Pref p) v bs = Match a <=>
     ?b lnum rv. v = flat_Loc b lnum /\
                 store_lookup lnum (flat_state_refs s) = SOME (Refv rv) /\
                 flat_pmatch s p rv bs = Match a`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `v:flat_v` (CONJUNCT1 (cases "flat_v"))) THEN
  REWRITE_TAC[flat_pmatch_def; distinctness "match_result";
              distinctness "flat_v"; injectivity "flat_v"] THEN
  REWRITE_TAC[case_eq "option"; case_eq "store_v"; distinctness "match_result";
              distinctness "option"; injectivity "option"] THEN
  MESON_TAC[]);;

let FLATPAUX_cpbs_pref_tac =
  FLATPAUX_cpbs_intro_tac [`t:tra`; `i:num`; `p:flat_pat`;
    `k:num`; `x:flat_exp`; `m:(flat_pat#num#flat_exp)list`; `exp:flat_exp`] THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  IL1AUX_PAIRARG_TAC THEN FLATPAUX_PAIR_EQ_SUBST_TAC THEN
  FLATPAUX_cpbs_hd_tac THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_eq "match_result";
    distinctness "match_result"; FLATPAUX_pmatch_Pref_Match]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LEFT_AND_EXISTS_THM; GSYM CONJ_ASSOC]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `b1:(varN#flat_v)list` (X_CHOOSE_THEN `b:bool`
    (X_CHOOSE_THEN `lnum:num` (X_CHOOSE_THEN `rv:flat_v` STRIP_ASSUME_TAC))) o
    check (is_exists o concl)) THEN
  FLATPAUX_SUBST_VAR_TAC "hv" THEN
  SUBGOAL_THEN `flat_evaluate env (s:(C,FFI)flat_state)
                  [flat_App t (flat_El 0) [x]] = (s,Rval [rv])` ASSUME_TAC THENL
  [MATCH_MP_TAC FLATPAUX_eval_El THEN EXISTS_TAC `flat_Loc b lnum` THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FLATPAUX_do_app_El_Loc THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  FLATPAUX_UNDISCH_PAT `flat_evaluate (env:(flat_v)flat_environment)
     (s:(C,FFI)flat_state) [flat_Let a b c d] = r` THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  REPEAT(CHANGED_TAC(CASE_REWRITE_TAC[HD] THEN
    REWRITE_TAC FLATPAUX_env_simps)) THEN DISCH_TAC THEN
  FLATPAUX_cpbs_ih_tac `exp2':flat_exp` `spt':num_set`
    `CONS (rv:flat_v) tvs` `pre_bindings:(varN#flat_v)list`
    `flat_environment_v_fupd
       (K (CONS (enc_num_to_name (i + 1),rv:flat_v)
             (flat_environment_v env))) env` THEN
  REWRITE_TAC[MAP; flat_pmatch_def; case_eq "match_result";
              distinctness "match_result"] THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[ALL2; ALL; o_THM; APPEND; flat_environment_INFO.ri_accfupds;
                  K_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[MATCH_MP (CONJUNCT1 ALOOKUP_rel_cons_false)
                (MATCH_MP FLATPAUX_win2 (ASSUME `j < i`))] THEN
  REPEAT CONJ_TAC THEN
  FIRST [ASM_ARITH_TAC;
         FIRST_ASSUM ACCEPT_TAC;
         EXISTS_TAC `b1:(varN#flat_v)list` THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         FLATPAUX_cpbs_fresh_hd_tac THEN NO_TAC;
         FLATPAUX_cpbs_tail_tac `insert k one spt'`
           `[enc_num_to_name (i + 1),rv:flat_v]` THEN NO_TAC;
         MATCH_MP_TAC FLATPAUX_cpbs_every_mono THEN EXISTS_TAC `i:num` THEN
         ASM_REWRITE_TAC[] THEN ARITH_TAC];;
let FLATPAUX_jn_props = prove
 (`!t i (ps:flat_pat list) jn.
     MAP (\(j,p). (j,enc_num_to_name (i + 1 + j)),p,i + 1 + j,
                  Var_local t (enc_num_to_name (i + 1 + j)))
         (enumerate 0 ps) = jn
     ==> LENGTH jn = LENGTH ps /\
         (!n. n < LENGTH ps
              ==> EL n jn = ((n,enc_num_to_name (i + 1 + n)),EL n ps,i + 1 + n,
                             Var_local t (enc_num_to_name (i + 1 + n)))) /\
         MAP FST (MAP SND jn) = ps /\
         (!y. MEM y jn <=>
              ?n. n < LENGTH ps /\
                  y = ((n,enc_num_to_name (i + 1 + n)),EL n ps,i + 1 + n,
                       Var_local t (enc_num_to_name (i + 1 + n))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `!n. n < LENGTH (ps:flat_pat list)
        ==> EL n (MAP (\(j,p). (j,enc_num_to_name (i + 1 + j)),p,i + 1 + j,
                               Var_local t (enc_num_to_name (i + 1 + j)))
                      (enumerate 0 ps)) =
            ((n,enc_num_to_name (i + 1 + n)),EL n ps,i + 1 + n,
             Var_local t (enc_num_to_name (i + 1 + n)))`
  ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC[EL_MAP; LENGTH_enumerate; EL_enumerate; ADD_CLAUSES] THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_enumerate] THEN CONJ_TAC THENL
  [REWRITE_TAC[LIST_EQ_REWRITE; LENGTH_MAP; LENGTH_enumerate] THEN
   ASM_SIMP_TAC[EL_MAP; LENGTH_MAP; LENGTH_enumerate];
   REWRITE_TAC[MEM_EXISTS_EL; LENGTH_MAP; LENGTH_enumerate] THEN
   ASM_MESON_TAC[]]);;

let FLATPAUX_pmatch_Pcon_Match = prove
 (`!(s:(C,FFI)flat_state) stmp ps v bs a.
     flat_pmatch s (flat_Pcon stmp ps) v bs = Match a
     ==> ?stmp' con_vs. v = flat_Conv stmp' con_vs /\
                        LENGTH ps = LENGTH con_vs /\
                        flat_pmatch_list s ps con_vs bs = Match a`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `v:flat_v` (CONJUNCT1 (cases "flat_v"))) THEN
  REWRITE_TAC[flat_pmatch_def; distinctness "match_result";
              distinctness "flat_v"; injectivity "flat_v"] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[distinctness "match_result"] THEN MESON_TAC[]);;

let FLATPAUX_ALOOKUP_unique = prove
 (`!(l:(A#B)list) x v.
     MEM (x,v) l /\ (!w. MEM (x,w) l ==> w = v) ==> ALOOKUP l x = SOME v`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`; `x:A`; `v:B`] THEN
  REWRITE_TAC[ALOOKUP_THM; PAIR_EQ] THEN STRIP_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let FLATPAUX_FOLDR_El = prove
 (`!(used:((num#mlstring)#(flat_pat#num#flat_exp))list) con_vs
    (env:(flat_v)flat_environment) (s:(C,FFI)flat_state) stmp x t exp
    new_names.
     IMAGE (SND o FST) (set_of_list used) SUBSET new_names /\
     (!y. MEM y used
          ==> FST (FST y) < LENGTH con_vs /\
              !env2. ALOOKUP_rel (\x. ~(x IN new_names)) (=)
                       (flat_environment_v env2) (flat_environment_v env)
                     ==> flat_evaluate env2 s [x] =
                         (s,Rval [flat_Conv stmp con_vs]))
     ==> !env2. ALOOKUP_rel (\x. ~(x IN new_names)) (=)
                  (flat_environment_v env2) (flat_environment_v env)
                ==> flat_evaluate env2 s
                      [ITLIST (\((j,nm),r) exp.
                                 flat_Let t (SOME nm) (flat_App t (flat_El j) [x])
                                   exp) used exp] =
                    flat_evaluate
                      (flat_environment_v_fupd
                         (K (APPEND (MAP (\y. SND (FST y),
                                              EL (FST (FST y)) con_vs)
                                         (REVERSE used))
                                    (flat_environment_v env2))) env2)
                      s [exp]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\((j,nm),(r:flat_pat#num#flat_exp)) exp.
       flat_Let t (SOME nm) (flat_App t (flat_El j) [x]) exp) =
    (\y exp. flat_Let t ((\y. SOME (SND (FST y))) y)
               ((\y. flat_App t (flat_El (FST (FST y))) [x]) y) exp)`
  SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y:(num#mlstring)#(flat_pat#num#flat_exp).
       SND (FST y),EL (FST (FST y)) (con_vs:flat_v list)) =
    (\y. THE ((\y. SOME (SND (FST y))) y),
         (\y. EL (FST (FST y)) con_vs) y)`
  SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; THE_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC pat_bindings_evaluate_FOLDR_lemma THEN
  ASM_REWRITE_TAC[IS_SOME_DEF; o_DEF; THE_DEF] THEN CONJ_TAC THENL
  [UNDISCH_TAC `IMAGE (SND o FST)
     (set_of_list (used:((num#mlstring)#(flat_pat#num#flat_exp))list)) SUBSET
                  (new_names:mlstring->bool)` THEN
   REWRITE_TAC[o_DEF];
   ALL_TAC] THEN
  X_GEN_TAC `y:(num#mlstring)#(flat_pat#num#flat_exp)` THEN DISCH_TAC THEN
  X_GEN_TAC `env2:(flat_v)flat_environment` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:(num#mlstring)#(flat_pat#num#flat_exp)` o
    check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC FLATPAUX_eval_El THEN
  EXISTS_TAC `flat_Conv stmp (con_vs:flat_v list)` THEN
  ASM_SIMP_TAC[FLATPAUX_do_app_El_Conv]);;
let FLATPAUX_used_MEM = prove
 (`!(jn:((num#mlstring)#(flat_pat#num#flat_exp))list) used (spt':num_set)
    (ps:flat_pat list) t i.
     (!y. MEM y jn <=>
          ?n. n < LENGTH ps /\
              y = ((n,enc_num_to_name (i + 1 + n)),EL n ps,i + 1 + n,
                   Var_local t (enc_num_to_name (i + 1 + n)))) /\
     FILTER (\(jn,q,kk,e). IS_SOME (lookup kk spt')) jn = used
     ==> !y. MEM y used <=>
             ?n. n < LENGTH ps /\ IS_SOME (lookup (i + 1 + n) spt') /\
                 y = ((n,enc_num_to_name (i + 1 + n)),EL n ps,i + 1 + n,
                      Var_local t (enc_num_to_name (i + 1 + n)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  ASM_REWRITE_TAC[MEM_FILTER] THEN GEN_TAC THEN EQ_TAC THENL
  [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC)) THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   DISCH_TAC THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
   DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   ASM_REWRITE_TAC[] THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]]);;

let FLATPAUX_new_names_props = prove
 (`!(used:((num#mlstring)#(flat_pat#num#flat_exp))list) (con_vs:flat_v list)
    (ps:flat_pat list) t i (spt':num_set).
     (!y. MEM y used <=>
          ?n. n < LENGTH ps /\ IS_SOME (lookup (i + 1 + n) spt') /\
              y = ((n,enc_num_to_name (i + 1 + n)),EL n ps,i + 1 + n,
                   Var_local t (enc_num_to_name (i + 1 + n))))
     ==> (!a b. MEM (a,b) (MAP (\y. SND (FST y),EL (FST (FST y)) con_vs)
                              (REVERSE used)) <=>
                ?n. n < LENGTH ps /\ IS_SOME (lookup (i + 1 + n) spt') /\
                    a = enc_num_to_name (i + 1 + n) /\ b = EL n con_vs) /\
         (!a. MEM a (MAP FST (MAP (\y. SND (FST y),EL (FST (FST y)) con_vs)
                                  (REVERSE used)))
              ==> i < dec_name_to_num a) /\
         (!n. n < LENGTH ps /\ IS_SOME (lookup (i + 1 + n) spt')
              ==> ALOOKUP (MAP (\y. SND (FST y),EL (FST (FST y)) con_vs)
                              (REVERSE used)) (enc_num_to_name (i + 1 + n)) =
                  SOME (EL n con_vs))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!a b. MEM (a,b) (MAP (\y. SND (FST y),EL (FST (FST y)) (con_vs:flat_v list))
                       (REVERSE (used:((num#mlstring)#(flat_pat#num#flat_exp))list))) <=>
          ?n. n < LENGTH (ps:flat_pat list) /\ IS_SOME (lookup (i + 1 + n) (spt':num_set)) /\
              a = enc_num_to_name (i + 1 + n) /\ b = EL n con_vs`
  ASSUME_TAC THENL
  [ASM_REWRITE_TAC[MEM_MAP; MEM_REVERSE] THEN REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:(num#mlstring)#(flat_pat#num#flat_exp)`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `((n,enc_num_to_name (i + 1 + n)),EL n (ps:flat_pat list),i + 1 + n,
                  Var_local t (enc_num_to_name (i + 1 + n)))` THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [GEN_TAC THEN ONCE_REWRITE_TAC[MEM_MAP] THEN REWRITE_TAC[EXISTS_PAIR_THM] THEN
   ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN ASM_REWRITE_TAC[dec_enc] THEN
   ARITH_TAC;
   ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FLATPAUX_ALOOKUP_unique THEN
  ASM_REWRITE_TAC[enc_num_to_name_inj; EQ_ADD_LCANCEL] THEN CONJ_TAC THENL
  [EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]; MESON_TAC[]]);;

let FLATPAUX_pats_bindings_EL = prove
 (`!(P:mlstring->bool) ps n.
     ALL P (flat_pats_bindings ps) /\ n < LENGTH ps
     ==> ALL P (flat_pat_bindings (EL n ps))`,
  REWRITE_TAC[pats_bindings_FLAT_MAP; GSYM ALL_MEM; MEM_FLAT; MEM_REVERSE;
              MEM_MAP] THEN
  MESON_TAC[MEM_EL]);;
let FLATPAUX_cpbs_pcon_tac =
  (FLATPAUX_cpbs_intro_tac [`t:tra`; `i:num`;
    `stmp:((ctor_id#type_group_id)option)`; `ps:flat_pat list`;
    `k:num`; `x:flat_exp`; `m:(flat_pat#num#flat_exp)list`; `exp:flat_exp`] THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  ABBREV_TAC `jn = MAP (\(j,p). (j,enc_num_to_name (i + 1 + j)),p,i + 1 + j,
                  Var_local t (enc_num_to_name (i + 1 + j)))
         (enumerate 0 (ps:flat_pat list))` THEN
  IL1AUX_PAIRARG_TAC THEN FLATPAUX_PAIR_EQ_SUBST_TAC) THEN
  (ABBREV_TAC `used = FILTER (\(jn,q,kk,e). IS_SOME (lookup kk (spt':num_set)))
                (jn:((num#mlstring)#(flat_pat#num#flat_exp))list)`) THEN
  (RULE_ASSUM_TAC(REWRITE_RULE[case_eq "match_result";
    distinctness "match_result"]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `b1:(varN#flat_v)list` STRIP_ASSUME_TAC o
    check (is_exists o concl)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `stmp':(ctor_id#type_id)option`
    (X_CHOOSE_THEN `con_vs:flat_v list` STRIP_ASSUME_TAC) o
    MATCH_MP FLATPAUX_pmatch_Pcon_Match) THEN
  FLATPAUX_SUBST_VAR_TAC "hv" THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FLATPAUX_jn_props)) THEN
  (FIRST_ASSUM(fun th19 -> FIRST_ASSUM(fun th12 ->
    ASSUME_TAC(MATCH_MP FLATPAUX_used_MEM (CONJ th19 th12)))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `con_vs:flat_v list` o
    MATCH_MP FLATPAUX_new_names_props) THEN STRIP_TAC) THEN
  (MP_TAC(ISPECL [`used:((num#mlstring)#(flat_pat#num#flat_exp))list`;
    `con_vs:flat_v list`; `env:(flat_v)flat_environment`;
    `s:(C,FFI)flat_state`; `stmp':(ctor_id#type_id)option`; `x:flat_exp`;
    `t:tra`; `exp2':flat_exp`; `{y:mlstring | ~(dec_name_to_num y < i)}`]
    FLATPAUX_FOLDR_El)) THEN
  (ANTS_TAC THENL
  [CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM; IN_SET_OF_LIST; o_THM] THEN
    X_GEN_TAC `z:mlstring` THEN
    DISCH_THEN(X_CHOOSE_THEN `y:(num#mlstring)#(flat_pat#num#flat_exp)` MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[dec_enc] THEN ARITH_TAC;
    ALL_TAC] THEN
   X_GEN_TAC `y:(num#mlstring)#(flat_pat#num#flat_exp)` THEN DISCH_TAC THEN
   SUBGOAL_THEN `~NULL (used:((num#mlstring)#(flat_pat#num#flat_exp))list)`
     ASSUME_TAC THENL
   [REWRITE_TAC[NULL_EQ_NIL] THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MEM]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   UNDISCH_TAC `MEM (y:(num#mlstring)#(flat_pat#num#flat_exp)) used` THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
   FLATPAUX_SUBST_VAR_TAC "y" THEN REWRITE_TAC[FST] THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   X_GEN_TAC `env2:(flat_v)flat_environment` THEN DISCH_TAC THEN
   REWRITE_TAC[GSYM pure_eval_to_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[domain_insert; IN_INSERT] THEN
   MATCH_MP_TAC(GEN_ALL ALOOKUP_rel_mono) THEN
   EXISTS_TAC `\x:mlstring. ~(x IN {y:mlstring | ~(dec_name_to_num y < i)})` THEN
   EXISTS_TAC `(=):flat_v->flat_v->bool` THEN
   ASM_REWRITE_TAC[IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[];
   ALL_TAC]) THEN
  (DISCH_THEN(MP_TAC o SPEC `env:(flat_v)flat_environment`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC ALOOKUP_rel_refl THEN REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) THEN
  (FLATPAUX_cpbs_ih_tac `exp2':flat_exp` `spt':num_set`
    `APPEND (con_vs:flat_v list) tvs` `pre_bindings:(varN#flat_v)list`
    `flat_environment_v_fupd
       (K (APPEND (MAP (\y. SND (FST y),EL (FST (FST y)) (con_vs:flat_v list))
                       (REVERSE (used:((num#mlstring)#(flat_pat#num#flat_exp))list)))
                  (flat_environment_v env))) env` THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[flat_environment_INFO.ri_accfupds; K_THM; MAP_APPEND;
                  pmatch_list_append_Match_exists]) THEN
  CONJ_TAC THENL
  [MAP_EVERY EXISTS_TAC [`con_vs:flat_v list`; `tvs:flat_v list`;
                         `b1:(varN#flat_v)list`] THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC LIST_REL_APPEND_suff THEN CONJ_TAC THENL
   [((REWRITE_TAC[LIST_REL_EL_EQN; LENGTH_MAP] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `n < LENGTH (ps:flat_pat list)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_MAP] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV)) THEN
    (X_GEN_TAC `env2:(flat_v)flat_environment` THEN STRIP_TAC THEN
    REWRITE_TAC[pure_eval_to_def; flat_evaluate_def] THEN
    SUBGOAL_THEN `((\k. k > j /\ k < i + 2 + LENGTH (con_vs:flat_v list)) o
                   dec_name_to_num) (enc_num_to_name (i + 1 + n))` ASSUME_TAC THENL
    [REWRITE_TAC[o_THM; dec_enc] THEN ASM_ARITH_TAC; ALL_TAC]) THEN
    (FIRST_X_ASSUM(fun th -> FIRST_X_ASSUM(fun th2 ->
      MP_TAC(MATCH_MP ALOOKUP_rel_EQ_ALOOKUP (CONJ th2 th))))) THEN
    (DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ALOOKUP_APPEND]) THEN
    (SUBGOAL_THEN `IS_SOME (lookup (i + 1 + n) (spt':num_set))` ASSUME_TAC THENL
    [REWRITE_TAC[IS_SOME_EXISTS; GSYM domain_lookup] THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
    (ASM_SIMP_TAC[] THEN CASE_REWRITE_TAC[]));
    (MATCH_MP_TAC FLATPAUX_cpbs_rel_mono THEN
  MAP_EVERY EXISTS_TAC [`if NULL (used:((num#mlstring)#(flat_pat#num#flat_exp))list)
                         then spt' else insert k one (spt':num_set)`;
    `flat_environment_v (env:(flat_v)flat_environment)`; `i:num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [COND_CASES_TAC THEN REWRITE_TAC[SUBSET_REFL; domain_insert] THEN SET_TAC[];
   ALL_TAC] THEN
  X_GEN_TAC `env2:(flat_v)flat_environment` THEN DISCH_TAC THEN
  MATCH_MP_TAC FLATPAUX_ALOOKUP_rel_drop THEN
  EXISTS_TAC `(\k. k > j /\ k < i + 2 + LENGTH (con_vs:flat_v list)) o
              dec_name_to_num` THEN
  EXISTS_TAC `MAP (\y. SND (FST y),EL (FST (FST y)) (con_vs:flat_v list))
                (REVERSE (used:((num#mlstring)#(flat_pat#num#flat_exp))list))` THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:mlstring` THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:mlstring` o check (fun th ->
    can (find_term ((=) `dec_name_to_num`)) (concl th) && is_forall (concl th) &&
    is_imp (snd (dest_forall (concl th))))) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC)];
   ALL_TAC] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  (CONJ_TAC THENL
  [SUBGOAL_THEN `ALL ((~) o ((\k. k < j) o dec_name_to_num) o FST)
     (MAP (\y. SND (FST y),EL (FST (FST y)) (con_vs:flat_v list))
          (REVERSE (used:((num#mlstring)#(flat_pat#num#flat_exp))list)))`
     (fun th -> REWRITE_TAC[MATCH_MP ALOOKUP_rel_APPEND_L_false th]) THENL
   [REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:mlstring`; `b:flat_v`] THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[dec_enc] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]];
   ALL_TAC]) THEN
  (CONJ_TAC THENL
  [ONCE_REWRITE_TAC[GSYM ALL_EL] THEN REWRITE_TAC[LENGTH_MAP] THEN
   ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   SUBGOAL_THEN `n < LENGTH (ps:flat_pat list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_SIMP_TAC[EL_MAP] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC FLATPAUX_pats_bindings_EL THEN ASM_REWRITE_TAC[];
    ASM_ARITH_TAC];
   MATCH_MP_TAC FLATPAUX_cpbs_every_mono THEN EXISTS_TAC `i:num` THEN
   ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* HOL4: the free variables j and base_vs are left free, as in HOL4; the  *)
(* unused quantified variable vset is dropped                               *)

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
  MATCH_MP_TAC compile_pat_bindings_ind THEN REPEAT CONJ_TAC THENL
  [FLATPAUX_cpbs_nil_tac; FLATPAUX_cpbs_pany_tac; FLATPAUX_cpbs_pvar_tac;
   FLATPAUX_cpbs_plit_tac; FLATPAUX_cpbs_pcon_tac; FLATPAUX_cpbs_pas_tac;
   FLATPAUX_cpbs_pref_tac]);;

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
  let cases1 = CONJUNCT1 flat_patternProof_v_rel_cases in
  let simp = CAKE_SIMP_CONV [simple_basic_val_rel_def; v_container_xs_def;
     injectivity "flat_v"; distinctness "flat_v"; LIST_REL_NIL; GSYM CONJ_ASSOC;
     RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM; UNWIND_THM1; UNWIND_THM2] in
  REPEAT CONJ_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [cases1] THEN
  CONV_TAC(LAND_CONV simp) THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[v_container_xs_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_container_xs_def]) THEN
  TRY(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_container_xs_def]) THEN
  ASM_MESON_TAC[]);;
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
  STRUCT_CASES_TAC(ISPEC `e:((varN#flat_v)list)match_result` (cases "match_result")) THEN
  REWRITE_TAC[match_rel_def; distinctness "match_result"]);;
let _ = cake_add_simps [match_rel_thms];;

let match_rel_IMP = prove
 (`match_rel N e e'
   ==> (e = No_match /\ e = e') \/
       (e = Match_type_error /\ e = e') \/
       (?env1 env2. e = Match env1 /\ e' = Match env2 /\
                    ALOOKUP_rel (\x. dec_name_to_num x < N)
                      flat_patternProof_v_rel env1 env2)`,
  STRUCT_CASES_TAC(ISPEC `e:((varN#flat_v)list)match_result` (cases "match_result")) THEN
  STRUCT_CASES_TAC(ISPEC `e':((varN#flat_v)list)match_result` (cases "match_result")) THEN
  REWRITE_TAC[match_rel_def; distinctness "match_result"; injectivity "match_result"] THEN
  MESON_TAC[]);;

let MAX_ADD_LESS = prove
 (`MAX i j + k < l <=> i + k < l /\ j + k < l`,
  REWRITE_TAC[MAX] THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let LESS_MAX_ADD = prove
 (`l < MAX i j + k <=> l < i + k \/ l < j + k`,
  REWRITE_TAC[MAX] THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let MAX_ADD_LE = prove
 (`MAX i j + k <= l <=> i + k <= l /\ j + k <= l`,
  REWRITE_TAC[MAX] THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let flat_patternProof_env_rel_mono = prove
 (`flat_patternProof_env_rel i env1 env2 /\ j <= i
   ==> flat_patternProof_env_rel j env1 env2`,
  REWRITE_TAC[FLATPAUX_env_rel_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC(GEN_ALL ALOOKUP_rel_mono) THEN
  EXISTS_TAC `\x. dec_name_to_num x < i` THEN
  EXISTS_TAC `flat_patternProof_v_rel` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let env_rel_ALOOKUP = prove
 (`flat_patternProof_env_rel N env1 env2 /\ dec_name_to_num n < N
   ==> OPTREL flat_patternProof_v_rel (ALOOKUP (flat_environment_v env1) n)
         (ALOOKUP (flat_environment_v env2) n)`,
  REWRITE_TAC[FLATPAUX_env_rel_def; ALOOKUP_rel_def] THEN MESON_TAC[]);;
let flat_patternProof_ALOOKUP_MAP_3 = prove
 (`(!x. MEM x xs ==> FST ((f:A#B->A#C) x) = FST x)
   ==> ALOOKUP (MAP f xs) x = OPTION_MAP (\y. SND (f (x,y))) (ALOOKUP xs x)`,
  SPEC_TAC(`xs:(A#B)list`,`xs:(A#B)list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALOOKUP_THM; OPTION_MAP_DEF; MEM] THEN
  REWRITE_TAC[DISJ_IMP_THM; FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPEC `h:A#B` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:B` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `(f:A#B->A#C) (a,b)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:A` (X_CHOOSE_THEN `d:C` (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN ASSUME_TAC th))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq (concl th) && is_var (lhs (concl th)) && is_var (rhs (concl th)))) THEN
  REWRITE_TAC[ALOOKUP_THM] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF]);;

let ALOOKUP_rel_MAP_same = prove
 (`(!x. MEM x xs ==> FST ((f:D->A#B) x) = FST ((g:D->A#C) x) /\
                     (P (FST (g x)) ==> R (SND (f x)) (SND (g x))))
   ==> ALOOKUP_rel P R (MAP f xs) (MAP g xs)`,
  SPEC_TAC(`xs:D list`,`xs:D list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; MEM; ALOOKUP_rel_empty] THEN
  REWRITE_TAC[DISJ_IMP_THM; FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp (concl th) &&
    (try fst (dest_const (fst (strip_comb (rand (concl th))))) = "ALOOKUP_rel"
     with Failure _ -> false))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPEC `(f:D->A#B) h` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:B` (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]))) THEN
  MP_TAC(ISPEC `(g:D->A#C) h` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a':A` (X_CHOOSE_THEN `c:C` (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq (concl th) && is_var (lhs (concl th)) && is_var (rhs (concl th)))) THEN
  MATCH_MP_TAC ALOOKUP_rel_cons THEN ASM_REWRITE_TAC[]);;
let FLATPAUX_MAP_FST_triple = prove
 (`!(g:flat_exp->flat_exp) (funs:(varN#varN#flat_exp)list).
     MAP FST (MAP (\(n,m,e). n,m,g e) funs) = MAP FST funs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  SPEC_TAC(`h:varN#varN#flat_exp`,`h:varN#varN#flat_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[]);;

let FLATPAUX_find_recfun_MAP = prove
 (`!(g:flat_exp->flat_exp) n (funs:(varN#varN#flat_exp)list) m e.
     find_recfun n funs = SOME (m,e)
     ==> find_recfun n (MAP (\(n,m,e). n,m,g e) funs) = SOME (m,g e)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[find_recfun_ALOOKUP] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALOOKUP_THM; option_DISTINCT] THEN
  SPEC_TAC(`h:varN#varN#flat_exp`,`h:varN#varN#flat_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[ALOOKUP_THM] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN MESON_TAC[]);;

let FLATPAUX_do_opapp_rec = prove
 (CASE_TERM `!N env1 env2 (funs:(varN#varN#flat_exp)list) cfg n v v' m exp.
   flat_patternProof_env_rel N env1 env2 /\
   ALL (\(n,m,e). FST (flat_pattern_compile_exp cfg e) < N) funs /\
   flat_patternProof_v_rel v v' /\ ALL_DISTINCT (MAP FST funs) /\
   find_recfun n funs = SOME (m,exp)
   ==> ?i sg exp' env2' cfg'.
         flat_pattern_compile_exp cfg' exp = (i,sg,exp') /\
         flat_patternProof_env_rel (i + 1)
           (flat_environment_v_fupd
              (K (CONS (m,v) (flat_build_rec_env funs env1
                                (flat_environment_v env1)))) env1) env2' /\
         ALL_DISTINCT (MAP FST (MAP (\(n,m,e).
           (n,m,SND (SND (flat_pattern_compile_exp cfg e)))) funs)) /\
         (match find_recfun n (MAP (\(n,m,e).
                   (n,m,SND (SND (flat_pattern_compile_exp cfg e)))) funs) with
            NONE -> NONE
          | SOME (n',e) ->
              SOME (flat_environment_v_fupd
                      (K (CONS (n',v')
                            (flat_build_rec_env
                               (MAP (\(n,m,e).
                                  (n,m,SND (SND (flat_pattern_compile_exp cfg e))))
                                  funs) env2 (flat_environment_v env2)))) env2,
                    e)) = SOME (env2',exp')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP
    (BETA_RULE (ISPEC `\e. SND (SND (flat_pattern_compile_exp cfg e))`
                  FLATPAUX_find_recfun_MAP)) th]) THEN
  CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[FLATPAUX_MAP_FST_triple; option_INJ; PAIR_EQ] THEN
  MAP_EVERY EXISTS_TAC [`FST (flat_pattern_compile_exp cfg exp)`;
    `FST (SND (flat_pattern_compile_exp cfg exp))`;
    `SND (SND (flat_pattern_compile_exp cfg exp))`;
    `flat_environment_v_fupd (K (CONS (m,v')
       (flat_build_rec_env (MAP (\(n,m,e).
          n,m,SND (SND (flat_pattern_compile_exp cfg e))) funs) env2
          (flat_environment_v env2)))) env2`; `cfg:flat_pattern_config`] THEN
  REWRITE_TAC[PAIR; FLATPAUX_env_rel_def; flat_environment_INFO.ri_accfupds;
              K_THM] THEN
  MATCH_MP_TAC ALOOKUP_rel_cons THEN ASM_REWRITE_TAC[build_rec_env_eq_MAP] THEN
  MATCH_MP_TAC ALOOKUP_rel_append_suff THEN CONJ_TAC THENL
  [REWRITE_TAC[GSYM MAP_o] THEN MATCH_MP_TAC ALOOKUP_rel_MAP_same THEN
   REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THEN MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (CONJUNCT2
     flat_patternProof_v_rel_rules))) THEN
   EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `FST (flat_pattern_compile_exp cfg exp) < N` ASSUME_TAC THENL
  [UNDISCH_TAC `ALL (\(n,m,e). FST (flat_pattern_compile_exp cfg e) < N)
                  (funs:(varN#varN#flat_exp)list)` THEN
   REWRITE_TAC[GSYM ALL_MEM] THEN
   DISCH_THEN(MP_TAC o SPEC `(n:varN,m:varN,exp:flat_exp)`) THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN DISCH_THEN MATCH_MP_TAC THEN
   MATCH_MP_TAC ALOOKUP_MEM THEN ASM_REWRITE_TAC[GSYM find_recfun_ALOOKUP];
   ALL_TAC] THEN
  MATCH_MP_TAC(GEN_ALL ALOOKUP_rel_mono) THEN
  EXISTS_TAC `\x. dec_name_to_num x < N` THEN
  EXISTS_TAC `flat_patternProof_v_rel` THEN
  ASM_REWRITE_TAC[GSYM FLATPAUX_env_rel_def] THEN REPEAT STRIP_TAC THEN
  ASM_ARITH_TAC);;

let do_opapp_thm = prove
 (`flat_do_opapp vs1 = SOME (env1,exp) /\ ALL2 flat_patternProof_v_rel vs1 vs2
   ==> ?i sg exp' env2 cfg. flat_pattern_compile_exp cfg exp = (i,sg,exp') /\
         flat_patternProof_env_rel (i + 1) env1 env2 /\
         flat_do_opapp vs2 = SOME (env2,exp')`,
  REWRITE_TAC[flat_do_opapp_def] THEN STRIP_TAC THEN FLATSEMAUX_SPLIT_TAC THEN
  GVS[FLATPAUX_LIST_REL_CONS1; LIST_REL_NIL; v_rel_l_cases] THENL
  [MAP_EVERY EXISTS_TAC [`FST (flat_pattern_compile_exp cfg exp)`;
     `FST (SND (flat_pattern_compile_exp cfg exp))`; `cfg:flat_pattern_config`] THEN
   REWRITE_TAC[PAIR; FLATPAUX_env_rel_def; flat_environment_INFO.ri_accfupds] THEN
   MATCH_MP_TAC ALOOKUP_rel_cons THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(GEN_ALL ALOOKUP_rel_mono) THEN
   EXISTS_TAC `\x. dec_name_to_num x < N` THEN
   EXISTS_TAC `flat_patternProof_v_rel` THEN
   ASM_REWRITE_TAC[GSYM FLATPAUX_env_rel_def] THEN REPEAT STRIP_TAC THEN
   ASM_ARITH_TAC;
   MATCH_MP_TAC FLATPAUX_do_opapp_rec THEN EXISTS_TAC `N:num` THEN
   ASM_REWRITE_TAC[]]);;

let do_opapp_thm_REVERSE = prove
 (`flat_do_opapp (REVERSE vs1) = SOME (env1,exp) /\
   ALL2 flat_patternProof_v_rel vs1 vs2
   ==> ?i sg exp' env2 cfg. flat_pattern_compile_exp cfg exp = (i,sg,exp') /\
         flat_patternProof_env_rel (i + 1) env1 env2 /\
         flat_do_opapp (REVERSE vs2) = SOME (env2,exp')`,
  STRIP_TAC THEN
  MP_TAC(INST [`REVERSE vs1:flat_v list`,`vs1:flat_v list`;
               `REVERSE vs2:flat_v list`,`vs2:flat_v list`] do_opapp_thm) THEN
  ASM_SIMP_TAC[EVERY2_REVERSE]);;
let FLATPAUX_match_rel_cons = prove
 (CASE_TERM `!N (pm:((varN#flat_v)list)match_result) pm1 pl pl1 g g1.
   (~(pm = Match_type_error) ==> match_rel N pm pm1) /\
   (pm = No_match /\ ~(pl = Match_type_error) ==> match_rel N pl pl1) /\
   (!b b1. pm = Match b /\
           ALOOKUP_rel (\x. dec_name_to_num x < N) flat_patternProof_v_rel b b1 /\
           ~(g b = Match_type_error) ==> match_rel N (g b) (g1 b1)) /\
   ~((match pm with
        No_match -> (match pl with
                       No_match -> No_match
                     | Match_type_error -> Match_type_error
                     | Match a -> No_match)
      | Match_type_error -> Match_type_error
      | Match b -> g b) = Match_type_error)
   ==> match_rel N
         (match pm with
            No_match -> (match pl with
                           No_match -> No_match
                         | Match_type_error -> Match_type_error
                         | Match a -> No_match)
          | Match_type_error -> Match_type_error
          | Match b -> g b)
         (match pm1 with
            No_match -> (match pl1 with
                           No_match -> No_match
                         | Match_type_error -> Match_type_error
                         | Match a -> No_match)
          | Match_type_error -> Match_type_error
          | Match b -> g1 b)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `pm:((varN#flat_v)list)match_result` (cases "match_result")) THEN
  STRUCT_CASES_TAC(ISPEC `pm1:((varN#flat_v)list)match_result` (cases "match_result")) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[match_rel_def; match_rel_thms; distinctness "match_result";
              injectivity "match_result"] THEN
  STRUCT_CASES_TAC(ISPEC `pl:((varN#flat_v)list)match_result` (cases "match_result")) THEN
  STRUCT_CASES_TAC(ISPEC `pl1:((varN#flat_v)list)match_result` (cases "match_result")) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[match_rel_def; match_rel_thms; distinctness "match_result";
              injectivity "match_result"] THEN
  MESON_TAC[]);;

let FLATPAUX_store_lookup_rel = prove
 (`!(R:A->B->bool) refs1 refs2 n x.
     ALL2 (sv_rel R) refs1 refs2 /\ store_lookup n refs1 = SOME x
     ==> ?y. store_lookup n refs2 = SOME y /\ sv_rel R x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[store_lookup_def; LIST_REL_EL_EQN] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[option_INJ] THEN
  REWRITE_TAC[UNWIND_THM1] THEN ASM_MESON_TAC[]);;

let FLATPAUX_pmatch_rel = prove
 (`(!(s:(C,FFI)flat_state) p v vs s1 v1 vs1.
      ~(flat_pmatch s p v vs = Match_type_error) /\
      flat_patternProof_state_rel cfg s s1 /\ flat_patternProof_v_rel v v1 /\
      ALOOKUP_rel (\x. dec_name_to_num x < N) flat_patternProof_v_rel vs vs1
      ==> match_rel N (flat_pmatch s p v vs) (flat_pmatch s1 p v1 vs1)) /\
   (!(s:(C,FFI)flat_state) ps v vs s1 v1 vs1.
      ~(flat_pmatch_list s ps v vs = Match_type_error) /\
      flat_patternProof_state_rel cfg s s1 /\ ALL2 flat_patternProof_v_rel v v1 /\
      ALOOKUP_rel (\x. dec_name_to_num x < N) flat_patternProof_v_rel vs vs1
      ==> match_rel N (flat_pmatch_list s ps v vs) (flat_pmatch_list s1 ps v1 vs1))`,
  MATCH_MP_TAC flat_pmatch_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_pmatch_def; v_rel_l_cases;
                              distinctness "match_result"]) THEN
  REWRITE_TAC[flat_pmatch_def; match_rel_def] THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  TRY(FLATPAUX_SUBST_VAR_TAC "v1") THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_NIL]) THEN
  TRY(FLATPAUX_SUBST_VAR_TAC "v1") THEN
  REWRITE_TAC[flat_pmatch_def; match_rel_def] THEN
  FIRST
   [FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC ALOOKUP_rel_cons THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    (* Plit *)
    ASM_CASES_TAC `l:lit = l'` THEN ASM_REWRITE_TAC[match_rel_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[match_rel_def] THEN NO_TAC;
    (* Pas *)
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ALOOKUP_rel_cons THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    (* Pcon *)
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM (MATCH_MP LIST_REL_LENGTH th)]) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    ASM_CASES_TAC `pmatch_stamps_ok stmp stmp' (LENGTH (ps:flat_pat list))
                     (LENGTH (vs:flat_v list))` THEN
    ASM_REWRITE_TAC[match_rel_def] THEN
    ASM_CASES_TAC `OPTION_MAP FST (stmp:(ctor_id#type_group_id)option) =
                   OPTION_MAP FST (stmp':(ctor_id#type_id)option)` THEN
    ASM_CASES_TAC `LENGTH (ps:flat_pat list) = LENGTH (vs:flat_v list)` THEN
    ASM_REWRITE_TAC[match_rel_def] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    (* Pref *)
    SUBGOAL_THEN `ALL2 (sv_rel flat_patternProof_v_rel)
                    (flat_state_refs (s:(C,FFI)flat_state))
                    (flat_state_refs (s1:(C,FFI)flat_state))` ASSUME_TAC THENL
    [UNDISCH_TAC `flat_patternProof_state_rel cfg (s:(C,FFI)flat_state) s1` THEN
     SIMP_TAC[flat_patternProof_state_rel_def];
     ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th])
      (X_CHOOSE_THEN `sv:(flat_v)store_v` (fun th -> REWRITE_TAC[th] THEN
         ASSUME_TAC th))
      (ISPEC `store_lookup lnum (flat_state_refs (s:(C,FFI)flat_state))`
         (cases "option")) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[match_rel_thms] THEN
    FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
      MP_TAC(MATCH_MP FLATPAUX_store_lookup_rel (CONJ th th2)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:(flat_v)store_v` (CONJUNCTS_THEN2
      (fun th -> REWRITE_TAC[th]) MP_TAC)) THEN
    REWRITE_TAC[sv_rel_cases] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[match_rel_thms] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] o
      check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN NO_TAC;
    (* pmatch_list cons *)
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[FLATPAUX_LIST_REL_CONS1] o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "ALL2"
      with Failure _ -> false)) THEN
    DISCH_THEN(X_CHOOSE_THEN `hv:flat_v` (X_CHOOSE_THEN `tvs:flat_v list`
      STRIP_ASSUME_TAC)) THEN
    FLATPAUX_SUBST_VAR_TAC "v1" THEN REWRITE_TAC[flat_pmatch_def] THEN
    MATCH_MP_TAC FLATPAUX_match_rel_cons THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
    [DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     MAP_EVERY X_GEN_TAC [`b:(varN#flat_v)list`; `b1:(varN#flat_v)list`] THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `b:(varN#flat_v)list`) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

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
  REWRITE_TAC[UNWIND_THM1] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl)) THEN
  MP_TAC FLATPAUX_pmatch_rel THEN
  DISCH_THEN(CONJUNCTS_THEN (fun th -> TRY(MATCH_MP_TAC th))) THEN
  ASM_REWRITE_TAC[]);;

let simple_val_rel_step_isClosure = prove
 (`simple_basic_val_rel x y ==> ~isClosure x /\ ~isClosure y`,
  STRUCT_CASES_TAC(ISPEC `x:flat_v` (CONJUNCT1 (cases "flat_v"))) THEN
  REWRITE_TAC[simple_basic_val_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[isClosure_simps]);;
let flat_patternProof_simple_val_rel = prove
 (`flat_simple_val_rel flat_patternProof_v_rel`,
  REWRITE_TAC[flat_simple_val_rel_def] THEN
  ONCE_REWRITE_TAC[CONJUNCT1 flat_patternProof_v_rel_cases] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THENL
  [STRIP_TAC THEN ASM_REWRITE_TAC[isClosure_simps] THEN
   ASM_MESON_TAC[simple_val_rel_step_isClosure];
   DISCH_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[isClosure_simps]) THEN
   ASM_MESON_TAC[isClosure_simps]]);;

let flat_patternProof_simple_state_rel = prove
 (`flat_simple_state_rel flat_patternProof_v_rel
     (flat_patternProof_state_rel cfg:(C,FFI)flat_state->(C,FFI)flat_state->bool)`,
  REWRITE_TAC[flat_simple_state_rel_def; flat_patternProof_state_rel_def;
              flat_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[]);;

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
  STRIP_TAC THEN
  MP_TAC(SPECL [`op:flat_op`; `s1:(C,FFI)flat_state`; `REVERSE vs1:flat_v list`;
                `t1:(C,FFI)flat_state`; `r1:(flat_v,flat_v)result`;
                `s2:(C,FFI)flat_state`; `REVERSE vs2:flat_v list`]
               flat_patternProof_do_app_thm) THEN
  ASM_SIMP_TAC[EVERY2_REVERSE]);;

let do_if_helper = prove
 (`flat_do_if b x y = SOME e /\ flat_patternProof_v_rel b b'
   ==> ((b' = flat_Boolv T) <=> (b = flat_Boolv T)) /\
       ((b' = flat_Boolv F) <=> (b = flat_Boolv F))`,
  REWRITE_TAC[flat_do_if_def] THEN
  ASM_CASES_TAC `b = flat_Boolv T` THEN ASM_REWRITE_TAC[] THENL
  [ALL_TAC;
   ASM_CASES_TAC `b = flat_Boolv F` THEN
   ASM_REWRITE_TAC[option_DISTINCT]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[flat_Boolv_def; v_rel_l_cases; LIST_REL_NIL] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[injectivity "flat_v"; option_INJ; PAIR_EQ; true_tag_def;
                  false_tag_def; ARITH_EQ]);;

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
  `measure flat_v_size`
  TERM_TAC
  `(encode_val (flat_Litv l) = pattern_semantics_Litv l) /\
   (encode_val (flat_Conv stmp xs) =
      Term (match stmp with NONE -> NONE | SOME (i,_) -> SOME i)
           (MAP encode_val xs)) /\
   (encode_val (flat_Loc _ n) = pattern_semantics_RefPtr n) /\
   (encode_val _ = pattern_semantics_Other)`;;

let encode_val_ind = cake_ind "encode_val";;
let FLATPAUX_eval_App1 = prove
 (`!(env:(flat_v)flat_environment) (s:(C,FFI)flat_state) x t op w s' r.
     flat_evaluate env s [x] = (s,Rval [w]) /\
     ~(op = Src Opapp) /\ ~(op = Src Eval) /\ ~(op = Src (ThunkOp ForceThunk)) /\
     flat_do_app s op [w] = SOME (s',Rval r)
     ==> flat_evaluate env s [flat_App t op [x]] = (s',Rval [r])`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[flat_evaluate_def; REVERSE; APPEND] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[REVERSE; APPEND] THEN
  CASE_REWRITE_TAC[list_result_def]);;
let FLATPAUX_option_DISTINCT = CONJ option_DISTINCT (distinctness "option");;

let FLATPAUX_decode_test_TagLenEq = prove
 (`pure_eval_to (s:(C,FFI)flat_state) env x (flat_Conv (SOME (c,tid)) xs)
   ==> pure_eval_to s env
         (flat_pattern_decode_test tr (pattern_semantics_TagLenEq t l) x)
         (flat_Boolv (t = c /\ l = LENGTH xs))`,
  REWRITE_TAC[pure_eval_to_def; flat_pattern_decode_test_def] THEN
  DISCH_TAC THEN MATCH_MP_TAC FLATPAUX_eval_App1 THEN
  EXISTS_TAC `flat_Conv (SOME (c:ctor_id,tid:type_id)) xs` THEN
  ASM_REWRITE_TAC[distinctness "flat_op"; flat_do_app_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[list_result_def] THEN
  AP_TERM_TAC THEN MESON_TAC[]);;

let FLATPAUX_decode_test_LitEq = prove
 (`pure_eval_to (s:(C,FFI)flat_state) env x (flat_Litv l2) /\
   lit_same_type l1 l2
   ==> pure_eval_to s env (flat_pattern_decode_test tr (LitEq l1) x)
         (flat_Boolv (l1 = l2))`,
  REWRITE_TAC[pure_eval_to_def; flat_pattern_decode_test_def] THEN
  STRIP_TAC THEN
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[flat_evaluate_def; REVERSE; APPEND; HD;
    distinctness "flat_op"; injectivity "flat_op"; distinctness "op"] THEN
    CASE_REWRITE_TAC[])) THEN
  REWRITE_TAC[flat_do_app_def] THEN
  REPEAT(CHANGED_TAC(REWRITE_TAC[REVERSE; APPEND] THEN CASE_REWRITE_TAC[])) THEN
  ASM_SIMP_TAC[flat_do_eq_def; lit_same_type_sym] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[list_result_def; PAIR_EQ; injectivity "result"; CONS_11] THEN
  AP_TERM_TAC THEN MESON_TAC[]);;

let decode_test_simulation = prove
 (`dt_test test enc_v = SOME b /\
   pure_eval_to (s:(C,FFI)flat_state) env x v /\ enc_v = encode_val v
   ==> pure_eval_to s env (flat_pattern_decode_test tr test x) (flat_Boolv b)`,
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> c /\ a /\ b`] THEN
  DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th) THEN SUBST1_TAC(CONJUNCT1 th)) THEN
  STRUCT_CASES_TAC(ISPEC `v:flat_v` (CONJUNCT1 (cases "flat_v"))) THEN
  STRUCT_CASES_TAC(ISPEC `test:dTest` (cases "dTest")) THEN
  REWRITE_TAC[encode_val_def; dt_test_def; FLATPAUX_option_DISTINCT] THEN
  EVERY_CASE_TAC THEN
  REWRITE_TAC[dt_test_def; FLATPAUX_option_DISTINCT; option_INJ] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  TRY(MATCH_MP_TAC FLATPAUX_decode_test_LitEq THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  REWRITE_TAC[LENGTH_MAP] THEN
  FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP FLATPAUX_decode_test_TagLenEq));;

let app_pos_Term_IMP = prove
 (`!xs n. app_pos refs (Pos n pos) (Term c xs) = SOME y
          ==> n < LENGTH xs /\ app_pos refs pos (EL n xs) = SOME y`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[app_pos_def; FLATPAUX_option_DISTINCT; LENGTH] THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[app_pos_def; EL; HD; TL; LT_0; LT_SUC; FLATPAUX_option_DISTINCT]);;

let encode_refs_def = cake_def
  `encode_refs (s:(C,FFI)flat_state) =
     FUN_FMAP (\i. encode_val (match EL i (flat_state_refs s) with Refv v -> v))
       (count (LENGTH (flat_state_refs s)) INTER
        {i | ?v. EL i (flat_state_refs s) = Refv v})`;;

let FLOOKUP_encode_refs = prove
 (CASE_TERM
  `FLOOKUP (encode_refs (s:(C,FFI)flat_state)) n =
     if n < LENGTH (flat_state_refs s)
     then (match EL n (flat_state_refs s) with
             Refv v -> SOME (encode_val v)
           | _ -> NONE)
     else NONE`,
  REWRITE_TAC[encode_refs_def] THEN
  SIMP_TAC[FLOOKUP_FUN_FMAP; FINITE_INTER; count_DEF; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
  ASM_CASES_TAC `n < LENGTH (flat_state_refs (s:(C,FFI)flat_state))` THEN
  ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `EL n (flat_state_refs (s:(C,FFI)flat_state))`
    (cases "store_v")) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "store_v"; injectivity "store_v"] THEN
  REWRITE_TAC[MESON[] `?v:flat_v. a = v`]);;

let decode_pos_simulation = prove
 (`!pos exp x.
     app_pos (encode_refs (s:(C,FFI)flat_state)) pos (encode_val x) = SOME enc_y /\
     pure_eval_to s env exp x
     ==> ?y. enc_y = encode_val y /\ pure_eval_to s env (decode_pos tr exp pos) y`,
  MATCH_MP_TAC position_INDUCT THEN CONJ_TAC THENL
  [REWRITE_TAC[app_pos_def; decode_pos_def; option_INJ] THEN MESON_TAC[];
   ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN X_GEN_TAC `pos:position` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`exp:flat_exp`; `x:flat_v`] THEN
  STRUCT_CASES_TAC(ISPEC `x:flat_v` (CONJUNCT1 (cases "flat_v"))) THEN
  REWRITE_TAC[encode_val_def; decode_pos_def] THENL
  [STRUCT_CASES_TAC(ISPEC `n:num` num_CASES) THEN
   REWRITE_TAC[app_pos_def; FLATPAUX_option_DISTINCT];
   (* Conv *)
   STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP app_pos_Term_IMP) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN
   EXISTS_TAC `EL n (a1:flat_v list)` THEN
   SUBGOAL_THEN `EL n (MAP encode_val a1) = encode_val (EL n a1)`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC EL_MAP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[pure_eval_to_def] THEN MATCH_MP_TAC FLATPAUX_eval_El THEN
   EXISTS_TAC `flat_Conv a0 (a1:flat_v list)` THEN
   ASM_SIMP_TAC[GSYM pure_eval_to_def; FLATPAUX_do_app_El_Conv];
   STRUCT_CASES_TAC(ISPEC `n:num` num_CASES) THEN
   REWRITE_TAC[app_pos_def; FLATPAUX_option_DISTINCT];
   STRUCT_CASES_TAC(ISPEC `n:num` num_CASES) THEN
   REWRITE_TAC[app_pos_def; FLATPAUX_option_DISTINCT];
   (* Loc *)
   STRUCT_CASES_TAC(ISPEC `n:num` num_CASES) THEN
   REWRITE_TAC[app_pos_def; FLATPAUX_option_DISTINCT] THEN
   CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[FLOOKUP_encode_refs] THEN
   COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[FLATPAUX_option_DISTINCT] THEN
   MP_TAC(ISPEC `EL a1 (flat_state_refs (s:(C,FFI)flat_state))`
     (cases "store_v")) THEN
   STRIP_TAC THEN FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[FLATPAUX_option_DISTINCT] THEN
   STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `a:flat_v` THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[pure_eval_to_def] THEN MATCH_MP_TAC FLATPAUX_eval_El THEN
   EXISTS_TAC `flat_Loc a0 a1` THEN
   ASM_REWRITE_TAC[GSYM pure_eval_to_def] THEN
   MATCH_MP_TAC FLATPAUX_do_app_El_Loc THEN
   ASM_REWRITE_TAC[store_lookup_def];
   STRUCT_CASES_TAC(ISPEC `n:num` num_CASES) THEN
   REWRITE_TAC[app_pos_def; FLATPAUX_option_DISTINCT]]);;
let fold_Boolv = GSYM (CONJ (REWRITE_RULE[GSYM bool_to_tag_def] flat_Boolv_def)
                             bool_to_tag_def);;

let flat_patternProof_do_eq_Boolv = prove
 (`flat_do_eq (flat_Boolv x) (flat_Boolv y) = Eq_val (x = y)`,
  MAP_EVERY BOOL_CASES_TAC [`x:bool`; `y:bool`] THEN
  REWRITE_TAC[flat_Boolv_def; flat_do_eq_def; true_tag_def; false_tag_def;
              LENGTH; option_INJ; PAIR_EQ; ARITH_EQ; flat_ctor_same_type_def]);;

let do_if_Boolv = prove
 (`flat_do_if (flat_Boolv x) y z = SOME (if x then y else z)`,
  BOOL_CASES_TAC `x:bool` THEN
  REWRITE_TAC[flat_do_if_def; flat_Boolv_def; injectivity "flat_v"; option_INJ;
              PAIR_EQ; true_tag_def; false_tag_def; ARITH_EQ]);;

let flat_patternProof_evaluate_Bool = prove
 (`flat_evaluate (env:(flat_v)flat_environment) (s:(C,FFI)flat_state)
     [flat_Bool t b] = (s,Rval [flat_Boolv b])`,
  REWRITE_TAC[flat_Bool_def; flat_evaluate_def; REVERSE] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[REVERSE; fold_Boolv]);;

let SmartIf_thm = prove
 (`SmartIf t e p q =
     if ?t. e = flat_Bool t T then p else
     if ?t. e = flat_Bool t F then q else
     flat_If t e p q`,
  REWRITE_TAC[SmartIf_def; flat_Bool_def; bool_to_tag_def] THEN
  STRUCT_CASES_TAC(ISPEC `e:flat_exp` (CONJUNCT1 (cases "flat_exp"))) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "flat_exp"; injectivity "flat_exp"] THEN
  EVERY_CASE_TAC THEN
  ASM_MESON_TAC[true_tag_def; false_tag_def; ARITH_RULE `~(0 = 1)`]);;

let evaluate_SmartIf = prove
 (`flat_evaluate (env:(flat_v)flat_environment) (s:(C,FFI)flat_state)
     [SmartIf t x y z] =
   flat_evaluate env s [flat_If t x y z]`,
  REWRITE_TAC[SmartIf_thm] THEN
  COND_CASES_TAC THENL
  [FIRST_X_ASSUM(X_CHOOSE_THEN `t':tra` SUBST1_TAC) THEN
   ASM_REWRITE_TAC[flat_evaluate_def] THEN
   REWRITE_TAC[flat_patternProof_evaluate_Bool] THEN CASE_REWRITE_TAC[HD] THEN
   REWRITE_TAC[do_if_Boolv] THEN CASE_REWRITE_TAC[];
   ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `t':tra` SUBST1_TAC) THEN
  ASM_REWRITE_TAC[flat_evaluate_def] THEN
  REWRITE_TAC[flat_patternProof_evaluate_Bool] THEN CASE_REWRITE_TAC[HD] THEN
  REWRITE_TAC[do_if_Boolv] THEN CASE_REWRITE_TAC[]);;

let FLATPAUX_EVAL_STEPS_TAC thl =
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC([flat_evaluate_def; REVERSE; APPEND; HD;
    flat_patternProof_evaluate_Bool; distinctness "flat_op";
    injectivity "flat_op"; distinctness "op"; do_if_Boolv] @ thl) THEN
    CASE_REWRITE_TAC[]));;

let decode_guard_simulation = prove
 (`!gd b. dt_eval_guard (encode_refs (s:(C,FFI)flat_state)) (encode_val y) gd =
            SOME b /\
          pure_eval_to s env x y
          ==> pure_eval_to s env (decode_guard tr x gd) (flat_Boolv b)`,
  MATCH_MP_TAC dGuard_INDUCT THEN REPEAT CONJ_TAC THENL
  [(* PosTest *)
   MAP_EVERY X_GEN_TAC [`pos:position`; `test:dTest`; `b:bool`] THEN
   REWRITE_TAC[dt_eval_guard_def; decode_guard_def] THEN
   REWRITE_TAC[case_eq "option"; FLATPAUX_option_DISTINCT] THEN STRIP_TAC THEN
   MP_TAC(SPECL [`pos:position`; `x:flat_exp`; `y:flat_v`]
     (INST [`a:term`,`enc_y:term`] decode_pos_simulation)) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `y':flat_v` STRIP_ASSUME_TAC) THEN
   MP_TAC(INST [`a:term`,`enc_v:term`; `y':flat_v`,`v:flat_v`;
                `decode_pos tr x pos`,`x:flat_exp`] decode_test_simulation) THEN
   ASM_REWRITE_TAC[];
   (* Not *)
   X_GEN_TAC `gd:dGuard` THEN DISCH_TAC THEN X_GEN_TAC `b:bool` THEN
   REWRITE_TAC[dt_eval_guard_def; decode_guard_def] THEN
   REWRITE_TAC[case_eq "option"; FLATPAUX_option_DISTINCT; option_INJ] THEN
   STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `a:bool`) THEN
   ASM_REWRITE_TAC[pure_eval_to_def] THEN DISCH_TAC THEN
   FLATPAUX_EVAL_STEPS_TAC[] THEN
   REWRITE_TAC[flat_do_app_def] THEN
   REPEAT(CHANGED_TAC(REWRITE_TAC[REVERSE; APPEND] THEN CASE_REWRITE_TAC[])) THEN
   REWRITE_TAC[flat_patternProof_do_eq_Boolv] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[list_result_def; PAIR_EQ; injectivity "result"; CONS_11] THEN
   AP_TERM_TAC THEN UNDISCH_TAC `~a <=> b` THEN BOOL_CASES_TAC `a:bool` THEN
   MESON_TAC[];
   (* Conj *)
   X_GEN_TAC `g1:dGuard` THEN X_GEN_TAC `g2:dGuard` THEN STRIP_TAC THEN
   X_GEN_TAC `b:bool` THEN
   REWRITE_TAC[dt_eval_guard_def; decode_guard_def] THEN
   REWRITE_TAC[case_eq "option"; FLATPAUX_option_DISTINCT] THEN STRIP_TAC THEN
   REWRITE_TAC[pure_eval_to_def; evaluate_SmartIf] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `a:bool` o check (fun th ->
     can (find_term ((=) `g1:dGuard`)) (concl th))) THEN
   ASM_REWRITE_TAC[pure_eval_to_def] THEN DISCH_TAC THEN
   FLATPAUX_EVAL_STEPS_TAC[] THEN
   UNDISCH_TAC `(if a then dt_eval_guard (encode_refs (s:(C,FFI)flat_state))
                             (encode_val y) g2 else SOME F) = SOME b` THEN
   BOOL_CASES_TAC `a:bool` THEN
   REWRITE_TAC[option_INJ; flat_patternProof_evaluate_Bool] THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `b:bool`) THEN
    ASM_REWRITE_TAC[pure_eval_to_def];
    DISCH_TAC THEN ASM_REWRITE_TAC[]];
   (* Disj *)
   X_GEN_TAC `g1:dGuard` THEN X_GEN_TAC `g2:dGuard` THEN STRIP_TAC THEN
   X_GEN_TAC `b:bool` THEN
   REWRITE_TAC[dt_eval_guard_def; decode_guard_def] THEN
   REWRITE_TAC[case_eq "option"; FLATPAUX_option_DISTINCT] THEN STRIP_TAC THEN
   REWRITE_TAC[pure_eval_to_def; evaluate_SmartIf] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `a:bool` o check (fun th ->
     can (find_term ((=) `g1:dGuard`)) (concl th))) THEN
   ASM_REWRITE_TAC[pure_eval_to_def] THEN DISCH_TAC THEN
   FLATPAUX_EVAL_STEPS_TAC[] THEN
   UNDISCH_TAC `(if a then SOME T else dt_eval_guard
                   (encode_refs (s:(C,FFI)flat_state)) (encode_val y) g2) = SOME b` THEN
   BOOL_CASES_TAC `a:bool` THEN
   REWRITE_TAC[option_INJ; flat_patternProof_evaluate_Bool] THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `b:bool`) THEN
    ASM_REWRITE_TAC[pure_eval_to_def]];
   (* True *)
   REWRITE_TAC[dt_eval_guard_def; decode_guard_def; option_INJ] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[pure_eval_to_def; flat_patternProof_evaluate_Bool]]);;
let FLATPAUX_simp_conj = prove
 (`!V W a b.
     dt_eval_guard r v V = SOME a /\
     (a ==> dt_eval_guard r v W = SOME b) /\ (~a ==> b = F)
     ==> dt_eval_guard r v
           (if V = pattern_semantics_Not True \/ W = pattern_semantics_Not True
            then pattern_semantics_Not True
            else if V = True then W
            else if W = True then V
            else Conj V W) = SOME b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `V = pattern_semantics_Not True` THENL
  [FIRST_X_ASSUM SUBST_ALL_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[dt_eval_guard_def]) THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN
   REWRITE_TAC[dt_eval_guard_def] THEN CASE_REWRITE_TAC[] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  ASM_CASES_TAC `W = pattern_semantics_Not True` THENL
  [FIRST_X_ASSUM SUBST_ALL_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[dt_eval_guard_def]) THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN
   ASM_REWRITE_TAC[dt_eval_guard_def] THEN CASE_REWRITE_TAC[] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `V = True` THENL
  [FIRST_X_ASSUM SUBST_ALL_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[dt_eval_guard_def; option_INJ]) THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `W = True` THENL
  [FIRST_X_ASSUM SUBST_ALL_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[dt_eval_guard_def; option_INJ]) THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[dt_eval_guard_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `a:bool` THEN ASM_MESON_TAC[]);;

let FLATPAUX_simp_disj = prove
 (`!V W a b.
     dt_eval_guard r v V = SOME a /\
     (~a ==> dt_eval_guard r v W = SOME b) /\ (a ==> b = T)
     ==> dt_eval_guard r v
           (if V = True \/ W = True then True
            else if V = pattern_semantics_Not True then W
            else if W = pattern_semantics_Not True then V
            else Disj V W) = SOME b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `V = True` THENL
  [FIRST_X_ASSUM SUBST_ALL_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[dt_eval_guard_def; option_INJ]) THEN
   REWRITE_TAC[dt_eval_guard_def] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  ASM_CASES_TAC `W = True` THENL
  [FIRST_X_ASSUM SUBST_ALL_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[dt_eval_guard_def; option_INJ]) THEN
   ASM_REWRITE_TAC[dt_eval_guard_def] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `V = pattern_semantics_Not True` THENL
  [FIRST_X_ASSUM SUBST_ALL_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[dt_eval_guard_def]) THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `W = pattern_semantics_Not True` THENL
  [FIRST_X_ASSUM SUBST_ALL_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[dt_eval_guard_def]) THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[dt_eval_guard_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `a:bool` THEN ASM_MESON_TAC[]);;

let FLATPAUX_simp_not = prove
 (CASE_TERM `!V a. dt_eval_guard r v V = SOME a
       ==> dt_eval_guard r v
             (match V with
                pattern_semantics_Not True -> True
              | pattern_semantics_Not w -> w
              | _ -> pattern_semantics_Not V) = SOME (~a)`,
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `V:dGuard` (cases "dGuard")) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[dt_eval_guard_def] THEN
  CASE_REWRITE_TAC[] THEN
  TRY(STRUCT_CASES_TAC(ISPEC `a:dGuard` (cases "dGuard")) THEN
      CASE_REWRITE_TAC[] THEN REWRITE_TAC[dt_eval_guard_def] THEN
      CASE_REWRITE_TAC[]) THEN
  REWRITE_TAC[case_eq "option"; option_INJ; FLATPAUX_option_DISTINCT] THEN
  MESON_TAC[]);;

let simp_guard_thm = prove
 (`!gd x. dt_eval_guard r v gd = SOME x
          ==> dt_eval_guard r v (simp_guard gd) = SOME x`,
  MATCH_MP_TAC simp_guard_ind THEN REPEAT CONJ_TAC THENL
  [(* Conj *)
   MAP_EVERY X_GEN_TAC [`g1:dGuard`; `g2:dGuard`] THEN STRIP_TAC THEN
   X_GEN_TAC `b:bool` THEN
   REWRITE_TAC[simp_guard_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[dt_eval_guard_def; case_eq "option"; FLATPAUX_option_DISTINCT] THEN
   DISCH_THEN(X_CHOOSE_THEN `a:bool` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `dt_eval_guard r v (simp_guard g1) = SOME a` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC FLATPAUX_simp_conj THEN EXISTS_TAC `a:bool` THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     is_cond (lhs (concl th)))) THEN
   ASM_REWRITE_TAC[option_INJ] THENL
   [DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MESON_TAC[]];
   (* Disj *)
   MAP_EVERY X_GEN_TAC [`g1:dGuard`; `g2:dGuard`] THEN STRIP_TAC THEN
   X_GEN_TAC `b:bool` THEN
   REWRITE_TAC[simp_guard_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[dt_eval_guard_def; case_eq "option"; FLATPAUX_option_DISTINCT] THEN
   DISCH_THEN(X_CHOOSE_THEN `a:bool` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `dt_eval_guard r v (simp_guard g1) = SOME a` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC FLATPAUX_simp_disj THEN EXISTS_TAC `a:bool` THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     is_cond (lhs (concl th)))) THEN
   ASM_REWRITE_TAC[option_INJ] THENL
   [DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MESON_TAC[]];
   (* Not *)
   X_GEN_TAC `g:dGuard` THEN DISCH_TAC THEN X_GEN_TAC `b:bool` THEN
   REWRITE_TAC[simp_guard_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[dt_eval_guard_def; case_eq "option"; FLATPAUX_option_DISTINCT;
               option_INJ] THEN
   DISCH_THEN(X_CHOOSE_THEN `a:bool` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC FLATPAUX_simp_not THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   (* PosTest and True *)
   REWRITE_TAC[simp_guard_def];
   REWRITE_TAC[simp_guard_def]]);;
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
  SPEC_TAC(`dtree:dTree`,`dtree:dTree`) THEN MATCH_MP_TAC dTree_INDUCT THEN
  REPEAT CONJ_TAC THENL
  [X_GEN_TAC `k:num` THEN
   REWRITE_TAC[dt_eval_def; decode_dtree_def; option_INJ] THEN
   STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CASE_REWRITE_TAC[];
   REWRITE_TAC[dt_eval_def; decode_dtree_def; option_INJ] THEN
   STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CASE_REWRITE_TAC[];
   REWRITE_TAC[dt_eval_def; FLATPAUX_option_DISTINCT];
   ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`g:dGuard`; `dt1:dTree`; `dt2:dTree`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REWRITE_TAC[dt_eval_def; decode_dtree_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[case_eq "option"; FLATPAUX_option_DISTINCT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `b:bool` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP simp_guard_thm) THEN
  SUBGOAL_THEN (CASE_TERM
   `flat_evaluate (env:(flat_v)flat_environment) (s:(C,FFI)flat_state)
      [if b then decode_dtree tr exps x default_x dt1
       else decode_dtree tr exps x default_x dt2] =
    flat_evaluate env s [match v with
                           MatchSuccess i -> (match lookup i exps with
                                                SOME exp -> exp
                                              | NONE -> default_x)
                         | _ -> default_x]`)
  ASSUME_TAC THENL
  [ASM_CASES_TAC `b:bool` THEN
   FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
     REWRITE_TAC[th] THEN ASSUME_TAC th) THENL
   [REMOVE_THEN "ih1" MATCH_MP_TAC; REMOVE_THEN "ih2" MATCH_MP_TAC] THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_CASES_TAC `simp_guard g = True` THENL
  [ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `b:bool` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `dt_eval_guard (encode_refs (s:(C,FFI)flat_state)) (encode_val y)
                   (simp_guard g) = SOME b` THEN
    ASM_REWRITE_TAC[dt_eval_guard_def; option_INJ];
    ALL_TAC] THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_CASES_TAC `simp_guard g = pattern_semantics_Not True` THENL
  [ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `~b` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `dt_eval_guard (encode_refs (s:(C,FFI)flat_state)) (encode_val y)
                   (simp_guard g) = SOME b` THEN
    ASM_REWRITE_TAC[dt_eval_guard_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[evaluate_SmartIf] THEN
  MP_TAC(SPECL [`simp_guard g`; `b:bool`] decode_guard_simulation) THEN
  ASM_REWRITE_TAC[pure_eval_to_def] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[flat_evaluate_def] THEN CASE_REWRITE_TAC[HD] THEN
  REWRITE_TAC[do_if_Boolv] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let FLATPAUX_mr_distinct =
  CONJ (distinctness "match_result") (GSYM (distinctness "match_result"));;
let FLATPAUX_pmr_distinct =
  CONJ (distinctness "pmatchResult") (GSYM (distinctness "pmatchResult"));;

let FLATPAUX_encode_pat_match = prove
 (`(!(s:(C,FFI)flat_state) pat v bs.
      ~(flat_pmatch s pat v bs = Match_type_error)
      ==> pattern_semantics_pmatch (encode_refs s) (encode_pat pat) (encode_val v) =
          (if flat_pmatch s pat v bs = No_match then PMatchFailure
           else PMatchSuccess)) /\
   (!(s:(C,FFI)flat_state) ps vs bs.
      ~(flat_pmatch_list s ps vs bs = Match_type_error)
      ==> pattern_semantics_pmatch_list (encode_refs s) (MAP encode_pat ps)
            (MAP encode_val vs) =
          (if flat_pmatch_list s ps vs bs = No_match then PMatchFailure
           else PMatchSuccess))`,
  MATCH_MP_TAC flat_pmatch_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_pmatch_def; FLATPAUX_mr_distinct]) THEN
  REWRITE_TAC[flat_pmatch_def; encode_pat_def; encode_val_def; MAP;
              pattern_semantics_pmatch_def; FLATPAUX_mr_distinct] THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  FIRST
   [(* Plit *)
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    ASM_CASES_TAC `l:lit = l'` THEN
    ASM_REWRITE_TAC[lit_same_type_refl; FLATPAUX_mr_distinct] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[FLATPAUX_mr_distinct; FLATPAUX_pmr_distinct] THEN
    NO_TAC;
    (* Pas *)
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    (* Pcon *)
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    ASM_CASES_TAC `pmatch_stamps_ok stmp stmp' (LENGTH (ps:flat_pat list))
                     (LENGTH (vs:flat_v list))` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pmatch_stamps_ok_cases] o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                           "pmatch_stamps_ok" with Failure _ -> false)) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq (concl th) && is_var (lhs (concl th)) &&
      (let n = fst(dest_var(lhs(concl th))) in n = "stmp" || n = "stmp'")))) THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[pattern_semantics_pmatch_def; OPTION_MAP_DEF; option_INJ;
                LENGTH_MAP; is_sibling_def] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[OPTION_MAP_DEF; option_INJ]) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    TRY(COND_CASES_TAC THEN FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) THEN
    ASM_REWRITE_TAC[FLATPAUX_mr_distinct; FLATPAUX_pmr_distinct] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    NO_TAC;
    (* Pref *)
    REWRITE_TAC[FLOOKUP_encode_refs] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[store_lookup_def] THEN
    COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[FLATPAUX_mr_distinct] THEN
    MP_TAC(ISPEC `EL lnum (flat_state_refs (s:(C,FFI)flat_state))` (cases "store_v")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[FLATPAUX_mr_distinct] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o
      REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[store_lookup_def] THEN NO_TAC;
    (* pmatch_list cons *)
    MP_TAC(ISPEC `flat_pmatch (s:(C,FFI)flat_state) p v bindings`
      (cases "match_result")) THEN
    STRIP_TAC THEN FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
      REWRITE_TAC[th]) THEN
    CASE_REWRITE_TAC[] THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FLATPAUX_mr_distinct; FLATPAUX_pmr_distinct;
                                injectivity "match_result"]) THEN
    TRY(FIRST_ASSUM CONTR_TAC) THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
    [MP_TAC(ISPEC `flat_pmatch_list (s:(C,FFI)flat_state) ps vs bindings`
       (cases "match_result")) THEN
     STRIP_TAC THEN FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
       REWRITE_TAC[th]) THEN
     CASE_REWRITE_TAC[] THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[FLATPAUX_mr_distinct; FLATPAUX_pmr_distinct]) THEN
     TRY(FIRST_ASSUM CONTR_TAC) THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
     REWRITE_TAC[FLATPAUX_pmr_distinct];
     FIRST_X_ASSUM(MP_TAC o SPEC `a:(varN#flat_v)list` o check (is_forall o concl)) THEN
     REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

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
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl)) THEN
  FIRST_X_ASSUM(fun th -> FIRST (map (fun c g -> MATCH_ACCEPT_TAC
    (MATCH_MP c th) g) (CONJUNCTS FLATPAUX_encode_pat_match))));;
let FLATPAUX_GEN_PSM_TAC : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
                                  "pattern_semantics_match" with Failure _ -> false) w in
  SPEC_TAC(t, mk_var("r", type_of t)) g;;

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
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC[MAPi_DEF; pattern_semantics_match_def; pmatch_rows_def] THEN
   CASE_REWRITE_TAC[];
   ALL_TAC] THEN
  SPEC_TAC(`h:flat_pat#A`,`h:flat_pat#A`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:flat_pat`; `e:A`; `j_offs:num`] THEN
  SUBGOAL_THEN `(\j (p,x). (encode_pat p, j + j_offs)) o SUC =
                (\j (p:flat_pat,x:A). (encode_pat p, j + SUC j_offs))`
    ASSUME_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM] THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[ADD_CLAUSES];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[MAPi_DEF; pmatch_rows_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[pattern_semantics_match_def] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC j_offs` o check (is_forall o concl)) THEN
  MP_TAC(ISPEC `flat_pmatch (s:(C,FFI)flat_state) p v []` (cases "match_result")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`s:(C,FFI)flat_state`; `p:flat_pat`; `v:flat_v`;
                `[]:(varN#flat_v)list`; `flat_pmatch (s:(C,FFI)flat_state) p v []`]
               (CONJUNCT1 encode_pat_match_simulation)) THEN
  ASM_REWRITE_TAC[FLATPAUX_mr_distinct] THEN DISCH_THEN SUBST1_TAC THEN
  CASE_REWRITE_TAC[] THENL
  [(* No_match *)
   DISCH_THEN(fun ih -> DISCH_TAC THEN MP_TAC(MP ih (ASSUME
     `~(pmatch_rows (t:(flat_pat#A)list) (s:(C,FFI)flat_state) v = Match_type_error)`))) THEN
   FLATPAUX_GEN_PSM_TAC THEN GEN_TAC THEN
   STRUCT_CASES_TAC(ISPEC `r:(matchResult)option` (cases "option")) THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN
   STRUCT_CASES_TAC(ISPEC `a:matchResult` (cases "matchResult")) THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `env:(varN#flat_v)list`
     STRIP_ASSUME_TAC)) THEN
   MAP_EVERY EXISTS_TAC [`SUC i`; `env:(varN#flat_v)list`] THEN
   ASM_REWRITE_TAC[EL; TL; LENGTH; LT_SUC] THEN ARITH_TAC;
   (* Match *)
   MP_TAC(ISPEC `pmatch_rows (t:(flat_pat#A)list) (s:(C,FFI)flat_state) v`
     (cases "match_result")) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[FLATPAUX_mr_distinct] THEN
   FLATPAUX_GEN_PSM_TAC THEN GEN_TAC THEN
   STRUCT_CASES_TAC(ISPEC `r:(matchResult)option` (cases "option")) THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN DISCH_TAC THEN
   MAP_EVERY EXISTS_TAC [`0`; `a:(varN#flat_v)list`] THEN
   ASM_REWRITE_TAC[EL; HD; LENGTH; LT_0; ADD_CLAUSES]]);;

let FLATPAUX_pmatch_status = prove
 (`(!(s:(C,FFI)flat_state) p v bs bs'.
      (flat_pmatch s p v bs = No_match <=> flat_pmatch s p v bs' = No_match) /\
      (flat_pmatch s p v bs = Match_type_error <=>
       flat_pmatch s p v bs' = Match_type_error)) /\
   (!(s:(C,FFI)flat_state) ps vs bs bs'.
      (flat_pmatch_list s ps vs bs = No_match <=>
       flat_pmatch_list s ps vs bs' = No_match) /\
      (flat_pmatch_list s ps vs bs = Match_type_error <=>
       flat_pmatch_list s ps vs bs' = Match_type_error))`,
  MESON_TAC[pmatch_any_no_match; pmatch_any_match_error]);;

let FLATPAUX_eval_Equality_Lit =
  REWRITE_RULE[flat_pattern_decode_test_def] FLATPAUX_decode_test_LitEq;;

let FLATPAUX_MAP_SND_MAPi = prove
 (`!(g:num->flat_exp) (ps:flat_pat list).
     MAP SND (MAPi (\i p. (p, g i)) ps) = MAPi (\i p. g i) ps /\
     MAP FST (MAPi (\i p. (p, g i)) ps) = ps`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_EQ_REWRITE; LENGTH_MAP; LENGTH_MAPi] THEN
  SIMP_TAC[EL_MAP; EL_MAPi; LENGTH_MAPi]);;
let FLATPAUX_case_status = prove
 (CASE_TERM `!(pm:((varN#flat_v)list)match_result) (pl:((varN#flat_v)list)match_result)
    (pl':((varN#flat_v)list)match_result)
    (g:(varN#flat_v)list->((varN#flat_v)list)match_result).
   (pl = Match_type_error <=> pl' = Match_type_error)
   ==> ((match pm with
           No_match -> (match pl with
                          No_match -> No_match
                        | Match_type_error -> Match_type_error
                        | Match a -> No_match)
         | Match_type_error -> Match_type_error
         | Match b -> g b) = No_match <=>
        (match pm with
           No_match -> (match pl' with
                          No_match -> No_match
                        | Match_type_error -> Match_type_error
                        | Match a -> No_match)
         | Match_type_error -> Match_type_error
         | Match b -> g b) = No_match) /\
       ((match pm with
           No_match -> (match pl with
                          No_match -> No_match
                        | Match_type_error -> Match_type_error
                        | Match a -> No_match)
         | Match_type_error -> Match_type_error
         | Match b -> g b) = Match_type_error <=>
        (match pm with
           No_match -> (match pl' with
                          No_match -> No_match
                        | Match_type_error -> Match_type_error
                        | Match a -> No_match)
         | Match_type_error -> Match_type_error
         | Match b -> g b) = Match_type_error)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `pm:((varN#flat_v)list)match_result` (cases "match_result")) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `pl:((varN#flat_v)list)match_result` (cases "match_result")) THEN
  STRUCT_CASES_TAC(ISPEC `pl':((varN#flat_v)list)match_result` (cases "match_result")) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[FLATPAUX_mr_distinct]);;
let FLATPAUX_npm_intro_tac outer =
  MAP_EVERY X_GEN_TAC outer THEN DISCH_THEN(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`vs:flat_v list`; `bindings:(varN#flat_v)list`;
    `exp:flat_exp`; `res:((varN#flat_v)list)match_result`] THEN
  REWRITE_TAC[naive_pattern_match_def; MAP; FLATPAUX_LIST_REL_CONS1] THEN
  STRIP_TAC THEN FLATPAUX_SUBST_VAR_TAC "vs" THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var (rhs (concl th)) &&
    fst(dest_var(rhs(concl th))) = "exp")) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var (rhs (concl th)) &&
    fst(dest_var(rhs(concl th))) = "res"));;

let FLATPAUX_npm_norm_tac =
  RULE_ASSUM_TAC(REWRITE_RULE[flat_pmatch_def]) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FLATPAUX_mr_distinct]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[flat_pmatch_def] THEN CASE_REWRITE_TAC[];;

let FLATPAUX_npm_ih_tac vs bs =
  REMOVE_THEN "ih" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [vs; bs] THEN
  ASM_REWRITE_TAC[];;

let FLATPAUX_npm_cases_v_tac =
  MP_TAC(ISPEC `hv:flat_v` (CONJUNCT1 (cases "flat_v"))) THEN STRIP_TAC THEN
  FLATPAUX_SUBST_VAR_TAC "hv" THEN FLATPAUX_npm_norm_tac;;

let FLATPAUX_IS_NOT_MTE th =
  is_neg (concl th) &&
  (try rand (rand (concl th)) = `Match_type_error:((varN#flat_v)list)match_result`
   with Failure _ -> false);;

(* the evaluation of the arguments of a constructor value *)
let FLATPAUX_npm_args_tac : tactic = fun (asl,w as g) ->
  let pat = `pure_eval_to (s:(C,FFI)flat_state) env (v:flat_exp)
               (flat_Conv X (a1:flat_v list))` in
  let th = snd(find (fun (_,th) -> can (term_match [] pat) (concl th)) asl) in
  let cv = rand(concl th) in
  (REWRITE_TAC[MAP_APPEND; FLATPAUX_MAP_SND_MAPi] THEN
   MATCH_MP_TAC LIST_REL_APPEND_suff THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[LIST_REL_EL_EQN; LENGTH_MAPi] THEN ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_MAPi] THEN
   REWRITE_TAC[pure_eval_to_def] THEN MATCH_MP_TAC FLATPAUX_eval_El THEN
   EXISTS_TAC cv THEN
   ASM_SIMP_TAC[GSYM pure_eval_to_def; FLATPAUX_do_app_El_Conv]) g;;

let FLATPAUX_eval_TagLenEq =
  REWRITE_RULE[flat_pattern_decode_test_def] FLATPAUX_decode_test_TagLenEq;;

let FLATPAUX_npm_nil_tac =
  REPEAT GEN_TAC THEN REWRITE_TAC[naive_pattern_match_def; MAP; LIST_REL_NIL] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  REWRITE_TAC[flat_pmatch_def; FLATPAUX_mr_distinct; pure_eval_to_def;
              flat_patternProof_evaluate_Bool];;

let FLATPAUX_npm_pany_tac =
  FLATPAUX_npm_intro_tac [`t:tra`; `x:flat_exp`; `mats:(flat_pat#flat_exp)list`] THEN
  FLATPAUX_npm_norm_tac THEN
  FLATPAUX_npm_ih_tac `tvs:flat_v list` `bindings:(varN#flat_v)list`;;

let FLATPAUX_npm_pvar_tac =
  FLATPAUX_npm_intro_tac [`t:tra`; `x:varN`; `x':flat_exp`;
    `mats:(flat_pat#flat_exp)list`] THEN
  FLATPAUX_npm_norm_tac THEN
  FLATPAUX_npm_ih_tac `tvs:flat_v list` `CONS (x:varN,hv:flat_v) bindings`;;

let FLATPAUX_npm_plit_tac =
  FLATPAUX_npm_intro_tac [`t:tra`; `l:lit`; `v:flat_exp`;
    `mats:(flat_pat#flat_exp)list`] THEN
  FLATPAUX_npm_cases_v_tac THEN
  (ASM_CASES_TAC `l:lit = a` THENL
  [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[]) THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
   REWRITE_TAC[pure_eval_to_def; evaluate_SmartIf] THEN
   MP_TAC(INST [`v:flat_exp`,`x:flat_exp`; `a:lit`,`l2:lit`; `a:lit`,`l1:lit`;
                `t:tra`,`tr:tra`] FLATPAUX_eval_Equality_Lit) THEN
   ASM_REWRITE_TAC[lit_same_type_refl; pure_eval_to_def] THEN DISCH_TAC THEN
   ASM_REWRITE_TAC[flat_evaluate_def] THEN CASE_REWRITE_TAC[HD] THEN
   REWRITE_TAC[do_if_Boolv] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[GSYM pure_eval_to_def] THEN
   FLATPAUX_npm_ih_tac `tvs:flat_v list` `bindings:(varN#flat_v)list`;
   FIRST_X_ASSUM(MP_TAC o check FLATPAUX_IS_NOT_MTE) THEN
   ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `lit_same_type l a` THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[FLATPAUX_mr_distinct] THEN
   MP_TAC(ISPEC `flat_pmatch_list (s:(C,FFI)flat_state)
     (MAP FST (mats:(flat_pat#flat_exp)list)) tvs bindings` (cases "match_result")) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[FLATPAUX_mr_distinct] THEN
   REWRITE_TAC[pure_eval_to_def; evaluate_SmartIf] THEN
   MP_TAC(INST [`v:flat_exp`,`x:flat_exp`; `a:lit`,`l2:lit`; `l:lit`,`l1:lit`;
                `t:tra`,`tr:tra`] FLATPAUX_eval_Equality_Lit) THEN
   ASM_REWRITE_TAC[pure_eval_to_def] THEN DISCH_TAC THEN
   ASM_REWRITE_TAC[flat_evaluate_def] THEN CASE_REWRITE_TAC[HD] THEN
   REWRITE_TAC[do_if_Boolv] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[flat_patternProof_evaluate_Bool]]);;

let FLATPAUX_npm_pcon_none_tac =
  FLATPAUX_npm_intro_tac [`t:tra`; `ps:flat_pat list`; `v:flat_exp`;
    `mats:(flat_pat#flat_exp)list`] THEN
  FLATPAUX_npm_cases_v_tac THEN
  FIRST_X_ASSUM(MP_TAC o check FLATPAUX_IS_NOT_MTE) THEN
  ASM_CASES_TAC `pmatch_stamps_ok NONE a0 (LENGTH (ps:flat_pat list))
                   (LENGTH (a1:flat_v list))` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[FLATPAUX_mr_distinct] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pmatch_stamps_ok_cases;
    FLATPAUX_option_DISTINCT] o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "pmatch_stamps_ok"
      with Failure _ -> false)) THEN
  FLATPAUX_SUBST_VAR_TAC "a0" THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
  DISCH_TAC THEN
  FLATPAUX_npm_ih_tac `APPEND (a1:flat_v list) tvs` `bindings:(varN#flat_v)list` THEN
  CONJ_TAC THENL [FLATPAUX_npm_args_tac; ALL_TAC] THEN
  REWRITE_TAC[MAP_APPEND; FLATPAUX_MAP_SND_MAPi] THEN
  ASM_SIMP_TAC[flat_pmatch_list_append];;

let FLATPAUX_npm_pas_tac =
  FLATPAUX_npm_intro_tac [`t:tra`; `p:flat_pat`; `nm:varN`; `v:flat_exp`;
    `mats:(flat_pat#flat_exp)list`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_pmatch_def]) THEN REWRITE_TAC[flat_pmatch_def] THEN
  MP_TAC(CONJUNCT2 (SPECL [`s:(C,FFI)flat_state`;
    `MAP FST (mats:(flat_pat#flat_exp)list)`; `tvs:flat_v list`;
    `bindings:(varN#flat_v)list`; `CONS (nm:varN,hv:flat_v) bindings`]
    (CONJUNCT2 FLATPAUX_pmatch_status))) THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP FLATPAUX_case_status th)) THEN
  DISCH_THEN(MP_TAC o SPECL
    [`flat_pmatch (s:(C,FFI)flat_state) p hv (CONS (nm:varN,hv:flat_v) bindings)`;
     `flat_pmatch_list (s:(C,FFI)flat_state) (MAP FST (mats:(flat_pat#flat_exp)list)) tvs`]) THEN
  BETA_TAC THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN
  REMOVE_THEN "ih" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`CONS (hv:flat_v) tvs`; `CONS (nm:varN,hv:flat_v) bindings`] THEN
  ASM_REWRITE_TAC[MAP; ALL2; flat_pmatch_def];;

let FLATPAUX_npm_pcon_some_tac =
  FLATPAUX_npm_intro_tac [`t:tra`; `stmp:ctor_id#type_group_id`; `ps:flat_pat list`;
    `v:flat_exp`; `mats:(flat_pat#flat_exp)list`] THEN
  FLATPAUX_npm_cases_v_tac THEN
  FIRST_X_ASSUM(MP_TAC o check FLATPAUX_IS_NOT_MTE) THEN
  ASM_CASES_TAC `pmatch_stamps_ok (SOME (stmp:ctor_id#type_group_id)) a0
                   (LENGTH (ps:flat_pat list)) (LENGTH (a1:flat_v list))` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[FLATPAUX_mr_distinct] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pmatch_stamps_ok_cases; option_INJ;
    FLATPAUX_option_DISTINCT] o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "pmatch_stamps_ok"
      with Failure _ -> false)) THEN
  FLATPAUX_SUBST_VAR_TAC "stmp" THEN FLATPAUX_SUBST_VAR_TAC "a0" THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN DISCH_TAC THEN
  REWRITE_TAC[pure_eval_to_def; evaluate_SmartIf] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (INST [`cn:num`,`t:num`;
      `LENGTH (ps:flat_pat list)`,`l:num`; `t:tra`,`tr:tra`]
      FLATPAUX_eval_TagLenEq) o check (fun th ->
    can (term_match [] `pure_eval_to (s:(C,FFI)flat_state) env (v:flat_exp)
                          (flat_Conv X (a1:flat_v list))`) (concl th))) THEN
  REWRITE_TAC[pure_eval_to_def] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[HD] THEN REWRITE_TAC[do_if_Boolv] THEN CASE_REWRITE_TAC[] THEN
  (ASM_CASES_TAC `(cn:num) = cn' /\ LENGTH (ps:flat_pat list) = LENGTH (a1:flat_v list)` THEN
  ASM_REWRITE_TAC[] THENL
  [FIRST_X_ASSUM(MP_TAC o check FLATPAUX_IS_NOT_MTE) THEN ASM_REWRITE_TAC[] THEN
   DISCH_TAC THEN REWRITE_TAC[GSYM pure_eval_to_def] THEN
   FLATPAUX_npm_ih_tac `APPEND (a1:flat_v list) tvs` `bindings:(varN#flat_v)list` THEN
   CONJ_TAC THENL [FLATPAUX_npm_args_tac; ALL_TAC] THEN
   REWRITE_TAC[MAP_APPEND; FLATPAUX_MAP_SND_MAPi] THEN
   ASM_SIMP_TAC[flat_pmatch_list_append];
   FIRST_X_ASSUM(MP_TAC o check FLATPAUX_IS_NOT_MTE) THEN ASM_REWRITE_TAC[] THEN
   CASE_REWRITE_TAC[] THEN
   MP_TAC(ISPEC `flat_pmatch_list (s:(C,FFI)flat_state)
      (MAP FST (mats:(flat_pat#flat_exp)list)) tvs bindings` (cases "match_result")) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[FLATPAUX_mr_distinct; flat_patternProof_evaluate_Bool]]);;

let FLATPAUX_npm_pref_tac =
  FLATPAUX_npm_intro_tac [`t:tra`; `p:flat_pat`; `v:flat_exp`;
    `mats:(flat_pat#flat_exp)list`] THEN
  FLATPAUX_npm_cases_v_tac THEN
  FIRST_X_ASSUM(MP_TAC o check FLATPAUX_IS_NOT_MTE) THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th])
    (X_CHOOSE_THEN `sv:(flat_v)store_v` (fun th -> REWRITE_TAC[th] THEN
       ASSUME_TAC th))
    (ISPEC `store_lookup a1 (flat_state_refs (s:(C,FFI)flat_state))`
       (cases "option")) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[FLATPAUX_mr_distinct] THEN
  UNDISCH_TAC `store_lookup a1 (flat_state_refs (s:(C,FFI)flat_state)) = SOME sv` THEN
  STRUCT_CASES_TAC(ISPEC `sv:(flat_v)store_v` (cases "store_v")) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[FLATPAUX_mr_distinct] THEN
  REPEAT DISCH_TAC THEN
  FLATPAUX_npm_ih_tac `CONS (a:flat_v) tvs` `bindings:(varN#flat_v)list` THEN
  REWRITE_TAC[MAP; ALL2; flat_pmatch_def] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[pure_eval_to_def] THEN MATCH_MP_TAC FLATPAUX_eval_El THEN
  EXISTS_TAC `flat_Loc a0 a1` THEN
  ASM_REWRITE_TAC[GSYM pure_eval_to_def] THEN
  MATCH_MP_TAC FLATPAUX_do_app_El_Loc THEN ASM_REWRITE_TAC[];;

let naive_pattern_match_correct = prove
 (`!t mats vs bindings exp res.
     ALL2 (pure_eval_to (s:(C,FFI)flat_state) env) (MAP SND mats) vs /\
     flat_pmatch_list s (MAP FST mats) vs bindings = res /\
     ~(res = Match_type_error) /\
     naive_pattern_match t mats = exp
     ==> pure_eval_to s env exp (flat_Boolv (~(res = No_match)))`,
  MATCH_MP_TAC naive_pattern_match_ind THEN REPEAT CONJ_TAC THENL
  [FLATPAUX_npm_nil_tac; FLATPAUX_npm_pany_tac; FLATPAUX_npm_pvar_tac;
   FLATPAUX_npm_plit_tac; FLATPAUX_npm_pcon_none_tac; FLATPAUX_npm_pas_tac;
   FLATPAUX_npm_pcon_some_tac; FLATPAUX_npm_pref_tac]);;
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
  MATCH_MP_TAC naive_pattern_matches_ind THEN CONJ_TAC THENL
  [REWRITE_TAC[naive_pattern_matches_def; pmatch_rows_def] THEN
   REPEAT STRIP_TAC THEN
   REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
   CASE_REWRITE_TAC[];
   ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:tra`; `x:flat_exp`; `p:flat_pat`; `x':flat_exp`;
    `ps:(flat_pat#flat_exp)list`; `dflt:flat_exp`] THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`exp:flat_exp`; `v:flat_v`;
    `res:((varN#flat_v)list#flat_pat#flat_exp)match_result`] THEN
  REWRITE_TAC[naive_pattern_matches_def; pmatch_rows_def] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  REWRITE_TAC[evaluate_SmartIf] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  MP_TAC(ISPEC `flat_pmatch (s:(C,FFI)flat_state) p v []` (cases "match_result")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[FLATPAUX_mr_distinct] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`naive_pattern_match t [p:flat_pat,x:flat_exp]`;
                `flat_pmatch_list (s:(C,FFI)flat_state) [p] [v] []`]
    (REWRITE_RULE[MAP; ALL2; pure_eval_to_def] (SPECL [`t:tra`; `[p:flat_pat,x:flat_exp]`;
      `[v:flat_v]`; `[]:(varN#flat_v)list`] naive_pattern_match_correct))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pure_eval_to_def]) THEN
  ASM_REWRITE_TAC[flat_pmatch_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[FLATPAUX_mr_distinct] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[HD] THEN REWRITE_TAC[do_if_Boolv] THEN CASE_REWRITE_TAC[] THENL
  [REMOVE_THEN "ih" MATCH_MP_TAC THEN EXISTS_TAC `v:flat_v` THEN
   ASM_REWRITE_TAC[pure_eval_to_def];
   FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
   MP_TAC(ISPEC `pmatch_rows (ps:(flat_pat#flat_exp)list) (s:(C,FFI)flat_state) v`
     (cases "match_result")) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[FLATPAUX_mr_distinct]]);;

let pmatch_rows_same_FST = prove
 (CASE_TERM `!(pats:(flat_pat#A)list) (pats2:(flat_pat#B)list).
     MAP FST pats = MAP FST pats2
     ==> (match pmatch_rows pats (s:(C,FFI)flat_state) v with
            Match_type_error -> pmatch_rows pats2 s v = Match_type_error
          | No_match -> pmatch_rows pats2 s v = No_match
          | Match (env,p,e) ->
              ?i. i < LENGTH pats2 /\ EL i pats = (p,e) /\
                  pmatch_rows pats2 s v = Match (env,EL i pats2))`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; NOT_CONS_NIL; GSYM NOT_CONS_NIL; CONS_11; pmatch_rows_def] THEN
  CASE_REWRITE_TAC[] THEN
  SPEC_TAC(`h:flat_pat#A`,`h:flat_pat#A`) THEN
  SPEC_TAC(`h':flat_pat#B`,`h':flat_pat#B`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`p2:flat_pat`; `e2:B`; `p:flat_pat`; `e:A`] THEN
  STRIP_TAC THEN FLATPAUX_SUBST_VAR_TAC "p" THEN
  REWRITE_TAC[pmatch_rows_def] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t':(flat_pat#B)list`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `flat_pmatch (s:(C,FFI)flat_state) p2 v []` (cases "match_result")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `pmatch_rows (t:(flat_pat#A)list) (s:(C,FFI)flat_state) v`
    (cases "match_result")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[FLATPAUX_mr_distinct] THEN
  TRY(DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
      EXISTS_TAC `0` THEN REWRITE_TAC[EL; HD; LENGTH; LT_0] THEN NO_TAC) THEN
  REPEAT IL1AUX_PAIRARG_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  FIRST [EXISTS_TAC `SUC i` THEN ASM_REWRITE_TAC[EL; TL; LENGTH; LT_SUC] THEN NO_TAC;
         ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
         EXISTS_TAC `0` THEN ASM_REWRITE_TAC[EL; HD; LENGTH; LT_0]]);;

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
  STRIP_TAC THEN REWRITE_TAC[compile_pats_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN COND_CASES_TAC THENL
  [MP_TAC(ISPECL [`pats:(flat_pat#flat_exp)list`;
     `ZIP (MAP FST (pats:(flat_pat#flat_exp)list))
          (MAP (compile_pat_rhs t N exp) pats)`] pmatch_rows_same_FST) THEN
   ANTS_TAC THENL [SIMP_TAC[MAP_ZIP; LENGTH_MAP]; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
   MP_TAC(ISPEC `pmatch_rows (pats:(flat_pat#flat_exp)list) (s:(C,FFI)flat_state) v`
     (cases "match_result")) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[FLATPAUX_mr_distinct] THEN
   REPEAT IL1AUX_PAIRARG_TAC THEN
   REPEAT STRIP_TAC THEN
   MP_TAC(SPECL [`t:tra`; `exp:flat_exp`;
     `ZIP (MAP FST (pats:(flat_pat#flat_exp)list))
          (MAP (compile_pat_rhs t N exp) pats)`; `default_x:flat_exp`;
     `naive_pattern_matches t exp (ZIP (MAP FST (pats:(flat_pat#flat_exp)list))
          (MAP (compile_pat_rhs t N exp) pats)) default_x`; `v:flat_v`;
     `pmatch_rows (ZIP (MAP FST (pats:(flat_pat#flat_exp)list))
          (MAP (compile_pat_rhs t N exp) pats)) (s:(C,FFI)flat_state) v`]
     naive_pattern_matches_correct) THEN
   ASM_REWRITE_TAC[FLATPAUX_mr_distinct] THEN DISCH_THEN SUBST1_TAC THEN
   CASE_REWRITE_TAC[] THEN
   SUBGOAL_THEN `i < LENGTH (pats:(flat_pat#flat_exp)list)` ASSUME_TAC THENL
   [UNDISCH_TAC `i < LENGTH (ZIP (MAP FST (pats:(flat_pat#flat_exp)list))
                    (MAP (compile_pat_rhs t N exp) pats))` THEN
    SIMP_TAC[LENGTH_ZIP; LENGTH_MAP];
    ALL_TAC] THEN
   ASM_SIMP_TAC[EL_ZIP; LENGTH_MAP; EL_MAP] THEN CASE_REWRITE_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`pats:(flat_pat#flat_exp)list`; `0`] pmatch_rows_encode) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  MP_TAC(ISPEC `pattern_semantics_match (encode_refs (s:(C,FFI)flat_state))
      (MAPi (\j (p,q). (encode_pat p,j)) (pats:(flat_pat#flat_exp)list))
      (encode_val v)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP flat_patternProof_comp_thm) THEN
  MP_TAC(INST [`v:flat_v`,`y:flat_v`;
    `pattern_comp_comp (MAPi (\j (p,q). (encode_pat p,j))
       (pats:(flat_pat#flat_exp)list))`,`dtree:dTree`;
    `a:matchResult`,`v:matchResult`; `exp:flat_exp`,`x:flat_exp`; `t:tra`,`tr:tra`;
    `fromList (MAP (compile_pat_rhs t N exp) (pats:(flat_pat#flat_exp)list))`,
    `exps:(flat_exp)spt`] decode_dtree_simulation) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  STRUCT_CASES_TAC(ISPEC `a:matchResult` (cases "matchResult")) THEN
  CASE_REWRITE_TAC[] THENL
  [DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `env':(varN#flat_v)list`
     STRIP_ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[lookup_fromList; LENGTH_MAP] THEN CASE_REWRITE_TAC[] THEN
   ASM_SIMP_TAC[EL_MAP] THEN
   MP_TAC(ISPEC `EL i (pats:(flat_pat#flat_exp)list)` PAIR_SURJECTIVE) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
   DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]]);;

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
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC[flat_pattern_compile_exp_def; PAIR_EQ; pmatch_rows_def] THEN
   REPEAT STRIP_TAC THEN
   REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
   CASE_REWRITE_TAC[pmatch_rows_def];
   ALL_TAC] THEN
  SPEC_TAC(`h:flat_pat#flat_exp`,`h:flat_pat#flat_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:flat_pat`; `x:flat_exp`; `k:num`; `sg:bool`;
    `pats2:(flat_pat#flat_exp)list`; `res:((varN#flat_v)list#flat_pat#flat_exp)match_result`] THEN
  REWRITE_TAC[flat_pattern_compile_exp_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT IL1AUX_PAIRARG_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl) o check (fun th ->
    can (find_term ((=) `pats2:(flat_pat#flat_exp)list`)) (concl th))) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  REWRITE_TAC[pmatch_rows_def] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k':num`; `sgp':bool`;
    `ps2':(flat_pat#flat_exp)list`;
    `pmatch_rows (t':(flat_pat#flat_exp)list) (s:(C,FFI)flat_state) v`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
  [FIRST_ASSUM(MP_TAC o check (fun th ->
     try fst(dest_const(fst(strip_comb(lhand(concl th))))) = "MAX"
     with Failure _ -> false)) THEN
   REWRITE_TAC[MAX] THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC;
   DISCH_TAC] THEN
  ASM_CASES_TAC `flat_pmatch (s:(C,FFI)flat_state) p v [] = Match_type_error` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`s:(C,FFI)flat_state`; `p:flat_pat`; `v:flat_v`;
    `[]:(varN#flat_v)list`; `flat_pmatch (s:(C,FFI)flat_state) p v []`;
    `t:(C,FFI)flat_state`; `v':flat_v`; `[]:(varN#flat_v)list`]
    (INST [`s_cfg:flat_pattern_config`,`cfg:flat_pattern_config`]
       (CONJUNCT1 pmatch_thm))) THEN
  ASM_REWRITE_TAC[ALOOKUP_rel_empty; UNWIND_THM1] THEN
  DISCH_THEN(MP_TAC o MATCH_MP match_rel_IMP) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "flat_pmatch"
     with Failure _ -> false)))) THEN
  CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_case_app (concl th))) THEN
  MP_TAC(ISPEC `pmatch_rows (t':(flat_pat#flat_exp)list) (s:(C,FFI)flat_state) v`
    (cases "match_result")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REPEAT IL1AUX_PAIRARG_TAC THEN
  TRY(DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN NO_TAC) THEN
  FIRST
   [DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `envx:(varN#flat_v)list`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`SUC i`; `envx:(varN#flat_v)list`] THEN
    ASM_REWRITE_TAC[EL; TL; LENGTH; LT_SUC] THEN NO_TAC;
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`0`; `env2:(varN#flat_v)list`] THEN
    ASM_REWRITE_TAC[EL; HD; LENGTH; LT_0] THEN NO_TAC;
    DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `envx:(varN#flat_v)list`
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`0`; `env2:(varN#flat_v)list`] THEN
    ASM_REWRITE_TAC[EL; HD; LENGTH; LT_0]]);;

let compile_match_EL = prove
 (`!pats pats2 k sg i.
     compile_match cfg pats = (k,sg,pats2) /\ i < LENGTH pats /\
     EL i pats = (pat,exp)
     ==> ?exp_i sg exp'. flat_pattern_compile_exp cfg exp = (exp_i,sg,exp') /\
                         EL i pats2 = (pat,exp') /\ exp_i <= k /\
                         max_dec_name (flat_pat_bindings pat) <= k`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  SPEC_TAC(`h:flat_pat#flat_exp`,`h:flat_pat#flat_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:flat_pat`; `x:flat_exp`; `pats2:(flat_pat#flat_exp)list`;
    `k:num`; `sg:bool`] THEN
  REWRITE_TAC[flat_pattern_compile_exp_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT IL1AUX_PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; LT_SUC; LT_0; PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THENL
  [REWRITE_TAC[EL; HD] THEN MAP_EVERY EXISTS_TAC [`i':num`; `sgx':bool`; `y':flat_exp`] THEN
   ASM_REWRITE_TAC[] THEN ARITH_TAC;
   FIRST_X_ASSUM(MP_TAC o SPECL [`ps2':(flat_pat#flat_exp)list`; `k':num`;
     `sgp':bool`; `i:num`]) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   MAP_EVERY EXISTS_TAC [`exp_i:num`; `sg':bool`; `exp':flat_exp`] THEN
   ASM_REWRITE_TAC[EL; TL] THEN ASM_ARITH_TAC]);;

let FLATPAUX_ALOOKUP_rel_eq_trans = prove
 (`!(P:A->bool) (R:B->C->bool) xs ys zs.
     ALOOKUP_rel P R xs ys /\ ALOOKUP_rel P (=) zs ys ==> ALOOKUP_rel P R xs zs`,
  REWRITE_TAC[ALOOKUP_rel_def; OPTREL_eq] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ALOOKUP (zs:(A#C)list) x = ALOOKUP (ys:(A#C)list) x`
    SUBST1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

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
  REWRITE_TAC[compile_pat_rhs_def; max_dec_name_LESS_EVERY] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `compile_pat_bindings tr (N + 1)
      [p,N,Var_local tr (enc_num_to_name N)] exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `spt:num_set` (X_CHOOSE_THEN `exp2:flat_exp`
    ASSUME_TAC)) THEN
  FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  MP_TAC(SPECL [`tr:tra`; `N + 1`; `[p:flat_pat,N:num,Var_local tr (enc_num_to_name N)]`;
    `exp:flat_exp`; `exp2:flat_exp`; `spt:num_set`; `s:(C,FFI)flat_state`;
    `[v:flat_v]`; `[]:(varN#flat_v)list`; `bindings:(varN#flat_v)list`;
    `flat_environment_v_fupd f (env3:(flat_v)flat_environment)`;
    `t:(C,FFI)flat_state`; `res:(flat_v list,flat_v)result`]
    (INST [`N - 1`,`j:num`; `flat_environment_v (env2:(flat_v)flat_environment)`,
           `base_vs:(varN#flat_v)list`] compile_pat_bindings_simulation)) THEN
  ASM_REWRITE_TAC[MAP; ALL2; ALL; APPEND; flat_pmatch_def] THEN
  CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[flat_environment_INFO.ri_accfupds] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(((\k. k < N - 1) o dec_name_to_num) (enc_num_to_name N))`
    ASSUME_TAC THENL [REWRITE_TAC[o_THM; dec_enc] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((\k. k > N - 1 /\ k < N + 1) o dec_name_to_num) (enc_num_to_name N)`
    ASSUME_TAC THENL
  [REWRITE_TAC[o_THM; dec_enc] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THENL
   [X_GEN_TAC `env2':(flat_v)flat_environment` THEN STRIP_TAC THEN
    REWRITE_TAC[pure_eval_to_def; flat_evaluate_def] THEN
    FIRST_X_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
      MP_TAC(MATCH_MP ALOOKUP_rel_EQ_ALOOKUP (CONJ th th2)))) THEN
    REWRITE_TAC[ALOOKUP_THM] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[];
    ARITH_TAC;
    REWRITE_TAC[MATCH_MP (CONJUNCT1 ALOOKUP_rel_cons_false)
      (ASSUME `~(((\k. k < N - 1) o dec_name_to_num) (enc_num_to_name N))`)] THEN
    MATCH_MP_TAC ALOOKUP_rel_refl THEN REWRITE_TAC[];
    ASM_ARITH_TAC;
    ARITH_TAC];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ext:(flat_v)flat_environment` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ext:(flat_v)flat_environment` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FLATPAUX_env_rel_def; flat_environment_INFO.ri_accfupds; K_THM] THEN
  MATCH_MP_TAC FLATPAUX_ALOOKUP_rel_eq_trans THEN
  EXISTS_TAC `APPEND bindings (flat_environment_v (env2:(flat_v)flat_environment))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ALOOKUP_rel_append_suff THEN CONJ_TAC THEN
   MATCH_MP_TAC(GEN_ALL ALOOKUP_rel_mono) THEN
   EXISTS_TAC `\x. dec_name_to_num x < M` THEN
   EXISTS_TAC `flat_patternProof_v_rel` THEN
   ASM_REWRITE_TAC[GSYM FLATPAUX_env_rel_def] THEN REPEAT STRIP_TAC THEN
   ASM_ARITH_TAC;
   UNDISCH_TAC `ALOOKUP_rel ((\k. k < N - 1) o dec_name_to_num) (=)
     (flat_environment_v (ext:(flat_v)flat_environment))
     (APPEND bindings (flat_environment_v (env2:(flat_v)flat_environment)))` THEN
   REWRITE_TAC[o_DEF]]);;

let flat_patternProof_state_rel_dec_clock = prove
 (`flat_patternProof_state_rel cfg (s1:(C,FFI)flat_state) s2
   ==> flat_patternProof_state_rel cfg (flat_dec_clock s1) (flat_dec_clock s2)`,
  SIMP_TAC[flat_patternProof_state_rel_def; flat_dec_clock_def;
           flat_state_INFO.ri_accfupds; K_THM]);;

let OPTION_ALL_FORALL = prove
 (`OPTION_ALL (P:A->bool) x <=> (!y. x = SOME y ==> P y)`,
  STRUCT_CASES_TAC(ISPEC `x:A option` (cases "option")) THEN
  REWRITE_TAC[OPTION_ALL_def; FLATPAUX_option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

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
  REWRITE_TAC[flat_patternProof_state_rel_def; install_conf_rel_def] THEN
  REWRITE_TAC[flat_do_eval_def] THEN STRIP_TAC THEN FLATSEMAUX_SPLIT_TAC THEN
  GVS[FLATPAUX_LIST_REL_CONS1; LIST_REL_NIL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pure_cc_def; LET_DEF; LET_END_DEF]) THEN
  RULE_ASSUM_TAC BETA_RULE THEN
  MP_TAC(MATCH_MP flat_simple_val_rel_v_to_bytes flat_patternProof_simple_val_rel) THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
    ASSUME_TAC(MATCH_MP th (CONJ th1 th2))))) THEN
  MP_TAC(MATCH_MP flat_simple_val_rel_v_to_words flat_patternProof_simple_val_rel) THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
    ASSUME_TAC(MATCH_MP th (CONJ th1 th2))))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[pure_co_def; PAIR_MAP_THM; I_THM] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(MAP (compile_dec cfg) decs = []) /\
    FST (shift_seq 1 ((I ## MAP (compile_dec cfg)) o
      install_config_compile_oracle (flat_state_eval_config (s:(C,FFI)flat_state))) 0) =
    FST (shift_seq 1 (install_config_compile_oracle (flat_state_eval_config s)) 0)`
    (fun th -> REWRITE_TAC[th]) THENL
  [ASM_REWRITE_TAC[MAP_EQ_NIL; shift_seq_def; o_THM] THEN
   MP_TAC(ISPEC `install_config_compile_oracle (flat_state_eval_config
     (s:(C,FFI)flat_state)) (0 + 1)` PAIR_SURJECTIVE) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM];
   ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Unitv`; `install_config_compile_oracle_fupd
    (K (shift_seq 1 ((I ## MAP (compile_dec cfg)) o
      install_config_compile_oracle (flat_state_eval_config (s:(C,FFI)flat_state)))))
    (flat_state_eval_config (t:(C,FFI)flat_state))`] THEN
  REWRITE_TAC[install_config_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[FUN_EQ_THM; shift_seq_def; o_THM] THEN
  REWRITE_TAC[flat_Unitv_def; v_rel_l_cases; LIST_REL_NIL] THEN MESON_TAC[]);;


let FLATPAUX_evaluate_decs_clauses =
  filter (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl(SPEC_ALL th)))))) =
                        "flat_evaluate_decs" with Failure _ -> false)
         (CONJUNCTS flat_evaluate_def);;

let flat_patternProof_evaluate_decs_sing = prove
 (`flat_evaluate_decs (s:(C,FFI)flat_state) [d] = evaluate_dec s d`,
  REWRITE_TAC FLATPAUX_evaluate_decs_clauses THEN
  MP_TAC(ISPEC `evaluate_dec (s:(C,FFI)flat_state) d` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `y:((flat_v)error_result)option` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC FLATPAUX_evaluate_decs_clauses);;

(* ------------------------------------------------------------------------- *)
(* compile_exps_evaluate                                                      *)
(* ------------------------------------------------------------------------- *)

(* compile_exps_evaluate: the induction predicates and one lemma per case *)
(* of flat_evaluate_ind                                                     *)

let FLATPAUX_ce_P_exp =
 `\env1 (s1:(C,FFI)flat_state) xs.
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

let FLATPAUX_ce_P_dec =
 `\(s1:(C,FFI)flat_state) d.
    !t1 res s2 cfg.
      evaluate_dec s1 d = (t1,res) /\
      flat_patternProof_state_rel s_cfg s1 s2 /\
      ~(res = SOME (Rabort Rtype_error))
      ==> ?t2 res'. evaluate_dec s2 (compile_dec cfg d) = (t2,res') /\
                    OPTREL (exc_rel flat_patternProof_v_rel) res res' /\
                    flat_patternProof_state_rel s_cfg t1 t2`;;

let FLATPAUX_ce_P_decs =
 `\(s1:(C,FFI)flat_state) decs.
    !t1 res s2 cfg decs'.
      flat_evaluate_decs s1 decs = (t1,res) /\
      decs' = MAP (compile_dec cfg) decs /\
      flat_patternProof_state_rel s_cfg s1 s2 /\
      ~(res = SOME (Rabort Rtype_error))
      ==> ?t2 res'. flat_evaluate_decs s2 decs' = (t2,res') /\
                    OPTREL (exc_rel flat_patternProof_v_rel) res res' /\
                    flat_patternProof_state_rel s_cfg t1 t2`;;

let FLATPAUX_ce_ind =
  CONV_RULE (DEPTH_CONV BETA_CONV)
    (ISPECL [FLATPAUX_ce_P_exp; FLATPAUX_ce_P_dec; FLATPAUX_ce_P_decs]
       flat_evaluate_ind);;

let FLATPAUX_ce_cases = conjuncts (lhand (concl FLATPAUX_ce_ind));;

let FLATPAUX_ce_tm k = el k FLATPAUX_ce_cases;;

let FLATPAUX_ce_nil = prove
 (FLATPAUX_ce_tm 0,
  REWRITE_TAC[flat_evaluate_def; flat_pattern_compile_exp_def; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  MAP_EVERY EXISTS_TAC [`s2:(C,FFI)flat_state`; `Rval []:(flat_v list,flat_v)result`] THEN
  ASM_REWRITE_TAC[result_rel_def; ALL2; flat_evaluate_def]);;


let FLATPAUX_ce_intro_tac =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[flat_pattern_compile_exp_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT IL1AUX_PAIRARG_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var (rhs (concl th)) &&
    mem (fst(dest_var(rhs(concl th)))) ["i"; "sg"; "ys"])));;

let FLATPAUX_SPLIT_ASM_TAC =
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;

let FLATPAUX_ce_lit = prove
 (FLATPAUX_ce_tm 2,
  FLATPAUX_ce_intro_tac THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_evaluate_def; PAIR_EQ]) THEN
  FLATPAUX_SPLIT_ASM_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  MAP_EVERY EXISTS_TAC [`s2:(C,FFI)flat_state`;
    `Rval [flat_Litv l]:(flat_v list,flat_v)result`] THEN
  ASM_REWRITE_TAC[result_rel_def; ALL2; flat_evaluate_def; v_rel_l_cases]);;

let FLATPAUX_ce_var = prove
 (FLATPAUX_ce_tm 7,
  FLATPAUX_ce_intro_tac THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_evaluate_def; PAIR_EQ]) THEN
  FLATPAUX_SPLIT_ASM_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  REWRITE_TAC[flat_evaluate_def; PAIR_EQ] THEN
  SUBGOAL_THEN `dec_name_to_num n < N` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(
     lhand(concl th))))) = "MAX" with Failure _ -> false)) THEN
   REWRITE_TAC[MAX] THEN ARITH_TAC;
   ALL_TAC] THEN
  FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
    MP_TAC(MATCH_MP env_rel_ALOOKUP (CONJ th th2)))) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  MP_TAC(ISPEC `ALOOKUP (flat_environment_v (env:(flat_v)flat_environment)) (n:varN)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[OPTREL_DEF; FLATPAUX_option_DISTINCT; option_INJ] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:flat_v` (X_CHOOSE_THEN `w:flat_v`
    STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`s2:(C,FFI)flat_state`;
    `Rval [w]:(flat_v list,flat_v)result`] THEN
  ASM_REWRITE_TAC[result_rel_def; ALL2]);;

let FLATPAUX_MAX_ASM_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(
    lhand(concl th))))) = "MAX" with Failure _ -> false)) THEN
  REWRITE_TAC[MAX] THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC;;

let FLATPAUX_EXISTS_EQ_TAC : tactic = fun (asl,w as g) ->
  let vs,body = strip_exists w in
  let v = hd vs in
  let find_wit c =
    let l,r = dest_eq c in
    if l = v && not (free_in v r) then r
    else if r = v && not (free_in v l) then l else failwith "wit" in
  EXISTS_TAC (tryfind find_wit (conjuncts body)) g;;

let FLATPAUX_ce_fun = prove
 (FLATPAUX_ce_tm 8,
  FLATPAUX_ce_intro_tac THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_evaluate_def; PAIR_EQ]) THEN
  FLATPAUX_SPLIT_ASM_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  REWRITE_TAC[flat_evaluate_def] THEN
  MP_TAC(SPECL [`N:num`; `env:(flat_v)flat_environment`; `n:varN`; `e:flat_exp`;
    `env2:(flat_v)flat_environment`; `cfg:flat_pattern_config`]
    (CONJUNCT1 (CONJUNCT2 flat_patternProof_v_rel_rules))) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [FLATPAUX_MAX_ASM_TAC; DISCH_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT FLATPAUX_EXISTS_EQ_TAC THEN
  ASM_REWRITE_TAC[result_rel_def; ALL2]);;

let FLATPAUX_evaluate_dec_clause =
  hd (filter (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl(SPEC_ALL th)))))) =
                            "evaluate_dec" with Failure _ -> false)
             (CONJUNCTS flat_evaluate_def));;

let FLATPAUX_v_rel_Unitv = prove
 (`(flat_patternProof_v_rel Unitv x <=> x = Unitv) /\
   (flat_patternProof_v_rel x Unitv <=> x = Unitv)`,
  REWRITE_TAC[flat_Unitv_def] THEN CONJ_TAC THENL
  [REWRITE_TAC[v_rel_l_cases; LIST_REL_NIL] THEN MESON_TAC[];
   ONCE_REWRITE_TAC[CONJUNCT1 flat_patternProof_v_rel_cases] THEN
   STRUCT_CASES_TAC(ISPEC `x:flat_v` (CONJUNCT1 (cases "flat_v"))) THEN
   REWRITE_TAC[simple_basic_val_rel_def; v_container_xs_def; LIST_REL_NIL;
               distinctness "flat_v"; injectivity "flat_v"] THEN
   MESON_TAC[]]);;

let FLATPAUX_ce_dec = prove
 (FLATPAUX_ce_tm 14,
  MAP_EVERY X_GEN_TAC [`s:(C,FFI)flat_state`; `e:flat_exp`] THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`t1:(C,FFI)flat_state`; `res:((flat_v)error_result)option`;
    `s2:(C,FFI)flat_state`; `cfg:flat_pattern_config`] THEN
  REWRITE_TAC[FLATPAUX_evaluate_dec_clause; compile_dec_def] THEN
  MP_TAC(ISPEC `flat_pattern_compile_exp cfg e` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `rest:bool#flat_exp` MP_TAC)) THEN
  MP_TAC(ISPEC `rest:bool#flat_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `sg0:bool` (X_CHOOSE_THEN `y:flat_exp` SUBST1_TAC)) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `flat_evaluate (flat_environment_REC [] :(flat_v)flat_environment)
                  (s:(C,FFI)flat_state) [e]` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(C,FFI)flat_state` (X_CHOOSE_THEN
    `r1:(flat_v list,flat_v)result` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`s1:(C,FFI)flat_state`;
    `r1:(flat_v list,flat_v)result`; `MAX n0 0`; `sg0 \/ F`; `[y:flat_exp]`;
    `n0 + 1`; `flat_environment_REC [] :(flat_v)flat_environment`;
    `s2:(C,FFI)flat_state`; `cfg:flat_pattern_config`]) THEN
  ASM_REWRITE_TAC[flat_pattern_compile_exp_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[FLATPAUX_env_rel_def; flat_environment_INFO.ri_accessors;
              ALOOKUP_rel_empty] THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL [REWRITE_TAC[MAX] THEN ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN SUBST_ALL_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     is_case_app (lhs (concl th)))) THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)flat_state` (X_CHOOSE_THEN
    `r2:(flat_v list,flat_v)result` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     is_case_app (lhs (concl th)))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "result_rel"
    with Failure _ -> false)) THEN
  MP_TAC(ISPEC `r1:(flat_v list,flat_v)result` (cases "result")) THEN
  STRIP_TAC THEN FLATPAUX_SUBST_VAR_TAC "r1" THEN
  REWRITE_TAC[result_rel_Rval; result_rel_Rerr1] THEN
  STRIP_TAC THEN FLATPAUX_SUBST_VAR_TAC "r2" THEN CASE_REWRITE_TAC[] THENL
  [COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
   REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `v':flat_v list = [Unitv]` SUBST1_TAC THENL
    [UNDISCH_TAC `ALL2 flat_patternProof_v_rel [Unitv] (v':flat_v list)` THEN
     REWRITE_TAC[FLATPAUX_LIST_REL_CONS1; LIST_REL_NIL; FLATPAUX_v_rel_Unitv] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    REWRITE_TAC[PAIR_EQ] THEN REPEAT FLATPAUX_EXISTS_EQ_TAC THEN
    ASM_REWRITE_TAC[OPTREL_NONE];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
      can (find_term ((=) `Rtype_error`)) (concl th))) THEN
    REWRITE_TAC[]];
   REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
   REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
   REWRITE_TAC[PAIR_EQ] THEN REPEAT FLATPAUX_EXISTS_EQ_TAC THEN
   ASM_REWRITE_TAC[OPTREL_SOME; option_INJ; UNWIND_THM1]]);;

let FLATPAUX_ce_decs_nil = prove
 (FLATPAUX_ce_tm 15,
  REWRITE_TAC FLATPAUX_evaluate_decs_clauses THEN REWRITE_TAC[MAP; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  ASM_REWRITE_TAC FLATPAUX_evaluate_decs_clauses THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT FLATPAUX_EXISTS_EQ_TAC THEN
  ASM_REWRITE_TAC[OPTREL_NONE]);;

let FLATPAUX_ce_decs_cons = prove
 (FLATPAUX_ce_tm 16,
  MAP_EVERY X_GEN_TAC [`s:(C,FFI)flat_state`; `d:flat_exp`; `ds:flat_exp list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihs") (LABEL_TAC "ihd")) THEN
  MAP_EVERY X_GEN_TAC [`t1:(C,FFI)flat_state`; `res:((flat_v)error_result)option`;
    `s2:(C,FFI)flat_state`; `cfg:flat_pattern_config`; `decs':flat_exp list`] THEN
  REWRITE_TAC FLATPAUX_evaluate_decs_clauses THEN REWRITE_TAC[MAP] THEN STRIP_TAC THEN
  FLATPAUX_SUBST_VAR_TAC "decs'" THEN REWRITE_TAC FLATPAUX_evaluate_decs_clauses THEN
  MP_TAC(ISPEC `evaluate_dec (s:(C,FFI)flat_state) d` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(C,FFI)flat_state` (X_CHOOSE_THEN
    `r:((flat_v)error_result)option` ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_case_app (lhs (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r:((flat_v)error_result)option` (cases "option")) THEN
  STRIP_TAC THEN FLATPAUX_SUBST_VAR_TAC "r" THEN CASE_REWRITE_TAC[] THENL
  [DISCH_TAC THEN
   REMOVE_THEN "ihd" (MP_TAC o SPECL [`s1:(C,FFI)flat_state`;
     `NONE:((flat_v)error_result)option`; `s2:(C,FFI)flat_state`;
     `cfg:flat_pattern_config`]) THEN
   ASM_REWRITE_TAC[FLATPAUX_option_DISTINCT] THEN
   DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)flat_state` (X_CHOOSE_THEN
     `r2:((flat_v)error_result)option` STRIP_ASSUME_TAC)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[OPTREL_NONE]) THEN FLATPAUX_SUBST_VAR_TAC "r2" THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   REMOVE_THEN "ihs" (MP_TAC o SPEC `s1:(C,FFI)flat_state`) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   EXISTS_TAC `cfg:flat_pattern_config` THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
   REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
   REMOVE_THEN "ihd" (MP_TAC o SPECL [`s1:(C,FFI)flat_state`;
     `SOME (a:(flat_v)error_result)`; `s2:(C,FFI)flat_state`;
     `cfg:flat_pattern_config`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)flat_state` (X_CHOOSE_THEN
     `r2:((flat_v)error_result)option` STRIP_ASSUME_TAC)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[OPTREL_SOME]) THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `e2:(flat_v)error_result` STRIP_ASSUME_TAC o
     check (is_exists o concl)) THEN
   FLATPAUX_SUBST_VAR_TAC "r2" THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[PAIR_EQ] THEN REPEAT FLATPAUX_EXISTS_EQ_TAC THEN
   ASM_REWRITE_TAC[OPTREL_SOME; option_INJ; UNWIND_THM1]]);;

let FLATPAUX_compile_exps_sing = prove
 (`!cfg e i sg y. flat_pattern_compile_exp cfg e = (i,sg,y)
     ==> flat_pattern_compile_exps cfg [e] = (i,sg,[y])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[flat_pattern_compile_exp_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; MAX] THEN ARITH_TAC);;

let FLATPAUX_SUBST_VARS_TAC =
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> let c = concl th in
           is_eq c && is_var (lhs c) && not (free_in (lhs c) (rhs c)))) ORELSE
         FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> let c = concl th in
           is_eq c && is_var (rhs c) && not (free_in (rhs c) (lhs c)))));;

let FLATPAUX_ce_intro2_tac outer =
  MAP_EVERY X_GEN_TAC outer THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[flat_pattern_compile_exp_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT IL1AUX_PAIRARG_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FLATPAUX_SPLIT_ASM_TAC THEN FLATPAUX_SUBST_VARS_TAC;;

let FLATPAUX_EVAL_SPLIT_TAC tm =
  MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s':(C,FFI)flat_state` (X_CHOOSE_THEN
    `r':(flat_v list,flat_v)result` ASSUME_TAC));;

let FLATPAUX_CE_IH_TAC lab es sv rv n env2 s2 : tactic = fun (asl,w as g) ->
  let l = subst [es,`es:flat_exp list`]
            `flat_pattern_compile_exps (cfg:flat_pattern_config) es` in
  let th = snd (find (fun (_,th) -> is_eq (concl th) && lhs (concl th) = l) asl) in
  let i,rest = dest_pair (rhs (concl th)) in
  let sg,ys = dest_pair rest in
  REMOVE_THEN lab (MP_TAC o SPECL [sv; rv; i; sg; ys; n; env2; s2;
    `cfg:flat_pattern_config`]) g;;

let FLATPAUX_MAX_SPLIT_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[FLATPAUX_MAX_LT; MAX_ADD_LESS]) THEN
  FLATPAUX_SPLIT_ASM_TAC;;

let FLATPAUX_NOT_TE_TAC rv =
  SUBGOAL_THEN (mk_neg(mk_eq(rv,`Rerr (Rabort Rtype_error):(flat_v list,flat_v)result`)))
    ASSUME_TAC THENL
  [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN FLATPAUX_SPLIT_ASM_TAC THEN
   FLATPAUX_SUBST_VARS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
   FIRST_ASSUM CONTR_TAC;
   ALL_TAC];;

let FLATPAUX_SING_RV_TAC =
  REPEAT(FIRST_ASSUM(fun th ->
    let r = rand (rhs (concl th)) in
    if is_comb r && fst(dest_const(rator r)) = "Rval" && is_var (rand r)
    then CHOOSE_THEN SUBST_ALL_TAC (MATCH_MP flat_evaluate_sing th)
    else failwith "sing"));;

let FLATPAUX_ce_raise = prove
 (FLATPAUX_ce_tm 3,
  FLATPAUX_ce_intro2_tac [`env:(flat_v)flat_environment`; `s:(C,FFI)flat_state`;
    `x:tra`; `e:flat_exp`] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FLATPAUX_compile_exps_sing) THEN
  FLATPAUX_EVAL_SPLIT_TAC `flat_evaluate env (s:(C,FFI)flat_state) [e]` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `flat_Raise`)) (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "flat_evaluate" with _ -> false)) (concl th))) THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_TAC THEN FLATPAUX_NOT_TE_TAC `r':(flat_v list,flat_v)result` THEN
  FLATPAUX_MAX_SPLIT_TAC THEN
  FLATPAUX_CE_IH_TAC "ih" `[e:flat_exp]` `s':(C,FFI)flat_state`
    `r':(flat_v list,flat_v)result` `N:num` `env2:(flat_v)flat_environment`
    `s2:(C,FFI)flat_state` THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)flat_state` (X_CHOOSE_THEN
    `r2:(flat_v list,flat_v)result` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r':(flat_v list,flat_v)result` (cases "result")) THEN
  STRIP_TAC THEN FLATPAUX_SUBST_VAR_TAC "r'" THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; result_rel_Rval; result_rel_Rerr1]) THEN
  FLATPAUX_SPLIT_ASM_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  FLATPAUX_SUBST_VARS_TAC THEN FLATPAUX_SING_RV_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FLATPAUX_LIST_REL_CONS1; LIST_REL_NIL]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  FLATPAUX_SUBST_VARS_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; HD] THEN REPEAT FLATPAUX_EXISTS_EQ_TAC THEN
  ASM_REWRITE_TAC[result_rel_def; exc_rel_def]);;
let FLATPAUX_ce_con_tac outer =
  FLATPAUX_ce_intro2_tac outer THEN
  FLATPAUX_EVAL_SPLIT_TAC `flat_evaluate env (s:(C,FFI)flat_state) (REVERSE es)` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `flat_Con`)) (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "flat_evaluate" with _ -> false)) (concl th))) THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_TAC THEN FLATPAUX_NOT_TE_TAC `r':(flat_v list,flat_v)result` THEN
  FLATPAUX_MAX_SPLIT_TAC THEN
  FLATPAUX_CE_IH_TAC "ih" `REVERSE (es:flat_exp list)` `s':(C,FFI)flat_state`
    `r':(flat_v list,flat_v)result` `N:num` `env2:(flat_v)flat_environment`
    `s2:(C,FFI)flat_state` THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)flat_state` (X_CHOOSE_THEN
    `r2:(flat_v list,flat_v)result` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[REVERSE_REVERSE] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r':(flat_v list,flat_v)result` (cases "result")) THEN
  STRIP_TAC THEN FLATPAUX_SUBST_VAR_TAC "r'" THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; result_rel_Rval; result_rel_Rerr1]) THEN
  FLATPAUX_SPLIT_ASM_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  FLATPAUX_SUBST_VARS_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT FLATPAUX_EXISTS_EQ_TAC THEN
  ASM_REWRITE_TAC[result_rel_def; exc_rel_def; ALL2; v_rel_l_cases] THEN
  TRY(EXISTS_TAC `REVERSE (v':flat_v list)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC EVERY2_REVERSE THEN ASM_REWRITE_TAC[]);;

let FLATPAUX_ce_con_none = prove
 (FLATPAUX_ce_tm 5,
  FLATPAUX_ce_con_tac [`env:(flat_v)flat_environment`; `s:(C,FFI)flat_state`;
    `x:tra`; `es:flat_exp list`]);;

let FLATPAUX_ce_con_some = prove
 (FLATPAUX_ce_tm 6,
  FLATPAUX_ce_con_tac [`env:(flat_v)flat_environment`; `s:(C,FFI)flat_state`;
    `x:tra`; `cn:ctor_id#type_id`; `es:flat_exp list`]);;
let FLATPAUX_env_rel_opt_bind = prove
 (`!N (n:(varN)option) env1 env2 v w.
     flat_patternProof_env_rel N env1 env2 /\ flat_patternProof_v_rel v w
     ==> flat_patternProof_env_rel N (flat_environment_v_fupd (opt_bind n v) env1)
                                     (flat_environment_v_fupd (opt_bind n w) env2)`,
  GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[FLATPAUX_env_rel_def; flat_environment_INFO.ri_accfupds; opt_bind_def] THEN
  CASE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ALOOKUP_rel_cons THEN ASM_REWRITE_TAC[]);;

let FLATPAUX_ce_let = prove
 (FLATPAUX_ce_tm 12,
  MAP_EVERY X_GEN_TAC [`env:(flat_v)flat_environment`; `s:(C,FFI)flat_state`;
    `x:tra`; `n:(varN)option`; `e1:flat_exp`; `e2:flat_exp`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[flat_pattern_compile_exp_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT IL1AUX_PAIRARG_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FLATPAUX_SPLIT_ASM_TAC THEN FLATPAUX_SUBST_VARS_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP FLATPAUX_compile_exps_sing)) THEN
  FLATPAUX_EVAL_SPLIT_TAC `flat_evaluate env (s:(C,FFI)flat_state) [e1]` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `flat_Let`)) (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "flat_evaluate" with _ -> false)) (concl th))) THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_TAC THEN FLATPAUX_NOT_TE_TAC `r':(flat_v list,flat_v)result` THEN
  FLATPAUX_MAX_SPLIT_TAC THEN
  FLATPAUX_CE_IH_TAC "ih" `[e1:flat_exp]` `s':(C,FFI)flat_state`
    `r':(flat_v list,flat_v)result` `N:num` `env2:(flat_v)flat_environment`
    `s2:(C,FFI)flat_state` THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2a:(C,FFI)flat_state` (X_CHOOSE_THEN
    `r2a:(flat_v list,flat_v)result` STRIP_ASSUME_TAC)) THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r':(flat_v list,flat_v)result` (cases "result")) THEN
  STRIP_TAC THEN FLATPAUX_SUBST_VAR_TAC "r'" THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; result_rel_Rval; result_rel_Rerr1]) THEN
  FLATPAUX_SPLIT_ASM_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  FLATPAUX_SUBST_VARS_TAC THEN FLATPAUX_SING_RV_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL2; HD]) THEN
  ASM_REWRITE_TAC[HD] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD] THENL
  [REMOVE_THEN "ih2" (MP_TAC o SPECL [`[y']:flat_v list`; `s':(C,FFI)flat_state`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`t1:(C,FFI)flat_state`; `r1:(flat_v list,flat_v)result`;
     `j':num`; `sg2':bool`; `[y2']:flat_exp list`; `N:num`;
     `flat_environment_v_fupd (opt_bind n (y:flat_v)) env2`; `t2a:(C,FFI)flat_state`;
     `cfg:flat_pattern_config`]) THEN
   ASM_REWRITE_TAC[HD] THEN ANTS_TAC THENL
   [MATCH_MP_TAC FLATPAUX_env_rel_opt_bind THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)flat_state` (X_CHOOSE_THEN
     `r2:(flat_v list,flat_v)result` STRIP_ASSUME_TAC)) THEN
   MAP_EVERY EXISTS_TAC [`t2:(C,FFI)flat_state`; `r2:(flat_v list,flat_v)result`] THEN
   ASM_REWRITE_TAC[];
   REPEAT FLATPAUX_EXISTS_EQ_TAC THEN ASM_REWRITE_TAC[result_rel_def]]);;
let FLATPAUX_Boolv_TF = prove
 (`~(flat_Boolv T = flat_Boolv F) /\ ~(flat_Boolv F = flat_Boolv T)`,
  REWRITE_TAC[flat_Boolv_def; injectivity "flat_v"; option_INJ; PAIR_EQ;
              true_tag_def; false_tag_def; ARITH_EQ]);;

let FLATPAUX_do_if_rel = prove
 (`!b b' x y e x' y'.
     flat_do_if b x y = SOME e /\ flat_patternProof_v_rel b b'
     ==> (e = x /\ flat_do_if b' x' y' = SOME x') \/
         (e = y /\ flat_do_if b' x' y' = SOME y')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP do_if_helper) THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[flat_do_if_def] THEN
  ASM_CASES_TAC `b = flat_Boolv T` THEN ASM_REWRITE_TAC[option_INJ; FLATPAUX_Boolv_TF] THENL
  [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `b = flat_Boolv F` THEN
  ASM_REWRITE_TAC[option_INJ; option_DISTINCT; FLATPAUX_Boolv_TF] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[FLATPAUX_Boolv_TF]);;
let FLATPAUX_TRIPLE_TAC tm (a,b,c) =
  MP_TAC(ISPEC tm FLATPAUX_TRIPLE_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN a (X_CHOOSE_THEN b (X_CHOOSE_THEN c ASSUME_TAC)));;

let FLATPAUX_IF_BRANCH_TAC e i sg y =
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REMOVE_THEN "ih2" (MP_TAC o SPECL [`[y']:flat_v list`; `s':(C,FFI)flat_state`; e]) THEN
  ASM_REWRITE_TAC[HD] THEN
  DISCH_THEN(MP_TAC o SPECL [`t1:(C,FFI)flat_state`; `r1:(flat_v list,flat_v)result`;
    i; sg; mk_list([y],`:flat_exp`); `N:num`; `env2:(flat_v)flat_environment`;
    `t2a:(C,FFI)flat_state`; `cfg:flat_pattern_config`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)flat_state` (X_CHOOSE_THEN
    `r2:(flat_v list,flat_v)result` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`t2:(C,FFI)flat_state`; `r2:(flat_v list,flat_v)result`] THEN
  ASM_REWRITE_TAC[];;

let FLATPAUX_ce_if = prove
 (FLATPAUX_ce_tm 10,
  MAP_EVERY X_GEN_TAC [`env:(flat_v)flat_environment`; `s:(C,FFI)flat_state`;
    `x:tra`; `e1:flat_exp`; `e2:flat_exp`; `e3:flat_exp`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN
  FLATPAUX_TRIPLE_TAC `flat_pattern_compile_exp cfg e1` (`i1:num`,`sg1:bool`,`y1:flat_exp`) THEN
  FLATPAUX_TRIPLE_TAC `flat_pattern_compile_exp cfg e2` (`i2:num`,`sg2:bool`,`y2:flat_exp`) THEN
  FLATPAUX_TRIPLE_TAC `flat_pattern_compile_exp cfg e3` (`i3:num`,`sg3:bool`,`y3:flat_exp`) THEN
  REWRITE_TAC[flat_pattern_compile_exp_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FLATPAUX_SPLIT_ASM_TAC THEN FLATPAUX_SUBST_VARS_TAC THEN
  REWRITE_TAC[evaluate_SmartIf] THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP FLATPAUX_compile_exps_sing)) THEN
  FLATPAUX_EVAL_SPLIT_TAC `flat_evaluate env (s:(C,FFI)flat_state) [e1]` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `flat_If`)) (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "flat_evaluate" with _ -> false)) (concl th))) THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_TAC THEN FLATPAUX_NOT_TE_TAC `r':(flat_v list,flat_v)result` THEN
  FLATPAUX_MAX_SPLIT_TAC THEN
  FLATPAUX_CE_IH_TAC "ih" `[e1:flat_exp]` `s':(C,FFI)flat_state`
    `r':(flat_v list,flat_v)result` `N:num` `env2:(flat_v)flat_environment`
    `s2:(C,FFI)flat_state` THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2a:(C,FFI)flat_state` (X_CHOOSE_THEN
    `r2a:(flat_v list,flat_v)result` STRIP_ASSUME_TAC)) THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r':(flat_v list,flat_v)result` (cases "result")) THEN
  STRIP_TAC THEN FLATPAUX_SUBST_VAR_TAC "r'" THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; result_rel_Rval; result_rel_Rerr1]) THEN
  FLATPAUX_SPLIT_ASM_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  FLATPAUX_SUBST_VARS_TAC THEN FLATPAUX_SING_RV_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL2; HD]) THEN
  ASM_REWRITE_TAC[HD] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD] THENL
  [MP_TAC(ISPEC `flat_do_if y' e2 e3` (cases "option")) THEN STRIP_TAC THEN
   FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN FLATPAUX_SPLIT_ASM_TAC THEN
    FLATPAUX_SUBST_VARS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    FIRST_ASSUM CONTR_TAC;
    FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
      MP_TAC(SPECL [`y2:flat_exp`; `y3:flat_exp`]
        (MATCH_MP FLATPAUX_do_if_rel (CONJ th th2))))) THEN
    STRIP_TAC THEN FLATPAUX_SUBST_VARS_TAC THENL
    [FLATPAUX_IF_BRANCH_TAC `e2:flat_exp` `i2:num` `sg2:bool` `y2:flat_exp`;
     FLATPAUX_IF_BRANCH_TAC `e3:flat_exp` `i3:num` `sg3:bool` `y3:flat_exp`]];
   REPEAT FLATPAUX_EXISTS_EQ_TAC THEN ASM_REWRITE_TAC[result_rel_def]]);;

let FLATPAUX_EVAL_SPLITN_TAC tm sv rv =
  MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN sv (X_CHOOSE_THEN rv ASSUME_TAC));;

let FLATPAUX_ce_cons = prove
 (FLATPAUX_ce_tm 1,
  MAP_EVERY X_GEN_TAC [`env:(flat_v)flat_environment`; `s:(C,FFI)flat_state`;
    `e1:flat_exp`; `e2:flat_exp`; `es:flat_exp list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN
  FLATPAUX_TRIPLE_TAC `flat_pattern_compile_exp cfg e1` (`i1:num`,`sg1:bool`,`y1:flat_exp`) THEN
  FLATPAUX_TRIPLE_TAC `flat_pattern_compile_exps cfg (CONS e2 es)`
    (`i2:num`,`sg2:bool`,`ys2:flat_exp list`) THEN
  ONCE_REWRITE_TAC[flat_pattern_compile_exp_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FLATPAUX_SPLIT_ASM_TAC THEN FLATPAUX_SUBST_VARS_TAC THEN
  SUBGOAL_THEN `?y2 ys3. ys2 = CONS (y2:flat_exp) ys3` STRIP_ASSUME_TAC THENL
  [FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1(CONJUNCT2 LENGTH_compile_exps_IMP))) THEN
   STRUCT_CASES_TAC(ISPEC `ys2:flat_exp list` list_CASES) THEN
   REWRITE_TAC[LENGTH; NOT_SUC; CONS_11] THEN MESON_TAC[];
   ALL_TAC] THEN
  FLATPAUX_SUBST_VARS_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FLATPAUX_compile_exps_sing) THEN
  FLATPAUX_EVAL_SPLIT_TAC `flat_evaluate env (s:(C,FFI)flat_state) [e1]` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `flat_evaluate env (s:(C,FFI)flat_state) (CONS e1 (CONS e2 es))`)) THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_TAC THEN FLATPAUX_NOT_TE_TAC `r':(flat_v list,flat_v)result` THEN
  FLATPAUX_MAX_SPLIT_TAC THEN
  FLATPAUX_CE_IH_TAC "ih" `[e1:flat_exp]` `s':(C,FFI)flat_state`
    `r':(flat_v list,flat_v)result` `N:num` `env2:(flat_v)flat_environment`
    `s2:(C,FFI)flat_state` THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2a:(C,FFI)flat_state` (X_CHOOSE_THEN
    `r2a:(flat_v list,flat_v)result` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r':(flat_v list,flat_v)result` (cases "result")) THEN
  STRIP_TAC THEN FLATPAUX_SUBST_VAR_TAC "r'" THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; result_rel_Rval; result_rel_Rerr1]) THEN
  FLATPAUX_SPLIT_ASM_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  FLATPAUX_SUBST_VARS_TAC THEN FLATPAUX_SING_RV_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL2; HD]) THEN
  ASM_REWRITE_TAC[HD] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD] THENL
  [FLATPAUX_EVAL_SPLITN_TAC `flat_evaluate env (s':(C,FFI)flat_state) (CONS e2 es)`
     `s3:(C,FFI)flat_state` `r3:(flat_v list,flat_v)result` THEN
   FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
   FLATPAUX_NOT_TE_TAC `r3:(flat_v list,flat_v)result` THEN
   REMOVE_THEN "ih2" (fun ih2 -> FIRST_ASSUM(fun th -> LABEL_TAC "ih2" (MATCH_MP ih2 th))) THEN
   FLATPAUX_CE_IH_TAC "ih2" `CONS (e2:flat_exp) es` `s3:(C,FFI)flat_state`
     `r3:(flat_v list,flat_v)result` `N:num` `env2:(flat_v)flat_environment`
     `t2a:(C,FFI)flat_state` THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `t2b:(C,FFI)flat_state` (X_CHOOSE_THEN
     `r2b:(flat_v list,flat_v)result` STRIP_ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   MP_TAC(ISPEC `r3:(flat_v list,flat_v)result` (cases "result")) THEN
   STRIP_TAC THEN FLATPAUX_SUBST_VAR_TAC "r3" THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; result_rel_Rval; result_rel_Rerr1]) THEN
   FLATPAUX_SPLIT_ASM_TAC THEN
   REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
   FLATPAUX_SUBST_VARS_TAC THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[PAIR_EQ] THEN REPEAT FLATPAUX_EXISTS_EQ_TAC THEN
   ASM_REWRITE_TAC[result_rel_def; ALL2];
   REPEAT FLATPAUX_EXISTS_EQ_TAC THEN ASM_REWRITE_TAC[result_rel_def]]);;
let FLATPAUX_letrec_compile = prove
 (CASE_TERM `!(fs:(varN#varN#flat_exp)list) cfg.
     MAP (\(a,b,(j,sg,e)). (a,b,e))
       (MAP (\fn. match fn with (a,b,c) -> (a,b,flat_pattern_compile_exp cfg c)) fs) =
     MAP (\(n,m,e). (n,m,SND (SND (flat_pattern_compile_exp cfg e)))) fs /\
     MAP (\(a,b,(j,sg,e)). j)
       (MAP (\fn. match fn with (a,b,c) -> (a,b,flat_pattern_compile_exp cfg c)) fs) =
     MAP (\(n,m,e). FST (flat_pattern_compile_exp cfg e)) fs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; CONS_11] THEN GEN_TAC THEN
  SPEC_TAC(`h:varN#varN#flat_exp`,`h:varN#varN#flat_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p1:varN`; `p2:varN`; `p3:flat_exp`] THEN
  CASE_REWRITE_TAC[] THEN
  FLATPAUX_TRIPLE_TAC `flat_pattern_compile_exp cfg p3` (`a1:num`,`a2:bool`,`a3:flat_exp`) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[FST; SND]);;

let FLATPAUX_letrec_env_rel = prove
 (`!N cfg (funs:(varN#varN#flat_exp)list) (env:(flat_v)flat_environment) env2.
     flat_patternProof_env_rel N env env2 /\
     ALL (\(n,m,e). FST (flat_pattern_compile_exp cfg e) < N) funs
     ==> flat_patternProof_env_rel N
           (flat_environment_v_fupd
              (K (flat_build_rec_env funs env (flat_environment_v env))) env)
           (flat_environment_v_fupd
              (K (flat_build_rec_env
                    (MAP (\(n,m,e). (n,m,SND (SND (flat_pattern_compile_exp cfg e))))
                         funs)
                    env2 (flat_environment_v env2))) env2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!f. flat_patternProof_v_rel (flat_Recclosure env funs f)
      (flat_Recclosure env2
         (MAP (\(n,m,e). (n,m,SND (SND (flat_pattern_compile_exp cfg e)))) funs) f)`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   MATCH_MP_TAC (CONJUNCT1(CONJUNCT2(CONJUNCT2 flat_patternProof_v_rel_rules))) THEN
   EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[FLATPAUX_env_rel_def; flat_environment_INFO.ri_accfupds; K_THM;
              build_rec_env_eq_MAP] THEN
  MATCH_MP_TAC ALOOKUP_rel_append_suff THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[FLATPAUX_env_rel_def]] THEN
  MATCH_MP_TAC ALOOKUP_rel_eq_fst THEN
  REWRITE_TAC[GSYM MAP_o] THEN
  REWRITE_TAC[ALL2_MAP2; ALL2_ALL; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_REWRITE_TAC[FST; SND]);;
let FLATPAUX_letrec_MAX_LIST = prove
 (`!(funs:(varN#varN#flat_exp)list) cfg N.
     MAX_LIST (MAP (\(n,m,e). FST (flat_pattern_compile_exp cfg e)) funs) < N <=>
     0 < N /\ ALL (\(n,m,e). FST (flat_pattern_compile_exp cfg e) < N) funs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; MAX_LIST; ALL; FLATPAUX_MAX_LT] THEN
  SPEC_TAC(`h:varN#varN#flat_exp`,`h:varN#varN#flat_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[CONJ_ACI]);;

let FLATPAUX_letrec_MAP_FST = prove
 (`!(funs:(varN#varN#flat_exp)list) cfg.
     MAP FST (MAP (\(n,m,e). (n,m,SND (SND (flat_pattern_compile_exp cfg e)))) funs) =
     MAP FST funs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; CONS_11] THEN
  SPEC_TAC(`h:varN#varN#flat_exp`,`h:varN#varN#flat_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[FST]);;

let FLATPAUX_ce_letrec = prove
 (FLATPAUX_ce_tm 13,
  MAP_EVERY X_GEN_TAC [`env:(flat_v)flat_environment`; `s:(C,FFI)flat_state`;
    `x:mlstring`; `funs:(varN#varN#flat_exp)list`; `e:flat_exp`] THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  REPEAT GEN_TAC THEN
  FLATPAUX_TRIPLE_TAC `flat_pattern_compile_exp cfg e` (`i1:num`,`sg1:bool`,`y1:flat_exp`) THEN
  REWRITE_TAC[flat_pattern_compile_exp_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FLATPAUX_SPLIT_ASM_TAC THEN FLATPAUX_SUBST_VARS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FLATPAUX_letrec_compile]) THEN
  REWRITE_TAC[FLATPAUX_letrec_compile] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FLATPAUX_MAX_LT; FLATPAUX_letrec_MAX_LIST]) THEN
  FLATPAUX_SPLIT_ASM_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FLATPAUX_compile_exps_sing) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `flat_Letrec`)) (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "flat_evaluate" with _ -> false)) (concl th))) THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN REWRITE_TAC[FLATPAUX_letrec_MAP_FST] THEN
  ASM_CASES_TAC `ALL_DISTINCT (MAP FST (funs:(varN#varN#flat_exp)list))` THEN
  ASM_REWRITE_TAC[] THENL
  [DISCH_TAC THEN
   REMOVE_THEN "ih" (MP_TAC o SPECL [`t1:(C,FFI)flat_state`; `r1:(flat_v list,flat_v)result`;
     `i1:num`; `sg1:bool`; `[y1]:flat_exp list`; `N:num`;
     `flat_environment_v_fupd (K (flat_build_rec_env
        (MAP (\(n,m,e). (n,m,SND (SND (flat_pattern_compile_exp cfg e)))) funs)
        env2 (flat_environment_v env2))) (env2:(flat_v)flat_environment)`;
     `s2:(C,FFI)flat_state`; `cfg:flat_pattern_config`] o
     C MATCH_MP (ASSUME `ALL_DISTINCT (MAP FST (funs:(varN#varN#flat_exp)list))`)) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC FLATPAUX_letrec_env_rel THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[];
   REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN FLATPAUX_SUBST_VARS_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC]);;
let FLATPAUX_LIST_CASES_TAC tm h t =
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN h (X_CHOOSE_THEN t SUBST_ALL_TAC))
    (ISPEC tm list_CASES);;

let FLATPAUX_dest_thunk_IsThunk_IMP = prove
 (`!vs (st:(flat_v store_v)list) m v.
     flat_dest_thunk vs st = flat_IsThunk m v
     ==> ?n. vs = [flat_Loc F n] /\ n < LENGTH st /\ EL n st = Thunk m v`,
  REPEAT GEN_TAC THEN
  FLATPAUX_LIST_CASES_TAC `vs:flat_v list` `h:flat_v` `t:flat_v list` THEN
  REWRITE_TAC[flat_dest_thunk_def; distinctness "flat_dest_thunk_ret"] THEN
  FLATPAUX_LIST_CASES_TAC `t:flat_v list` `h2:flat_v` `t2:flat_v list` THEN
  REWRITE_TAC[flat_dest_thunk_def; distinctness "flat_dest_thunk_ret"] THEN
  STRUCT_CASES_TAC (ISPEC `h:flat_v` (CONJUNCT1 (cases "flat_v"))) THEN
  REWRITE_TAC[flat_dest_thunk_def; distinctness "flat_dest_thunk_ret"; store_lookup_def;
              CONS_11; injectivity "flat_v"] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "flat_dest_thunk_ret"] THEN
  MP_TAC(ISPEC `EL a1 (st:(flat_v store_v)list)` (cases "store_v")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "flat_dest_thunk_ret"] THEN
  DISJ_CASES_THEN SUBST_ALL_TAC (ISPEC `a0':thunk_mode` (cases "thunk_mode")) THEN
  BOOL_CASES_TAC `a0:bool` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "flat_dest_thunk_ret"; injectivity "flat_dest_thunk_ret"] THEN
  STRIP_TAC THEN EXISTS_TAC `a1:num` THEN ASM_REWRITE_TAC[]);;
let FLATPAUX_dest_thunk_rel = prove
 (`!vs vs' (s:(C,FFI)flat_state) t m v cfg.
     flat_dest_thunk vs (flat_state_refs s) = flat_IsThunk m v /\
     ALL2 flat_patternProof_v_rel vs vs' /\ flat_patternProof_state_rel cfg s t
     ==> ?v'. flat_dest_thunk vs' (flat_state_refs t) = flat_IsThunk m v' /\
              flat_patternProof_v_rel v v'`,
  REWRITE_TAC[flat_patternProof_state_rel_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC o
    MATCH_MP FLATPAUX_dest_thunk_IsThunk_IMP) THEN
  FLATPAUX_SUBST_VARS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FLATPAUX_LIST_REL_CONS1; LIST_REL_NIL; v_rel_l_cases]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  FLATPAUX_SUBST_VARS_TAC THEN
  UNDISCH_TAC `ALL2 (sv_rel flat_patternProof_v_rel) (flat_state_refs (s:(C,FFI)flat_state))
                 (flat_state_refs (t:(C,FFI)flat_state))` THEN
  REWRITE_TAC[LIST_REL_EL_EQN] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[sv_rel_cases] THEN
  REWRITE_TAC[injectivity "store_v"; distinctness "store_v"] THEN STRIP_TAC THEN
  REWRITE_TAC[flat_dest_thunk_def; store_lookup_def] THEN
  FLATPAUX_SUBST_VARS_TAC THEN
  SUBGOAL_THEN `n < LENGTH (flat_state_refs (t:(C,FFI)flat_state))` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISJ_CASES_THEN SUBST_ALL_TAC (ISPEC `m':thunk_mode` (cases "thunk_mode")) THEN
  CASE_REWRITE_TAC[] THEN EXISTS_TAC `v2:flat_v` THEN ASM_REWRITE_TAC[]);;
let FLATPAUX_update_thunk_SOME_IMP = prove
 (`!vs (st:(flat_v store_v)list) ws st1.
     flat_update_thunk vs st ws = SOME st1
     ==> ?n w. vs = [flat_Loc F n] /\ ws = [w] /\ flat_dest_thunk [w] st = flat_NotThunk /\
               store_assign n (Thunk Evaluated w) st = SOME st1`,
  REPEAT GEN_TAC THEN
  FLATPAUX_LIST_CASES_TAC `vs:flat_v list` `h:flat_v` `t:flat_v list` THEN
  REWRITE_TAC[flat_update_thunk_def; option_DISTINCT] THEN
  FLATPAUX_LIST_CASES_TAC `t:flat_v list` `h2:flat_v` `t2:flat_v list` THEN
  REWRITE_TAC[flat_update_thunk_def; option_DISTINCT] THEN
  FLATPAUX_LIST_CASES_TAC `ws:flat_v list` `w:flat_v` `wt:flat_v list` THEN
  REWRITE_TAC[flat_update_thunk_def; option_DISTINCT] THEN
  FLATPAUX_LIST_CASES_TAC `wt:flat_v list` `w2:flat_v` `wt2:flat_v list` THEN
  REWRITE_TAC[flat_update_thunk_def; option_DISTINCT] THEN
  STRUCT_CASES_TAC (ISPEC `h:flat_v` (CONJUNCT1 (cases "flat_v"))) THEN
  REWRITE_TAC[flat_update_thunk_def; option_DISTINCT; CONS_11; injectivity "flat_v";
              distinctness "flat_v"] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  MP_TAC(ISPEC `flat_dest_thunk [w] (st:(flat_v store_v)list)` (cases "flat_dest_thunk_ret")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`a1:num`; `w:flat_v`] THEN ASM_REWRITE_TAC[]);;
let FLATPAUX_update_thunk_rel = prove
 (`!vs vs' (s:(C,FFI)flat_state) t ws ws' refs cfg.
     flat_update_thunk vs (flat_state_refs s) ws = SOME refs /\
     ALL2 flat_patternProof_v_rel vs vs' /\ ALL2 flat_patternProof_v_rel ws ws' /\
     flat_patternProof_state_rel cfg s t
     ==> ?refs'. flat_update_thunk vs' (flat_state_refs t) ws' = SOME refs' /\
                 flat_patternProof_state_rel cfg (flat_state_refs_fupd (K refs) s)
                   (flat_state_refs_fupd (K refs') t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `w:flat_v` STRIP_ASSUME_TAC) o
    MATCH_MP FLATPAUX_update_thunk_SOME_IMP) THEN
  FLATPAUX_SUBST_VARS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FLATPAUX_LIST_REL_CONS1; LIST_REL_NIL; v_rel_l_cases]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  FLATPAUX_SUBST_VARS_TAC THEN
  MP_TAC(ISPECL [`flat_patternProof_v_rel`;
    `flat_patternProof_state_rel cfg:(C,FFI)flat_state->(C,FFI)flat_state->bool`;
    `n:num`; `Thunk Evaluated (w:flat_v)`; `s:(C,FFI)flat_state`;
    `refs:(flat_v store_v)list`; `t:(C,FFI)flat_state`; `Thunk Evaluated (hv:flat_v)`]
    simple_state_rel_store_assign) THEN
  ASM_REWRITE_TAC[flat_patternProof_simple_state_rel; sv_rel_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `refs':(flat_v store_v)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `refs':(flat_v store_v)list` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(REWRITE_RULE[flat_patternProof_state_rel_def]
    (ASSUME `flat_patternProof_state_rel cfg (s:(C,FFI)flat_state) t`)) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`flat_patternProof_v_rel`; `flat_state_refs (s:(C,FFI)flat_state)`;
    `flat_state_refs (t:(C,FFI)flat_state)`; `Evaluated`; `w:flat_v`; `hv:flat_v`]
    FLATSEMAUX_bad_thunk_update_rel) THEN
  ASM_REWRITE_TAC[flat_bad_thunk_update_def; flat_patternProof_simple_val_rel] THEN
  DISCH_TAC THEN REWRITE_TAC[flat_update_thunk_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;
let FLATPAUX_dec_name_f = prove
 (`dec_name_to_num (implode "f") = 0`,
  REWRITE_TAC[dec_name_to_num_def; strlen_implode] THEN
  CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let FLATPAUX_compile_AppUnit = prove
 (`!cfg t nm. ?sg.
     flat_pattern_compile_exps cfg [flat_AppUnit (Var_local t nm)] =
     (dec_name_to_num nm, sg, [flat_AppUnit (Var_local t nm)])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[flat_AppUnit_def; flat_pattern_compile_exp_def; REVERSE; APPEND] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[flat_pattern_compile_exp_def; REVERSE; APPEND] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ; REVERSE; APPEND] THEN
  EXISTS_TAC `op_sets_globals (Src Opapp)` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[MAX] THEN ARITH_TAC);;
let FLATPAUX_env_rel_REC1 = prove
 (`!N nm v w. flat_patternProof_v_rel v w
     ==> flat_patternProof_env_rel N (flat_environment_REC [(nm,v)])
                                     (flat_environment_REC [(nm,w)])`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[FLATPAUX_env_rel_def; flat_environment_INFO.ri_accessors] THEN
  MATCH_MP_TAC ALOOKUP_rel_cons THEN ASM_REWRITE_TAC[ALOOKUP_rel_empty]);;
let FLATPAUX_result_rel_list_result = prove
 (`!(R1:A->B->bool) (R2:C->D->bool) r1 r2.
     result_rel R1 R2 r1 r2
     ==> result_rel (ALL2 R1) R2 (list_result r1) (list_result r2)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r1:(A,C)result` (cases "result")) THEN
  STRUCT_CASES_TAC(ISPEC `r2:(B,D)result` (cases "result")) THEN
  REWRITE_TAC[result_rel_def; list_result_def; ALL2]);;

let FLATPAUX_option_pair_cases = prove
 (`!x:(A#B)option. x = NONE \/ ?a b. x = SOME (a,b)`,
  MESON_TAC[cases "option"; PAIR]);;

let FLATPAUX_option_triple_cases = prove
 (`!x:(A#B#D)option. x = NONE \/ ?a b c. x = SOME (a,b,c)`,
  MESON_TAC[cases "option"; PAIR]);;
let FLATPAUX_TE_CONTR_TAC =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN FLATPAUX_SUBST_VARS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;;

let FLATPAUX_APP_OPAPP_TAC =
  DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `env1:(flat_v)flat_environment`
    (X_CHOOSE_THEN `e1:flat_exp` ASSUME_TAC))
    (ISPEC `flat_do_opapp (REVERSE (a:flat_v list))` FLATPAUX_option_pair_cases) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
  [FLATPAUX_TE_CONTR_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP do_opapp_thm_REVERSE (CONJ
    (ASSUME `flat_do_opapp (REVERSE (a:flat_v list)) = SOME (env1,e1)`)
    (ASSUME `ALL2 flat_patternProof_v_rel a v'`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ic:num` (X_CHOOSE_THEN `sgc:bool` (X_CHOOSE_THEN `ec:flat_exp`
    (X_CHOOSE_THEN `envc:(flat_v)flat_environment` (X_CHOOSE_THEN `cfgc:flat_pattern_config`
     STRIP_ASSUME_TAC))))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(MATCH_MP flat_patternProof_state_rel_IMP_clock
    (ASSUME `flat_patternProof_state_rel s_cfg (s':(C,FFI)flat_state) t2a`)) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `flat_state_clock (s':(C,FFI)flat_state) = 0` THEN ASM_REWRITE_TAC[] THENL
  [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN FLATPAUX_SUBST_VARS_TAC THEN
   REWRITE_TAC[PAIR_EQ] THEN REPEAT FLATPAUX_EXISTS_EQ_TAC THEN
   ASM_REWRITE_TAC[result_rel_def; exc_rel_def];
   DISCH_TAC THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP FLATPAUX_compile_exps_sing) THEN
   MP_TAC(MATCH_MP flat_patternProof_state_rel_dec_clock
     (ASSUME `flat_patternProof_state_rel s_cfg (s':(C,FFI)flat_state) t2a`)) THEN
   DISCH_TAC THEN
   REMOVE_THEN "ih_opapp" (MP_TAC o SPECL [`a:flat_v list`; `env1:(flat_v)flat_environment`;
     `s':(C,FFI)flat_state`; `e1:flat_exp`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`t1:(C,FFI)flat_state`; `r1:(flat_v list,flat_v)result`;
     `ic:num`; `sgc:bool`; `[ec]:flat_exp list`; `ic + 1`; `envc:(flat_v)flat_environment`;
     `flat_dec_clock (t2a:(C,FFI)flat_state)`; `cfgc:flat_pattern_config`]) THEN
   ASM_REWRITE_TAC[ARITH_RULE `i < i + 1`]];;

let FLATPAUX_APP_OTHER_TAC =
  DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s3:(C,FFI)flat_state`
    (X_CHOOSE_THEN `r3:(flat_v,flat_v)result` ASSUME_TAC))
    (ISPEC `flat_do_app (s':(C,FFI)flat_state) op (REVERSE (a:flat_v list))`
       FLATPAUX_option_pair_cases) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
  [FLATPAUX_TE_CONTR_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP do_app_thm_REVERSE (CONJ
    (ASSUME `flat_do_app (s':(C,FFI)flat_state) op (REVERSE (a:flat_v list)) = SOME (s3,r3)`)
    (CONJ (ASSUME `flat_patternProof_state_rel s_cfg (s':(C,FFI)flat_state) t2a`)
          (ASSUME `ALL2 flat_patternProof_v_rel a v'`)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)flat_state` (X_CHOOSE_THEN
    `r3':(flat_v,flat_v)result` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN FLATPAUX_SUBST_VARS_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT FLATPAUX_EXISTS_EQ_TAC THEN
  ASM_SIMP_TAC[FLATPAUX_result_rel_list_result];;
let FLATPAUX_APP_EVAL_TAC =
  DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `decs:flat_exp list`
    (X_CHOOSE_THEN `ecfg:(C)install_config` (X_CHOOSE_THEN `retv:flat_v` ASSUME_TAC)))
    (ISPEC `flat_do_eval (REVERSE (a:flat_v list))
              (flat_state_eval_config (s':(C,FFI)flat_state))`
       FLATPAUX_option_triple_cases) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
  [FLATPAUX_TE_CONTR_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP do_eval_thm (CONJ
    (ASSUME `flat_do_eval (REVERSE (a:flat_v list))
               (flat_state_eval_config (s':(C,FFI)flat_state)) = SOME (decs,ecfg,retv)`)
    (CONJ (ASSUME `flat_patternProof_state_rel s_cfg (s':(C,FFI)flat_state) t2a`)
          (MATCH_MP EVERY2_REVERSE (ASSUME `ALL2 flat_patternProof_v_rel a v'`))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `retv':flat_v` (X_CHOOSE_THEN `decs':flat_exp list`
    (X_CHOOSE_THEN `ecfg':(C)install_config` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[flat_state_INFO.ri_accfupds] THEN
  MP_TAC(MATCH_MP flat_patternProof_state_rel_IMP_clock
    (ASSUME `flat_patternProof_state_rel s_cfg (s':(C,FFI)flat_state) t2a`)) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `flat_state_clock (s':(C,FFI)flat_state) = 0` THEN ASM_REWRITE_TAC[] THENL
  [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN FLATPAUX_SUBST_VARS_TAC THEN
   REWRITE_TAC[PAIR_EQ] THEN REPEAT FLATPAUX_EXISTS_EQ_TAC THEN
   ASM_REWRITE_TAC[result_rel_def; exc_rel_def];
   ALL_TAC] THEN
  FLATPAUX_EVAL_SPLITN_TAC `flat_evaluate_decs (flat_dec_clock
      (flat_state_eval_config_fupd (K ecfg) (s':(C,FFI)flat_state))) decs`
    `s3:(C,FFI)flat_state` `res3:((flat_v)error_result)option` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(res3 = SOME (Rabort Rtype_error):((flat_v)error_result)option)`
    ASSUME_TAC THENL
  [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN FLATPAUX_SPLIT_ASM_TAC THEN
   FLATPAUX_SUBST_VARS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
   ALL_TAC] THEN
  MP_TAC(MATCH_MP flat_patternProof_state_rel_dec_clock
    (ASSUME `flat_patternProof_state_rel s_cfg
               (flat_state_eval_config_fupd (K ecfg) (s':(C,FFI)flat_state))
               (flat_state_eval_config_fupd (K ecfg') t2a)`)) THEN
  DISCH_TAC THEN
  REMOVE_THEN "ih_eval" (MP_TAC o SPECL [`a:flat_v list`; `retv:flat_v`;
    `ecfg:(C)install_config`; `s':(C,FFI)flat_state`; `decs:flat_exp list`]) THEN
  ASM_REWRITE_TAC[flat_state_INFO.ri_accfupds] THEN
  DISCH_THEN(MP_TAC o SPECL [`s3:(C,FFI)flat_state`; `res3:((flat_v)error_result)option`;
    `flat_dec_clock (flat_state_eval_config_fupd (K ecfg') (t2a:(C,FFI)flat_state))`;
    `s_cfg:flat_pattern_config`; `MAP (compile_dec s_cfg) (decs:flat_exp list)`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)flat_state` (X_CHOOSE_THEN
    `res':((flat_v)error_result)option` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `e3:(flat_v)error_result` SUBST_ALL_TAC)
    (ISPEC `res3:((flat_v)error_result)option` (cases "option")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[OPTREL_NONE; OPTREL_SOME]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  FLATPAUX_SUBST_VARS_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN FLATPAUX_SPLIT_ASM_TAC THEN
  FLATPAUX_SUBST_VARS_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT FLATPAUX_EXISTS_EQ_TAC THEN
  ASM_REWRITE_TAC[result_rel_def; ALL2];;
let FLATPAUX_APP_FORCE_TAC =
  DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `m:thunk_mode` (X_CHOOSE_THEN `tv:flat_v` ASSUME_TAC)))
    (ISPEC `flat_dest_thunk a (flat_state_refs (s':(C,FFI)flat_state))`
      (cases "flat_dest_thunk_ret")) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
  [FLATPAUX_TE_CONTR_TAC; FLATPAUX_TE_CONTR_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP FLATPAUX_dest_thunk_rel (CONJ
    (ASSUME `flat_dest_thunk a (flat_state_refs (s':(C,FFI)flat_state)) = flat_IsThunk m tv`)
    (CONJ (ASSUME `ALL2 flat_patternProof_v_rel a v'`)
          (ASSUME `flat_patternProof_state_rel s_cfg (s':(C,FFI)flat_state) t2a`)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `tv':flat_v` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISJ_CASES_THEN SUBST_ALL_TAC (ISPEC `m:thunk_mode` (cases "thunk_mode")) THEN
  CASE_REWRITE_TAC[] THENL
  [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN FLATPAUX_SUBST_VARS_TAC THEN
   REWRITE_TAC[PAIR_EQ] THEN REPEAT FLATPAUX_EXISTS_EQ_TAC THEN
   ASM_REWRITE_TAC[result_rel_def; ALL2];
   ALL_TAC] THEN
  FLATPAUX_EVAL_SPLITN_TAC `flat_evaluate (flat_environment_REC [(implode "f",tv)])
      (s':(C,FFI)flat_state) [flat_AppUnit (Var_local backend_common_None (implode "f"))]`
    `s3:(C,FFI)flat_state` `r3:(flat_v list,flat_v)result` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  FLATPAUX_NOT_TE_TAC `r3:(flat_v list,flat_v)result` THEN
  REMOVE_THEN "ih_force" (MP_TAC o SPECL [`a:flat_v list`; `tv:flat_v`;
    `s':(C,FFI)flat_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cfg:flat_pattern_config`; `backend_common_None`; `implode "f"`]
    FLATPAUX_compile_AppUnit) THEN
  DISCH_THEN(X_CHOOSE_TAC `sgu:bool`) THEN
  DISCH_THEN(MP_TAC o SPECL [`s3:(C,FFI)flat_state`; `r3:(flat_v list,flat_v)result`;
    `dec_name_to_num (implode "f")`; `sgu:bool`;
    `[flat_AppUnit (Var_local backend_common_None (implode "f"))]`; `1`;
    `flat_environment_REC [(implode "f",tv':flat_v)]`; `t2a:(C,FFI)flat_state`;
    `cfg:flat_pattern_config`]) THEN
  ASM_REWRITE_TAC[FLATPAUX_dec_name_f; ARITH_RULE `0 < 1`] THEN
  ANTS_TAC THENL [MATCH_MP_TAC FLATPAUX_env_rel_REC1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2b:(C,FFI)flat_state` (X_CHOOSE_THEN
    `r2b:(flat_v list,flat_v)result` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r3:(flat_v list,flat_v)result` (cases "result")) THEN
  STRIP_TAC THEN FLATPAUX_SUBST_VAR_TAC "r3" THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; result_rel_Rval; result_rel_Rerr1]) THEN
  FLATPAUX_SPLIT_ASM_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  FLATPAUX_SUBST_VARS_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
  [DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `refs1:(flat_v store_v)list` ASSUME_TAC)
     (ISPEC `flat_update_thunk a (flat_state_refs (s3:(C,FFI)flat_state)) a'`
       (cases "option")) THEN
   FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN FLATPAUX_SPLIT_ASM_TAC THEN
    FLATPAUX_SUBST_VARS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    FIRST_ASSUM CONTR_TAC;
    MP_TAC(MATCH_MP FLATPAUX_update_thunk_rel (CONJ
      (ASSUME `flat_update_thunk a (flat_state_refs (s3:(C,FFI)flat_state)) a' =
               SOME refs1`)
      (CONJ (ASSUME `ALL2 flat_patternProof_v_rel a v'`)
        (CONJ (ASSUME `ALL2 flat_patternProof_v_rel a' v''`)
              (ASSUME `flat_patternProof_state_rel s_cfg (s3:(C,FFI)flat_state) t2b`))))) THEN
    DISCH_THEN(X_CHOOSE_THEN `refs2:(flat_v store_v)list` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN FLATPAUX_SPLIT_ASM_TAC THEN
    FLATPAUX_SUBST_VARS_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN REPEAT FLATPAUX_EXISTS_EQ_TAC THEN
    ASM_REWRITE_TAC[result_rel_def]];
   REWRITE_TAC[PAIR_EQ] THEN REPEAT FLATPAUX_EXISTS_EQ_TAC THEN
   ASM_REWRITE_TAC[result_rel_def]];;
let FLATPAUX_ce_app = prove
 (FLATPAUX_ce_tm 9,
  MAP_EVERY X_GEN_TAC [`env:(flat_v)flat_environment`; `s:(C,FFI)flat_state`;
    `x:tra`; `op:flat_op`; `es:flat_exp list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") (CONJUNCTS_THEN2 (LABEL_TAC "ih_opapp")
    (CONJUNCTS_THEN2 (LABEL_TAC "ih_eval") (LABEL_TAC "ih_force")))) THEN
  REPEAT GEN_TAC THEN
  FLATPAUX_TRIPLE_TAC `flat_pattern_compile_exps cfg (REVERSE es)`
    (`i1:num`,`sg1:bool`,`ys1:flat_exp list`) THEN
  REWRITE_TAC[flat_pattern_compile_exp_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FLATPAUX_SPLIT_ASM_TAC THEN FLATPAUX_SUBST_VARS_TAC THEN
  FLATPAUX_EVAL_SPLIT_TAC `flat_evaluate env (s:(C,FFI)flat_state) (REVERSE es)` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `flat_App`)) (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "flat_evaluate" with _ -> false)) (concl th))) THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_TAC THEN FLATPAUX_NOT_TE_TAC `r':(flat_v list,flat_v)result` THEN
  FLATPAUX_MAX_SPLIT_TAC THEN
  FLATPAUX_CE_IH_TAC "ih" `REVERSE (es:flat_exp list)` `s':(C,FFI)flat_state`
    `r':(flat_v list,flat_v)result` `N:num` `env2:(flat_v)flat_environment`
    `s2:(C,FFI)flat_state` THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2a:(C,FFI)flat_state` (X_CHOOSE_THEN
    `r2a:(flat_v list,flat_v)result` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[REVERSE_REVERSE] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r':(flat_v list,flat_v)result` (cases "result")) THEN
  STRIP_TAC THEN FLATPAUX_SUBST_VAR_TAC "r'" THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; result_rel_Rval; result_rel_Rerr1]) THEN
  FLATPAUX_SPLIT_ASM_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  FLATPAUX_SUBST_VARS_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
  [ALL_TAC;
   REWRITE_TAC[PAIR_EQ] THEN REPEAT FLATPAUX_EXISTS_EQ_TAC THEN
   ASM_REWRITE_TAC[result_rel_def]] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  ASM_CASES_TAC `op = Src Opapp` THEN ASM_REWRITE_TAC[] THENL
  [FLATPAUX_APP_OPAPP_TAC;
   ASM_CASES_TAC `op = Src Eval` THEN ASM_REWRITE_TAC[] THENL
   [FLATPAUX_APP_EVAL_TAC;
    ASM_CASES_TAC `op = Src (ThunkOp ForceThunk)` THEN ASM_REWRITE_TAC[] THENL
    [FLATPAUX_APP_FORCE_TAC; FLATPAUX_APP_OTHER_TAC]]]);;
let FLATPAUX_match_result_cases = prove
 (`!x:((varN#flat_v)list#flat_pat#flat_exp)match_result.
     x = No_match \/ x = Match_type_error \/ ?env p e. x = Match (env,p,e)`,
  MESON_TAC[cases "match_result"; PAIR]);;

let FLATPAUX_compile_pats_sim = prove
 (CASE_TERM `!env env2 (s':(C,FFI)flat_state) t2a v1 w1 pes ps2 j sgp N cfg tr k dflt
      d1 d2 t1 r1.
   (!env' p e'. pmatch_rows pes s' v1 = Match (env',p,e') /\
                ALL_DISTINCT (flat_pat_bindings p)
      ==> !t1 r1 i sg ys N env2 s2 cfg.
            flat_evaluate (flat_environment_v_fupd
                             (K (APPEND env' (flat_environment_v env))) env) s' [e'] =
              (t1,r1) /\
            flat_pattern_compile_exps cfg [e'] = (i,sg,ys) /\
            flat_patternProof_env_rel N (flat_environment_v_fupd
                             (K (APPEND env' (flat_environment_v env))) env) env2 /\
            flat_patternProof_state_rel s_cfg s' s2 /\ i < N /\
            ~(r1 = Rerr (Rabort Rtype_error))
            ==> ?t2 r2. result_rel (ALL2 flat_patternProof_v_rel) flat_patternProof_v_rel
                          r1 r2 /\
                        flat_patternProof_state_rel s_cfg t1 t2 /\
                        flat_evaluate env2 s2 ys = (t2,r2)) /\
   compile_match cfg pes = (j,sgp,ps2) /\
   flat_patternProof_env_rel N env env2 /\
   flat_patternProof_state_rel s_cfg s' t2a /\
   flat_patternProof_v_rel v1 w1 /\ j + 2 <= k /\ k <= N /\
   (match pmatch_rows pes s' v1 with
      Match_type_error -> (s',Rerr (Rabort Rtype_error))
    | No_match -> (s',Rerr (Rraise d1))
    | Match (env',p',e') ->
        if ALL_DISTINCT (flat_pat_bindings p')
        then flat_evaluate (flat_environment_v_fupd
                              (K (APPEND env' (flat_environment_v env))) env) s' [e']
        else (s',Rerr (Rabort Rtype_error))) = (t1,r1) /\
   ~(r1 = Rerr (Rabort Rtype_error)) /\
   flat_evaluate (flat_environment_v_fupd
                    (K (CONS (enc_num_to_name k,w1) (flat_environment_v env2))) env2)
     t2a [dflt] = (t2a,Rerr (Rraise d2)) /\
   flat_patternProof_v_rel d1 d2
   ==> ?t2 r2. result_rel (ALL2 flat_patternProof_v_rel) flat_patternProof_v_rel r1 r2 /\
               flat_patternProof_state_rel s_cfg t1 t2 /\
               flat_evaluate (flat_environment_v_fupd
                    (K (CONS (enc_num_to_name k,w1) (flat_environment_v env2))) env2) t2a
                 [compile_pats cfg sgp tr k (Var_local tr (enc_num_to_name k)) dflt ps2] =
               (t2,r2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih2") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `j <= N:num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP compile_match_pmatch_rows (CONJ
    (ASSUME `compile_match cfg pes = (j,sgp,ps2)`)
    (CONJ (ASSUME `flat_patternProof_state_rel s_cfg (s':(C,FFI)flat_state) t2a`)
      (CONJ (ASSUME `flat_patternProof_v_rel v1 w1`)
        (CONJ (ASSUME `j <= N:num`)
              (REFL `pmatch_rows (pes:(flat_pat#flat_exp)list) (s':(C,FFI)flat_state) v1`)))))) THEN
  SUBGOAL_THEN `pure_eval_to (t2a:(C,FFI)flat_state)
     (flat_environment_v_fupd
        (K (CONS (enc_num_to_name k,w1) (flat_environment_v env2))) env2)
     (Var_local tr (enc_num_to_name k)) w1` ASSUME_TAC THENL
  [REWRITE_TAC[pure_eval_to_def; flat_evaluate_def; flat_environment_INFO.ri_accfupds;
               K_THM; ALOOKUP_DEF] THEN CASE_REWRITE_TAC[];
   ALL_TAC] THEN
  DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `env1':(varN#flat_v)list` (X_CHOOSE_THEN `p1:flat_pat`
      (X_CHOOSE_THEN `e1':flat_exp` ASSUME_TAC))))
    (ISPEC `pmatch_rows (pes:(flat_pat#flat_exp)list) (s':(C,FFI)flat_state) v1` FLATPAUX_match_result_cases) THEN
  FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
  [DISCH_TAC THEN
   SUBGOAL_THEN `~(pmatch_rows (ps2:(flat_pat#flat_exp)list) (t2a:(C,FFI)flat_state) w1 = Match_type_error)`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[distinctness "match_result"]; ALL_TAC] THEN
   FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
     REWRITE_TAC[MATCH_MP evaluate_compile_pats (CONJ th th2)])) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN FLATPAUX_SPLIT_ASM_TAC THEN
   FLATPAUX_SUBST_VARS_TAC THEN
   REWRITE_TAC[PAIR_EQ] THEN REPEAT FLATPAUX_EXISTS_EQ_TAC THEN
   ASM_REWRITE_TAC[result_rel_def; exc_rel_def];
   RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN FLATPAUX_SPLIT_ASM_TAC THEN
   FLATPAUX_SUBST_VARS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
   FIRST_ASSUM CONTR_TAC;
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ii:num` (X_CHOOSE_THEN `envb:(varN#flat_v)list`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(MATCH_MP compile_match_EL (CONJ (ASSUME `compile_match cfg pes = (j,sgp,ps2)`)
    (CONJ (ASSUME `ii < LENGTH (pes:(flat_pat#flat_exp)list)`)
          (SYM(ASSUME `(p1,e1') = EL ii (pes:(flat_pat#flat_exp)list)`))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `exp_i:num` (X_CHOOSE_THEN `sgi:bool`
    (X_CHOOSE_THEN `expc:flat_exp` STRIP_ASSUME_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `EL ii ps2 = (p1:flat_pat,expc:flat_exp)`]) THEN
  SUBGOAL_THEN `~(pmatch_rows (ps2:(flat_pat#flat_exp)list) (t2a:(C,FFI)flat_state) w1 = Match_type_error)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[distinctness "match_result"]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
    REWRITE_TAC[MATCH_MP evaluate_compile_pats (CONJ th th2)])) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `ALL_DISTINCT (flat_pat_bindings p1)` THENL
  [ALL_TAC;
   RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~ALL_DISTINCT (flat_pat_bindings p1)`]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN FLATPAUX_SPLIT_ASM_TAC THEN
   FLATPAUX_SUBST_VARS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
   FIRST_ASSUM CONTR_TAC] THEN
  FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  FLATPAUX_EVAL_SPLITN_TAC `flat_evaluate (flat_environment_v_fupd
      (K (CONS (enc_num_to_name k,w1) (flat_environment_v env2))) env2)
      (t2a:(C,FFI)flat_state)
      [compile_pat_rhs tr k (Var_local tr (enc_num_to_name k)) (p1,expc)]`
    `t3:(C,FFI)flat_state` `r3:(flat_v list,flat_v)result` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `max_dec_name (flat_pat_bindings p1) < k - 1 /\ exp_i < k - 1`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP evaluate_compile_pat_rhs (CONJ
    (ASSUME `flat_evaluate (flat_environment_v_fupd
      (K (CONS (enc_num_to_name k,w1) (flat_environment_v env2))) env2)
      (t2a:(C,FFI)flat_state)
      [compile_pat_rhs tr k (Var_local tr (enc_num_to_name k)) (p1,expc)] = (t3,r3)`)
    (CONJ (CONJUNCT1 (MATCH_MP pmatch_rows_IMP_pmatch
             (ASSUME `pmatch_rows (ps2:(flat_pat#flat_exp)list) (t2a:(C,FFI)flat_state) w1 = Match (envb,p1,expc)`)))
     (CONJ (ASSUME `flat_patternProof_env_rel N env env2`)
      (CONJ (ASSUME `ALOOKUP_rel (\x. dec_name_to_num x < N) flat_patternProof_v_rel
                       env1' envb`)
       (CONJ (ISPECL [`CONS (enc_num_to_name k,w1:flat_v) (flat_environment_v env2)`;
                      `flat_environment_v (env2:(flat_v)flat_environment)`] K_THM)
        (CONJ (ASSUME `k <= N:num`)
              (ASSUME `max_dec_name (flat_pat_bindings p1) < k - 1`)))))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ext_env:(flat_v)flat_environment` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FLATPAUX_compile_exps_sing) THEN
  REMOVE_THEN "ih2" (MP_TAC o SPECL [`t1:(C,FFI)flat_state`; `r1:(flat_v list,flat_v)result`;
    `exp_i:num`; `sgi:bool`; `[expc]:flat_exp list`; `k - 1`;
    `ext_env:(flat_v)flat_environment`; `t2a:(C,FFI)flat_state`;
    `cfg:flat_pattern_config`] o
    C MP (ASSUME `ALL_DISTINCT (flat_pat_bindings p1)`) o REWRITE_RULE[] o
    SPECL [`env1':(varN#flat_v)list`; `p1:flat_pat`; `e1':flat_exp`]) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)flat_state` (X_CHOOSE_THEN
    `r2:(flat_v list,flat_v)result` STRIP_ASSUME_TAC)) THEN
  FLATPAUX_SUBST_VARS_TAC THEN
  MAP_EVERY EXISTS_TAC [`t2:(C,FFI)flat_state`; `r2:(flat_v list,flat_v)result`] THEN
  ASM_REWRITE_TAC[]);;
let FLATPAUX_ce_mat = prove
 (FLATPAUX_ce_tm 11,
  MAP_EVERY X_GEN_TAC [`env:(flat_v)flat_environment`; `s:(C,FFI)flat_state`;
    `x:tra`; `e:flat_exp`; `pes:(flat_pat#flat_exp)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN
  FLATPAUX_TRIPLE_TAC `flat_pattern_compile_exp cfg e` (`i1:num`,`sg1:bool`,`y1:flat_exp`) THEN
  FLATPAUX_TRIPLE_TAC `compile_match cfg pes`
    (`j:num`,`sgp:bool`,`ps2:(flat_pat#flat_exp)list`) THEN
  REWRITE_TAC[flat_pattern_compile_exp_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FLATPAUX_SPLIT_ASM_TAC THEN FLATPAUX_SUBST_VARS_TAC THEN
  SUBGOAL_THEN `i1 < N /\ j + 2 <= MAX i1 j + 2 /\ MAX i1 j + 2 <= N` STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `MAX (MAX i1 j + 2) 0 < N` THEN REWRITE_TAC[MAX] THEN
   REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FLATPAUX_compile_exps_sing) THEN
  FLATPAUX_EVAL_SPLIT_TAC `flat_evaluate env (s:(C,FFI)flat_state) [e]` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `flat_Mat`)) (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "flat_evaluate" with _ -> false))
      (concl th))) THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_TAC THEN FLATPAUX_NOT_TE_TAC `r':(flat_v list,flat_v)result` THEN
  FLATPAUX_CE_IH_TAC "ih" `[e:flat_exp]` `s':(C,FFI)flat_state`
    `r':(flat_v list,flat_v)result` `N:num` `env2:(flat_v)flat_environment`
    `s2:(C,FFI)flat_state` THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2a:(C,FFI)flat_state` (X_CHOOSE_THEN
    `r2a:(flat_v list,flat_v)result` STRIP_ASSUME_TAC)) THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r':(flat_v list,flat_v)result` (cases "result")) THEN
  STRIP_TAC THEN FLATPAUX_SUBST_VAR_TAC "r'" THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; result_rel_Rval; result_rel_Rerr1]) THEN
  FLATPAUX_SPLIT_ASM_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  FLATPAUX_SUBST_VARS_TAC THEN FLATPAUX_SING_RV_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL2; HD]) THEN
  ASM_REWRITE_TAC[HD] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD] THENL
  [REWRITE_TAC[FLATPAUX_env_opt_bind] THEN
   MP_TAC(SPECL [`env:(flat_v)flat_environment`; `env2:(flat_v)flat_environment`;
     `s':(C,FFI)flat_state`; `t2a:(C,FFI)flat_state`; `y':flat_v`; `y:flat_v`;
     `pes:(flat_pat#flat_exp)list`; `ps2:(flat_pat#flat_exp)list`; `j:num`; `sgp:bool`;
     `N:num`; `cfg:flat_pattern_config`; `x:tra`; `MAX i1 j + 2`;
     `flat_Raise x (flat_Con x (SOME (bind_tag,NONE)) [])`;
     `flat_bind_exn_v`; `flat_Conv (SOME (bind_tag,NONE)) []`;
     `t1:(C,FFI)flat_state`; `r1:(flat_v list,flat_v)result`] FLATPAUX_compile_pats_sim) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MAP_EVERY X_GEN_TAC [`env1':(varN#flat_v)list`; `p1:flat_pat`; `e1':flat_exp`] THEN
     STRIP_TAC THEN
     REMOVE_THEN "ih2" (MP_TAC o SPECL [`[y']:flat_v list`; `p1:flat_pat`;
       `env1':(varN#flat_v)list`; `s':(C,FFI)flat_state`; `e1':flat_exp`]) THEN
     ASM_REWRITE_TAC[HD];
     REWRITE_TAC[flat_evaluate_def; REVERSE] THEN CASE_REWRITE_TAC[] THEN
     REWRITE_TAC[HD; REVERSE];
     REWRITE_TAC[flat_bind_exn_v_def; v_rel_l_cases] THEN
     EXISTS_TAC `[]:flat_v list` THEN REWRITE_TAC[ALL2]];
    REWRITE_TAC[]];
   REPEAT FLATPAUX_EXISTS_EQ_TAC THEN ASM_REWRITE_TAC[result_rel_def]]);;
let FLATPAUX_result_cases3 = prove
 (`!r:(A,B)result. (?v. r = Rval v) \/ (?e. r = Rerr (Rraise e)) \/
                   (?a. r = Rerr (Rabort a))`,
  MESON_TAC[cases "result"; cases "error_result"]);;

let FLATPAUX_ce_handle = prove
 (FLATPAUX_ce_tm 4,
  MAP_EVERY X_GEN_TAC [`env:(flat_v)flat_environment`; `s:(C,FFI)flat_state`;
    `x:tra`; `e:flat_exp`; `pes:(flat_pat#flat_exp)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN
  FLATPAUX_TRIPLE_TAC `flat_pattern_compile_exp cfg e` (`i1:num`,`sg1:bool`,`y1:flat_exp`) THEN
  FLATPAUX_TRIPLE_TAC `compile_match cfg pes`
    (`j:num`,`sgp:bool`,`ps2:(flat_pat#flat_exp)list`) THEN
  REWRITE_TAC[flat_pattern_compile_exp_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FLATPAUX_SPLIT_ASM_TAC THEN FLATPAUX_SUBST_VARS_TAC THEN
  SUBGOAL_THEN `i1 < N /\ j + 2 <= MAX i1 j + 2 /\ MAX i1 j + 2 <= N` STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `MAX (MAX i1 j + 2) 0 < N` THEN REWRITE_TAC[MAX] THEN
   REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FLATPAUX_compile_exps_sing) THEN
  FLATPAUX_EVAL_SPLIT_TAC `flat_evaluate env (s:(C,FFI)flat_state) [e]` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `flat_Handle`)) (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "flat_evaluate" with _ -> false))
      (concl th))) THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_TAC THEN FLATPAUX_NOT_TE_TAC `r':(flat_v list,flat_v)result` THEN
  FLATPAUX_CE_IH_TAC "ih" `[e:flat_exp]` `s':(C,FFI)flat_state`
    `r':(flat_v list,flat_v)result` `N:num` `env2:(flat_v)flat_environment`
    `s2:(C,FFI)flat_state` THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2a:(C,FFI)flat_state` (X_CHOOSE_THEN
    `r2a:(flat_v list,flat_v)result` STRIP_ASSUME_TAC)) THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs:flat_v list` SUBST_ALL_TAC)
    (DISJ_CASES_THEN2 (X_CHOOSE_THEN `v1:flat_v` SUBST_ALL_TAC)
                      (X_CHOOSE_THEN `ab:abort` SUBST_ALL_TAC))
    (ISPEC `r':(flat_v list,flat_v)result` FLATPAUX_result_cases3) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; result_rel_Rval; result_rel_Rerr1;
                              exc_rel_raise1; exc_rel_type_error1]) THEN
  FLATPAUX_SPLIT_ASM_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  FLATPAUX_SUBST_VARS_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
  [REWRITE_TAC[PAIR_EQ] THEN REPEAT FLATPAUX_EXISTS_EQ_TAC THEN
   ASM_REWRITE_TAC[result_rel_def];
   REWRITE_TAC[pmatch_rows_def; flat_pmatch_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[flat_pat_bindings_def; ALL_DISTINCT; MEM; APPEND] THEN
   MP_TAC(SPECL [`env:(flat_v)flat_environment`; `env2:(flat_v)flat_environment`;
     `s':(C,FFI)flat_state`; `t2a:(C,FFI)flat_state`; `v1:flat_v`; `v':flat_v`;
     `pes:(flat_pat#flat_exp)list`; `ps2:(flat_pat#flat_exp)list`; `j:num`; `sgp:bool`;
     `N:num`; `cfg:flat_pattern_config`; `x:tra`; `MAX i1 j + 2`;
     `flat_Raise x (Var_local x (enc_num_to_name (MAX i1 j + 2)))`;
     `v1:flat_v`; `v':flat_v`;
     `t1:(C,FFI)flat_state`; `r1:(flat_v list,flat_v)result`] FLATPAUX_compile_pats_sim) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
    [MAP_EVERY X_GEN_TAC [`env1':(varN#flat_v)list`; `p1:flat_pat`; `e1':flat_exp`] THEN
     STRIP_TAC THEN
     REMOVE_THEN "ih2" (MP_TAC o SPECL [`v1:flat_v`; `p1:flat_pat`;
       `env1':(varN#flat_v)list`; `s':(C,FFI)flat_state`; `e1':flat_exp`]) THEN
     ASM_REWRITE_TAC[];
     REWRITE_TAC[flat_evaluate_def; flat_environment_INFO.ri_accfupds; K_THM;
                 ALOOKUP_DEF] THEN
     CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD]];
    REWRITE_TAC[]];
   REWRITE_TAC[PAIR_EQ] THEN REPEAT FLATPAUX_EXISTS_EQ_TAC THEN
   ASM_REWRITE_TAC[result_rel_def; exc_rel_def]]);;

let FLATPAUX_ce_all =
  MATCH_MP FLATPAUX_ce_ind
    (end_itlist CONJ [FLATPAUX_ce_nil; FLATPAUX_ce_cons; FLATPAUX_ce_lit; FLATPAUX_ce_raise;
       FLATPAUX_ce_handle; FLATPAUX_ce_con_none; FLATPAUX_ce_con_some; FLATPAUX_ce_var;
       FLATPAUX_ce_fun; FLATPAUX_ce_app; FLATPAUX_ce_if; FLATPAUX_ce_mat; FLATPAUX_ce_let;
       FLATPAUX_ce_letrec; FLATPAUX_ce_dec; FLATPAUX_ce_decs_nil; FLATPAUX_ce_decs_cons]);;

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
  CONJ_TAC THEN REPEAT GEN_TAC THENL
  [MATCH_ACCEPT_TAC(SPEC_ALL(CONJUNCT1 FLATPAUX_ce_all));
   MATCH_ACCEPT_TAC(SPEC_ALL(CONJUNCT2(CONJUNCT2 FLATPAUX_ce_all)))]);;

let compile_decs_eval_sim = prove
 (`install_conf_rel cfg (ic1:(C)install_config) ic2
   ==> flat_eval_sim (ffi:(FFI)ffi_state) prog prog' ic1 ic2
         (\decs decs'. MAP (compile_dec cfg2) decs = decs') F`,
  REWRITE_TAC[flat_eval_sim_def] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES] THEN
  MP_TAC(SPECL [`flat_initial_state (ffi:(FFI)ffi_state) k (ic1:(C)install_config)`;
     `prog:flat_exp list`;
     `flat_initial_state (ffi:(FFI)ffi_state) k (ic2:(C)install_config)`;
     `s2:(C,FFI)flat_state`; `cfg2:flat_pattern_config`; `prog':flat_exp list`;
     `res1:((flat_v)error_result)option`]
     (INST [`cfg:flat_pattern_config`,`s_cfg:flat_pattern_config`]
        (CONJUNCT2 compile_exps_evaluate))) THEN
  ASM_SIMP_TAC[flat_patternProof_state_rel_initial_state] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)flat_state` (X_CHOOSE_THEN
    `res2:((flat_v)error_result)option` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`res2:((flat_v)error_result)option`; `t2:(C,FFI)flat_state`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[flat_patternProof_state_rel_def]; ALL_TAC] THEN
  UNDISCH_TAC `OPTREL (exc_rel flat_patternProof_v_rel) res1 res2` THEN
  STRUCT_CASES_TAC(ISPEC `res1:((flat_v)error_result)option` (cases "option")) THEN
  REWRITE_TAC[OPTREL_NONE; OPTREL_SOME; option_DISTINCT; option_INJ] THEN
  STRUCT_CASES_TAC(ISPEC `a:(flat_v)error_result` (cases "error_result")) THEN
  REWRITE_TAC[exc_rel_raise1; exc_rel_type_error1; distinctness "error_result";
              injectivity "error_result"] THEN
  MESON_TAC[]);;

let compile_decs_semantics = prove
 (`install_conf_rel cfg (ic1:(C)install_config) ic2 /\
   ~(flat_semantics ic1 (ffi:(FFI)ffi_state) prog = Fail)
   ==> flat_semantics ic1 ffi prog =
       flat_semantics ic2 ffi (MAP (compile_dec cfg1) prog)`,
  STRIP_TAC THEN
  MP_TAC(ISPECL [`ffi:(FFI)ffi_state`; `prog:flat_exp list`;
    `MAP (compile_dec cfg1) prog`; `ic1:(C)install_config`; `ic2:(C)install_config`;
    `\decs decs'. MAP (compile_dec cfg1) decs = (decs':flat_exp list)`]
    flat_IMP_semantics_eq) THEN
  REWRITE_TAC[MATCH_MP compile_decs_eval_sim
    (ASSUME `install_conf_rel cfg (ic1:(C)install_config) ic2`)] THEN
  ASM_REWRITE_TAC[]);;

(* set_globals and esgc properties *)

(* local helpers: SmartIf is one of its branches or an If; flat_Bool       *)

let FLATPAUX_SmartIf_P = prove
 (`!(P:flat_exp->bool) t e p q.
     P p /\ P q /\ P (flat_If t e p q) ==> P (SmartIf t e p q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SmartIf_thm] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let FLATPAUX_SMARTIF_TAC tm =
  MATCH_MP_TAC (BETA_RULE (ISPEC tm FLATPAUX_SmartIf_P));;

let FLATPAUX_BAG_TAC : tactic =
  let rws = [flat_set_globals_def; SUB_BAG_LEQ; BAG_UNION; EMPTY_BAG_alt; FUN_EQ_THM] in
  RULE_ASSUM_TAC(REWRITE_RULE rws) THEN REWRITE_TAC rws THEN
  (X_GEN_TAC `bx:num` ORELSE ALL_TAC) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall (concl th) then MP_TAC (SPEC `bx:num` th) else failwith "bag")) THEN
  ARITH_TAC;;

let set_globals_decode_pos = prove
 (`!p exp. flat_set_globals exp = EMPTY_BAG
           ==> flat_set_globals (decode_pos t exp p) = EMPTY_BAG`,
  MATCH_MP_TAC position_INDUCT THEN
  SIMP_TAC[decode_pos_def; flat_set_globals_def; flat_op_gbag_def; BAG_UNION_EMPTY]);;

let set_globals_decode_test = prove
 (`flat_set_globals exp = EMPTY_BAG
   ==> flat_set_globals (flat_pattern_decode_test t d exp) = EMPTY_BAG`,
  STRUCT_CASES_TAC(ISPEC `d:dTest` (cases "dTest")) THEN
  SIMP_TAC[flat_pattern_decode_test_def; flat_set_globals_def; flat_op_gbag_def;
           BAG_UNION_EMPTY]);;

let set_globals_decode_guard = prove
 (`flat_set_globals exp = EMPTY_BAG
   ==> flat_set_globals (decode_guard t exp gd) = EMPTY_BAG`,
  DISCH_TAC THEN SPEC_TAC(`gd:dGuard`,`gd:dGuard`) THEN
  MATCH_MP_TAC dGuard_INDUCT THEN
  ASM_SIMP_TAC[decode_guard_def; flat_set_globals_def; flat_Bool_def; flat_op_gbag_def;
               BAG_UNION_EMPTY; set_globals_decode_test; set_globals_decode_pos] THEN
  REPEAT STRIP_TAC THEN
  FLATPAUX_SMARTIF_TAC `\e. flat_set_globals e = EMPTY_BAG` THEN
  ASM_REWRITE_TAC[flat_set_globals_def; BAG_UNION_EMPTY]);;

let set_globals_decode_dtree_empty = prove
 (`flat_set_globals x = EMPTY_BAG /\ flat_set_globals dflt = EMPTY_BAG /\
   ALL (\y. flat_set_globals y = EMPTY_BAG) (toList br_spt)
   ==> flat_set_globals (decode_dtree t br_spt x dflt dtree) = EMPTY_BAG`,
  STRIP_TAC THEN SPEC_TAC(`dtree:dTree`,`dtree:dTree`) THEN
  MATCH_MP_TAC dTree_INDUCT THEN REPEAT CONJ_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[decode_dtree_def] THEN
   MP_TAC(ISPEC `lookup a (br_spt:(flat_exp)spt)` (cases "option")) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   UNDISCH_TAC `ALL (\y. flat_set_globals y = EMPTY_BAG) (toList (br_spt:(flat_exp)spt))` THEN
   REWRITE_TAC[GSYM ALL_MEM; MEM_toList] THEN ASM_MESON_TAC[];
   ASM_REWRITE_TAC[decode_dtree_def];
   REWRITE_TAC[decode_dtree_def; flat_set_globals_def];
   REPEAT STRIP_TAC THEN REWRITE_TAC[decode_dtree_def] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   FLATPAUX_SMARTIF_TAC `\e. flat_set_globals e = EMPTY_BAG` THEN
   ASM_SIMP_TAC[flat_set_globals_def; BAG_UNION_EMPTY; set_globals_decode_guard]]);;

let inv_on_FOLDR = prove
 (`!f:B->C. (!x v. MEM (x:A) xs ==> f (g x v) = f v) ==> f (ITLIST g xs v) = f v`,
  GEN_TAC THEN SPEC_TAC(`xs:A list`,`xs:A list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ITLIST; MEM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
  [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN ASM_MESON_TAC[]);;

let FLATPAUX_cpb_ITLIST = prove
 (`!(L:((num#mlstring)#(flat_pat#num#flat_exp))list) tr x e.
     (flat_set_globals x = EMPTY_BAG
      ==> flat_set_globals (ITLIST (\((j,nm),r) exp.
             flat_Let tr (SOME nm) (flat_App tr (flat_El j) [x]) exp) L e) =
          flat_set_globals e) /\
     (flat_esgc_free x /\ flat_esgc_free e
      ==> flat_esgc_free (ITLIST (\((j,nm),r) exp.
             flat_Let tr (SOME nm) (flat_App tr (flat_El j) [x]) exp) L e)) /\
     (no_Mat x /\ no_Mat e
      ==> no_Mat (ITLIST (\((j,nm),r) exp.
             flat_Let tr (SOME nm) (flat_App tr (flat_El j) [x]) exp) L e))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST] THEN
  SPEC_TAC(`h:(num#mlstring)#(flat_pat#num#flat_exp)`,
           `h:(num#mlstring)#(flat_pat#num#flat_exp)`) THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_SIMP_TAC[flat_set_globals_def; flat_esgc_free_def; no_Mat_def; ALL;
               BAG_UNION_EMPTY; flat_op_gbag_def]);;

let FLATPAUX_cpb_ALL_jnms = prove
 (`!(l:(num#flat_pat)list) t i.
     ALL (\(p:flat_pat,k:num,e). flat_set_globals e = EMPTY_BAG)
       (MAP SND (MAP (\(j,p). (j,enc_num_to_name (i + 1 + j)),
                       p,i + 1 + j,Var_local t (enc_num_to_name (i + 1 + j))) l)) /\
     ALL (\(p:flat_pat,k:num,e). flat_esgc_free e)
       (MAP SND (MAP (\(j,p). (j,enc_num_to_name (i + 1 + j)),
                       p,i + 1 + j,Var_local t (enc_num_to_name (i + 1 + j))) l)) /\
     ALL (\(p:flat_pat,k:num,e). no_Mat e)
       (MAP SND (MAP (\(j,p). (j,enc_num_to_name (i + 1 + j)),
                       p,i + 1 + j,Var_local t (enc_num_to_name (i + 1 + j))) l))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL] THEN
  SPEC_TAC(`h:num#flat_pat`,`h:num#flat_pat`) THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_REWRITE_TAC[SND; flat_set_globals_def; flat_esgc_free_def; no_Mat_def]);;

let FLATPAUX_cpb_props = prove
 (`!t i n_bindings exp.
     (ALL (\(p:flat_pat,k:num,e). flat_set_globals e = EMPTY_BAG) n_bindings
      ==> flat_set_globals (SND (compile_pat_bindings t i n_bindings exp)) =
          flat_set_globals exp) /\
     (flat_esgc_free exp /\ ALL (\(p:flat_pat,k:num,e). flat_esgc_free e) n_bindings
      ==> flat_esgc_free (SND (compile_pat_bindings t i n_bindings exp))) /\
     (no_Mat exp /\ ALL (\(p:flat_pat,k:num,e). no_Mat e) n_bindings
      ==> no_Mat (SND (compile_pat_bindings t i n_bindings exp)))`,
  MATCH_MP_TAC compile_pat_bindings_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  REWRITE_TAC[compile_pat_bindings_def; ALL] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT IL1AUX_PAIRARG_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SND; ALL; ALL_APPEND; FLATPAUX_cpb_ALL_jnms]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV GEN_BETA_CONV)) THEN
  REWRITE_TAC[SND] THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REPEAT CONJ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[flat_set_globals_def; flat_esgc_free_def; no_Mat_def; ALL;
               BAG_UNION_EMPTY; flat_op_gbag_def; FLATPAUX_cpb_ITLIST]);;

let set_globals_compile_pat_bindings = prove
 (`!t i n_bindings exp.
     ALL (\(p:flat_pat,k:num,v_exp). flat_set_globals v_exp = EMPTY_BAG) n_bindings
     ==> flat_set_globals (SND (compile_pat_bindings t i n_bindings exp)) =
         flat_set_globals exp`,
  MESON_TAC[FLATPAUX_cpb_props]);;

(* local helper: the three properties of the expressions of a MAPi of El *)

let FLATPAUX_MAPi_El_props = prove
 (`!t x (ps:flat_pat list).
     (flat_set_globals x = EMPTY_BAG
      ==> ALL (\v. flat_set_globals (SND v) = EMPTY_BAG)
            (MAPi (\i p. p,flat_App t (flat_El i) [x]) ps)) /\
     (flat_esgc_free x
      ==> ALL flat_esgc_free (MAP SND (MAPi (\i p. p,flat_App t (flat_El i) [x]) ps))) /\
     (no_Mat x ==> ALL (no_Mat o SND) (MAPi (\i p. p,flat_App t (flat_El i) [x]) ps))`,
  REWRITE_TAC[GSYM ALL_MEM; MEM_MAPi; MEM_MAP] THEN REPEAT STRIP_TAC THEN
  FLATPAUX_SUBST_VARS_TAC THEN
  ASM_REWRITE_TAC[o_THM; SND; flat_set_globals_def; flat_esgc_free_def; no_Mat_def; ALL;
                  BAG_UNION_EMPTY; flat_op_gbag_def]);;

(* local helper: SmartIf_P at the predicate of the goal *)

let FLATPAUX_SMARTIF_GOAL_TAC : tactic = fun (asl,w as g) ->
  let s = find_term (fun t -> is_comb t && (let f,args = strip_comb t in
            is_const f && fst(dest_const f) = "SmartIf" && length args = 4)) w in
  let v = genvar `:flat_exp` in
  let p = mk_abs(v, subst [v,s] w) in
  MATCH_MP_TAC (BETA_RULE (ISPEC p FLATPAUX_SmartIf_P)) g;;

(* local helper: the three properties of naive_pattern_match *)

let FLATPAUX_npm_props = prove
 (`!t xs.
     (ALL (\v. flat_set_globals (SND v) = EMPTY_BAG) xs
      ==> flat_set_globals (naive_pattern_match t xs) = EMPTY_BAG) /\
     (ALL flat_esgc_free (MAP SND xs) ==> flat_esgc_free (naive_pattern_match t xs)) /\
     (ALL (no_Mat o SND) xs ==> no_Mat (naive_pattern_match t xs))`,
  MATCH_MP_TAC naive_pattern_match_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  REWRITE_TAC[naive_pattern_match_def; ALL; MAP; ALL_APPEND; MAP_APPEND; o_THM] THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; MAP; ALL_APPEND; MAP_APPEND; o_THM]) THEN
  REPEAT CONJ_TAC THEN TRY STRIP_TAC THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[FLATPAUX_MAPi_El_props; flat_set_globals_def; flat_esgc_free_def;
                   no_Mat_def; ALL; BAG_UNION_EMPTY; flat_op_gbag_def] THEN NO_TAC) THEN
  TRY FLATPAUX_SMARTIF_GOAL_TAC THEN
  ASM_SIMP_TAC[flat_set_globals_def; flat_esgc_free_def; no_Mat_def; ALL; flat_Bool_def;
               BAG_UNION_EMPTY; flat_op_gbag_def; FLATPAUX_MAPi_El_props]);;

let set_globals_naive_pattern_match = prove
 (`!t xs. ALL (\v. flat_set_globals (SND v) = EMPTY_BAG) xs
          ==> flat_set_globals (naive_pattern_match t xs) = EMPTY_BAG`,
  MESON_TAC[FLATPAUX_npm_props]);;

let set_globals_naive_pattern_matches = prove
 (`flat_set_globals x = EMPTY_BAG
   ==> SUB_BAG (flat_set_globals (naive_pattern_matches t x ps dflt))
               (flat_elist_globals (CONS dflt (MAP SND ps)))`,
  DISCH_TAC THEN SPEC_TAC(`ps:(flat_pat#flat_exp)list`,`ps:(flat_pat#flat_exp)list`) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[naive_pattern_matches_def; MAP; flat_set_globals_def; BAG_UNION_EMPTY;
              SUB_BAG_REFL] THEN
  SPEC_TAC(`h:flat_pat#flat_exp`,`h:flat_pat#flat_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; naive_pattern_matches_def; MAP; SND] THEN
  MAP_EVERY X_GEN_TAC [`p:flat_pat`; `y:flat_exp`] THEN
  SUBGOAL_THEN `flat_set_globals (naive_pattern_match t [(p:flat_pat,x:flat_exp)]) =
                EMPTY_BAG` ASSUME_TAC THENL
  [MATCH_MP_TAC set_globals_naive_pattern_match THEN ASM_REWRITE_TAC[ALL; SND];
   ALL_TAC] THEN
  REWRITE_TAC[SmartIf_thm] THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[flat_set_globals_def; BAG_UNION_EMPTY] THEN
  FLATPAUX_BAG_TAC);;

let set_toList_fromList = prove
 (`set_of_list (toList (fromList (xs:A list))) = set_of_list xs`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_toList; lookup_fromList; MEM_EXISTS_EL] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
  [EXISTS_TAC `k:num` THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
   REWRITE_TAC[option_DISTINCT; option_INJ] THEN ASM_MESON_TAC[];
   EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[option_INJ]]);;

(* local helper: the branches of compile_pats keep the globals of the       *)
(* right-hand sides                                                          *)

let FLATPAUX_branches_set_globals = prove
 (`!ps. flat_set_globals x = EMPTY_BAG
        ==> flat_elist_globals (MAP (compile_pat_rhs t N x) ps) =
            flat_elist_globals (MAP SND ps)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; flat_set_globals_def] THEN
  SPEC_TAC(`h:flat_pat#flat_exp`,`h:flat_pat#flat_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; compile_pat_rhs_def; SND] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC set_globals_compile_pat_bindings THEN
  REWRITE_TAC[ALL] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[]);;

let set_globals_compile_pats = prove
 (`(~naive ==> flat_elist_globals (CONS dflt (MAP SND ps)) = EMPTY_BAG) /\
   flat_set_globals x = EMPTY_BAG
   ==> SUB_BAG (flat_set_globals (compile_pats cfg naive t N x dflt ps))
               (flat_elist_globals (CONS dflt (MAP SND ps)))`,
  STRIP_TAC THEN REWRITE_TAC[compile_pats_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THENL
  [MATCH_MP_TAC SUB_BAG_TRANS THEN
   EXISTS_TAC `flat_elist_globals (CONS dflt (MAP SND (ZIP (MAP FST ps)
                 (MAP (compile_pat_rhs t N x) (ps:(flat_pat#flat_exp)list)))))` THEN
   ASM_SIMP_TAC[set_globals_naive_pattern_matches] THEN
   SIMP_TAC[MAP_SND_ZIP; LENGTH_MAP] THEN
   ASM_SIMP_TAC[flat_set_globals_def; FLATPAUX_branches_set_globals; SUB_BAG_REFL];
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[SUB_BAG_EMPTY] THEN
  MATCH_MP_TAC set_globals_decode_dtree_empty THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_set_globals_def; BAG_UNION_EMPTY]) THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM; GSYM IN_SET_OF_LIST; set_toList_fromList] THEN
  REWRITE_TAC[IN_SET_OF_LIST; MEM_MAP; EXISTS_PAIR_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[compile_pat_rhs_def] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhs o rand) set_globals_compile_pat_bindings
                            (lhs w))) THEN
  REWRITE_TAC[ALL] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o check (is_conj o concl)) THEN
  REWRITE_TAC[elist_globals_eq_empty; MEM_MAP; EXISTS_PAIR_THM] THEN
  ASM_MESON_TAC[SND]);;

let SUB_BAG_2 = prove
 (`SUB_BAG x (y:A->num) /\ SUB_BAG x' y'
   ==> SUB_BAG (BAG_UNION x x') (BAG_UNION y y')`,
  REWRITE_TAC[SUB_BAG_LEQ; BAG_UNION] THEN MESON_TAC[LE_ADD2]);;

(* local helper: compile_pats with the compiled rows of compile_match *)

let FLATPAUX_cp_bag = prove
 (`compile_match cfg ps = (j,sgp,ps2) /\
   SUB_BAG (flat_elist_globals (MAP SND ps2)) (flat_elist_globals (MAP SND ps)) /\
   flat_set_globals dflt = EMPTY_BAG /\ flat_set_globals x = EMPTY_BAG
   ==> SUB_BAG (flat_set_globals (compile_pats cfg sgp t k x dflt ps2))
               (flat_elist_globals (MAP SND ps))`,
  STRIP_TAC THEN MATCH_MP_TAC SUB_BAG_TRANS THEN
  EXISTS_TAC `flat_elist_globals (CONS dflt (MAP SND (ps2:(flat_pat#flat_exp)list)))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC set_globals_compile_pats THEN ASM_REWRITE_TAC[] THEN
   FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (CONJUNCT2(CONJUNCT2
     compile_exp_set_globals_tup)) th]) THEN
   DISCH_TAC THEN
   UNDISCH_TAC `SUB_BAG (flat_elist_globals (MAP SND (ps2:(flat_pat#flat_exp)list)))
                  (flat_elist_globals (MAP SND (ps:(flat_pat#flat_exp)list)))` THEN
   ASM_REWRITE_TAC[SUB_BAG_EMPTY; flat_set_globals_def; BAG_UNION_EMPTY];
   ASM_REWRITE_TAC[flat_set_globals_def; BAG_UNION_EMPTY]]);;

let FLATPAUX_letrec_bag = prove
 (`!fs:(varN#varN#flat_exp)list.
     (!a b c. MEM (a,b,c) fs
              ==> SUB_BAG (flat_set_globals (SND (SND (flat_pattern_compile_exp cfg c))))
                          (flat_set_globals c))
     ==> SUB_BAG (flat_elist_globals (MAP (SND o SND)
                    (MAP (\(n,m,e). (n,m,SND (SND (flat_pattern_compile_exp cfg e)))) fs)))
                 (flat_elist_globals (MAP (SND o SND) fs))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; flat_set_globals_def; SUB_BAG_REFL] THEN
  SPEC_TAC(`h:varN#varN#flat_exp`,`h:varN#varN#flat_exp`) THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN GEN_TAC THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN GEN_TAC THEN GEN_TAC THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[MEM; o_THM; SND; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUB_BAG_2 THEN CONJ_TAC THENL
  [ASM_MESON_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

(* local helper: discharges the guards x = (i,sg,y) of instantiated      *)
(* induction hypotheses                                                   *)

let FLATPAUX_UNGUARD_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    let vs,body = strip_forall c in
    if vs = [] || not (is_imp body) then failwith "unguard" else
    let eqs = conjuncts (lhand body) in
    let inst = map dest_eq eqs in
    if not (forall (fun (l,r) -> mem r vs) inst) ||
       not (forall (fun v -> exists (fun (l,r) -> r = v) inst) vs)
    then failwith "unguard" else
    let th' = SPECL (map (fun v -> fst (find (fun (l,r) -> r = v) inst)) vs) th in
    ASSUME_TAC (MP th' (EQT_ELIM (REWRITE_CONV[] (lhand (concl th')))))));;

let FLATPAUX_ces_fun = prove
 (`(!cfg exp. SUB_BAG (flat_set_globals (SND (SND (flat_pattern_compile_exp cfg exp))))
                      (flat_set_globals exp)) /\
   (!cfg exps. SUB_BAG (flat_elist_globals (SND (SND (flat_pattern_compile_exps cfg exps))))
                       (flat_elist_globals exps)) /\
   (!cfg m. SUB_BAG (flat_elist_globals (MAP SND (SND (SND (compile_match cfg m)))))
                    (flat_elist_globals (MAP SND m)))`,
  MATCH_MP_TAC flat_pattern_compile_exp_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  REWRITE_TAC[flat_pattern_compile_exp_def] THEN
  REPEAT IL1AUX_PAIRARG_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN REWRITE_TAC[FST; SND] THEN
  FLATPAUX_UNGUARD_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[elist_globals_REVERSE]) THEN
  REWRITE_TAC[flat_set_globals_def; elist_globals_REVERSE; MAP; BAG_UNION_EMPTY;
              FLATPAUX_letrec_compile; SmartIf_thm] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[flat_set_globals_def] THEN
  FIRST [FLATPAUX_BAG_TAC;
         MATCH_MP_TAC SUB_BAG_2 THEN CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          FIRST [MATCH_MP_TAC FLATPAUX_letrec_bag THEN FIRST_ASSUM ACCEPT_TAC;
                 FIRST_ASSUM(fun th -> MATCH_MP_TAC (REWRITE_RULE[IMP_IMP]
                   (MATCH_MP (REWRITE_RULE[IMP_CONJ] FLATPAUX_cp_bag) th))) THEN
                 ASM_REWRITE_TAC[flat_set_globals_def]]]]);;

let compile_exp_set_globals = prove
 (`(!cfg exp N sg exp'. flat_pattern_compile_exp cfg exp = (N,sg,exp')
      ==> SUB_BAG (flat_set_globals exp') (flat_set_globals exp)) /\
   (!cfg exps N sg exps'. flat_pattern_compile_exps cfg exps = (N,sg,exps')
      ==> SUB_BAG (flat_elist_globals exps') (flat_elist_globals exps)) /\
   (!cfg m N sg m'. compile_match cfg m = (N,sg,m')
      ==> SUB_BAG (flat_elist_globals (MAP SND m')) (flat_elist_globals (MAP SND m)))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
  [MP_TAC(SPEC_ALL (CONJUNCT1 FLATPAUX_ces_fun));
   MP_TAC(SPEC_ALL (CONJUNCT1 (CONJUNCT2 FLATPAUX_ces_fun)));
   MP_TAC(SPEC_ALL (CONJUNCT2 (CONJUNCT2 FLATPAUX_ces_fun)))] THEN
  ASM_REWRITE_TAC[SND]);;

let flat_patternProof_FST_SND_EQ_CASE = prove
 (`FST = (\(a:A,b:B). a) /\ SND = (\(a:A,b:B). b)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; FST; SND]);;

let flat_patternProof_compile_decs_elist_globals = prove
 (`!decs. SUB_BAG (flat_elist_globals (MAP (compile_dec cfg) decs))
                  (flat_elist_globals decs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; flat_set_globals_def; SUB_BAG_REFL] THEN
  MATCH_MP_TAC SUB_BAG_2 THEN ASM_REWRITE_TAC[compile_dec_def] THEN
  REWRITE_TAC[FLATPAUX_ces_fun]);;

let esgc_free_decode_pos = prove
 (`!p exp. flat_esgc_free exp ==> flat_esgc_free (decode_pos t exp p)`,
  MATCH_MP_TAC position_INDUCT THEN
  SIMP_TAC[decode_pos_def; flat_esgc_free_def; ALL]);;

let esgc_free_decode_test = prove
 (`flat_esgc_free exp ==> flat_esgc_free (flat_pattern_decode_test t d exp)`,
  STRUCT_CASES_TAC(ISPEC `d:dTest` (cases "dTest")) THEN
  SIMP_TAC[flat_pattern_decode_test_def; flat_esgc_free_def; ALL]);;

let esgc_free_decode_guard = prove
 (`flat_esgc_free exp ==> flat_esgc_free (decode_guard t exp gd)`,
  DISCH_TAC THEN SPEC_TAC(`gd:dGuard`,`gd:dGuard`) THEN
  MATCH_MP_TAC dGuard_INDUCT THEN
  ASM_SIMP_TAC[decode_guard_def; flat_esgc_free_def; flat_Bool_def; ALL;
               esgc_free_decode_test; esgc_free_decode_pos] THEN
  REPEAT STRIP_TAC THEN FLATPAUX_SMARTIF_GOAL_TAC THEN
  ASM_REWRITE_TAC[flat_esgc_free_def; flat_Bool_def; ALL]);;

let esgc_free_decode_dtree = prove
 (`flat_esgc_free v_exp /\ flat_esgc_free dflt /\
   ALL (\y. flat_esgc_free y) (toList br_spt)
   ==> flat_esgc_free (decode_dtree t br_spt v_exp dflt dtree)`,
  STRIP_TAC THEN SPEC_TAC(`dtree:dTree`,`dtree:dTree`) THEN
  MATCH_MP_TAC dTree_INDUCT THEN REPEAT CONJ_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[decode_dtree_def] THEN
   MP_TAC(ISPEC `lookup a (br_spt:(flat_exp)spt)` (cases "option")) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   UNDISCH_TAC `ALL (\y. flat_esgc_free y) (toList (br_spt:(flat_exp)spt))` THEN
   REWRITE_TAC[GSYM ALL_MEM; MEM_toList] THEN ASM_MESON_TAC[];
   ASM_REWRITE_TAC[decode_dtree_def];
   REWRITE_TAC[decode_dtree_def; flat_esgc_free_def];
   REPEAT STRIP_TAC THEN REWRITE_TAC[decode_dtree_def] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   FLATPAUX_SMARTIF_GOAL_TAC THEN
   ASM_SIMP_TAC[flat_esgc_free_def; esgc_free_decode_guard]]);;

let esgc_free_compile_pat_bindings = prove
 (`!t i n_bindings exp.
     flat_esgc_free exp /\
     ALL (\(p:flat_pat,k:num,v_exp). flat_esgc_free v_exp) n_bindings
     ==> flat_esgc_free (SND (compile_pat_bindings t i n_bindings exp))`,
  MESON_TAC[FLATPAUX_cpb_props]);;

let esgc_free_naive_pattern_match = prove
 (`!t xs. ALL flat_esgc_free (MAP SND xs)
          ==> flat_esgc_free (naive_pattern_match t xs)`,
  MESON_TAC[FLATPAUX_npm_props]);;

let esgc_free_naive_pattern_matches = prove
 (`!t x xs dflt. ALL flat_esgc_free (CONS x (CONS dflt (MAP SND xs)))
                 ==> flat_esgc_free (naive_pattern_matches t x xs dflt)`,
  MATCH_MP_TAC naive_pattern_matches_ind THEN
  REWRITE_TAC[naive_pattern_matches_def; ALL; MAP] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN FLATPAUX_SMARTIF_GOAL_TAC THEN
  ASM_SIMP_TAC[flat_esgc_free_def; esgc_free_naive_pattern_match; ALL; MAP]);;

let esgc_free_compile_pats = prove
 (`flat_esgc_free dflt /\ ALL flat_esgc_free (MAP SND ps)
   ==> flat_esgc_free (compile_pats cfg naive t N (Var_local t' nm) dflt ps)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `ALL flat_esgc_free (MAP (compile_pat_rhs t N (Var_local t' nm)) ps)`
    ASSUME_TAC THENL
  [UNDISCH_TAC `ALL flat_esgc_free (MAP SND (ps:(flat_pat#flat_exp)list))` THEN
   SPEC_TAC(`ps:(flat_pat#flat_exp)list`,`ps:(flat_pat#flat_exp)list`) THEN
   LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL] THEN
   SPEC_TAC(`h:flat_pat#flat_exp`,`h:flat_pat#flat_exp`) THEN
   REWRITE_TAC[FORALL_PAIR_THM; compile_pat_rhs_def; SND] THEN
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
   MATCH_MP_TAC esgc_free_compile_pat_bindings THEN
   REWRITE_TAC[ALL] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
   ASM_REWRITE_TAC[flat_esgc_free_def];
   ALL_TAC] THEN
  REWRITE_TAC[compile_pats_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THENL
  [MATCH_MP_TAC esgc_free_naive_pattern_matches THEN
   ASM_SIMP_TAC[ALL; MAP_SND_ZIP; LENGTH_MAP; flat_esgc_free_def];
   MATCH_MP_TAC esgc_free_decode_dtree THEN
   ASM_REWRITE_TAC[flat_esgc_free_def; GSYM ALL_MEM; GSYM IN_SET_OF_LIST;
                   set_toList_fromList] THEN
   ASM_REWRITE_TAC[IN_SET_OF_LIST; ALL_MEM; ETA_AX]]);;

let FLATPAUX_cef_fun = prove
 (`(!cfg exp. flat_esgc_free exp
              ==> flat_esgc_free (SND (SND (flat_pattern_compile_exp cfg exp)))) /\
   (!cfg exps. ALL flat_esgc_free exps
               ==> ALL flat_esgc_free (SND (SND (flat_pattern_compile_exps cfg exps)))) /\
   (!cfg m. ALL (flat_esgc_free o SND) m
            ==> ALL (flat_esgc_free o SND) (SND (SND (compile_match cfg m))))`,
  MATCH_MP_TAC flat_pattern_compile_exp_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  REWRITE_TAC[flat_pattern_compile_exp_def] THEN
  REPEAT IL1AUX_PAIRARG_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN REWRITE_TAC[FST; SND] THEN
  FLATPAUX_UNGUARD_TAC THEN
  REWRITE_TAC[flat_esgc_free_def; EVERY_REVERSE; ALL; MAP; o_THM; ALL_MAP;
              FLATPAUX_letrec_compile] THEN
  REPEAT STRIP_TAC THEN TRY FLATPAUX_SMARTIF_GOAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL_MAP]) THEN
  ASM_SIMP_TAC[flat_esgc_free_def; EVERY_REVERSE; ALL; MAP; o_THM; ALL_MAP] THEN
  FIRST [MATCH_MP_TAC esgc_free_compile_pats THEN
         ASM_SIMP_TAC[flat_esgc_free_def; ALL; ALL_MAP] THEN NO_TAC;
         MP_TAC(ISPEC `fs:(varN#varN#flat_exp)list` FLATPAUX_letrec_bag) THEN
         REWRITE_TAC[CONJUNCT1 FLATPAUX_ces_fun] THEN ASM_REWRITE_TAC[SUB_BAG_EMPTY] THEN
         NO_TAC;
         FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 compile_exp_set_globals)) THEN
         ASM_REWRITE_TAC[SUB_BAG_EMPTY]]);;

let flat_patternProof_compile_exp_esgc_free = prove
 (`(!cfg exp N sg exp'. flat_pattern_compile_exp cfg exp = (N,sg,exp') /\
                        flat_esgc_free exp
      ==> flat_esgc_free exp') /\
   (!cfg exps N sg exps'. flat_pattern_compile_exps cfg exps = (N,sg,exps') /\
                          ALL flat_esgc_free exps
      ==> ALL flat_esgc_free exps') /\
   (!cfg m N sg m'. compile_match cfg m = (N,sg,m') /\ ALL (flat_esgc_free o SND) m
      ==> ALL (flat_esgc_free o SND) m')`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
  [MP_TAC(SPEC_ALL (CONJUNCT1 FLATPAUX_cef_fun));
   MP_TAC(SPEC_ALL (CONJUNCT1 (CONJUNCT2 FLATPAUX_cef_fun)));
   MP_TAC(SPEC_ALL (CONJUNCT2 (CONJUNCT2 FLATPAUX_cef_fun)))] THEN
  ASM_REWRITE_TAC[SND]);;

let flat_patternProof_compile_decs_esgc_free = prove
 (`!decs. ALL flat_esgc_free decs ==> ALL flat_esgc_free (MAP (compile_dec cfg) decs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[compile_dec_def; FLATPAUX_cef_fun]);;

(* the no_Mat results *)

let naive_pattern_match_no_Mat = prove
 (`!t xs. ALL (no_Mat o SND) xs ==> no_Mat (naive_pattern_match t xs)`,
  MESON_TAC[FLATPAUX_npm_props]);;

let naive_pattern_matches_no_Mat = prove
 (`!t x xs dflt. ALL no_Mat (CONS x (CONS dflt (MAP SND xs)))
                 ==> no_Mat (naive_pattern_matches t x xs dflt)`,
  MATCH_MP_TAC naive_pattern_matches_ind THEN
  REWRITE_TAC[naive_pattern_matches_def; ALL; MAP] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN FLATPAUX_SMARTIF_GOAL_TAC THEN
  ASM_SIMP_TAC[no_Mat_def; naive_pattern_match_no_Mat; ALL; MAP; o_THM]);;

let compile_pat_bindings_no_Mat = prove
 (`!t i n_bindings exp.
     no_Mat exp /\ ALL (\(p:flat_pat,k:num,v_exp). no_Mat v_exp) n_bindings
     ==> no_Mat (SND (compile_pat_bindings t i n_bindings exp))`,
  MESON_TAC[FLATPAUX_cpb_props]);;

let decode_pos_no_Mat = prove
 (`!p exp. no_Mat exp ==> no_Mat (decode_pos t exp p)`,
  MATCH_MP_TAC position_INDUCT THEN
  SIMP_TAC[decode_pos_def; no_Mat_def; ALL]);;

let decode_test_no_Mat = prove
 (`no_Mat exp ==> no_Mat (flat_pattern_decode_test t d exp)`,
  STRUCT_CASES_TAC(ISPEC `d:dTest` (cases "dTest")) THEN
  SIMP_TAC[flat_pattern_decode_test_def; no_Mat_def; ALL]);;

let decode_guard_no_Mat = prove
 (`no_Mat exp ==> no_Mat (decode_guard t exp gd)`,
  DISCH_TAC THEN SPEC_TAC(`gd:dGuard`,`gd:dGuard`) THEN
  MATCH_MP_TAC dGuard_INDUCT THEN
  ASM_SIMP_TAC[decode_guard_def; no_Mat_def; flat_Bool_def; ALL;
               decode_test_no_Mat; decode_pos_no_Mat] THEN
  REPEAT STRIP_TAC THEN FLATPAUX_SMARTIF_GOAL_TAC THEN
  ASM_REWRITE_TAC[no_Mat_def; flat_Bool_def; ALL]);;

let decode_dtree_no_Mat = prove
 (`no_Mat v_exp /\ no_Mat dflt /\ ALL no_Mat (toList br_spt)
   ==> no_Mat (decode_dtree t br_spt v_exp dflt dtree)`,
  STRIP_TAC THEN SPEC_TAC(`dtree:dTree`,`dtree:dTree`) THEN
  MATCH_MP_TAC dTree_INDUCT THEN REPEAT CONJ_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[decode_dtree_def] THEN
   MP_TAC(ISPEC `lookup a (br_spt:(flat_exp)spt)` (cases "option")) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   UNDISCH_TAC `ALL no_Mat (toList (br_spt:(flat_exp)spt))` THEN
   REWRITE_TAC[GSYM ALL_MEM; MEM_toList] THEN ASM_MESON_TAC[];
   ASM_REWRITE_TAC[decode_dtree_def];
   REWRITE_TAC[decode_dtree_def; no_Mat_def];
   REPEAT STRIP_TAC THEN REWRITE_TAC[decode_dtree_def] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   FLATPAUX_SMARTIF_GOAL_TAC THEN
   ASM_SIMP_TAC[no_Mat_def; decode_guard_no_Mat]]);;

let compile_pats_no_Mat = prove
 (`no_Mat dflt /\ no_Mat x /\ ALL no_Mat (MAP SND ps)
   ==> no_Mat (compile_pats cfg naive t N x dflt ps)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `ALL no_Mat (MAP (compile_pat_rhs t N x) ps)` ASSUME_TAC THENL
  [UNDISCH_TAC `ALL no_Mat (MAP SND (ps:(flat_pat#flat_exp)list))` THEN
   SPEC_TAC(`ps:(flat_pat#flat_exp)list`,`ps:(flat_pat#flat_exp)list`) THEN
   LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL] THEN
   SPEC_TAC(`h:flat_pat#flat_exp`,`h:flat_pat#flat_exp`) THEN
   REWRITE_TAC[FORALL_PAIR_THM; compile_pat_rhs_def; SND] THEN
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
   MATCH_MP_TAC compile_pat_bindings_no_Mat THEN
   REWRITE_TAC[ALL] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[compile_pats_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THENL
  [MATCH_MP_TAC naive_pattern_matches_no_Mat THEN
   ASM_SIMP_TAC[ALL; MAP_SND_ZIP; LENGTH_MAP];
   MATCH_MP_TAC decode_dtree_no_Mat THEN
   ASM_REWRITE_TAC[GSYM ALL_MEM; GSYM IN_SET_OF_LIST; set_toList_fromList] THEN
   ASM_REWRITE_TAC[IN_SET_OF_LIST; ALL_MEM]]);;

let FLATPAUX_letrec_noMat = prove
 (`!fs:(varN#varN#flat_exp)list.
     (!a b c. MEM (a,b,c) fs ==> no_Mat (SND (SND (flat_pattern_compile_exp cfg c))))
     ==> ALL no_Mat (MAP (SND o SND)
           (MAP (\(n,m,e). (n,m,SND (SND (flat_pattern_compile_exp cfg e)))) fs))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL] THEN
  SPEC_TAC(`h:varN#varN#flat_exp`,`h:varN#varN#flat_exp`) THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN GEN_TAC THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN GEN_TAC THEN GEN_TAC THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[MEM; o_THM; SND; PAIR_EQ] THEN
  REPEAT STRIP_TAC THENL
  [ASM_MESON_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let FLATPAUX_cnm_fun = prove
 (`(!cfg exp. no_Mat (SND (SND (flat_pattern_compile_exp cfg exp)))) /\
   (!cfg exps. ALL no_Mat (SND (SND (flat_pattern_compile_exps cfg exps)))) /\
   (!cfg pats. ALL no_Mat (MAP SND (SND (SND (compile_match cfg pats)))))`,
  MATCH_MP_TAC flat_pattern_compile_exp_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  REWRITE_TAC[flat_pattern_compile_exp_def] THEN
  REPEAT IL1AUX_PAIRARG_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN REWRITE_TAC[FST; SND] THEN
  FLATPAUX_UNGUARD_TAC THEN
  REWRITE_TAC[no_Mat_def; EVERY_REVERSE; ALL; MAP; o_THM; FLATPAUX_letrec_compile] THEN
  CASE_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN TRY FLATPAUX_SMARTIF_GOAL_TAC THEN
  ASM_SIMP_TAC[no_Mat_def; EVERY_REVERSE; ALL; MAP; o_THM] THEN
  FIRST [MATCH_MP_TAC compile_pats_no_Mat THEN
         ASM_SIMP_TAC[no_Mat_def; ALL] THEN NO_TAC;
         MATCH_MP_TAC FLATPAUX_letrec_noMat THEN ASM_REWRITE_TAC[]]);;

let compile_exp_no_Mat = prove
 (`(!cfg exp N sg exp'. flat_pattern_compile_exp cfg exp = (N,sg,exp')
      ==> no_Mat exp') /\
   (!cfg exps N sg exps'. flat_pattern_compile_exps cfg exps = (N,sg,exps')
      ==> ALL no_Mat exps') /\
   (!cfg pats N sg pats'. compile_match cfg pats = (N,sg,pats')
      ==> ALL no_Mat (MAP SND pats'))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
  [MP_TAC(SPEC_ALL (CONJUNCT1 FLATPAUX_cnm_fun));
   MP_TAC(SPEC_ALL (CONJUNCT1 (CONJUNCT2 FLATPAUX_cnm_fun)));
   MP_TAC(SPEC_ALL (CONJUNCT2 (CONJUNCT2 FLATPAUX_cnm_fun)))] THEN
  ASM_REWRITE_TAC[SND]);;

let compile_decs_no_Mat = prove
 (`!decs. no_Mat_decs (MAP (compile_dec cfg) decs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; no_Mat_decs_def] THEN
  ASM_REWRITE_TAC[compile_dec_def; FLATPAUX_cnm_fun]);;
