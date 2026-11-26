(* ========================================================================= *)
(* compute_execProof: port of HOL4 candle/prover/compute/                    *)
(* compute_execProofScript.sml (CakeML v3479).  Verification of the fast     *)
(* interpreter for the Candle compute primitive.                             *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The overloads of compute_syntax are read by its parser extension (see   *)
(*   the header of compute_syntax.ml).                                       *)
(* - Names as doc/names.tsv says: code_rel_cases is                          *)
(*   compute_code_rel_cases, HOL4's local rebinding cexp_vars_def (of        *)
(*   compute_syntaxProof's cexp_vars_def) is compute_cexp_vars_def; as a     *)
(*   [local,simp] theorem it is not registered with the simpset.             *)
(* - code_rel is polymorphic in the equations, as in HOL4: eqs has the type  *)
(*   (mlstring#A list#B) list; v1 ++ [n] ++ v2 is APPEND (APPEND v1 [n]) v2. *)
(* - The free variables of the HOL4 statements are universally quantified.   *)
(* - Local helpers that are not HOL4 theorems are CMPEXPAUX_.                *)
(* ========================================================================= *)

needs "candle/prover/compute/compute_evalProof.ml";;
needs "candle/prover/compute/compute_exec.ml";;

prioritize_num();;
type_invention_error := true;;

compute_overloads_on ();;

(* ------------------------------------------------------------------------- *)
(* verification                                                              *)
(* ------------------------------------------------------------------------- *)

let from_cv_def = cake_def
  `(from_cv (compute_exec_Num n) = compute_Num n) /\
   (from_cv (compute_exec_Pair x y) = compute_Pair (from_cv x) (from_cv y))`;;
let _ = cake_add_simps [from_cv_def];;

let from_res_def = cake_def
  `(from_res (f:A->B) (M_success v:(A,E)exc) = (M_success (f v):(B,E)exc)) /\
   (from_res (f:A->B) (M_failure e:(A,E)exc) = (M_failure e:(B,E)exc))`;;
let _ = cake_add_simps [from_res_def];;

let code_rel_rules,code_rel_ind,compute_code_rel_cases,code_rel_strongind = cake_inductive
  `(!(eqs:(mlstring#(A)list#B)list) v1 n v2.
      ~MEM n v1 ==>
      code_rel eqs (APPEND (APPEND v1 [n]) v2) (compute_Var n)
        (compute_exec_Var (LENGTH v1))) /\
   (!(eqs:(mlstring#(A)list#B)list) vars n.
      code_rel eqs vars (compute_Num n) (compute_exec_Const n)) /\
   (!(eqs:(mlstring#(A)list#B)list) vars x y x1 y1.
      code_rel eqs vars x x1 /\
      code_rel eqs vars y y1 ==>
      code_rel eqs vars (compute_Pair x y) (compute_exec_Binop compute_exec_Pair x1 y1)) /\
   (!(eqs:(mlstring#(A)list#B)list) vars x y z x1 y1 z1.
      code_rel eqs vars x x1 /\
      code_rel eqs vars y y1 /\
      code_rel eqs vars z z1 ==>
      code_rel eqs vars (compute_If x y z) (compute_exec_If x1 y1 z1)) /\
   (!(eqs:(mlstring#(A)list#B)list) vars s x y x1 y1.
      code_rel eqs vars x x1 /\
      code_rel eqs (CONS s vars) y y1 ==>
      code_rel eqs vars (compute_Let s x y) (compute_exec_Let x1 y1)) /\
   (!(eqs:(mlstring#(A)list#B)list) vars xs xs1 f l body n.
      ALL2 (code_rel eqs vars) xs xs1 /\
      n < LENGTH eqs /\ EL n eqs = (f,l,body) /\
      LENGTH l = LENGTH xs /\
      (!k. k < n ==> ~(FST (EL k eqs) = f)) ==>
      code_rel eqs vars (compute_App f xs) (compute_exec_App n xs1)) /\
   (!(eqs:(mlstring#(A)list#B)list) vars x x1 m.
      code_rel eqs vars x x1 ==>
      code_rel eqs vars (compute_Uop m x) (compute_exec_Monop (compute_monop m) x1)) /\
   (!(eqs:(mlstring#(A)list#B)list) vars x y x1 y1 b.
      code_rel eqs vars x x1 /\
      code_rel eqs vars y y1 ==>
      code_rel eqs vars (compute_Binop b x y) (compute_exec_Binop (compute_binop b) x1 y1))`;;

let option_ALOOKUP = prove
 (`!(eqs:(A#B#C)list) n f l body (s:hol_refs).
     n < LENGTH eqs /\
     EL n eqs = (f,l,body) /\
     (!k. k < n ==> ~(FST (EL k eqs) = f)) ==>
     compute_option (ALOOKUP eqs) f s = (M_success (l,body),s)`,
  SUBGOAL_THEN
   `!(eqs:(A#B#C)list) n f l body.
      n < LENGTH eqs /\ EL n eqs = (f,l,body) /\
      (!k. k < n ==> ~(FST (EL k eqs) = f)) ==> ALOOKUP eqs f = SOME (l,body)`
   (fun th -> REPEAT STRIP_TAC THEN REWRITE_TAC[compute_option_def] THEN
              SUBGOAL_THEN `ALOOKUP (eqs:(A#B#C)list) f = SOME (l,body)` SUBST1_TAC THENL
               [MATCH_MP_TAC th THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
                CAKE_REWRITE_TAC[st_ex_return_def]]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  SPEC_TAC(`h:A#B#C`,`h:A#B#C`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`; `c:C`; `n:num`] THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `m:num` SUBST1_TAC)
    (SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[EL; HD; TL; LT_SUC; ALOOKUP_THM] THENL
   [REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(a:A = f)` (fun th -> REWRITE_TAC[th]) THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LT_0; EL; HD; FST]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `SUC k`) THEN
    ASM_REWRITE_TAC[LT_SUC; EL; TL]]);;

let LESS_LENGTH_env_lookup = prove
 (`!xs n. n < LENGTH xs ==> env_lookup n xs = EL n xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN REWRITE_TAC[env_lookup_def; EL; HD; TL; LT_SUC; NOT_SUC; SUC_SUB1] THEN
  ASM_MESON_TAC[]);;

let compute_eval_from_cv = prove
 (`!x (s:hol_refs) ck eqs.
     compute_eval ck eqs (from_cv x) s = (M_success (from_cv x),s)`,
  MATCH_MP_TAC cv_INDUCT THEN REWRITE_TAC[from_cv_def] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[compute_eval_def] THEN
  ASM CAKE_REWRITE_TAC[st_ex_return_def; st_ex_bind_def]);;

let compile_eval_list_length = prove
 (`!cvs xs ck ceqs (s:hol_refs) s'.
     compute_eval_list ck ceqs cvs s = (M_success xs,s') ==> LENGTH xs = LENGTH cvs`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[compute_eval_def] THEN
  REWRITE_TAC[ml_monadBase_st_ex_bind_success; ml_monadBase_st_ex_return_success;
              injectivity "exc"] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH; SUC_INJ] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let cexp_value_from_cv = prove
 (`!y. cexp_value (from_cv y)`,
  MATCH_MP_TAC cv_INDUCT THEN ASM_REWRITE_TAC[from_cv_def; cexp_value_def]);;

(* HOL4: Theorem cexp_vars_def[local,simp] = compute_syntaxProofTheory.cexp_vars_def *)
let compute_cexp_vars_def = cexp_vars_def;;

let eqs_ok_def = cake_def
  `eqs_ok (eqs:(mlstring#mlstring list#compute_exp)list) <=>
     ALL (\(n,args,body).
            cexp_vars body SUBSET set_of_list args /\ ALL_DISTINCT args /\
            code_rel eqs (REVERSE args) body (compile_to_ce eqs (n,args,body))) eqs`;;

let do_uop_from_cv = prove
 (`!uop a (s:A).
     compute_do_uop uop (from_cv a) s =
     (M_success (from_cv (compute_monop uop a)):(compute_exp,B)exc,s)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `uop:uop` (cases "uop")) THEN
  STRUCT_CASES_TAC (SPEC `a:cv` (cases "cv")) THEN
  CAKE_REWRITE_TAC[compute_do_uop_def; compute_do_fst_def; compute_do_snd_def;
                   compute_do_ispair_def; compute_monop_def; compute_monop_fst_def;
                   compute_monop_snd_def; compute_monop_ispair_def; from_cv_def;
                   st_ex_return_def]);;

let from_cv_11 = prove
 (`!x y. from_cv x = from_cv y <=> x = y`,
  MATCH_MP_TAC cv_INDUCT THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY (DISCH_TAC THEN GEN_TAC) THEN
  STRUCT_CASES_TAC (SPEC `y:cv` (cases "cv")) THEN
  ASM_REWRITE_TAC[from_cv_def; injectivity "compute_exp"; distinctness "compute_exp";
                  injectivity "cv"; distinctness "cv"]);;

let do_binop_from_cv = prove
 (`!bop a b (s:A).
     compute_do_binop bop (from_cv a) (from_cv b) s =
     (M_success (from_cv (compute_binop bop a b)):(compute_exp,B)exc,s)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `bop:compute_binop` (cases "compute_binop")) THEN
  STRUCT_CASES_TAC (SPEC `a:cv` (cases "cv")) THEN
  STRUCT_CASES_TAC (SPEC `b:cv` (cases "cv")) THEN
  REWRITE_TAC[compute_do_binop_def; compute_binop_def] THEN
  CAKE_REWRITE_TAC[compute_do_arith_def; compute_do_reln_def; compute_do_eq_def;
                   compute_binop_add_def; compute_binop_sub_def; compute_binop_mul_def;
                   compute_binop_div_def; compute_binop_mod_def; compute_binop_less_def;
                   compute_binop_eq_def; from_cv_def; to_num_def; st_ex_return_def;
                   SAFEDIV_def; SAFEMOD_def; cv_T_def; cv_F_def; LET_DEF; LET_END_DEF;
                   from_cv_11; injectivity "cv"; distinctness "cv";
                   injectivity "compute_exp"; distinctness "compute_exp";
                   ADD_CLAUSES; MULT_CLAUSES; SUB_0; PAIR_EQ; injectivity "exc"] THEN
  TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[from_cv_def; ONE]);;

let env_lookup_lemma = prove
 (`!v1 (env:(mlstring#cv)list) s v2.
     MAP FST env = APPEND (APPEND v1 [s]) v2 /\ ~MEM s v1 ==>
     ?z. ALOOKUP (MAP (\(x,y). (x,from_cv y)) env) s = SOME (from_cv z) /\
         env_lookup (LENGTH v1) (MAP SND env) = z`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `env:(mlstring#cv)list` THEN
  STRUCT_CASES_TAC (ISPEC `env:(mlstring#cv)list` list_CASES) THEN
  REWRITE_TAC[MAP; APPEND; NOT_NIL_CONS; NOT_CONS_NIL] THENL
   [SPEC_TAC(`h:mlstring#cv`,`p:mlstring#cv`); SPEC_TAC(`h':mlstring#cv`,`p:mlstring#cv`)] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[CONS_11; MEM; LENGTH; ALOOKUP_THM; env_lookup_def; NOT_SUC; SUC_SUB1;
              DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THENL
   [EXISTS_TAC `p2:cv` THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(p1:mlstring = s)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `v2:mlstring list` THEN
    ASM_REWRITE_TAC[]]);;

let subst_from_cv = prove
 (`!v xs. compute_subst xs (from_cv v) = from_cv v`,
  MATCH_MP_TAC cv_INDUCT THEN REWRITE_TAC[from_cv_def; compute_subst_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let subst_subst = prove
 (`!e (xs:(mlstring#compute_exp)list) ys.
     ALL (\x. ?v. SND x = from_cv v) ys ==>
     compute_subst xs (compute_subst ys e) = compute_subst (APPEND ys xs) e`,
  MATCH_MP_TAC cexp_vars_ind THEN REWRITE_TAC[compute_subst_def] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [(* (Num is solved by the rewriting) Var *)
    REWRITE_TAC[ALOOKUP_APPEND] THEN TOP_CASE_TAC THEN
    CAKE_REWRITE_TAC[compute_subst_def] THEN
    FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP ALOOKUP_MEM) THEN
    UNDISCH_TAC `ALL (\x. ?v. SND x = from_cv v) (ys:(mlstring#compute_exp)list)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
    REWRITE_TAC[SND] THEN STRIP_TAC THEN ASM_REWRITE_TAC[subst_from_cv];
    (* Pair *)
    ASM_SIMP_TAC[];
    (* Uop *)
    ASM_SIMP_TAC[];
    (* Binop *)
    ASM_SIMP_TAC[];
    (* If *)
    ASM_SIMP_TAC[];
    (* Let *)
    ASM_SIMP_TAC[FILTER_APPEND; EVERY_FILTER_IMP];
    (* App *)
    AP_TERM_TAC THEN REWRITE_TAC[GSYM MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
    REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN ASM_SIMP_TAC[]]);;

let alookup_subst = prove
 (`!e (xs:(mlstring#compute_exp)list) ys.
     ALOOKUP xs = ALOOKUP ys ==> compute_subst xs e = compute_subst ys e`,
  MATCH_MP_TAC cexp_vars_ind THEN REWRITE_TAC[compute_subst_def] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[injectivity "compute_exp"] THEN REPEAT CONJ_TAC THENL
   [(* (Num and Var are solved by the rewriting) Pair *)
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* Uop *)
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* Binop *)
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* If *)
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* Let *)
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[FUN_EQ_THM; ALOOKUP_FILTER];
    (* App *)
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    X_GEN_TAC `y:compute_exp` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:compute_exp`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let CMPEXPAUX_ALL_SND_from_cv = prove
 (`!(env:(mlstring#cv)list).
     ALL (\x. ?v. SND x = from_cv v) (MAP (\(x,y). (x,from_cv y)) env)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ALL] THEN
  SPEC_TAC(`h:mlstring#cv`,`h:mlstring#cv`) THEN REWRITE_TAC[FORALL_PAIR_THM; SND] THEN
  MESON_TAC[]);;

let subst_cons_lemma = prove
 (`!s a (env:(mlstring#cv)list) e2.
     compute_subst [(s,from_cv a)]
       (compute_subst (FILTER (\(n,x). ~(n = s)) (MAP (\(x,y). (x,from_cv y)) env)) e2) =
     compute_subst (MAP (\(x,y). (x,from_cv y)) (CONS (s,a) env)) e2`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPECL [`e2:compute_exp`; `[s:mlstring,from_cv a]`;
                  `FILTER (\(n,x). ~(n = s))
                     (MAP (\(x,y). (x,from_cv y)) (env:(mlstring#cv)list))`]
                 subst_subst) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC EVERY_FILTER_IMP THEN REWRITE_TAC[CMPEXPAUX_ALL_SND_from_cv];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC alookup_subst THEN
  REWRITE_TAC[FUN_EQ_THM; MAP; ALOOKUP_APPEND; ALOOKUP_FILTER; ALOOKUP_THM] THEN
  X_GEN_TAC `k:mlstring` THEN ASM_CASES_TAC `k:mlstring = s` THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN TOP_CASE_TAC THEN CAKE_REWRITE_TAC[]);;

let subst_eq_subst_lemma = prove
 (`!s (xs:(mlstring#compute_exp)list) ys.
     ALL_DISTINCT (MAP FST xs) /\ xs = REVERSE ys ==>
       compute_subst xs s = compute_subst ys s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC alookup_subst THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `k:mlstring` THEN MATCH_MP_TAC alookup_distinct_reverse THEN
  UNDISCH_TAC `ALL_DISTINCT (MAP FST (REVERSE (ys:(mlstring#compute_exp)list)))` THEN
  REWRITE_TAC[GSYM MAP_REVERSE; ALL_DISTINCT_REVERSE]);;

(* the inversion of code_rel for each constructor *)
let CMPEXPAUX_code_rel_inv = prove
 (`(!(eqs:(mlstring#(A)list#B)list) vars n e1.
      code_rel eqs vars (compute_Var n) e1 <=>
      ?v1 v2. vars = APPEND (APPEND v1 [n]) v2 /\
              e1 = compute_exec_Var (LENGTH v1) /\ ~MEM n v1) /\
   (!(eqs:(mlstring#(A)list#B)list) vars n e1.
      code_rel eqs vars (compute_Num n) e1 <=> e1 = compute_exec_Const n) /\
   (!(eqs:(mlstring#(A)list#B)list) vars x y e1.
      code_rel eqs vars (compute_Pair x y) e1 <=>
      ?x1 y1. e1 = compute_exec_Binop compute_exec_Pair x1 y1 /\
              code_rel eqs vars x x1 /\ code_rel eqs vars y y1) /\
   (!(eqs:(mlstring#(A)list#B)list) vars x y z e1.
      code_rel eqs vars (compute_If x y z) e1 <=>
      ?x1 y1 z1. e1 = compute_exec_If x1 y1 z1 /\
                 code_rel eqs vars x x1 /\ code_rel eqs vars y y1 /\
                 code_rel eqs vars z z1) /\
   (!(eqs:(mlstring#(A)list#B)list) vars s x y e1.
      code_rel eqs vars (compute_Let s x y) e1 <=>
      ?x1 y1. e1 = compute_exec_Let x1 y1 /\
              code_rel eqs vars x x1 /\ code_rel eqs (CONS s vars) y y1) /\
   (!(eqs:(mlstring#(A)list#B)list) vars f xs e1.
      code_rel eqs vars (compute_App f xs) e1 <=>
      ?xs1 l body n. e1 = compute_exec_App n xs1 /\
                     ALL2 (code_rel eqs vars) xs xs1 /\
                     n < LENGTH eqs /\ EL n eqs = (f,l,body) /\
                     LENGTH l = LENGTH xs /\
                     (!k. k < n ==> ~(FST (EL k eqs) = f))) /\
   (!(eqs:(mlstring#(A)list#B)list) vars m x e1.
      code_rel eqs vars (compute_Uop m x) e1 <=>
      ?x1. e1 = compute_exec_Monop (compute_monop m) x1 /\ code_rel eqs vars x x1) /\
   (!(eqs:(mlstring#(A)list#B)list) vars b x y e1.
      code_rel eqs vars (compute_Binop b x y) e1 <=>
      ?x1 y1. e1 = compute_exec_Binop (compute_binop b) x1 y1 /\
              code_rel eqs vars x x1 /\ code_rel eqs vars y y1)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [compute_code_rel_cases] THEN
  REWRITE_TAC[injectivity "compute_exp"; distinctness "compute_exp"] THEN
  MESON_TAC[]);;

let CMPEXPAUX_from_res_eq = prove
 (`(!(f:A->B) (r:(A,E)exc) y. from_res f r = M_success y <=> ?x. r = M_success x /\ f x = y) /\
   (!(f:A->B) (r:(A,E)exc) e. from_res f r = M_failure e <=> r = M_failure e)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `r:(A,E)exc` (cases "exc")) THEN
  REWRITE_TAC[from_res_def; injectivity "exc"; distinctness "exc"] THEN MESON_TAC[]);;

let CMPEXPAUX_MAP_ZIP_from_cv = prove
 (`!(a:mlstring list) (b:cv list). LENGTH a = LENGTH b ==>
     MAP (\(x,y). (x,from_cv y)) (ZIP a b) = ZIP a (MAP from_cv b)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; ZIP; MAP] THEN ASM_SIMP_TAC[]);;

(* the substitution of an App step, as one of the induction *)
let CMPEXPAUX_subst_ZIP = prove
 (`!(l:mlstring list) cs vs body.
     ALL_DISTINCT l /\ LENGTH l = LENGTH cs /\ REVERSE cs = MAP from_cv vs ==>
     compute_subst (ZIP l cs) body =
     compute_subst (MAP (\(x,y). (x,from_cv y)) (ZIP (REVERSE l) vs)) body`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (REVERSE (l:mlstring list)) = LENGTH (vs:cv list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_REVERSE; LENGTH_MAP]; ALL_TAC] THEN
  ASM_SIMP_TAC[CMPEXPAUX_MAP_ZIP_from_cv] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    try fst (dest_const (rator (lhs (concl th)))) = "REVERSE" with Failure _ -> false)) THEN
  ASM_SIMP_TAC[GSYM REVERSE_ZIP] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC subst_eq_subst_lemma THEN
  REWRITE_TAC[GSYM MAP_REVERSE; ALL_DISTINCT_REVERSE] THEN ASM_SIMP_TAC[MAP_FST_ZIP]);;

let CMPEXPAUX_get_code = prove
 (`!(eqs:(mlstring#mlstring list#compute_exp)list) n (s:hol_refs).
     n < LENGTH eqs ==>
     get_code n (build_funs eqs) s = (M_success (compile_to_ce eqs (EL n eqs)),s)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[get_code_def; build_funs_def; regexp_compiler_length_def;
               regexp_compiler_sub_def; LENGTH_MAP; EL_MAP; st_ex_return_def]);;

(* the monadic plumbing *)
let CMPEXPAUX_SIMP_TAC : tactic =
  CAKE_REWRITE_TAC[st_ex_bind_def; st_ex_return_def; st_ex_ignore_bind_def;
                   from_res_def; from_cv_def; PAIR_EQ; FST; SND;
                   holKernel_raise_Failure_def; injectivity "exc"; distinctness "exc"];;

(* rewrite compute_eval ck ceqs (compute_subst (MAP g env0) e) st of the goal *)
(* by its induction hypothesis, with e1 from a code_rel assumption; side    *)
(* proves the conditions                                                      *)
let CMPEXPAUX_IH_TAC (side:tactic) : tactic = fun (asl,w as g) ->
  let is_ev t = try let f,args = strip_comb t in
                    fst (dest_const f) = "compute_eval" && length args = 4
                with Failure _ -> false in
  let evs = filter (fun t -> free_in t w) (find_terms is_ev w) in
  let attempt ev =
    let args = snd (strip_comb ev) in
    let se = el 2 args and st = el 3 args in
    let e = rand se in
    let env0 = rand (rand (rator se)) in
    let e1 = tryfind (fun (_,th) -> let c = concl th in
               let f,cargs = strip_comb c in
               if fst (dest_const f) = "code_rel" && el 2 cargs = e then el 3 cargs
               else failwith "no") asl in
    tryfind (fun (_,th) -> let th' = SPECL [env0; e1; st] th in
               if is_imp (concl th') && lhs (rand (concl th')) = ev then th'
               else failwith "no") asl in
  let ih = tryfind attempt evs in
  (MP_TAC ih THEN ANTS_TAC THENL [side; DISCH_THEN SUBST1_TAC]) g;;

(* the list induction hypothesis for compute_eval_list ck ceqs (MAP       *)
(* (compute_subst (MAP g env0)) es) st and exec_list ... e1 acc st of the  *)
(* goal, as an antecedent of the goal                                       *)
let CMPEXPAUX_LIST_IH_TAC (side:tactic) : tactic = fun (asl,w as g) ->
  let is_c n k t = try let f,args = strip_comb t in
                       fst (dest_const f) = n && length args = k
                   with Failure _ -> false in
  let evl = find (fun t -> free_in t w) (find_terms (is_c "compute_eval_list" 4) w) in
  let exl = find (fun t -> free_in t w) (find_terms (is_c "exec_list" 6) w) in
  let eargs = snd (strip_comb evl) and xargs = snd (strip_comb exl) in
  let mes = el 2 eargs and st = el 3 eargs in
  let env0 = rand (rand (rand (rator mes))) in
  let e1 = el 3 xargs and acc = el 4 xargs in
  let ih = tryfind (fun (_,th) -> let th' = SPECL [env0; e1; st; acc] th in
             if is_imp (concl th') && free_in evl (rand (concl th')) then th'
             else failwith "no") asl in
  (MP_TAC ih THEN ANTS_TAC THENL [side; ALL_TAC]) g;;

(* cases on a run of name (arity k) in the goal: its result and state (the *)
(* new names avoid the hypotheses of the assumptions too)                   *)
let CMPEXPAUX_CASES_TAC (name:string) (k:int) : tactic = fun (asl,w as g) ->
  let is_ex t = try let f,args = strip_comb t in
                    fst (dest_const f) = name && length args = k
                with Failure _ -> false in
  let t = find (fun t -> free_in t w) (find_terms is_ex w) in
  let [rty; sty] = snd (dest_type (type_of t)) in
  let avoid = frees w @ freesl (map (concl o snd) asl) @
              freesl (List.concat (map (hyp o snd) asl)) in
  let r = variant avoid (mk_var("r",rty)) in
  let s2 = variant (r::avoid) (mk_var("st",sty)) in
  (MP_TAC (ISPEC t PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN r (X_CHOOSE_THEN s2 (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
   DISJ_CASES_THEN (CHOOSE_THEN SUBST_ALL_TAC) (ISPEC r (cases "exc"))) g;;

let CMPEXPAUX_EXEC_CASES_TAC : tactic =
  CMPEXPAUX_CASES_TAC "exec" 5 ORELSE CMPEXPAUX_CASES_TAC "exec_list" 6;;

(* the case set-up: e1 from the inversion of code_rel (PREP0: no IH) *)
let CMPEXPAUX_PREP0_TAC : tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CMPEXPAUX_code_rel_inv; compute_cexp_vars_def; UNION_SUBSET] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl));;

let CMPEXPAUX_PREP_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN CMPEXPAUX_PREP0_TAC THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;

(* the unfolding of compute_eval and exec on the constructors *)
let CMPEXPAUX_UNFOLD_TAC : tactic =
  REWRITE_TAC[compute_subst_def] THEN ONCE_REWRITE_TAC[compute_eval_def] THEN
  ONCE_REWRITE_TAC[exec_def];;

let CMPEXPAUX_STEP_TAC : tactic =
  CMPEXPAUX_IH_TAC (ASM_REWRITE_TAC[]) THEN CMPEXPAUX_EXEC_CASES_TAC THEN CMPEXPAUX_SIMP_TAC;;

(* exec_thm in equational form: compute_eval of the substituted expression *)
(* is exec, its result mapped by from_cv                                    *)
let CMPEXPAUX_exec_eqn = prove
 (`
 (!ck eqs e (env:(mlstring#cv)list) e1 (s:hol_refs).
    cexp_vars e SUBSET set_of_list (MAP FST env) /\ eqs_ok eqs /\
    code_rel eqs (MAP FST env) e e1 ==>
    compute_eval ck eqs (compute_subst (MAP (\(x,y). (x,from_cv y)) env) e) s =
    (from_res from_cv (FST (exec (build_funs eqs) (MAP SND env) ck e1 s)),
     SND (exec (build_funs eqs) (MAP SND env) ck e1 s))) /\
 (!ck eqs es (env:(mlstring#cv)list) e1 (s:hol_refs) acc.
    ALL (\e. cexp_vars e SUBSET set_of_list (MAP FST env)) es /\ eqs_ok eqs /\
    ALL2 (code_rel eqs (MAP FST env)) es e1 ==>
    SND (compute_eval_list ck eqs (MAP (compute_subst (MAP (\(x,y). (x,from_cv y)) env)) es) s) =
    SND (exec_list (build_funs eqs) (MAP SND env) ck e1 acc s) /\
    from_res (\xs. APPEND (REVERSE xs) (MAP from_cv acc))
      (FST (compute_eval_list ck eqs
              (MAP (compute_subst (MAP (\(x,y). (x,from_cv y)) env)) es) s)) =
    from_res (MAP from_cv) (FST (exec_list (build_funs eqs) (MAP SND env) ck e1 acc s)))`,
  MATCH_MP_TAC compute_eval_ind_ind THEN REPEAT CONJ_TAC THENL
   [(* Var *)
    CMPEXPAUX_PREP0_TAC THEN
    MP_TAC (ISPECL [`v1:mlstring list`; `env:(mlstring#cv)list`; `s:mlstring`;
                    `v2:mlstring list`] env_lookup_lemma) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[compute_subst_def] THEN CAKE_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[exec_def] THEN
    ASM_REWRITE_TAC[compute_eval_from_cv] THEN CMPEXPAUX_SIMP_TAC;
    (* Num *)
    CMPEXPAUX_PREP0_TAC THEN CMPEXPAUX_UNFOLD_TAC THEN CMPEXPAUX_SIMP_TAC;
    (* Pair *)
    CMPEXPAUX_PREP_TAC THEN CMPEXPAUX_UNFOLD_TAC THEN CMPEXPAUX_SIMP_TAC THEN
    CMPEXPAUX_STEP_TAC THEN CMPEXPAUX_STEP_TAC;
    (* Uop *)
    CMPEXPAUX_PREP_TAC THEN CMPEXPAUX_UNFOLD_TAC THEN CMPEXPAUX_SIMP_TAC THEN
    CMPEXPAUX_STEP_TAC THEN REWRITE_TAC[do_uop_from_cv] THEN CMPEXPAUX_SIMP_TAC;
    (* Binop *)
    CMPEXPAUX_PREP_TAC THEN CMPEXPAUX_UNFOLD_TAC THEN CMPEXPAUX_SIMP_TAC THEN
    CMPEXPAUX_STEP_TAC THEN CMPEXPAUX_STEP_TAC THEN
    REWRITE_TAC[do_binop_from_cv] THEN CMPEXPAUX_SIMP_TAC;
    (* App *)
    CMPEXPAUX_PREP_TAC THEN CMPEXPAUX_UNFOLD_TAC THEN
    ASM_CASES_TAC `ck = 0` THEN ASM_REWRITE_TAC[] THENL [CMPEXPAUX_SIMP_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun ckth -> RULE_ASSUM_TAC (REWRITE_RULE[ckth]) THEN ASSUME_TAC ckth) THEN
    W(fun (asl,w) -> let st = rand (lhs w) in
        MP_TAC (ISPECL [`ceqs:(mlstring#mlstring list#compute_exp)list`; `n:num`;
                        `f:mlstring`; `l:mlstring list`; `body:compute_exp`; st]
                       option_ALOOKUP)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[st_ex_bind_def] THEN ASM_REWRITE_TAC[] THEN CMPEXPAUX_SIMP_TAC THEN
    ASM_REWRITE_TAC[compute_check_def; LENGTH_MAP] THEN CMPEXPAUX_SIMP_TAC THEN
    CMPEXPAUX_LIST_IH_TAC
      (ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `UNIONS (set_of_list (MAP cexp_vars cs)) SUBSET
                    set_of_list (MAP FST (env:(mlstring#cv)list))` THEN
       REWRITE_TAC[UNIONS_SUBSET; IN_SET_OF_LIST; MEM_MAP; GSYM ALL_MEM] THEN
       MESON_TAC[]) THEN
    CMPEXPAUX_CASES_TAC "exec_list" 6 THEN CMPEXPAUX_CASES_TAC "compute_eval_list" 4 THEN
    CMPEXPAUX_SIMP_TAC THEN REWRITE_TAC[MAP; APPEND_NIL] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[CMPEXPAUX_get_code] THEN CMPEXPAUX_SIMP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `MEM (f,l,body) (ceqs:(mlstring#mlstring list#compute_exp)list)`
      ASSUME_TAC THENL
     [UNDISCH_TAC `EL n (ceqs:(mlstring#mlstring list#compute_exp)list) = f,l,body` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `cexp_vars body SUBSET set_of_list l /\ ALL_DISTINCT (l:mlstring list) /\
                  code_rel ceqs (REVERSE l) body (compile_to_ce ceqs (f,l,body))`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `eqs_ok ceqs` THEN REWRITE_TAC[eqs_ok_def; GSYM ALL_MEM] THEN
      DISCH_THEN(MP_TAC o SPEC `(f:mlstring,l:mlstring list,body:compute_exp)`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (a':compute_exp list) = LENGTH (cs:compute_exp list)` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP compile_eval_list_length) THEN REWRITE_TAC[LENGTH_MAP];
      ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (REVERSE (l:mlstring list)) = LENGTH (a:cv list)` ASSUME_TAC THENL
     [UNDISCH_TAC `REVERSE a' = MAP from_cv (a:cv list)` THEN
      DISCH_THEN(MP_TAC o AP_TERM `LENGTH:(compute_exp)list->num`) THEN
      ASM_REWRITE_TAC[LENGTH_REVERSE; LENGTH_MAP];
      ALL_TAC] THEN
    MP_TAC (ISPECL [`l:mlstring list`; `a':compute_exp list`; `a:cv list`;
                    `body:compute_exp`] CMPEXPAUX_subst_ZIP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM(ASSUME_TAC o SPEC `body:compute_exp` o check (fun th ->
      try type_of (fst (dest_forall (concl th))) = `:compute_exp` with Failure _ -> false)) THEN
    CMPEXPAUX_IH_TAC
      (ASM_SIMP_TAC[MAP_FST_ZIP] THEN
       UNDISCH_TAC `cexp_vars body SUBSET set_of_list (l:mlstring list)` THEN
       REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_REVERSE]) THEN
    ASM_SIMP_TAC[MAP_SND_ZIP];
    (* If *)
    CMPEXPAUX_PREP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    FIRST_X_ASSUM(ASSUME_TAC o (fun th -> MP th (SPEC `0` NOT_SUC)) o SPEC `SUC 0` o
      check (fun th -> try type_of (fst (dest_forall (concl th))) = `:num`
                       with Failure _ -> false)) THEN
    CMPEXPAUX_UNFOLD_TAC THEN CMPEXPAUX_SIMP_TAC THEN CMPEXPAUX_STEP_TAC THEN
    STRUCT_CASES_TAC (SPEC `a:cv` (cases "cv")) THEN CMPEXPAUX_SIMP_TAC THEN
    TRY COND_CASES_TAC THEN
    CMPEXPAUX_IH_TAC (ASM_REWRITE_TAC[]) THEN CMPEXPAUX_SIMP_TAC;
    (* Let *)
    CMPEXPAUX_PREP_TAC THEN CMPEXPAUX_UNFOLD_TAC THEN
    ASM_CASES_TAC `ck = 0` THEN ASM_REWRITE_TAC[] THENL [CMPEXPAUX_SIMP_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun ckth -> RULE_ASSUM_TAC (REWRITE_RULE[ckth]) THEN ASSUME_TAC ckth) THEN
    CMPEXPAUX_SIMP_TAC THEN CMPEXPAUX_STEP_TAC THEN
    REWRITE_TAC[subst_cons_lemma] THEN
    CMPEXPAUX_IH_TAC
      (REWRITE_TAC[MAP; FST; set_of_list] THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]) THEN
    REWRITE_TAC[MAP; SND];
    (* Nil *)
    REPEAT GEN_TAC THEN REWRITE_TAC[MAP; ALL2_DEF] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[compute_eval_def; exec_def] THEN
    CMPEXPAUX_SIMP_TAC THEN REWRITE_TAC[REVERSE; APPEND];
    (* Cons *)
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    X_GEN_TAC `env:(mlstring#cv)list` THEN X_GEN_TAC `e1:ce list` THEN
    STRUCT_CASES_TAC (ISPEC `e1:ce list` list_CASES) THEN
    REWRITE_TAC[ALL2; ALL; MAP] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[compute_eval_def; exec_def] THEN CMPEXPAUX_SIMP_TAC THEN
    CMPEXPAUX_STEP_TAC THEN
    CMPEXPAUX_LIST_IH_TAC (ASM_REWRITE_TAC[]) THEN
    CMPEXPAUX_CASES_TAC "exec_list" 6 THEN CMPEXPAUX_CASES_TAC "compute_eval_list" 4 THEN
    CMPEXPAUX_SIMP_TAC THEN
    REWRITE_TAC[REVERSE; GSYM APPEND_ASSOC; APPEND; MAP] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let exec_thm = prove
 (`(!ck eqs e res (env:(mlstring#cv)list) e1 (s:hol_refs) s1.
      compute_eval ck eqs (compute_subst (MAP (\(x,y). (x,from_cv y)) env) e) s =
        (res,s1) /\
      cexp_vars e SUBSET set_of_list (MAP FST env) /\ eqs_ok eqs /\
      code_rel eqs (MAP FST env) e e1 ==>
      ?res1. exec (build_funs eqs) (MAP SND env) ck e1 s = (res1,s1) /\
             res = from_res from_cv res1) /\
   (!ck eqs e res (env:(mlstring#cv)list) e1 (s:hol_refs) s1 acc.
      compute_eval_list ck eqs (MAP (compute_subst (MAP (\(x,y). (x,from_cv y)) env)) e) s =
        (res,s1) /\
      ALL (\e. cexp_vars e SUBSET set_of_list (MAP FST env)) e /\ eqs_ok eqs /\
      ALL2 (code_rel eqs (MAP FST env)) e e1 ==>
      ?res1. exec_list (build_funs eqs) (MAP SND env) ck e1 acc s = (res1,s1) /\
             from_res (\xs. APPEND (REVERSE xs) (MAP from_cv acc)) res =
             from_res (MAP from_cv) res1)`,
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MP_TAC (SPECL [`ck:num`; `eqs:(mlstring#mlstring list#compute_exp)list`;
                   `e:compute_exp`; `env:(mlstring#cv)list`; `e1:ce`; `s:hol_refs`]
                  (CONJUNCT1 CMPEXPAUX_exec_eqn)) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    EXISTS_TAC `FST (exec (build_funs eqs) (MAP SND (env:(mlstring#cv)list)) ck e1 s)`;
    MP_TAC (SPECL [`ck:num`; `eqs:(mlstring#mlstring list#compute_exp)list`;
                   `e:compute_exp list`; `env:(mlstring#cv)list`; `e1:ce list`;
                   `s:hol_refs`; `acc:cv list`]
                  (CONJUNCT2 CMPEXPAUX_exec_eqn)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `FST (exec_list (build_funs eqs) (MAP SND (env:(mlstring#cv)list)) ck e1 acc s)`] THEN
  ASM_REWRITE_TAC[PAIR]);;

(* HOL4: exec_thm |> CONJUNCT1 |> Q.SPECL [..,[],to_ce eqs [] e,..]  *)
(* |> SIMP_RULE std_ss [MAP,subst_empty,LIST_TO_SET]                   *)
let exec_lemma = GEN_ALL (REWRITE_RULE[MAP; subst_empty; set_of_list]
  (SPECL [`ck:num`; `eqs:(mlstring#mlstring list#compute_exp)list`; `e:compute_exp`;
          `res:(compute_exp,hol_exn)exc`; `[]:(mlstring#cv)list`; `to_ce eqs [] e`;
          `s:hol_refs`; `s1:hol_refs`] (CONJUNCT1 exec_thm)));;

let LIST_REL_MAP_lemma = prove
 (`!(R:A->B->bool) (f:A->B) xs. ALL2 R xs (MAP f xs) <=> ALL (\x. R x (f x)) xs`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2; MAP; ALL]);;

(* findi of a member of a list: the position before which it is not *)
let CMPEXPAUX_findi_split = prove
 (`!vars (s:mlstring).
     MEM s vars ==>
     ?v1 v2. vars = APPEND (APPEND v1 [s]) v2 /\ findi s vars = LENGTH v1 /\ ~MEM s v1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; findi_def] THEN GEN_TAC THEN
  ASM_CASES_TAC `(s:mlstring) = h` THEN ASM_REWRITE_TAC[] THENL
   [MAP_EVERY EXISTS_TAC [`[]:mlstring list`; `t:mlstring list`] THEN
    REWRITE_TAC[APPEND; MEM; LENGTH];
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:mlstring`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v1:mlstring list` (X_CHOOSE_THEN `v2:mlstring list`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`CONS (h:mlstring) v1`; `v2:mlstring list`] THEN
    ASM_REWRITE_TAC[APPEND; MEM; LENGTH] THEN ARITH_TAC]);;

(* findi of the name of an equation of a list with distinct names *)
let CMPEXPAUX_findi_eqs = prove
 (`!(eqs:(mlstring#mlstring list#compute_exp)list) f args body.
     ALL_DISTINCT (MAP FST eqs) /\ MEM (f,args,body) eqs ==>
     findi f (MAP FST eqs) < LENGTH eqs /\
     EL (findi f (MAP FST eqs)) eqs = (f,args,body) /\
     (!k. k < findi f (MAP FST eqs) ==> ~(FST (EL k eqs) = f))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN
  SPEC_TAC(`h:mlstring#mlstring list#compute_exp`,`h:mlstring#mlstring list#compute_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:mlstring`; `b:mlstring list`; `c:compute_exp`;
                       `f:mlstring`; `args:mlstring list`; `body:compute_exp`] THEN
  REWRITE_TAC[MAP; ALL_DISTINCT; findi_def; LENGTH; PAIR_EQ] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[EL; HD; LT_0; CONJUNCT1 LT];
    ASM_CASES_TAC `(f:mlstring) = a` THENL
     [UNDISCH_TAC `~MEM (a:mlstring) (MAP FST (t:(mlstring#mlstring list#compute_exp)list))` THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `(f:mlstring) = a`)) THEN
      REWRITE_TAC[MEM_MAP; NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `(f:mlstring,args:mlstring list,body:compute_exp)`) THEN
      ASM_REWRITE_TAC[FST];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`f:mlstring`; `args:mlstring list`; `body:compute_exp`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `1 + n = SUC n`; LT_SUC; EL; TL] THEN ASM_REWRITE_TAC[] THEN
    INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; FST; LT_SUC] THEN ASM_MESON_TAC[]]);;

(* the witnesses x1 of goals ?x1 .. . (.. t = x1 ..) /\ .. *)
let CMPEXPAUX_WITNESS_TAC : tactic = fun (asl,w as g) ->
  let vs,body = strip_exists w in
  let cs = conjuncts body in
  let ws = map (fun v -> lhs (find (fun c -> is_eq c && rhs c = v) cs)) vs in
  (MAP_EVERY EXISTS_TAC ws THEN REWRITE_TAC[]) g;;

let CMPEXPAUX_IHS_TAC : tactic =
  CMPEXPAUX_WITNESS_TAC THEN REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[];;

let code_rel_to_ce = prove
 (`!e vars (eqs:(mlstring#mlstring list#compute_exp)list).
     cexp_vars e SUBSET set_of_list vars /\ cexp_consts_ok eqs e /\
     ALL (\(n,args,body). cexp_vars body SUBSET set_of_list args /\
                          cexp_consts_ok eqs body) eqs /\
     ALL_DISTINCT (MAP FST eqs) ==>
     code_rel eqs vars e (to_ce eqs vars e)`,
  MATCH_MP_TAC cexp_vars_ind THEN
  REWRITE_TAC[to_ce_def; cexp_consts_ok_def; compute_cexp_vars_def; UNION_SUBSET] THEN
  REWRITE_TAC[CMPEXPAUX_code_rel_inv; injectivity "ce"] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [(* (Num is solved by the rewriting) Var *)
    MATCH_MP_TAC CMPEXPAUX_findi_split THEN
    UNDISCH_TAC `{s:mlstring} SUBSET set_of_list vars` THEN
    REWRITE_TAC[SING_SUBSET; IN_SET_OF_LIST];
    (* Pair *)
    CMPEXPAUX_IHS_TAC;
    (* Uop *)
    CMPEXPAUX_IHS_TAC;
    (* Binop *)
    CMPEXPAUX_IHS_TAC;
    (* If *)
    CMPEXPAUX_IHS_TAC;
    (* Let *)
    SUBGOAL_THEN `cexp_vars q SUBSET set_of_list (CONS (s:mlstring) vars)` ASSUME_TAC THENL
     [REWRITE_TAC[set_of_list] THEN ASM SET_TAC[]; CMPEXPAUX_IHS_TAC];
    (* App *)
    SUBGOAL_THEN `?args body. MEM (s,args,body) (eqs:(mlstring#mlstring list#compute_exp)list) /\
                              LENGTH (args:mlstring list) = LENGTH (cs:compute_exp list)`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `MEM (s,LENGTH (cs:compute_exp list))
                     (MAP (\(f,n,x). (f,LENGTH n))
                          (eqs:(mlstring#mlstring list#compute_exp)list))` THEN
      REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; PAIR_EQ] THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC (SPECL [`eqs:(mlstring#mlstring list#compute_exp)list`; `s:mlstring`;
                   `args:mlstring list`; `body:compute_exp`] CMPEXPAUX_findi_eqs) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
      [`MAP (to_ce eqs vars) (cs:compute_exp list)`; `args:mlstring list`;
       `body:compute_exp`;
       `findi (s:mlstring) (MAP FST (eqs:(mlstring#mlstring list#compute_exp)list))`] THEN
    ASM_REWRITE_TAC[LIST_REL_MAP_lemma] THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `y:compute_exp` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:compute_exp`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `UNIONS (set_of_list (MAP cexp_vars cs)) SUBSET set_of_list vars` THEN
      REWRITE_TAC[UNIONS_SUBSET; IN_SET_OF_LIST; MEM_MAP] THEN ASM_MESON_TAC[];
      UNDISCH_TAC `ALL (cexp_consts_ok (eqs:(mlstring#mlstring list#compute_exp)list)) cs` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[]]]);;

let compute_eval_eq_exec = prove
 (`!e (eqs:(mlstring#mlstring list#compute_exp)list) ck (s:hol_refs).
     cexp_vars e = {} /\
     cexp_consts_ok eqs e /\
     ALL_DISTINCT (MAP FST eqs) /\
     ALL (\(n,args,body).
            ALL_DISTINCT args /\
            cexp_vars body SUBSET set_of_list args /\
            cexp_consts_ok eqs body) eqs
     ==>
     compute_eval ck eqs e s =
       let (r,s1) = exec (build_funs eqs) [] ck (to_ce eqs [] e) s in
         (from_res from_cv r, s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `eqs_ok (eqs:(mlstring#mlstring list#compute_exp)list)` ASSUME_TAC THENL
   [REWRITE_TAC[eqs_ok_def; GSYM ALL_MEM; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:mlstring`; `args:mlstring list`; `body:compute_exp`] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o
      C MATCH_MP (ASSUME `MEM (n:mlstring,args:mlstring list,body:compute_exp) eqs`) o
      check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[compile_to_ce_def] THEN
    MATCH_MP_TAC code_rel_to_ce THEN ASM_REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `cexp_vars body SUBSET set_of_list (args:mlstring list)` THEN
      REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_REVERSE];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC (SPECL [`ck:num`; `eqs:(mlstring#mlstring list#compute_exp)list`; `e:compute_exp`;
                 `[]:(mlstring#cv)list`; `to_ce eqs [] e`; `s:hol_refs`]
                (CONJUNCT1 CMPEXPAUX_exec_eqn)) THEN
  REWRITE_TAC[MAP; subst_empty; set_of_list] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC code_rel_to_ce THEN
    ASM_REWRITE_TAC[set_of_list; SUBSET_REFL; GSYM ALL_MEM; FORALL_PAIR_THM] THEN
    ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC (ISPEC `exec (build_funs eqs) [] ck (to_ce eqs [] e) (s:hol_refs)`
                PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF]);;

compute_overloads_off ();;
