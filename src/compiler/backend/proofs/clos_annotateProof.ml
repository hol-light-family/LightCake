(* ========================================================================= *)
(* clos_annotateProof: port of HOL4 compiler/backend/proofs/                 *)
(* clos_annotateProofScript.sml (CakeML v3479).                              *)
(* Correctness proof for clos_annotate.                                      *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/db_vars.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/semantics/backendProps.ml";;

type_invention_error := true;;

(* alternative definition of free_vars (fv) function *)

(* HOL4: alt_fv_def *)
let alt_fv_def = cake_def
  `alt_fv n xs <=> has_var n (SND (alt_free xs))`;;

(* HOL4: alt_free_thm *)
let alt_free_thm = prove
 (CASE_TERM `!xs. let (ys,l) = alt_free xs in !n. alt_fv n xs <=> has_var n l`,
  GEN_TAC THEN MP_TAC(ISPEC `alt_free xs` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ys:clos_exp list` (X_CHOOSE_THEN `l:db_var_set` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[alt_fv_def] THEN CASE_REWRITE_TAC[SND]);;

(* HOL4: alt_fv *)
let alt_fv = prove
 (CASE_TERM
  `(!n. alt_fv n [] <=> F) /\
   (!y xs x n. alt_fv n (CONS x (CONS y xs)) <=> alt_fv n [x] \/ alt_fv n (CONS y xs)) /\
   (!v0 v n. alt_fv n [clos_Var v0 v] <=> n = v) /\
   (!x3 x2 x1 v1 n.
      alt_fv n [clos_If v1 x1 x2 x3] <=> alt_fv n [x1] \/ alt_fv n [x2] \/ alt_fv n [x3]) /\
   (!xs x2 v2 n.
      alt_fv n [clos_Let v2 xs x2] <=>
        if no_overlap (LENGTH xs) (SND (alt_free [x2])) /\ ALL pure xs then
          alt_fv (n + LENGTH xs) [x2]
        else
          alt_fv n xs \/ alt_fv (n + LENGTH xs) [x2]) /\
   (!x1 v3 n. alt_fv n [clos_Raise v3 x1] <=> alt_fv n [x1]) /\
   (!x1 v4 n. alt_fv n [clos_Tick v4 x1] <=> alt_fv n [x1]) /\
   (!xs v5 op n. alt_fv n [clos_Op v5 op xs] <=> alt_fv n xs) /\
   (!x2 x1 v6 n loc_opt.
      alt_fv n [clos_App v6 loc_opt x1 x2] <=> alt_fv n [x1] \/ alt_fv n x2) /\
   (!x1 vs v7 num_args n loc.
      alt_fv n [Fn v7 loc vs num_args x1] <=> alt_fv (n + num_args) [x1]) /\
   (!x1 vs v8 n loc fns.
      alt_fv n [clos_Letrec v8 loc vs fns x1] <=>
        EX (\p. match p with
                  (num_args,x) -> alt_fv (n + num_args + LENGTH fns) [x]) fns \/
        alt_fv (n + LENGTH fns) [x1]) /\
   (!x2 x1 v9 n. alt_fv n [clos_Handle v9 x1 x2] <=> alt_fv n [x1] \/ alt_fv (n + 1) [x2]) /\
   (!xs v10 ticks n dest. alt_fv n [clos_Call v10 ticks dest xs] <=> alt_fv n xs)`,
  REWRITE_TAC[alt_fv_def] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[alt_free_def] THEN REPEAT PAIRARG_TAC THEN ASM_REWRITE_TAC[SND] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[SND; has_var_def; has_var_mk_Union] THENL
   [(* Let *)
    COND_CASES_TAC THEN ASM_REWRITE_TAC[SND; has_var_def; has_var_mk_Union];
    (* Letrec *)
    REWRITE_TAC[has_var_list_mk_Union; EX_MAP; o_DEF] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
    CASE_REWRITE_TAC[] THEN PAIRARG_TAC THEN ASM_REWRITE_TAC[SND; has_var_def; ADD_AC]]);;

(* HOL4: alt_fv_nil [simp] *)
let alt_fv_nil = prove
 (`alt_fv v [] <=> F`,
  REWRITE_TAC[alt_fv]);;
let _ = cake_add_simps [alt_fv_nil];;

(* HOL4: alt_fv1_def *)
let alt_fv1_def = cake_def
  `alt_fv1 v e <=> alt_fv v [e]`;;

(* HOL4: alt_fv1_intro [simp] *)
let alt_fv1_intro = GSYM alt_fv1_def;;
let _ = cake_add_simps [alt_fv1_intro];;

(* HOL4: alt_fv1_thm (HOL4 computes it with SIMP_RULE) *)
let alt_fv1_thm = REWRITE_RULE[alt_fv1_intro] alt_fv;;

(* HOL4: alt_fv_cons [simp] *)
let alt_fv_cons = prove
 (`alt_fv v (CONS x xs) <=> alt_fv1 v x \/ alt_fv v xs`,
  CASES_ON `xs:clos_exp list` THEN REWRITE_TAC[alt_fv; alt_fv1_def]);;
let _ = cake_add_simps [alt_fv_cons];;

(* HOL4: alt_fv_REPLICATE [simp] *)
let alt_fv_REPLICATE = prove
 (`alt_fv n (REPLICATE m e) <=> 0 < m /\ alt_fv1 n e`,
  SPEC_TAC(`m:num`,`m:num`) THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[REPLICATE; alt_fv_nil; alt_fv_cons; LT_REFL; LT_0] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [alt_fv_REPLICATE];;

(* value relation *)

(* HOL4: Overload alt_fv_set = (\x y. alt_fv y x); here alt_fv_set xs is     *)
(* written (\n. alt_fv n xs) and alt_fv_set xs n as alt_fv n xs              *)

(* HOL4: v_rel (with env_ok) *)
let clos_annotateProof_v_rel_rules,clos_annotateProof_v_rel_ind,
    clos_annotateProof_v_rel_cases,clos_annotateProof_v_rel_strongind =
  cake_inductive
  `(!j. clos_annotateProof_v_rel (clos_Number j) (clos_Number j)) /\
   (!w. clos_annotateProof_v_rel (clos_Word64 w) (clos_Word64 w)) /\
   (!t xs ys.
      ALL2 clos_annotateProof_v_rel xs ys ==>
      clos_annotateProof_v_rel (clos_Block t xs) (clos_Block t ys)) /\
   (!ws. clos_annotateProof_v_rel (ByteVector ws) (ByteVector ws)) /\
   (!b r1. clos_annotateProof_v_rel (clos_RefPtr b r1) (clos_RefPtr b r1)) /\
   (!c m num_args i c' env env' vals vals' p.
      clos_annotate_shift (FST (alt_free [c])) m num_args i = [c'] /\
      (!n. alt_fv n [c] /\ num_args <= n ==> env_ok m 0 i env env' (n - num_args)) /\
      every_Fn_vs_NONE [c] /\ LENGTH env = m /\
      ALL2 clos_annotateProof_v_rel vals vals' ==>
      clos_annotateProof_v_rel (clos_Closure p vals env num_args c)
                               (clos_Closure p vals' env' num_args c')) /\
   (!cs cs' env env' vals vals' index p.
      ALL2 (\p1 p2. match p1 with
                      (num_args,c1) ->
                        match p2 with
                          (num_args',c1') ->
                            ?m i.
                              num_args' = num_args /\
                              clos_annotate_shift (FST (alt_free [c1])) m
                                (LENGTH cs + num_args) i = [c1'] /\
                              (!n. alt_fv n [c1] /\ num_args + LENGTH cs <= n ==>
                                   env_ok m 0 i env env' (n - (num_args + LENGTH cs))) /\
                              every_Fn_vs_NONE [c1] /\ LENGTH env = m) cs cs' /\
      ALL2 clos_annotateProof_v_rel vals vals' /\ index < LENGTH cs ==>
      clos_annotateProof_v_rel (clos_Recclosure p vals env cs index)
                               (clos_Recclosure p vals' env' cs' index)) /\
   (!m l (i:num spt) env2 env2' n. l + m <= n ==> env_ok m l i env2 env2' n) /\
   (!m l (i:num spt) env2 env2' n.
      n < l /\ clos_annotateProof_v_rel (EL n env2) (EL n env2') /\
      n < LENGTH env2 /\ n < LENGTH env2' ==>
      env_ok m l i env2 env2' n) /\
   (!m l i env2 env2' n v.
      l <= n /\ n < l + m /\ n < l + m /\ lookup (n - l) i = SOME v /\
      n < LENGTH env2 /\ l + v < LENGTH env2' /\
      clos_annotateProof_v_rel (EL n env2) (EL (l + v) env2') ==>
      env_ok m l i env2 env2' n)`;;

(* HOL4: v_rel_simp (HOL4 computes it with SIMP_CONV and v_rel_cases; here *)
(* the same terms are rewritten with the cases theorem and unwound)        *)
let clos_annotateProof_v_rel_simp =
  let conv =
    GEN_REWRITE_CONV I [CONJUNCT1 clos_annotateProof_v_rel_cases] THENC
    REWRITE_CONV[distinctness "clos_v"; injectivity "clos_v"; GSYM CONJ_ASSOC] THENC
    TOP_DEPTH_CONV UNWIND_CONV THENC REWRITE_CONV[] THENC
    TOP_DEPTH_CONV UNWIND_CONV in
  end_itlist CONJ (map (GEN_ALL o conv)
   [`clos_annotateProof_v_rel (clos_Number x) y`;
    `clos_annotateProof_v_rel (clos_Word64 n) y`;
    `clos_annotateProof_v_rel (clos_Block n l) y`;
    `clos_annotateProof_v_rel (ByteVector ws) y`;
    `clos_annotateProof_v_rel (clos_RefPtr b x) y`;
    `clos_annotateProof_v_rel (clos_Closure n l v x w) y`;
    `clos_annotateProof_v_rel (clos_Recclosure x1 x2 x3 x4 x5) y`;
    `clos_annotateProof_v_rel y (clos_Number x)`;
    `clos_annotateProof_v_rel y (clos_Block n l)`;
    `clos_annotateProof_v_rel y (ByteVector ws)`;
    `clos_annotateProof_v_rel y (clos_RefPtr b x)`;
    `clos_annotateProof_v_rel y (clos_Closure n l v x w)`;
    `clos_annotateProof_v_rel y (clos_Word64 n)`;
    `clos_annotateProof_v_rel y (clos_Recclosure x1 x2 x3 x4 x5)`]);;

(* HOL4: v_rel_Boolv [simp] *)
let clos_annotateProof_v_rel_Boolv = prove
 (`(clos_annotateProof_v_rel x (clos_Boolv b) <=> x = clos_Boolv b) /\
   (clos_annotateProof_v_rel (clos_Boolv b) x <=> x = clos_Boolv b)`,
  REWRITE_TAC[clos_Boolv_def; clos_annotateProof_v_rel_simp; LIST_REL_NIL; ALL2] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [clos_annotateProof_v_rel_Boolv];;

(* HOL4: v_rel_Unit [simp] *)
let clos_annotateProof_v_rel_Unit = prove
 (`(clos_annotateProof_v_rel x clos_Unit <=> x = clos_Unit) /\
   (clos_annotateProof_v_rel clos_Unit x <=> x = clos_Unit)`,
  REWRITE_TAC[clos_Unit_def; clos_annotateProof_v_rel_simp; LIST_REL_NIL; ALL2] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [clos_annotateProof_v_rel_Unit];;

(* HOL4: val env_ok_def = v_rel_cases |> CONJUNCT2 *)
let CLOSP1AUX_ann_env_ok_def = CONJUNCT2 clos_annotateProof_v_rel_cases;;

(* HOL4: env_ok_EXTEND [local] *)
let env_ok_EXTEND = prove
 (`ALL2 clos_annotateProof_v_rel env1 env2 /\ l1 = LENGTH env1 /\
   (l1 <= n ==> env_ok m l i env1' env2' (n - l1)) ==>
   env_ok m (l + l1) i (APPEND env1 env1') (APPEND env2 env2') n`,
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  REWRITE_TAC[CLOSP1AUX_ann_env_ok_def; LENGTH_APPEND] THEN
  ASM_CASES_TAC `n < LENGTH (env1:clos_v list)` THENL
   [DISJ2_TAC THEN DISJ1_TAC THEN
    SUBGOAL_THEN `n < LENGTH (env2:clos_v list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_APPEND1] THEN
    UNDISCH_TAC `ALL2 clos_annotateProof_v_rel env1 env2` THEN
    REWRITE_TAC[LIST_REL_EL_EQN] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (env1:clos_v list) <= n /\ LENGTH (env2:clos_v list) <= n`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_APPEND2] THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
                             concl th = `LENGTH (env1:clos_v list) = LENGTH (env2:clos_v list)`
                          then SUBST_ALL_TAC th else NO_TAC) THEN
  REWRITE_TAC[CLOSP1AUX_ann_env_ok_def] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN ASM_ARITH_TAC;
    DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `v:num` THEN
    SUBGOAL_THEN `n - (l + LENGTH (env2:clos_v list)) = n - LENGTH env2 - l /\
                  LENGTH (env2:clos_v list) <= (l + LENGTH env2) + v /\
                  ((l + LENGTH env2) + v) - LENGTH env2 = l + v`
      STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_APPEND2] THEN ASM_ARITH_TAC]);;

(* HOL4: the ML values env_ok_cons, env_ok_1, env_ok_some, env_ok_append, *)
(* instances of env_ok_EXTEND                                              *)
let CLOSP1AUX_ann_env_ok_cons = prove
 (`clos_annotateProof_v_rel v1 v2 /\ (1 <= n ==> env_ok m l i env1' env2' (n - 1)) ==>
   env_ok m (l + 1) i (CONS v1 env1') (CONS v2 env2') n`,
  STRIP_TAC THEN
  MP_TAC(INST [`[v1:clos_v]`,`env1:clos_v list`; `[v2:clos_v]`,`env2:clos_v list`;
               `1`,`l1:num`] env_ok_EXTEND) THEN
  REWRITE_TAC[APPEND; ALL2; LENGTH; GSYM ONE] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let CLOSP1AUX_ann_env_ok_1 = prove
 (`clos_annotateProof_v_rel v1 v2 /\ (1 <= n ==> env_ok m 0 i env1' env2' (n - 1)) ==>
   env_ok m 1 i (CONS v1 env1') (CONS v2 env2') n`,
  MP_TAC(INST [`0`,`l:num`] CLOSP1AUX_ann_env_ok_cons) THEN REWRITE_TAC[ADD_CLAUSES]);;

let CLOSP1AUX_ann_env_ok_some = prove
 (`!env1 env2 env1' env2' m l i n k.
     l + LENGTH env1 = k /\ ALL2 clos_annotateProof_v_rel env1 env2 /\
     (LENGTH env1 <= n ==> env_ok m l i env1' env2' (n - LENGTH env1)) ==>
     env_ok m k i (APPEND env1 env1') (APPEND env2 env2') n`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC env_ok_EXTEND THEN ASM_REWRITE_TAC[]);;

let CLOSP1AUX_ann_env_ok_append = prove
 (`ALL2 clos_annotateProof_v_rel env1 env2 /\ LENGTH env1 = l1 /\
   (l1 <= n ==> env_ok m 0 i env1' env2' (n - l1)) ==>
   env_ok m l1 i (APPEND env1 env1') (APPEND env2 env2') n`,
  STRIP_TAC THEN MP_TAC(INST [`0`,`l:num`] env_ok_EXTEND) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

(* HOL4: env_ok_EXTEND_IGNORE [local] *)
let env_ok_EXTEND_IGNORE = prove
 (`LENGTH env2 = LENGTH env1 /\ LENGTH env1 <= n /\ l1 = LENGTH env1 /\
   env_ok m l i env1' env2' (n - l1) ==>
   env_ok m (l + l1) i (APPEND env1 env1') (APPEND env2 env2') n`,
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `LENGTH (env2:clos_v list) <= n` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `env_ok m l i env1' env2' (n - LENGTH (env1:clos_v list))` THEN
  REWRITE_TAC[CLOSP1AUX_ann_env_ok_def; LENGTH_APPEND] THEN
  ASM_SIMP_TAC[EL_APPEND2] THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN ASM_ARITH_TAC;
    DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `v:num` THEN
    SUBGOAL_THEN `n - (l + LENGTH (env1:clos_v list)) = n - LENGTH env1 - l /\
                  LENGTH (env2:clos_v list) <= (l + LENGTH env1) + v /\
                  ((l + LENGTH env1) + v) - LENGTH (env2:clos_v list) = l + v`
      STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_APPEND2] THEN ASM_ARITH_TAC]);;

(* HOL4: state_rel_def *)
let clos_annotateProof_state_rel_def = cake_def
  `clos_annotateProof_state_rel (s:(C,FFI)clos_state) (t:(C,FFI)clos_state) <=>
     clos_state_clock s = clos_state_clock t /\
     clos_state_ffi s = clos_state_ffi t /\
     clos_state_max_app s = clos_state_max_app t /\
     clos_state_compile_oracle t =
       (I ## clos_annotate_annotate 0 ## clos_annotate_compile) o
       clos_state_compile_oracle s /\
     clos_state_compile s =
       (\cfg p. match p with
                  (es,aux) -> clos_state_compile t cfg
                                (clos_annotate_annotate 0 es, clos_annotate_compile aux)) /\
     ALL2 (OPTREL clos_annotateProof_v_rel) (clos_state_globals s) (clos_state_globals t) /\
     FDOM (clos_state_refs s) = FDOM (clos_state_refs t) /\
     (!n r1. FLOOKUP (clos_state_refs s) n = SOME r1 ==>
             ?r2. FLOOKUP (clos_state_refs t) n = SOME r2 /\
                  clos_ref_rel clos_annotateProof_v_rel r1 r2) /\
     FDOM (clos_state_code s) = FDOM (clos_state_code t) /\
     (!name arity c.
        FLOOKUP (clos_state_code s) name = SOME (arity,c) ==>
        ?c2. clos_annotate_shift (FST (alt_free [c])) 0 arity LN = [c2] /\
             FLOOKUP (clos_state_code t) name = SOME (arity,c2))`;;

(* HOL4: state_rel_max_app *)
let clos_annotateProof_state_rel_max_app = prove
 (`clos_annotateProof_state_rel (s:(C,FFI)clos_state) t ==>
   clos_state_max_app s = clos_state_max_app t`,
  SIMP_TAC[clos_annotateProof_state_rel_def]);;

(* some syntactic properties of the compiler *)

(* HOL4: MAP_FST_compile [simp] *)
let clos_annotateProof_MAP_FST_compile = prove
 (`!p. MAP FST (clos_annotate_compile p) = MAP FST p`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[clos_annotate_compile_def; MAP] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[clos_annotate_compile_def] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPEC `h:num#num#clos_exp` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `y:num#clos_exp` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[FST]);;
let _ = cake_add_simps [clos_annotateProof_MAP_FST_compile];;

(* HOL4: REVERSE_compile *)
let REVERSE_compile = prove
 (`REVERSE (clos_annotate_compile ls) = clos_annotate_compile (REVERSE ls)`,
  REWRITE_TAC[clos_annotate_compile_def; MAP_REVERSE]);;

(* HOL4: ALOOKUP_compile *)
let ALOOKUP_compile = prove
 (CASE_TERM
  `ALOOKUP (clos_annotate_compile ls) =
   OPTION_MAP (\p. match p with
                     (args,e) -> (args, HD (clos_annotate_annotate args [e]))) o
   ALOOKUP ls`,
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  SPEC_TAC(`ls:(num#num#clos_exp)list`,`ls:(num#num#clos_exp)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[clos_annotate_compile_def; MAP; ALOOKUP_THM; OPTION_MAP_DEF] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[clos_annotate_compile_def] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `h:num#num#clos_exp` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `y:num#clos_exp` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[ALOOKUP_THM] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[]);;

(* HOL4: compile_append *)
let compile_append = prove
 (`clos_annotate_compile (APPEND p1 p2) =
   APPEND (clos_annotate_compile p1) (clos_annotate_compile p2)`,
  REWRITE_TAC[clos_annotate_compile_def; MAP_APPEND]);;

(* semantic functions respect relation *)

(* local helpers: clos_ref_rel with the right side known; the references of *)
(* related states; an update of related references                         *)
let CLOSP1AUX_ann_ref_rel_right = prove
 (`(!(R:A->B->bool) x ws. clos_ref_rel R x (clos_ValueArray ws) <=>
                          ?vs. x = clos_ValueArray vs /\ ALL2 R vs ws) /\
   (!(R:A->B->bool) x bs. clos_ref_rel R x (clos_ByteArray bs) <=> x = clos_ByteArray bs) /\
   (!(R:A->B->bool) x m b. clos_ref_rel R x (clos_Thunk m b) <=>
                           ?a. x = clos_Thunk m a /\ R a b)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN CASES_ON `x:(A)clos_ref` THEN
  REWRITE_TAC[clos_ref_rel_def; distinctness "clos_ref"; injectivity "clos_ref"] THEN
  MESON_TAC[]);;

let CLOSP1AUX_ann_flookup_rel = prove
 (`!(s1:(C,FFI)clos_state) s2 n.
     clos_annotateProof_state_rel s1 s2 ==>
     OPTREL (clos_ref_rel clos_annotateProof_v_rel)
            (FLOOKUP (clos_state_refs s1) n) (FLOOKUP (clos_state_refs s2) n)`,
  REWRITE_TAC[clos_annotateProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  CASES_ON `FLOOKUP (clos_state_refs (s1:(C,FFI)clos_state)) n` THENL
   [SUBGOAL_THEN `FLOOKUP (clos_state_refs (s2:(C,FFI)clos_state)) n = NONE` SUBST1_TAC THENL
     [UNDISCH_TAC `FLOOKUP (clos_state_refs (s1:(C,FFI)clos_state)) n = NONE` THEN
      REWRITE_TAC[FLOOKUP_DEF] THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
      REWRITE_TAC[distinctness "option"];
      REWRITE_TAC[OPTREL_THM]];
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `a:(clos_v)clos_ref`] o
                  check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[OPTREL_THM]]);;

let CLOSP1AUX_ann_state_rel_refs_upd = prove
 (`!(s1:(C,FFI)clos_state) s2 p a b.
     clos_annotateProof_state_rel s1 s2 /\ clos_ref_rel clos_annotateProof_v_rel a b ==>
     clos_annotateProof_state_rel
       (clos_state_refs_fupd (K (clos_state_refs s1 |+ (p,a))) s1)
       (clos_state_refs_fupd (K (clos_state_refs s2 |+ (p,b))) s2)`,
  REWRITE_TAC[clos_annotateProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM;
              FDOM_FUPDATE; FLOOKUP_UPDATE] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
           free_in `clos_state_code (s1:(C,FFI)clos_state)` (concl th))) THEN
         ASM_REWRITE_TAC[] THEN NO_TAC;
         POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
         REWRITE_TAC[injectivity "option"] THEN ASM_MESON_TAC[]]);;

(* local helpers: the relations are simple (closProps simple_val_rel and *)
(* simple_state_rel)                                                      *)
let CLOSP1AUX_ann_simple_val_rel = prove
 (`clos_simple_val_rel clos_annotateProof_v_rel`,
  REWRITE_TAC[clos_simple_val_rel_def; clos_annotateProof_v_rel_simp] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[clos_isClos_def]);;

let CLOSP1AUX_ann_simple_state_rel = prove
 (`clos_simple_state_rel clos_annotateProof_v_rel
     (clos_annotateProof_state_rel:(C,FFI)clos_state->(C,FFI)clos_state->bool)`,
  REWRITE_TAC[clos_simple_state_rel_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `ptr:num` o MATCH_MP CLOSP1AUX_ann_flookup_rel) THEN
    ASM_REWRITE_TAC[OPTREL_NONE];
    FIRST_ASSUM(MP_TAC o SPEC `ptr:num` o MATCH_MP CLOSP1AUX_ann_flookup_rel) THEN
    ASM_REWRITE_TAC[OPTREL_SOME; CLOSP1AUX_ann_ref_rel_right] THEN MESON_TAC[];
    FIRST_ASSUM(MP_TAC o SPEC `ptr:num` o MATCH_MP CLOSP1AUX_ann_flookup_rel) THEN
    ASM_REWRITE_TAC[OPTREL_SOME; CLOSP1AUX_ann_ref_rel_right] THEN MESON_TAC[];
    FIRST_ASSUM(MP_TAC o SPEC `ptr:num` o MATCH_MP CLOSP1AUX_ann_flookup_rel) THEN
    ASM_REWRITE_TAC[OPTREL_SOME; CLOSP1AUX_ann_ref_rel_right] THEN MESON_TAC[];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  TRY(MATCH_MP_TAC CLOSP1AUX_ann_state_rel_refs_upd THEN
      ASM_REWRITE_TAC[clos_ref_rel_def] THEN NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_annotateProof_state_rel_def]) THEN
  ASM_REWRITE_TAC[clos_annotateProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM]);;

(* HOL4: list_to_v_v_rel *)
let clos_annotateProof_list_to_v_v_rel = prove
 (`!xs ys. ALL2 clos_annotateProof_v_rel xs ys ==>
           clos_annotateProof_v_rel (clos_list_to_v xs) (clos_list_to_v ys)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM_SIMP_TAC[clos_list_to_v_def; clos_annotateProof_v_rel_simp; injectivity "clos_v";
               UNWIND_THM1; ALL2]);;

(* HOL4: v_to_list [local] *)
let clos_annotateProof_v_to_list = prove
 (`!h h'. clos_annotateProof_v_rel h h' ==>
          (clos_v_to_list h = NONE /\ clos_v_to_list h' = NONE) \/
          ?x x'. clos_v_to_list h = SOME x /\ clos_v_to_list h' = SOME x' /\
                 ALL2 clos_annotateProof_v_rel x x'`,
  MATCH_MP_TAC clos_v_to_list_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try rator (rator (concl th)) =
                                  `clos_annotateProof_v_rel` with Failure _ -> false)) THEN
  REWRITE_TAC[clos_annotateProof_v_rel_simp] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN RVEQ_TAC THEN
  REWRITE_TAC[clos_v_to_list_def] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
    EXISTS_TAC `[]:clos_v list` THEN EXISTS_TAC `[]:clos_v list` THEN REWRITE_TAC[ALL2];
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `h'':clos_v` o C MP (ASSUME `tag = cons_tag`)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
    MAP_EVERY EXISTS_TAC [`CONS (h:clos_v) x`; `CONS (h':clos_v) x'`] THEN
    ASM_REWRITE_TAC[ALL2]]);;

(* HOL4: do_app_lemma [local] *)
let clos_annotateProof_do_app_lemma = prove
 (CASE_TERM
  `clos_annotateProof_state_rel (s:(C,FFI)clos_state) t /\
   ALL2 clos_annotateProof_v_rel xs ys ==>
   match clos_do_app opp xs s with
     Rval (x,s1) -> ?y t1. clos_annotateProof_v_rel x y /\
                           clos_annotateProof_state_rel s1 t1 /\
                           clos_do_app opp ys t = Rval (y,t1)
   | Rerr err1 -> ?err2. clos_do_app opp ys t = Rerr err2 /\
                         exc_rel clos_annotateProof_v_rel err1 err2`,
  STRIP_TAC THEN
  MP_TAC(ISPECL [`clos_annotateProof_v_rel`;
                 `clos_annotateProof_state_rel:(C,FFI)clos_state->(C,FFI)clos_state->bool`;
                 `s:(C,FFI)clos_state`; `t:(C,FFI)clos_state`; `xs:clos_v list`;
                 `ys:clos_v list`; `opp:clos_op`] simple_val_rel_do_app) THEN
  ASM_REWRITE_TAC[CLOSP1AUX_ann_simple_val_rel; CLOSP1AUX_ann_simple_state_rel]);;

(* HOL4: do_app_thm [local] *)
let clos_annotateProof_do_app_thm = prove
 (`clos_annotateProof_state_rel (s1:(C,FFI)clos_state) t1 /\
   ALL2 clos_annotateProof_v_rel xs ys /\ clos_do_app op xs s1 = Rval (v,s2) ==>
   ?w t2. clos_do_app op ys t1 = Rval (w,t2) /\ clos_annotateProof_v_rel v w /\
          clos_annotateProof_state_rel s2 t2`,
  STRIP_TAC THEN
  MP_TAC(INST [`s1:(C,FFI)clos_state`,`s:(C,FFI)clos_state`; `t1:(C,FFI)clos_state`,
               `t:(C,FFI)clos_state`; `op:clos_op`,`opp:clos_op`]
         clos_annotateProof_do_app_lemma) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4: v_rel_Number [local] *)
let clos_annotateProof_v_rel_Number = prove
 (`(clos_annotateProof_v_rel x (clos_Number i) <=> x = clos_Number i) /\
   (clos_annotateProof_v_rel (clos_Number i) x <=> x = clos_Number i) /\
   (clos_annotateProof_v_rel (ByteVector ws) x <=> x = ByteVector ws) /\
   (clos_annotateProof_v_rel x (clos_Word64 w) <=> x = clos_Word64 w) /\
   (clos_annotateProof_v_rel (clos_Word64 w) x <=> x = clos_Word64 w)`,
  REWRITE_TAC[clos_annotateProof_v_rel_simp]);;

(* HOL4: do_app_err_thm [local] *)
let do_app_err_thm = prove
 (`clos_annotateProof_state_rel (s1:(C,FFI)clos_state) t1 /\
   ALL2 clos_annotateProof_v_rel xs ys /\
   clos_do_app op xs s1 = Rerr err /\ ~(err = Rabort Rtype_error) ==>
   ?w. clos_do_app op ys t1 = Rerr w /\ exc_rel clos_annotateProof_v_rel err w`,
  STRIP_TAC THEN
  MP_TAC(INST [`s1:(C,FFI)clos_state`,`s:(C,FFI)clos_state`; `t1:(C,FFI)clos_state`,
               `t:(C,FFI)clos_state`; `op:clos_op`,`opp:clos_op`]
         clos_annotateProof_do_app_lemma) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* HOL4: v_to_bytes *)
let clos_annotateProof_v_to_bytes = prove
 (`clos_annotateProof_v_rel x y ==> clos_v_to_bytes x = clos_v_to_bytes y`,
  MESON_TAC[clos_simple_val_rel_v_to_bytes; CLOSP1AUX_ann_simple_val_rel]);;

(* HOL4: v_to_words *)
let clos_annotateProof_v_to_words = prove
 (`clos_annotateProof_v_rel x y ==> clos_v_to_words x = clos_v_to_words y`,
  MESON_TAC[clos_simple_val_rel_v_to_words; CLOSP1AUX_ann_simple_val_rel]);;

(* a local helper: the states after an installation are related *)
let CLOSP1AUX_ann_install_state = prove
 (`!(s1:(C,FFI)clos_state) t1 aux.
     clos_annotateProof_state_rel s1 t1 ==>
     clos_annotateProof_state_rel
       (clos_state_code_fupd (K (clos_state_code s1 |++ aux))
          (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle s1)))
             (clos_state_clock_fupd (K (clos_state_clock s1 - 1)) s1)))
       (clos_state_code_fupd (K (clos_state_code t1 |++ clos_annotate_compile aux))
          (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle t1)))
             (clos_state_clock_fupd (K (clos_state_clock t1 - 1)) t1)))`,
  REWRITE_TAC[clos_annotateProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM;
              FDOM_FUPDATE_LIST; clos_annotateProof_MAP_FST_compile] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[shift_seq_def; FUN_EQ_THM; o_THM];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `FLOOKUP (clos_state_code (s1:(C,FFI)clos_state) |++ aux) name =
                 SOME (arity,c)` THEN
    REWRITE_TAC[flookup_fupdate_list; REVERSE_compile; ALOOKUP_compile; o_THM] THEN
    CASES_ON `ALOOKUP (REVERSE (aux:(num#num#clos_exp)list)) name` THEN
    REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THENL
     [DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[clos_annotate_annotate_def; PAIR_EQ] THEN
      ONCE_REWRITE_TAC[GSYM HD_FST_alt_free] THEN
      EXISTS_TAC `HD (clos_annotate_shift [HD (FST (alt_free [c:clos_exp]))] 0 arity LN)` THEN
      REWRITE_TAC[HD_shift]]]);;

(* a local helper: an installation with a wrong number of arguments *)
let CLOSP1AUX_ann_do_install_shape = prove
 (`!vs (s:(C,FFI)clos_state).
     ~(LENGTH vs = 2) ==> clos_do_install vs s = (Rerr (Rabort Rtype_error),s)`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `vs:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_do_install_def; LENGTH] THEN CASE_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC (ISPEC `t:clos_v list` list_CASES) THEN
  REWRITE_TAC[LENGTH] THEN CASE_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC (ISPEC `t':clos_v list` list_CASES) THEN
  REWRITE_TAC[LENGTH] THEN CASE_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4: do_install_thm *)
let do_install_thm = prove
 (`clos_annotateProof_state_rel (s1:(C,FFI)clos_state) t1 /\
   ALL2 clos_annotateProof_v_rel xs ys /\
   clos_do_install xs s1 = (res1,s2) /\
   clos_do_install ys t1 = (res2,t2) ==>
   result_rel (\e1 e2. e2 = clos_annotate_annotate 0 e1) (=) res1 res2 /\
   clos_annotateProof_state_rel s2 t2`,
  STRIP_TAC THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
   ASM_CASES_TAC `LENGTH (xs:clos_v list) = 2` THENL
    [ALL_TAC;
     SUBGOAL_THEN `~(LENGTH (ys:clos_v list) = 2)` ASSUME_TAC THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
     REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
              CLOSPROPSAUX_is_app "clos_do_install" (lhs (concl th))))) THEN
     ASM_SIMP_TAC[CLOSP1AUX_ann_do_install_shape; PAIR_EQ] THEN
     REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[result_rel_def; exc_rel_def]] THEN
   UNDISCH_TAC `ALL2 clos_annotateProof_v_rel xs ys` THEN
   UNDISCH_TAC `LENGTH (xs:clos_v list) = 2` THEN
   REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL; ARITH_RULE `2 = SUC 1 /\ 1 = SUC 0`] THEN
   STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[LIST_REL_CONS1; LIST_REL_NIL] THEN
   STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[clos_annotateProof_state_rel_def] o
               check (CLOSPROPSAUX_is_app "clos_annotateProof_state_rel" o concl)) THEN
   REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
            CLOSPROPSAUX_is_app "clos_do_install" (lhs (concl th))))) THEN
   REWRITE_TAC[clos_do_install_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[SYM (MATCH_MP clos_annotateProof_v_to_bytes
                      (ASSUME `clos_annotateProof_v_rel h h''`));
               SYM (MATCH_MP clos_annotateProof_v_to_words
                      (ASSUME `clos_annotateProof_v_rel h' h'''`))] THEN
   CASES_ON `clos_v_to_bytes h` THEN CASES_ON `clos_v_to_words h'` THEN
   CASE_REWRITE_TAC[] THEN
   TRY(REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
       ASM_REWRITE_TAC[result_rel_def; exc_rel_def] THEN NO_TAC) THEN
   ASM_REWRITE_TAC[o_THM] THEN
   MP_TAC(ISPEC `clos_state_compile_oracle (s1:(C,FFI)clos_state) 0` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `cfg:C` (X_CHOOSE_THEN `progs:clos_prog` ASSUME_TAC)) THEN
   MP_TAC(ISPEC `progs:clos_prog` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `es:clos_exp list`
     (X_CHOOSE_THEN `aux:(num#num#clos_exp)list` SUBST_ALL_TAC)) THEN
   ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM] THEN CASE_REWRITE_TAC[] THEN
   CONV_TAC(DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   CASE_REWRITE_TAC[SND; clos_annotateProof_MAP_FST_compile] THEN
  REWRITE_TAC[shift_seq_def; o_THM; FST_PAIR_MAP; I_THM] THEN
   SUBGOAL_THEN `clos_annotate_annotate 0 es = [] <=> es = []` SUBST1_TAC THENL
    [REWRITE_TAC[clos_annotate_annotate_def; GSYM LENGTH_EQ_NIL; shift_LENGTH_LEMMA;
                 LENGTH_FST_alt_free];
     ALL_TAC] THEN
   COND_CASES_TAC THEN REWRITE_TAC[] THEN
   TRY(REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
       ASM_REWRITE_TAC[result_rel_def; exc_rel_def] THEN NO_TAC) THEN
   CASES_ON `clos_state_compile (t1:(C,FFI)clos_state) cfg
               (clos_annotate_annotate 0 es,clos_annotate_compile aux)` THEN
   CASE_REWRITE_TAC[] THEN
   TRY(REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
       ASM_REWRITE_TAC[result_rel_def; exc_rel_def] THEN NO_TAC) THEN
   MP_TAC(ISPEC `a'':byte list#int64 list#C` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `b1:byte list` (X_CHOOSE_THEN `r1:int64 list#C` SUBST_ALL_TAC)) THEN
   MP_TAC(ISPEC `r1:int64 list#C` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `d1:int64 list` (X_CHOOSE_THEN `c1:C` SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
   TRY(REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
       ASM_REWRITE_TAC[result_rel_def; exc_rel_def] THEN NO_TAC) THEN
   MP_TAC(SPECL [`s1:(C,FFI)clos_state`; `t1:(C,FFI)clos_state`;
                 `aux:(num#num#clos_exp)list`] CLOSP1AUX_ann_install_state) THEN
   ASM_REWRITE_TAC[shift_seq_def; o_THM] THEN DISCH_TAC THEN
   COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   ASM_REWRITE_TAC[result_rel_def; exc_rel_def]);;

(* compiler correctness *)

(* HOL4: lookup_EL_shifted_env [local] *)
let lookup_EL_shifted_env = prove
 (`!y n k. n < LENGTH y /\ ALL_DISTINCT y ==>
           lookup (EL n y) (shifted_env k y) = SOME (k + n)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[EL; HD; TL; shifted_env_def; lookup_insert; ALL_DISTINCT;
              ADD_CLAUSES; LT_SUC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(EL n' (t:num list) = h)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[MEM_EL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n':num`; `k + 1`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* HOL4: env_ok_shifted_env [local] *)
let env_ok_shifted_env = prove
 (`env_ok m l i env env2 k /\ MEM k live /\ ALL_DISTINCT live /\
   lookup_vars (MAP (clos_annotate_get_var m l i) (FILTER (\n. n < m + l) live)) env2 =
   SOME x ==>
   env_ok (m + l) 0 (shifted_env 0 (FILTER (\n. n < m + l) live)) env x k`,
  STRIP_TAC THEN
  ABBREV_TAC `y = FILTER (\n. n < m + l) (live:num list)` THEN
  SUBGOAL_THEN `ALL_DISTINCT (y:num list)` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN MATCH_MP_TAC FILTER_ALL_DISTINCT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `k < m + l` THENL
   [ALL_TAC;
    REWRITE_TAC[CLOSP1AUX_ann_env_ok_def] THEN DISJ1_TAC THEN ASM_ARITH_TAC] THEN
  SUBGOAL_THEN `MEM k (y:num list)` MP_TAC THENL
   [EXPAND_TAC "y" THEN ASM_REWRITE_TAC[MEM_FILTER]; ALL_TAC] THEN
  REWRITE_TAC[MEM_EXISTS_EL] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  MP_TAC(ISPECL [`MAP (clos_annotate_get_var (m:num) l (i:num spt)) (y:num list)`; `n:num`;
                 `x:clos_v list`; `env2:clos_v list`] lookup_vars_MEM) THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN ASM_SIMP_TAC[EL_MAP] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP lookup_vars_SOME) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN
  REWRITE_TAC[CLOSP1AUX_ann_env_ok_def] THEN DISJ2_TAC THEN DISJ2_TAC THEN
  EXISTS_TAC `n:num` THEN
  MP_TAC(SPECL [`y:num list`; `n:num`; `0`] lookup_EL_shifted_env) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN DISCH_TAC THEN
  UNDISCH_TAC `env_ok m l i env env2 k` THEN
  REWRITE_TAC[CLOSP1AUX_ann_env_ok_def; clos_annotate_get_var_def] THEN STRIP_TAC THENL
   [ASM_ARITH_TAC;
    ASM_REWRITE_TAC[LE_0] THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `~(k < l)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[zlookup_def; LE_0] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* HOL4: EL_shift_alt_free [local] *)
let EL_shift_alt_free = prove
 (`!fns index. index < LENGTH fns ==>
     [EL index (clos_annotate_shift (FST (alt_free fns)) l m i)] =
     clos_annotate_shift (FST (alt_free [EL index fns])) l m i`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  SUBGOAL_THEN `FST (alt_free (CONS h t)) = CONS (HD (FST (alt_free [h]))) (FST (alt_free t))`
    SUBST1_TAC THENL [MATCH_ACCEPT_TAC alt_free_CONS; ALL_TAC] THEN
  ONCE_REWRITE_TAC[shift_CONS] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `index:num` num_CASES) THEN
  REWRITE_TAC[LT_SUC; LT_0; EL; HD; TL] THENL
   [REWRITE_TAC[HD_shift; HD_FST_alt_free];
    ASM_SIMP_TAC[]]);;

(* HOL4: FOLDR_mk_Union [local] *)
let FOLDR_mk_Union = prove
 (CASE_TERM
  `!ys aux l.
     ITLIST (\p q. match p with
                     (x,l) -> match q with
                                (ts,alt_frees) -> (CONS (x:A) ts, mk_Union l alt_frees))
            ys (aux,l) =
     (APPEND (MAP FST ys) aux, ITLIST mk_Union (MAP SND ys) l)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; MAP; APPEND] THEN
  MP_TAC(ISPEC `h:A#db_var_set` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FST; SND] THEN CASE_REWRITE_TAC[]);;

(* HOL4: evaluate_shift_REPLICATE_const_0 [simp] *)
let evaluate_shift_REPLICATE_const_0 = prove
 (`clos_evaluate (clos_annotate_shift (REPLICATE n (const_0 v8)) m l i,env,
                  (t1:(C,FFI)clos_state)) =
   (Rval (REPLICATE n (clos_Number (&0))),t1)`,
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[REPLICATE; clos_annotate_shift_def; clos_evaluate_def] THEN
  ONCE_REWRITE_TAC[shift_CONS] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN
  ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN
  SUBGOAL_THEN `clos_evaluate ([HD (clos_annotate_shift [const_0 v8] m l i)],env,
                               (t1:(C,FFI)clos_state)) = (Rval [clos_Number (&0)],t1)`
    SUBST1_TAC THENL
   [REWRITE_TAC[const_0_def; clos_annotate_shift_def] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[HD] THEN
    ONCE_REWRITE_TAC[clos_evaluate_def] THEN CASE_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[clos_evaluate_def] THEN CASE_REWRITE_TAC[distinctness "clos_op"; REVERSE] THEN
    REWRITE_TAC[clos_do_app_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[clos_do_int_app_def] THEN CASE_REWRITE_TAC[];
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD]]);;
let _ = cake_add_simps [evaluate_shift_REPLICATE_const_0];;

(* HOL4: no_overlap_has_var_IMP [local] *)
let no_overlap_has_var_IMP = prove
 (`!n l2 x. no_overlap n l2 /\ has_var x l2 ==> n <= x`,
  INDUCT_TAC THEN REWRITE_TAC[no_overlap_def; LE_0] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l2:db_var_set`; `x:num`]) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `x:num = n` THENL [ASM_MESON_TAC[]; ASM_ARITH_TAC]);;

(* HOL4: evaluate_pure_IMP [local] *)
let evaluate_pure_IMP = prove
 (`clos_evaluate (xs,env,(s:(C,FFI)clos_state)) = (q,r) /\ ALL pure xs /\
   ~(q = Rerr (Rabort Rtype_error)) ==>
   ?vs. q = Rval vs /\ r = s /\ LENGTH vs = LENGTH xs`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`xs:clos_exp list`; `env:clos_v list`; `s:(C,FFI)clos_state`]
               EVERY_pure_correct) THEN
  ASM_REWRITE_TAC[] THEN CASES_ON `q:(clos_v list,clos_v)result` THEN
  CASE_REWRITE_TAC[injectivity "result"; UNWIND_THM1] THEN
  CASES_ON `a:(clos_v)error_result` THEN CASE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* HOL4: state_rel_opt_rel_refs [local] *)
let clos_annotateProof_state_rel_opt_rel_refs = prove
 (`(clos_annotateProof_state_rel (s1:(C,FFI)clos_state) s2 /\
    FLOOKUP (clos_state_refs s1) n = r1 ==>
    ?r2. FLOOKUP (clos_state_refs s2) n = r2 /\
         OPTREL (clos_ref_rel clos_annotateProof_v_rel) r1 r2) /\
   (clos_annotateProof_state_rel s1 s2 /\ FLOOKUP (clos_state_refs s2) n = r2 ==>
    ?r1. FLOOKUP (clos_state_refs s1) n = r1 /\
         OPTREL (clos_ref_rel clos_annotateProof_v_rel) r1 r2)`,
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[UNWIND_THM1] THEN
  ASM_SIMP_TAC[CLOSP1AUX_ann_flookup_rel]);;

(* HOL4: state_rel_clocks_eqs [local] *)
let clos_annotateProof_state_rel_clocks_eqs = prove
 (`clos_annotateProof_state_rel (s:(C,FFI)clos_state) t ==>
   clos_state_clock s = clos_state_clock t`,
  SIMP_TAC[clos_annotateProof_state_rel_def]);;

(* a local helper: dest_thunk of related values agree on NotThunk *)
let CLOSP1AUX_ann_not_thunk = prove
 (`!(s1:(C,FFI)clos_state) s2 x y.
     clos_annotateProof_state_rel s1 s2 /\ clos_annotateProof_v_rel x y ==>
     (clos_dest_thunk [x] (clos_state_refs s1) = clos_NotThunk <=>
      clos_dest_thunk [y] (clos_state_refs s2) = clos_NotThunk)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`clos_annotateProof_v_rel`;
                 `clos_annotateProof_state_rel:(C,FFI)clos_state->(C,FFI)clos_state->bool`;
                 `s1:(C,FFI)clos_state`; `s2:(C,FFI)clos_state`;
                 `x:clos_v`; `y:clos_v`; `Evaluated`] CLOSPROPSAUX_bad_thunk_rel) THEN
  ASM_REWRITE_TAC[CLOSP1AUX_ann_simple_val_rel; CLOSP1AUX_ann_simple_state_rel;
                  clos_bad_thunk_update_def] THEN
  MESON_TAC[]);;

(* HOL4: rel_update_thunk [local] *)
let clos_annotateProof_rel_update_thunk = prove
 (`clos_annotateProof_state_rel (s1:(C,FFI)clos_state) s2 /\
   ALL2 clos_annotateProof_v_rel vs ys ==>
   (clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s1) vs = SOME refs1 ==>
    ?refs2. clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s2) ys = SOME refs2 /\
            clos_annotateProof_state_rel (clos_state_refs_fupd (K refs1) s1)
                                         (clos_state_refs_fupd (K refs2) s2))`,
  STRIP_TAC THEN
  SUBGOAL_THEN `(vs = [] /\ ys = []) \/
                (?x y. vs = [x] /\ ys = [y] /\ clos_annotateProof_v_rel x y) \/
                (?x1 x2 r1 y1 y2 r2. vs = CONS x1 (CONS x2 r1) /\
                                     ys = CONS y1 (CONS y2 r2))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ALL2 clos_annotateProof_v_rel vs ys` THEN
    STRUCT_CASES_TAC(ISPEC `vs:clos_v list` list_CASES) THEN
    REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1] THENL [MESON_TAC[]; ALL_TAC] THEN
    STRUCT_CASES_TAC(ISPEC `t:clos_v list` list_CASES) THEN
    REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[CONS_11; NOT_CONS_NIL; UNWIND_THM1] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[clos_update_thunk_def; distinctness "option"];
    ALL_TAC;
    ASM_REWRITE_TAC[clos_update_thunk_def; distinctness "option"]] THEN
  ASM_REWRITE_TAC[clos_update_thunk_def] THEN
  MP_TAC(SPECL [`s1:(C,FFI)clos_state`; `s2:(C,FFI)clos_state`; `x:clos_v`; `y:clos_v`]
               CLOSP1AUX_ann_not_thunk) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  ASM_CASES_TAC `clos_dest_thunk [x] (clos_state_refs (s1:(C,FFI)clos_state)) =
                 clos_NotThunk` THENL
   [SUBGOAL_THEN `clos_dest_thunk [y] (clos_state_refs (s2:(C,FFI)clos_state)) =
                  clos_NotThunk` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[store_thunk_def] THEN
    MP_TAC(SPECL [`s1:(C,FFI)clos_state`; `s2:(C,FFI)clos_state`; `ptr:num`]
                 CLOSP1AUX_ann_flookup_rel) THEN
    ASM_REWRITE_TAC[] THEN
    CASES_ON `FLOOKUP (clos_state_refs (s1:(C,FFI)clos_state)) ptr` THEN
    CASES_ON `FLOOKUP (clos_state_refs (s2:(C,FFI)clos_state)) ptr` THEN
    REWRITE_TAC[OPTREL_THM; case_def "option"; distinctness "option"] THEN
    CASES_ON `a:(clos_v)clos_ref` THEN REWRITE_TAC[clos_ref_rel_simp] THEN
    STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[distinctness "option"] THEN
    TRY(CASES_ON `a0:thunk_mode` THEN CASE_REWRITE_TAC[]) THEN
    REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[UNWIND_THM1] THEN
    MATCH_MP_TAC CLOSP1AUX_ann_state_rel_refs_upd THEN
    ASM_REWRITE_TAC[clos_ref_rel_def];
    REWRITE_TAC[MATCH_MP (ISPECL [`clos_dest_thunk [x] (clos_state_refs (s1:(C,FFI)clos_state))`;
                                  `store_thunk ptr (clos_Thunk Evaluated x)
                                     (clos_state_refs (s1:(C,FFI)clos_state))`]
                                 CLOSSEMAUX_dest_thunk_NONE)
                          (ASSUME `~(clos_dest_thunk [x]
                                       (clos_state_refs (s1:(C,FFI)clos_state)) =
                                     clos_NotThunk)`);
                distinctness "option"]]);;

(* a local helper: the invariant on the code and the oracle of shift_correct *)
(* holds in later states (HOL4: code_tac)                                     *)
let CLOSP1AUX_ann_inv_mono = prove
 (`!(s:(C,FFI)clos_state) (s1:(C,FFI)clos_state).
     CLOSPROPSAUX_code_inv (clos_state_compile_oracle s) (clos_state_code s)
                           (clos_state_compile_oracle s1) (clos_state_code s1) /\
     FEVERY (\p. every_Fn_vs_NONE [SND (SND p)]) (clos_state_code s) /\
     (!n. every_Fn_vs_NONE (FST (SND (clos_state_compile_oracle s n))) /\
          every_Fn_vs_NONE (MAP (SND o SND) (SND (SND (clos_state_compile_oracle s n))))) ==>
     FEVERY (\p. every_Fn_vs_NONE [SND (SND p)]) (clos_state_code s1) /\
     (!n. every_Fn_vs_NONE (FST (SND (clos_state_compile_oracle s1 n))) /\
          every_Fn_vs_NONE (MAP (SND o SND) (SND (SND (clos_state_compile_oracle s1 n)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSPROPSAUX_code_inv_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[shift_seq_def] THEN
  ASM_SIMP_TAC[DISTINCT_FUPDATE_LIST_UNION; DISJOINT_FEVERY_FUNION; FDOM_alist_to_fmap;
               ALL_DISTINCT_FEVERY_alist_to_fmap; EVERY_FLAT; ALL_MAP; EVERY_GENLIST] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl)) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  GEN_REWRITE_TAC (LAND_CONV) [every_Fn_vs_NONE_EVERY] THEN
  REWRITE_TAC[ALL_MAP; o_DEF]);;

(* ------------------------------------------------------------------------- *)
(* The simulation (HOL4: shift_correct), proved by the induction of         *)
(* closProps (CLOSPROPSAUX_evaluate_ind) on the evaluation of the source,   *)
(* with one lemma per case                                                  *)
(* ------------------------------------------------------------------------- *)

let CLOSP1AUX_ann_ind =
  let p = `\xs env (s1:(C,FFI)clos_state).
     !env' t1 res s2 m l i.
       clos_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) /\
       LENGTH env = m + l /\
       (\n. alt_fv n xs) SUBSET env_ok m l i env env' /\
       every_Fn_vs_NONE xs /\
       FEVERY (\p. every_Fn_vs_NONE [SND (SND p)]) (clos_state_code s1) /\
       (!n. every_Fn_vs_NONE (FST (SND (clos_state_compile_oracle s1 n))) /\
            every_Fn_vs_NONE (MAP (SND o SND) (SND (SND (clos_state_compile_oracle s1 n))))) /\
       clos_annotateProof_state_rel s1 t1 ==>
       ?res' t2.
         clos_evaluate (clos_annotate_shift (FST (alt_free xs)) m l i,env',t1) = (res',t2) /\
         result_rel (ALL2 clos_annotateProof_v_rel) clos_annotateProof_v_rel res res' /\
         clos_annotateProof_state_rel s2 t2`
  and q = `\loc_opt f args (s1:(C,FFI)clos_state).
     !res s2 f' args' s1'.
       evaluate_app loc_opt f args s1 = (res,s2) /\
       clos_annotateProof_v_rel f f' /\ ALL2 clos_annotateProof_v_rel args args' /\
       FEVERY (\p. every_Fn_vs_NONE [SND (SND p)]) (clos_state_code s1) /\
       (!n. every_Fn_vs_NONE (FST (SND (clos_state_compile_oracle s1 n))) /\
            every_Fn_vs_NONE (MAP (SND o SND) (SND (SND (clos_state_compile_oracle s1 n))))) /\
       clos_annotateProof_state_rel s1 s1' /\ ~(res = Rerr (Rabort Rtype_error)) ==>
       ?res' s2'.
         evaluate_app loc_opt f' args' s1' = (res',s2') /\
         result_rel (ALL2 clos_annotateProof_v_rel) clos_annotateProof_v_rel res res' /\
         clos_annotateProof_state_rel s2 s2'` in
  CONV_RULE (DEPTH_CONV BETA_CONV) (ISPECL [p;q] CLOSPROPSAUX_evaluate_ind);;
let CLOSP1AUX_ann_cases = conjuncts (lhand (concl CLOSP1AUX_ann_ind));;

(* local helpers: the expressions computed by alt_free, by constructor, and *)
(* the singleton results of shift after alt_free                             *)
let CLOSP1AUX_ann_alt_free_FST = prove
 (`(!x y xs. FST (alt_free (CONS x (CONS y xs))) =
             APPEND (FST (alt_free [x])) (FST (alt_free (CONS y xs)))) /\
   (!t v. FST (alt_free [clos_Var t v]) = [clos_Var t v]) /\
   (!t x1 x2 x3. FST (alt_free [clos_If t x1 x2 x3]) =
                 [clos_If t (HD (FST (alt_free [x1]))) (HD (FST (alt_free [x2])))
                            (HD (FST (alt_free [x3])))]) /\
   (!t xs x2. FST (alt_free [clos_Let t xs x2]) =
              if no_overlap (LENGTH xs) (SND (alt_free [x2])) /\ ALL pure xs
              then [clos_Let t (REPLICATE (LENGTH xs) (const_0 t)) (HD (FST (alt_free [x2])))]
              else [clos_Let t (FST (alt_free xs)) (HD (FST (alt_free [x2])))]) /\
   (!t x1. FST (alt_free [clos_Raise t x1]) = [clos_Raise t (HD (FST (alt_free [x1])))]) /\
   (!t x1. FST (alt_free [clos_Tick t x1]) = [clos_Tick t (HD (FST (alt_free [x1])))]) /\
   (!t op xs. FST (alt_free [clos_Op t op xs]) = [clos_Op t op (FST (alt_free xs))]) /\
   (!t loc_opt x1 xs2.
      FST (alt_free [clos_App t loc_opt x1 xs2]) =
      [clos_App t loc_opt (HD (FST (alt_free [x1]))) (FST (alt_free xs2))]) /\
   (!nm loc vs num_args x1.
      FST (alt_free [Fn nm loc vs num_args x1]) =
      [Fn nm loc (SOME (vars_to_list (db_vars_Shift num_args (SND (alt_free [x1])))))
          num_args (HD (FST (alt_free [x1])))]) /\
   (!t x1 x2. FST (alt_free [clos_Handle t x1 x2]) =
              [clos_Handle t (HD (FST (alt_free [x1]))) (HD (FST (alt_free [x2])))]) /\
   (!t ticks dest xs. FST (alt_free [clos_Call t ticks dest xs]) =
                      [clos_Call t ticks dest (FST (alt_free xs))])`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[alt_free_def] THEN REPEAT PAIRARG_TAC THEN ASM_REWRITE_TAC[FST; SND] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[FST; SND] THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[FST]));;

let CLOSP1AUX_ann_HD_shift = prove
 (`!x m l i. [HD (clos_annotate_shift (FST (alt_free [x])) m l i)] =
             clos_annotate_shift (FST (alt_free [x])) m l i`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM HD_FST_alt_free] THEN REWRITE_TAC[HD_shift]);;

let CLOSP1AUX_ann_shift_thm = CONV_RULE (DEPTH_CONV let_CONV) clos_annotate_shift_def;;

(* the target of an expression after alt_free and shift, normalised *)
let CLOSP1AUX_ANN_TGT_TAC : tactic =
  REWRITE_TAC[CLOSP1AUX_ann_alt_free_FST; CLOSP1AUX_ann_shift_thm] THEN
  REWRITE_TAC[HD_FST_alt_free; CLOSP1AUX_ann_HD_shift];;

(* the end of a case: the existential target result unwound *)
let CLOSP1AUX_ANN_FIN_TAC : tactic =
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC] THEN CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  ASM_REWRITE_TAC[result_rel_def; exc_rel_def; ALL2];;

let CLOSP1AUX_ann_nil = prove
 (el 0 CLOSP1AUX_ann_cases,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_evaluate_def; PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN REWRITE_TAC[alt_free_def; FST; clos_annotate_shift_def; clos_evaluate_def] THEN
  CLOSP1AUX_ANN_FIN_TAC);;

let CLOSP1AUX_ann_var = prove
 (el 2 CLOSP1AUX_ann_cases,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
                  CLOSPROPSAUX_is_app "clos_evaluate" (lhs (concl th)))) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN CLOSP1AUX_ANN_TGT_TAC THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o CONV_RULE(DEPTH_CONV BETA_CONV) o
                REWRITE_RULE[SUBSET; IN] o check (CLOSPROPSAUX_is_app "SUBSET" o concl)) THEN
  REWRITE_TAC[alt_fv1_thm; alt_fv1_intro] THEN
  REWRITE_TAC[CLOSP1AUX_ann_env_ok_def; clos_annotate_get_var_def; zlookup_def] THEN
  STRIP_TAC THENL
   [ASM_ARITH_TAC;
    CLOSP1AUX_ANN_FIN_TAC;
    SUBGOAL_THEN `~(n < l)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CLOSP1AUX_ANN_FIN_TAC]);;

(* local tactics of the simulation: an induction hypothesis of P or Q shape *)
(* (forall, then an implication whose first antecedent is an evaluation)   *)
let CLOSP1AUX_ann_is_PQ name th =
  let c = snd(strip_forall(concl th)) in
  is_imp c && is_conj (lhand c) &&
  (let a = lhand (lhand c) in
   is_eq a && CLOSPROPSAUX_is_app name (lhs a) && is_pair (rhs a) &&
   is_var (lhand (rhs a)));;
let CLOSP1AUX_ann_is_P = CLOSP1AUX_ann_is_PQ "clos_evaluate";;
let CLOSP1AUX_ann_is_Q = CLOSP1AUX_ann_is_PQ "evaluate_app";;

(* resolve the conditional induction hypotheses with the assumptions *)
let CLOSP1AUX_ANN_COND_IH_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let mentions_eval t =
    can (find_term (fun t -> try let n = fst(dest_const t) in
                                 n = "clos_evaluate" || n = "evaluate_app"
                             with Failure _ -> false)) t in
  let is_cond_ih th =
    not (CLOSP1AUX_ann_is_P th) && not (CLOSP1AUX_ann_is_Q th) &&
    (let c = snd(strip_forall(concl th)) in
     is_imp c && mentions_eval (rand c) && is_forall (rand c)) in
  let cihs = filter is_cond_ih asms in
  let try_prove th =
    let vs,c = strip_forall (concl th) in
    if is_imp c then
      let a = lhand c in
      if exists (fun v -> free_in v a) vs then [] else
      [GENL vs (MP (SPECL vs th)
                   (try EQT_ELIM (REWRITE_CONV [HD] a)
                    with Failure _ -> EQT_ELIM (REWRITE_CONV (HD :: asms) a)))]
    else [] in
  let rec resolve depth th =
    if CLOSP1AUX_ann_is_P th || CLOSP1AUX_ann_is_Q th then [th]
    else if depth = 0 then [] else
    let rs = mapfilter (fun a -> MATCH_MP th a) asms @ (try try_prove th with Failure _ -> []) in
    flat (map (resolve (depth-1)) rs) in
  let res = flat (map (fun th -> resolve 4 (CLOSPROPSAUX_curry_top th)) cihs) in
  let res = filter (fun th -> not (exists (fun a -> aconv (concl a) (concl th)) asms)) res in
  MAP_EVERY ASSUME_TAC res gl;;

(* name the first source evaluation of the antecedent of the goal that is  *)
(* not yet named: rrK, ssK; the result variable is remembered              *)
let CLOSP1AUX_ann_counter = ref 0;;
let CLOSP1AUX_ann_last = ref `T`;;
let rec CLOSP1AUX_ann_free_evals tm =
  if is_abs tm then [] else
  (if is_comb tm && CLOSPROPSAUX_is_app "clos_evaluate" tm then [tm] else []) @
  (if is_comb tm then CLOSP1AUX_ann_free_evals (rator tm) @ CLOSP1AUX_ann_free_evals (rand tm)
   else []);;
let CLOSP1AUX_ANN_NAME_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w in
  let named = mapfilter (fun (_,th) -> lhs (concl th)) asl in
  let evs = filter (fun t -> not (mem t named)) (CLOSP1AUX_ann_free_evals ant) in
  let tm = hd evs in
  let rty,sty = (match dest_type (type_of tm) with (_,[a;b]) -> a,b | _ -> failwith "NAME") in
  incr CLOSP1AUX_ann_counter;
  let k = string_of_int (!CLOSP1AUX_ann_counter) in
  let r = mk_var("rr" ^ k, rty) and s = mk_var("ss" ^ k, sty) in
  CLOSP1AUX_ann_last := r;
  (MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN r (X_CHOOSE_THEN s ASSUME_TAC)) THEN
   POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)) gl;;

(* the named result is not a type error (else the result of the case is one) *)
let CLOSP1AUX_ANN_NOT_TE_TAC : tactic = fun (asl,w as gl) ->
  let r = !CLOSP1AUX_ann_last in
  let tm = mk_eq(r, mk_comb(mk_const("Rerr",[type_of r |> dest_type |> snd |> hd, aty;
                                               type_of r |> dest_type |> snd |> tl |> hd, bty]),
                            `Rabort Rtype_error:(clos_v)error_result`)) in
  (ASM_CASES_TAC tm THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
     STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
     ALL_TAC]) gl;;

(* the invariant on the code and the oracle in the state of the named      *)
(* evaluation, from the invariant in its first state                        *)
let CLOSP1AUX_ANN_INV_TAC : tactic = fun (asl,w as gl) ->
  let r = !CLOSP1AUX_ann_last in
  let ev = find (fun th -> let c = concl th in is_eq c && is_pair (rhs c) &&
                   fst (dest_pair (rhs c)) = r) (map snd asl) in
  let ci = MATCH_MP (CONJUNCT1 CLOSPROPSAUX_evaluate_code_lemma) ev in
  (MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] CLOSP1AUX_ann_inv_mono) ci) THEN
   ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   STRIP_TAC) gl;;

(* apply the P-shaped induction hypothesis of the named evaluation to the  *)
(* target evaluation in the goal; dtac proves its antecedents; the target  *)
(* result is named rr'K, ttK                                                *)
let CLOSP1AUX_ANN_IH_TAC (dtac:tactic) : tactic = fun (asl,w as gl) ->
  let r = !CLOSP1AUX_ann_last in
  let asms = map snd asl in
  let ev = find (fun th -> let c = concl th in is_eq c && is_pair (rhs c) &&
                   fst (dest_pair (rhs c)) = r) asms in
  let src = lhs (concl ev) in
  let x = fst (dest_pair (rand src)) in
  let ss = snd (dest_pair (rhs (concl ev))) in
  let tgt = find_term (fun t -> is_comb t && CLOSPROPSAUX_is_app "clos_evaluate" t &&
              (let a = fst (dest_pair (rand t)) in
               CLOSPROPSAUX_is_app "clos_annotate_shift" a &&
               (let f = hd (snd (strip_comb a)) in
                CLOSPROPSAUX_is_app "FST" f && rand (rand f) = x))) (rand w) in
  let a,bc = dest_pair (rand tgt) in
  let e',t = dest_pair bc in
  let [_;mm;ll;ii] = snd (strip_comb a) in
  let use ih =
    let vs,bod = strip_forall (concl ih) in
    let ev1 = lhand (lhand bod) in
    if lhs ev1 = src then SPECL [e'; t; r; ss; mm; ll; ii] ih else failwith "use" in
  let ih = tryfind use (filter CLOSP1AUX_ann_is_P asms) in
  let k = string_of_int (!CLOSP1AUX_ann_counter) in
  let r' = mk_var("rr'" ^ k, type_of r) and t' = mk_var("tt" ^ k, type_of t) in
  (MP_TAC ih THEN ANTS_TAC THENL [dtac; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN r' (X_CHOOSE_THEN t' STRIP_ASSUME_TAC)) THEN
   FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = tgt
                         then REWRITE_TAC[th] else NO_TAC)) gl;;

(* split the named source result; the target result follows *)
let CLOSP1AUX_ANN_SPLIT_TAC : tactic = fun (asl,w as gl) ->
  let r = !CLOSP1AUX_ann_last in
  (CASES_ON r THEN
   FIRST_X_ASSUM(fun th -> let c = concl th in
     if CLOSPROPSAUX_is_app "result_rel" c && is_var (rand c) &&
        (CLOSPROPSAUX_is_app "Rval" (rand (rator c)) ||
         CLOSPROPSAUX_is_app "Rerr" (rand (rator c)))
     then MP_TAC th else NO_TAC) THEN
   REWRITE_TAC[result_rel_Rval; result_rel_Rerr1] THEN
   DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
   DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
   CASE_REWRITE_TAC[]) gl;;

(* local helpers: related states with decreased clocks; the code and the  *)
(* oracle of a state with a decreased clock                                 *)
let CLOSP1AUX_ann_state_rel_dec_clock = prove
 (`!(s:(C,FFI)clos_state) t k.
     clos_annotateProof_state_rel s t ==>
     clos_annotateProof_state_rel (clos_dec_clock k s) (clos_dec_clock k t)`,
  REWRITE_TAC[clos_annotateProof_state_rel_def; clos_dec_clock_def;
              clos_state_INFO.ri_accfupds; K_THM] THEN SIMP_TAC[]);;

let CLOSP1AUX_ann_dec_clock_code = prove
 (`!(s:(C,FFI)clos_state) k.
     clos_state_code (clos_dec_clock k s) = clos_state_code s /\
     clos_state_compile_oracle (clos_dec_clock k s) = clos_state_compile_oracle s`,
  REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM]);;

(* the antecedents of an induction hypothesis in the same environment *)
let CLOSP1AUX_ANN_SUBSET_TAC : tactic =
  REWRITE_TAC[SUBSET; IN] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o CONV_RULE(DEPTH_CONV BETA_CONV) o REWRITE_RULE[SUBSET; IN] o
              check (CLOSPROPSAUX_is_app "SUBSET" o concl)) THEN
  REWRITE_TAC[alt_fv] THEN ASM_REWRITE_TAC[];;

let CLOSP1AUX_ANN_EVERY_FN_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSPROPSAUX_is_app "every_Fn_vs_NONE" o concl))) THEN
  REWRITE_TAC[every_Fn_vs_NONE_def] THEN SIMP_TAC[];;

(* the antecedents of an induction hypothesis *)
let CLOSP1AUX_ANN_DISCH_TAC : tactic =
  REWRITE_TAC[HD] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(CLOSP1AUX_ANN_SUBSET_TAC THEN NO_TAC) THEN
  TRY(CLOSP1AUX_ANN_EVERY_FN_TAC THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC CLOSP1AUX_ann_state_rel_dec_clock THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  TRY(REWRITE_TAC[CLOSP1AUX_ann_dec_clock_code] THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC);;

(* the named evaluation, its type error excluded, its invariant, the       *)
(* induction hypothesis applied, its result split                           *)
let CLOSP1AUX_ANN_STEP_TAC (dtac:tactic) : tactic =
  CLOSP1AUX_ANN_COND_IH_TAC THEN CLOSP1AUX_ANN_NAME_TAC THEN CLOSP1AUX_ANN_NOT_TE_TAC THEN
  CLOSP1AUX_ANN_INV_TAC THEN CLOSP1AUX_ANN_IH_TAC dtac THEN CLOSP1AUX_ANN_SPLIT_TAC;;

(* unfold the source evaluation and normalise the target *)
let CLOSP1AUX_ANN_UNFOLD_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
                  CLOSPROPSAUX_is_app "clos_evaluate" (lhs (concl th)))) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN CLOSP1AUX_ANN_TGT_TAC;;

(* a local helper: shift of the alt_free of a CONS *)
let CLOSP1AUX_ann_shift_append = prove
 (`!x rest m l i.
     clos_annotate_shift (APPEND (FST (alt_free [x])) rest) m l i =
     CONS (HD (clos_annotate_shift (FST (alt_free [x])) m l i))
          (clos_annotate_shift rest m l i)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM HD_FST_alt_free] THEN
  REWRITE_TAC[APPEND] THEN ONCE_REWRITE_TAC[shift_CONS] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[HD]);;

(* singleton results: clos_evaluate ([e],env,s) = (Rval a,s') gives a = [r]; *)
(* related lists of a known shape are split                                 *)
let CLOSP1AUX_ANN_SING_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && CLOSPROPSAUX_is_app "clos_evaluate" (lhs c) &&
       (let r = fst(dest_pair(rhs c)) in
        CLOSPROPSAUX_is_app "Rval" r && is_var (rand r))
    then (STRIP_ASSUME_TAC(MATCH_MP clos_evaluate_SING th) THEN ASSUME_TAC th)
    else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_var (lhs (concl th)) &&
                              is_cons (rhs (concl th)) then SUBST_ALL_TAC th else NO_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if CLOSPROPSAUX_is_app "ALL2" c &&
       ((is_cons (lhand c) && (is_var (rand c) || is_cons (rand c))) ||
        (is_var (lhand c) && is_cons (rand c)))
    then MP_TAC th THEN REWRITE_TAC[LIST_REL_CONS1; LIST_REL_CONS2; LIST_REL_NIL; ALL2] THEN
         STRIP_TAC THEN RVEQ_TAC
    else NO_TAC));;


(* a local helper: related values are the same boolean *)
let CLOSP1AUX_ann_v_rel_Boolv_eq = prove
 (`!x y. clos_annotateProof_v_rel x y ==> !b. clos_Boolv b = x <=> clos_Boolv b = y`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_annotateProof_v_rel_Boolv]) THEN ASM_REWRITE_TAC[]);;

(* the tests of the target on booleans are those of the source *)
let CLOSP1AUX_ANN_BOOLV_TAC : tactic =
  CLOSP1AUX_ANN_SING_TAC THEN REWRITE_TAC[HD] THEN
  (fun (asl,w as gl) ->
     let ths = mapfilter (fun (_,th) -> MATCH_MP CLOSP1AUX_ann_v_rel_Boolv_eq th) asl in
     REWRITE_TAC (map GSYM ths) gl);;

(* the end of a case: the results are related *)
let CLOSP1AUX_ANN_END_TAC : tactic =
  TRY DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  CLOSP1AUX_ANN_SING_TAC THEN CLOSP1AUX_ANN_FIN_TAC THEN ASM_REWRITE_TAC[HD; ALL2];;

(* the result is that of a subexpression or of an application: its        *)
(* induction hypothesis                                                     *)
let CLOSP1AUX_ANN_TAIL_TAC (dtac:tactic) : tactic =
  TRY DISCH_TAC THEN CLOSP1AUX_ANN_COND_IH_TAC THEN
  FIRST_ASSUM(fun ih -> if CLOSP1AUX_ann_is_P ih || CLOSP1AUX_ann_is_Q ih
                        then MATCH_MP_TAC ih THEN dtac THEN NO_TAC else NO_TAC);;

let CLOSP1AUX_ann_cons = prove
 (el 1 CLOSP1AUX_ann_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
                 CLOSPROPSAUX_is_app "clos_evaluate" (lhs (concl th)))) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN
  REWRITE_TAC[CLOSP1AUX_ann_alt_free_FST; CLOSP1AUX_ann_shift_append] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [clos_evaluate_CONS] THEN
  REWRITE_TAC[CLOSP1AUX_ann_HD_shift] THEN
  REPEAT (CLOSP1AUX_ANN_STEP_TAC CLOSP1AUX_ANN_DISCH_TAC) THEN CLOSP1AUX_ANN_END_TAC);;

let CLOSP1AUX_ann_if = prove
 (el 3 CLOSP1AUX_ann_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_ANN_UNFOLD_TAC THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN REWRITE_TAC[CLOSP1AUX_ann_HD_shift] THEN
  CLOSP1AUX_ANN_STEP_TAC CLOSP1AUX_ANN_DISCH_TAC THENL
   [CLOSP1AUX_ANN_BOOLV_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    FIRST [CLOSP1AUX_ANN_TAIL_TAC CLOSP1AUX_ANN_DISCH_TAC; CLOSP1AUX_ANN_END_TAC];
    CLOSP1AUX_ANN_END_TAC]);;

(* the simple cases: the subexpressions in the environment of the expression *)
let CLOSP1AUX_ANN_SIMPLE_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_ANN_UNFOLD_TAC THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN REWRITE_TAC[CLOSP1AUX_ann_HD_shift] THEN
  REPEAT (CLOSP1AUX_ANN_STEP_TAC CLOSP1AUX_ANN_DISCH_TAC) THEN CLOSP1AUX_ANN_END_TAC;;

let CLOSP1AUX_ann_raise = prove
 (el 5 CLOSP1AUX_ann_cases,
  CLOSP1AUX_ANN_SIMPLE_TAC);;

let CLOSP1AUX_ann_tick = prove
 (el 11 CLOSP1AUX_ann_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_ANN_UNFOLD_TAC THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN REWRITE_TAC[CLOSP1AUX_ann_HD_shift] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM (MATCH_MP clos_annotateProof_state_rel_clocks_eqs th)]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN CLOSP1AUX_ANN_FIN_TAC;
    CLOSP1AUX_ANN_TAIL_TAC CLOSP1AUX_ANN_DISCH_TAC]);;

let CLOSP1AUX_ann_let = prove
 (el 4 CLOSP1AUX_ann_cases,
  (REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_ANN_UNFOLD_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[CLOSP1AUX_ann_shift_thm; HD_FST_alt_free] THEN
      ONCE_REWRITE_TAC[clos_evaluate_def] THEN REWRITE_TAC[CLOSP1AUX_ann_HD_shift] THENL
       [FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th -> is_conj (concl th) &&
          CLOSPROPSAUX_is_app "no_overlap" (lhand (concl th)))); ALL_TAC]) THENL
  [(* pure bindings: dummies *)
   REWRITE_TAC[evaluate_shift_REPLICATE_const_0; LENGTH_REPLICATE] THEN CASE_REWRITE_TAC[] THEN
    CLOSP1AUX_ANN_NAME_TAC THEN CLOSP1AUX_ANN_NOT_TE_TAC THEN
    FIRST_ASSUM(fun th -> if is_eq (concl th) && is_pair (rhs (concl th)) &&
                             fst (dest_pair (rhs (concl th))) = !CLOSP1AUX_ann_last
      then MP_TAC (MATCH_MP evaluate_pure_IMP (CONJ th (CONJ (ASSUME `ALL pure xs`)
              (ASSUME (mk_neg (mk_eq (!CLOSP1AUX_ann_last,
                                      `Rerr (Rabort Rtype_error):(clos_v list,clos_v)result`)))))))
      else NO_TAC) THEN
    STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[] THEN
   DISCH_TAC THEN CLOSP1AUX_ANN_COND_IH_TAC THEN
    FIRST_ASSUM(fun ih -> if CLOSP1AUX_ann_is_P ih then MATCH_MP_TAC ih else NO_TAC) THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(CLOSP1AUX_ANN_EVERY_FN_TAC THEN NO_TAC) THEN
    TRY(REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC THEN NO_TAC) THEN
    SUBGOAL_THEN `!nn. alt_fv nn [x2] ==> LENGTH (xs:clos_exp list) <= nn` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC no_overlap_has_var_IMP THEN
      EXISTS_TAC `SND (alt_free [x2])` THEN ASM_REWRITE_TAC[GSYM alt_fv_def];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC env_ok_EXTEND_IGNORE THEN
    ASM_SIMP_TAC[LENGTH_REPLICATE] THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONV_RULE(DEPTH_CONV BETA_CONV) o REWRITE_RULE[SUBSET; IN] o
                check (CLOSPROPSAUX_is_app "SUBSET" o concl)) THEN
    ASM_REWRITE_TAC[alt_fv] THEN
    SUBGOAL_THEN `(nn - LENGTH (xs:clos_exp list)) + LENGTH xs = nn` SUBST1_TAC THENL
     [MATCH_MP_TAC SUB_ADD THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]];
   (* the bindings evaluated *)
   CLOSP1AUX_ANN_STEP_TAC CLOSP1AUX_ANN_DISCH_TAC THENL [ALL_TAC; CLOSP1AUX_ANN_END_TAC] THEN
    DISCH_TAC THEN CLOSP1AUX_ANN_COND_IH_TAC THEN
    FIRST_ASSUM(fun ih -> if CLOSP1AUX_ann_is_P ih then MATCH_MP_TAC ih else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if is_eq (concl th) &&
                            CLOSPROPSAUX_is_app "clos_evaluate" (lhs (concl th)) &&
                             fst (dest_pair (rand (lhs (concl th)))) = `xs:clos_exp list`
                          then ASSUME_TAC (MATCH_MP clos_evaluate_IMP_LENGTH th) else NO_TAC) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH o
                check (fun th -> CLOSPROPSAUX_is_app "ALL2" (concl th))) THEN
    REWRITE_TAC[LENGTH_FST_alt_free] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(CLOSP1AUX_ANN_EVERY_FN_TAC THEN NO_TAC) THEN
    TRY(REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC THEN NO_TAC) THEN
    REWRITE_TAC[SUBSET; IN] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC env_ok_EXTEND THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONV_RULE(DEPTH_CONV BETA_CONV) o REWRITE_RULE[SUBSET; IN] o
                check (CLOSPROPSAUX_is_app "SUBSET" o concl)) THEN
    ASM_REWRITE_TAC[alt_fv] THEN DISJ2_TAC THEN ASM_SIMP_TAC[SUB_ADD]]);;

let CLOSP1AUX_ann_handle = prove
 (el 6 CLOSP1AUX_ann_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_ANN_UNFOLD_TAC THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN REWRITE_TAC[CLOSP1AUX_ann_HD_shift] THEN
   CLOSP1AUX_ANN_STEP_TAC CLOSP1AUX_ANN_DISCH_TAC THENL [CLOSP1AUX_ANN_END_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(fun th -> if CLOSPROPSAUX_is_app "exc_rel" (concl th) then MP_TAC th
                           else NO_TAC) THEN
   CASES_ON `a:(clos_v)error_result` THEN
   REWRITE_TAC[exc_rel_raise1; exc_rel_type_error1] THEN STRIP_TAC THEN RVEQ_TAC THEN
   CASE_REWRITE_TAC[] THENL [ALL_TAC; CLOSP1AUX_ANN_END_TAC] THEN
  DISCH_TAC THEN CLOSP1AUX_ANN_COND_IH_TAC THEN
   FIRST_ASSUM(fun ih -> if CLOSP1AUX_ann_is_P ih then MATCH_MP_TAC ih else NO_TAC) THEN
   REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
   TRY(CLOSP1AUX_ANN_EVERY_FN_TAC THEN NO_TAC) THEN
   TRY(REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC THEN NO_TAC) THEN
   REWRITE_TAC[SUBSET; IN] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
   MATCH_MP_TAC CLOSP1AUX_ann_env_ok_cons THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   FIRST_ASSUM(MATCH_MP_TAC o CONV_RULE(DEPTH_CONV BETA_CONV) o REWRITE_RULE[SUBSET; IN] o
               check (CLOSPROPSAUX_is_app "SUBSET" o concl)) THEN
   ASM_SIMP_TAC[alt_fv; SUB_ADD]);;

let CLOSP1AUX_ann_app = prove
 (el 10 CLOSP1AUX_ann_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_ANN_UNFOLD_TAC THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN
   REWRITE_TAC[CLOSP1AUX_ann_HD_shift; shift_LENGTH_LEMMA; LENGTH_FST_alt_free] THEN
   COND_CASES_TAC THENL [ALL_TAC; CLOSP1AUX_ANN_END_TAC] THEN
   CLOSP1AUX_ANN_STEP_TAC CLOSP1AUX_ANN_DISCH_TAC THENL [ALL_TAC; CLOSP1AUX_ANN_END_TAC] THEN
   CLOSP1AUX_ANN_STEP_TAC CLOSP1AUX_ANN_DISCH_TAC THENL [ALL_TAC; CLOSP1AUX_ANN_END_TAC] THEN
   CLOSP1AUX_ANN_SING_TAC THEN REWRITE_TAC[HD] THEN
  CLOSP1AUX_ANN_TAIL_TAC CLOSP1AUX_ANN_DISCH_TAC);;

let CLOSP1AUX_ann_app_nil = prove
 (el 13 CLOSP1AUX_ann_cases,
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_app_NIL; LIST_REL_NIL; PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN REWRITE_TAC[evaluate_app_NIL] THEN CLOSP1AUX_ANN_FIN_TAC);;

(* local helpers: related states with the clock set to zero; the code found *)
(* by a call in related states                                              *)
let CLOSP1AUX_ann_state_rel_clock0 = prove
 (`!(s:(C,FFI)clos_state) t.
     clos_annotateProof_state_rel s t ==>
     clos_annotateProof_state_rel (clos_state_clock_fupd (K 0) s)
                                  (clos_state_clock_fupd (K 0) t)`,
  REWRITE_TAC[clos_annotateProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[]);;

let CLOSP1AUX_ann_state_rel_code = prove
 (`!(s:(C,FFI)clos_state) t name arity c.
     clos_annotateProof_state_rel s t /\ FLOOKUP (clos_state_code s) name = SOME (arity,c) ==>
     ?c2. clos_annotate_shift (FST (alt_free [c])) 0 arity LN = [c2] /\
          FLOOKUP (clos_state_code t) name = SOME (arity,c2)`,
  REWRITE_TAC[clos_annotateProof_state_rel_def] THEN MESON_TAC[]);;

let CLOSP1AUX_ann_find_code = prove
 (`!(s:(C,FFI)clos_state) t dest vs ys args exp.
     clos_annotateProof_state_rel s t /\ ALL2 clos_annotateProof_v_rel vs ys /\
     clos_find_code dest vs (clos_state_code s) = SOME (args,exp) ==>
     args = vs /\ FLOOKUP (clos_state_code s) dest = SOME (LENGTH vs,exp) /\
     ?c2. clos_find_code dest ys (clos_state_code t) = SOME (ys,c2) /\
          clos_annotate_shift (FST (alt_free [exp])) 0 (LENGTH vs) LN = [c2]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_find_code_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `SOME (args,exp):(clos_v list#clos_exp)option`)) THEN
  CASES_ON `FLOOKUP (clos_state_code (s:(C,FFI)clos_state)) dest` THEN
  CASE_REWRITE_TAC[distinctness "option"] THEN
  MP_TAC(ISPEC `a:num#clos_exp` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[injectivity "option"; distinctness "option"; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CLOSP1AUX_ann_state_rel_code o
              CONJ (ASSUME `clos_annotateProof_state_rel (s:(C,FFI)clos_state) t`)) THEN
  STRIP_TAC THEN EXISTS_TAC `c2:clos_exp` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* the pair of the antecedent split into args and exp *)
let CLOSP1AUX_ANN_PAIR_ANT_TAC : tactic = fun (asl,w as gl) ->
  let pr = find_term (fun t -> is_var t && type_of t = `:clos_v list # clos_exp`) (lhand w) in
  (MP_TAC(ISPEC pr PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `args:clos_v list`
     (X_CHOOSE_THEN `exp:clos_exp` SUBST_ALL_TAC))) gl;;

let CLOSP1AUX_ann_call = prove
 (el 12 CLOSP1AUX_ann_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_ANN_UNFOLD_TAC THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN REWRITE_TAC[CLOSP1AUX_ann_HD_shift] THEN
   CLOSP1AUX_ANN_STEP_TAC CLOSP1AUX_ANN_DISCH_TAC THENL [ALL_TAC; CLOSP1AUX_ANN_END_TAC] THEN
   (fun (asl,w as gl) ->
      let fc = find_term (fun t -> is_comb t && CLOSPROPSAUX_is_app "clos_find_code" t &&
                                   length (snd (strip_comb t)) = 3) (lhand w) in
      (CASES_ON fc THEN CASE_REWRITE_TAC[] THENL [CLOSP1AUX_ANN_END_TAC; ALL_TAC]) gl) THEN
  CLOSP1AUX_ANN_PAIR_ANT_TAC THEN CASE_REWRITE_TAC[] THEN
   IMP_RES_TAC CLOSP1AUX_ann_find_code THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
   CASE_REWRITE_TAC[] THEN
   FIRST_ASSUM(fun th ->
     if CLOSPROPSAUX_is_app "clos_annotateProof_state_rel" (concl th)
     then REWRITE_TAC[GSYM (MATCH_MP clos_annotateProof_state_rel_clocks_eqs th)] else NO_TAC) THEN
  (COND_CASES_TAC THEN REWRITE_TAC[] THENL
       [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN CLOSP1AUX_ANN_FIN_TAC THEN
        MATCH_MP_TAC CLOSP1AUX_ann_state_rel_clock0 THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_ASSUM(fun th -> let c = concl th in
        if is_eq c && CLOSPROPSAUX_is_app "clos_annotate_shift" (lhs c) && is_cons (rhs c)
        then REWRITE_TAC[SYM th] else NO_TAC) THEN
      DISCH_TAC THEN CLOSP1AUX_ANN_COND_IH_TAC THEN
      FIRST_ASSUM(fun ih -> if CLOSP1AUX_ann_is_P ih then MATCH_MP_TAC ih else NO_TAC) THEN
      REWRITE_TAC[CLOSP1AUX_ann_dec_clock_code] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      TRY(MATCH_MP_TAC CLOSP1AUX_ann_state_rel_dec_clock THEN FIRST_ASSUM ACCEPT_TAC THEN
          NO_TAC) THEN
      TRY(ASM_ARITH_TAC THEN NO_TAC)) THENL
  [(* the environment of the body *)
   REWRITE_TAC[SUBSET; IN; CLOSP1AUX_ann_env_ok_def] THEN X_GEN_TAC `nn:num` THEN
    DISCH_TAC THEN ASM_CASES_TAC `nn < LENGTH (a:clos_v list)` THENL
     [DISJ2_TAC THEN DISJ1_TAC THEN
      FIRST_ASSUM(MP_TAC o REWRITE_RULE[LIST_REL_EL_EQN] o
                  check (CLOSPROPSAUX_is_app "ALL2" o concl)) THEN
      ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
      DISJ1_TAC THEN ASM_ARITH_TAC];
   (* the body has no free variables annotations *)
   REPEAT(FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[FEVERY_ALL_FLOOKUP] o
                          check (CLOSPROPSAUX_is_app "FEVERY" o concl))) THEN
    FIRST_ASSUM(fun th -> if is_eq (concl th) && CLOSPROPSAUX_is_app "FLOOKUP" (lhs (concl th))
                          then MP_TAC th else NO_TAC) THEN
    MESON_TAC[SND]]);;

(* local helpers: the variables of a related environment in range *)
let CLOSP1AUX_ann_env_ok_get_var = prove
 (`!m l i env env' k.
     env_ok m l i env env' k /\ k < m + l ==>
     clos_annotate_get_var (m:num) l i k < LENGTH env' /\
     clos_annotateProof_v_rel (EL k env) (EL (clos_annotate_get_var m l i k) env')`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CLOSP1AUX_ann_env_ok_def; clos_annotate_get_var_def; zlookup_def] THEN
  STRIP_TAC THENL
   [ASM_ARITH_TAC;
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(k < l)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]]);;

let CLOSP1AUX_ann_lookup_vars_live = prove
 (`!m l i env env' live.
     (!k. MEM k live ==> env_ok m l i env env' k) ==>
     ?x. lookup_vars (MAP (clos_annotate_get_var (m:num) l i) (FILTER (\n. n < m + l) live))
                     env' = SOME x`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[option_nchotomy] `~(y = NONE) ==> ?x:A. y = SOME x`) THEN
  REWRITE_TAC[lookup_vars_NONE; MEM_MAP; MEM_FILTER; NOT_EXISTS_THM] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(SPECL [`m:num`; `l:num`; `i:num spt`; `env:clos_v list`; `env':clos_v list`;
                `x:num`] CLOSP1AUX_ann_env_ok_get_var) THEN
  ASM_SIMP_TAC[] THEN ASM_ARITH_TAC);;

let CLOSP1AUX_ann_fn = prove
 (el 8 CLOSP1AUX_ann_cases,
  REPEAT GEN_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_ANN_UNFOLD_TAC THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN
   UNDISCH_TAC `every_Fn_vs_NONE [Fn x loc vsopt num_args exp]` THEN
   REWRITE_TAC[every_Fn_vs_NONE_def] THEN
   CASES_ON `vsopt:(num list)option` THEN REWRITE_TAC[IS_NONE_DEF] THEN DISCH_TAC THEN
   CASE_REWRITE_TAC[] THEN
   FIRST_ASSUM(fun th -> if CLOSPROPSAUX_is_app "clos_annotateProof_state_rel" (concl th)
     then REWRITE_TAC[GSYM (MATCH_MP clos_annotateProof_state_rel_max_app th)] else NO_TAC) THEN
   COND_CASES_TAC THEN REWRITE_TAC[] THENL [ALL_TAC; CLOSP1AUX_ANN_END_TAC] THEN
   REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `!k. MEM k (vars_to_list (db_vars_Shift num_args (SND (alt_free [exp])))) ==>
                     env_ok m l i env env' k` ASSUME_TAC THENL
    [REWRITE_TAC[MEM_vars_to_list; has_var_def] THEN REPEAT STRIP_TAC THEN
     FIRST_ASSUM(MATCH_MP_TAC o CONV_RULE(DEPTH_CONV BETA_CONV) o REWRITE_RULE[SUBSET; IN] o
                 check (CLOSPROPSAUX_is_app "SUBSET" o concl)) THEN
     ASM_REWRITE_TAC[alt_fv; alt_fv_def];
     ALL_TAC] THEN
   FIRST_ASSUM(X_CHOOSE_TAC `x:clos_v list` o MATCH_MP CLOSP1AUX_ann_lookup_vars_live) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CLOSP1AUX_ANN_FIN_TAC THEN
   MATCH_MP_TAC (el 5 (CONJUNCTS clos_annotateProof_v_rel_rules)) THEN
   EXISTS_TAC `m + l:num` THEN
   EXISTS_TAC `shifted_env 0 (FILTER (\n. n < m + l)
                (vars_to_list (db_vars_Shift num_args (SND (alt_free [exp])))))` THEN
   ASM_REWRITE_TAC[CLOSP1AUX_ann_HD_shift; ALL2] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC (INST [`env':clos_v list`,`env2:clos_v list`] env_ok_shifted_env) THEN
   ASM_REWRITE_TAC[ALL_DISTINCT_vars_to_list] THEN
   SUBGOAL_THEN `MEM (n - num_args) (vars_to_list (db_vars_Shift num_args (SND (alt_free [exp]))))`
     (fun th -> ASM_SIMP_TAC[th]) THEN
   ASM_SIMP_TAC[MEM_vars_to_list; has_var_def; SUB_ADD; GSYM alt_fv_def]);;

(* local helpers: the forcing body after alt_free and shift; the programs *)
(* installed come from the oracle                                         *)
let CLOSP1AUX_ann_shift_AppUnit = prove
 (`!t i. clos_annotate_shift (FST (alt_free [clos_AppUnit (clos_Var t 0)])) 0 1 i =
         [clos_AppUnit (clos_Var t 0)]`,
  REWRITE_TAC[clos_AppUnit_def; alt_free_def] THEN CASE_REWRITE_TAC[FST; HD] THEN
  REWRITE_TAC[CLOSP1AUX_ann_shift_thm; clos_annotate_shift_def; HD;
              clos_annotate_get_var_def; ARITH] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[HD]);;

let CLOSP1AUX_ann_do_install_es = prove
 (`!vs (s:(C,FFI)clos_state) es s'.
     clos_do_install vs s = (Rval es,s') ==>
     FST (SND (clos_state_compile_oracle s 0)) = es /\ ~(es = [])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_install_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_MESON_TAC[]);;

(* name a pair-valued term of the goal: (rK,sK) *)
let CLOSP1AUX_ANN_NAME_TERM_TAC (tm:term) (r:string) (s:string) : tactic = fun (asl,w as gl) ->
  let rty,sty = (match dest_type (type_of tm) with (_,[a;b]) -> a,b | _ -> failwith "NT") in
  let rv = mk_var(r, rty) and sv = mk_var(s, sty) in
  (MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN rv (X_CHOOSE_THEN sv ASSUME_TAC)) THEN
   POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)) gl;;

(* the installations of the source and of the target related (do_install_thm) *)
let CLOSP1AUX_ANN_INSTALL_TAC : tactic = fun (asl,w as gl) ->
  let di = find_term (fun t -> is_comb t && CLOSPROPSAUX_is_app "clos_do_install" t &&
                               length (snd (strip_comb t)) = 2) (lhand w) in
  let dt = find_term (fun t -> is_comb t && CLOSPROPSAUX_is_app "clos_do_install" t &&
                               length (snd (strip_comb t)) = 2) (rand w) in
  (CLOSP1AUX_ANN_NAME_TERM_TAC di "ir1" "is1" THEN CLOSP1AUX_ANN_NAME_TERM_TAC dt "ir2" "is2" THEN
   MP_TAC(SPECL [rand (rator di); rand di; rand (rator dt); rand dt;
                 mk_var("ir1",`:(clos_exp list,clos_v)result`);
                 mk_var("is1",`:(C,FFI)clos_state`);
                 mk_var("ir2",`:(clos_exp list,clos_v)result`);
                 mk_var("is2",`:(C,FFI)clos_state`)]
          (GENL [`xs:clos_v list`; `s1:(C,FFI)clos_state`; `ys:clos_v list`;
                 `t1:(C,FFI)clos_state`; `res1:(clos_exp list,clos_v)result`;
                 `s2:(C,FFI)clos_state`; `res2:(clos_exp list,clos_v)result`;
                 `t2:(C,FFI)clos_state`] do_install_thm)) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EVERY2_REVERSE THEN FIRST_ASSUM ACCEPT_TAC;
     STRIP_TAC]) gl;;

let CLOSP1AUX_ANN_INSTALL_DISCH_TAC : tactic =
  REWRITE_TAC[HD] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(REWRITE_TAC[LENGTH] THEN ARITH_TAC THEN NO_TAC) THEN
  TRY(REWRITE_TAC[SUBSET; IN; CLOSP1AUX_ann_env_ok_def] THEN ARITH_TAC THEN NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if is_eq (concl th) && CLOSPROPSAUX_is_app "clos_do_install" (lhs (concl th))
    then MP_TAC (MATCH_MP CLOSP1AUX_ann_do_install_es th) THEN
         DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN NO_TAC
    else NO_TAC);;

let CLOSP1AUX_ANN_APPUNIT_DISCH_TAC : tactic =
  REWRITE_TAC[HD] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(REWRITE_TAC[LENGTH] THEN ARITH_TAC THEN NO_TAC) THEN
  TRY(REWRITE_TAC[every_Fn_vs_NONE_def; clos_AppUnit_def] THEN NO_TAC) THEN
  REWRITE_TAC[SUBSET; IN; clos_AppUnit_def; alt_fv; alt_fv_nil] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[CLOSP1AUX_ann_env_ok_def; EL; HD; LENGTH; ARITH];;

let CLOSP1AUX_ANN_UT_TERMS (w:term) =
  let us = find_term (fun t -> is_comb t && CLOSPROPSAUX_is_app "clos_update_thunk" t &&
                               length (snd (strip_comb t)) = 3) (lhand w) in
  let ut = find_term (fun t -> is_comb t && CLOSPROPSAUX_is_app "clos_update_thunk" t &&
                               length (snd (strip_comb t)) = 3) (rand w) in
  us, ut;;

let CLOSP1AUX_ANN_UT1_TAC : tactic = fun (asl,w as gl) ->
  let us,ut = CLOSP1AUX_ANN_UT_TERMS w in
  let [xs; rs; vs] = snd (strip_comb us) and [ys; rt; ws] = snd (strip_comb ut) in
  (MP_TAC(ISPECL [`clos_annotateProof_v_rel`; xs; ys] CLOSPROPSAUX_vr_RefPtr_shape) THEN
   ASM_REWRITE_TAC[CLOSP1AUX_ann_simple_val_rel] THEN STRIP_TAC) gl;;

let CLOSP1AUX_ANN_UT2_TAC : tactic = fun (asl,w as gl) ->
  let us,ut = CLOSP1AUX_ANN_UT_TERMS w in
  let [xs; rs; vs] = snd (strip_comb us) and [ys; rt; ws] = snd (strip_comb ut) in
  let rel_th = REWRITE_RULE[IMP_CONJ] (GEN_ALL clos_annotateProof_rel_update_thunk) in
  (CASES_ON us THEN CASE_REWRITE_TAC[] THENL
    [CLOSP1AUX_ANN_END_TAC;
     FIRST_ASSUM(fun sr -> if CLOSPROPSAUX_is_app "clos_annotateProof_state_rel" (concl sr) &&
                              rand (concl sr) = rand rt then
       let th1 = MATCH_MP rel_th sr in
       FIRST_ASSUM(fun al -> if CLOSPROPSAUX_is_app "ALL2" (concl al) && lhand (concl al) = vs
         then let th2 = MATCH_MP th1 al in
              FIRST_ASSUM(fun ue -> if is_eq (concl ue) && lhs (concl ue) = us
                                    then MP_TAC (MATCH_MP th2 ue) else NO_TAC)
         else NO_TAC)
       else NO_TAC) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
     CLOSP1AUX_ANN_END_TAC]) gl;;

let CLOSP1AUX_ANN_DO_APP_TAC : tactic = fun (asl,w as gl) ->
  let ds = find_term (fun t -> is_comb t && CLOSPROPSAUX_is_app "clos_do_app" t &&
                               length (snd (strip_comb t)) = 3) (lhand w) in
  let dt = find_term (fun t -> is_comb t && CLOSPROPSAUX_is_app "clos_do_app" t &&
                               length (snd (strip_comb t)) = 3) (rand w) in
  let [opp; xs; s] = snd (strip_comb ds) and [_; ys; t] = snd (strip_comb dt) in
  (MP_TAC(INST [s,`s:(C,FFI)clos_state`; t,`t:(C,FFI)clos_state`; xs,`xs:clos_v list`;
                ys,`ys:clos_v list`; opp,`opp:clos_op`] clos_annotateProof_do_app_lemma) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EVERY2_REVERSE THEN FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC] THEN
   CASES_ON ds THEN CASE_REWRITE_TAC[] THENL
    [FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = ds then
        MP_TAC(ISPEC (rand (rhs (concl th))) PAIR_SURJECTIVE) else NO_TAC) THEN
     DISCH_THEN(X_CHOOSE_THEN `dv:clos_v` (X_CHOOSE_THEN `ds1:(C,FFI)clos_state`
       SUBST_ALL_TAC)) THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CLOSP1AUX_ANN_END_TAC;
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CLOSP1AUX_ANN_END_TAC]) gl;;

let CLOSP1AUX_ann_op = prove
 (el 7 CLOSP1AUX_ann_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_ANN_UNFOLD_TAC THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN REWRITE_TAC[CLOSP1AUX_ann_HD_shift] THEN
   CLOSP1AUX_ANN_STEP_TAC CLOSP1AUX_ANN_DISCH_TAC THENL [ALL_TAC; CLOSP1AUX_ANN_END_TAC] THEN
  (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THENL
  [(* Install *)
   CLOSP1AUX_ANN_INSTALL_TAC THEN
   (FIRST_ASSUM(fun th -> if is_eq (concl th) &&
                            CLOSPROPSAUX_is_app "clos_do_install" (lhs (concl th))
                                && is_var (fst (dest_pair (rhs (concl th)))) &&
                                name_of (fst (dest_pair (rhs (concl th)))) = "ir1"
         then MP_TAC (MATCH_MP (REWRITE_RULE[IMP_CONJ] CLOSP1AUX_ann_inv_mono)
                        (MATCH_MP CLOSPROPSAUX_do_install_code th)) else NO_TAC) THEN
       ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
       ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN STRIP_TAC THEN
       CASES_ON `ir1:(clos_exp list,clos_v)result` THEN
       FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOSPROPSAUX_is_app "result_rel" (concl th) &&
                                               rand (concl th) =
                                               `ir2:(clos_exp list,clos_v)result`)) THEN
       REWRITE_TAC[result_rel_Rval; result_rel_Rerr1] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
       STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[] THEN
       REWRITE_TAC[clos_annotate_annotate_def]) THENL
   [(CLOSP1AUX_ANN_STEP_TAC CLOSP1AUX_ANN_INSTALL_DISCH_TAC) THENL
     [(STRIP_TAC THEN RVEQ_TAC THEN CLOSP1AUX_ANN_FIN_TAC THEN
          MATCH_MP_TAC LIST_REL_LAST THEN ASM_REWRITE_TAC[] THEN
          REPEAT(FIRST_X_ASSUM(fun th ->
            if is_eq (concl th) && CLOSPROPSAUX_is_app "clos_do_install" (lhs (concl th))
            then MP_TAC (MATCH_MP CLOSP1AUX_ann_do_install_es th) else NO_TAC)) THEN
          REPEAT(FIRST_X_ASSUM(fun th ->
            if is_eq (concl th) && CLOSPROPSAUX_is_app "clos_evaluate" (lhs (concl th))
            then MP_TAC (MATCH_MP clos_evaluate_IMP_LENGTH th) else NO_TAC)) THEN
          REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN MESON_TAC[]);
      (CLOSP1AUX_ANN_END_TAC)];
    (FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOSPROPSAUX_is_app "exc_rel" (concl th))) THEN
        CASES_ON `a':(clos_v)error_result` THEN
        REWRITE_TAC[exc_rel_raise1; exc_rel_type_error1] THENL
         [FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
                                    CLOSPROPSAUX_is_app "clos_do_install" (lhs (concl th)) &&
                                    CLOSPROPSAUX_is_app "Rerr" (fst (dest_pair (rhs (concl th))))
                                  then MP_TAC (MATCH_MP do_install_not_Rraise th) else NO_TAC) THEN
          REWRITE_TAC[] THEN MESON_TAC[];
          STRIP_TAC THEN RVEQ_TAC THEN CLOSP1AUX_ANN_END_TAC])];
   (* not Install *)
   (COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ALL_TAC; ALL_TAC]) THENL
   [(* ThunkOp ForceThunk *)
    ((fun (asl,w as gl) ->
          let dt = find_term (fun t -> is_comb t && CLOSPROPSAUX_is_app "clos_dest_thunk" t &&
                                       length (snd (strip_comb t)) = 2) (rand w) in
          let ys = rand (rator dt) and t = rand (rand dt) in
          let ds = find_term (fun t -> is_comb t && CLOSPROPSAUX_is_app "clos_dest_thunk" t &&
                                       length (snd (strip_comb t)) = 2) (lhand w) in
          let xs = rand (rator ds) and s = rand (rand ds) in
          (MP_TAC(ISPECL [`clos_annotateProof_v_rel`;
                          `clos_annotateProof_state_rel:(C,FFI)clos_state->(C,FFI)clos_state->bool`;
                          s; t; xs; ys] CLOSPROPSAUX_dest_thunk_rel) THEN
           ASM_REWRITE_TAC[CLOSP1AUX_ann_simple_val_rel; CLOSP1AUX_ann_simple_state_rel] THEN
           CASES_ON dt THEN CASE_REWRITE_TAC[]) gl)) THENL
     [(DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN CLOSP1AUX_ANN_END_TAC);
      (DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN CLOSP1AUX_ANN_END_TAC);
      (DISCH_THEN(X_CHOOSE_THEN `thv:clos_v`
            (CONJUNCTS_THEN2 (fun th -> SUBST1_TAC th THEN ASSUME_TAC th) ASSUME_TAC)) THEN
          CASE_REWRITE_TAC[] THEN CASES_ON `a0:thunk_mode` THEN CASE_REWRITE_TAC[] THENL
           [CLOSP1AUX_ANN_END_TAC; ALL_TAC] THEN
          GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
            [GSYM (SPECL [`backend_common_None`; `LN:num spt`] CLOSP1AUX_ann_shift_AppUnit)] THEN
          CLOSP1AUX_ANN_STEP_TAC CLOSP1AUX_ANN_APPUNIT_DISCH_TAC THENL
           [ALL_TAC; CLOSP1AUX_ANN_END_TAC]) THEN
      (CLOSP1AUX_ANN_UT1_TAC) THENL
      [(RVEQ_TAC THEN CLOSP1AUX_ANN_UT2_TAC);
       (FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
                                     CLOSPROPSAUX_is_app "clos_dest_thunk" (lhs (concl th)) &&
                                     CLOSPROPSAUX_is_app "clos_IsThunk" (rhs (concl th)) &&
                                     is_var (lhand (lhs (concl th)))
                                   then MP_TAC th else NO_TAC) THEN
           ASM_SIMP_TAC[CLOSSEMAUX_dest_thunk_NotThunk; distinctness "clos_dest_thunk_ret"])]];
    (* other operations *)
    (CLOSP1AUX_ANN_DO_APP_TAC)]]);;

(* a local helper: the shifted alt_free of a Letrec, in closed form *)
let CLOSP1AUX_ann_shift_letrec = prove
 (`!nms loc vs fns x1 m l i.
     clos_annotate_shift (FST (alt_free [clos_Letrec nms loc vs fns x1])) m l i =
     [clos_Letrec nms loc
        (SOME (MAP (clos_annotate_get_var m l i)
                 (FILTER (\n. n < m + l)
                    (vars_to_list (list_mk_Union
                       (MAP (\p. db_vars_Shift (FST p + LENGTH fns) (SND (alt_free [SND p])))
                            fns))))))
        (MAP (\p. (FST p,
                   HD (clos_annotate_shift (FST (alt_free [SND p])) (m + l)
                         (FST p + LENGTH fns)
                         (shifted_env 0
                            (FILTER (\n. n < m + l)
                               (vars_to_list (list_mk_Union
                                  (MAP (\p. db_vars_Shift (FST p + LENGTH fns)
                                                          (SND (alt_free [SND p])))
                                       fns))))))))
             fns)
        (HD (clos_annotate_shift (FST (alt_free [x1])) m (l + LENGTH fns) i))]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[alt_free_def] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FST; SND; CLOSP1AUX_ann_shift_thm] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[pair_CASE_def] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[MAP_MAP_o; o_DEF; LENGTH_MAP; FST; SND; HD_FST_alt_free]);;

(* a local helper: ALL2 with a mapped right list *)
let CLOSP1AUX_ann_ALL2_MAP_R = prove
 (`!(R:A->B->bool) (h:A->B) l. ALL2 R l (MAP h l) <=> ALL (\x. R x (h x)) l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ALL2; ALL]);;

let CLOSP1AUX_ann_letrec = prove
 (el 9 CLOSP1AUX_ann_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   UNDISCH_TAC `every_Fn_vs_NONE [clos_Letrec x loc namesopt fns exp]` THEN
   REWRITE_TAC[every_Fn_vs_NONE_def] THEN
   CASES_ON `namesopt:(num list)option` THEN REWRITE_TAC[IS_NONE_DEF] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
                   CLOSPROPSAUX_is_app "clos_evaluate" (lhs (concl th)))) THEN
   REWRITE_TAC[CLOSP1AUX_ann_shift_letrec] THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN
   CASE_REWRITE_TAC[] THEN
   ABBREV_TAC `live = vars_to_list (list_mk_Union
                 (MAP (\p. db_vars_Shift (FST p + LENGTH fns) (SND (alt_free [SND p])))
                      (fns:(num#clos_exp)list)))` THEN
  ABBREV_TAC `funs2 = MAP (\p. (FST p,
                   HD (clos_annotate_shift (FST (alt_free [SND p])) (m + l)
                         (FST p + LENGTH fns) (shifted_env 0 (FILTER (\n. n < m + l) live)))))
                (fns:(num#clos_exp)list)` THEN
   SUBGOAL_THEN `LENGTH (funs2:(num#clos_exp)list) = LENGTH (fns:(num#clos_exp)list)`
     ASSUME_TAC THENL
    [EXPAND_TAC "funs2" THEN REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
   COND_CASES_TAC THENL [ALL_TAC; CLOSP1AUX_ANN_END_TAC] THEN
   SUBGOAL_THEN (CASE_TERM `ALL (\p. match p with (num_args,e) ->
                        num_args <= clos_state_max_app (t1:(C,FFI)clos_state) /\ ~(num_args = 0))
                     (funs2:(num#clos_exp)list)`) ASSUME_TAC THENL
    [EXPAND_TAC "funs2" THEN
     FIRST_ASSUM(fun th -> if CLOSPROPSAUX_is_app "clos_annotateProof_state_rel" (concl th)
       then REWRITE_TAC[GSYM (MATCH_MP clos_annotateProof_state_rel_max_app th)] else NO_TAC) THEN
     UNDISCH_TAC (CASE_TERM `ALL (\p. match p with (num_args,e) ->
                        num_args <= clos_state_max_app (s:(C,FFI)clos_state) /\ ~(num_args = 0))
                     (fns:(num#clos_exp)list)`) THEN
     REWRITE_TAC[ALL_MAP; o_DEF; pair_CASE_def] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC[FST];
     ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `!k. MEM k live ==> alt_fv k [clos_Letrec x loc NONE fns exp]` ASSUME_TAC THENL
    [EXPAND_TAC "live" THEN
     REWRITE_TAC[MEM_vars_to_list; has_var_list_mk_Union; EX_MAP; o_DEF; has_var_def; alt_fv;
                 pair_CASE_def; alt_fv_def] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ADD_ASSOC] THEN MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `!k. MEM k live ==> env_ok m l i env env' k` ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN
     FIRST_ASSUM(MATCH_MP_TAC o CONV_RULE(DEPTH_CONV BETA_CONV) o REWRITE_RULE[SUBSET; IN] o
                 check (CLOSPROPSAUX_is_app "SUBSET" o concl)) THEN
     ASM_SIMP_TAC[];
     ALL_TAC] THEN
   FIRST_ASSUM(X_CHOOSE_TAC `env2:clos_v list` o MATCH_MP CLOSP1AUX_ann_lookup_vars_live) THEN
   ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[CLOSP1AUX_ann_HD_shift] THEN
  (DISCH_TAC THEN CLOSP1AUX_ANN_COND_IH_TAC THEN
      FIRST_ASSUM(fun ih -> if CLOSP1AUX_ann_is_P ih then MATCH_MP_TAC ih else NO_TAC) THEN
      EXISTS_TAC `list_of_seq (clos_Recclosure loc [] env fns)
                    (LENGTH (fns:(num#clos_exp)list))` THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      TRY(REWRITE_TAC[LENGTH_APPEND; LENGTH_LIST_OF_SEQ] THEN ASM_ARITH_TAC THEN NO_TAC) THEN
      REWRITE_TAC[SUBSET; IN] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC env_ok_EXTEND THEN REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN CONJ_TAC THENL
       [ALL_TAC;
        DISCH_TAC THEN
        FIRST_ASSUM(MATCH_MP_TAC o CONV_RULE(DEPTH_CONV BETA_CONV) o REWRITE_RULE[SUBSET; IN] o
                    check (CLOSPROPSAUX_is_app "SUBSET" o concl)) THEN
        ASM_SIMP_TAC[alt_fv; SUB_ADD]]) THEN
  REWRITE_TAC[LIST_REL_GENLIST] THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC (el 6 (CONJUNCTS clos_annotateProof_v_rel_rules)) THEN
   ASM_REWRITE_TAC[ALL2] THEN EXPAND_TAC "funs2" THEN
   REWRITE_TAC[CLOSP1AUX_ann_ALL2_MAP_R; GSYM ALL_MEM; FORALL_PAIR_THM] THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN
   MAP_EVERY X_GEN_TAC [`n:num`; `e:clos_exp`] THEN DISCH_TAC THEN
   CASE_REWRITE_TAC[] THEN
   EXISTS_TAC `m + l:num` THEN EXISTS_TAC `shifted_env 0 (FILTER (\n. n < m + l) live)` THEN
  (SUBGOAL_THEN `LENGTH (fns:(num#clos_exp)list) + n = n + LENGTH fns` SUBST1_TAC THENL
       [ARITH_TAC; REWRITE_TAC[CLOSP1AUX_ann_HD_shift]] THEN
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN
        MATCH_MP_TAC (INST [`env':clos_v list`,`env2:clos_v list`;
                            `env2:clos_v list`,`x:clos_v list`]
                        env_ok_shifted_env) THEN
        ALL_TAC;
        ALL_TAC]) THENL
  [(* the environment of the body of a function *)
   SUBGOAL_THEN `MEM (n' - (n + LENGTH (fns:(num#clos_exp)list))) live` ASSUME_TAC THENL
     [EXPAND_TAC "live" THEN
      REWRITE_TAC[MEM_vars_to_list; has_var_list_mk_Union; EX_MAP; o_DEF; has_var_def;
                  GSYM EX_MEM] THEN
      CONV_TAC(DEPTH_CONV BETA_CONV) THEN EXISTS_TAC `(n:num,e:clos_exp)` THEN
      ASM_SIMP_TAC[FST; SND; SUB_ADD; GSYM alt_fv_def];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "live" THEN REWRITE_TAC[ALL_DISTINCT_vars_to_list];
   (* the body of a function has no annotations *)
   FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
      `every_Fn_vs_NONE (MAP SND (fns:(num#clos_exp)list))`)) THEN
    ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] THEN
    REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `(n:num,e:clos_exp)`) THEN ASM_REWRITE_TAC[SND] THEN
    REWRITE_TAC[ALL] THEN
   REWRITE_TAC[MEM] THEN MESON_TAC[]]);;

let CLOSP1AUX_ANN_LENS_TAC : tactic = fun (asl,w as gl) ->
  let ths = mapfilter (fun (_,th) -> MATCH_MP LIST_REL_LENGTH th) asl in
  let ths = filter (fun th -> not (lhs (concl th) = rhs (concl th))) ths in
  (MAP_EVERY (fun th -> SUBST_ALL_TAC (SYM th) ORELSE ALL_TAC) ths) gl;;

let CLOSP1AUX_ANN_DC_SPLIT_TAC =
  CONJ_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[injectivity "option"; injectivity "app_kind"; distinctness "app_kind"] THEN
  STRIP_TAC THEN RVEQ_TAC;;

let CLOSP1AUX_ann_dest_closure = prove
 (`!max_app loc_opt f f' args args'.
     clos_annotateProof_v_rel f f' /\ ALL2 clos_annotateProof_v_rel args args' ==>
     (!v. dest_closure max_app loc_opt f args = SOME (Partial_app v) ==>
          ?v'. dest_closure max_app loc_opt f' args' = SOME (Partial_app v') /\
               clos_annotateProof_v_rel v v') /\
     (!exp env rest. dest_closure max_app loc_opt f args = SOME (Full_app exp env rest) ==>
          ?m l i exp' env' rest'.
            dest_closure max_app loc_opt f' args' = SOME (Full_app exp' env' rest') /\
            clos_annotate_shift (FST (alt_free [exp])) m l i = [exp'] /\
            LENGTH env = m + l /\
            (\n. alt_fv n [exp]) SUBSET env_ok m l i env env' /\
            every_Fn_vs_NONE [exp] /\
            ALL2 clos_annotateProof_v_rel rest rest')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  UNDISCH_TAC `clos_annotateProof_v_rel f f'` THEN
  CASES_ON `f:clos_v` THEN REWRITE_TAC[clos_annotateProof_v_rel_simp] THEN STRIP_TAC THEN
  RVEQ_TAC THEN REWRITE_TAC[dest_closure_def] THEN
  CASE_REWRITE_TAC[distinctness "option"] THENL
   [(* Closure *)
    CLOSP1AUX_ANN_LENS_TAC THEN CLOSP1AUX_ANN_DC_SPLIT_TAC THENL
     [REWRITE_TAC[clos_annotateProof_v_rel_simp; injectivity "clos_v"; UNWIND_THM1] THEN
      EXISTS_TAC `i:num spt` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EVERY2_APPEND_suff THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`LENGTH (a2:clos_v list)`; `a3:num`; `i:num spt`] THEN
      REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `LENGTH (APPEND (REVERSE (TAKE (a3 - LENGTH (a1:clos_v list))
                        (REVERSE (args:clos_v list)))) a1) = a3` ASSUME_TAC THENL
       [REWRITE_TAC[LENGTH_APPEND; LENGTH_REVERSE] THEN
        SUBGOAL_THEN `a3 - LENGTH (a1:clos_v list) <= LENGTH (REVERSE (args:clos_v list))`
          (fun th -> SIMP_TAC[th; LENGTH_TAKE]) THENL
         [REWRITE_TAC[LENGTH_REVERSE] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
        REWRITE_TAC[SUBSET; IN] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC CLOSP1AUX_ann_env_ok_some THEN EXISTS_TAC `0` THEN
        ASM_REWRITE_TAC[ADD_CLAUSES] THEN CONJ_TAC THENL
         [MATCH_MP_TAC EVERY2_APPEND_suff THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC EVERY2_REVERSE THEN MATCH_MP_TAC EVERY2_TAKE THEN
          MATCH_MP_TAC EVERY2_REVERSE THEN ASM_REWRITE_TAC[];
          ASM_SIMP_TAC[]];
        MATCH_MP_TAC EVERY2_REVERSE THEN MATCH_MP_TAC EVERY2_DROP THEN
        MATCH_MP_TAC EVERY2_REVERSE THEN ASM_REWRITE_TAC[]]];
    (* Recclosure *)
    FIRST_ASSUM(fun th -> if CLOSPROPSAUX_is_app "ALL2" (concl th) &&
                             is_abs (rand (rator (rator (concl th))))
      then MP_TAC (REWRITE_RULE[LIST_REL_EL_EQN] th) else NO_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `a4:num`)) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[pair_CASE_def] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `ii:num spt` STRIP_ASSUME_TAC) THEN
    CLOSP1AUX_ANN_LENS_TAC THEN
    ASM_REWRITE_TAC[pair_CASE_def] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC(DEPTH_CONV let_CONV) THEN CLOSP1AUX_ANN_DC_SPLIT_TAC THENL
     [REWRITE_TAC[clos_annotateProof_v_rel_simp; injectivity "clos_v"; UNWIND_THM1] THEN
      REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EVERY2_APPEND_suff THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`LENGTH (a2:clos_v list)`;
        `LENGTH (a3:(num#clos_exp)list) + FST (EL a4 (a3:(num#clos_exp)list))`;
        `ii:num spt`] THEN
      REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `LENGTH (APPEND (REVERSE (TAKE (FST (EL a4 (a3:(num#clos_exp)list)) -
                      LENGTH (a1:clos_v list)) (REVERSE (args:clos_v list)))) a1) =
                    FST (EL a4 a3)` ASSUME_TAC THENL
       [REWRITE_TAC[LENGTH_APPEND; LENGTH_REVERSE] THEN
        SUBGOAL_THEN `FST (EL a4 (a3:(num#clos_exp)list)) - LENGTH (a1:clos_v list) <=
                      LENGTH (REVERSE (args:clos_v list))`
          (fun th -> SIMP_TAC[th; LENGTH_TAKE]) THENL
         [REWRITE_TAC[LENGTH_REVERSE] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [POP_ASSUM MP_TAC THEN REWRITE_TAC[LENGTH_APPEND; LENGTH_LIST_OF_SEQ] THEN ARITH_TAC;
        REWRITE_TAC[SUBSET; IN] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
        X_GEN_TAC `n:num` THEN DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
        MATCH_MP_TAC CLOSP1AUX_ann_env_ok_some THEN
        EXISTS_TAC `LENGTH (a3:(num#clos_exp)list)` THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          MATCH_MP_TAC EVERY2_APPEND_suff THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC EVERY2_REVERSE THEN MATCH_MP_TAC EVERY2_TAKE THEN
          MATCH_MP_TAC EVERY2_REVERSE THEN ASM_REWRITE_TAC[];
          DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC CLOSP1AUX_ann_env_ok_some THEN EXISTS_TAC `0` THEN
          REWRITE_TAC[ADD_CLAUSES; LENGTH_LIST_OF_SEQ; LIST_REL_GENLIST] THEN CONJ_TAC THENL
           [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
            REWRITE_TAC[clos_annotateProof_v_rel_simp; injectivity "clos_v"; UNWIND_THM1] THEN
            REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
            ASM_REWRITE_TAC[ALL2];
            DISCH_TAC THEN
            SUBGOAL_THEN `n - FST (EL a4 (a3:(num#clos_exp)list)) - LENGTH a3 =
                          n - (FST (EL a4 a3) + LENGTH a3)` SUBST1_TAC THENL
             [ARITH_TAC;
              FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]];
        MATCH_MP_TAC EVERY2_REVERSE THEN MATCH_MP_TAC EVERY2_DROP THEN
        MATCH_MP_TAC EVERY2_REVERSE THEN ASM_REWRITE_TAC[]]]]);;

(* local tactics of the application case: split a named result; apply the *)
(* induction hypothesis of the remaining application                        *)
let CLOSP1AUX_ANN_SPLIT_ON_TAC (r:term) : tactic = fun g ->
  (CLOSP1AUX_ann_last := r; CLOSP1AUX_ANN_SPLIT_TAC g);;

let CLOSP1AUX_ANN_APP_IH1_TAC : tactic = fun (asl,w as gl) ->
  let ev = lhand w in
  let x = el 1 (snd (strip_comb (lhs ev))) in
  (DISCH_TAC THEN
   REMOVE_THEN "ih1" (MP_TAC o SPECL [`a0:clos_exp`; `a1:clos_v list`; x; `a2:clos_v list`;
                                     `q1:(C,FFI)clos_state`]) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]) gl;;

let CLOSP1AUX_ann_app_cons = prove
 (el 14 CLOSP1AUX_ann_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[LIST_REL_CONS1] o
    check (fun th -> CLOSPROPSAUX_is_app "ALL2" (concl th) && is_cons (lhand (concl th)))) THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP clos_annotateProof_state_rel_max_app) THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP clos_annotateProof_state_rel_clocks_eqs) THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP LIST_REL_LENGTH o
    check (fun th -> CLOSPROPSAUX_is_app "ALL2" (concl th) && is_cons (lhand (concl th)))) THEN
  MP_TAC(SPECL [`clos_state_max_app (s:(C,FFI)clos_state)`; `loc_opt:num option`;
                `f:clos_v`; `f':clos_v`; `CONS (v4:clos_v) v5`; `CONS (h':clos_v) t'`]
               CLOSP1AUX_ann_dest_closure) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `evaluate_app loc_opt f (CONS v4 v5) (s:(C,FFI)clos_state) = res,s2` THEN
  SIMP_TAC[evaluate_app_rw; NOT_CONS_NIL] THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `dest_closure (clos_state_max_app (s:(C,FFI)clos_state)) loc_opt f (CONS v4 v5)` THEN
  CASE_REWRITE_TAC[] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
    ALL_TAC] THEN
  CASES_ON `a:app_kind` THEN
  CASE_REWRITE_TAC[injectivity "option"; injectivity "app_kind"; distinctness "app_kind"] THENL
   [(* Partial_app *)
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[] o SPEC `a':clos_v` o
      check (fun th -> try let v,b = dest_forall (concl th) in
                           type_of v = `:clos_v` && is_imp b with Failure _ -> false)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    CLOSP1AUX_ANN_FIN_TAC THEN
    TRY(MATCH_MP_TAC CLOSP1AUX_ann_state_rel_clock0 THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(MATCH_MP_TAC CLOSP1AUX_ann_state_rel_dec_clock THEN ASM_REWRITE_TAC[] THEN NO_TAC);
    ALL_TAC] THEN
  (* Full_app *)
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[] o
    SPECL [`a0:clos_exp`; `a1:clos_v list`; `a2:clos_v list`] o
    check (fun th -> let vs,b = strip_forall (concl th) in
                     length vs = 3 && is_imp b && is_exists (rand b))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP LIST_REL_LENGTH o
    check (fun th -> CLOSPROPSAUX_is_app "ALL2" (concl th) &&
                     lhand (concl th) = `a2:clos_v list`)) THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN CLOSP1AUX_ANN_FIN_TAC THEN
    MATCH_MP_TAC CLOSP1AUX_ann_state_rel_clock0 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPEC `clos_evaluate ([a0:clos_exp],a1,clos_dec_clock (LENGTH (CONS (v4:clos_v) v5) -
                  LENGTH (a2:clos_v list)) (s:(C,FFI)clos_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `q1:(C,FFI)clos_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r1:(clos_v list,clos_v)result = Rerr (Rabort Rtype_error)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "ih2" (MP_TAC o SPECL [`a0:clos_exp`; `a1:clos_v list`; `a2:clos_v list`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`env':clos_v list`;
    `clos_dec_clock (LENGTH (CONS (v4:clos_v) v5) - LENGTH (a2:clos_v list))
                    (s1':(C,FFI)clos_state)`;
    `r1:(clos_v list,clos_v)result`; `q1:(C,FFI)clos_state`; `m:num`; `l:num`;
    `i:num spt`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CLOSP1AUX_ann_dec_clock_code] THEN
    MATCH_MP_TAC CLOSP1AUX_ann_state_rel_dec_clock THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun eq -> if is_eq (concl eq) &&
                           CLOSPROPSAUX_is_app "clos_annotate_shift" (lhs (concl eq))
                        then REWRITE_TAC[eq] else NO_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `q2:(C,FFI)clos_state` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun ev -> if is_eq (concl ev) && is_pair (rhs (concl ev)) &&
                           fst (dest_pair (rhs (concl ev))) = `r1:(clos_v list,clos_v)result`
    then MP_TAC (REWRITE_RULE[CLOSP1AUX_ann_dec_clock_code]
                   (MATCH_MP (CONJUNCT1 CLOSPROPSAUX_evaluate_code_lemma) ev))
    else NO_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CLOSP1AUX_ann_inv_mono)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CLOSP1AUX_ANN_SPLIT_ON_TAC `r1:(clos_v list,clos_v)result` THENL
   [CLOSP1AUX_ANN_SING_TAC THEN CASE_REWRITE_TAC[] THEN CLOSP1AUX_ANN_APP_IH1_TAC;
    CLOSP1AUX_ANN_END_TAC]);;

(* HOL4: shift_correct [local] *)
let shift_correct = prove
 (`(!xs env (s1:(C,FFI)clos_state) env' t1 res s2 m l i.
      clos_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) /\
      LENGTH env = m + l /\
      (\n. alt_fv n xs) SUBSET env_ok m l i env env' /\
      every_Fn_vs_NONE xs /\
      FEVERY (\p. every_Fn_vs_NONE [SND (SND p)]) (clos_state_code s1) /\
      (!n. every_Fn_vs_NONE (FST (SND (clos_state_compile_oracle s1 n))) /\
           every_Fn_vs_NONE (MAP (SND o SND) (SND (SND (clos_state_compile_oracle s1 n))))) /\
      clos_annotateProof_state_rel s1 t1 ==>
      ?res' t2.
        clos_evaluate (clos_annotate_shift (FST (alt_free xs)) m l i,env',t1) = (res',t2) /\
        result_rel (ALL2 clos_annotateProof_v_rel) clos_annotateProof_v_rel res res' /\
        clos_annotateProof_state_rel s2 t2) /\
   (!loc_opt f args (s1:(C,FFI)clos_state) res s2 f' args' s1'.
      evaluate_app loc_opt f args s1 = (res,s2) /\
      clos_annotateProof_v_rel f f' /\ ALL2 clos_annotateProof_v_rel args args' /\
      FEVERY (\p. every_Fn_vs_NONE [SND (SND p)]) (clos_state_code s1) /\
      (!n. every_Fn_vs_NONE (FST (SND (clos_state_compile_oracle s1 n))) /\
           every_Fn_vs_NONE (MAP (SND o SND) (SND (SND (clos_state_compile_oracle s1 n))))) /\
      clos_annotateProof_state_rel s1 s1' /\ ~(res = Rerr (Rabort Rtype_error)) ==>
      ?res' s2'.
        evaluate_app loc_opt f' args' s1' = (res',s2') /\
        result_rel (ALL2 clos_annotateProof_v_rel) clos_annotateProof_v_rel res res' /\
        clos_annotateProof_state_rel s2 s2')`,
  MATCH_ACCEPT_TAC
    (MP CLOSP1AUX_ann_ind
        (end_itlist CONJ
           [CLOSP1AUX_ann_nil; CLOSP1AUX_ann_cons; CLOSP1AUX_ann_var; CLOSP1AUX_ann_if;
            CLOSP1AUX_ann_let; CLOSP1AUX_ann_raise; CLOSP1AUX_ann_handle; CLOSP1AUX_ann_op;
            CLOSP1AUX_ann_fn; CLOSP1AUX_ann_letrec; CLOSP1AUX_ann_app; CLOSP1AUX_ann_tick;
            CLOSP1AUX_ann_call; CLOSP1AUX_ann_app_nil; CLOSP1AUX_ann_app_cons])));;

(* HOL4: env_set_default [local] *)
let env_set_default = prove
 (`!x env'. x SUBSET env_ok 0 0 LN [] env'`,
  REWRITE_TAC[SUBSET; IN] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (el 7 (CONJUNCTS clos_annotateProof_v_rel_rules)) THEN ARITH_TAC);;

(* HOL4: annotate_correct *)
let annotate_correct =
  REWRITE_RULE [GSYM clos_annotate_annotate_def; env_set_default; LENGTH; ADD_0]
    (INST [`0`,`m:num`; `0`,`l:num`; `LN:num spt`,`i:num spt`;
           `[]:clos_v list`,`env:clos_v list`]
       (SPEC_ALL (CONJUNCT1 shift_correct)));;

(* ------------------------------------------------------------------------- *)
(* syntactic properties                                                      *)
(* ------------------------------------------------------------------------- *)

(* HOL4: every_Fn_vs_SOME_shift [simp] *)
let every_Fn_vs_SOME_shift = prove
 (`!a b c d. every_Fn_vs_SOME (clos_annotate_shift a b c d)`,
  MATCH_MP_TAC clos_annotate_shift_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN
  REWRITE_TAC[clos_annotate_shift_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[every_Fn_vs_SOME_def; every_Fn_vs_SOME_APPEND; HD_shift; IS_SOME_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[every_Fn_vs_SOME_EVERY] THEN
  REWRITE_TAC[MAP_MAP_o; ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[SND; HD_shift] THEN ASM_SIMP_TAC[]);;
let _ = cake_add_simps [every_Fn_vs_SOME_shift];;

(* HOL4: every_Fn_vs_SOME_annotate [simp] *)
let every_Fn_vs_SOME_annotate = prove
 (`!n es. every_Fn_vs_SOME (clos_annotate_annotate n es)`,
  REWRITE_TAC[clos_annotate_annotate_def; every_Fn_vs_SOME_shift]);;
let _ = cake_add_simps [every_Fn_vs_SOME_annotate];;

(* HOL4: every_Fn_SOME_shift [simp] *)
let every_Fn_SOME_shift = prove
 (`!a b c d. every_Fn_SOME (clos_annotate_shift a b c d) <=> every_Fn_SOME a`,
  MATCH_MP_TAC clos_annotate_shift_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN
  REWRITE_TAC[clos_annotate_shift_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[every_Fn_SOME_def; every_Fn_SOME_APPEND; HD_shift; IS_SOME_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[every_Fn_SOME_EVERY] THEN
  REWRITE_TAC[MAP_MAP_o; ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[SND; HD_shift] THEN ASM_SIMP_TAC[]);;
let _ = cake_add_simps [every_Fn_SOME_shift];;

(* HOL4: every_Fn_SOME_const_0 [simp] *)
let every_Fn_SOME_const_0 = prove
 (`!t. every_Fn_SOME [const_0 t]`,
  REWRITE_TAC[const_0_def; every_Fn_SOME_def]);;
let _ = cake_add_simps [every_Fn_SOME_const_0];;

(* local helpers for the inductions on alt_free: a pair equation is the   *)
(* equations of its projections; the induction with the pair equations of *)
(* the hypotheses eliminated and the goal in projections                    *)
let CLOSP1AUX_ann_pair_split = prove
 (`!(p:A#B) a b. p = (a,b) <=> FST p = a /\ SND p = b`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ]);;

let CLOSP1AUX_ANN_AF_IND_TAC : tactic =
  MATCH_MP_TAC alt_free_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY (DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CLOSP1AUX_ann_pair_split; IMP_CONJ; RIGHT_FORALL_IMP_THM;
                              FORALL_UNWIND_THM1]) THEN
  REWRITE_TAC[alt_free_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE_def] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FST; SND];;

let CLOSP1AUX_ann_every_Fn_SOME_REPLICATE = prove
 (`!n t. every_Fn_SOME (REPLICATE n (const_0 t))`,
  ONCE_REWRITE_TAC[every_Fn_SOME_EVERY] THEN
  REWRITE_TAC[EVERY_REPLICATE; every_Fn_SOME_const_0]);;

(* HOL4: every_Fn_SOME_alt_free *)
let every_Fn_SOME_alt_free = prove
 (`!es. every_Fn_SOME es ==> every_Fn_SOME (FST (alt_free es))`,
  CLOSP1AUX_ANN_AF_IND_TAC THEN
  REWRITE_TAC[every_Fn_SOME_def; every_Fn_SOME_APPEND; HD_FST_alt_free] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THENL
   [COND_CASES_TAC THEN
    REWRITE_TAC[FST; every_Fn_SOME_def; HD_FST_alt_free;
                CLOSP1AUX_ann_every_Fn_SOME_REPLICATE] THEN
    ASM_MESON_TAC[];
    UNDISCH_TAC `every_Fn_SOME (MAP SND (fns:(num#clos_exp)list))` THEN
    ONCE_REWRITE_TAC[every_Fn_SOME_EVERY] THEN
    REWRITE_TAC[MAP_MAP_o; ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND; HD_FST_alt_free] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[]]);;

(* HOL4: every_Fn_SOME_annotate *)
let every_Fn_SOME_annotate = prove
 (`!n es. every_Fn_SOME es ==> every_Fn_SOME (clos_annotate_annotate n es)`,
  SIMP_TAC[clos_annotate_annotate_def; every_Fn_SOME_shift; every_Fn_SOME_alt_free]);;

(* HOL4: shift_code_locs [local] *)
let shift_code_locs = prove
 (`!xs env s1 env'. code_locs (clos_annotate_shift xs env s1 env') = code_locs xs`,
  MATCH_MP_TAC clos_annotate_shift_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN
  REWRITE_TAC[clos_annotate_shift_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[code_locs_def; code_locs_append; HD_shift; LENGTH_MAP] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[MAP_MAP_o] THEN ONCE_REWRITE_TAC[code_locs_map] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[SND; HD_shift] THEN ASM_SIMP_TAC[]);;

(* HOL4: code_locs_const_0 [simp] *)
let code_locs_const_0 = prove
 (`!t. code_locs [const_0 t] = []`,
  REWRITE_TAC[const_0_def; code_locs_def]);;
let _ = cake_add_simps [code_locs_const_0];;

(* local helpers: the locations of a list of copies of const_0; a list     *)
(* whose elements are among those of a second list and which is distinct   *)
(* when the second one is, preserved by APPEND and FLAT                     *)
let CLOSP1AUX_ann_code_locs_REP = prove
 (`!n t. code_locs (REPLICATE n (const_0 t)) = []`,
  INDUCT_TAC THEN REWRITE_TAC[REPLICATE; code_locs_def] THEN
  ONCE_REWRITE_TAC[code_locs_cons] THEN ASM_REWRITE_TAC[code_locs_const_0; APPEND]);;

let CLOSP1AUX_ann_sub_APPEND = prove
 (`!(a:A list) b c d.
     (set_of_list b SUBSET set_of_list a /\ (ALL_DISTINCT a ==> ALL_DISTINCT b)) /\
     (set_of_list d SUBSET set_of_list c /\ (ALL_DISTINCT c ==> ALL_DISTINCT d)) ==>
     set_of_list (APPEND b d) SUBSET set_of_list (APPEND a c) /\
     (ALL_DISTINCT (APPEND a c) ==> ALL_DISTINCT (APPEND b d))`,
  REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_APPEND; ALL_DISTINCT_APPEND] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]]);;

let CLOSP1AUX_ann_sub_refl = prove
 (`!(a:A list). set_of_list a SUBSET set_of_list a /\ (ALL_DISTINCT a ==> ALL_DISTINCT a)`,
  REWRITE_TAC[SUBSET_REFL]);;

let CLOSP1AUX_ann_sub_FLAT = prove
 (`!(f:B->A list) g l.
     (!x. MEM x l ==> set_of_list (g x) SUBSET set_of_list (f x) /\
                      (ALL_DISTINCT (f x) ==> ALL_DISTINCT (g x))) ==>
     set_of_list (FLAT (MAP g l)) SUBSET set_of_list (FLAT (MAP f l)) /\
     (ALL_DISTINCT (FLAT (MAP f l)) ==> ALL_DISTINCT (FLAT (MAP g l)))`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; FLAT; MEM; set_of_list; SUBSET_REFL; ALL_DISTINCT] THEN
  DISCH_TAC THEN MATCH_MP_TAC CLOSP1AUX_ann_sub_APPEND THEN ASM_MESON_TAC[]);;

(* a local tactic: the locations of an expression and of its alt_free form, *)
(* by the structure of the two lists                                        *)
let rec CLOSP1AUX_ANN_SUB_TAC g =
  (FIRST [MATCH_ACCEPT_TAC CLOSP1AUX_ann_sub_refl;
          FIRST_ASSUM MATCH_ACCEPT_TAC;
          CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
          REWRITE_TAC[set_of_list; EMPTY_SUBSET; ALL_DISTINCT] THEN NO_TAC;
          MATCH_MP_TAC CLOSP1AUX_ann_sub_APPEND THEN CONJ_TAC THEN CLOSP1AUX_ANN_SUB_TAC;
          MATCH_MP_TAC CLOSP1AUX_ann_sub_FLAT THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
          ASM_MESON_TAC[]]) g;;

(* a local helper: alt_free_code_locs and alt_free_code_locs_distinct in    *)
(* one induction                                                            *)
let CLOSP1AUX_ann_alt_free_code_locs = prove
 (`!xs. set_of_list (code_locs (FST (alt_free xs))) SUBSET set_of_list (code_locs xs) /\
        (ALL_DISTINCT (code_locs xs) ==> ALL_DISTINCT (code_locs (FST (alt_free xs))))`,
  CLOSP1AUX_ANN_AF_IND_TAC THEN
  REWRITE_TAC[code_locs_def; HD_FST_alt_free; LENGTH_MAP] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[code_locs_append; HD_FST_alt_free; MAP_MAP_o; o_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND; code_locs_map; HD_FST_alt_free] THEN
  TRY(REWRITE_TAC[SUBSET_REFL; ALL_DISTINCT] THEN NO_TAC) THEN
  TRY(CLOSP1AUX_ANN_SUB_TAC THEN NO_TAC) THEN
  COND_CASES_TAC THEN REWRITE_TAC[FST; code_locs_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CLOSP1AUX_ann_code_locs_REP; HD_FST_alt_free] THEN
  MATCH_MP_TAC CLOSP1AUX_ann_sub_APPEND THEN
  (CONJ_TAC THENL [ALL_TAC; CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]) THENL
   [REWRITE_TAC[set_of_list; EMPTY_SUBSET; ALL_DISTINCT];
    ASM_MESON_TAC[]]);;

(* HOL4: alt_free_code_locs [local] *)
let alt_free_code_locs = prove
 (`!xs. set_of_list (code_locs (FST (alt_free xs))) SUBSET set_of_list (code_locs xs)`,
  REWRITE_TAC[CLOSP1AUX_ann_alt_free_code_locs]);;

(* HOL4: alt_free_code_locs_distinct [local] *)
let alt_free_code_locs_distinct = prove
 (`!xs. ALL_DISTINCT (code_locs xs) ==> ALL_DISTINCT (code_locs (FST (alt_free xs)))`,
  REWRITE_TAC[CLOSP1AUX_ann_alt_free_code_locs]);;

(* HOL4: annotate_code_locs *)
let annotate_code_locs = prove
 (`!n ls. set_of_list (code_locs (clos_annotate_annotate n ls)) SUBSET
          set_of_list (code_locs ls) /\
          (ALL_DISTINCT (code_locs ls) ==>
           ALL_DISTINCT (code_locs (clos_annotate_annotate n ls)))`,
  REWRITE_TAC[clos_annotate_annotate_def; shift_code_locs; alt_free_code_locs;
              alt_free_code_locs_distinct]);;

(* HOL4: EVERY_shift_sing *)
let EVERY_shift_sing = prove
 (`!(f:clos_exp->bool) y x1 x2 x3.
     ALL f (clos_annotate_shift [y] x1 x2 x3) <=> f (HD (clos_annotate_shift [y] x1 x2 x3))`,
  REPEAT GEN_TAC THEN
  X_CHOOSE_THEN `z:clos_exp` SUBST1_TAC
    (SPECL [`y:clos_exp`; `x1:num`; `x2:num`; `x3:num spt`] shift_SING) THEN
  REWRITE_TAC[ALL; HD]);;

(* a local tactic: shift preserves a property of all subexpressions *)
let CLOSP1AUX_ANN_SHIFT_ALL_TAC (defs:thm list) : tactic =
  MATCH_MP_TAC clos_annotate_shift_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY (DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; EVERY_shift_sing]) THEN
  REWRITE_TAC[clos_annotate_shift_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC(ALL :: ALL_APPEND :: EVERY_shift_sing :: shift_LENGTH_LEMMA :: defs) THEN
  REPEAT STRIP_TAC THEN TRY(ASM_MESON_TAC[] THEN NO_TAC) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSPROPSAUX_is_app "ALL" o concl))) THEN
  REWRITE_TAC[MAP_MAP_o; ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[SND] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[];;

(* HOL4: shift_obeys_max_app *)
let shift_obeys_max_app = prove
 (`!xs m l i. ALL (obeys_max_app n) xs ==>
              ALL (obeys_max_app n) (clos_annotate_shift xs m l i)`,
  CLOSP1AUX_ANN_SHIFT_ALL_TAC [obeys_max_app_def]);;

(* local helpers: the property of the singleton alt_free form; a local      *)
(* tactic: alt_free preserves a property of all subexpressions               *)
let CLOSP1AUX_ann_ALL_alt_free_sing = prove
 (`!(f:clos_exp->bool) x. ALL f (FST (alt_free [x])) <=> f (HD (FST (alt_free [x])))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM HD_FST_alt_free] THEN REWRITE_TAC[ALL; HD]);;

let CLOSP1AUX_ANN_AF_ALL_TAC (defs:thm list) : tactic =
  CLOSP1AUX_ANN_AF_IND_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; CLOSP1AUX_ann_ALL_alt_free_sing]) THEN
  REWRITE_TAC(ALL :: ALL_APPEND :: CLOSP1AUX_ann_ALL_alt_free_sing :: LENGTH_FST_alt_free ::
              defs) THEN
  REPEAT STRIP_TAC THEN TRY(ASM_MESON_TAC[] THEN NO_TAC) THEN
  TRY(COND_CASES_TAC THEN
      REWRITE_TAC(FST :: ALL :: EVERY_REPLICATE :: const_0_def ::
                  CLOSP1AUX_ann_ALL_alt_free_sing :: defs) THEN
      ASM_MESON_TAC[] THEN NO_TAC) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSPROPSAUX_is_app "ALL" o concl))) THEN
  REWRITE_TAC[MAP_MAP_o; ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[];;

(* HOL4: alt_free_obeys_max_app *)
let alt_free_obeys_max_app = prove
 (`!xs (m:num) (l:num) (i:num spt).
     ALL (obeys_max_app n) xs ==> ALL (obeys_max_app n) (FST (alt_free xs))`,
  SUBGOAL_THEN `!xs. ALL (obeys_max_app n) xs ==> ALL (obeys_max_app n) (FST (alt_free xs))`
    (fun th -> REWRITE_TAC[th]) THEN
  CLOSP1AUX_ANN_AF_ALL_TAC [obeys_max_app_def]);;

(* HOL4: annotate_obeys_max_app *)
let annotate_obeys_max_app = prove
 (`!n xs. ALL (obeys_max_app m) xs ==>
          ALL (obeys_max_app m) (clos_annotate_annotate n xs)`,
  SIMP_TAC[clos_annotate_annotate_def; shift_obeys_max_app; alt_free_obeys_max_app]);;

(* HOL4: shift_no_Labels *)
let shift_no_Labels = prove
 (`!xs m l i. ALL no_Labels xs ==> ALL no_Labels (clos_annotate_shift xs m l i)`,
  CLOSP1AUX_ANN_SHIFT_ALL_TAC [no_Labels_def]);;

(* HOL4: alt_free_no_Labels *)
let alt_free_no_Labels = prove
 (`!xs (m:num) (l:num) (i:num spt).
     ALL no_Labels xs ==> ALL no_Labels (FST (alt_free xs))`,
  SUBGOAL_THEN `!xs. ALL no_Labels xs ==> ALL no_Labels (FST (alt_free xs))`
    (fun th -> REWRITE_TAC[th]) THEN
  CLOSP1AUX_ANN_AF_ALL_TAC [no_Labels_def; distinctness "clos_op"]);;

(* HOL4: annotate_no_Labels *)
let annotate_no_Labels = prove
 (`!n xs. ALL no_Labels xs ==> ALL no_Labels (clos_annotate_annotate n xs)`,
  SIMP_TAC[clos_annotate_annotate_def; shift_no_Labels; alt_free_no_Labels]);;

(* HOL4: code_locs_REP_const_0 *)
let code_locs_REP_const_0 = prove
 (`!n t. code_locs (REPLICATE n (const_0 t)) = []`,
  REWRITE_TAC[CLOSP1AUX_ann_code_locs_REP]);;

(* HOL4: code_locs_alt_free *)
let code_locs_alt_free = prove
 (`!xs r1 r2. alt_free xs = (r1,r2) ==>
              set_of_list (code_locs r1) SUBSET set_of_list (code_locs xs)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `xs:clos_exp list` alt_free_code_locs) THEN
  ASM_REWRITE_TAC[FST]);;

(* HOL4: code_locs_shift *)
let code_locs_shift = prove
 (`!xs k1 k2 k3. code_locs (clos_annotate_shift xs k1 k2 k3) = code_locs xs`,
  REWRITE_TAC[shift_code_locs]);;

(* HOL4: code_locs_annotate *)
let code_locs_annotate = prove
 (`!n xs. set_of_list (code_locs (clos_annotate_annotate n xs)) SUBSET
          set_of_list (code_locs xs)`,
  REWRITE_TAC[clos_annotate_annotate_def; code_locs_shift; alt_free_code_locs]);;

(* semantics preservation *)

(* a local helper: the initial states are related *)
let CLOSP1AUX_ann_initial_state_rel = prove
 (`!(ffi:(FFI)ffi_state) max_app prog (co:num->C#clos_prog)
     (cc:C->clos_prog->(byte list#int64 list#C)option) k.
     clos_annotateProof_state_rel
       (clos_initial_state ffi max_app (alist_to_fmap prog) co
          (pure_cc clos_annotate_compile_inc cc) k)
       (clos_initial_state ffi max_app (alist_to_fmap (clos_annotate_compile prog))
          (pure_co clos_annotate_compile_inc o co) cc k)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_annotateProof_state_rel_def; clos_initial_state_def;
              clos_state_INFO.ri_accessors; ALL2; FLOOKUP_EMPTY; distinctness "option";
              FDOM_alist_to_fmap; clos_annotateProof_MAP_FST_compile] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; pure_co_def] THEN GEN_TAC THEN
    SPEC_TAC(`(co:num->C#clos_prog) x`,`p:C#clos_prog`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM; clos_annotate_compile_inc_def; I_THM];
    REWRITE_TAC[FUN_EQ_THM; pure_cc_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[clos_annotate_compile_inc_def];
    REWRITE_TAC[ALOOKUP_EQ_FLOOKUP; ALOOKUP_compile; o_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
    REWRITE_TAC[UNWIND_THM1; clos_annotate_annotate_def] THEN
    ONCE_REWRITE_TAC[GSYM HD_FST_alt_free] THEN REWRITE_TAC[HD_shift] THEN
    EXISTS_TAC `HD (clos_annotate_shift [HD (FST (alt_free [c:clos_exp]))] 0 arity LN)` THEN
    REWRITE_TAC[HD_shift]]);;

(* HOL4: semantics_annotate *)
let semantics_annotate = prove
 (`~(clos_semantics (ffi:(FFI)ffi_state) max_app (alist_to_fmap prog) (co:num->C#clos_prog)
       (pure_cc clos_annotate_compile_inc
                (cc:C->clos_prog->(byte list#int64 list#C)option)) xs = Fail) ==>
   every_Fn_vs_NONE xs /\
   every_Fn_vs_NONE (MAP (SND o SND) prog) /\
   (!n. every_Fn_vs_NONE (FST (SND (co n))) /\
        every_Fn_vs_NONE (MAP (SND o SND) (SND (SND (co n))))) ==>
   clos_semantics ffi max_app (alist_to_fmap (clos_annotate_compile prog))
     (pure_co clos_annotate_compile_inc o co) cc (clos_annotate_annotate 0 xs) =
   clos_semantics ffi max_app (alist_to_fmap prog) co
     (pure_cc clos_annotate_compile_inc cc) xs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ffi:(FFI)ffi_state`; `max_app:num`;
                 `alist_to_fmap prog:(num,num#clos_exp)fmap`; `co:num->C#clos_prog`;
                 `(pure_cc clos_annotate_compile_inc
                    (cc:C->clos_prog->(byte list#int64 list#C)option)):
                  C->clos_prog->(byte list#int64 list#C)option`;
                 `xs:clos_exp list`;
                 `alist_to_fmap (clos_annotate_compile prog):(num,num#clos_exp)fmap`;
                 `(pure_co clos_annotate_compile_inc o (co:num->C#clos_prog)):
                  num->C#clos_prog`;
                 `cc:C->clos_prog->(byte list#int64 list#C)option`;
                 `clos_annotate_annotate 0 xs`;
                 `\(c1:(num,num#clos_exp)fmap) (o1:num->C#clos_prog)
                   (k1:C->clos_prog->(byte list#int64 list#C)option)
                   (e1:clos_exp list) (c2:(num,num#clos_exp)fmap) (o2:num->C#clos_prog)
                   (k2:C->clos_prog->(byte list#int64 list#C)option) (e2:clos_exp list). T`]
                clos_IMP_semantics_eq) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[clos_eval_sim_def] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES] THEN
  MP_TAC(INST [`[]:clos_v list`,`env':clos_v list`;
               `clos_initial_state (ffi:(FFI)ffi_state) max_app (alist_to_fmap prog)
                  (co:num->C#clos_prog)
                  (pure_cc clos_annotate_compile_inc
                     (cc:C->clos_prog->(byte list#int64 list#C)option)) k`,
               `s1:(C,FFI)clos_state`;
               `res1:(clos_v list,clos_v)result`,`res:(clos_v list,clos_v)result`;
               `clos_initial_state (ffi:(FFI)ffi_state) max_app
                  (alist_to_fmap (clos_annotate_compile prog))
                  (pure_co clos_annotate_compile_inc o (co:num->C#clos_prog))
                  (cc:C->clos_prog->(byte list#int64 list#C)option) k`,
               `t1:(C,FFI)clos_state`] annotate_correct) THEN
  ASM_REWRITE_TAC[CLOSP1AUX_ann_initial_state_rel] THEN
  REWRITE_TAC[clos_initial_state_def; clos_state_INFO.ri_accessors] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FEVERY_alist_to_fmap THEN
    UNDISCH_TAC `every_Fn_vs_NONE (MAP (SND o SND) (prog:(num#num#clos_exp)list))` THEN
    GEN_REWRITE_TAC LAND_CONV [every_Fn_vs_NONE_EVERY] THEN
    REWRITE_TAC[ALL_MAP; o_DEF];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM clos_initial_state_def] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`res':(clos_v list,clos_v)result`; `t2:(C,FFI)clos_state`] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[clos_annotateProof_state_rel_def] o
    check (CLOSPROPSAUX_is_app "clos_annotateProof_state_rel" o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSPROPSAUX_is_app "result_rel" o concl)) THEN
  CASES_ON `res1:(clos_v list,clos_v)result` THEN
  CASES_ON `res':(clos_v list,clos_v)result` THEN
  REWRITE_TAC[result_rel_def] THEN
  TRY(CASES_ON `a:(clos_v)error_result` THEN CASES_ON `a':(clos_v)error_result`) THEN
  REWRITE_TAC[exc_rel_def]);;

(* more syntactic properties *)

(* HOL4: call_dests_shift [simp] *)
let call_dests_shift = prove
 (`!a b c d. app_call_dests opt (clos_annotate_shift a b c d) = app_call_dests opt a`,
  MATCH_MP_TAC clos_annotate_shift_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN
  REWRITE_TAC[clos_annotate_shift_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[app_call_dests_def; app_call_dests_append; HD_shift] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[MAP_MAP_o] THEN ONCE_REWRITE_TAC[app_call_dests_map] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[SND; HD_shift] THEN ASM_SIMP_TAC[]);;
let _ = cake_add_simps [call_dests_shift];;

(* a local helper: a property of all expressions of a singleton annotate *)
let CLOSP1AUX_ann_annotate_sing_ALL = prove
 (`!(f:clos_exp->bool) n e.
     ALL f (clos_annotate_annotate n [e]) <=> f (HD (clos_annotate_annotate n [e]))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_annotate_annotate_def] THEN
  ONCE_REWRITE_TAC[GSYM HD_FST_alt_free] THEN REWRITE_TAC[EVERY_shift_sing]);;

(* HOL4: no_Labels_ann *)
let no_Labels_ann = prove
 (`!xs. ALL no_Labels (MAP (SND o SND) xs) ==>
        ALL no_Labels (MAP (SND o SND) (clos_annotate_compile xs))`,
  REWRITE_TAC[clos_annotate_compile_def] THEN REWRITE_TAC[MAP_MAP_o] THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[SND] THEN
  MESON_TAC[REWRITE_RULE[ALL; CLOSP1AUX_ann_annotate_sing_ALL]
              (SPECL [`n:num`; `[e:clos_exp]`] annotate_no_Labels)]);;

(* HOL4: obeys_max_app_ann *)
let obeys_max_app_ann = prove
 (`!xs. ALL (obeys_max_app m) (MAP (SND o SND) xs) ==>
        ALL (obeys_max_app m) (MAP (SND o SND) (clos_annotate_compile xs))`,
  REWRITE_TAC[clos_annotate_compile_def] THEN REWRITE_TAC[MAP_MAP_o] THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[SND] THEN
  MESON_TAC[REWRITE_RULE[ALL; CLOSP1AUX_ann_annotate_sing_ALL]
              (SPECL [`n:num`; `[e:clos_exp]`] annotate_obeys_max_app)]);;

(* HOL4: HD_annotate_SING *)
let HD_annotate_SING = prove
 (`!x y. [HD (clos_annotate_annotate x [y])] = clos_annotate_annotate x [y]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_annotate_annotate_def] THEN
  ONCE_REWRITE_TAC[GSYM HD_FST_alt_free] THEN REWRITE_TAC[HD_shift]);;

(* HOL4: every_Fn_SOME_ann *)
let every_Fn_SOME_ann = prove
 (`!xs. every_Fn_SOME (MAP (SND o SND) xs) ==>
        every_Fn_SOME (MAP (SND o SND) (clos_annotate_compile xs))`,
  ONCE_REWRITE_TAC[every_Fn_SOME_EVERY] THEN
  REWRITE_TAC[clos_annotate_compile_def] THEN REWRITE_TAC[MAP_MAP_o] THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[SND; HD_annotate_SING] THEN MESON_TAC[every_Fn_SOME_annotate]);;
