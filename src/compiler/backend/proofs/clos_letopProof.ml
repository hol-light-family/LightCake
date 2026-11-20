(* ========================================================================= *)
(* clos_letopProof: port of HOL4 compiler/backend/proofs/                    *)
(* clos_letopProofScript.sml (CakeML v3479).                                 *)
(* Correctness proof for clos_letop.                                         *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/clos_letop.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/closLang.ml";;

type_invention_error := true;;

(* CLOSP2AUX_ names are local helpers. *)

(* HOL4: let_op_SING *)
let let_op_SING = prove
 (`!x. ?y. clos_letop_let_op [x] = [y]`,
  MESON_TAC[clos_letop_let_op_sing_eq]);;

(* HOL4: HD_let_op_SING [simp] *)
let HD_let_op_SING = prove
 (`!x. [HD (clos_letop_let_op [x])] = clos_letop_let_op [x] /\
       LENGTH (clos_letop_let_op [x]) = 1`,
  GEN_TAC THEN REWRITE_TAC[CONJUNCT1 clos_letop_let_op_sing_eq; HD; LENGTH; ONE]);;
let _ = cake_add_simps [HD_let_op_SING];;

(* HOL4: code_rel_def *)
let clos_letopProof_code_rel_def = cake_def
  `clos_letopProof_code_rel e1 e2 <=> e2 = clos_letop_let_op e1`;;

(* HOL4: code_rel_IMP_LENGTH *)
let clos_letopProof_code_rel_IMP_LENGTH = prove
 (`!xs ys. clos_letopProof_code_rel xs ys ==> LENGTH xs = LENGTH ys`,
  SIMP_TAC[clos_letopProof_code_rel_def; clos_letop_LENGTH_let_op]);;

(* HOL4: code_rel_CONS_CONS *)
let clos_letopProof_code_rel_CONS_CONS = prove
 (`clos_letopProof_code_rel (CONS x1 (CONS x2 xs)) (CONS y1 (CONS y2 ys)) ==>
   clos_letopProof_code_rel [x1] [y1] /\
   clos_letopProof_code_rel (CONS x2 xs) (CONS y2 ys)`,
  REWRITE_TAC[clos_letopProof_code_rel_def; clos_letop_let_op_def; CONS_11] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[HD_let_op_SING]);;

(* value relation *)

(* HOL4: f_rel_def *)
let clos_letopProof_f_rel_def = cake_def
  `clos_letopProof_f_rel (a1:num,e1:clos_exp) (a2:num,e2:clos_exp) <=>
     a1 = a2 /\ clos_letopProof_code_rel [e1] [e2]`;;

(* HOL4: v_rel (funs1 and funs2 of the last rule, free in HOL4, are bound) *)
let clos_letopProof_v_rel_rules,clos_letopProof_v_rel_ind,
    clos_letopProof_v_rel_cases,clos_letopProof_v_rel_strongind =
  cake_inductive
  `(!i. clos_letopProof_v_rel (clos_Number i) (clos_Number i)) /\
   (!w. clos_letopProof_v_rel (clos_Word64 w) (clos_Word64 w)) /\
   (!w. clos_letopProof_v_rel (ByteVector w) (ByteVector w)) /\
   (!n b. clos_letopProof_v_rel (clos_RefPtr b n) (clos_RefPtr b n)) /\
   (!tag xs ys.
      ALL2 clos_letopProof_v_rel xs ys ==>
      clos_letopProof_v_rel (clos_Block tag xs) (clos_Block tag ys)) /\
   (!loc args1 args2 env1 env2 num_args e1 e2.
      ALL2 clos_letopProof_v_rel env1 env2 /\
      ALL2 clos_letopProof_v_rel args1 args2 /\
      clos_letopProof_code_rel [e1] [e2] ==>
      clos_letopProof_v_rel (clos_Closure loc args1 env1 num_args e1)
                            (clos_Closure loc args2 env2 num_args e2)) /\
   (!loc args1 args2 env1 env2 funs1 funs2 k.
      ALL2 clos_letopProof_v_rel env1 env2 /\
      ALL2 clos_letopProof_v_rel args1 args2 /\
      ALL2 clos_letopProof_f_rel funs1 funs2 ==>
      clos_letopProof_v_rel (clos_Recclosure loc args1 env1 funs1 k)
                            (clos_Recclosure loc args2 env2 funs2 k))`;;

(* HOL4: v_rel_simps [simp] (HOL4 computes it with SIMP_CONV from v_rel_cases) *)
let clos_letopProof_v_rel_simps = prove
 (`(!n x. clos_letopProof_v_rel (clos_Number n) x <=> x = clos_Number n) /\
   (!n p x. clos_letopProof_v_rel (clos_Block n p) x <=>
            ?ys. x = clos_Block n ys /\ ALL2 clos_letopProof_v_rel p ys) /\
   (!p x. clos_letopProof_v_rel (clos_Word64 p) x <=> x = clos_Word64 p) /\
   (!p x. clos_letopProof_v_rel (ByteVector p) x <=> x = ByteVector p) /\
   (!b p x. clos_letopProof_v_rel (clos_RefPtr b p) x <=> x = clos_RefPtr b p) /\
   (!x1 x2 x3 x4 x5 x.
      clos_letopProof_v_rel (clos_Closure x1 x2 x3 x4 x5) x <=>
      ?args2 env2 e2.
        x = clos_Closure x1 args2 env2 x4 e2 /\
        ALL2 clos_letopProof_v_rel x3 env2 /\ ALL2 clos_letopProof_v_rel x2 args2 /\
        clos_letopProof_code_rel [x5] [e2]) /\
   (!y1 y2 y3 y4 y5 x.
      clos_letopProof_v_rel (clos_Recclosure y1 y2 y3 y4 y5) x <=>
      ?args2 env2 funs2.
        x = clos_Recclosure y1 args2 env2 funs2 y5 /\
        ALL2 clos_letopProof_v_rel y3 env2 /\ ALL2 clos_letopProof_v_rel y2 args2 /\
        ALL2 clos_letopProof_f_rel y4 funs2) /\
   (!b x. clos_letopProof_v_rel (clos_Boolv b) x <=> x = clos_Boolv b) /\
   (!x. clos_letopProof_v_rel clos_Unit x <=> x = clos_Unit)`,
  REWRITE_TAC[clos_Boolv_def; clos_Unit_def] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_letopProof_v_rel_cases] THEN
  REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"; GSYM CONJ_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[LIST_REL_NIL] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[] THEN MESON_TAC[]);;
let _ = cake_add_simps [clos_letopProof_v_rel_simps];;

(* a local helper: v_rel with the right value known *)
let CLOSP2AUX_letop_v_rel_right = prove
 (`(!x n. clos_letopProof_v_rel x (clos_Number n) <=> x = clos_Number n) /\
   (!x n p. clos_letopProof_v_rel x (clos_Block n p) <=>
            ?xs. x = clos_Block n xs /\ ALL2 clos_letopProof_v_rel xs p) /\
   (!x p. clos_letopProof_v_rel x (clos_Word64 p) <=> x = clos_Word64 p) /\
   (!x p. clos_letopProof_v_rel x (ByteVector p) <=> x = ByteVector p) /\
   (!x b p. clos_letopProof_v_rel x (clos_RefPtr b p) <=> x = clos_RefPtr b p) /\
   (!x x1 x2 x3 x4 x5.
      clos_letopProof_v_rel x (clos_Closure x1 x2 x3 x4 x5) <=>
      ?args1 env1 e1.
        x = clos_Closure x1 args1 env1 x4 e1 /\
        ALL2 clos_letopProof_v_rel env1 x3 /\ ALL2 clos_letopProof_v_rel args1 x2 /\
        clos_letopProof_code_rel [e1] [x5]) /\
   (!x y1 y2 y3 y4 y5.
      clos_letopProof_v_rel x (clos_Recclosure y1 y2 y3 y4 y5) <=>
      ?args1 env1 funs1.
        x = clos_Recclosure y1 args1 env1 funs1 y5 /\
        ALL2 clos_letopProof_v_rel env1 y3 /\ ALL2 clos_letopProof_v_rel args1 y2 /\
        ALL2 clos_letopProof_f_rel funs1 y4)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_letopProof_v_rel_cases] THEN
  REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"; GSYM CONJ_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[LIST_REL_NIL] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[] THEN MESON_TAC[]);;

(* state relation *)

(* HOL4: ref_rel *)
let clos_letopProof_ref_rel_rules,clos_letopProof_ref_rel_ind,
    clos_letopProof_ref_rel_cases,clos_letopProof_ref_rel_strongind =
  cake_inductive
  `(!bs. clos_letopProof_ref_rel (clos_ByteArray bs) (clos_ByteArray bs)) /\
   (!xs ys.
      ALL2 clos_letopProof_v_rel xs ys ==>
      clos_letopProof_ref_rel (clos_ValueArray xs) (clos_ValueArray ys)) /\
   (!m v w.
      clos_letopProof_v_rel v w ==>
      clos_letopProof_ref_rel (clos_Thunk m v) (clos_Thunk m w))`;;

(* HOL4: FMAP_REL_def *)
let clos_letopProof_FMAP_REL_def = cake_def
  `clos_letopProof_FMAP_REL (r:A->B->bool) (f1:(K,A)fmap) (f2:(K,B)fmap) <=>
     FDOM f1 = FDOM f2 /\
     !k v. FLOOKUP f1 k = SOME v ==> ?v2. FLOOKUP f2 k = SOME v2 /\ r v v2`;;

(* HOL4: state_rel_def *)
let clos_letopProof_state_rel_def = cake_def
  `clos_letopProof_state_rel (s:(C,FFI)clos_state) (t:(C,FFI)clos_state) <=>
     (!n. SND (SND (clos_state_compile_oracle s n)) = []) /\
     clos_state_code s = FEMPTY /\ clos_state_code t = FEMPTY /\
     clos_state_max_app t = clos_state_max_app s /\ 1 <= clos_state_max_app s /\
     clos_state_clock t = clos_state_clock s /\
     clos_state_ffi t = clos_state_ffi s /\
     ALL2 (OPTREL clos_letopProof_v_rel) (clos_state_globals s) (clos_state_globals t) /\
     clos_letopProof_FMAP_REL clos_letopProof_ref_rel
       (clos_state_refs s) (clos_state_refs t) /\
     clos_state_compile s = pure_cc clos_letop_compile_inc (clos_state_compile t) /\
     clos_state_compile_oracle t =
       pure_co clos_letop_compile_inc o clos_state_compile_oracle s`;;

(* a local helper: v_rel is a simple value relation (HOL4 proves it inline  *)
(* in do_app_lemma with simple_val_rel_def and v_rel_cases)                 *)
let CLOSP2AUX_letop_simple_val_rel = prove
 (`clos_simple_val_rel clos_letopProof_v_rel`,
  REWRITE_TAC[clos_simple_val_rel_def; CLOSP2AUX_letop_v_rel_right] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[clos_isClos_def]);;

(* HOL4: v_rel_IMP_v_to_bytes_lemma [local] *)
let clos_letopProof_v_rel_IMP_v_to_bytes_lemma = prove
 (`!x y.
     clos_letopProof_v_rel x y ==>
     !ns:byte list.
       clos_v_to_list x = SOME (MAP (clos_Number o int_of_num o val) ns) <=>
       clos_v_to_list y = SOME (MAP (clos_Number o int_of_num o val) ns)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_ASSOC] THEN ONCE_REWRITE_TAC[MAP_o] THEN
  MP_TAC(MATCH_MP v_rel_to_list_byte1 CLOSP2AUX_letop_simple_val_rel) THEN
  DISCH_THEN(MP_TAC o SPECL [`y:clos_v`; `x:clos_v`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* HOL4: v_rel_IMP_v_to_bytes [local] *)
let clos_letopProof_v_rel_IMP_v_to_bytes = prove
 (`clos_letopProof_v_rel x y ==> clos_v_to_bytes y = clos_v_to_bytes x`,
  MESON_TAC[clos_simple_val_rel_v_to_bytes; CLOSP2AUX_letop_simple_val_rel]);;

(* HOL4: v_rel_IMP_v_to_words_lemma [local] *)
let clos_letopProof_v_rel_IMP_v_to_words_lemma = prove
 (`!x y.
     clos_letopProof_v_rel x y ==>
     !ns. clos_v_to_list x = SOME (MAP clos_Word64 ns) <=>
          clos_v_to_list y = SOME (MAP clos_Word64 ns)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `clos_v_to_list y` (cases "option")) THEN STRIP_TAC THENL
   [MP_TAC(SPECL [`x:clos_v`; `y:clos_v`; `clos_letopProof_v_rel`] vr_list_NONE) THEN
    ASM_REWRITE_TAC[CLOSP2AUX_letop_simple_val_rel] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[distinctness "option"];
    MP_TAC(MATCH_MP CLOSPROPSAUX_v_to_list_SOME CLOSP2AUX_letop_simple_val_rel) THEN
    DISCH_THEN(MP_TAC o SPECL [`y:clos_v`; `a:clos_v list`; `x:clos_v`]) THEN
    ASM_REWRITE_TAC[injectivity "option"] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[injectivity "option"] THEN
    MP_TAC(MATCH_MP val_rel_to_words_lemma CLOSP2AUX_letop_simple_val_rel) THEN
    DISCH_THEN(MP_TAC o SPECL [`xs:clos_v list`; `a:clos_v list`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* HOL4: v_rel_IMP_v_to_words [local] *)
let clos_letopProof_v_rel_IMP_v_to_words = prove
 (`clos_letopProof_v_rel x y ==> clos_v_to_words y = clos_v_to_words x`,
  MESON_TAC[clos_simple_val_rel_v_to_words; CLOSP2AUX_letop_simple_val_rel]);;

(* HOL4: dest_op_SOME_IMP *)
let dest_op_SOME_IMP = prove
 (`!x (args:A list) opp. clos_letop_dest_op x args = SOME opp ==>
     ?t xs. x = clos_Op t opp xs /\ clos_letop_var_list 0 xs args`,
  GEN_TAC THEN CASES_ON `x:clos_exp` THEN
  REWRITE_TAC[clos_letop_dest_op_def; distinctness "option"] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; injectivity "clos_exp"] THEN
  ASM_MESON_TAC[]);;

(* HOL4: var_list_IMP_LENGTH *)
let var_list_IMP_LENGTH = prove
 (`!n xs (ys:A list). clos_letop_var_list n xs ys ==> LENGTH xs = LENGTH ys`,
  MATCH_MP_TAC clos_letop_var_list_ind THEN
  REWRITE_TAC[clos_letop_var_list_def; LENGTH] THEN MESON_TAC[]);;

(* HOL4: var_list_IMP_evaluate [local] (the first of HOL4's two theorems of *)
(* this name; the second, below, rebinds it)                                *)
let CLOSP2AUX_letop_var_list_IMP_evaluate = prove
 (`!a2 a1 xs (ys:clos_exp list) (s:(C,FFI)clos_state) env.
     clos_letop_var_list (LENGTH a1) xs ys /\ LENGTH ys = LENGTH a2 ==>
     clos_evaluate (xs,APPEND (APPEND a1 a2) env,s) = (Rval a2,s)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP var_list_IMP_LENGTH) THEN
    ASM_REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[clos_evaluate_def];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ys:clos_exp list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; ARITH_RULE `~(0 = SUC n)`; SUC_INJ] THEN
  STRUCT_CASES_TAC(ISPEC `xs:clos_exp list` list_CASES) THEN
  REWRITE_TAC[clos_letop_var_list_def] THEN
  CASES_ON `h'':clos_exp` THEN REWRITE_TAC[clos_letop_var_list_def] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN
  REWRITE_TAC[clos_evaluate_def] THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH;
                  ARITH_RULE `!a b. a < a + SUC b`] THEN
  REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[HD; ARITH_RULE `!a b c. a < (a + SUC b) + c`] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`APPEND a1 [h:clos_v]`; `t'':clos_exp list`;
                                `t':clos_exp list`; `s:(C,FFI)clos_state`;
                                `env:clos_v list`]) THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ONE; ADD_CLAUSES; GSYM APPEND_ASSOC; APPEND] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ADD1]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[HD]);;

(* HOL4: var_list_IMP_evaluate [local] *)
let var_list_IMP_evaluate = prove
 (`!vs xs (ys:clos_exp list) (s:(C,FFI)clos_state) env.
     clos_letop_var_list 0 xs ys /\ LENGTH ys = LENGTH vs ==>
     clos_evaluate (xs,APPEND vs env,s) = (Rval vs,s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`vs:clos_v list`; `[]:clos_v list`; `xs:clos_exp list`;
                 `ys:clos_exp list`; `s:(C,FFI)clos_state`; `env:clos_v list`]
                CLOSP2AUX_letop_var_list_IMP_evaluate) THEN
  ASM_REWRITE_TAC[LENGTH; APPEND]);;

(* HOL4: lookup_vars_lemma *)
let clos_letopProof_lookup_vars_lemma = prove
 (CASE_TERM
  `!vs env1 env2.
     ALL2 clos_letopProof_v_rel env1 env2 ==>
     match lookup_vars vs env1 with
       NONE -> lookup_vars vs env2 = NONE
     | SOME l1 -> ?l2. ALL2 clos_letopProof_v_rel l1 l2 /\ lookup_vars vs env2 = SOME l2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[lookup_vars_def; case_def "option"] THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `[]:clos_v list` THEN REWRITE_TAC[ALL2]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`env1:clos_v list`; `env2:clos_v list`]) THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[case_def "option"] THEN
  CASES_ON `lookup_vars (t:num list) (env1:clos_v list)` THEN
  REWRITE_TAC[case_def "option"] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[case_def "option"; injectivity "option"; UNWIND_THM1; ALL2] THEN
  EXISTS_TAC `CONS (EL h env2) (l2:clos_v list)` THEN ASM_REWRITE_TAC[ALL2] THEN
  UNDISCH_TAC `ALL2 clos_letopProof_v_rel env1 env2` THEN
  REWRITE_TAC[LIST_REL_EL_EQN] THEN ASM_MESON_TAC[]);;

(* HOL4: find_code_lemma *)
let clos_letopProof_find_code_lemma = prove
 (`!s t p args.
     clos_letopProof_state_rel (s:(C,FFI)clos_state) t ==>
     clos_find_code p (args:clos_v list) (clos_state_code s) = NONE /\
     clos_find_code p args (clos_state_code t) = NONE`,
  SIMP_TAC[clos_letopProof_state_rel_def; clos_find_code_def; FLOOKUP_EMPTY] THEN
  REWRITE_TAC[case_def "option"]);;

(* HOL4: dest_closure_SOME_IMP *)
let clos_letopProof_dest_closure_SOME_IMP = prove
 (`dest_closure max_app loc_opt f2 xs = SOME x ==>
   (?loc arg_env clo_env num_args e. f2 = clos_Closure loc arg_env clo_env num_args e) \/
   (?loc arg_env clo_env fns i. f2 = clos_Recclosure loc arg_env clo_env fns i)`,
  CASES_ON `f2:clos_v` THEN REWRITE_TAC[dest_closure_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "clos_v"] THEN MESON_TAC[]);;

(* local helpers: an update of related finite maps; ref_rel with the right *)
(* side known; the references of related states; updates of references     *)
let CLOSP2AUX_letop_FMAP_REL_FUPDATE = prove
 (`!(r:A->B->bool) (f1:(K,A)fmap) f2 k a b.
     clos_letopProof_FMAP_REL r f1 f2 /\ r a b ==>
     clos_letopProof_FMAP_REL r (f1 |+ (k,a)) (f2 |+ (k,b))`,
  REWRITE_TAC[clos_letopProof_FMAP_REL_def; FDOM_FUPDATE; FLOOKUP_UPDATE] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[injectivity "option"] THEN ASM_MESON_TAC[]);;

let CLOSP2AUX_letop_ref_rel_right = prove
 (`(!x bs. clos_letopProof_ref_rel x (clos_ByteArray bs) <=> x = clos_ByteArray bs) /\
   (!x ys. clos_letopProof_ref_rel x (clos_ValueArray ys) <=>
           ?xs. x = clos_ValueArray xs /\ ALL2 clos_letopProof_v_rel xs ys) /\
   (!x m w. clos_letopProof_ref_rel x (clos_Thunk m w) <=>
            ?v. x = clos_Thunk m v /\ clos_letopProof_v_rel v w)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_letopProof_ref_rel_cases] THEN
  REWRITE_TAC[distinctness "clos_ref"; injectivity "clos_ref"] THEN MESON_TAC[]);;

let CLOSP2AUX_letop_ref_rel_left = prove
 (`(!y bs. clos_letopProof_ref_rel (clos_ByteArray bs) y <=> y = clos_ByteArray bs) /\
   (!y xs. clos_letopProof_ref_rel (clos_ValueArray xs) y <=>
           ?ys. y = clos_ValueArray ys /\ ALL2 clos_letopProof_v_rel xs ys) /\
   (!y m v. clos_letopProof_ref_rel (clos_Thunk m v) y <=>
            ?w. y = clos_Thunk m w /\ clos_letopProof_v_rel v w)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_letopProof_ref_rel_cases] THEN
  REWRITE_TAC[distinctness "clos_ref"; injectivity "clos_ref"] THEN MESON_TAC[]);;

let CLOSP2AUX_letop_flookup_rel = prove
 (`!(s1:(C,FFI)clos_state) s2 n.
     clos_letopProof_state_rel s1 s2 ==>
     OPTREL clos_letopProof_ref_rel
            (FLOOKUP (clos_state_refs s1) n) (FLOOKUP (clos_state_refs s2) n)`,
  REWRITE_TAC[clos_letopProof_state_rel_def; clos_letopProof_FMAP_REL_def] THEN
  REPEAT STRIP_TAC THEN
  CASES_ON `FLOOKUP (clos_state_refs (s1:(C,FFI)clos_state)) n` THENL
   [SUBGOAL_THEN `FLOOKUP (clos_state_refs (s2:(C,FFI)clos_state)) n = NONE` SUBST1_TAC THENL
     [UNDISCH_TAC `FLOOKUP (clos_state_refs (s1:(C,FFI)clos_state)) n = NONE` THEN
      REWRITE_TAC[FLOOKUP_DEF] THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
      REWRITE_TAC[distinctness "option"];
      REWRITE_TAC[OPTREL_THM]];
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `a:(clos_v)clos_ref`] o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[OPTREL_THM]]);;

let CLOSP2AUX_letop_state_rel_refs_upd = prove
 (`!(s1:(C,FFI)clos_state) s2 p a b.
     clos_letopProof_state_rel s1 s2 /\ clos_letopProof_ref_rel a b ==>
     clos_letopProof_state_rel
       (clos_state_refs_fupd (K (clos_state_refs s1 |+ (p,a))) s1)
       (clos_state_refs_fupd (K (clos_state_refs s2 |+ (p,b))) s2)`,
  REWRITE_TAC[clos_letopProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[CLOSP2AUX_letop_FMAP_REL_FUPDATE]);;

(* HOL4: simple_state_rel [local] *)
let clos_letopProof_simple_state_rel = prove
 (`clos_simple_state_rel clos_letopProof_v_rel
     (clos_letopProof_state_rel:(C,FFI)clos_state->(C,FFI)clos_state->bool)`,
  REWRITE_TAC[clos_simple_state_rel_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `ptr:num` o MATCH_MP CLOSP2AUX_letop_flookup_rel) THEN
    ASM_REWRITE_TAC[OPTREL_NONE];
    FIRST_ASSUM(MP_TAC o SPEC `ptr:num` o MATCH_MP CLOSP2AUX_letop_flookup_rel) THEN
    ASM_REWRITE_TAC[OPTREL_SOME; CLOSP2AUX_letop_ref_rel_right] THEN MESON_TAC[];
    FIRST_ASSUM(MP_TAC o SPEC `ptr:num` o MATCH_MP CLOSP2AUX_letop_flookup_rel) THEN
    ASM_REWRITE_TAC[OPTREL_SOME; CLOSP2AUX_letop_ref_rel_right] THEN MESON_TAC[];
    FIRST_ASSUM(MP_TAC o SPEC `ptr:num` o MATCH_MP CLOSP2AUX_letop_flookup_rel) THEN
    ASM_REWRITE_TAC[OPTREL_SOME; CLOSP2AUX_letop_ref_rel_right] THEN MESON_TAC[];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_letopProof_state_rel_def]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  FIRST_ASSUM(fun th -> if can (find_term (fun t -> t = `clos_letopProof_FMAP_REL:
                              (clos_v clos_ref->clos_v clos_ref->bool)->
                              (num,clos_v clos_ref)fmap->(num,clos_v clos_ref)fmap->bool`))
                              (concl th)
                        then ASSUME_TAC (CONJUNCT1 (REWRITE_RULE[clos_letopProof_FMAP_REL_def] th))
                        else NO_TAC) THEN
  ASM_REWRITE_TAC[clos_letopProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  MATCH_MP_TAC CLOSP2AUX_letop_FMAP_REL_FUPDATE THEN
  ASM_REWRITE_TAC[CLOSP2AUX_letop_ref_rel_right; injectivity "clos_ref"; UNWIND_THM1]);;

(* HOL4: do_app_lemma [local] *)
let clos_letopProof_do_app_lemma = prove
 (CASE_TERM
  `clos_letopProof_state_rel s (t:(C,FFI)clos_state) /\
   ALL2 clos_letopProof_v_rel xs ys ==>
   match clos_do_app opp xs s with
     Rerr err1 -> (?err2. clos_do_app opp ys t = Rerr err2 /\
                          exc_rel clos_letopProof_v_rel err1 err2)
   | Rval (x,s1) -> ?y t1. clos_letopProof_v_rel x y /\
                           clos_letopProof_state_rel s1 t1 /\
                           clos_do_app opp ys t = Rval (y,t1)`,
  MATCH_MP_TAC simple_val_rel_do_app THEN
  REWRITE_TAC[CLOSP2AUX_letop_simple_val_rel; clos_letopProof_simple_state_rel]);;

(* a local helper: the oracle conditions of simple_val_rel_do_install *)
let CLOSP2AUX_letop_simple_compile_state_rel = prove
 (`simple_compile_state_rel clos_letopProof_v_rel
     (clos_letopProof_state_rel:(C,FFI)clos_state->(C,FFI)clos_state->bool)
     clos_letop_compile_inc clos_letopProof_code_rel`,
  REWRITE_TAC[simple_compile_state_rel_def; clos_letopProof_simple_state_rel] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[clos_letopProof_state_rel_def]) THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM; clos_letop_compile_inc_def; PAIR_EQ] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[clos_letop_LENGTH_let_op; clos_letopProof_code_rel_def];
    GEN_TAC THEN
    REWRITE_TAC[clos_letopProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM;
                shift_seq_def] THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]]);;

(* HOL4: do_install_lemma [local] *)
let clos_letopProof_do_install_lemma = prove
 (CASE_TERM
  `clos_letopProof_state_rel (s:(C,FFI)clos_state) t /\
   ALL2 clos_letopProof_v_rel xs ys ==>
   match clos_do_install xs s with
     (Rerr err1,s1) -> ?err2 t1. clos_do_install ys t = (Rerr err2,t1) /\
                                 exc_rel clos_letopProof_v_rel err1 err2 /\
                                 clos_letopProof_state_rel s1 t1
   | (Rval exps1,s1) -> ?exps2 t1. clos_letopProof_state_rel s1 t1 /\ ~(exps1 = []) /\
                                   clos_letopProof_code_rel exps1 exps2 /\
                                   clos_do_install ys t = (Rval exps2,t1)`,
  MATCH_MP_TAC (ISPEC `clos_letop_compile_inc:clos_prog->clos_prog`
                 simple_val_rel_do_install) THEN
  REWRITE_TAC[CLOSP2AUX_letop_simple_val_rel; CLOSP2AUX_letop_simple_compile_state_rel]);;

(* HOL4: state_rel_opt_rel_refs [local] *)
let clos_letopProof_state_rel_opt_rel_refs = prove
 (`(clos_letopProof_state_rel (s1:(C,FFI)clos_state) s2 /\
    FLOOKUP (clos_state_refs s1) n = r1 ==>
    ?r2. FLOOKUP (clos_state_refs s2) n = r2 /\ OPTREL clos_letopProof_ref_rel r1 r2) /\
   (clos_letopProof_state_rel s1 s2 /\ FLOOKUP (clos_state_refs s2) n = r2 ==>
    ?r1. FLOOKUP (clos_state_refs s1) n = r1 /\ OPTREL clos_letopProof_ref_rel r1 r2)`,
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[UNWIND_THM1] THEN
  ASM_SIMP_TAC[CLOSP2AUX_letop_flookup_rel]);;

(* HOL4: state_rel_clocks_eqs [local] *)
let clos_letopProof_state_rel_clocks_eqs = prove
 (`clos_letopProof_state_rel (s1:(C,FFI)clos_state) s2 ==>
   clos_state_clock s1 = clos_state_clock s2`,
  SIMP_TAC[clos_letopProof_state_rel_def]);;

(* HOL4: state_rel_dec_clock [local] *)
let clos_letopProof_state_rel_dec_clock = prove
 (`clos_letopProof_state_rel (s1:(C,FFI)clos_state) s2 ==>
   clos_letopProof_state_rel (clos_dec_clock 1 s1) (clos_dec_clock 1 s2)`,
  SIMP_TAC[clos_letopProof_state_rel_def; clos_dec_clock_def; clos_state_INFO.ri_accfupds;
           K_THM]);;

(* a local helper: dest_thunk of related values agree on NotThunk *)
let CLOSP2AUX_letop_not_thunk = prove
 (`!(s1:(C,FFI)clos_state) s2 x y.
     clos_letopProof_state_rel s1 s2 /\ clos_letopProof_v_rel x y ==>
     (clos_dest_thunk [x] (clos_state_refs s1) = clos_NotThunk <=>
      clos_dest_thunk [y] (clos_state_refs s2) = clos_NotThunk)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`clos_letopProof_v_rel`;
                 `clos_letopProof_state_rel:(C,FFI)clos_state->(C,FFI)clos_state->bool`;
                 `s1:(C,FFI)clos_state`; `s2:(C,FFI)clos_state`;
                 `x:clos_v`; `y:clos_v`; `Evaluated`] CLOSPROPSAUX_bad_thunk_rel) THEN
  ASM_REWRITE_TAC[CLOSP2AUX_letop_simple_val_rel; clos_letopProof_simple_state_rel;
                  clos_bad_thunk_update_def] THEN
  MESON_TAC[]);;

(* HOL4: rel_update_thunk [local] *)
let clos_letopProof_rel_update_thunk = prove
 (`clos_letopProof_state_rel (s1:(C,FFI)clos_state) s2 /\
   ALL2 clos_letopProof_v_rel vs ys ==>
   (clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s1) vs = NONE ==>
    clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s2) ys = NONE) /\
   (clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s1) vs = SOME refs1 ==>
    ?refs2. clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s2) ys = SOME refs2 /\
            clos_letopProof_state_rel (clos_state_refs_fupd (K refs1) s1)
                                      (clos_state_refs_fupd (K refs2) s2))`,
  STRIP_TAC THEN
  SUBGOAL_THEN `(vs = [] /\ ys = []) \/
                (?x y. vs = [x] /\ ys = [y] /\ clos_letopProof_v_rel x y) \/
                (?x1 x2 r1 y1 y2 r2. vs = CONS x1 (CONS x2 r1) /\
                                     ys = CONS y1 (CONS y2 r2))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ALL2 clos_letopProof_v_rel vs ys` THEN
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
               CLOSP2AUX_letop_not_thunk) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  ASM_CASES_TAC `clos_dest_thunk [x] (clos_state_refs (s1:(C,FFI)clos_state)) =
                 clos_NotThunk` THENL
   [SUBGOAL_THEN `clos_dest_thunk [y] (clos_state_refs (s2:(C,FFI)clos_state)) =
                  clos_NotThunk` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    SUBGOAL_THEN `~(clos_dest_thunk [y] (clos_state_refs (s2:(C,FFI)clos_state)) =
                    clos_NotThunk)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CLOSSEMAUX_dest_thunk_NONE; distinctness "option"]] THEN
  REWRITE_TAC[store_thunk_def] THEN
  MP_TAC(SPECL [`s1:(C,FFI)clos_state`; `s2:(C,FFI)clos_state`; `ptr:num`]
               CLOSP2AUX_letop_flookup_rel) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (clos_state_refs (s1:(C,FFI)clos_state)) ptr` THEN
  CASES_ON `FLOOKUP (clos_state_refs (s2:(C,FFI)clos_state)) ptr` THEN
  REWRITE_TAC[OPTREL_THM; case_def "option"; distinctness "option"] THEN
  CASES_ON `a:(clos_v)clos_ref` THEN REWRITE_TAC[CLOSP2AUX_letop_ref_rel_left] THEN
  STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[distinctness "option"] THEN
  TRY(CASES_ON `a0:thunk_mode` THEN CASE_REWRITE_TAC[]) THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[UNWIND_THM1] THEN
  MATCH_MP_TAC CLOSP2AUX_letop_state_rel_refs_upd THEN
  ASM_REWRITE_TAC[CLOSP2AUX_letop_ref_rel_left; injectivity "clos_ref"; UNWIND_THM1]);;

(* ------------------------------------------------------------------------- *)
(* The correctness of let_op (HOL4: evaluate_let_op), a forwards simulation, *)
(* proved by the induction of closProps (CLOSPROPSAUX_evaluate_ind) on the   *)
(* source evaluation, with one lemma per case and local tactics:            *)
(*   NAME_TAC  name the first source evaluation of the goal's antecedent     *)
(*   COND_IH_TAC  resolve the conditional induction hypotheses              *)
(*   IH_TAC    apply an induction hypothesis to the newest named source      *)
(*             evaluation: the target evaluation, related result and state,  *)
(*             and rewrite the target of the goal with it                    *)
(*   SPLIT_TAC split the related results (Rval, Rraise, Rabort)              *)
(*   FIN_TAC   finish when both results are known                            *)
(* (HOL4: first_x_assum drule \\ disch_then drule \\ fs [case_eq_thms])      *)
(* ------------------------------------------------------------------------- *)

let CLOSP2AUX_letop_ind =
  let p = `\xs env1 (s1:(C,FFI)clos_state).
     !res1 s2 ys env2 t1.
       clos_evaluate (xs,env1,s1) = (res1,s2) /\
       ALL2 clos_letopProof_v_rel env1 env2 /\
       clos_letopProof_state_rel s1 t1 /\ clos_letopProof_code_rel xs ys ==>
       ?res2 t2.
         clos_evaluate (ys,env2,t1) = (res2,t2) /\
         result_rel (ALL2 clos_letopProof_v_rel) clos_letopProof_v_rel res1 res2 /\
         clos_letopProof_state_rel s2 t2`
  and q = `\loc_opt f1 args1 (s1:(C,FFI)clos_state).
     !res1 s2 f2 args2 t1.
       evaluate_app loc_opt f1 args1 s1 = (res1,s2) /\
       clos_letopProof_v_rel f1 f2 /\ ALL2 clos_letopProof_v_rel args1 args2 /\
       clos_letopProof_state_rel s1 t1 ==>
       ?res2 t2.
         evaluate_app loc_opt f2 args2 t1 = (res2,t2) /\
         result_rel (ALL2 clos_letopProof_v_rel) clos_letopProof_v_rel res1 res2 /\
         clos_letopProof_state_rel s2 t2` in
  CONV_RULE (DEPTH_CONV BETA_CONV) (ISPECL [p;q] CLOSPROPSAUX_evaluate_ind);;
let CLOSP2AUX_letop_cases = conjuncts (lhand (concl CLOSP2AUX_letop_ind));;

let CLOSP2AUX_letop_counter = ref 0;;

let CLOSP2AUX_letop_is_eval t =
  (CLOSPROPSAUX_is_app "clos_evaluate" t && is_comb t) ||
  (CLOSPROPSAUX_is_app "evaluate_app" t && length (snd (strip_comb t)) = 4);;

let CLOSP2AUX_letop_is_P th =
  let c = snd(strip_forall(concl th)) in
  is_imp c && is_conj (lhand c) &&
  (let a = lhand (lhand c) in
   is_eq a && CLOSP2AUX_letop_is_eval (lhs a) && is_pair (rhs a) &&
   is_var (fst (dest_pair (rhs a))));;

let CLOSP2AUX_LETOP_COND_IH_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let mentions_eval t = can (find_term CLOSP2AUX_letop_is_eval) t in
  let is_cond_ih th =
    not (CLOSP2AUX_letop_is_P th) &&
    (let c = snd(strip_forall(concl th)) in
     is_imp c && mentions_eval (rand c) && is_forall (rand c)) in
  let cihs = filter is_cond_ih asms in
  let rec resolve depth th =
    if CLOSP2AUX_letop_is_P th then [th]
    else if depth = 0 then [] else
    let rs = mapfilter (fun a -> MATCH_MP th a) asms in
    flat (map (resolve (depth-1)) rs) in
  let res = flat (map (fun th -> resolve 4 (CLOSPROPSAUX_curry_top th)) cihs) in
  let res = filter (fun th -> not (exists (fun a -> aconv (concl a) (concl th)) asms)) res in
  MAP_EVERY ASSUME_TAC res gl;;

let rec CLOSP2AUX_letop_find_closed bvs tm =
  (if CLOSP2AUX_letop_is_eval tm && not (exists (fun v -> vfree_in v tm) bvs)
   then [tm] else []) @
  (match tm with
     Comb(f,x) -> CLOSP2AUX_letop_find_closed bvs f @ CLOSP2AUX_letop_find_closed bvs x
   | Abs(v,b) -> CLOSP2AUX_letop_find_closed (v::bvs) b
   | _ -> []);;

let rec CLOSP2AUX_letop_find_closed_any bvs tm =
  (if not (exists (fun v -> vfree_in v tm) bvs) then [tm] else []) @
  (match tm with
     Comb(f,x) -> CLOSP2AUX_letop_find_closed_any bvs f @
                  CLOSP2AUX_letop_find_closed_any bvs x
   | Abs(v,b) -> CLOSP2AUX_letop_find_closed_any (v::bvs) b
   | _ -> []);;

let CLOSP2AUX_LETOP_NAME_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w in
  let named = mapfilter (fun (_,th) -> lhs (concl th)) asl in
  let evs = filter (fun t -> not (mem t named)) (CLOSP2AUX_letop_find_closed [] ant) in
  let tm = hd evs in
  let ty = type_of tm in
  let rty,sty = (match dest_type ty with (_,[a;b]) -> a,b | _ -> failwith "NAME") in
  incr CLOSP2AUX_letop_counter;
  let k = string_of_int (!CLOSP2AUX_letop_counter) in
  let r = mk_var("rr" ^ k, rty) and s = mk_var("ss" ^ k, sty) in
  (MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN r (X_CHOOSE_THEN s ASSUME_TAC)) THEN
   POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
   CASE_REWRITE_TAC[]) gl;;

(* the code_rel antecedent of an induction hypothesis: from an assumption, *)
(* or the target let_op X of the source X                                   *)
let CLOSP2AUX_letop_code_disch (asl:thm list) (th:thm) : thm =
  try tryfind (fun a -> MATCH_MP th a) asl with Failure _ ->
  let ys,bod = dest_forall (concl th) in
  let x = lhand (lhand bod) in
  let tgt = if can (find_term (fun t -> try fst(dest_const t) = "clos_AppUnit"
                                       with Failure _ -> false)) x
            then x else mk_comb(`clos_letop_let_op`, x) in
  let th1 = SPEC tgt th in
  MP th1 (EQT_ELIM (REWRITE_CONV[clos_letopProof_code_rel_def; clos_letop_let_op_def;
                                 clos_AppUnit_def; HD] (lhand (concl th1))));;

let CLOSP2AUX_letop_all2_cons = prove
 (`!h1 h2 t1 t2. clos_letopProof_v_rel h1 h2 /\ ALL2 clos_letopProof_v_rel t1 t2 ==>
                 ALL2 clos_letopProof_v_rel (CONS h1 t1) (CONS h2 t2)`,
  REWRITE_TAC[ALL2]);;

let CLOSP2AUX_letop_all2_append = ISPEC `clos_letopProof_v_rel` EVERY2_APPEND_suff;;

let CLOSP2AUX_letop_all2_nil = prove
 (`ALL2 clos_letopProof_v_rel [] []`,
  REWRITE_TAC[ALL2]);;

(* the relation of a source environment to a target one *)
let rec CLOSP2AUX_letop_env (asl:thm list) (e:term) : thm =
  try find (fun th -> let c = concl th in
              CLOSPROPSAUX_is_app "ALL2" c && lhand c = e &&
              rator (rator c) = `ALL2 clos_letopProof_v_rel`) asl
  with Failure _ ->
  if CLOSPROPSAUX_is_app "APPEND" e then
    MATCH_MP CLOSP2AUX_letop_all2_append
      (CONJ (CLOSP2AUX_letop_env asl (lhand e)) (CLOSP2AUX_letop_env asl (rand e)))
  else if is_cons e then
    let h,t = dest_cons e in
    let vh = find (fun th -> let c = concl th in
                     CLOSPROPSAUX_is_app "clos_letopProof_v_rel" c && lhand c = h) asl in
    MATCH_MP CLOSP2AUX_letop_all2_cons (CONJ vh (CLOSP2AUX_letop_env asl t))
  else if e = `[]:clos_v list` then CLOSP2AUX_letop_all2_nil
  else failwith "CLOSP2AUX_letop_env";;

let CLOSP2AUX_LETOP_ENV_TAC : tactic = fun (asl,w as gl) ->
  let ev = concl (snd (hd asl)) in
  let l = lhs ev in
  if not (CLOSPROPSAUX_is_app "clos_evaluate" l) then ALL_TAC gl else
  let e = fst (dest_pair (snd (dest_pair (rand l)))) in
  let asms = map snd asl in
  let th = CLOSP2AUX_letop_env asms e in
  if exists (fun a -> concl a = concl th) asms then ALL_TAC gl
  else (ASSUME_TAC th THEN
        (fun (asl,w) -> match asl with
             a::b::rest -> ALL_TAC (b::a::rest,w)
           | _ -> ALL_TAC (asl,w))) gl;;

let CLOSP2AUX_letop_apply (asl:thm list) (ih:thm) (ev:thm) : thm =
  let th1 = MATCH_MP (REWRITE_RULE[IMP_CONJ] ih) ev in
  let rec disch th =
    let vs,bod = strip_forall (concl th) in
    if not (is_imp bod) then th else
    let ant = lhand bod in
    if CLOSPROPSAUX_is_app "clos_letopProof_code_rel" ant
    then CLOSP2AUX_letop_code_disch asl th
    else disch (tryfind (fun a -> MATCH_MP th a) asl) in
  disch th1;;

let CLOSP2AUX_LETOP_IH_TAC : tactic = fun (asl,w as gl) ->
  let ev = snd (hd asl) in
  let asms = map snd asl in
  let ihs = filter CLOSP2AUX_letop_is_P asms in
  let res = mapfilter (fun ih -> CLOSP2AUX_letop_apply asms ih ev) ihs in
  if res = [] then failwith "CLOSP2AUX_LETOP_IH_TAC" else
  let th = hd res in
  let k = string_of_int (!CLOSP2AUX_letop_counter) in
  let v1,b1 = dest_exists (concl th) in
  let v2,_ = dest_exists b1 in
  let r = mk_var("rt" ^ k, type_of v1) and t = mk_var("tt" ^ k, type_of v2) in
  (X_CHOOSE_THEN r (X_CHOOSE_THEN t
     (fun th -> let tg,rest = CONJ_PAIR th in
                REWRITE_TAC[HD_let_op_SING] THEN REWRITE_TAC[tg] THEN
                ASSUME_TAC tg THEN STRIP_ASSUME_TAC rest)) th THEN
   CASE_REWRITE_TAC[]) gl;;

let CLOSP2AUX_letop_res_cases = prove
 (`!r rr. result_rel (ALL2 clos_letopProof_v_rel) clos_letopProof_v_rel r rr ==>
          (?a a'. r = Rval a /\ rr = Rval a' /\ ALL2 clos_letopProof_v_rel a a') \/
          (?v v'. r = Rerr (Rraise v) /\ rr = Rerr (Rraise v') /\
                  clos_letopProof_v_rel v v') \/
          (?ab. r = Rerr (Rabort ab) /\ rr = Rerr (Rabort ab))`,
  REPEAT GEN_TAC THEN
  CASES_ON `r:(clos_v list,clos_v)result` THEN
  REWRITE_TAC[result_rel_Rval; result_rel_Rerr1; injectivity "result";
              distinctness "result"] THENL [MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `a:(clos_v)error_result` THEN
  REWRITE_TAC[exc_rel_raise1; exc_rel_type_error1; injectivity "error_result";
              distinctness "error_result"] THEN MESON_TAC[]);;

let CLOSP2AUX_LETOP_SPLIT_TAC : tactic = fun (asl,w as gl) ->
  let k = string_of_int (!CLOSP2AUX_letop_counter) in
  let rr = mk_var("rr" ^ k, `:(clos_v list,clos_v)result`) in
  let sa = mk_var("sa" ^ k, `:clos_v list`) and ta = mk_var("ta" ^ k, `:clos_v list`)
  and sv = mk_var("sv" ^ k, `:clos_v`) and tv = mk_var("tv" ^ k, `:clos_v`)
  and ab = mk_var("ab" ^ k, `:abort`) in
  (FIRST_X_ASSUM(fun th ->
     if CLOSPROPSAUX_is_app "result_rel" (concl th) && lhand (concl th) = rr
     then DISJ_CASES_THEN2 (X_CHOOSE_THEN sa (X_CHOOSE_THEN ta STRIP_ASSUME_TAC))
            (DISJ_CASES_THEN2 (X_CHOOSE_THEN sv (X_CHOOSE_THEN tv STRIP_ASSUME_TAC))
                              (X_CHOOSE_THEN ab STRIP_ASSUME_TAC))
            (MATCH_MP CLOSP2AUX_letop_res_cases th)
     else NO_TAC) THEN
   RVEQ_TAC THEN CASE_REWRITE_TAC[]) gl;;

let CLOSP2AUX_LETOP_STEP_TAC : tactic =
  CLOSP2AUX_LETOP_COND_IH_TAC THEN CLOSP2AUX_LETOP_NAME_TAC THEN
  TRY CLOSP2AUX_LETOP_ENV_TAC THEN CLOSP2AUX_LETOP_IH_TAC THEN CLOSP2AUX_LETOP_SPLIT_TAC;;

let CLOSP2AUX_letop_evaluate_SING_let_op = prove
 (`!x env (s:(C,FFI)clos_state) r s2.
     clos_evaluate (clos_letop_let_op [x],env,s) = (Rval r,s2) ==> ?r1. r = [r1]`,
  REWRITE_TAC[CONJUNCT1 clos_letop_let_op_sing_eq] THEN MESON_TAC[clos_evaluate_SING]);;

let CLOSP2AUX_LETOP_SING_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && CLOSPROPSAUX_is_app "clos_evaluate" (lhs c) &&
       is_pair (rhs c) &&
       (let r = fst(dest_pair(rhs c)) in CLOSPROPSAUX_is_app "Rval" r && is_var (rand r)) &&
       (let xs = fst(dest_pair(rand(lhs c))) in
        (is_list xs && length (dest_list xs) = 1) ||
        (CLOSPROPSAUX_is_app "clos_letop_let_op" xs &&
         (let a = rand xs in is_list a && length (dest_list a) = 1)))
    then (let xs = fst(dest_pair(rand(lhs c))) in
          STRIP_ASSUME_TAC(MATCH_MP (if is_list xs then clos_evaluate_SING
                                     else CLOSP2AUX_letop_evaluate_SING_let_op) th) THEN
          ASSUME_TAC th)
    else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_var (lhs (concl th)) &&
                              is_cons (rhs (concl th)) then SUBST_ALL_TAC th else NO_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if CLOSPROPSAUX_is_app "ALL2" c && is_cons (lhand c) && is_cons (rand c)
    then MP_TAC th THEN REWRITE_TAC[ALL2] THEN STRIP_TAC else NO_TAC));;

let CLOSP2AUX_LETOP_FIN_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC] THEN CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  CLOSP2AUX_LETOP_SING_TAC THEN
  ASM_REWRITE_TAC[result_rel_def; exc_rel_def; injectivity "result"; distinctness "result";
                  ALL2; HD];;

(* local helpers for dest_closure of related values (forwards) *)
let CLOSP2AUX_letop_full_env = prove
 (`!args1 args2 a1 a2 env1 env2 k.
     ALL2 clos_letopProof_v_rel args1 args2 /\ ALL2 clos_letopProof_v_rel a1 a2 /\
     ALL2 clos_letopProof_v_rel env1 env2 ==>
     ALL2 clos_letopProof_v_rel
       (APPEND (APPEND (REVERSE (TAKE k (REVERSE args1))) a1) env1)
       (APPEND (APPEND (REVERSE (TAKE k (REVERSE args2))) a2) env2)`,
  REPEAT STRIP_TAC THEN
  REPEAT(MATCH_MP_TAC CLOSP2AUX_letop_all2_append THEN CONJ_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EVERY2_REVERSE THEN
  MATCH_MP_TAC EVERY2_TAKE THEN MATCH_MP_TAC EVERY2_REVERSE THEN ASM_REWRITE_TAC[]);;

let CLOSP2AUX_letop_full_rest = prove
 (`!args1 args2 k.
     ALL2 clos_letopProof_v_rel args1 args2 ==>
     ALL2 clos_letopProof_v_rel (REVERSE (DROP k (REVERSE args1)))
                                (REVERSE (DROP k (REVERSE args2)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EVERY2_REVERSE THEN
  MATCH_MP_TAC EVERY2_DROP THEN MATCH_MP_TAC EVERY2_REVERSE THEN ASM_REWRITE_TAC[]);;

let CLOSP2AUX_letop_recc_rel = prove
 (`!loc env1 env2 funs1 funs2 n.
     ALL2 clos_letopProof_v_rel env1 env2 /\ ALL2 clos_letopProof_f_rel funs1 funs2 ==>
     ALL2 clos_letopProof_v_rel
       (list_of_seq (clos_Recclosure loc [] env1 funs1) n)
       (list_of_seq (clos_Recclosure loc [] env2 funs2) n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_REL_GENLIST] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (el 6 (CONJUNCTS clos_letopProof_v_rel_rules)) THEN
  ASM_REWRITE_TAC[ALL2]);;

let CLOSP2AUX_letop_full_env_rec = prove
 (`!args1 args2 a1 a2 env1 env2 funs1 funs2 loc k n.
     ALL2 clos_letopProof_v_rel args1 args2 /\ ALL2 clos_letopProof_v_rel a1 a2 /\
     ALL2 clos_letopProof_v_rel env1 env2 /\ ALL2 clos_letopProof_f_rel funs1 funs2 ==>
     ALL2 clos_letopProof_v_rel
       (APPEND (APPEND (APPEND (REVERSE (TAKE k (REVERSE args1))) a1)
                       (list_of_seq (clos_Recclosure loc [] env1 funs1) n)) env1)
       (APPEND (APPEND (APPEND (REVERSE (TAKE k (REVERSE args2))) a2)
                       (list_of_seq (clos_Recclosure loc [] env2 funs2) n)) env2)`,
  REPEAT STRIP_TAC THEN
  REPEAT(MATCH_MP_TAC CLOSP2AUX_letop_all2_append THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[CLOSP2AUX_letop_recc_rel] THEN MATCH_MP_TAC EVERY2_REVERSE THEN
  MATCH_MP_TAC EVERY2_TAKE THEN MATCH_MP_TAC EVERY2_REVERSE THEN ASM_REWRITE_TAC[]);;

let CLOSP2AUX_LETOP_DC_TAC : tactic =
  ASSUM_LIST(fun l -> MAP_EVERY (ASSUME_TAC o MATCH_MP LIST_REL_LENGTH)
                        (filter (CLOSPROPSAUX_is_app "ALL2" o concl) l)) THEN
  ASM_REWRITE_TAC[COND_SWAP; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REPEAT COND_CASES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; distinctness "app_kind";
              injectivity "app_kind"] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  ASM_SIMP_TAC[CLOSP2AUX_letop_full_env; CLOSP2AUX_letop_full_rest; CLOSP2AUX_letop_recc_rel;
               CLOSP2AUX_letop_full_env_rec; CLOSP2AUX_letop_all2_append] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC (el 5 (CONJUNCTS clos_letopProof_v_rel_rules))) THEN
  TRY(MATCH_MP_TAC (el 6 (CONJUNCTS clos_letopProof_v_rel_rules))) THEN
  ASM_SIMP_TAC[CLOSP2AUX_letop_all2_append];;

let CLOSP2AUX_letop_dest_closure_cases = prove
 (`!m lo f1 f2 args1 args2.
     clos_letopProof_v_rel f1 f2 /\ ALL2 clos_letopProof_v_rel args1 args2 ==>
     (dest_closure m lo f1 args1 = NONE /\ dest_closure m lo f2 args2 = NONE) \/
     (?v1 v2. dest_closure m lo f1 args1 = SOME (Partial_app v1) /\
              dest_closure m lo f2 args2 = SOME (Partial_app v2) /\
              clos_letopProof_v_rel v1 v2) \/
     (?e1 env1 rest1 e2 env2 rest2.
        dest_closure m lo f1 args1 = SOME (Full_app e1 env1 rest1) /\
        dest_closure m lo f2 args2 = SOME (Full_app e2 env2 rest2) /\
        clos_letopProof_code_rel [e1] [e2] /\ ALL2 clos_letopProof_v_rel env1 env2 /\
        ALL2 clos_letopProof_v_rel rest1 rest2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CASES_ON `f1:clos_v` THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSPROPSAUX_is_app "clos_letopProof_v_rel" o concl)) THEN
  REWRITE_TAC[clos_letopProof_v_rel_simps] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[dest_closure_def] THEN CASE_REWRITE_TAC[] THENL
   [CLOSP2AUX_LETOP_DC_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `EL a4 (a3:(num#clos_exp)list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `b1:clos_exp` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `EL a4 (funs2:(num#clos_exp)list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:num` (X_CHOOSE_THEN `b2:clos_exp` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH o
              check (fun th -> concl th = `ALL2 clos_letopProof_f_rel a3 funs2`)) THEN
  ASM_CASES_TAC `a4 < LENGTH (a3:(num#clos_exp)list)` THENL
   [SUBGOAL_THEN `clos_letopProof_f_rel (EL a4 a3) (EL a4 funs2)` MP_TAC THENL
     [ASM_MESON_TAC[LIST_REL_EL_EQN]; ALL_TAC] THEN
    ASM_REWRITE_TAC[clos_letopProof_f_rel_def] THEN STRIP_TAC THEN RVEQ_TAC THEN
    CLOSP2AUX_LETOP_DC_TAC;
    SUBGOAL_THEN `LENGTH (a3:(num#clos_exp)list) <= a4 /\
                  LENGTH (funs2:(num#clos_exp)list) <= a4` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

(* HOL4: dest_closure_SOME_Full_app *)
let clos_letopProof_dest_closure_SOME_Full_app = prove
 (`clos_letopProof_v_rel f1 f2 /\ clos_letopProof_v_rel a1 a2 /\
   ALL2 clos_letopProof_v_rel args1 args2 /\
   dest_closure max_app loc_opt f1 (CONS a1 args1) = SOME (Full_app exp1 env1 rest_args1) ==>
   ?exp2 env2 rest_args2.
     clos_letopProof_code_rel [exp1] [exp2] /\
     ALL2 clos_letopProof_v_rel env1 env2 /\
     ALL2 clos_letopProof_v_rel rest_args1 rest_args2 /\
     dest_closure max_app loc_opt f2 (CONS a2 args2) = SOME (Full_app exp2 env2 rest_args2)`,
  STRIP_TAC THEN
  MP_TAC(ISPECL [`max_app:num`; `loc_opt:num option`; `f1:clos_v`; `f2:clos_v`;
                 `CONS (a1:clos_v) args1`; `CONS (a2:clos_v) args2`]
                CLOSP2AUX_letop_dest_closure_cases) THEN
  ASM_REWRITE_TAC[ALL2] THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; distinctness "app_kind";
              injectivity "app_kind"] THEN
  MESON_TAC[]);;

let CLOSP2AUX_LETOP_INTRO_TAC : tactic =
  REPEAT GEN_TAC THEN
  (fun (asl,w as gl) ->
     if is_imp w && is_forall (rand w)
     then (DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN REPEAT GEN_TAC) gl
     else ALL_TAC gl) THEN
  STRIP_TAC;;

(* the target code of the case: ys = let_op xs, unfolded once *)
let CLOSP2AUX_LETOP_TGT_TAC : tactic =
  FIRST_X_ASSUM(SUBST_ALL_TAC o
    REWRITE_RULE[clos_letopProof_code_rel_def; clos_letop_let_op_def; LET_DEF; LET_END_DEF] o
    check (CLOSPROPSAUX_is_app "clos_letopProof_code_rel" o concl));;

let CLOSP2AUX_LETOP_UNFOLD_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
                                CLOSP2AUX_letop_is_eval (lhs (concl th)) &&
                                is_var (fst (dest_pair (rhs (concl th)))))) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN REWRITE_TAC[HD_let_op_SING] THEN
  CASE_REWRITE_TAC[];;

let CLOSP2AUX_letop_nil = prove
 (el 0 CLOSP2AUX_letop_cases,
  CLOSP2AUX_LETOP_INTRO_TAC THEN CLOSP2AUX_LETOP_TGT_TAC THEN
  CLOSP2AUX_LETOP_UNFOLD_TAC THEN CLOSP2AUX_LETOP_FIN_TAC);;

let CLOSP2AUX_letop_cons = prove
 (el 1 CLOSP2AUX_letop_cases,
  CLOSP2AUX_LETOP_INTRO_TAC THEN CLOSP2AUX_LETOP_TGT_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
                                CLOSP2AUX_letop_is_eval (lhs (concl th)) &&
                                is_var (fst (dest_pair (rhs (concl th)))))) THEN
  ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN REWRITE_TAC[HD_let_op_SING] THEN
  CASE_REWRITE_TAC[] THEN
  REPEAT CLOSP2AUX_LETOP_STEP_TAC THEN CLOSP2AUX_LETOP_FIN_TAC);;

let CLOSP2AUX_letop_var = prove
 (el 2 CLOSP2AUX_letop_cases,
  CLOSP2AUX_LETOP_INTRO_TAC THEN CLOSP2AUX_LETOP_TGT_TAC THEN CLOSP2AUX_LETOP_UNFOLD_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH o
              check (CLOSPROPSAUX_is_app "ALL2" o concl)) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN CLOSP2AUX_LETOP_FIN_TAC THEN
  ASM_MESON_TAC[LIST_REL_EL_EQN]);;

let CLOSP2AUX_letop_Boolv_HD = prove
 (`!a a' b. ALL2 clos_letopProof_v_rel a a' ==>
            (clos_Boolv b = HD a' <=> clos_Boolv b = HD a)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[HD] THEN
  REWRITE_TAC[clos_Boolv_def] THEN
  UNDISCH_TAC `clos_letopProof_v_rel h h'` THEN
  GEN_REWRITE_TAC LAND_CONV [clos_letopProof_v_rel_cases] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_NIL]) THEN
  EQ_TAC THEN STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_NIL]) THEN
  ASM_MESON_TAC[LIST_REL_NIL]);;

(* rewrite the Boolv tests of target values to those of the source values *)
let CLOSP2AUX_LETOP_BOOLV_TAC : tactic =
  ASSUM_LIST(fun l -> REWRITE_TAC(mapfilter (MATCH_MP CLOSP2AUX_letop_Boolv_HD) l));;

let CLOSP2AUX_letop_if = prove
 (el 3 CLOSP2AUX_letop_cases,
  CLOSP2AUX_LETOP_INTRO_TAC THEN CLOSP2AUX_LETOP_TGT_TAC THEN CLOSP2AUX_LETOP_UNFOLD_TAC THEN
  CLOSP2AUX_LETOP_STEP_TAC THENL
   [ALL_TAC; CLOSP2AUX_LETOP_FIN_TAC; CLOSP2AUX_LETOP_FIN_TAC] THEN
  CLOSP2AUX_LETOP_BOOLV_TAC THEN REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THEN
  REPEAT CLOSP2AUX_LETOP_STEP_TAC THEN CLOSP2AUX_LETOP_FIN_TAC);;

let CLOSP2AUX_letop_raise = prove
 (el 5 CLOSP2AUX_letop_cases,
  CLOSP2AUX_LETOP_INTRO_TAC THEN CLOSP2AUX_LETOP_TGT_TAC THEN CLOSP2AUX_LETOP_UNFOLD_TAC THEN
  REPEAT CLOSP2AUX_LETOP_STEP_TAC THEN CLOSP2AUX_LETOP_FIN_TAC);;

let CLOSP2AUX_letop_handle = prove
 (el 6 CLOSP2AUX_letop_cases,
  CLOSP2AUX_LETOP_INTRO_TAC THEN CLOSP2AUX_LETOP_TGT_TAC THEN CLOSP2AUX_LETOP_UNFOLD_TAC THEN
  REPEAT CLOSP2AUX_LETOP_STEP_TAC THEN CLOSP2AUX_LETOP_FIN_TAC);;

let CLOSP2AUX_letop_let_op_Op = prove
 (`!x2 t op ys0. HD (clos_letop_let_op [x2]) = clos_Op t op ys0 ==>
                 clos_letop_let_op [x2] = [clos_Op t op ys0]`,
  MESON_TAC[HD_let_op_SING]);;

(* the target evaluation of the body of a Let that let_op turned into an Op: *)
(* its arguments are the variables of the bound values (HOL4: imp_res_tac    *)
(* dest_op_SOME_IMP \\ ... \\ drule var_list_IMP_evaluate)                  *)
let CLOSP2AUX_LETOP_OP_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let hd_th = find (fun th -> let c = concl th in
                     is_eq c && CLOSPROPSAUX_is_app "HD" (lhs c) &&
                     CLOSPROPSAUX_is_app "clos_Op" (rhs c)) asms in
  let lo = MATCH_MP CLOSP2AUX_letop_let_op_Op hd_th in
  let x2code = lhs (concl lo) in
  let ev = find (fun th -> let c = concl th in
                  is_eq c && CLOSPROPSAUX_is_app "clos_evaluate" (lhs c) &&
                  fst (dest_pair (rand (lhs c))) = x2code) asms in
  let vl = find (fun th -> CLOSPROPSAUX_is_app "clos_letop_var_list" (concl th)) asms in
  let args_tgt = rand (concl vl) in
  let ev_args = find (fun th -> let c = concl th in
                       is_eq c && CLOSPROPSAUX_is_app "clos_evaluate" (lhs c) &&
                       fst (dest_pair (rand (lhs c))) = args_tgt) asms in
  let len = MATCH_MP clos_evaluate_IMP_LENGTH ev_args in
  let vie = MATCH_MP var_list_IMP_evaluate (CONJ vl len) in
  let ev' = CASE_REWRITE_RULE[] (REWRITE_RULE[vie]
              (ONCE_REWRITE_RULE[clos_evaluate_def] (REWRITE_RULE[lo] ev))) in
  (REWRITE_TAC[ev'] THEN CASE_REWRITE_TAC[]) gl;;

let CLOSP2AUX_letop_let = prove
 (el 4 CLOSP2AUX_letop_cases,
  CLOSP2AUX_LETOP_INTRO_TAC THEN CLOSP2AUX_LETOP_TGT_TAC THEN
  CASES_ON `clos_letop_dest_op (HD (clos_letop_let_op [x2])) (clos_letop_let_op xs)` THEN
  CASE_REWRITE_TAC[] THENL
   [CLOSP2AUX_LETOP_UNFOLD_TAC THEN
    REPEAT CLOSP2AUX_LETOP_STEP_TAC THEN CLOSP2AUX_LETOP_FIN_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP dest_op_SOME_IMP o
              check (fun th -> is_eq (concl th) &&
                               CLOSPROPSAUX_is_app "clos_letop_dest_op" (lhs (concl th)))) THEN
  CLOSP2AUX_LETOP_UNFOLD_TAC THEN
  CLOSP2AUX_LETOP_STEP_TAC THENL
   [ALL_TAC; CLOSP2AUX_LETOP_FIN_TAC; CLOSP2AUX_LETOP_FIN_TAC] THEN
  CLOSP2AUX_LETOP_STEP_TAC THEN CLOSP2AUX_LETOP_OP_TAC THEN CLOSP2AUX_LETOP_FIN_TAC);;

(* local helpers for the Op case: dest_thunk, do_install, do_app and        *)
(* update_thunk of related values (HOL4: oneline dest_thunk_def,            *)
(* do_install_lemma, do_app_lemma, rel_update_thunk)                         *)

let CLOSP2AUX_letop_RefPtr_shape = prove
 (`!xs ys.
     ALL2 clos_letopProof_v_rel xs ys ==>
     (?b ptr. xs = [clos_RefPtr b ptr] /\ ys = [clos_RefPtr b ptr]) \/
     ((!b ptr. ~(xs = [clos_RefPtr b ptr])) /\ (!b ptr. ~(ys = [clos_RefPtr b ptr])))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `?b ptr. ys = [clos_RefPtr b ptr]` THENL
   [DISJ1_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `b:bool` (X_CHOOSE_THEN `ptr:num` SUBST_ALL_TAC)) THEN
    UNDISCH_TAC `ALL2 clos_letopProof_v_rel xs [clos_RefPtr b ptr]` THEN
    REWRITE_TAC[LIST_REL_CONS2; LIST_REL_NIL; CLOSP2AUX_letop_v_rel_right] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[CONS_11] THEN MESON_TAC[];
    DISJ2_TAC THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `ALL2 clos_letopProof_v_rel [clos_RefPtr b ptr] ys` THEN
      REWRITE_TAC[LIST_REL_CONS1; LIST_REL_NIL] THEN STRIP_TAC THEN
      UNDISCH_TAC `clos_letopProof_v_rel (clos_RefPtr b ptr) h'` THEN
      GEN_REWRITE_TAC LAND_CONV [clos_letopProof_v_rel_cases] THEN
      REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"] THEN
      STRIP_TAC THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]]]);;

let CLOSP2AUX_letop_dest_thunk_rel = prove
 (CASE_TERM `!(s:(C,FFI)clos_state) t xs ys.
     clos_letopProof_state_rel s t /\ ALL2 clos_letopProof_v_rel xs ys ==>
     match clos_dest_thunk ys (clos_state_refs t) with
       clos_BadRef -> clos_dest_thunk xs (clos_state_refs s) = clos_BadRef
     | clos_NotThunk -> clos_dest_thunk xs (clos_state_refs s) = clos_NotThunk
     | clos_IsThunk m w -> ?v. clos_dest_thunk xs (clos_state_refs s) = clos_IsThunk m v /\
                              clos_letopProof_v_rel v w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`xs:clos_v list`; `ys:clos_v list`] CLOSP2AUX_letop_RefPtr_shape) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[CLOSSEMAUX_dest_thunk_NotThunk] THEN CASE_REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[clos_dest_thunk_def] THEN
  MP_TAC(SPECL [`s:(C,FFI)clos_state`; `t:(C,FFI)clos_state`; `ptr:num`]
               CLOSP2AUX_letop_flookup_rel) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (clos_state_refs (t:(C,FFI)clos_state)) ptr` THEN
  CASES_ON `FLOOKUP (clos_state_refs (s:(C,FFI)clos_state)) ptr` THEN
  REWRITE_TAC[OPTREL_THM] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a:(clos_v)clos_ref` THEN REWRITE_TAC[CLOSP2AUX_letop_ref_rel_right] THEN
  STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a0:thunk_mode` THEN CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "clos_dest_thunk_ret"] THEN
  ASM_MESON_TAC[]);;

let CLOSP2AUX_letop_dest_thunk_IsThunk = prove
 (`!xs (refs:(num,(clos_v)clos_ref)fmap) m v.
     clos_dest_thunk xs refs = clos_IsThunk m v ==> ?b ptr. xs = [clos_RefPtr b ptr]`,
  MESON_TAC[CLOSSEMAUX_dest_thunk_NotThunk; distinctness "clos_dest_thunk_ret"]);;

let CLOSP2AUX_letop_dest_thunk_cases = prove
 (`!(s:(C,FFI)clos_state) t xs ys.
     clos_letopProof_state_rel s t /\ ALL2 clos_letopProof_v_rel xs ys ==>
     (clos_dest_thunk ys (clos_state_refs t) = clos_BadRef /\
      clos_dest_thunk xs (clos_state_refs s) = clos_BadRef) \/
     (clos_dest_thunk ys (clos_state_refs t) = clos_NotThunk /\
      clos_dest_thunk xs (clos_state_refs s) = clos_NotThunk) \/
     (?w v. clos_dest_thunk ys (clos_state_refs t) = clos_IsThunk Evaluated w /\
            clos_dest_thunk xs (clos_state_refs s) = clos_IsThunk Evaluated v /\
            clos_letopProof_v_rel v w) \/
     (?w v b ptr. clos_dest_thunk ys (clos_state_refs t) = clos_IsThunk NotEvaluated w /\
            clos_dest_thunk xs (clos_state_refs s) = clos_IsThunk NotEvaluated v /\
            clos_letopProof_v_rel v w /\
            ys = [clos_RefPtr b ptr] /\ xs = [clos_RefPtr b ptr])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CLOSP2AUX_letop_dest_thunk_rel) THEN
  CASES_ON `clos_dest_thunk ys (clos_state_refs (t:(C,FFI)clos_state))` THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "clos_dest_thunk_ret"; injectivity "clos_dest_thunk_ret"] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:clos_v` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSP2AUX_letop_dest_thunk_IsThunk o
    check (fun th -> is_eq (concl th) && lhand (lhs (concl th)) = `ys:clos_v list`)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSP2AUX_letop_RefPtr_shape o CONJUNCT2) THEN
  ASM_REWRITE_TAC[CONS_11; injectivity "clos_v"] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `a0:thunk_mode` (cases "thunk_mode")) THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[distinctness "thunk_mode"] THEN ASM_MESON_TAC[]);;

let CLOSP2AUX_letop_do_install_cases = prove
 (`!(s:(C,FFI)clos_state) t xs ys.
     clos_letopProof_state_rel s t /\ ALL2 clos_letopProof_v_rel xs ys ==>
     (?err1 s1 err2 t1. clos_do_install xs s = (Rerr err1,s1) /\
                        clos_do_install ys t = (Rerr err2,t1) /\
                        exc_rel clos_letopProof_v_rel err1 err2 /\
                        clos_letopProof_state_rel s1 t1) \/
     (?exps1 s1 exps2 t1.
        clos_do_install xs s = (Rval exps1,s1) /\
        clos_do_install ys t = (Rval exps2,t1) /\
        clos_letopProof_state_rel s1 t1 /\ ~(exps1 = []) /\
        clos_letopProof_code_rel exps1 exps2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP clos_letopProof_do_install_lemma) THEN
  MP_TAC(ISPEC `clos_do_install xs (s:(C,FFI)clos_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(clos_exp list,clos_v)result`
    (X_CHOOSE_THEN `s1:(C,FFI)clos_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN
  CASES_ON `r:(clos_exp list,clos_v)result` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"] THEN MESON_TAC[]);;

let CLOSP2AUX_letop_do_app_cases = prove
 (`!(s:(C,FFI)clos_state) t xs ys opp.
     clos_letopProof_state_rel s t /\ ALL2 clos_letopProof_v_rel xs ys ==>
     (?err1 err2. clos_do_app opp xs s = Rerr err1 /\ clos_do_app opp ys t = Rerr err2 /\
                  exc_rel clos_letopProof_v_rel err1 err2) \/
     (?x s1 y t1. clos_do_app opp xs s = Rval (x,s1) /\ clos_do_app opp ys t = Rval (y,t1) /\
                  clos_letopProof_v_rel x y /\ clos_letopProof_state_rel s1 t1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP clos_letopProof_do_app_lemma) THEN
  CASES_ON `clos_do_app opp xs (s:(C,FFI)clos_state)` THEN CASE_REWRITE_TAC[] THEN
  TRY(CASES_ON `a:clos_v#(C,FFI)clos_state` THEN CASE_REWRITE_TAC[]) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  MESON_TAC[]);;

let CLOSP2AUX_letop_update_thunk_cases = prove
 (`!(s1:(C,FFI)clos_state) s2 vs ys v ptr.
     clos_letopProof_state_rel s1 s2 /\ ALL2 clos_letopProof_v_rel vs ys ==>
     (clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s1) vs = NONE /\
      clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s2) ys = NONE) \/
     (?refs1 refs2.
        clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s1) vs = SOME refs1 /\
        clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s2) ys = SOME refs2 /\
        clos_letopProof_state_rel (clos_state_refs_fupd (K refs1) s1)
                                  (clos_state_refs_fupd (K refs2) s2))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs (s1:(C,FFI)clos_state)) vs` THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  ASM_MESON_TAC[clos_letopProof_rel_update_thunk]);;

(* local tactics of the Op case: split a do_install, dest_thunk, do_app or  *)
(* update_thunk of the source (in the goal's antecedent) together with the  *)
(* target's, by the case lemmas above                                       *)
let CLOSP2AUX_letop_rel_facts (asl:thm list) (xs:term) (s:term) : thm =
  let find_all2 l = find (fun th -> let c = concl th in
                      CLOSPROPSAUX_is_app "ALL2" c && lhand c = l &&
                      rator (rator c) = `ALL2 clos_letopProof_v_rel`) asl in
  let all2 = try find_all2 xs with Failure _ ->
             if CLOSPROPSAUX_is_app "REVERSE" xs
             then MATCH_MP EVERY2_REVERSE (find_all2 (rand xs))
             else failwith "CLOSP2AUX_letop_rel_facts" in
  let sr = find (fun th -> let c = concl th in
                   CLOSPROPSAUX_is_app "clos_letopProof_state_rel" c && lhand c = s) asl in
  CONJ sr all2;;

let CLOSP2AUX_letop_find_ant (s:string) (w:term) : term =
  hd (filter (CLOSPROPSAUX_is_app s) (CLOSP2AUX_letop_find_closed_any [] (lhand w)));;

let CLOSP2AUX_LETOP_INSTALL_TAC : tactic = fun (asl,w as gl) ->
  let tm = CLOSP2AUX_letop_find_ant "clos_do_install" w in
  let th = MATCH_MP CLOSP2AUX_letop_do_install_cases
             (CLOSP2AUX_letop_rel_facts (map snd asl) (lhand tm) (rand tm)) in
  (MP_TAC th THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
    [CLOSP2AUX_LETOP_FIN_TAC;
     REPEAT CLOSP2AUX_LETOP_STEP_TAC THEN CLOSP2AUX_LETOP_FIN_TAC THEN
     MATCH_MP_TAC LIST_REL_LAST THEN ASM_REWRITE_TAC[] THEN
     REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP clos_evaluate_IMP_LENGTH)) THEN
     ASM_MESON_TAC[LENGTH_EQ_NIL]]) gl;;

let CLOSP2AUX_LETOP_DO_APP_TAC : tactic = fun (asl,w as gl) ->
  let tm = CLOSP2AUX_letop_find_ant "clos_do_app" w in
  let opp = lhand (rator tm) in
  let th = SPEC opp (MATCH_MP CLOSP2AUX_letop_do_app_cases
             (CLOSP2AUX_letop_rel_facts (map snd asl) (lhand tm) (rand tm))) in
  (MP_TAC th THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CLOSP2AUX_LETOP_FIN_TAC) gl;;

let CLOSP2AUX_LETOP_UPDATE_TAC : tactic = fun (asl,w as gl) ->
  let tm = CLOSP2AUX_letop_find_ant "clos_update_thunk" w in
  let args = snd (strip_comb tm) in
  let p = hd (dest_list (el 0 args)) in
  let b = lhand p and ptr = rand p in
  let s = rand (el 1 args) in
  let th = SPECL [b; ptr] (MATCH_MP CLOSP2AUX_letop_update_thunk_cases
             (CLOSP2AUX_letop_rel_facts (map snd asl) (el 2 args) s)) in
  (MP_TAC th THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CLOSP2AUX_LETOP_FIN_TAC) gl;;

let CLOSP2AUX_LETOP_FORCE_TAC : tactic = fun (asl,w as gl) ->
  let tm = CLOSP2AUX_letop_find_ant "clos_dest_thunk" w in
  let th = MATCH_MP CLOSP2AUX_letop_dest_thunk_cases
             (CLOSP2AUX_letop_rel_facts (map snd asl) (lhand tm) (rand (rand tm))) in
  (MP_TAC th THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
    [CLOSP2AUX_LETOP_FIN_TAC; CLOSP2AUX_LETOP_FIN_TAC; CLOSP2AUX_LETOP_FIN_TAC;
     REPEAT(FIRST_X_ASSUM(fun th -> let c = concl th in
       if is_eq c && is_var (lhs c) && is_cons (rhs c) then SUBST_ALL_TAC th
       else NO_TAC)) THEN
     CLOSP2AUX_LETOP_STEP_TAC THENL
      [CLOSP2AUX_LETOP_UPDATE_TAC; CLOSP2AUX_LETOP_FIN_TAC; CLOSP2AUX_LETOP_FIN_TAC]]) gl;;

let CLOSP2AUX_letop_op = prove
 (el 7 CLOSP2AUX_letop_cases,
  CLOSP2AUX_LETOP_INTRO_TAC THEN CLOSP2AUX_LETOP_TGT_TAC THEN CLOSP2AUX_LETOP_UNFOLD_TAC THEN
  CLOSP2AUX_LETOP_STEP_TAC THENL
   [ALL_TAC; CLOSP2AUX_LETOP_FIN_TAC; CLOSP2AUX_LETOP_FIN_TAC] THEN
  ASM_CASES_TAC `op = clos_Install` THEN ASM_REWRITE_TAC[] THENL
   [CLOSP2AUX_LETOP_INSTALL_TAC;
    ASM_CASES_TAC `op = clos_ThunkOp ForceThunk` THEN ASM_REWRITE_TAC[] THENL
     [CLOSP2AUX_LETOP_FORCE_TAC; CLOSP2AUX_LETOP_DO_APP_TAC]]);;

let CLOSP2AUX_letop_lookup_vars_cases = prove
 (`!vs env1 env2. ALL2 clos_letopProof_v_rel env1 env2 ==>
     (lookup_vars vs env1 = NONE /\ lookup_vars vs env2 = NONE) \/
     (?l1 l2. lookup_vars vs env1 = SOME l1 /\ lookup_vars vs env2 = SOME l2 /\
              ALL2 clos_letopProof_v_rel l1 l2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `vs:num list` o
    MATCH_MP (REWRITE_RULE[RIGHT_FORALL_IMP_THM] (ONCE_REWRITE_RULE[SWAP_FORALL_THM]
              clos_letopProof_lookup_vars_lemma))) THEN
  CASES_ON `lookup_vars vs (env1:clos_v list)` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN MESON_TAC[]);;

let CLOSP2AUX_letop_fn = prove
 (el 8 CLOSP2AUX_letop_cases,
  CLOSP2AUX_LETOP_INTRO_TAC THEN CLOSP2AUX_LETOP_TGT_TAC THEN CLOSP2AUX_LETOP_UNFOLD_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2
    (REWRITE_RULE[clos_letopProof_state_rel_def] th))))]) THEN
  COND_CASES_TAC THENL [ALL_TAC; CLOSP2AUX_LETOP_FIN_TAC] THEN
  CASES_ON `vsopt:(num list)option` THEN CASE_REWRITE_TAC[] THENL
   [CLOSP2AUX_LETOP_FIN_TAC THEN
    MATCH_MP_TAC (el 5 (CONJUNCTS clos_letopProof_v_rel_rules)) THEN
    ASM_REWRITE_TAC[ALL2; clos_letopProof_code_rel_def; HD_let_op_SING];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:num list` o MATCH_MP CLOSP2AUX_letop_lookup_vars_cases o
              check (CLOSPROPSAUX_is_app "ALL2" o concl)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CLOSP2AUX_LETOP_FIN_TAC THEN
  MATCH_MP_TAC (el 5 (CONJUNCTS clos_letopProof_v_rel_rules)) THEN
  ASM_REWRITE_TAC[ALL2; clos_letopProof_code_rel_def; HD_let_op_SING]);;

(* local helpers for the Letrec case *)
let CLOSP2AUX_letop_f_rel_MAP = prove
 (CASE_TERM `!fns. ALL2 clos_letopProof_f_rel fns
               (MAP (\p. match p with
                           (num_args,x) -> (num_args, HD (clos_letop_let_op [x]))) fns)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL2] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `h:num#clos_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `x:clos_exp` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_letopProof_f_rel_def; clos_letopProof_code_rel_def; HD_let_op_SING]);;

let CLOSP2AUX_letop_ALL_MAP = prove
 (CASE_TERM `!(P:num->bool) (f:clos_exp->clos_exp) l.
     ALL (\p. match p with (num_args,e) -> P num_args)
         (MAP (\p. match p with (num_args,x) -> (num_args, f x)) l) <=>
     ALL (\p. match p with (num_args,e) -> P num_args) l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `h:num#clos_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `x:clos_exp` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[]);;

(* replace the condition of the first conditional of the target by that of *)
(* the source (proved equal by thl), so that both are split together       *)
let CLOSP2AUX_LETOP_SYNC_COND_TAC (thl:thm list) : tactic = fun (asl,w as gl) ->
  let cs = rand (rator (rator (find_term is_cond (lhand w)))) in
  let ct = rand (rator (rator (find_term is_cond (rand w)))) in
  if ct = cs then ALL_TAC gl else
  (SUBGOAL_THEN (mk_eq(ct,cs)) SUBST1_TAC THENL
    [ASM_REWRITE_TAC thl; ALL_TAC]) gl;;

let CLOSP2AUX_LETOP_RECC_TAC : tactic = fun (asl,w as gl) ->
  let is_recc t = CLOSPROPSAUX_is_app "list_of_seq" t &&
                  CLOSPROPSAUX_is_app "clos_Recclosure" (lhand t) in
  let t1 = find_term is_recc (lhand w) and t2 = find_term is_recc (rand w) in
  let env_of t = rand (rator (lhand t)) and fns_of t = rand (lhand t) in
  let e1 = env_of t1 and e2 = env_of t2 in
  let all2 = CLOSP2AUX_letop_env (map snd asl) e1 in
  if not (rand (concl all2) = e2) then failwith "CLOSP2AUX_LETOP_RECC_TAC" else
  let frel = ISPEC (fns_of t1) CLOSP2AUX_letop_f_rel_MAP in
  let loc = hd (snd (strip_comb (lhand t1))) and n = rand t1 in
  ASSUME_TAC (SPECL [loc; n] (MATCH_MP CLOSP2AUX_letop_recc_rel (CONJ all2 frel))) gl;;

let CLOSP2AUX_letop_state_rel_max_app = prove
 (`!(s:(C,FFI)clos_state) t. clos_letopProof_state_rel s t ==>
     clos_state_max_app t = clos_state_max_app s`,
  SIMP_TAC[clos_letopProof_state_rel_def]);;

let CLOSP2AUX_letop_letrec = prove
 (el 9 CLOSP2AUX_letop_cases,
  CLOSP2AUX_LETOP_INTRO_TAC THEN CLOSP2AUX_LETOP_TGT_TAC THEN CLOSP2AUX_LETOP_UNFOLD_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSP2AUX_letop_state_rel_max_app o
              check (CLOSPROPSAUX_is_app "clos_letopProof_state_rel" o concl)) THEN
  CLOSP2AUX_LETOP_SYNC_COND_TAC[CLOSP2AUX_letop_ALL_MAP] THEN
  COND_CASES_TAC THENL [ALL_TAC; CLOSP2AUX_LETOP_FIN_TAC] THEN
  REWRITE_TAC[LENGTH_MAP] THEN
  CASES_ON `namesopt:(num list)option` THEN CASE_REWRITE_TAC[] THENL
   [CLOSP2AUX_LETOP_RECC_TAC THEN
    REPEAT CLOSP2AUX_LETOP_STEP_TAC THEN CLOSP2AUX_LETOP_FIN_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:num list` o MATCH_MP CLOSP2AUX_letop_lookup_vars_cases o
              check (fun th -> concl th = `ALL2 clos_letopProof_v_rel env env2`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN BETA_TAC THENL
   [CLOSP2AUX_LETOP_FIN_TAC; ALL_TAC] THEN
  CLOSP2AUX_LETOP_RECC_TAC THEN
  REPEAT CLOSP2AUX_LETOP_STEP_TAC THEN CLOSP2AUX_LETOP_FIN_TAC);;

let CLOSP2AUX_letop_HD_rel = prove
 (`!sv tv x env (s:(C,FFI)clos_state) t.
     clos_evaluate ([x],env,s) = (Rval sv,t) /\ ALL2 clos_letopProof_v_rel sv tv ==>
     clos_letopProof_v_rel (HD sv) (HD tv)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o MATCH_MP clos_evaluate_SING) MP_TAC) THEN
  ASM_REWRITE_TAC[LIST_REL_CONS1; LIST_REL_NIL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[HD]);;

(* the relation of the heads of related singleton results *)
let CLOSP2AUX_LETOP_HD_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let evs = filter (fun th -> let c = concl th in
                     is_eq c && CLOSPROPSAUX_is_app "clos_evaluate" (lhs c)) asms in
  let res = flat (map (fun ev -> mapfilter (fun a ->
                    MATCH_MP CLOSP2AUX_letop_HD_rel (CONJ ev a)) asms) evs) in
  let res = filter (fun th -> not (exists (fun a -> concl a = concl th) asms)) res in
  MAP_EVERY ASSUME_TAC res gl;;

let CLOSP2AUX_letop_app = prove
 (el 10 CLOSP2AUX_letop_cases,
  CLOSP2AUX_LETOP_INTRO_TAC THEN CLOSP2AUX_LETOP_TGT_TAC THEN CLOSP2AUX_LETOP_UNFOLD_TAC THEN
  CLOSP2AUX_LETOP_SYNC_COND_TAC[clos_letop_LENGTH_let_op] THEN
  COND_CASES_TAC THENL [ALL_TAC; CLOSP2AUX_LETOP_FIN_TAC] THEN
  CLOSP2AUX_LETOP_STEP_TAC THENL
   [ALL_TAC; CLOSP2AUX_LETOP_FIN_TAC; CLOSP2AUX_LETOP_FIN_TAC] THEN
  CLOSP2AUX_LETOP_STEP_TAC THENL
   [ALL_TAC; CLOSP2AUX_LETOP_FIN_TAC; CLOSP2AUX_LETOP_FIN_TAC] THEN
  CLOSP2AUX_LETOP_HD_TAC THEN
  CLOSP2AUX_LETOP_STEP_TAC THEN CLOSP2AUX_LETOP_FIN_TAC);;

let CLOSP2AUX_letop_tick = prove
 (el 11 CLOSP2AUX_letop_cases,
  CLOSP2AUX_LETOP_INTRO_TAC THEN CLOSP2AUX_LETOP_TGT_TAC THEN CLOSP2AUX_LETOP_UNFOLD_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[SYM (MATCH_MP clos_letopProof_state_rel_clocks_eqs th)]) THEN
  COND_CASES_TAC THENL [CLOSP2AUX_LETOP_FIN_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP clos_letopProof_state_rel_dec_clock o
              check (CLOSPROPSAUX_is_app "clos_letopProof_state_rel" o concl)) THEN
  REPEAT CLOSP2AUX_LETOP_STEP_TAC THEN CLOSP2AUX_LETOP_FIN_TAC);;

let CLOSP2AUX_letop_call = prove
 (el 12 CLOSP2AUX_letop_cases,
  CLOSP2AUX_LETOP_INTRO_TAC THEN CLOSP2AUX_LETOP_TGT_TAC THEN CLOSP2AUX_LETOP_UNFOLD_TAC THEN
  CLOSP2AUX_LETOP_STEP_TAC THENL
   [ALL_TAC; CLOSP2AUX_LETOP_FIN_TAC; CLOSP2AUX_LETOP_FIN_TAC] THEN
  ASSUM_LIST(fun l -> REWRITE_TAC(flat (map (fun th ->
    let th' = REWRITE_RULE[clos_letopProof_state_rel_def] th in
    [CONJUNCT1 (CONJUNCT2 th'); CONJUNCT1 (CONJUNCT2 (CONJUNCT2 th'))])
    (filter (CLOSPROPSAUX_is_app "clos_letopProof_state_rel" o concl) l)))) THEN
  REWRITE_TAC[clos_find_code_def; FLOOKUP_EMPTY] THEN CASE_REWRITE_TAC[] THEN
  CLOSP2AUX_LETOP_FIN_TAC);;

let CLOSP2AUX_letop_app_nil = prove
 (el 13 CLOSP2AUX_letop_cases,
  CLOSP2AUX_LETOP_INTRO_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOSPROPSAUX_is_app "ALL2" (concl th) &&
                                lhand (concl th) = `[]:clos_v list`)) THEN
  REWRITE_TAC[LIST_REL_NIL] THEN DISCH_THEN SUBST1_TAC THEN
  CLOSP2AUX_LETOP_UNFOLD_TAC THEN REWRITE_TAC[evaluate_app_NIL] THEN
  CLOSP2AUX_LETOP_FIN_TAC);;

(* local helpers for the evaluate_app case *)
let CLOSP2AUX_letop_state_rel_dec_clock_n = prove
 (`!n (s1:(C,FFI)clos_state) s2. clos_letopProof_state_rel s1 s2 ==>
     clos_letopProof_state_rel (clos_dec_clock n s1) (clos_dec_clock n s2)`,
  SIMP_TAC[clos_letopProof_state_rel_def; clos_dec_clock_def; clos_state_INFO.ri_accfupds;
           K_THM]);;

let CLOSP2AUX_letop_state_rel_with_clock = prove
 (`!k (s1:(C,FFI)clos_state) s2. clos_letopProof_state_rel s1 s2 ==>
     clos_letopProof_state_rel (clos_state_clock_fupd (K k) s1)
                               (clos_state_clock_fupd (K k) s2)`,
  SIMP_TAC[clos_letopProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM]);;

let CLOSP2AUX_LETOP_CLOCK_SYNC_TAC : tactic =
  ASSUM_LIST(fun l -> REWRITE_TAC(map (SYM o MATCH_MP clos_letopProof_state_rel_clocks_eqs)
    (filter (CLOSPROPSAUX_is_app "clos_letopProof_state_rel" o concl) l)));;

let CLOSP2AUX_LETOP_APP_FIN_TAC : tactic =
  CLOSP2AUX_LETOP_FIN_TAC THEN
  ASM_SIMP_TAC[CLOSP2AUX_letop_state_rel_with_clock; CLOSP2AUX_letop_state_rel_dec_clock_n];;

let CLOSP2AUX_letop_app_cons = prove
 (el 14 CLOSP2AUX_letop_cases,
  CLOSP2AUX_LETOP_INTRO_TAC THEN
  FIRST_X_ASSUM(fun th -> if CLOSPROPSAUX_is_app "ALL2" (concl th) &&
                             is_cons (lhand (concl th))
                          then ASSUME_TAC (SYM (MATCH_MP LIST_REL_LENGTH th)) THEN MP_TAC th
                          else NO_TAC) THEN
  REWRITE_TAC[LIST_REL_CONS1] THEN STRIP_TAC THEN RVEQ_TAC THEN
  CLOSP2AUX_LETOP_UNFOLD_TAC THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP CLOSP2AUX_letop_state_rel_max_app th]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`clos_state_max_app (s:(C,FFI)clos_state)`; `loc_opt:num option`;
                 `f:clos_v`; `f2:clos_v`; `CONS (v4:clos_v) v5`; `CONS (h':clos_v) t'`]
                CLOSP2AUX_letop_dest_closure_cases) THEN
  ASM_REWRITE_TAC[ALL2] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [CLOSP2AUX_LETOP_FIN_TAC;
    CLOSP2AUX_LETOP_CLOCK_SYNC_TAC THEN COND_CASES_TAC THEN CLOSP2AUX_LETOP_APP_FIN_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if concl th = `ALL2 clos_letopProof_v_rel rest1 rest2`
                        then REWRITE_TAC[SYM (MATCH_MP LIST_REL_LENGTH th)] else NO_TAC) THEN
  CLOSP2AUX_LETOP_CLOCK_SYNC_TAC THEN
  ASM_CASES_TAC `clos_state_clock (s:(C,FFI)clos_state) <
                 LENGTH (CONS (v4:clos_v) v5) - LENGTH (rest1:clos_v list)` THEN
  ASM_REWRITE_TAC[] THENL [CLOSP2AUX_LETOP_APP_FIN_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `LENGTH (CONS (v4:clos_v) v5) - LENGTH (rest1:clos_v list)` o
              MATCH_MP CLOSP2AUX_letop_state_rel_dec_clock_n o
              check (fun th -> concl th = `clos_letopProof_state_rel (s:(C,FFI)clos_state) t1`)) THEN
  CLOSP2AUX_LETOP_STEP_TAC THENL
   [ALL_TAC; CLOSP2AUX_LETOP_FIN_TAC; CLOSP2AUX_LETOP_FIN_TAC] THEN
  CLOSP2AUX_LETOP_SING_TAC THEN CASE_REWRITE_TAC[] THEN
  CLOSP2AUX_LETOP_STEP_TAC THEN CLOSP2AUX_LETOP_FIN_TAC);;

(* HOL4: evaluate_let_op *)
let clos_letopProof_evaluate_let_op = prove
 (`(!xs env1 (s1:(C,FFI)clos_state) res1 s2 ys env2 t1.
      clos_evaluate (xs,env1,s1) = (res1,s2) /\
      ALL2 clos_letopProof_v_rel env1 env2 /\ clos_letopProof_state_rel s1 t1 /\
      clos_letopProof_code_rel xs ys ==>
      ?res2 t2.
        clos_evaluate (ys,env2,t1) = (res2,t2) /\
        result_rel (ALL2 clos_letopProof_v_rel) clos_letopProof_v_rel res1 res2 /\
        clos_letopProof_state_rel s2 t2) /\
   (!loc_opt f1 args1 (s1:(C,FFI)clos_state) res1 s2 f2 args2 t1.
      evaluate_app loc_opt f1 args1 s1 = (res1,s2) /\
      clos_letopProof_v_rel f1 f2 /\ ALL2 clos_letopProof_v_rel args1 args2 /\
      clos_letopProof_state_rel s1 t1 ==>
      ?res2 t2.
        evaluate_app loc_opt f2 args2 t1 = (res2,t2) /\
        result_rel (ALL2 clos_letopProof_v_rel) clos_letopProof_v_rel res1 res2 /\
        clos_letopProof_state_rel s2 t2)`,
  let th = MATCH_MP CLOSP2AUX_letop_ind
             (end_itlist CONJ
                [CLOSP2AUX_letop_nil; CLOSP2AUX_letop_cons; CLOSP2AUX_letop_var;
                 CLOSP2AUX_letop_if; CLOSP2AUX_letop_let; CLOSP2AUX_letop_raise;
                 CLOSP2AUX_letop_handle; CLOSP2AUX_letop_op; CLOSP2AUX_letop_fn;
                 CLOSP2AUX_letop_letrec; CLOSP2AUX_letop_app; CLOSP2AUX_letop_tick;
                 CLOSP2AUX_letop_call; CLOSP2AUX_letop_app_nil; CLOSP2AUX_letop_app_cons]) in
  CONJ_TAC THENL [MATCH_ACCEPT_TAC (CONJUNCT1 th); MATCH_ACCEPT_TAC (CONJUNCT2 th)]);;

(* HOL4: let_op_correct *)
let let_op_correct = prove
 (`!xs env1 (s1:(C,FFI)clos_state) res1 s2 env2 t1.
     clos_evaluate (xs,env1,s1) = (res1,s2) /\
     ALL2 clos_letopProof_v_rel env1 env2 /\ clos_letopProof_state_rel s1 t1 ==>
     ?res2 t2.
       clos_evaluate (clos_letop_let_op xs,env2,t1) = (res2,t2) /\
       result_rel (ALL2 clos_letopProof_v_rel) clos_letopProof_v_rel res1 res2 /\
       clos_letopProof_state_rel s2 t2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (CONJUNCT1 clos_letopProof_evaluate_let_op) THEN
  MAP_EVERY EXISTS_TAC [`xs:clos_exp list`; `env1:clos_v list`;
                        `s1:(C,FFI)clos_state`] THEN
  ASM_REWRITE_TAC[clos_letopProof_code_rel_def]);;

(* preservation of observational semantics *)

(* a local helper: related results have the same shape *)
let CLOSP2AUX_letop_result_shape = prove
 (`!(R1:A->B->bool) (R2:C->D->bool) x y.
     result_rel R1 R2 x y ==>
     result_rel (\(a:A) (b:B). T) (\(a:C) (b:D). T) x y`,
  REPEAT GEN_TAC THEN CASES_ON `x:(A,C)result` THEN CASES_ON `y:(B,D)result` THEN
  REWRITE_TAC[result_rel_def] THEN
  CASES_ON `a:(C)error_result` THEN CASES_ON `a':(D)error_result` THEN
  REWRITE_TAC[exc_rel_def] THEN MESON_TAC[]);;

(* HOL4: semantics_let_op *)
let semantics_let_op = prove
 (`~(clos_semantics (ffi:(FFI)ffi_state) max_app FEMPTY (co:num -> C # clos_prog)
       (pure_cc (clos_letop_compile_inc:clos_prog->clos_prog) cc) xs = Fail) ==>
   (!n. SND (SND (co n)) = []) /\ 1 <= max_app ==>
   clos_semantics ffi max_app FEMPTY
     (pure_co (clos_letop_compile_inc:clos_prog->clos_prog) o co) cc
     (clos_letop_let_op xs) =
   clos_semantics ffi max_app FEMPTY co
     (pure_cc (clos_letop_compile_inc:clos_prog->clos_prog) cc) xs`,
  DISCH_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] clos_IMP_semantics_eq) THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `\(c1:(num,num#clos_exp)fmap) (o1:num->C#clos_prog)
                (k1:C->clos_prog->(byte list # int64 list # C)option) (e1:clos_exp list)
                (c2:(num,num#clos_exp)fmap) (o2:num->C#clos_prog)
                (k2:C->clos_prog->(byte list # int64 list # C)option) (e2:clos_exp list). T` THEN
  REWRITE_TAC[clos_eval_sim_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`xs:clos_exp list`; `[]:clos_v list`;
                 `clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY
                    (co:num -> C # clos_prog)
                    (pure_cc (clos_letop_compile_inc:clos_prog->clos_prog) cc) k`;
                 `res1:(clos_v list,clos_v)result`; `s2:(C,FFI)clos_state`;
                 `[]:clos_v list`;
                 `clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY
                    (pure_co (clos_letop_compile_inc:clos_prog->clos_prog) o
                     (co:num -> C # clos_prog)) cc k`]
                let_op_correct) THEN
  ASM_REWRITE_TAC[ALL2] THEN ANTS_TAC THENL
   [REWRITE_TAC[clos_letopProof_state_rel_def; clos_initial_state_def;
                clos_state_INFO.ri_accessors; ALL2; clos_letopProof_FMAP_REL_def;
                FLOOKUP_EMPTY; distinctness "option"] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP CLOSP2AUX_letop_result_shape);
    RULE_ASSUM_TAC(REWRITE_RULE[clos_letopProof_state_rel_def]) THEN ASM_REWRITE_TAC[]]);;

(* syntactic properties *)

(* a local helper: the properties of a list of variables *)
let CLOSP2AUX_letop_var_list_props = prove
 (`!n ys0 (zs:A list).
     clos_letop_var_list n ys0 zs ==>
     code_locs ys0 = [] /\ every_Fn_SOME ys0 /\ every_Fn_vs_NONE ys0 /\
     (!m. ALL (obeys_max_app m) ys0) /\ ALL no_Labels ys0 /\
     (!x. app_call_dests x ys0 = {}) /\
     UNIONS (set_of_list (MAP clos_get_code_labels ys0)) = {}`,
  MATCH_MP_TAC clos_letop_var_list_ind THEN
  REWRITE_TAC[clos_letop_var_list_def; code_locs_def; every_Fn_SOME_def;
              every_Fn_vs_NONE_def; app_call_dests_def; ALL; MAP; set_of_list;
              UNIONS_0] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[code_locs_cons; CLOSPROPSAUX_every_Fn_SOME_cons;
                   CLOSPROPSAUX_every_Fn_vs_NONE_cons; app_call_dests_cons] THEN
  ASM_REWRITE_TAC[code_locs_def; every_Fn_SOME_def; every_Fn_vs_NONE_def;
                  app_call_dests_def; obeys_max_app_def; no_Labels_def;
                  clos_get_code_labels_def; UNIONS_INSERT; APPEND; UNION_EMPTY]);;

(* HOL4: var_list_IMP_code_locs [local] *)
let var_list_IMP_code_locs = prove
 (`!k l (x:A list). clos_letop_var_list k l x ==> code_locs l = []`,
  MESON_TAC[CLOSP2AUX_letop_var_list_props]);;

let CLOSP2AUX_letop_sing_Var = prove
 (`!h tr k. clos_letop_let_op_sing h = clos_Var tr k ==> h = clos_Var tr k`,
  GEN_TAC THEN CASES_ON `h:clos_exp` THEN
  REWRITE_TAC[clos_letop_let_op_sing_def; LET_DEF; LET_END_DEF;
              distinctness "clos_exp"] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  TRY (CASES_ON `clos_letop_dest_op (clos_letop_let_op_sing a2)
                   (clos_letop_let_op_list a1)` THEN CASE_REWRITE_TAC[]) THEN
  REWRITE_TAC[distinctness "clos_exp"]);;

let CLOSP2AUX_letop_let_op_CONS = prove
 (`!t h. clos_letop_let_op (CONS h t) =
         CONS (HD (clos_letop_let_op [h])) (clos_letop_let_op t)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  REWRITE_TAC[clos_letop_let_op_def; HD_let_op_SING]);;

(* HOL4: var_list_let_op_IMP_code_locs [local] *)
let var_list_let_op_IMP_code_locs = prove
 (`!k l (x:A list). clos_letop_var_list k (clos_letop_let_op l) x ==> code_locs l = []`,
  GEN_TAC THEN GEN_TAC THEN SPEC_TAC(`k:num`,`k:num`) THEN
  SPEC_TAC(`l:clos_exp list`,`l:clos_exp list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[code_locs_def] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CLOSP2AUX_letop_let_op_CONS; CONJUNCT1 clos_letop_let_op_sing_eq; HD] THEN
  STRUCT_CASES_TAC(ISPEC `x:A list` list_CASES) THEN
  REWRITE_TAC[clos_letop_var_list_def] THEN
  CASES_ON `clos_letop_let_op_sing h` THEN ASM_REWRITE_TAC[clos_letop_var_list_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP CLOSP2AUX_letop_sing_Var o
    check (fun th -> is_eq (concl th) &&
                     CLOSPROPSAUX_is_app "clos_letop_let_op_sing" (lhs (concl th)))) THEN
  ONCE_REWRITE_TAC[code_locs_cons] THEN REWRITE_TAC[code_locs_def; APPEND] THEN
  ASM_MESON_TAC[]);;

let CLOSP2AUX_letop_syn_defs =
  [code_locs_def; every_Fn_SOME_def; every_Fn_vs_NONE_def; obeys_max_app_def;
   no_Labels_def; app_call_dests_def; clos_get_code_labels_def; o_THM;
   LET_DEF; LET_END_DEF; MAP; LENGTH; ALL];;

let CLOSP2AUX_LETOP_SYN_GEN_TAC : tactic =
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[clos_letop_let_op_sing_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  ASM_REWRITE_TAC CLOSP2AUX_letop_syn_defs THEN
  ONCE_REWRITE_TAC[code_locs_cons; CLOSPROPSAUX_every_Fn_SOME_cons;
                   CLOSPROPSAUX_every_Fn_vs_NONE_cons; app_call_dests_cons] THEN
  ASM_REWRITE_TAC[];;

let CLOSP2AUX_LETOP_SYN_LET_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihx2") ASSUME_TAC) THEN
  REWRITE_TAC[clos_letop_let_op_sing_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  CASES_ON `clos_letop_dest_op (clos_letop_let_op_sing x2) (clos_letop_let_op_list xs)` THEN
  CASE_REWRITE_TAC[] THENL
   [REMOVE_THEN "ihx2" ASSUME_TAC THEN ASM_REWRITE_TAC CLOSP2AUX_letop_syn_defs;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP dest_op_SOME_IMP o
    check (fun th -> is_eq (concl th) &&
                     CLOSPROPSAUX_is_app "clos_letop_dest_op" (lhs (concl th)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSP2AUX_letop_var_list_props o
    check (CLOSPROPSAUX_is_app "clos_letop_var_list" o concl)) THEN
  REWRITE_TAC CLOSP2AUX_letop_syn_defs THEN BETA_TAC THEN
  REMOVE_THEN "ihx2" (fun ih -> REWRITE_TAC (map GSYM (CONJUNCTS ih))) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC (CLOSP2AUX_letop_syn_defs @ [UNION_EMPTY; APPEND_NIL; CONJ_ACI]);;

let CLOSP2AUX_letop_syn = prove
 (`(!e. code_locs [clos_letop_let_op_sing e] = code_locs [e] /\
        (every_Fn_SOME [clos_letop_let_op_sing e] <=> every_Fn_SOME [e]) /\
        (every_Fn_vs_NONE [clos_letop_let_op_sing e] <=> every_Fn_vs_NONE [e]) /\
        (!m. obeys_max_app m (clos_letop_let_op_sing e) <=> obeys_max_app m e) /\
        (no_Labels (clos_letop_let_op_sing e) <=> no_Labels e) /\
        (!x. app_call_dests x [clos_letop_let_op_sing e] = app_call_dests x [e]) /\
        clos_get_code_labels (clos_letop_let_op_sing e) = clos_get_code_labels e) /\
   (!es. code_locs (clos_letop_let_op_list es) = code_locs es /\
         (every_Fn_SOME (clos_letop_let_op_list es) <=> every_Fn_SOME es) /\
         (every_Fn_vs_NONE (clos_letop_let_op_list es) <=> every_Fn_vs_NONE es) /\
         (!m. ALL (obeys_max_app m) (clos_letop_let_op_list es) <=>
              ALL (obeys_max_app m) es) /\
         (ALL no_Labels (clos_letop_let_op_list es) <=> ALL no_Labels es) /\
         (!x. app_call_dests x (clos_letop_let_op_list es) = app_call_dests x es) /\
         MAP clos_get_code_labels (clos_letop_let_op_list es) =
         MAP clos_get_code_labels es /\
         LENGTH (clos_letop_let_op_list es) = LENGTH es) /\
   (!fns. code_locs (MAP SND (let_op_let fns)) = code_locs (MAP SND fns) /\
          (every_Fn_SOME (MAP SND (let_op_let fns)) <=> every_Fn_SOME (MAP SND fns)) /\
          (every_Fn_vs_NONE (MAP SND (let_op_let fns)) <=>
           every_Fn_vs_NONE (MAP SND fns)) /\
          (!m. ALL (obeys_max_app m) (MAP SND (let_op_let fns)) <=>
               ALL (obeys_max_app m) (MAP SND fns)) /\
          (ALL no_Labels (MAP SND (let_op_let fns)) <=> ALL no_Labels (MAP SND fns)) /\
          (!x. app_call_dests x (MAP SND (let_op_let fns)) =
               app_call_dests x (MAP SND fns)) /\
          MAP (clos_get_code_labels o SND) (let_op_let fns) =
          MAP (clos_get_code_labels o SND) fns /\
          LENGTH (let_op_let fns) = LENGTH fns)`,
  MATCH_MP_TAC clos_letop_let_op_sing_ind THEN REPEAT CONJ_TAC THEN
  (fun (asl,w as gl) ->
     if can (find_term (fun t -> is_const t && fst(dest_const t) = "clos_Let")) w
     then CLOSP2AUX_LETOP_SYN_LET_TAC gl else CLOSP2AUX_LETOP_SYN_GEN_TAC gl));;

let CLOSP2AUX_letop_list = CONJUNCT1 (CONJUNCT2 clos_letop_let_op_sing_eq);;

(* HOL4: code_locs_let_op *)
let code_locs_let_op = prove
 (`!xs. code_locs (clos_letop_let_op xs) = code_locs xs`,
  REWRITE_TAC[CLOSP2AUX_letop_list; CLOSP2AUX_letop_syn]);;

(* HOL4: let_op_every_Fn_SOME [simp] *)
let let_op_every_Fn_SOME = prove
 (`!es. every_Fn_SOME (clos_letop_let_op es) <=> every_Fn_SOME es`,
  REWRITE_TAC[CLOSP2AUX_letop_list; CLOSP2AUX_letop_syn]);;
let _ = cake_add_simps [let_op_every_Fn_SOME];;

(* HOL4: let_op_every_Fn_vs_NONE [simp] *)
let let_op_every_Fn_vs_NONE = prove
 (`!es. every_Fn_vs_NONE (clos_letop_let_op es) <=> every_Fn_vs_NONE es`,
  REWRITE_TAC[CLOSP2AUX_letop_list; CLOSP2AUX_letop_syn]);;
let _ = cake_add_simps [let_op_every_Fn_vs_NONE];;

(* HOL4: EVERY_let_op_sing *)
let EVERY_let_op_sing = prove
 (`ALL f (clos_letop_let_op [x]) <=> f (HD (clos_letop_let_op [x]))`,
  REWRITE_TAC[CONJUNCT1 clos_letop_let_op_sing_eq; HD; ALL]);;

(* HOL4: var_list_no_Labels *)
let var_list_no_Labels = prove
 (`!n l (m:A list). clos_letop_var_list n l m ==>
     ALL no_Labels l /\ ALL (obeys_max_app k) l`,
  MESON_TAC[CLOSP2AUX_letop_var_list_props]);;

(* HOL4: let_op_obeys_max_app *)
let let_op_obeys_max_app = prove
 (`!es. ALL (obeys_max_app k) (clos_letop_let_op es) <=> ALL (obeys_max_app k) es`,
  REWRITE_TAC[CLOSP2AUX_letop_list; CLOSP2AUX_letop_syn]);;

(* HOL4: let_op_no_Labels *)
let let_op_no_Labels = prove
 (`!es. ALL no_Labels (clos_letop_let_op es) <=> ALL no_Labels es`,
  REWRITE_TAC[CLOSP2AUX_letop_list; CLOSP2AUX_letop_syn]);;

(* HOL4: var_list_app_call_dests *)
let var_list_app_call_dests = prove
 (`!x y (z:A list). clos_letop_var_list x y z ==> app_call_dests a y = {}`,
  MESON_TAC[CLOSP2AUX_letop_var_list_props]);;

(* HOL4: let_op_app_call_dests [simp] *)
let let_op_app_call_dests = prove
 (`!es. app_call_dests x (clos_letop_let_op es) = app_call_dests x es`,
  REWRITE_TAC[CLOSP2AUX_letop_list; CLOSP2AUX_letop_syn]);;
let _ = cake_add_simps [let_op_app_call_dests];;

(* HOL4: var_list_code_labels_imp *)
let clos_letopProof_var_list_code_labels_imp = prove
 (`!n x (y:A list). clos_letop_var_list n x y ==>
     UNIONS (set_of_list (MAP clos_get_code_labels x)) = {}`,
  MESON_TAC[CLOSP2AUX_letop_var_list_props]);;

(* HOL4: let_op_get_code_labels [simp] *)
let let_op_get_code_labels = prove
 (`!es. MAP clos_get_code_labels (clos_letop_let_op es) = MAP clos_get_code_labels es`,
  REWRITE_TAC[CLOSP2AUX_letop_list; CLOSP2AUX_letop_syn]);;
let _ = cake_add_simps [let_op_get_code_labels];;
