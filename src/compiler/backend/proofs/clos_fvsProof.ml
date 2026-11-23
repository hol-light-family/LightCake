(* ========================================================================= *)
(* clos_fvsProof: port of HOL4 compiler/backend/proofs/                      *)
(* clos_fvsProofScript.sml (CakeML v3479).                                   *)
(* Correctness proof for clos_fvs.                                           *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_fvs.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/backendProps.ml";;

type_invention_error := true;;

(* HOL4: LENGTH_remove_fvs *)
let clos_fvsProof_LENGTH_remove_fvs = prove
 (`!fvs xs. LENGTH (remove_fvs fvs xs) = LENGTH xs`,
  REWRITE_TAC[clos_fvs_LENGTH_remove_fvs]);;

let remove_fvs_SING = prove
 (`!x. ?y. remove_fvs fvs [x] = [y]`,
  REWRITE_TAC[CONJUNCT1 remove_fvs_sing_eq; CONS_11] THEN MESON_TAC[]);;

let HD_remove_fvs_SING = prove
 (`!x. [HD (remove_fvs fvs [x])] = remove_fvs fvs [x]`,
  REWRITE_TAC[CONJUNCT1 remove_fvs_sing_eq; HD]);;
let _ = cake_add_simps [HD_remove_fvs_SING];;

let EVERY_remove_fvs_SING = prove
 (`ALL P (remove_fvs fvs [x]) <=> P (HD (remove_fvs fvs [x]))`,
  REWRITE_TAC[CONJUNCT1 remove_fvs_sing_eq; HD; ALL]);;

(* HOL4: code_rel *)
let clos_fvsProof_code_rel_def = cake_def
  `clos_fvsProof_code_rel fvs e1 e2 <=> e2 = remove_fvs fvs e1`;;

(* HOL4: code_rel_IMP_LENGTH *)
let clos_fvsProof_code_rel_IMP_LENGTH = prove
 (`!xs ys. clos_fvsProof_code_rel fvs xs ys ==> LENGTH xs = LENGTH ys`,
  SIMP_TAC[clos_fvsProof_code_rel_def; clos_fvs_LENGTH_remove_fvs]);;

(* HOL4: code_rel_CONS_CONS *)
let clos_fvsProof_code_rel_CONS_CONS = prove
 (`clos_fvsProof_code_rel fvs (CONS x1 (CONS x2 xs)) (CONS y1 (CONS y2 ys)) ==>
   clos_fvsProof_code_rel fvs [x1] [y1] /\
   clos_fvsProof_code_rel fvs (CONS x2 xs) (CONS y2 ys)`,
  REWRITE_TAC[clos_fvsProof_code_rel_def; remove_fvs_def; CONS_11] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[HD_remove_fvs_SING]);;

(* value relation *)

(* HOL4: f_rel *)
let clos_fvsProof_f_rel_def = cake_def
  `clos_fvsProof_f_rel fvs ((a1:num),(e1:clos_exp)) (a2,e2) <=>
     a1 = a2 /\ clos_fvsProof_code_rel (a1 + fvs) [e1] [e2]`;;

(* HOL4: v_rel (funs1 and funs2 of the last rule, free in HOL4, are bound) *)
let clos_fvsProof_v_rel_rules,clos_fvsProof_v_rel_ind,
    clos_fvsProof_v_rel_cases,clos_fvsProof_v_rel_strongind =
  cake_inductive
  `(!i. clos_fvsProof_v_rel (clos_Number i) (clos_Number i)) /\
   (!w. clos_fvsProof_v_rel (clos_Word64 w) (clos_Word64 w)) /\
   (!w. clos_fvsProof_v_rel (ByteVector w) (ByteVector w)) /\
   (!n b. clos_fvsProof_v_rel (clos_RefPtr b n) (clos_RefPtr b n)) /\
   (!tag xs ys.
      ALL2 clos_fvsProof_v_rel xs ys ==>
      clos_fvsProof_v_rel (clos_Block tag xs) (clos_Block tag ys)) /\
   (!loc args1 args2 env1 env2 num_args e1 e2.
      ALL2 clos_fvsProof_v_rel env1 env2 /\
      ALL2 clos_fvsProof_v_rel args1 args2 /\
      clos_fvsProof_code_rel (LENGTH env1 + num_args) [e1] [e2] ==>
      clos_fvsProof_v_rel (clos_Closure loc args1 env1 num_args e1)
                          (clos_Closure loc args2 env2 num_args e2)) /\
   (!loc args1 args2 env1 env2 funs1 funs2 k.
      ALL2 clos_fvsProof_v_rel env1 env2 /\
      ALL2 clos_fvsProof_v_rel args1 args2 /\
      ALL2 (clos_fvsProof_f_rel (LENGTH env1 + LENGTH funs1)) funs1 funs2 ==>
      clos_fvsProof_v_rel (clos_Recclosure loc args1 env1 funs1 k)
                          (clos_Recclosure loc args2 env2 funs2 k))`;;

(* HOL4: v_rel_simps (HOL4 computes it with SIMP_CONV from v_rel_cases) *)
let clos_fvsProof_v_rel_simps = prove
 (`(!n x. clos_fvsProof_v_rel (clos_Number n) x <=> x = clos_Number n) /\
   (!n p x. clos_fvsProof_v_rel (clos_Block n p) x <=>
            ?ys. x = clos_Block n ys /\ ALL2 clos_fvsProof_v_rel p ys) /\
   (!p x. clos_fvsProof_v_rel (clos_Word64 p) x <=> x = clos_Word64 p) /\
   (!p x. clos_fvsProof_v_rel (ByteVector p) x <=> x = ByteVector p) /\
   (!b p x. clos_fvsProof_v_rel (clos_RefPtr b p) x <=> x = clos_RefPtr b p) /\
   (!x1 x2 x3 x4 x5 x.
      clos_fvsProof_v_rel (clos_Closure x1 x2 x3 x4 x5) x <=>
      ?args2 env2 e2.
        x = clos_Closure x1 args2 env2 x4 e2 /\
        ALL2 clos_fvsProof_v_rel x3 env2 /\ ALL2 clos_fvsProof_v_rel x2 args2 /\
        clos_fvsProof_code_rel (LENGTH x3 + x4) [x5] [e2]) /\
   (!y1 y2 y3 y4 y5 x.
      clos_fvsProof_v_rel (clos_Recclosure y1 y2 y3 y4 y5) x <=>
      ?args2 env2 funs2.
        x = clos_Recclosure y1 args2 env2 funs2 y5 /\
        ALL2 clos_fvsProof_v_rel y3 env2 /\ ALL2 clos_fvsProof_v_rel y2 args2 /\
        ALL2 (clos_fvsProof_f_rel (LENGTH y3 + LENGTH y4)) y4 funs2) /\
   (!b x. clos_fvsProof_v_rel (clos_Boolv b) x <=> x = clos_Boolv b) /\
   (!x. clos_fvsProof_v_rel clos_Unit x <=> x = clos_Unit)`,
  REWRITE_TAC[clos_Boolv_def; clos_Unit_def] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_fvsProof_v_rel_cases] THEN
  REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"; GSYM CONJ_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[LIST_REL_NIL] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[]);;
let _ = cake_add_simps [clos_fvsProof_v_rel_simps];;

(* state relation *)

(* HOL4: ref_rel *)
let clos_fvsProof_ref_rel_rules,clos_fvsProof_ref_rel_ind,
    clos_fvsProof_ref_rel_cases,clos_fvsProof_ref_rel_strongind =
  cake_inductive
  `(!bs. clos_fvsProof_ref_rel (clos_ByteArray bs) (clos_ByteArray bs)) /\
   (!xs ys.
      ALL2 clos_fvsProof_v_rel xs ys ==>
      clos_fvsProof_ref_rel (clos_ValueArray xs) (clos_ValueArray ys)) /\
   (!m v w.
      clos_fvsProof_v_rel v w ==>
      clos_fvsProof_ref_rel (clos_Thunk m v) (clos_Thunk m w))`;;

(* HOL4: state_rel *)
let clos_fvsProof_state_rel_def = cake_def
  `clos_fvsProof_state_rel (s:(C,FFI)clos_state) (t:(C,FFI)clos_state) <=>
     (!n. SND (SND (clos_state_compile_oracle s n)) = []) /\
     clos_state_code s = FEMPTY /\ clos_state_code t = FEMPTY /\
     clos_state_max_app t = clos_state_max_app s /\ 1 <= clos_state_max_app s /\
     clos_state_clock t = clos_state_clock s /\
     clos_state_ffi t = clos_state_ffi s /\
     ALL2 (OPTREL clos_fvsProof_v_rel) (clos_state_globals s) (clos_state_globals t) /\
     fmap_rel clos_fvsProof_ref_rel (clos_state_refs s) (clos_state_refs t) /\
     clos_state_compile s = pure_cc clos_fvs_compile_inc (clos_state_compile t) /\
     clos_state_compile_oracle t =
       pure_co clos_fvs_compile_inc o clos_state_compile_oracle s`;;

(* a local helper: v_rel is a simple value relation (HOL4 proves it inline  *)
(* in do_app_lemma with simple_val_rel_def and v_rel_cases)                 *)
let CLOSP1AUX_fvs_simple_val_rel = prove
 (`clos_simple_val_rel clos_fvsProof_v_rel`,
  REWRITE_TAC[clos_simple_val_rel_def; isClos_cases] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [clos_fvsProof_v_rel_cases] THEN
  REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"] THEN MESON_TAC[]);;

let clos_fvsProof_v_rel_IMP_v_to_bytes_lemma = prove
 (`!x y.
     clos_fvsProof_v_rel x y ==>
     !ns:byte list.
       clos_v_to_list x = SOME (MAP (clos_Number o int_of_num o val) ns) <=>
       clos_v_to_list y = SOME (MAP (clos_Number o int_of_num o val) ns)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_ASSOC] THEN ONCE_REWRITE_TAC[MAP_o] THEN
  MP_TAC(MATCH_MP v_rel_to_list_byte1 CLOSP1AUX_fvs_simple_val_rel) THEN
  DISCH_THEN(MP_TAC o SPECL [`y:clos_v`; `x:clos_v`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let clos_fvsProof_v_rel_IMP_v_to_bytes = prove
 (`clos_fvsProof_v_rel x y ==> clos_v_to_bytes y = clos_v_to_bytes x`,
  MESON_TAC[clos_simple_val_rel_v_to_bytes; CLOSP1AUX_fvs_simple_val_rel]);;

let clos_fvsProof_v_rel_IMP_v_to_words_lemma = prove
 (`!x y.
     clos_fvsProof_v_rel x y ==>
     !ns. clos_v_to_list x = SOME (MAP clos_Word64 ns) <=>
          clos_v_to_list y = SOME (MAP clos_Word64 ns)`,
  MATCH_MP_TAC clos_v_to_list_ind THEN RW[] THEN FS[clos_v_to_list_def] THEN
  ASM_CASES_TAC `tag = cons_tag` THEN FS[] THEN RES_TAC THEN FS[case_eq "option"] THEN
  QCASES_ON "ns" THEN FS[] THEN EQ_TAC THEN RW[] THEN FS[] THEN QCASES_ON "h" THEN FS[]);;

let clos_fvsProof_v_rel_IMP_v_to_words = prove
 (`clos_fvsProof_v_rel x y ==> clos_v_to_words y = clos_v_to_words x`,
  MESON_TAC[clos_simple_val_rel_v_to_words; CLOSP1AUX_fvs_simple_val_rel]);;

(* HOL4: lookup_vars_lemma *)
let clos_fvsProof_lookup_vars_lemma = prove
 (CASE_TERM
  `!vs env1 env2.
     ALL2 clos_fvsProof_v_rel env1 env2 ==>
     match lookup_vars vs env1 with
       NONE -> lookup_vars vs env2 = NONE
     | SOME l1 -> ?l2. ALL2 clos_fvsProof_v_rel l1 l2 /\ lookup_vars vs env2 = SOME l2`,
  LIST_INDUCT_TAC THEN FS[lookup_vars_def] THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC LIST_REL_LENGTH THEN RW[] THEN RES_TAC THEN
  QCASES_ON "lookup_vars t env1" THEN FS[] THEN FS[LIST_REL_EL_EQN]);;

(* HOL4: find_code_lemma *)
let clos_fvsProof_find_code_lemma = prove
 (`!s t p args.
     clos_fvsProof_state_rel (s:(C,FFI)clos_state) t ==>
     clos_find_code p (args:clos_v list) (clos_state_code s) = NONE /\
     clos_find_code p args (clos_state_code t) = NONE`,
  SIMP_TAC[clos_fvsProof_state_rel_def; clos_find_code_def; FLOOKUP_EMPTY] THEN
  REWRITE_TAC[case_def "option"]);;

(* HOL4: dest_closure_SOME_IMP *)
let clos_fvsProof_dest_closure_SOME_IMP = prove
 (`dest_closure max_app loc_opt f2 xs = SOME x ==>
   (?loc arg_env clo_env num_args e. f2 = clos_Closure loc arg_env clo_env num_args e) \/
   (?loc arg_env clo_env fns i. f2 = clos_Recclosure loc arg_env clo_env fns i)`,
  QCASES_ON "f2" THEN FS[dest_closure_def]);;

(* local helpers: f_rel elementwise and on the components of the pairs; *)
(* the functions of a Letrec and their remove_fvs images              *)
let CLOSP1AUX_f_rel_EL = GEN_ALL (ISPEC `clos_fvsProof_f_rel n` LIST_REL_EL_EQN);;

let CLOSP1AUX_f_rel_FST_SND = prove
 (`!n p1 p2. clos_fvsProof_f_rel n p1 p2 <=>
             FST p1 = FST p2 /\ clos_fvsProof_code_rel (FST p1 + n) [SND p1] [SND p2]`,
  REWRITE_TAC[FORALL_PAIR_THM; clos_fvsProof_f_rel_def; FST; SND]);;

let CLOSP1AUX_fvs_f_rel_MAP = prove
 (CASE_TERM `!n k fns.
     ALL2 (clos_fvsProof_f_rel (n + k)) fns
       (MAP (\p. match p with
                   (num_args,x) -> (num_args, HD (remove_fvs (num_args + k + n) [x])))
            fns)`,
  FS[CLOSP1AUX_f_rel_EL; CLOSP1AUX_f_rel_FST_SND; EL_MAP; pair_CASE_def;
     clos_fvsProof_code_rel_def; ADD_AC]);;

(* dest_closure on related closures and arguments: the closure cases, the  *)
(* conditions of dest_closure, then the related environments and code      *)
let CLOSP1AUX_DEST_CLOSURE_TAC : tactic =
  REPEAT GEN_TAC THEN QCASES_ON "f1" THEN REWRITE_TAC[clos_fvsProof_v_rel_simps] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN IMP_RES_TAC LIST_REL_LENGTH THEN
  GVS[dest_closure_def; pair_CASE_def; CLOSP1AUX_f_rel_EL; CLOSP1AUX_f_rel_FST_SND] THEN
  REPEAT COND_CASES_TAC THEN GVS[DE_MORGAN_THM; NOT_LE] THEN
  FS[LIST_REL_APPEND_EQ; LIST_REL_REVERSE_EQ; EVERY2_TAKE; EVERY2_DROP; LIST_REL_GENLIST;
     CLOSP1AUX_f_rel_EL; CLOSP1AUX_f_rel_FST_SND; clos_fvsProof_v_rel_simps; LENGTH_TAKE_EQ] THEN
  TRY (FS[clos_fvsProof_code_rel_def; ARITH_ss] THEN AP_THM_TAC THEN AP_TERM_TAC) THEN
  DECIDE_TAC;;

(* HOL4: dest_closure_SOME_Full_app *)
let clos_fvsProof_dest_closure_SOME_Full_app = prove
 (`clos_fvsProof_v_rel f1 f2 /\ clos_fvsProof_v_rel a1 a2 /\
   ALL2 clos_fvsProof_v_rel args1 args2 /\
   dest_closure max_app loc_opt f1 (CONS a1 args1) = SOME (Full_app exp1 env1 rest_args1) ==>
   ?exp2 env2 rest_args2.
     clos_fvsProof_code_rel (LENGTH env1) [exp1] [exp2] /\
     ALL2 clos_fvsProof_v_rel env1 env2 /\
     ALL2 clos_fvsProof_v_rel rest_args1 rest_args2 /\
     dest_closure max_app loc_opt f2 (CONS a2 args2) = SOME (Full_app exp2 env2 rest_args2)`,
  CLOSP1AUX_DEST_CLOSURE_TAC);;

(* a local helper: the NONE and Partial_app cases (inline in HOL4's proof   *)
(* of evaluate_remove_fvs)                                                 *)
let CLOSP1AUX_dest_closure_NONE_Partial = prove
 (`(!f1 f2 args1 args2.
      clos_fvsProof_v_rel f1 f2 /\ ALL2 clos_fvsProof_v_rel args1 args2 ==>
      dest_closure max_app loc_opt f1 args1 = NONE ==>
      dest_closure max_app loc_opt f2 args2 = NONE) /\
   (!f1 f2 args1 args2 v.
      clos_fvsProof_v_rel f1 f2 /\ ALL2 clos_fvsProof_v_rel args1 args2 ==>
      dest_closure max_app loc_opt f1 args1 = SOME (Partial_app v) ==>
      ?w. dest_closure max_app loc_opt f2 args2 = SOME (Partial_app w) /\
          clos_fvsProof_v_rel v w)`,
  CONJ_TAC THEN CLOSP1AUX_DEST_CLOSURE_TAC);;

(* HOL4: simple_state_rel [local] *)
let clos_fvsProof_simple_state_rel = prove
 (`clos_simple_state_rel clos_fvsProof_v_rel
     (clos_fvsProof_state_rel:(C,FFI)clos_state->(C,FFI)clos_state->bool)`,
  FS[clos_simple_state_rel_def; clos_fvsProof_state_rel_def] THEN RW[] THEN
  FS[fmap_rel_def; FLOOKUP_DEF] THEN RFS[] THEN
  TRY (FIRST_X_ASSUM DRULE THEN FS[clos_fvsProof_ref_rel_cases]) THEN
  FS[FAPPLY_FUPDATE_THM] THEN RW[] THEN FS[clos_fvsProof_ref_rel_cases]);;

(* HOL4: do_app_lemma [local] *)
let clos_fvsProof_do_app_lemma = prove
 (CASE_TERM
  `clos_fvsProof_state_rel (s:(C,FFI)clos_state) t /\ ALL2 clos_fvsProof_v_rel xs ys ==>
   match clos_do_app opp xs s with
     Rerr err1 -> ?err2. clos_do_app opp ys t = Rerr err2 /\
                         exc_rel clos_fvsProof_v_rel err1 err2
   | Rval (x,s1) -> ?y t1. clos_fvsProof_v_rel x y /\ clos_fvsProof_state_rel s1 t1 /\
                           clos_do_app opp ys t = Rval (y,t1)`,
  MP_TAC(ISPECL [`clos_fvsProof_v_rel`;
                 `clos_fvsProof_state_rel:(C,FFI)clos_state->(C,FFI)clos_state->bool`;
                 `s:(C,FFI)clos_state`; `t:(C,FFI)clos_state`; `xs:clos_v list`;
                 `ys:clos_v list`; `opp:clos_op`] simple_val_rel_do_app) THEN
  REWRITE_TAC[CLOSP1AUX_fvs_simple_val_rel; clos_fvsProof_simple_state_rel]);;

(* a local helper: the oracle conditions of simple_val_rel_do_install *)
let CLOSP1AUX_fvs_simple_compile_state_rel = prove
 (`simple_compile_state_rel clos_fvsProof_v_rel
     (clos_fvsProof_state_rel:(C,FFI)clos_state->(C,FFI)clos_state->bool)
     clos_fvs_compile_inc (clos_fvsProof_code_rel 0)`,
  REWRITE_TAC[simple_compile_state_rel_def; clos_fvsProof_simple_state_rel] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[clos_fvsProof_state_rel_def]) THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM; clos_fvs_compile_inc_def; PAIR_EQ] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[clos_fvs_compile_def; clos_fvsProof_LENGTH_remove_fvs;
                    clos_fvsProof_code_rel_def];
    GEN_TAC THEN
    REWRITE_TAC[clos_fvsProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM;
                shift_seq_def] THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]]);;

(* HOL4: do_install_lemma [local] *)
let clos_fvsProof_do_install_lemma = prove
 (CASE_TERM
  `clos_fvsProof_state_rel (s:(C,FFI)clos_state) t /\ ALL2 clos_fvsProof_v_rel xs ys ==>
   match clos_do_install xs s with
     (Rerr err1,s1) -> ?err2 t1. clos_do_install ys t = (Rerr err2,t1) /\
                                 exc_rel clos_fvsProof_v_rel err1 err2 /\
                                 clos_fvsProof_state_rel s1 t1
   | (Rval exps1,s1) -> ?exps2 t1. clos_fvsProof_state_rel s1 t1 /\ ~(exps1 = []) /\
                                   clos_fvsProof_code_rel 0 exps1 exps2 /\
                                   clos_do_install ys t = (Rval exps2,t1)`,
  MP_TAC(ISPECL [`clos_fvs_compile_inc:clos_prog->clos_prog`; `clos_fvsProof_v_rel`;
                 `clos_fvsProof_state_rel:(C,FFI)clos_state->(C,FFI)clos_state->bool`;
                 `clos_fvsProof_code_rel 0`;
                 `s:(C,FFI)clos_state`; `t:(C,FFI)clos_state`; `xs:clos_v list`;
                 `ys:clos_v list`] simple_val_rel_do_install) THEN
  REWRITE_TAC[CLOSP1AUX_fvs_simple_val_rel; CLOSP1AUX_fvs_simple_compile_state_rel]);;

(* HOL4: state_rel_opt_rel_refs [local] *)
let clos_fvsProof_state_rel_opt_rel_refs = prove
 (`(clos_fvsProof_state_rel (s1:(C,FFI)clos_state) s2 /\
    FLOOKUP (clos_state_refs s1) n = r1 ==>
    ?r2. FLOOKUP (clos_state_refs s2) n = r2 /\ OPTREL clos_fvsProof_ref_rel r1 r2) /\
   (clos_fvsProof_state_rel s1 s2 /\ FLOOKUP (clos_state_refs s2) n = r2 ==>
    ?r1. FLOOKUP (clos_state_refs s1) n = r1 /\ OPTREL clos_fvsProof_ref_rel r1 r2)`,
  REWRITE_TAC[clos_fvsProof_state_rel_def; fmap_rel_def; FLOOKUP_DEF] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[UNWIND_THM1] THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[UNWIND_THM1] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[OPTREL_THM]);;

(* HOL4: state_rel_clocks_eqs [local] *)
let clos_fvsProof_state_rel_clocks_eqs = prove
 (`clos_fvsProof_state_rel (s1:(C,FFI)clos_state) s2 ==>
   clos_state_clock s1 = clos_state_clock s2`,
  SIMP_TAC[clos_fvsProof_state_rel_def]);;

(* HOL4: state_rel_dec_clock [local] *)
let clos_fvsProof_state_rel_dec_clock = prove
 (`clos_fvsProof_state_rel (s1:(C,FFI)clos_state) s2 ==>
   clos_fvsProof_state_rel (clos_dec_clock 1 s1) (clos_dec_clock 1 s2)`,
  REWRITE_TAC[clos_fvsProof_state_rel_def; clos_dec_clock_def;
              clos_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[]);;

(* a local helper: updating related references keeps the states related *)
let CLOSP1AUX_fvs_state_rel_refs_upd = prove
 (`!(s1:(C,FFI)clos_state) s2 p a b.
     clos_fvsProof_state_rel s1 s2 /\ clos_fvsProof_ref_rel a b ==>
     clos_fvsProof_state_rel
       (clos_state_refs_fupd (K (clos_state_refs s1 |+ (p,a))) s1)
       (clos_state_refs_fupd (K (clos_state_refs s2 |+ (p,b))) s2)`,
  REWRITE_TAC[clos_fvsProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[fmap_rel_FUPDATE_same]);;

(* a local helper: the references of related states are related *)
let CLOSP1AUX_fvs_flookup_rel = prove
 (`!(s1:(C,FFI)clos_state) s2 n.
     clos_fvsProof_state_rel s1 s2 ==>
     OPTREL clos_fvsProof_ref_rel (FLOOKUP (clos_state_refs s1) n)
                                  (FLOOKUP (clos_state_refs s2) n)`,
  MESON_TAC[clos_fvsProof_state_rel_opt_rel_refs]);;

(* local helpers for the forcing of thunks *)
let CLOSP1AUX_dest_thunk_NotThunk = prove
 (`!xs (refs:(num,(clos_v)clos_ref)fmap).
     (!b ptr. ~(xs = [clos_RefPtr b ptr])) ==> clos_dest_thunk xs refs = clos_NotThunk`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[clos_dest_thunk_def] THEN
  STRUCT_CASES_TAC(ISPEC `t:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_dest_thunk_def; CONS_11] THEN
  CASES_ON `h:clos_v` THEN REWRITE_TAC[clos_dest_thunk_def; injectivity "clos_v";
                                      distinctness "clos_v"] THEN
  MESON_TAC[]);;
let CLOSP1AUX_fvs_dest_thunk_rel = prove
 (CASE_TERM `!(s:(C,FFI)clos_state) t xs ys.
     clos_fvsProof_state_rel s t /\ ALL2 clos_fvsProof_v_rel xs ys ==>
     match clos_dest_thunk ys (clos_state_refs t) with
       clos_BadRef -> clos_dest_thunk xs (clos_state_refs s) = clos_BadRef
     | clos_NotThunk -> clos_dest_thunk xs (clos_state_refs s) = clos_NotThunk
     | clos_IsThunk m w -> ?v. clos_dest_thunk xs (clos_state_refs s) = clos_IsThunk m v /\
                              clos_fvsProof_v_rel v w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `?b ptr. xs = [clos_RefPtr b ptr]` THENL
   [FS[] THEN RVEQ_TAC THEN FS[clos_dest_thunk_def] THEN
    FIRST_ASSUM (MP_TAC o SPEC `ptr:num` o MATCH_MP CLOSP1AUX_fvs_flookup_rel) THEN
    QCASES_ON "FLOOKUP (clos_state_refs s) ptr" THEN FS[OPTREL_THM; OPTREL_SOME] THEN
    STRIP_TAC THEN FS[] THEN QCASES_ON "a" THEN FS[clos_fvsProof_ref_rel_cases] THEN
    TRY (QCASES_ON "a0") THEN RW[] THEN FS[];
    SUBGOAL_THEN `!b ptr. ~(ys = [clos_RefPtr b ptr])` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN RVEQ_TAC THEN FS[ONCE clos_fvsProof_v_rel_cases];
      FS[CLOSP1AUX_dest_thunk_NotThunk; NOT_EXISTS_THM]]]);;

let CLOSP1AUX_dest_thunk_IsThunk = prove
 (`!xs refs m v. clos_dest_thunk xs refs = clos_IsThunk m v ==>
                 ?b ptr. xs = [clos_RefPtr b ptr]`,
  MESON_TAC[CLOSP1AUX_dest_thunk_NotThunk; distinctness "clos_dest_thunk_ret"]);;

(* HOL4: rel_update_thunk [local] *)
let clos_fvsProof_rel_update_thunk = prove
 (`clos_fvsProof_state_rel (s1:(C,FFI)clos_state) s2 /\
   ALL2 clos_fvsProof_v_rel vs ys ==>
   (clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s1) vs = NONE ==>
    clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s2) ys = NONE) /\
   (clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s1) vs = SOME refs1 ==>
    ?refs2. clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s2) ys = SOME refs2 /\
            clos_fvsProof_state_rel (clos_state_refs_fupd (K refs1) s1)
                                    (clos_state_refs_fupd (K refs2) s2))`,
  STRIP_TAC THEN QCASES_ON "vs" THEN FS[clos_update_thunk_def] THEN
  QCASES_ON "a1" THEN FS[clos_update_thunk_def] THEN RVEQ_TAC THEN
  DRULE CLOSP1AUX_fvs_dest_thunk_rel THEN DISCH_THEN (QSPECL_THEN ["[a0]"; "[y]"] MP_TAC) THEN
  FS[] THEN TOP_CASE_TAC THEN RW[store_thunk_def] THEN
  FIRST_ASSUM (MP_TAC o SPEC `ptr:num` o MATCH_MP CLOSP1AUX_fvs_flookup_rel) THEN
  QCASES_ON "FLOOKUP (clos_state_refs s1) ptr" THEN FS[OPTREL_THM; OPTREL_SOME] THEN
  STRIP_TAC THEN FS[] THEN QCASES_ON "a" THEN FS[clos_fvsProof_ref_rel_cases] THEN
  RVEQ_TAC THEN FS[] THEN TOP_CASE_TAC THEN FS[] THEN RVEQ_TAC THEN
  MATCH_MP_TAC CLOSP1AUX_fvs_state_rel_refs_upd THEN FS[clos_fvsProof_ref_rel_cases]);;

(* ------------------------------------------------------------------------- *)
(* The correctness of remove_fvs (HOL4: evaluate_remove_fvs), by the         *)
(* induction of closProps (CLOSPROPSAUX_evaluate_ind), case by case as in    *)
(* HOL4                                                                      *)
(* ------------------------------------------------------------------------- *)

(* local helpers: booleans on the right of v_rel, and related values agree  *)
(* on being a boolean                                                      *)
let CLOSP1AUX_fvs_v_rel_Boolv_right = prove
 (`!x b. clos_fvsProof_v_rel x (clos_Boolv b) <=> x = clos_Boolv b`,
  REWRITE_TAC[clos_Boolv_def] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_fvsProof_v_rel_cases] THEN
  REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"; GSYM CONJ_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[LIST_REL_NIL] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[]);;

let CLOSP1AUX_fvs_Boolv_rel = prove
 (`!x y b. clos_fvsProof_v_rel x y ==> (clos_Boolv b = y <=> clos_Boolv b = x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
  FS[CLOSP1AUX_fvs_v_rel_Boolv_right]);;

(* local helpers: a case on a pair built by a case on a pair; clock updates *)
(* of related states; dest_closure_SOME_Full_app with the dest_closure     *)
(* first, so that IMP_RES_TAC resolves it on that assumption first         *)
let CLOSP1AUX_pair_CASE_CASE = prove
 (`!(x:A#B) (f:A->B->C#D) (g:C->D->E).
     pair_CASE (pair_CASE x f) g = pair_CASE x (\a b. pair_CASE (f a b) g)`,
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE]);;

let CLOSP1AUX_fvs_state_rel_clock = prove
 (`!(s:(C,FFI)clos_state) t n.
     clos_fvsProof_state_rel s t ==>
     clos_fvsProof_state_rel (clos_state_clock_fupd (K n) s) (clos_state_clock_fupd (K n) t) /\
     clos_fvsProof_state_rel (clos_dec_clock n s) (clos_dec_clock n t)`,
  REWRITE_TAC[clos_fvsProof_state_rel_def; clos_dec_clock_def;
              clos_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[]);;

let CLOSP1AUX_full_app_dc =
  ONCE_REWRITE_RULE[TAUT `a /\ b /\ c /\ d ==> e <=> d ==> a /\ b /\ c ==> e`]
    clos_fvsProof_dest_closure_SOME_Full_app;;

(* HOL4: evaluate_remove_fvs *)
let evaluate_remove_fvs = prove
 (`(!xs env1 (s1:(C,FFI)clos_state) res1 s2 ys env2 t1.
      clos_evaluate (xs,env1,s1) = (res1,s2) /\
      ALL2 clos_fvsProof_v_rel env1 env2 /\ clos_fvsProof_state_rel s1 t1 /\
      clos_fvsProof_code_rel (LENGTH env1) xs ys ==>
      ?res2 t2.
        clos_evaluate (ys,env2,t1) = (res2,t2) /\
        result_rel (ALL2 clos_fvsProof_v_rel) clos_fvsProof_v_rel res1 res2 /\
        clos_fvsProof_state_rel s2 t2) /\
   (!loc_opt f1 args1 (s1:(C,FFI)clos_state) res1 s2 f2 args2 t1.
      evaluate_app loc_opt f1 args1 s1 = (res1,s2) /\
      clos_fvsProof_v_rel f1 f2 /\ ALL2 clos_fvsProof_v_rel args1 args2 /\
      clos_fvsProof_state_rel s1 t1 ==>
      ?res2 t2.
        evaluate_app loc_opt f2 args2 t1 = (res2,t2) /\
        result_rel (ALL2 clos_fvsProof_v_rel) clos_fvsProof_v_rel res1 res2 /\
        clos_fvsProof_state_rel s2 t2)`,
  let start_tac =
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    FS[clos_fvsProof_code_rel_def; remove_fvs_def] THEN RVEQ_TAC THEN
    QPAT_X_ASSUM "clos_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[clos_evaluate_def]) THEN
    RW CLOSPROPSAUX_eval_case_eqs
  and ih_tac =
    FIRST_X_ASSUM (fun th ->
      if is_imp (snd (strip_forall (concl th))) then DRULE_ALL th else NO_TAC) THEN
    DISCH_THEN (CAKE_ASSUME_TAC o CAKE_SIMP_RULE[]) THEN RVEQ_TAC
  and srel_tac =
    QPAT_ASSUM "clos_fvsProof_state_rel _ _"
      (STRIP_ASSUME_TAC o REWRITE_RULE[clos_fvsProof_state_rel_def])
  and src_tac =
    QPAT_X_ASSUM "_ = (res1,s2)" MP_TAC THEN RW CLOSPROPSAUX_eval_case_eqs THEN
    ONCE_REWRITE_TAC[clos_evaluate_def] THEN SIMP[]
  and letrec_ih_tac =
    LAST_X_ASSUM (DRULE_THEN (IRULE o REWRITE_RULE[LENGTH_LIST_OF_SEQ])) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EVERY2_APPEND_suff THEN
    FS[LIST_REL_GENLIST; clos_fvsProof_v_rel_simps; CLOSP1AUX_fvs_f_rel_MAP] in
  MATCH_MP_TAC CLOSPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THENL
   [(* nil *)
    RW[clos_evaluate_def; clos_fvsProof_code_rel_def; remove_fvs_def];
    (* cons *)
    start_tac THEN ih_tac THEN ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN SIMP[] THEN
    ih_tac THEN SIMP[] THEN IMP_RES_TAC clos_evaluate_SING THEN GVS[];
    (* Var *)
    RW[clos_evaluate_def; remove_fvs_def; clos_fvsProof_code_rel_def] THEN
    IMP_RES_TAC LIST_REL_LENGTH THEN RFS[LIST_REL_EL_EQN; clos_do_app_def];
    (* If *)
    start_tac THEN ih_tac THEN TRY ih_tac THEN ONCE_REWRITE_TAC[clos_evaluate_def] THEN
    SIMP[] THEN IMP_RES_TAC clos_evaluate_SING THEN GVS[] THEN
    IMP_RES_TAC CLOSP1AUX_fvs_Boolv_rel THEN FS[];
    (* Let *)
    start_tac THEN ih_tac THEN ONCE_REWRITE_TAC[clos_evaluate_def] THEN SIMP[] THEN
    IMP_RES_TAC clos_evaluate_IMP_LENGTH THEN FS[clos_fvsProof_LENGTH_remove_fvs] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN LAST_X_ASSUM DRULE THEN DISCH_THEN IRULE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EVERY2_APPEND_suff THEN ASM_REWRITE_TAC[];
    (* Raise *)
    start_tac THEN ih_tac THEN ONCE_REWRITE_TAC[clos_evaluate_def] THEN SIMP[] THEN
    IMP_RES_TAC clos_evaluate_SING THEN GVS[];
    (* Handle *)
    start_tac THEN ih_tac THEN ONCE_REWRITE_TAC[clos_evaluate_def] THEN SIMP[] THEN
    TRY ih_tac THEN FS[ADD1];
    (* Op: the arguments first, then Install, ForceThunk or the other operations *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    FS[clos_fvsProof_code_rel_def; remove_fvs_def; PULL_EXISTS] THEN RVEQ_TAC THEN
    QPAT_X_ASSUM "clos_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[clos_evaluate_def]) THEN
    RW[pair_case_eq; case_eq "result"] THEN ih_tac THEN
    TRY (ONCE_REWRITE_TAC[clos_evaluate_def] THEN SIMP[] THEN NO_TAC) THEN
    ASM_CASES_TAC `op = clos_Install` THENL
     [src_tac THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP EVERY2_REVERSE) THEN
      DRULE (GEN_ALL clos_fvsProof_do_install_lemma) THEN DISCH_THEN DRULE THEN
      SIMP[] THEN STRIP_TAC THEN FS[clos_fvsProof_code_rel_def] THEN RVEQ_TAC THEN
      TRY ih_tac THEN SIMP[] THEN MATCH_MP_TAC LIST_REL_LAST THEN
      IMP_RES_TAC clos_evaluate_IMP_LENGTH THEN ASM_MESON_TAC[LENGTH_EQ_NIL];
      ALL_TAC] THEN
    ASM_CASES_TAC `op = clos_ThunkOp ForceThunk` THENL
     [src_tac THEN DRULE CLOSP1AUX_fvs_dest_thunk_rel THEN DISCH_THEN DRULE THEN
      TOP_CASE_TAC THEN FS[] THEN RW[] THEN TRY ih_tac THEN
      FS[clos_AppUnit_def; remove_fvs_def] THEN
      IMP_RES_TAC CLOSP1AUX_dest_thunk_IsThunk THEN GVS[] THEN
      DRULE_ALL clos_fvsProof_rel_update_thunk THEN REWRITE_TAC[FORALL_AND_THM] THEN
      STRIP_TAC THEN RES_TAC THEN FS[];
      src_tac THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP EVERY2_REVERSE) THEN
      DRULE (GEN_ALL clos_fvsProof_do_app_lemma) THEN DISCH_THEN DRULE THEN
      DISCH_THEN (QSPEC_THEN "op" MP_TAC) THEN SIMP[] THEN STRIP_TAC THEN SIMP[]];
    (* Fn *)
    REPEAT STRIP_TAC THEN FS[clos_fvsProof_code_rel_def; remove_fvs_def] THEN RVEQ_TAC THEN
    srel_tac THEN
    QPAT_X_ASSUM "clos_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[clos_evaluate_def]) THEN
    ONCE_REWRITE_TAC[clos_evaluate_def] THEN QCASES_ON "vsopt" THEN RW[] THEN
    TRY (QSPECL_THEN ["a"; "env1"; "env2"] MP_TAC clos_fvsProof_lookup_vars_lemma THEN
         QPAT_X_ASSUM "_ = res1,s2" MP_TAC THEN TOP_CASE_TAC THEN RW[] THEN
         IMP_RES_TAC lookup_vars_SOME) THEN
    FS[clos_fvsProof_code_rel_def; ADD_AC];
    (* Letrec *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    FS[clos_fvsProof_code_rel_def; remove_fvs_def] THEN RVEQ_TAC THEN srel_tac THEN
    QPAT_X_ASSUM "clos_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[clos_evaluate_def]) THEN
    ONCE_REWRITE_TAC[clos_evaluate_def] THEN
    FS[ALL_MAP; o_DEF; LENGTH_MAP; CLOSP1AUX_pair_CASE_CASE] THEN
    COND_CASES_TAC THEN RW[] THEN QCASES_ON "namesopt" THEN GVS[] THENL
     [letrec_ih_tac;
      QSPECL_THEN ["a"; "env1"; "env2"] MP_TAC clos_fvsProof_lookup_vars_lemma THEN
      QCASES_ON "lookup_vars a env1" THEN GVS[] THEN STRIP_TAC THEN
      IMP_RES_TAC lookup_vars_SOME THEN FS[] THEN letrec_ih_tac];
    (* App *)
    start_tac THEN REPEAT ih_tac THEN ONCE_REWRITE_TAC[clos_evaluate_def] THEN
    SIMP[clos_fvsProof_LENGTH_remove_fvs] THEN IMP_RES_TAC clos_evaluate_SING THEN GVS[];
    (* Tick *)
    start_tac THEN srel_tac THEN ONCE_REWRITE_TAC[clos_evaluate_def] THEN SIMP[] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP clos_fvsProof_state_rel_dec_clock) THEN
    ih_tac THEN SIMP[];
    (* Call *)
    start_tac THEN ih_tac THEN IMP_RES_TAC clos_fvsProof_find_code_lemma THEN
    ONCE_REWRITE_TAC[clos_evaluate_def] THEN RFS[];
    (* evaluate_app NIL *)
    RW[clos_evaluate_def];
    (* evaluate_app CONS: dest_closure gives NONE, Partial_app or Full_app *)
    REWRITE_TAC[LENGTH] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    STRIP_TAC THEN srel_tac THEN
    QPAT_X_ASSUM "evaluate_app _ _ _ _ = _" (MP_TAC o ONCE_REWRITE_RULE[clos_evaluate_def]) THEN
    RW[pair_case_eq; COND_CASE_EQ; option_case_eq; case_eq "app_kind"] THEN
    IMP_RES_TAC CLOSP1AUX_dest_closure_NONE_Partial THEN
    QPAT_X_ASSUM "ALL2 _ (CONS _ _) _" (STRIP_ASSUME_TAC o REWRITE_RULE[LIST_REL_CONS1]) THEN
    RVEQ_TAC THEN IMP_RES_TAC CLOSP1AUX_full_app_dc THEN
    IMP_RES_TAC (GSYM LIST_REL_LENGTH) THEN IMP_RES_TAC CLOSP1AUX_fvs_state_rel_clock THEN
    ONCE_REWRITE_TAC[clos_evaluate_def] THEN SIMP[] THEN
    LAST_X_ASSUM (DRULE_THEN (DRULE_THEN (DRULE_THEN (QSPECL_THEN
      ["[exp2]"; "env2"; "clos_dec_clock (SUC (LENGTH v5) - LENGTH a2) t1"] MP_TAC)))) THEN
    SIMP[] THEN STRIP_TAC THEN QPAT_X_ASSUM "_ = (res1,s2)" MP_TAC THEN
    QPAT_X_ASSUM "result_rel _ _ _ _" MP_TAC THEN QCASES_ON "x" THEN RW[] THEN
    IMP_RES_TAC clos_evaluate_SING THEN RVEQ_TAC THEN FS[LIST_REL_CONS1] THEN RVEQ_TAC THEN
    TRY ih_tac THEN SIMP[]]);;

let remove_fvs_correct = prove
 (`!xs env1 (s1:(C,FFI)clos_state) res1 s2 env2 t1.
     clos_evaluate (xs,env1,s1) = (res1,s2) /\
     ALL2 clos_fvsProof_v_rel env1 env2 /\ clos_fvsProof_state_rel s1 t1 ==>
     ?res2 t2.
       clos_evaluate (remove_fvs (LENGTH env1) xs,env2,t1) = (res2,t2) /\
       result_rel (ALL2 clos_fvsProof_v_rel) clos_fvsProof_v_rel res1 res2 /\
       clos_fvsProof_state_rel s2 t2`,
  REPEAT STRIP_TAC THEN DRULE (CONJUNCT1 evaluate_remove_fvs) THEN
  FS[clos_fvsProof_code_rel_def]);;

(* preservation of observational semantics *)

(* HOL4: semantics_compile *)
let clos_fvsProof_semantics_compile = prove
 (`~(clos_semantics (ffi:(FFI)ffi_state) max_app FEMPTY (co:num->C#clos_prog)
       (pure_cc clos_fvs_compile_inc cc) xs = Fail) ==>
   (!n. SND (SND (co n)) = []) /\ 1 <= max_app ==>
   clos_semantics ffi max_app FEMPTY (pure_co clos_fvs_compile_inc o co) cc
     (clos_fvs_compile xs) =
   clos_semantics ffi max_app FEMPTY co (pure_cc clos_fvs_compile_inc cc) xs`,
  REPEAT STRIP_TAC THEN IRULE clos_IMP_semantics_eq THEN
  QEXISTS_TAC "\\c1 o1 k1 e1 c2 o2 k2 e2. T" THEN FS[clos_eval_sim_def] THEN RW[] THEN
  DRULE remove_fvs_correct THEN
  DISCH_THEN (QSPECL_THEN ["[]"; "clos_initial_state ffi max_app FEMPTY
                                  (pure_co clos_fvs_compile_inc o co) cc k"] MP_TAC) THEN
  FS[clos_fvsProof_state_rel_def; clos_initial_state_def; clos_fvs_compile_def] THEN
  STRIP_TAC THEN QEXISTS_TAC "0" THEN FS[] THEN
  QCASES_ON "res1" THEN FS[] THEN QCASES_ON "a" THEN FS[]);;

(* syntactic properties *)

(* local helpers: remove_fvs on lists and the functions of a Letrec, by the *)
(* mutual induction of remove_fvs_sing (clos_fvs.ml)                        *)
let CLOSP1AUX_RFS_TAC (thl:thm list) : tactic =
  MATCH_MP_TAC remove_fvs_sing_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN
  REWRITE_TAC[remove_fvs_sing_def; LET_DEF; LET_END_DEF] THEN TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC([MAP; LENGTH; ALL] @ thl);;

let CLOSP1AUX_remove_fvs_list = prove
 (`!fvs es. remove_fvs fvs es = remove_fvs_list fvs es`,
  REWRITE_TAC[remove_fvs_sing_eq]);;

let CLOSP1AUX_rfs_code_locs = prove
 (`(!fvs e. code_locs [remove_fvs_sing fvs e] = code_locs [e]) /\
   (!fvs es. code_locs (remove_fvs_list fvs es) = code_locs es) /\
   (!m fvs fns. code_locs (MAP SND (remove_fvs_let m fvs fns)) = code_locs (MAP SND fns) /\
                LENGTH (remove_fvs_let m fvs fns) = LENGTH fns)`,
  MATCH_MP_TAC remove_fvs_sing_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN
  REWRITE_TAC[remove_fvs_sing_def; LET_DEF; LET_END_DEF] THEN TRY COND_CASES_TAC THEN
  ONCE_REWRITE_TAC[code_locs_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; MAP; LENGTH; code_locs_def] THEN
  TRY(ONCE_REWRITE_TAC[code_locs_cons] THEN ASM_REWRITE_TAC[]));;

let code_locs_remove_fvs = prove
 (`!fvs xs. code_locs (remove_fvs fvs xs) = code_locs xs`,
  REWRITE_TAC[CLOSP1AUX_remove_fvs_list; CLOSP1AUX_rfs_code_locs]);;
let _ = cake_add_simps [code_locs_remove_fvs];;

let CLOSP1AUX_every_Fn_SOME_cons = prove
 (`!x xs. every_Fn_SOME (CONS x xs) <=> every_Fn_SOME [x] /\ every_Fn_SOME xs`,
  REPEAT GEN_TAC THEN CASES_ON `xs:clos_exp list` THEN REWRITE_TAC[every_Fn_SOME_def]);;

let CLOSP1AUX_every_Fn_vs_NONE_cons = prove
 (`!x xs. every_Fn_vs_NONE (CONS x xs) <=> every_Fn_vs_NONE [x] /\ every_Fn_vs_NONE xs`,
  REPEAT GEN_TAC THEN CASES_ON `xs:clos_exp list` THEN REWRITE_TAC[every_Fn_vs_NONE_def]);;

let CLOSP1AUX_IS_NONE_EQ = prove
 (`!x:A option. IS_NONE x <=> x = NONE`,
  GEN_TAC THEN CASES_ON `x:A option` THEN
  REWRITE_TAC[IS_NONE_DEF; distinctness "option"]);;

let CLOSP1AUX_LENGTH_remove_fvs_let = prove
 (`!m fvs fns. LENGTH (remove_fvs_let m fvs fns) = LENGTH fns`,
  MESON_TAC[CLOSP1AUX_rfs_code_locs]);;

(* a local helper: is a term an application of the constant name *)
let CLOSP1AUX_is_app name tm =
  try fst(dest_const(fst(strip_comb tm))) = name with Failure _ -> false;;

let CLOSP1AUX_rfs_fv = prove
 (`(!fvs e. every_Fn_vs_NONE [e] ==> !v. clos_fv1 v (remove_fvs_sing fvs e) ==> v < fvs) /\
   (!fvs es. every_Fn_vs_NONE es ==> !v. clos_fv v (remove_fvs_list fvs es) ==> v < fvs) /\
   (!m fvs fns. every_Fn_vs_NONE (MAP SND fns) ==>
                !v n x. MEM (n,x) (remove_fvs_let m fvs fns) /\ clos_fv1 v x ==> v < n + m + fvs)`,
  MATCH_MP_TAC remove_fvs_sing_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[remove_fvs_sing_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[fv1_thm; clos_fv_def; every_Fn_vs_NONE_def; MEM; fv_cons; MAP;
              CLOSP1AUX_IS_NONE_EQ; CLOSP1AUX_LENGTH_remove_fvs_let; GSYM EX_MEM;
              EXISTS_PAIR_THM; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if CLOSP1AUX_is_app "every_Fn_vs_NONE" c && is_cons (rand c) &&
       not (rand (rand c) = `[]:clos_exp list`)
    then STRIP_ASSUME_TAC (ONCE_REWRITE_RULE[CLOSP1AUX_every_Fn_vs_NONE_cons] th)
    else NO_TAC)) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  TRY(FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term is_cond) (concl th))) THEN
      COND_CASES_TAC THEN REWRITE_TAC[fv1_thm; clos_fv_def] THEN ASM_ARITH_TAC) THEN
  CLOSPROPSAUX_RES_TAC THEN TRY ASM_ARITH_TAC);;

let fv_max_remove_fvs = prove
 (`!fvs xs. every_Fn_vs_NONE xs ==> (!v. clos_fv v (remove_fvs fvs xs) ==> v < fvs)`,
  REWRITE_TAC[CLOSP1AUX_remove_fvs_list] THEN MESON_TAC[CLOSP1AUX_rfs_fv]);;

let CLOSP1AUX_rfs_every_Fn = prove
 (`(!fvs e. (every_Fn_SOME [remove_fvs_sing fvs e] <=> every_Fn_SOME [e]) /\
            (every_Fn_vs_NONE [remove_fvs_sing fvs e] <=> every_Fn_vs_NONE [e])) /\
   (!fvs es. (every_Fn_SOME (remove_fvs_list fvs es) <=> every_Fn_SOME es) /\
             (every_Fn_vs_NONE (remove_fvs_list fvs es) <=> every_Fn_vs_NONE es)) /\
   (!m fvs fns. (every_Fn_SOME (MAP SND (remove_fvs_let m fvs fns)) <=>
                 every_Fn_SOME (MAP SND fns)) /\
                (every_Fn_vs_NONE (MAP SND (remove_fvs_let m fvs fns)) <=>
                 every_Fn_vs_NONE (MAP SND fns)))`,
  CLOSP1AUX_RFS_TAC[every_Fn_SOME_def; every_Fn_vs_NONE_def] THEN
  ONCE_REWRITE_TAC[CLOSP1AUX_every_Fn_SOME_cons; CLOSP1AUX_every_Fn_vs_NONE_cons] THEN
  ASM_REWRITE_TAC[]);;

let remove_fvs_every_Fn_SOME = prove
 (`!fvs es. every_Fn_SOME (remove_fvs fvs es) <=> every_Fn_SOME es`,
  REWRITE_TAC[CLOSP1AUX_remove_fvs_list; CLOSP1AUX_rfs_every_Fn]);;
let _ = cake_add_simps [remove_fvs_every_Fn_SOME];;

let remove_fvs_every_Fn_vs_NONE = prove
 (`!fvs es. every_Fn_vs_NONE (remove_fvs fvs es) <=> every_Fn_vs_NONE es`,
  REWRITE_TAC[CLOSP1AUX_remove_fvs_list; CLOSP1AUX_rfs_every_Fn]);;
let _ = cake_add_simps [remove_fvs_every_Fn_vs_NONE];;

let CLOSP1AUX_rfs_globals = prove
 (`(!fvs e. clos_set_globals (remove_fvs_sing fvs e) = clos_set_globals e /\
            (clos_esgc_free (remove_fvs_sing fvs e) <=> clos_esgc_free e)) /\
   (!fvs es. clos_elist_globals (remove_fvs_list fvs es) = clos_elist_globals es /\
             MAP clos_set_globals (remove_fvs_list fvs es) = MAP clos_set_globals es /\
             (ALL clos_esgc_free (remove_fvs_list fvs es) <=> ALL clos_esgc_free es)) /\
   (!m fvs fns. clos_elist_globals (MAP SND (remove_fvs_let m fvs fns)) =
                clos_elist_globals (MAP SND fns))`,
  CLOSP1AUX_RFS_TAC[clos_set_globals_def; clos_esgc_free_def; clos_op_gbag_def;
                    BAG_UNION_EMPTY]);;

let remove_fvs_set_globals = prove
 (`!fvs x. MAP clos_set_globals (remove_fvs fvs x) = MAP clos_set_globals x`,
  REWRITE_TAC[CLOSP1AUX_remove_fvs_list; CLOSP1AUX_rfs_globals]);;
let _ = cake_add_simps [remove_fvs_set_globals];;

let set_globals_HD_remove_fvs_SING = prove
 (`clos_set_globals (HD (remove_fvs fvs [x])) = clos_set_globals x`,
  REWRITE_TAC[CONJUNCT1 remove_fvs_sing_eq; HD; CLOSP1AUX_rfs_globals]);;
let _ = cake_add_simps [set_globals_HD_remove_fvs_SING];;

let remove_fvs_esgc_free = prove
 (`!fvs x. ALL clos_esgc_free (remove_fvs fvs x) <=> ALL clos_esgc_free x`,
  REWRITE_TAC[CLOSP1AUX_remove_fvs_list; CLOSP1AUX_rfs_globals]);;
let _ = cake_add_simps [remove_fvs_esgc_free];;

let remove_fvs_elist_globals = prove
 (`clos_elist_globals (remove_fvs fvs xs) = clos_elist_globals xs`,
  REWRITE_TAC[CLOSP1AUX_remove_fvs_list; CLOSP1AUX_rfs_globals]);;
let _ = cake_add_simps [remove_fvs_elist_globals];;

let EVERY_remove_fvs_sing = prove
 (`ALL f (remove_fvs n [y]) <=> f (HD (remove_fvs n [y]))`,
  REWRITE_TAC[CONJUNCT1 remove_fvs_sing_eq; HD; ALL]);;

let CLOSP1AUX_rfs_labels = prove
 (`(!fvs e. (no_Labels (remove_fvs_sing fvs e) <=> no_Labels e) /\
            (!k. obeys_max_app k (remove_fvs_sing fvs e) <=> obeys_max_app k e) /\
            clos_get_code_labels (remove_fvs_sing fvs e) = clos_get_code_labels e) /\
   (!fvs es. (ALL no_Labels (remove_fvs_list fvs es) <=> ALL no_Labels es) /\
             (!k. ALL (obeys_max_app k) (remove_fvs_list fvs es) <=>
                  ALL (obeys_max_app k) es) /\
             MAP clos_get_code_labels (remove_fvs_list fvs es) =
             MAP clos_get_code_labels es /\
             LENGTH (remove_fvs_list fvs es) = LENGTH es) /\
   (!m fvs fns. (ALL no_Labels (MAP SND (remove_fvs_let m fvs fns)) <=>
                 ALL no_Labels (MAP SND fns)) /\
                (!k. ALL (obeys_max_app k) (MAP SND (remove_fvs_let m fvs fns)) <=>
                     ALL (obeys_max_app k) (MAP SND fns)) /\
                MAP (clos_get_code_labels o SND) (remove_fvs_let m fvs fns) =
                MAP (clos_get_code_labels o SND) fns /\
                LENGTH (remove_fvs_let m fvs fns) = LENGTH fns)`,
  CLOSP1AUX_RFS_TAC[no_Labels_def; obeys_max_app_def; clos_get_code_labels_def;
                    distinctness "clos_op"; assign_get_code_label_def; o_THM;
                    set_of_list; UNIONS_0; UNION_EMPTY]);;

let remove_fvs_no_Labels = prove
 (`!n xs. ALL no_Labels (remove_fvs n xs) <=> ALL no_Labels xs`,
  REWRITE_TAC[CLOSP1AUX_remove_fvs_list; CLOSP1AUX_rfs_labels]);;

let remove_fvs_obeys_max_app = prove
 (`!n xs. ALL (obeys_max_app k) (remove_fvs n xs) <=> ALL (obeys_max_app k) xs`,
  REWRITE_TAC[CLOSP1AUX_remove_fvs_list; CLOSP1AUX_rfs_labels]);;

let get_code_labels_remove_fvs = prove
 (`!n es. MAP clos_get_code_labels (remove_fvs n es) = MAP clos_get_code_labels es`,
  REWRITE_TAC[CLOSP1AUX_remove_fvs_list; CLOSP1AUX_rfs_labels]);;
let _ = cake_add_simps [get_code_labels_remove_fvs];;
