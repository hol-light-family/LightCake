(* ========================================================================= *)
(* clos_ticksProof: port of HOL4 compiler/backend/proofs/                    *)
(* clos_ticksProofScript.sml (CakeML v3479).                                 *)
(* Correctness proof for clos_ticks.                                         *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/clos_ticks.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/closLang.ml";;

type_invention_error := true;;

(* CLOSP2AUX_ names are local helpers. *)

(* HOL4: remove_ticks_IMP_LENGTH *)
let remove_ticks_IMP_LENGTH = prove
 (`!(es:clos_exp list) xs. xs = clos_ticks_remove_ticks es ==> LENGTH es = LENGTH xs`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[clos_ticks_LENGTH_remove_ticks]);;

(* HOL4: remove_ticks_SING *)
let clos_ticksProof_remove_ticks_SING = prove
 (`!e. ?e'. clos_ticks_remove_ticks [e] = [e']`,
  MESON_TAC[remove_ticks_sing_eq]);;

(* HOL4: HD_remove_ticks_SING [simp] *)
let HD_remove_ticks_SING = prove
 (`!x. [HD (clos_ticks_remove_ticks [x])] = clos_ticks_remove_ticks [x] /\
       LENGTH (clos_ticks_remove_ticks [x]) = 1`,
  GEN_TAC THEN REWRITE_TAC[remove_ticks_sing_eq; HD; LENGTH; ONE]);;
let _ = cake_add_simps [HD_remove_ticks_SING];;

(* code relation *)

(* HOL4: code_rel_def *)
let clos_ticksProof_code_rel_def = cake_def
  `clos_ticksProof_code_rel e1 e2 <=> e2 = clos_ticks_remove_ticks e1`;;

(* HOL4: code_rel_IMP_LENGTH *)
let clos_ticksProof_code_rel_IMP_LENGTH = prove
 (`!xs ys. clos_ticksProof_code_rel xs ys ==> LENGTH xs = LENGTH ys`,
  SIMP_TAC[clos_ticksProof_code_rel_def; clos_ticks_LENGTH_remove_ticks]);;

(* HOL4: remove_ticks_CONS *)
let remove_ticks_CONS = prove
 (`!es e. clos_ticks_remove_ticks (CONS e es) =
          CONS (HD (clos_ticks_remove_ticks [e])) (clos_ticks_remove_ticks es)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  REWRITE_TAC[clos_ticks_remove_ticks_def; HD_remove_ticks_SING]);;

(* HOL4: code_rel_CONS_CONS *)
let clos_ticksProof_code_rel_CONS_CONS = prove
 (`!x1 x2 xs y1 y2 ys.
     clos_ticksProof_code_rel (CONS x1 (CONS x2 xs)) (CONS y1 (CONS y2 ys)) <=>
     clos_ticksProof_code_rel [x1] [y1] /\
     clos_ticksProof_code_rel (CONS x2 xs) (CONS y2 ys)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_ticksProof_code_rel_def] THEN
  REWRITE_TAC[ISPECL [`CONS (x2:clos_exp) xs`; `x1:clos_exp`] remove_ticks_CONS] THEN
  MP_TAC(SPEC `x1:clos_exp` clos_ticksProof_remove_ticks_SING) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[HD; CONS_11]);;

(* value relation *)

(* HOL4: f_rel_def *)
let clos_ticksProof_f_rel_def = cake_def
  `clos_ticksProof_f_rel (a1:num,e1:clos_exp) (a2:num,e2:clos_exp) <=>
     a1 = a2 /\ clos_ticksProof_code_rel [e1] [e2]`;;

(* HOL4: v_rel (funs1 and funs2 of the last rule, free in HOL4, are bound) *)
let clos_ticksProof_v_rel_rules,clos_ticksProof_v_rel_ind,
    clos_ticksProof_v_rel_cases,clos_ticksProof_v_rel_strongind =
  cake_inductive
  `(!i. clos_ticksProof_v_rel (clos_Number i) (clos_Number i)) /\
   (!w. clos_ticksProof_v_rel (clos_Word64 w) (clos_Word64 w)) /\
   (!w. clos_ticksProof_v_rel (ByteVector w) (ByteVector w)) /\
   (!n b. clos_ticksProof_v_rel (clos_RefPtr b n) (clos_RefPtr b n)) /\
   (!tag xs ys.
      ALL2 clos_ticksProof_v_rel xs ys ==>
      clos_ticksProof_v_rel (clos_Block tag xs) (clos_Block tag ys)) /\
   (!loc args1 args2 env1 env2 num_args e1 e2.
      ALL2 clos_ticksProof_v_rel env1 env2 /\
      ALL2 clos_ticksProof_v_rel args1 args2 /\
      clos_ticksProof_code_rel [e1] [e2] ==>
      clos_ticksProof_v_rel (clos_Closure loc args1 env1 num_args e1)
                            (clos_Closure loc args2 env2 num_args e2)) /\
   (!loc args1 args2 env1 env2 funs1 funs2 k.
      ALL2 clos_ticksProof_v_rel env1 env2 /\
      ALL2 clos_ticksProof_v_rel args1 args2 /\
      ALL2 clos_ticksProof_f_rel funs1 funs2 ==>
      clos_ticksProof_v_rel (clos_Recclosure loc args1 env1 funs1 k)
                            (clos_Recclosure loc args2 env2 funs2 k))`;;

(* HOL4: v_rel_simps [simp] (HOL4 computes it with SIMP_CONV from v_rel_cases) *)
let clos_ticksProof_v_rel_simps = prove
 (`(!x n. clos_ticksProof_v_rel x (clos_Number n) <=> x = clos_Number n) /\
   (!x n p. clos_ticksProof_v_rel x (clos_Block n p) <=>
            ?xs. x = clos_Block n xs /\ ALL2 clos_ticksProof_v_rel xs p) /\
   (!x p. clos_ticksProof_v_rel x (clos_Word64 p) <=> x = clos_Word64 p) /\
   (!x p. clos_ticksProof_v_rel x (ByteVector p) <=> x = ByteVector p) /\
   (!x b p. clos_ticksProof_v_rel x (clos_RefPtr b p) <=> x = clos_RefPtr b p) /\
   (!x x1 x2 x3 x4 x5.
      clos_ticksProof_v_rel x (clos_Closure x1 x2 x3 x4 x5) <=>
      ?args1 env1 e1.
        x = clos_Closure x1 args1 env1 x4 e1 /\
        ALL2 clos_ticksProof_v_rel env1 x3 /\ ALL2 clos_ticksProof_v_rel args1 x2 /\
        clos_ticksProof_code_rel [e1] [x5]) /\
   (!x y1 y2 y3 y4 y5.
      clos_ticksProof_v_rel x (clos_Recclosure y1 y2 y3 y4 y5) <=>
      ?args1 env1 funs1.
        x = clos_Recclosure y1 args1 env1 funs1 y5 /\
        ALL2 clos_ticksProof_v_rel env1 y3 /\ ALL2 clos_ticksProof_v_rel args1 y2 /\
        ALL2 clos_ticksProof_f_rel funs1 y4) /\
   (!x b. clos_ticksProof_v_rel x (clos_Boolv b) <=> x = clos_Boolv b) /\
   (!x. clos_ticksProof_v_rel x clos_Unit <=> x = clos_Unit)`,
  REWRITE_TAC[clos_Boolv_def; clos_Unit_def] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_ticksProof_v_rel_cases] THEN
  REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"; GSYM CONJ_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[LIST_REL_NIL] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[] THEN MESON_TAC[]);;
let _ = cake_add_simps [clos_ticksProof_v_rel_simps];;

(* state relation *)

(* HOL4: ref_rel *)
let clos_ticksProof_ref_rel_rules,clos_ticksProof_ref_rel_ind,
    clos_ticksProof_ref_rel_cases,clos_ticksProof_ref_rel_strongind =
  cake_inductive
  `(!bs. clos_ticksProof_ref_rel (clos_ByteArray bs) (clos_ByteArray bs)) /\
   (!xs ys.
      ALL2 clos_ticksProof_v_rel xs ys ==>
      clos_ticksProof_ref_rel (clos_ValueArray xs) (clos_ValueArray ys)) /\
   (!m v w.
      clos_ticksProof_v_rel v w ==>
      clos_ticksProof_ref_rel (clos_Thunk m v) (clos_Thunk m w))`;;

(* HOL4: FMAP_REL_def *)
let clos_ticksProof_FMAP_REL_def = cake_def
  `clos_ticksProof_FMAP_REL (r:A->B->bool) (f1:(K,A)fmap) (f2:(K,B)fmap) <=>
     FDOM f1 = FDOM f2 /\
     !k v. FLOOKUP f1 k = SOME v ==> ?v2. FLOOKUP f2 k = SOME v2 /\ r v v2`;;

(* HOL4: state_rel_def *)
let clos_ticksProof_state_rel_def = cake_def
  `clos_ticksProof_state_rel (s:(C,FFI)clos_state) (t:(C,FFI)clos_state) <=>
     (!n. SND (SND (clos_state_compile_oracle s n)) = []) /\
     clos_state_code s = FEMPTY /\ clos_state_code t = FEMPTY /\
     clos_state_max_app t = clos_state_max_app s /\ 1 <= clos_state_max_app s /\
     clos_state_clock t = clos_state_clock s /\
     clos_state_ffi t = clos_state_ffi s /\
     ALL2 (OPTREL clos_ticksProof_v_rel) (clos_state_globals s) (clos_state_globals t) /\
     clos_ticksProof_FMAP_REL clos_ticksProof_ref_rel
       (clos_state_refs s) (clos_state_refs t) /\
     clos_state_compile s = pure_cc clos_ticks_compile_inc (clos_state_compile t) /\
     clos_state_compile_oracle t =
       pure_co clos_ticks_compile_inc o clos_state_compile_oracle s`;;

(* eval remove ticks *)

(* HOL4: mk_Ticks_def *)
let clos_ticksProof_mk_Ticks_def = cake_def
  `(clos_ticksProof_mk_Ticks [] (e:clos_exp) = e) /\
   (clos_ticksProof_mk_Ticks (CONS t tr) e =
      clos_Tick t (clos_ticksProof_mk_Ticks tr e))`;;

(* a local helper: induction on expressions with one predicate *)
let CLOSP2AUX_ticks_exp_ind =
  let th = ISPECL [`P:clos_exp->bool`; `\x:clos_exp list. T`; `\x:(num#clos_exp)list. T`;
                   `\x:num#clos_exp. T`] clos_exp_INDUCT in
  GEN `P:clos_exp->bool` (REWRITE_RULE[] (CONV_RULE (DEPTH_CONV BETA_CONV) th));;

(* HOL4: remove_ticks_Tick *)
let remove_ticks_Tick = prove
 (`!x t e. ~([clos_Tick t e] = clos_ticks_remove_ticks [x])`,
  REWRITE_TAC[CONJUNCT1 remove_ticks_sing_eq; CONS_11] THEN
  MATCH_MP_TAC CLOSP2AUX_ticks_exp_ind THEN
  REWRITE_TAC[clos_ticks_remove_ticks_sing_def; LET_DEF; LET_END_DEF;
              distinctness "clos_exp"] THEN
  MESON_TAC[]);;

(* a local helper: every expression is some Ticks around an expression that *)
(* is not a Tick, with the same remove_ticks                                *)
let CLOSP2AUX_ticks_strip = prove
 (`!x. ?ts y. x = clos_ticksProof_mk_Ticks ts y /\ (!t e. ~(y = clos_Tick t e)) /\
              clos_ticks_remove_ticks [x] = clos_ticks_remove_ticks [y]`,
  let other =
    REPEAT GEN_TAC THEN TRY (DISCH_THEN(K ALL_TAC)) THEN
    EXISTS_TAC `[]:tra list` THEN
    REWRITE_TAC[clos_ticksProof_mk_Ticks_def; UNWIND_THM1; distinctness "clos_exp"]
  and tick =
    REPEAT GEN_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `ts:tra list` (X_CHOOSE_THEN `y:clos_exp` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`CONS (a0:tra) ts`; `y:clos_exp`] THEN
    ASM_REWRITE_TAC[clos_ticksProof_mk_Ticks_def; clos_ticks_remove_ticks_def] in
  MATCH_MP_TAC CLOSP2AUX_ticks_exp_ind THEN REPEAT CONJ_TAC THENL
   [other; other; other; other; other; tick; other; other; other; other; other]);;

(* a local tactic for the remove_ticks_X_IMP_mk_Ticks theorems: strip the   *)
(* Ticks of the source, split it, and solve by matching                      *)
let CLOSP2AUX_TICKS_IMP_TAC : tactic =
  GEN_TAC THEN
  X_CHOOSE_THEN `ts:tra list` (X_CHOOSE_THEN `y:clos_exp` STRIP_ASSUME_TAC)
    (SPEC `x:clos_exp` CLOSP2AUX_ticks_strip) THEN
  ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(fun l -> MP_TAC(el 1 (rev l))) THEN
  SPEC_TAC(`y:clos_exp`,`y:clos_exp`) THEN
  MATCH_MP_TAC CLOSP2AUX_ticks_exp_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY (DISCH_THEN(K ALL_TAC)) THEN
  REWRITE_TAC[clos_ticks_remove_ticks_def; LET_DEF; LET_END_DEF; CONS_11;
              distinctness "clos_exp"; injectivity "clos_exp"] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[MESON[] `!t e. ~(!t' e'. ~(clos_Tick t e = clos_Tick t' e'))`] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[HD_remove_ticks_SING];;

(* HOL4: remove_ticks_Var_IMP_mk_Ticks *)
let remove_ticks_Var_IMP_mk_Ticks = prove
 (`!x tr n. [clos_Var tr n] = clos_ticks_remove_ticks [x] ==>
            ?ts. x = clos_ticksProof_mk_Ticks ts (clos_Var tr n)`,
  CLOSP2AUX_TICKS_IMP_TAC);;

(* HOL4: remove_ticks_If_IMP_mk_Ticks *)
let remove_ticks_If_IMP_mk_Ticks = prove
 (`!x tr e1' e2' e3'.
     [clos_If tr e1' e2' e3'] = clos_ticks_remove_ticks [x] ==>
     ?ts e1 e2 e3. x = clos_ticksProof_mk_Ticks ts (clos_If tr e1 e2 e3) /\
                   e1' = HD (clos_ticks_remove_ticks [e1]) /\
                   e2' = HD (clos_ticks_remove_ticks [e2]) /\
                   e3' = HD (clos_ticks_remove_ticks [e3])`,
  CLOSP2AUX_TICKS_IMP_TAC);;

(* HOL4: remove_ticks_Let_IMP_mk_Ticks *)
let remove_ticks_Let_IMP_mk_Ticks = prove
 (`!x t l e. [clos_Let t l e] = clos_ticks_remove_ticks [x] ==>
             ?ts l' e'. x = clos_ticksProof_mk_Ticks ts (clos_Let t l' e') /\
                        l = clos_ticks_remove_ticks l' /\
                        [e] = clos_ticks_remove_ticks [e']`,
  CLOSP2AUX_TICKS_IMP_TAC);;

(* HOL4: remove_ticks_Raise_IMP_mk_Ticks *)
let remove_ticks_Raise_IMP_mk_Ticks = prove
 (`!x t e. [clos_Raise t e] = clos_ticks_remove_ticks [x] ==>
           ?ts e'. x = clos_ticksProof_mk_Ticks ts (clos_Raise t e') /\
                   [e] = clos_ticks_remove_ticks [e']`,
  CLOSP2AUX_TICKS_IMP_TAC);;

(* HOL4: remove_ticks_Handle_IMP_mk_Ticks *)
let remove_ticks_Handle_IMP_mk_Ticks = prove
 (`!x t e1' e2'. [clos_Handle t e1' e2'] = clos_ticks_remove_ticks [x] ==>
                 ?ts e1 e2. x = clos_ticksProof_mk_Ticks ts (clos_Handle t e1 e2) /\
                            [e1'] = clos_ticks_remove_ticks [e1] /\
                            [e2'] = clos_ticks_remove_ticks [e2]`,
  CLOSP2AUX_TICKS_IMP_TAC);;

(* HOL4: remove_ticks_Op_IMP_mk_Ticks *)
let remove_ticks_Op_IMP_mk_Ticks = prove
 (`!x tr op es'. [clos_Op tr op es'] = clos_ticks_remove_ticks [x] ==>
                 ?ts es. x = clos_ticksProof_mk_Ticks ts (clos_Op tr op es) /\
                         es' = clos_ticks_remove_ticks es`,
  CLOSP2AUX_TICKS_IMP_TAC);;

(* HOL4: remove_ticks_Fn_IMP_mk_Ticks *)
let remove_ticks_Fn_IMP_mk_Ticks = prove
 (`!x tr loc vsopt num_args e'.
     [Fn tr loc vsopt num_args e'] = clos_ticks_remove_ticks [x] ==>
     ?ts e. x = clos_ticksProof_mk_Ticks ts (Fn tr loc vsopt num_args e) /\
            [e'] = clos_ticks_remove_ticks [e]`,
  CLOSP2AUX_TICKS_IMP_TAC);;

(* HOL4: remove_ticks_Letrec_IMP_mk_Ticks *)
let remove_ticks_Letrec_IMP_mk_Ticks = prove
 (CASE_TERM
  `!x tr loc vsopt fns' e'.
     [clos_Letrec tr loc vsopt fns' e'] = clos_ticks_remove_ticks [x] ==>
     ?ts fns e. x = clos_ticksProof_mk_Ticks ts (clos_Letrec tr loc vsopt fns e) /\
                e' = HD (clos_ticks_remove_ticks [e]) /\
                fns' = MAP (\p. match p with
                                  (num_args,x) ->
                                    (num_args, HD (clos_ticks_remove_ticks [x]))) fns`,
  CLOSP2AUX_TICKS_IMP_TAC);;

(* HOL4: remove_ticks_App_IMP_mk_Ticks *)
let remove_ticks_App_IMP_mk_Ticks = prove
 (`!x tr loc_opt e1' es'.
     [clos_App tr loc_opt e1' es'] = clos_ticks_remove_ticks [x] ==>
     ?ts e1 es. x = clos_ticksProof_mk_Ticks ts (clos_App tr loc_opt e1 es) /\
                e1' = HD (clos_ticks_remove_ticks [e1]) /\
                es' = clos_ticks_remove_ticks es`,
  CLOSP2AUX_TICKS_IMP_TAC);;

(* HOL4: remove_ticks_Call_IMP_mk_Ticks *)
let remove_ticks_Call_IMP_mk_Ticks = prove
 (`!x tr ticks' dest es'. [clos_Call tr ticks' dest es'] = clos_ticks_remove_ticks [x] ==>
     ticks' = 0 /\
     ?ts ticks es. x = clos_ticksProof_mk_Ticks ts (clos_Call tr ticks dest es) /\
                   es' = clos_ticks_remove_ticks es`,
  CLOSP2AUX_TICKS_IMP_TAC);;

(* HOL4: remove_ticks_mk_Ticks *)
let remove_ticks_mk_Ticks = prove
 (`!tr e. clos_ticks_remove_ticks [clos_ticksProof_mk_Ticks tr e] =
          clos_ticks_remove_ticks [e]`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[clos_ticksProof_mk_Ticks_def; clos_ticks_remove_ticks_def]);;

(* HOL4: evaluate_mk_Ticks *)
let evaluate_mk_Ticks = prove
 (`!tr e env (s1:(C,FFI)clos_state).
     clos_evaluate ([clos_ticksProof_mk_Ticks tr e],env,s1) =
     if clos_state_clock s1 < LENGTH tr
     then (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) s1)
     else clos_evaluate ([e],env,clos_dec_clock (LENGTH tr) s1)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[clos_ticksProof_mk_Ticks_def; LENGTH; LT; clos_dec_clock_def; SUB_0;
                clos_with_same_clock];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_ticksProof_mk_Ticks_def; LENGTH; clos_evaluate_def] THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[LT_0; PAIR_EQ; clos_state_component_equality;
                    clos_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  SUBGOAL_THEN `clos_state_clock (s1:(C,FFI)clos_state) - 1 < LENGTH (t:tra list) <=>
                clos_state_clock s1 < SUC (LENGTH t)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[clos_state_INFO.ri_fupdfupds; K_o_THM; clos_state_INFO.ri_accfupds;
              K_THM] THEN
  REPEAT AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* HOL4: simple_val_rel *)
let clos_ticksProof_simple_val_rel = prove
 (`clos_simple_val_rel clos_ticksProof_v_rel`,
  REWRITE_TAC[clos_simple_val_rel_def; clos_ticksProof_v_rel_simps] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[clos_isClos_def]);;

(* local helpers: an update of related finite maps; ref_rel with the right *)
(* side known; the references of related states; updates of references     *)
let CLOSP2AUX_ticks_FMAP_REL_FUPDATE = prove
 (`!(r:A->B->bool) (f1:(K,A)fmap) f2 k a b.
     clos_ticksProof_FMAP_REL r f1 f2 /\ r a b ==>
     clos_ticksProof_FMAP_REL r (f1 |+ (k,a)) (f2 |+ (k,b))`,
  REWRITE_TAC[clos_ticksProof_FMAP_REL_def; FDOM_FUPDATE; FLOOKUP_UPDATE] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[injectivity "option"] THEN ASM_MESON_TAC[]);;

let CLOSP2AUX_ticks_ref_rel_right = prove
 (`(!x bs. clos_ticksProof_ref_rel x (clos_ByteArray bs) <=> x = clos_ByteArray bs) /\
   (!x ys. clos_ticksProof_ref_rel x (clos_ValueArray ys) <=>
           ?xs. x = clos_ValueArray xs /\ ALL2 clos_ticksProof_v_rel xs ys) /\
   (!x m w. clos_ticksProof_ref_rel x (clos_Thunk m w) <=>
            ?v. x = clos_Thunk m v /\ clos_ticksProof_v_rel v w)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_ticksProof_ref_rel_cases] THEN
  REWRITE_TAC[distinctness "clos_ref"; injectivity "clos_ref"] THEN MESON_TAC[]);;

let CLOSP2AUX_ticks_flookup_rel = prove
 (`!(s1:(C,FFI)clos_state) s2 n.
     clos_ticksProof_state_rel s1 s2 ==>
     OPTREL clos_ticksProof_ref_rel
            (FLOOKUP (clos_state_refs s1) n) (FLOOKUP (clos_state_refs s2) n)`,
  REWRITE_TAC[clos_ticksProof_state_rel_def; clos_ticksProof_FMAP_REL_def] THEN
  REPEAT STRIP_TAC THEN
  CASES_ON `FLOOKUP (clos_state_refs (s1:(C,FFI)clos_state)) n` THENL
   [SUBGOAL_THEN `FLOOKUP (clos_state_refs (s2:(C,FFI)clos_state)) n = NONE` SUBST1_TAC THENL
     [UNDISCH_TAC `FLOOKUP (clos_state_refs (s1:(C,FFI)clos_state)) n = NONE` THEN
      REWRITE_TAC[FLOOKUP_DEF] THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
      REWRITE_TAC[distinctness "option"];
      REWRITE_TAC[OPTREL_THM]];
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `a:(clos_v)clos_ref`] o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[OPTREL_THM]]);;

let CLOSP2AUX_ticks_state_rel_refs_upd = prove
 (`!(s1:(C,FFI)clos_state) s2 p a b.
     clos_ticksProof_state_rel s1 s2 /\ clos_ticksProof_ref_rel a b ==>
     clos_ticksProof_state_rel
       (clos_state_refs_fupd (K (clos_state_refs s1 |+ (p,a))) s1)
       (clos_state_refs_fupd (K (clos_state_refs s2 |+ (p,b))) s2)`,
  REWRITE_TAC[clos_ticksProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[CLOSP2AUX_ticks_FMAP_REL_FUPDATE]);;

(* HOL4: simple_state_rel *)
let clos_ticksProof_simple_state_rel = prove
 (`clos_simple_state_rel clos_ticksProof_v_rel
     (clos_ticksProof_state_rel:(C,FFI)clos_state->(C,FFI)clos_state->bool)`,
  REWRITE_TAC[clos_simple_state_rel_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `ptr:num` o MATCH_MP CLOSP2AUX_ticks_flookup_rel) THEN
    ASM_REWRITE_TAC[OPTREL_NONE];
    FIRST_ASSUM(MP_TAC o SPEC `ptr:num` o MATCH_MP CLOSP2AUX_ticks_flookup_rel) THEN
    ASM_REWRITE_TAC[OPTREL_SOME; CLOSP2AUX_ticks_ref_rel_right] THEN MESON_TAC[];
    FIRST_ASSUM(MP_TAC o SPEC `ptr:num` o MATCH_MP CLOSP2AUX_ticks_flookup_rel) THEN
    ASM_REWRITE_TAC[OPTREL_SOME; CLOSP2AUX_ticks_ref_rel_right] THEN MESON_TAC[];
    FIRST_ASSUM(MP_TAC o SPEC `ptr:num` o MATCH_MP CLOSP2AUX_ticks_flookup_rel) THEN
    ASM_REWRITE_TAC[OPTREL_SOME; CLOSP2AUX_ticks_ref_rel_right] THEN MESON_TAC[];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_ticksProof_state_rel_def]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  FIRST_ASSUM(fun th -> if can (find_term (fun t -> t = `clos_ticksProof_FMAP_REL:
                              (clos_v clos_ref->clos_v clos_ref->bool)->
                              (num,clos_v clos_ref)fmap->(num,clos_v clos_ref)fmap->bool`))
                              (concl th)
                        then ASSUME_TAC (CONJUNCT1 (REWRITE_RULE[clos_ticksProof_FMAP_REL_def] th))
                        else NO_TAC) THEN
  ASM_REWRITE_TAC[clos_ticksProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  MATCH_MP_TAC CLOSP2AUX_ticks_FMAP_REL_FUPDATE THEN
  ASM_REWRITE_TAC[CLOSP2AUX_ticks_ref_rel_right; injectivity "clos_ref"; UNWIND_THM1]);;

(* HOL4: do_app_lemma [local] *)
let clos_ticksProof_do_app_lemma = prove
 (CASE_TERM
  `clos_ticksProof_state_rel s (t:(C,FFI)clos_state) /\
   ALL2 clos_ticksProof_v_rel xs ys ==>
   match clos_do_app opp ys t with
     Rerr err2 -> (?err1. clos_do_app opp xs s = Rerr err1 /\
                          exc_rel clos_ticksProof_v_rel err1 err2)
   | Rval (y,t1) -> ?x s1. clos_ticksProof_v_rel x y /\
                           clos_ticksProof_state_rel s1 t1 /\
                           clos_do_app opp xs s = Rval (x,s1)`,
  MATCH_MP_TAC simple_val_rel_do_app_rev THEN
  REWRITE_TAC[clos_ticksProof_simple_val_rel; clos_ticksProof_simple_state_rel]);;

(* a local helper: the oracle conditions of simple_val_rel_do_install *)
let CLOSP2AUX_ticks_simple_compile_state_rel = prove
 (`simple_compile_state_rel clos_ticksProof_v_rel
     (clos_ticksProof_state_rel:(C,FFI)clos_state->(C,FFI)clos_state->bool)
     clos_ticks_compile_inc clos_ticksProof_code_rel`,
  REWRITE_TAC[simple_compile_state_rel_def; clos_ticksProof_simple_state_rel] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[clos_ticksProof_state_rel_def]) THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM; clos_ticks_compile_inc_def; PAIR_EQ] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[clos_ticks_LENGTH_remove_ticks; clos_ticksProof_code_rel_def];
    GEN_TAC THEN
    REWRITE_TAC[clos_ticksProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM;
                shift_seq_def] THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]]);;

(* HOL4: do_install_lemma [local] *)
let clos_ticksProof_do_install_lemma = prove
 (CASE_TERM
  `clos_ticksProof_state_rel (s:(C,FFI)clos_state) t /\
   ALL2 clos_ticksProof_v_rel xs ys ==>
   match clos_do_install xs s with
     (Rerr err1,s1) -> ?err2 t1. clos_do_install ys t = (Rerr err2,t1) /\
                                 exc_rel clos_ticksProof_v_rel err1 err2 /\
                                 clos_ticksProof_state_rel s1 t1
   | (Rval exps1,s1) -> ?exps2 t1. clos_ticksProof_state_rel s1 t1 /\ ~(exps1 = []) /\
                                   clos_ticksProof_code_rel exps1 exps2 /\
                                   clos_do_install ys t = (Rval exps2,t1)`,
  MATCH_MP_TAC (ISPEC `clos_ticks_compile_inc:clos_prog->clos_prog`
                 simple_val_rel_do_install) THEN
  REWRITE_TAC[clos_ticksProof_simple_val_rel; CLOSP2AUX_ticks_simple_compile_state_rel]);;

(* HOL4: lookup_vars_lemma *)
let clos_ticksProof_lookup_vars_lemma = prove
 (CASE_TERM
  `!vs env1 env2. ALL2 clos_ticksProof_v_rel env1 env2 ==>
     match lookup_vars vs env2 with
       NONE -> lookup_vars vs env1 = NONE
     | SOME l2 -> ?l1. ALL2 clos_ticksProof_v_rel l1 l2 /\ lookup_vars vs env1 = SOME l1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[lookup_vars_def] THEN CASE_REWRITE_TAC[] THENL
   [MESON_TAC[ALL2]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`env1:clos_v list`; `env2:clos_v list`]) THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `lookup_vars t (env2:clos_v list)` THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  EXISTS_TAC `CONS (EL h (env1:clos_v list)) l1` THEN
  ASM_REWRITE_TAC[ALL2] THEN ASM_MESON_TAC[LIST_REL_EL_EQN]);;

(* HOL4: state_rel_IMP_max_app_EQ *)
let state_rel_IMP_max_app_EQ = prove
 (`!s (t:(C,FFI)clos_state). clos_ticksProof_state_rel s t ==>
     clos_state_max_app s = clos_state_max_app t`,
  SIMP_TAC[clos_ticksProof_state_rel_def]);;

(* HOL4: state_rel_IMP_code_FEMPTY [local] *)
let state_rel_IMP_code_FEMPTY = prove
 (`!s (t:(C,FFI)clos_state). clos_ticksProof_state_rel s t ==>
     clos_state_code s = FEMPTY /\ clos_state_code t = FEMPTY`,
  SIMP_TAC[clos_ticksProof_state_rel_def]);;

(* HOL4: state_rel_clock *)
let clos_ticksProof_state_rel_clock = prove
 (`!s (t:(C,FFI)clos_state) k.
     clos_ticksProof_state_rel (clos_state_clock_fupd (K k) s)
                               (clos_state_clock_fupd (K k) t) <=>
     clos_ticksProof_state_rel s (clos_state_clock_fupd (K (clos_state_clock s)) t)`,
  REWRITE_TAC[clos_ticksProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM]);;

(* HOL4: dest_closure_SOME_IMP *)
let clos_ticksProof_dest_closure_SOME_IMP = prove
 (`dest_closure max_app loc_opt f2 xs = SOME x ==>
   (?loc arg_env clo_env num_args e. f2 = clos_Closure loc arg_env clo_env num_args e) \/
   (?loc arg_env clo_env fns i. f2 = clos_Recclosure loc arg_env clo_env fns i)`,
  CASES_ON `f2:clos_v` THEN REWRITE_TAC[dest_closure_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "clos_v"] THEN MESON_TAC[]);;

(* HOL4: v_rel_IMP_v_to_bytes [local] *)
let clos_ticksProof_v_rel_IMP_v_to_bytes = prove
 (`clos_ticksProof_v_rel x y ==> clos_v_to_bytes y = clos_v_to_bytes x`,
  MESON_TAC[clos_ticksProof_simple_val_rel; clos_simple_val_rel_v_to_bytes]);;

(* HOL4: v_rel_IMP_v_to_words [local] *)
let clos_ticksProof_v_rel_IMP_v_to_words = prove
 (`clos_ticksProof_v_rel x y ==> clos_v_to_words y = clos_v_to_words x`,
  MESON_TAC[clos_ticksProof_simple_val_rel; clos_simple_val_rel_v_to_words]);;

(* HOL4: state_rel_opt_rel_refs [local] *)
let clos_ticksProof_state_rel_opt_rel_refs = prove
 (`(clos_ticksProof_state_rel (s1:(C,FFI)clos_state) s2 /\
    FLOOKUP (clos_state_refs s1) n = r1 ==>
    ?r2. FLOOKUP (clos_state_refs s2) n = r2 /\ OPTREL clos_ticksProof_ref_rel r1 r2) /\
   (clos_ticksProof_state_rel s1 s2 /\ FLOOKUP (clos_state_refs s2) n = r2 ==>
    ?r1. FLOOKUP (clos_state_refs s1) n = r1 /\ OPTREL clos_ticksProof_ref_rel r1 r2)`,
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[UNWIND_THM1] THEN
  ASM_SIMP_TAC[CLOSP2AUX_ticks_flookup_rel]);;

(* HOL4: state_rel_clock_eqs [local] *)
let state_rel_clock_eqs = prove
 (`clos_ticksProof_state_rel (s:(C,FFI)clos_state) t ==>
   clos_state_clock s = clos_state_clock t`,
  SIMP_TAC[clos_ticksProof_state_rel_def]);;

(* HOL4: state_rel_dec_clock [local] *)
let clos_ticksProof_state_rel_dec_clock = prove
 (`clos_ticksProof_state_rel (s1:(C,FFI)clos_state) s2 ==>
   clos_ticksProof_state_rel (clos_dec_clock 1 s1) (clos_dec_clock 1 s2)`,
  SIMP_TAC[clos_ticksProof_state_rel_def; clos_dec_clock_def; clos_state_INFO.ri_accfupds;
           K_THM]);;

(* a local helper: dest_thunk of related values agree on NotThunk *)
let CLOSP2AUX_ticks_not_thunk = prove
 (`!(s1:(C,FFI)clos_state) s2 x y.
     clos_ticksProof_state_rel s1 s2 /\ clos_ticksProof_v_rel x y ==>
     (clos_dest_thunk [x] (clos_state_refs s1) = clos_NotThunk <=>
      clos_dest_thunk [y] (clos_state_refs s2) = clos_NotThunk)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`clos_ticksProof_v_rel`;
                 `clos_ticksProof_state_rel:(C,FFI)clos_state->(C,FFI)clos_state->bool`;
                 `s1:(C,FFI)clos_state`; `s2:(C,FFI)clos_state`;
                 `x:clos_v`; `y:clos_v`; `Evaluated`] CLOSPROPSAUX_bad_thunk_rel) THEN
  ASM_REWRITE_TAC[clos_ticksProof_simple_val_rel; clos_ticksProof_simple_state_rel;
                  clos_bad_thunk_update_def] THEN
  MESON_TAC[]);;

(* HOL4: rel_update_thunk [local] *)
let clos_ticksProof_rel_update_thunk = prove
 (`clos_ticksProof_state_rel (s1:(C,FFI)clos_state) s2 /\
   ALL2 clos_ticksProof_v_rel vs ys ==>
   (clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s2) ys = NONE ==>
    clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s1) vs = NONE) /\
   (clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s2) ys = SOME refs2 ==>
    ?refs1. clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s1) vs = SOME refs1 /\
            clos_ticksProof_state_rel (clos_state_refs_fupd (K refs1) s1)
                                      (clos_state_refs_fupd (K refs2) s2))`,
  STRIP_TAC THEN
  SUBGOAL_THEN `(vs = [] /\ ys = []) \/
                (?x y. vs = [x] /\ ys = [y] /\ clos_ticksProof_v_rel x y) \/
                (?x1 x2 r1 y1 y2 r2. vs = CONS x1 (CONS x2 r1) /\
                                     ys = CONS y1 (CONS y2 r2))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ALL2 clos_ticksProof_v_rel vs ys` THEN
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
               CLOSP2AUX_ticks_not_thunk) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  ASM_CASES_TAC `clos_dest_thunk [y] (clos_state_refs (s2:(C,FFI)clos_state)) =
                 clos_NotThunk` THENL
   [SUBGOAL_THEN `clos_dest_thunk [x] (clos_state_refs (s1:(C,FFI)clos_state)) =
                  clos_NotThunk` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    SUBGOAL_THEN `~(clos_dest_thunk [x] (clos_state_refs (s1:(C,FFI)clos_state)) =
                    clos_NotThunk)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CLOSSEMAUX_dest_thunk_NONE; distinctness "option"]] THEN
  REWRITE_TAC[store_thunk_def] THEN
  MP_TAC(SPECL [`s1:(C,FFI)clos_state`; `s2:(C,FFI)clos_state`; `ptr:num`]
               CLOSP2AUX_ticks_flookup_rel) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (clos_state_refs (s1:(C,FFI)clos_state)) ptr` THEN
  CASES_ON `FLOOKUP (clos_state_refs (s2:(C,FFI)clos_state)) ptr` THEN
  REWRITE_TAC[OPTREL_THM; case_def "option"; distinctness "option"] THEN
  CASES_ON `a':(clos_v)clos_ref` THEN REWRITE_TAC[CLOSP2AUX_ticks_ref_rel_right] THEN
  STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[distinctness "option"] THEN
  TRY(CASES_ON `a0:thunk_mode` THEN CASE_REWRITE_TAC[]) THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[UNWIND_THM1] THEN
  MATCH_MP_TAC CLOSP2AUX_ticks_state_rel_refs_upd THEN
  ASM_REWRITE_TAC[CLOSP2AUX_ticks_ref_rel_right; injectivity "clos_ref"; UNWIND_THM1]);;

(* ------------------------------------------------------------------------- *)
(* The correctness of remove_ticks (HOL4: evaluate_remove_ticks), a         *)
(* backwards simulation with extra clock for the source.  It is proved by   *)
(* the induction of closProps (CLOSPROPSAUX_evaluate_ind) on the target     *)
(* evaluation, with one lemma per case.  Local helpers: the Ticks of a      *)
(* source expression are absorbed by its extra clock (CLOSP2AUX_ticks_lift); *)
(* a source sub-evaluation that does not time out is shifted to a larger    *)
(* clock (CLOSP2AUX_ticks_add) after the existential clock of the goal is   *)
(* split (BASICAUX_EX_ADD), so the source is evaluated step by     *)
(* step along the target (HOL4: qexists_tac `ck + ck'` with                  *)
(* evaluate_add_clock).                                                      *)
(* ------------------------------------------------------------------------- *)

let CLOSP2AUX_ticks_lift = prove
 (`!ts e env1 (s1:(C,FFI)clos_state) res2 t2.
     (?ck res1 s2.
        clos_evaluate ([e],env1,clos_state_clock_fupd (K (clos_state_clock s1 + ck)) s1) =
        (res1,s2) /\
        result_rel (ALL2 clos_ticksProof_v_rel) clos_ticksProof_v_rel res1 res2 /\
        clos_ticksProof_state_rel s2 t2) ==>
     (?ck res1 s2.
        clos_evaluate ([clos_ticksProof_mk_Ticks ts e],env1,
                       clos_state_clock_fupd (K (clos_state_clock s1 + ck)) s1) =
        (res1,s2) /\
        result_rel (ALL2 clos_ticksProof_v_rel) clos_ticksProof_v_rel res1 res2 /\
        clos_ticksProof_state_rel s2 t2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ck + LENGTH (ts:tra list)` THEN
  REWRITE_TAC[evaluate_mk_Ticks; clos_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[ARITH_RULE `~(c + ck + n < n:num)`] THEN
  REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM;
              clos_state_INFO.ri_fupdfupds; K_o_THM;
              ARITH_RULE `(c + ck + n) - n:num = c + ck`] THEN
  ASM_MESON_TAC[]);;

let CLOSP2AUX_ticks_add = prove
 (`!xs env (s:(C,FFI)clos_state) ck1 r u.
     clos_evaluate (xs,env,clos_state_clock_fupd (K (clos_state_clock s + ck1)) s) = (r,u) /\
     ~(r = Rerr (Rabort Rtimeout_error)) ==>
     !ck2. clos_evaluate (xs,env,clos_state_clock_fupd (K (clos_state_clock s + ck1 + ck2)) s) =
           (r,clos_state_clock_fupd (K (clos_state_clock u + ck2)) u)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP clos_evaluate_add_clock) THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; clos_state_INFO.ri_fupdfupds; K_o_THM; K_THM;
              ADD_ASSOC]);;

let CLOSP2AUX_ticks_ind =
  let p = `\ys env2 (t1:(C,FFI)clos_state).
     !res2 t2 env1 s1 xs.
       clos_evaluate (ys,env2,t1) = (res2,t2) /\
       ALL2 clos_ticksProof_v_rel env1 env2 /\
       clos_ticksProof_state_rel s1 t1 /\ clos_ticksProof_code_rel xs ys ==>
       ?ck res1 s2.
         clos_evaluate (xs,env1,clos_state_clock_fupd (K (clos_state_clock s1 + ck)) s1) =
         (res1,s2) /\
         result_rel (ALL2 clos_ticksProof_v_rel) clos_ticksProof_v_rel res1 res2 /\
         clos_ticksProof_state_rel s2 t2`
  and q = `\loc_opt f2 args2 (t1:(C,FFI)clos_state).
     !res2 t2 f1 args1 s1.
       evaluate_app loc_opt f2 args2 t1 = (res2,t2) /\
       clos_ticksProof_v_rel f1 f2 /\ ALL2 clos_ticksProof_v_rel args1 args2 /\
       clos_ticksProof_state_rel s1 t1 ==>
       ?ck res1 s2.
         evaluate_app loc_opt f1 args1
           (clos_state_clock_fupd (K (clos_state_clock s1 + ck)) s1) = (res1,s2) /\
         result_rel (ALL2 clos_ticksProof_v_rel) clos_ticksProof_v_rel res1 res2 /\
         clos_ticksProof_state_rel s2 t2` in
  CONV_RULE (DEPTH_CONV BETA_CONV) (ISPECL [p;q] CLOSPROPSAUX_evaluate_ind);;
let CLOSP2AUX_ticks_cases = conjuncts (lhand (concl CLOSP2AUX_ticks_ind));;

(* local helpers: the sources of empty and singleton targets *)
let CLOSP2AUX_ticks_code_nil = prove
 (`!xs. clos_ticksProof_code_rel xs [] <=> xs = []`,
  GEN_TAC THEN REWRITE_TAC[clos_ticksProof_code_rel_def] THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SYM o AP_TERM `LENGTH:clos_exp list->num`) THEN
    REWRITE_TAC[clos_ticks_LENGTH_remove_ticks; LENGTH; LENGTH_EQ_NIL];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[clos_ticks_remove_ticks_def]]);;

let CLOSP2AUX_ticks_code_sing = prove
 (`!xs y. clos_ticksProof_code_rel xs [y] <=>
          ?x. xs = [x] /\ [y] = clos_ticks_remove_ticks [x]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_ticksProof_code_rel_def] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o SYM o AP_TERM `LENGTH:clos_exp list->num`) THEN
  REWRITE_TAC[clos_ticks_LENGTH_remove_ticks; LENGTH; ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  STRIP_TAC THEN EXISTS_TAC `h:clos_exp` THEN ASM_MESON_TAC[]);;

(* the source of a singleton target: strip its Ticks (HOL4: imp_res_tac    *)
(* remove_ticks_X_IMP_mk_Ticks \\ rveq \\ simp [evaluate_mk_Ticks])          *)
let CLOSP2AUX_TICKS_SRC_TAC (imp:thm) : tactic =
  FIRST_X_ASSUM(MP_TAC o check (CLOSPROPSAUX_is_app "clos_ticksProof_code_rel" o concl)) THEN
  REWRITE_TAC[CLOSP2AUX_ticks_code_sing] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:clos_exp`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (STRIP_ASSUME_TAC o MATCH_MP imp))) THEN
  RVEQ_TAC THEN
  MATCH_MP_TAC CLOSP2AUX_ticks_lift;;

(* local helpers: Boolv tests of related values; the three shapes of      *)
(* related results; the not-timeout facts of the shifted evaluations       *)
let CLOSP2AUX_ticks_Boolv_HD = prove
 (`!a' a b. ALL2 clos_ticksProof_v_rel a' a ==>
            (clos_Boolv b = HD a' <=> clos_Boolv b = HD a)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[HD] THEN
  REWRITE_TAC[clos_Boolv_def] THEN
  UNDISCH_TAC `clos_ticksProof_v_rel h h'` THEN
  GEN_REWRITE_TAC LAND_CONV [clos_ticksProof_v_rel_cases] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_NIL]) THEN
  EQ_TAC THEN STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_NIL]) THEN
  ASM_MESON_TAC[LIST_REL_NIL]);;

let CLOSP2AUX_ticks_res_cases = prove
 (`!r rr. result_rel (ALL2 clos_ticksProof_v_rel) clos_ticksProof_v_rel r rr ==>
          (?a a'. rr = Rval a /\ r = Rval a' /\ ALL2 clos_ticksProof_v_rel a' a) \/
          (?v v'. rr = Rerr (Rraise v) /\ r = Rerr (Rraise v') /\
                  clos_ticksProof_v_rel v' v) \/
          (?ab. rr = Rerr (Rabort ab) /\ r = Rerr (Rabort ab))`,
  REPEAT GEN_TAC THEN
  CASES_ON `rr:(clos_v list,clos_v)result` THEN
  REWRITE_TAC[clos_result_rel_Rval2; result_rel_Rerr2; injectivity "result";
              distinctness "result"] THENL [MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `a:(clos_v)error_result` THEN
  REWRITE_TAC[exc_rel_raise2; exc_rel_type_error2; injectivity "error_result";
              distinctness "error_result"] THEN MESON_TAC[]);;

let CLOSP2AUX_ticks_not_timeout = prove
 (`(!a:clos_v list. ~(Rval a:(clos_v list,clos_v)result = Rerr (Rabort Rtimeout_error))) /\
   (!v:clos_v. ~(Rerr (Rraise v):(clos_v list,clos_v)result = Rerr (Rabort Rtimeout_error)))`,
  REWRITE_TAC[distinctness "result"; injectivity "result"; distinctness "error_result"]);;

let CLOSP2AUX_ticks_add_app = prove
 (`!lo f args (s:(C,FFI)clos_state) ck1 r u.
     evaluate_app lo f args (clos_state_clock_fupd (K (clos_state_clock s + ck1)) s) = (r,u) /\
     ~(r = Rerr (Rabort Rtimeout_error)) ==>
     !ck2. evaluate_app lo f args
             (clos_state_clock_fupd (K (clos_state_clock s + ck1 + ck2)) s) =
           (r,clos_state_clock_fupd (K (clos_state_clock u + ck2)) u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  MP_TAC(SPECL [`lo:num option`; `f:clos_v`; `args:clos_v list`;
    `clos_state_clock_fupd (K (clos_state_clock (s:(C,FFI)clos_state) + ck1)) s`;
    `r:(clos_v list,clos_v)result`; `u:(C,FFI)clos_state`; `ck2:num`]
    (CONJUNCT2 CLOSPROPSAUX_evaluate_add_to_clock)) THEN
  ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; clos_state_INFO.ri_fupdfupds; K_o_THM; K_THM;
                  ADD_ASSOC]);;

let CLOSP2AUX_ticks_disch_shift = prove
 (`!ck1 A (P:num->bool). (A ==> ?ck. P (ck1 + ck)) ==> (A ==> ?ck. P ck)`,
  MESON_TAC[]);;

(* local tactics of the case lemmas.                                        *)
(*   NAME_TAC   name the first target evaluation of the goal's antecedent    *)
(*   COND_IH_TAC  resolve the conditional induction hypotheses              *)
(*   IH_TAC     apply an induction hypothesis to the newest named target     *)
(*              evaluation: the source evaluation, related result and state *)
(*   SPLIT_TAC  split the related results (Rval, Rraise, Rabort)             *)
(*   SHIFT_TAC  step the source evaluation of the goal past the new source   *)
(*              evaluation (HOL4: qexists_tac `ck + ck'` \\ evaluate_add_clock) *)
(*   FIN_TAC    finish when the source result is known                       *)

let CLOSP2AUX_ticks_counter = ref 0;;

let CLOSP2AUX_ticks_is_eval t =
  (CLOSPROPSAUX_is_app "clos_evaluate" t && is_comb t) ||
  (CLOSPROPSAUX_is_app "evaluate_app" t && length (snd (strip_comb t)) = 4);;

let CLOSP2AUX_ticks_is_P th =
  let c = snd(strip_forall(concl th)) in
  is_imp c && is_conj (lhand c) &&
  (let a = lhand (lhand c) in
   is_eq a && CLOSP2AUX_ticks_is_eval (lhs a) && is_pair (rhs a) &&
   is_var (fst (dest_pair (rhs a))));;

let CLOSP2AUX_TICKS_COND_IH_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let mentions_eval t = can (find_term CLOSP2AUX_ticks_is_eval) t in
  let is_cond_ih th =
    not (CLOSP2AUX_ticks_is_P th) &&
    (let c = snd(strip_forall(concl th)) in
     is_imp c && mentions_eval (rand c) && is_forall (rand c)) in
  let cihs = filter is_cond_ih asms in
  let rec resolve depth th =
    if CLOSP2AUX_ticks_is_P th then [th]
    else if depth = 0 then [] else
    let rs = mapfilter (fun a -> MATCH_MP th a) asms in
    flat (map (resolve (depth-1)) rs) in
  let res = flat (map (fun th -> resolve 4 (CLOSPROPSAUX_curry_top th)) cihs) in
  let res = filter (fun th -> not (exists (fun a -> aconv (concl a) (concl th)) asms)) res in
  MAP_EVERY ASSUME_TAC res gl;;

(* the evaluations of a term that are not under a binder of their variables *)
let rec CLOSP2AUX_ticks_find_closed bvs tm =
  (if CLOSP2AUX_ticks_is_eval tm && not (exists (fun v -> vfree_in v tm) bvs)
   then [tm] else []) @
  (match tm with
     Comb(f,x) -> CLOSP2AUX_ticks_find_closed bvs f @ CLOSP2AUX_ticks_find_closed bvs x
   | Abs(v,b) -> CLOSP2AUX_ticks_find_closed (v::bvs) b
   | _ -> []);;

(* all subterms that are not under a binder of their variables *)
let rec CLOSP2AUX_ticks_find_closed_any bvs tm =
  (if not (exists (fun v -> vfree_in v tm) bvs) then [tm] else []) @
  (match tm with
     Comb(f,x) -> CLOSP2AUX_ticks_find_closed_any bvs f @
                  CLOSP2AUX_ticks_find_closed_any bvs x
   | Abs(v,b) -> CLOSP2AUX_ticks_find_closed_any (v::bvs) b
   | _ -> []);;

let CLOSP2AUX_TICKS_NAME_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w in
  let named = mapfilter (fun (_,th) -> lhs (concl th)) asl in
  let evs = filter (fun t -> not (mem t named)) (CLOSP2AUX_ticks_find_closed [] ant) in
  let tm = hd evs in
  let ty = type_of tm in
  let rty,sty = (match dest_type ty with (_,[a;b]) -> a,b | _ -> failwith "NAME") in
  incr CLOSP2AUX_ticks_counter;
  let k = string_of_int (!CLOSP2AUX_ticks_counter) in
  let r = mk_var("rr" ^ k, rty) and s = mk_var("tt" ^ k, sty) in
  (MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN r (X_CHOOSE_THEN s ASSUME_TAC)) THEN
   POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
   CASE_REWRITE_TAC[]) gl;;

(* the code_rel antecedent of an induction hypothesis *)
let CLOSP2AUX_ticks_code_disch (asl:thm list) (th:thm) : thm =
  try tryfind (fun a -> MATCH_MP th a) asl with Failure _ ->
  let xs,bod = dest_forall (concl th) in
  let x = rand (lhand bod) in
  try let eq = find (fun a -> let c = concl a in
                       is_eq c && lhs c = x &&
                       CLOSPROPSAUX_is_app "clos_ticks_remove_ticks" (rhs c)) asl in
      let src = rand (rhs (concl eq)) in
      MP (SPEC src th) (EQ_MP (SYM (SPECL [src; x] clos_ticksProof_code_rel_def)) eq)
  with Failure _ ->
  let src =
    if CLOSPROPSAUX_is_app "clos_ticks_remove_ticks" x then rand x else
    (try (match dest_list x with
            [h] when CLOSPROPSAUX_is_app "HD" h &&
                     CLOSPROPSAUX_is_app "clos_ticks_remove_ticks" (rand h) -> rand (rand h)
          | _ -> x)
     with Failure _ -> x) in
  let th1 = SPEC src th in
  MP th1 (EQT_ELIM (REWRITE_CONV[clos_ticksProof_code_rel_def; HD_remove_ticks_SING;
                                 clos_ticks_remove_ticks_def; clos_AppUnit_def; HD]
                                (lhand (concl th1))));;

let CLOSP2AUX_ticks_apply (asl:thm list) (ih:thm) (ev:thm) : thm =
  let th1 = MATCH_MP (REWRITE_RULE[IMP_CONJ] ih) ev in
  let rec disch th =
    let vs,bod = strip_forall (concl th) in
    if not (is_imp bod) then th else
    let ant = lhand bod in
    if CLOSPROPSAUX_is_app "clos_ticksProof_code_rel" ant
    then CLOSP2AUX_ticks_code_disch asl th
    else disch (tryfind (fun a -> MATCH_MP th a) asl) in
  disch th1;;

let CLOSP2AUX_TICKS_IH_TAC : tactic = fun (asl,w as gl) ->
  let ev = snd (hd asl) in
  let asms = map snd asl in
  let ihs = filter CLOSP2AUX_ticks_is_P asms in
  let res = mapfilter (fun ih -> CLOSP2AUX_ticks_apply asms ih ev) ihs in
  if res = [] then failwith "CLOSP2AUX_TICKS_IH_TAC" else
  let th = hd res in
  let k = string_of_int (!CLOSP2AUX_ticks_counter) in
  let v1,b1 = dest_exists (concl th) in
  let v2,b2 = dest_exists b1 in
  let v3,_ = dest_exists b2 in
  let ck = mk_var("ck" ^ k, type_of v1) and r = mk_var("rs" ^ k, type_of v2)
  and u = mk_var("us" ^ k, type_of v3) in
  X_CHOOSE_THEN ck (X_CHOOSE_THEN r (X_CHOOSE_THEN u STRIP_ASSUME_TAC)) th gl;;

let CLOSP2AUX_TICKS_SPLIT_TAC : tactic = fun (asl,w as gl) ->
  let k = string_of_int (!CLOSP2AUX_ticks_counter) in
  let rr = mk_var("rr" ^ k, `:(clos_v list,clos_v)result`) in
  let va = mk_var("va" ^ k, `:clos_v list`) and sa = mk_var("sa" ^ k, `:clos_v list`)
  and vv = mk_var("vv" ^ k, `:clos_v`) and sv = mk_var("sv" ^ k, `:clos_v`)
  and ab = mk_var("ab" ^ k, `:abort`) in
  (FIRST_X_ASSUM(fun th ->
     if CLOSPROPSAUX_is_app "result_rel" (concl th) && rand (concl th) = rr
     then DISJ_CASES_THEN2 (X_CHOOSE_THEN va (X_CHOOSE_THEN sa STRIP_ASSUME_TAC))
            (DISJ_CASES_THEN2 (X_CHOOSE_THEN vv (X_CHOOSE_THEN sv STRIP_ASSUME_TAC))
                              (X_CHOOSE_THEN ab STRIP_ASSUME_TAC))
            (MATCH_MP CLOSP2AUX_ticks_res_cases th)
     else NO_TAC) THEN
   RVEQ_TAC THEN CASE_REWRITE_TAC[]) gl;;

let CLOSP2AUX_TICKS_SHIFT_TAC : tactic = fun (asl,w as gl) ->
  let k = string_of_int (!CLOSP2AUX_ticks_counter) in
  let ck = mk_var("ck" ^ k, `:num`) in
  let esrc = find (fun th -> let c = concl th in is_eq c &&
                     CLOSP2AUX_ticks_is_eval (lhs c) && free_in ck (lhs c)) (map snd asl) in
  let r = fst (dest_pair (rhs (concl esrc))) in
  let is_abort = CLOSPROPSAUX_is_app "Rerr" r && CLOSPROPSAUX_is_app "Rabort" (rand r) in
  if is_abort then
    (DISCH_TAC THEN EXISTS_TAC ck THEN POP_ASSUM MP_TAC THEN
     REWRITE_TAC[esrc] THEN CASE_REWRITE_TAC[]) gl
  else
    let nt = EQT_ELIM (REWRITE_CONV[CLOSP2AUX_ticks_not_timeout]
                        (mk_neg (mk_eq (r, `Rerr (Rabort Rtimeout_error):(clos_v list,clos_v)result`)))) in
    let add = if CLOSPROPSAUX_is_app "clos_evaluate" (lhs (concl esrc))
              then CLOSP2AUX_ticks_add else CLOSP2AUX_ticks_add_app in
    (MATCH_MP_TAC (SPEC ck CLOSP2AUX_ticks_disch_shift) THEN
     REWRITE_TAC[MATCH_MP add (CONJ esrc nt)] THEN CASE_REWRITE_TAC[]) gl;;

(* the relation of the environment of the newest named target evaluation *)
let CLOSP2AUX_ticks_all2_cons = prove
 (`!h1 h2 t1 t2. clos_ticksProof_v_rel h1 h2 /\ ALL2 clos_ticksProof_v_rel t1 t2 ==>
                 ALL2 clos_ticksProof_v_rel (CONS h1 t1) (CONS h2 t2)`,
  REWRITE_TAC[ALL2]);;

let CLOSP2AUX_ticks_all2_append = ISPEC `clos_ticksProof_v_rel` EVERY2_APPEND_suff;;

let CLOSP2AUX_ticks_all2_nil = prove
 (`ALL2 clos_ticksProof_v_rel [] []`,
  REWRITE_TAC[ALL2]);;

let rec CLOSP2AUX_ticks_env (asl:thm list) (e:term) : thm =
  try find (fun th -> let c = concl th in
              CLOSPROPSAUX_is_app "ALL2" c && rand c = e &&
              rator (rator c) = `ALL2 clos_ticksProof_v_rel`) asl
  with Failure _ ->
  if CLOSPROPSAUX_is_app "APPEND" e then
    MATCH_MP CLOSP2AUX_ticks_all2_append
      (CONJ (CLOSP2AUX_ticks_env asl (lhand e)) (CLOSP2AUX_ticks_env asl (rand e)))
  else if is_cons e then
    let h,t = dest_cons e in
    let vh = find (fun th -> let c = concl th in
                     CLOSPROPSAUX_is_app "clos_ticksProof_v_rel" c && rand c = h) asl in
    MATCH_MP CLOSP2AUX_ticks_all2_cons (CONJ vh (CLOSP2AUX_ticks_env asl t))
  else if e = `[]:clos_v list` then CLOSP2AUX_ticks_all2_nil
  else failwith "CLOSP2AUX_ticks_env";;

let CLOSP2AUX_TICKS_ENV_TAC : tactic = fun (asl,w as gl) ->
  let ev = concl (snd (hd asl)) in
  let l = lhs ev in
  if not (CLOSPROPSAUX_is_app "clos_evaluate" l) then ALL_TAC gl else
  let e = fst (dest_pair (snd (dest_pair (rand l)))) in
  let asms = map snd asl in
  let th = CLOSP2AUX_ticks_env asms e in
  if exists (fun a -> concl a = concl th) asms then ALL_TAC gl
  else (ASSUME_TAC th THEN
        (fun (asl,w) -> match asl with
             a::b::rest -> ALL_TAC (b::a::rest,w)
           | _ -> ALL_TAC (asl,w))) gl;;

let CLOSP2AUX_TICKS_STEP_TAC : tactic =
  CLOSP2AUX_TICKS_COND_IH_TAC THEN CLOSP2AUX_TICKS_NAME_TAC THEN
  TRY CLOSP2AUX_TICKS_ENV_TAC THEN CLOSP2AUX_TICKS_IH_TAC THEN
  CLOSP2AUX_TICKS_SPLIT_TAC THEN CLOSP2AUX_TICKS_SHIFT_TAC;;

let CLOSP2AUX_TICKS_SING_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && CLOSPROPSAUX_is_app "clos_evaluate" (lhs c) &&
       is_pair (rhs c) &&
       (let r = fst(dest_pair(rhs c)) in CLOSPROPSAUX_is_app "Rval" r && is_var (rand r)) &&
       (let xs = fst(dest_pair(rand(lhs c))) in
        is_list xs && length (dest_list xs) = 1)
    then (STRIP_ASSUME_TAC(MATCH_MP clos_evaluate_SING th) THEN ASSUME_TAC th)
    else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_var (lhs (concl th)) &&
                              is_cons (rhs (concl th)) then SUBST_ALL_TAC th else NO_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if CLOSPROPSAUX_is_app "ALL2" c && is_cons (lhand c) && is_cons (rand c)
    then MP_TAC th THEN REWRITE_TAC[ALL2] THEN STRIP_TAC else NO_TAC));;

let CLOSP2AUX_TICKS_FIN_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  TRY (EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock]) THEN
  REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC] THEN CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  CLOSP2AUX_TICKS_SING_TAC THEN
  ASM_REWRITE_TAC[result_rel_def; exc_rel_def; injectivity "result"; distinctness "result";
                  ALL2; HD];;


let CLOSP2AUX_TICKS_INTRO_TAC : tactic =
  REPEAT GEN_TAC THEN
  (fun (asl,w as gl) ->
     if is_imp w && is_forall (rand w)
     then (DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN REPEAT GEN_TAC) gl
     else ALL_TAC gl) THEN
  STRIP_TAC;;

let CLOSP2AUX_TICKS_UNFOLD_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
                                CLOSP2AUX_ticks_is_eval (lhs (concl th)) &&
                                is_var (fst (dest_pair (rhs (concl th)))))) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN CASE_REWRITE_TAC[];;

let CLOSP2AUX_ticks_nil = prove
 (el 0 CLOSP2AUX_ticks_cases,
  CLOSP2AUX_TICKS_INTRO_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSPROPSAUX_is_app "clos_ticksProof_code_rel" o concl)) THEN
  REWRITE_TAC[CLOSP2AUX_ticks_code_nil] THEN DISCH_THEN SUBST1_TAC THEN
  CLOSP2AUX_TICKS_UNFOLD_TAC THEN CLOSP2AUX_TICKS_FIN_TAC);;

let CLOSP2AUX_ticks_code_cons2 = prove
 (`!xs0 y1 y2 ys. clos_ticksProof_code_rel xs0 (CONS y1 (CONS y2 ys)) <=>
     ?x1 x2 xs. xs0 = CONS x1 (CONS x2 xs) /\ clos_ticksProof_code_rel [x1] [y1] /\
                clos_ticksProof_code_rel (CONS x2 xs) (CONS y2 ys)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP clos_ticksProof_code_rel_IMP_LENGTH) THEN
    POP_ASSUM MP_TAC THEN
    STRUCT_CASES_TAC(ISPEC `xs0:clos_exp list` list_CASES) THEN
    REWRITE_TAC[LENGTH; NOT_SUC; ARITH_RULE `~(0 = SUC n)`] THEN
    STRUCT_CASES_TAC(ISPEC `t:clos_exp list` list_CASES) THEN
    REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; ARITH_RULE `~(0 = SUC n)`] THEN
    REWRITE_TAC[clos_ticksProof_code_rel_CONS_CONS] THEN MESON_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[clos_ticksProof_code_rel_CONS_CONS]]);;

let CLOSP2AUX_ticks_cons = prove
 (el 1 CLOSP2AUX_ticks_cases,
  CLOSP2AUX_TICKS_INTRO_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSPROPSAUX_is_app "clos_ticksProof_code_rel" o concl)) THEN
  REWRITE_TAC[CLOSP2AUX_ticks_code_cons2] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CLOSP2AUX_TICKS_UNFOLD_TAC THEN
  REPEAT CLOSP2AUX_TICKS_STEP_TAC THEN CLOSP2AUX_TICKS_FIN_TAC);;

let CLOSP2AUX_ticks_var = prove
 (el 2 CLOSP2AUX_ticks_cases,
  CLOSP2AUX_TICKS_INTRO_TAC THEN CLOSP2AUX_TICKS_SRC_TAC remove_ticks_Var_IMP_mk_Ticks THEN
  CLOSP2AUX_TICKS_UNFOLD_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH o
              check (CLOSPROPSAUX_is_app "ALL2" o concl)) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN CLOSP2AUX_TICKS_FIN_TAC THEN
  ASM_MESON_TAC[LIST_REL_EL_EQN]);;

(* rewrite the Boolv tests of source values to those of the target values *)
let CLOSP2AUX_TICKS_BOOLV_TAC : tactic =
  ASSUM_LIST(fun l -> REWRITE_TAC(mapfilter (MATCH_MP CLOSP2AUX_ticks_Boolv_HD) l));;

let CLOSP2AUX_ticks_if = prove
 (el 3 CLOSP2AUX_ticks_cases,
  CLOSP2AUX_TICKS_INTRO_TAC THEN CLOSP2AUX_TICKS_SRC_TAC remove_ticks_If_IMP_mk_Ticks THEN
  CLOSP2AUX_TICKS_UNFOLD_TAC THEN CLOSP2AUX_TICKS_STEP_TAC THENL
   [ALL_TAC; CLOSP2AUX_TICKS_FIN_TAC; CLOSP2AUX_TICKS_FIN_TAC] THEN
  CLOSP2AUX_TICKS_BOOLV_TAC THEN REPEAT COND_CASES_TAC THEN
  REPEAT CLOSP2AUX_TICKS_STEP_TAC THEN CLOSP2AUX_TICKS_FIN_TAC);;

let CLOSP2AUX_ticks_let = prove
 (el 4 CLOSP2AUX_ticks_cases,
  CLOSP2AUX_TICKS_INTRO_TAC THEN CLOSP2AUX_TICKS_SRC_TAC remove_ticks_Let_IMP_mk_Ticks THEN
  CLOSP2AUX_TICKS_UNFOLD_TAC THEN
  REPEAT CLOSP2AUX_TICKS_STEP_TAC THEN CLOSP2AUX_TICKS_FIN_TAC);;

let CLOSP2AUX_ticks_raise = prove
 (el 5 CLOSP2AUX_ticks_cases,
  CLOSP2AUX_TICKS_INTRO_TAC THEN CLOSP2AUX_TICKS_SRC_TAC remove_ticks_Raise_IMP_mk_Ticks THEN
  CLOSP2AUX_TICKS_UNFOLD_TAC THEN
  REPEAT CLOSP2AUX_TICKS_STEP_TAC THEN CLOSP2AUX_TICKS_FIN_TAC);;

let CLOSP2AUX_ticks_handle = prove
 (el 6 CLOSP2AUX_ticks_cases,
  CLOSP2AUX_TICKS_INTRO_TAC THEN CLOSP2AUX_TICKS_SRC_TAC remove_ticks_Handle_IMP_mk_Ticks THEN
  CLOSP2AUX_TICKS_UNFOLD_TAC THEN
  REPEAT CLOSP2AUX_TICKS_STEP_TAC THEN CLOSP2AUX_TICKS_FIN_TAC);;

(* local helpers for the Op case: dest_thunk, do_install and do_app of     *)
(* related values, seen from the target (HOL4: oneline dest_thunk_def,      *)
(* do_install_lemma, do_install_add_to_clock, do_app_lemma)                 *)

let CLOSP2AUX_ticks_RefPtr_shape = prove
 (`!xs ys.
     ALL2 clos_ticksProof_v_rel xs ys ==>
     (?b ptr. xs = [clos_RefPtr b ptr] /\ ys = [clos_RefPtr b ptr]) \/
     ((!b ptr. ~(xs = [clos_RefPtr b ptr])) /\ (!b ptr. ~(ys = [clos_RefPtr b ptr])))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `?b ptr. ys = [clos_RefPtr b ptr]` THENL
   [DISJ1_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `b:bool` (X_CHOOSE_THEN `ptr:num` SUBST_ALL_TAC)) THEN
    UNDISCH_TAC `ALL2 clos_ticksProof_v_rel xs [clos_RefPtr b ptr]` THEN
    REWRITE_TAC[LIST_REL_CONS2; LIST_REL_NIL; clos_ticksProof_v_rel_simps] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[CONS_11] THEN MESON_TAC[];
    DISJ2_TAC THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `ALL2 clos_ticksProof_v_rel [clos_RefPtr b ptr] ys` THEN
      REWRITE_TAC[LIST_REL_CONS1; LIST_REL_NIL] THEN STRIP_TAC THEN
      UNDISCH_TAC `clos_ticksProof_v_rel (clos_RefPtr b ptr) h'` THEN
      GEN_REWRITE_TAC LAND_CONV [clos_ticksProof_v_rel_cases] THEN
      REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"] THEN
      STRIP_TAC THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]]]);;

let CLOSP2AUX_ticks_dest_thunk_rel = prove
 (CASE_TERM `!(s:(C,FFI)clos_state) t xs ys.
     clos_ticksProof_state_rel s t /\ ALL2 clos_ticksProof_v_rel xs ys ==>
     match clos_dest_thunk ys (clos_state_refs t) with
       clos_BadRef -> clos_dest_thunk xs (clos_state_refs s) = clos_BadRef
     | clos_NotThunk -> clos_dest_thunk xs (clos_state_refs s) = clos_NotThunk
     | clos_IsThunk m w -> ?v. clos_dest_thunk xs (clos_state_refs s) = clos_IsThunk m v /\
                              clos_ticksProof_v_rel v w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`xs:clos_v list`; `ys:clos_v list`] CLOSP2AUX_ticks_RefPtr_shape) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[CLOSSEMAUX_dest_thunk_NotThunk] THEN CASE_REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[clos_dest_thunk_def] THEN
  MP_TAC(SPECL [`s:(C,FFI)clos_state`; `t:(C,FFI)clos_state`; `ptr:num`]
               CLOSP2AUX_ticks_flookup_rel) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (clos_state_refs (t:(C,FFI)clos_state)) ptr` THEN
  CASES_ON `FLOOKUP (clos_state_refs (s:(C,FFI)clos_state)) ptr` THEN
  REWRITE_TAC[OPTREL_THM] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a:(clos_v)clos_ref` THEN REWRITE_TAC[CLOSP2AUX_ticks_ref_rel_right] THEN
  STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a0:thunk_mode` THEN CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "clos_dest_thunk_ret"] THEN
  ASM_MESON_TAC[]);;

let CLOSP2AUX_ticks_do_install = prove
 (`!(s:(C,FFI)clos_state) t xs ys.
     clos_ticksProof_state_rel s t /\ ALL2 clos_ticksProof_v_rel xs ys ==>
     (!err2 t1. clos_do_install ys t = (Rerr err2,t1) ==>
        ?err1 s1. clos_do_install xs s = (Rerr err1,s1) /\
                  exc_rel clos_ticksProof_v_rel err1 err2 /\
                  clos_ticksProof_state_rel s1 t1) /\
     (!exps2 t1. clos_do_install ys t = (Rval exps2,t1) ==>
        ?exps1 s1.
          (!ck. clos_do_install xs
                  (clos_state_clock_fupd (K (clos_state_clock s + ck)) s) =
                (Rval exps1,clos_state_clock_fupd (K (clos_state_clock s1 + ck)) s1)) /\
          clos_ticksProof_state_rel s1 t1 /\ ~(exps1 = []) /\
          clos_ticksProof_code_rel exps1 exps2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP clos_ticksProof_do_install_lemma) THEN
  MP_TAC(ISPEC `clos_do_install xs (s:(C,FFI)clos_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(clos_exp list,clos_v)result`
    (X_CHOOSE_THEN `s1:(C,FFI)clos_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `r:(clos_exp list,clos_v)result` THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[do_install_add_to_clock]);;

let CLOSP2AUX_ticks_do_app = prove
 (`!(s:(C,FFI)clos_state) t xs ys opp.
     clos_ticksProof_state_rel s t /\ ALL2 clos_ticksProof_v_rel xs ys ==>
     (!err2. clos_do_app opp ys t = Rerr err2 ==>
        ?err1. clos_do_app opp xs s = Rerr err1 /\ exc_rel clos_ticksProof_v_rel err1 err2) /\
     (!y t1. clos_do_app opp ys t = Rval (y,t1) ==>
        ?x s1. clos_do_app opp xs s = Rval (x,s1) /\ clos_ticksProof_v_rel x y /\
               clos_ticksProof_state_rel s1 t1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP clos_ticksProof_do_app_lemma) THEN
  CASES_ON `clos_do_app opp ys (t:(C,FFI)clos_state)` THEN CASE_REWRITE_TAC[] THEN
  TRY(CASES_ON `a:clos_v#(C,FFI)clos_state` THEN CASE_REWRITE_TAC[]) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  MESON_TAC[]);;

(* case splits of the Op case, seen from the target *)
let CLOSP2AUX_ticks_do_install_cases = prove
 (`!(s:(C,FFI)clos_state) t xs ys.
     clos_ticksProof_state_rel s t /\ ALL2 clos_ticksProof_v_rel xs ys ==>
     (?err2 t1 err1 s1. clos_do_install ys t = (Rerr err2,t1) /\
                        clos_do_install xs s = (Rerr err1,s1) /\
                        exc_rel clos_ticksProof_v_rel err1 err2 /\
                        clos_ticksProof_state_rel s1 t1) \/
     (?exps2 t1 exps1 s1.
        clos_do_install ys t = (Rval exps2,t1) /\
        (!ck. clos_do_install xs (clos_state_clock_fupd (K (clos_state_clock s + ck)) s) =
              (Rval exps1,clos_state_clock_fupd (K (clos_state_clock s1 + ck)) s1)) /\
        clos_ticksProof_state_rel s1 t1 /\ ~(exps1 = []) /\
        clos_ticksProof_code_rel exps1 exps2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CLOSP2AUX_ticks_do_install) THEN
  MP_TAC(ISPEC `clos_do_install ys (t:(C,FFI)clos_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(clos_exp list,clos_v)result`
    (X_CHOOSE_THEN `t1:(C,FFI)clos_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN
  CASES_ON `r:(clos_exp list,clos_v)result` THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"] THEN MESON_TAC[]);;

let CLOSP2AUX_ticks_do_app_cases = prove
 (`!(s:(C,FFI)clos_state) t xs ys opp.
     clos_ticksProof_state_rel s t /\ ALL2 clos_ticksProof_v_rel xs ys ==>
     (?err2 err1. clos_do_app opp ys t = Rerr err2 /\ clos_do_app opp xs s = Rerr err1 /\
                  exc_rel clos_ticksProof_v_rel err1 err2) \/
     (?y t1 x s1. clos_do_app opp ys t = Rval (y,t1) /\ clos_do_app opp xs s = Rval (x,s1) /\
                  clos_ticksProof_v_rel x y /\ clos_ticksProof_state_rel s1 t1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `opp:clos_op` o MATCH_MP CLOSP2AUX_ticks_do_app) THEN
  CASES_ON `clos_do_app opp ys (t:(C,FFI)clos_state)` THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"] THENL
   [CASES_ON `a:clos_v#(C,FFI)clos_state` THEN REWRITE_TAC[PAIR_EQ]; ALL_TAC] THEN
  MESON_TAC[]);;

let CLOSP2AUX_ticks_dest_thunk_IsThunk = prove
 (`!xs (refs:(num,(clos_v)clos_ref)fmap) m v.
     clos_dest_thunk xs refs = clos_IsThunk m v ==> ?b ptr. xs = [clos_RefPtr b ptr]`,
  MESON_TAC[CLOSSEMAUX_dest_thunk_NotThunk; distinctness "clos_dest_thunk_ret"]);;

let CLOSP2AUX_ticks_dest_thunk_cases = prove
 (`!(s:(C,FFI)clos_state) t xs ys.
     clos_ticksProof_state_rel s t /\ ALL2 clos_ticksProof_v_rel xs ys ==>
     (clos_dest_thunk ys (clos_state_refs t) = clos_BadRef /\
      clos_dest_thunk xs (clos_state_refs s) = clos_BadRef) \/
     (clos_dest_thunk ys (clos_state_refs t) = clos_NotThunk /\
      clos_dest_thunk xs (clos_state_refs s) = clos_NotThunk) \/
     (?w v. clos_dest_thunk ys (clos_state_refs t) = clos_IsThunk Evaluated w /\
            clos_dest_thunk xs (clos_state_refs s) = clos_IsThunk Evaluated v /\
            clos_ticksProof_v_rel v w) \/
     (?w v b ptr. clos_dest_thunk ys (clos_state_refs t) = clos_IsThunk NotEvaluated w /\
            clos_dest_thunk xs (clos_state_refs s) = clos_IsThunk NotEvaluated v /\
            clos_ticksProof_v_rel v w /\
            ys = [clos_RefPtr b ptr] /\ xs = [clos_RefPtr b ptr])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CLOSP2AUX_ticks_dest_thunk_rel) THEN
  CASES_ON `clos_dest_thunk ys (clos_state_refs (t:(C,FFI)clos_state))` THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "clos_dest_thunk_ret"; injectivity "clos_dest_thunk_ret"] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:clos_v` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSP2AUX_ticks_dest_thunk_IsThunk o
    check (fun th -> is_eq (concl th) && lhand (lhs (concl th)) = `ys:clos_v list`)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSP2AUX_ticks_RefPtr_shape o CONJUNCT2) THEN
  ASM_REWRITE_TAC[CONS_11; injectivity "clos_v"] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `a0:thunk_mode` (cases "thunk_mode")) THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[distinctness "thunk_mode"] THEN ASM_MESON_TAC[]);;

let CLOSP2AUX_ticks_update_thunk_cases = prove
 (`!(s1:(C,FFI)clos_state) s2 vs ys v ptr.
     clos_ticksProof_state_rel s1 s2 /\ ALL2 clos_ticksProof_v_rel vs ys ==>
     (clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s2) ys = NONE /\
      clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s1) vs = NONE) \/
     (?refs1 refs2.
        clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s2) ys = SOME refs2 /\
        clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s1) vs = SOME refs1 /\
        clos_ticksProof_state_rel (clos_state_refs_fupd (K refs1) s1)
                                  (clos_state_refs_fupd (K refs2) s2))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs (s2:(C,FFI)clos_state)) ys` THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  ASM_MESON_TAC[clos_ticksProof_rel_update_thunk]);;

(* local tactics of the Op case: split a do_install, dest_thunk, do_app or  *)
(* update_thunk of the target (in the goal's antecedent) together with the  *)
(* source's, by the case lemmas above                                       *)
let CLOSP2AUX_ticks_rel_facts (asl:thm list) (ys:term) (t:term) : thm =
  let find_all2 l = find (fun th -> let c = concl th in
                      CLOSPROPSAUX_is_app "ALL2" c && rand c = l &&
                      rator (rator c) = `ALL2 clos_ticksProof_v_rel`) asl in
  let all2 = try find_all2 ys with Failure _ ->
             if CLOSPROPSAUX_is_app "REVERSE" ys
             then MATCH_MP EVERY2_REVERSE (find_all2 (rand ys))
             else failwith "CLOSP2AUX_ticks_rel_facts" in
  let sr = find (fun th -> let c = concl th in
                   CLOSPROPSAUX_is_app "clos_ticksProof_state_rel" c && rand c = t) asl in
  CONJ sr all2;;

let CLOSP2AUX_ticks_find_ant (s:string) (w:term) : term =
  hd (filter (CLOSPROPSAUX_is_app s) (CLOSP2AUX_ticks_find_closed_any [] (lhand w)));;

let CLOSP2AUX_TICKS_EX0_TAC : tactic =
  DISCH_TAC THEN EXISTS_TAC `0` THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock];;

let CLOSP2AUX_TICKS_INSTALL_TAC : tactic = fun (asl,w as gl) ->
  let tm = CLOSP2AUX_ticks_find_ant "clos_do_install" w in
  let th = MATCH_MP CLOSP2AUX_ticks_do_install_cases
             (CLOSP2AUX_ticks_rel_facts (map snd asl) (lhand tm) (rand tm)) in
  (MP_TAC th THEN STRIP_TAC THENL
    [CLOSP2AUX_TICKS_EX0_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
     CLOSP2AUX_TICKS_FIN_TAC;
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
     REPEAT CLOSP2AUX_TICKS_STEP_TAC THEN CLOSP2AUX_TICKS_FIN_TAC THEN
     MATCH_MP_TAC LIST_REL_LAST THEN ASM_REWRITE_TAC[] THEN
     REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP clos_evaluate_IMP_LENGTH)) THEN
     ASM_MESON_TAC[LENGTH_EQ_NIL]]) gl;;

let CLOSP2AUX_TICKS_DO_APP_TAC : tactic = fun (asl,w as gl) ->
  let tm = CLOSP2AUX_ticks_find_ant "clos_do_app" w in
  let opp = lhand (rator tm) in
  let th = SPEC opp (MATCH_MP CLOSP2AUX_ticks_do_app_cases
             (CLOSP2AUX_ticks_rel_facts (map snd asl) (lhand tm) (rand tm))) in
  (CLOSP2AUX_TICKS_EX0_TAC THEN MP_TAC th THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CLOSP2AUX_TICKS_FIN_TAC) gl;;

let CLOSP2AUX_TICKS_UPDATE_TAC : tactic = fun (asl,w as gl) ->
  let tm = CLOSP2AUX_ticks_find_ant "clos_update_thunk" w in
  let args = snd (strip_comb tm) in
  let p = hd (dest_list (el 0 args)) in
  let b = lhand p and ptr = rand p in
  let t = rand (el 1 args) in
  let th = SPECL [b; ptr] (MATCH_MP CLOSP2AUX_ticks_update_thunk_cases
             (CLOSP2AUX_ticks_rel_facts (map snd asl) (el 2 args) t)) in
  (CLOSP2AUX_TICKS_EX0_TAC THEN MP_TAC th THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CLOSP2AUX_TICKS_FIN_TAC) gl;;

let CLOSP2AUX_TICKS_FORCE_TAC : tactic = fun (asl,w as gl) ->
  let tm = CLOSP2AUX_ticks_find_ant "clos_dest_thunk" w in
  let th = MATCH_MP CLOSP2AUX_ticks_dest_thunk_cases
             (CLOSP2AUX_ticks_rel_facts (map snd asl) (lhand tm) (rand (rand tm))) in
  (MP_TAC th THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
    [CLOSP2AUX_TICKS_FIN_TAC; CLOSP2AUX_TICKS_FIN_TAC; CLOSP2AUX_TICKS_FIN_TAC;
     REPEAT(FIRST_X_ASSUM(fun th -> let c = concl th in
       if is_eq c && is_var (lhs c) && is_cons (rhs c) then SUBST_ALL_TAC th
       else NO_TAC)) THEN
     CLOSP2AUX_TICKS_STEP_TAC THENL
      [REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN CLOSP2AUX_TICKS_UPDATE_TAC;
       CLOSP2AUX_TICKS_FIN_TAC; CLOSP2AUX_TICKS_FIN_TAC]]) gl;;

let CLOSP2AUX_ticks_op = prove
 (el 7 CLOSP2AUX_ticks_cases,
  CLOSP2AUX_TICKS_INTRO_TAC THEN CLOSP2AUX_TICKS_SRC_TAC remove_ticks_Op_IMP_mk_Ticks THEN
  CLOSP2AUX_TICKS_UNFOLD_TAC THEN CLOSP2AUX_TICKS_STEP_TAC THENL
   [ALL_TAC; CLOSP2AUX_TICKS_FIN_TAC; CLOSP2AUX_TICKS_FIN_TAC] THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
  ASM_CASES_TAC `op = clos_Install` THEN ASM_REWRITE_TAC[] THENL
   [CLOSP2AUX_TICKS_INSTALL_TAC;
    ASM_CASES_TAC `op = clos_ThunkOp ForceThunk` THEN ASM_REWRITE_TAC[] THENL
     [CLOSP2AUX_TICKS_FORCE_TAC; CLOSP2AUX_TICKS_DO_APP_TAC]]);;

(* local helpers for the application cases: dest_closure of related values *)
(* (HOL4 proves this inline in the evaluate_app cases)                     *)
let CLOSP2AUX_ticks_full_env = prove
 (`!args1 args2 a1 a2 env1 env2 k.
     ALL2 clos_ticksProof_v_rel args1 args2 /\ ALL2 clos_ticksProof_v_rel a1 a2 /\
     ALL2 clos_ticksProof_v_rel env1 env2 ==>
     ALL2 clos_ticksProof_v_rel
       (APPEND (APPEND (REVERSE (TAKE k (REVERSE args1))) a1) env1)
       (APPEND (APPEND (REVERSE (TAKE k (REVERSE args2))) a2) env2)`,
  REPEAT STRIP_TAC THEN
  REPEAT(MATCH_MP_TAC CLOSP2AUX_ticks_all2_append THEN CONJ_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EVERY2_REVERSE THEN
  MATCH_MP_TAC EVERY2_TAKE THEN MATCH_MP_TAC EVERY2_REVERSE THEN ASM_REWRITE_TAC[]);;

let CLOSP2AUX_ticks_full_rest = prove
 (`!args1 args2 k.
     ALL2 clos_ticksProof_v_rel args1 args2 ==>
     ALL2 clos_ticksProof_v_rel (REVERSE (DROP k (REVERSE args1)))
                                (REVERSE (DROP k (REVERSE args2)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EVERY2_REVERSE THEN
  MATCH_MP_TAC EVERY2_DROP THEN MATCH_MP_TAC EVERY2_REVERSE THEN ASM_REWRITE_TAC[]);;

let CLOSP2AUX_ticks_recc_rel = prove
 (`!loc env1 env2 funs1 funs2 n.
     ALL2 clos_ticksProof_v_rel env1 env2 /\ ALL2 clos_ticksProof_f_rel funs1 funs2 ==>
     ALL2 clos_ticksProof_v_rel
       (list_of_seq (clos_Recclosure loc [] env1 funs1) n)
       (list_of_seq (clos_Recclosure loc [] env2 funs2) n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_REL_GENLIST] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (el 6 (CONJUNCTS clos_ticksProof_v_rel_rules)) THEN
  ASM_REWRITE_TAC[ALL2]);;

let CLOSP2AUX_ticks_full_env_rec = prove
 (`!args1 args2 a1 a2 env1 env2 funs1 funs2 loc k n.
     ALL2 clos_ticksProof_v_rel args1 args2 /\ ALL2 clos_ticksProof_v_rel a1 a2 /\
     ALL2 clos_ticksProof_v_rel env1 env2 /\ ALL2 clos_ticksProof_f_rel funs1 funs2 ==>
     ALL2 clos_ticksProof_v_rel
       (APPEND (APPEND (APPEND (REVERSE (TAKE k (REVERSE args1))) a1)
                       (list_of_seq (clos_Recclosure loc [] env1 funs1) n)) env1)
       (APPEND (APPEND (APPEND (REVERSE (TAKE k (REVERSE args2))) a2)
                       (list_of_seq (clos_Recclosure loc [] env2 funs2) n)) env2)`,
  REPEAT STRIP_TAC THEN
  REPEAT(MATCH_MP_TAC CLOSP2AUX_ticks_all2_append THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[CLOSP2AUX_ticks_recc_rel] THEN MATCH_MP_TAC EVERY2_REVERSE THEN
  MATCH_MP_TAC EVERY2_TAKE THEN MATCH_MP_TAC EVERY2_REVERSE THEN ASM_REWRITE_TAC[]);;

let CLOSP2AUX_TICKS_DC_TAC : tactic =
  ASSUM_LIST(fun l -> MAP_EVERY (ASSUME_TAC o MATCH_MP LIST_REL_LENGTH)
                        (filter (CLOSPROPSAUX_is_app "ALL2" o concl) l)) THEN
  ASM_REWRITE_TAC[COND_SWAP; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REPEAT COND_CASES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; distinctness "app_kind";
              injectivity "app_kind"] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  ASM_SIMP_TAC[CLOSP2AUX_ticks_full_env; CLOSP2AUX_ticks_full_rest; CLOSP2AUX_ticks_recc_rel;
               CLOSP2AUX_ticks_full_env_rec; CLOSP2AUX_ticks_all2_append] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC (el 5 (CONJUNCTS clos_ticksProof_v_rel_rules))) THEN
  TRY(MATCH_MP_TAC (el 6 (CONJUNCTS clos_ticksProof_v_rel_rules))) THEN
  ASM_SIMP_TAC[CLOSP2AUX_ticks_all2_append];;

let CLOSP2AUX_ticks_dest_closure_cases = prove
 (`!m lo f1 f2 args1 args2.
     clos_ticksProof_v_rel f1 f2 /\ ALL2 clos_ticksProof_v_rel args1 args2 ==>
     (dest_closure m lo f2 args2 = NONE /\ dest_closure m lo f1 args1 = NONE) \/
     (?v2 v1. dest_closure m lo f2 args2 = SOME (Partial_app v2) /\
              dest_closure m lo f1 args1 = SOME (Partial_app v1) /\
              clos_ticksProof_v_rel v1 v2) \/
     (?e2 env2 rest2 e1 env1 rest1.
        dest_closure m lo f2 args2 = SOME (Full_app e2 env2 rest2) /\
        dest_closure m lo f1 args1 = SOME (Full_app e1 env1 rest1) /\
        clos_ticksProof_code_rel [e1] [e2] /\ ALL2 clos_ticksProof_v_rel env1 env2 /\
        ALL2 clos_ticksProof_v_rel rest1 rest2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CASES_ON `f2:clos_v` THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSPROPSAUX_is_app "clos_ticksProof_v_rel" o concl)) THEN
  REWRITE_TAC[clos_ticksProof_v_rel_simps] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[dest_closure_def] THEN CASE_REWRITE_TAC[] THENL
   [CLOSP2AUX_TICKS_DC_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `EL a4 (funs1:(num#clos_exp)list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `b1:clos_exp` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `EL a4 (a3:(num#clos_exp)list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:num` (X_CHOOSE_THEN `b2:clos_exp` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH o
              check (fun th -> concl th = `ALL2 clos_ticksProof_f_rel funs1 a3`)) THEN
  ASM_CASES_TAC `a4 < LENGTH (a3:(num#clos_exp)list)` THENL
   [SUBGOAL_THEN `clos_ticksProof_f_rel (EL a4 funs1) (EL a4 a3)` MP_TAC THENL
     [ASM_MESON_TAC[LIST_REL_EL_EQN]; ALL_TAC] THEN
    ASM_REWRITE_TAC[clos_ticksProof_f_rel_def] THEN STRIP_TAC THEN RVEQ_TAC THEN
    CLOSP2AUX_TICKS_DC_TAC;
    SUBGOAL_THEN `LENGTH (a3:(num#clos_exp)list) <= a4` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

let CLOSP2AUX_ticks_lookup_vars_cases = prove
 (`!vs env1 env2. ALL2 clos_ticksProof_v_rel env1 env2 ==>
     (lookup_vars vs env2 = NONE /\ lookup_vars vs env1 = NONE) \/
     (?l2 l1. lookup_vars vs env2 = SOME l2 /\ lookup_vars vs env1 = SOME l1 /\
              ALL2 clos_ticksProof_v_rel l1 l2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `vs:num list` o
    MATCH_MP (REWRITE_RULE[RIGHT_FORALL_IMP_THM] (ONCE_REWRITE_RULE[SWAP_FORALL_THM]
              clos_ticksProof_lookup_vars_lemma))) THEN
  CASES_ON `lookup_vars vs (env2:clos_v list)` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN MESON_TAC[]);;

let CLOSP2AUX_ticks_fn = prove
 (el 8 CLOSP2AUX_ticks_cases,
  CLOSP2AUX_TICKS_INTRO_TAC THEN CLOSP2AUX_TICKS_SRC_TAC remove_ticks_Fn_IMP_mk_Ticks THEN
  CLOSP2AUX_TICKS_UNFOLD_TAC THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP state_rel_IMP_max_app_EQ o
              check (CLOSPROPSAUX_is_app "clos_ticksProof_state_rel" o concl)) THEN
  COND_CASES_TAC THENL [ALL_TAC; CLOSP2AUX_TICKS_FIN_TAC] THEN
  CASES_ON `vsopt:(num list)option` THEN CASE_REWRITE_TAC[] THENL
   [CLOSP2AUX_TICKS_FIN_TAC THEN
    MATCH_MP_TAC (el 5 (CONJUNCTS clos_ticksProof_v_rel_rules)) THEN
    ASM_REWRITE_TAC[ALL2; clos_ticksProof_code_rel_def];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:num list` o MATCH_MP CLOSP2AUX_ticks_lookup_vars_cases o
              check (CLOSPROPSAUX_is_app "ALL2" o concl)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CLOSP2AUX_TICKS_FIN_TAC THEN
  MATCH_MP_TAC (el 5 (CONJUNCTS clos_ticksProof_v_rel_rules)) THEN
  ASM_REWRITE_TAC[ALL2; clos_ticksProof_code_rel_def]);;

(* local helpers for the Letrec case *)
let CLOSP2AUX_ticks_f_rel_MAP = prove
 (CASE_TERM `!fns. ALL2 clos_ticksProof_f_rel fns
               (MAP (\p. match p with
                           (num_args,x) -> (num_args, HD (clos_ticks_remove_ticks [x]))) fns)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL2] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `h:num#clos_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `x:clos_exp` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_ticksProof_f_rel_def; clos_ticksProof_code_rel_def; HD_remove_ticks_SING]);;

let CLOSP2AUX_ticks_ALL_MAP = prove
 (CASE_TERM `!(P:num->bool) (f:clos_exp->clos_exp) l.
     ALL (\p. match p with (num_args,e) -> P num_args)
         (MAP (\p. match p with (num_args,x) -> (num_args, f x)) l) <=>
     ALL (\p. match p with (num_args,e) -> P num_args) l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `h:num#clos_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `x:clos_exp` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[]);;

(* replace the condition of the first conditional of the source by that of *)
(* the target (proved equal by thl), so that both are split together       *)
let CLOSP2AUX_TICKS_SYNC_COND_TAC (thl:thm list) : tactic = fun (asl,w as gl) ->
  let ct = rand (rator (rator (find_term is_cond (lhand w)))) in
  let cs = rand (rator (rator (find_term is_cond (rand w)))) in
  if ct = cs then ALL_TAC gl else
  (SUBGOAL_THEN (mk_eq(cs,ct)) SUBST1_TAC THENL
    [ASM_REWRITE_TAC thl; ALL_TAC]) gl;;

let CLOSP2AUX_TICKS_RECC_TAC : tactic = fun (asl,w as gl) ->
  let is_recc t = CLOSPROPSAUX_is_app "list_of_seq" t &&
                  CLOSPROPSAUX_is_app "clos_Recclosure" (lhand t) in
  let t2 = find_term is_recc (lhand w) and t1 = find_term is_recc (rand w) in
  let env_of t = rand (rator (lhand t)) and fns_of t = rand (lhand t) in
  let e1 = env_of t1 and e2 = env_of t2 in
  let all2 = CLOSP2AUX_ticks_env (map snd asl) e2 in
  if not (lhand (concl all2) = e1) then failwith "CLOSP2AUX_TICKS_RECC_TAC" else
  let frel = ISPEC (fns_of t1) CLOSP2AUX_ticks_f_rel_MAP in
  let loc = hd (snd (strip_comb (lhand t1))) and n = rand t1 in
  ASSUME_TAC (SPECL [loc; n] (MATCH_MP CLOSP2AUX_ticks_recc_rel (CONJ all2 frel))) gl;;

let CLOSP2AUX_ticks_letrec = prove
 (el 9 CLOSP2AUX_ticks_cases,
  CLOSP2AUX_TICKS_INTRO_TAC THEN CLOSP2AUX_TICKS_SRC_TAC remove_ticks_Letrec_IMP_mk_Ticks THEN
  CLOSP2AUX_TICKS_UNFOLD_TAC THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_IMP_max_app_EQ o
              check (CLOSPROPSAUX_is_app "clos_ticksProof_state_rel" o concl)) THEN
  CLOSP2AUX_TICKS_SYNC_COND_TAC[CLOSP2AUX_ticks_ALL_MAP] THEN
  COND_CASES_TAC THENL [ALL_TAC; CLOSP2AUX_TICKS_FIN_TAC] THEN
  REWRITE_TAC[LENGTH_MAP] THEN
  CASES_ON `namesopt:(num list)option` THEN CASE_REWRITE_TAC[] THENL
   [CLOSP2AUX_TICKS_RECC_TAC THEN
    REPEAT CLOSP2AUX_TICKS_STEP_TAC THEN CLOSP2AUX_TICKS_FIN_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:num list` o MATCH_MP CLOSP2AUX_ticks_lookup_vars_cases o
              check (fun th -> concl th = `ALL2 clos_ticksProof_v_rel env1 env`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN BETA_TAC THENL
   [CLOSP2AUX_TICKS_FIN_TAC; ALL_TAC] THEN
  CLOSP2AUX_TICKS_RECC_TAC THEN
  REPEAT CLOSP2AUX_TICKS_STEP_TAC THEN CLOSP2AUX_TICKS_FIN_TAC);;

let CLOSP2AUX_ticks_HD_rel = prove
 (`!sv tv x env (s:(C,FFI)clos_state) t.
     clos_evaluate ([x],env,s) = (Rval tv,t) /\ ALL2 clos_ticksProof_v_rel sv tv ==>
     clos_ticksProof_v_rel (HD sv) (HD tv)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o MATCH_MP clos_evaluate_SING) MP_TAC) THEN
  ASM_REWRITE_TAC[LIST_REL_CONS2; LIST_REL_NIL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[HD]);;

(* the relation of the heads of related singleton results *)
let CLOSP2AUX_TICKS_HD_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let evs = filter (fun th -> let c = concl th in
                     is_eq c && CLOSPROPSAUX_is_app "clos_evaluate" (lhs c)) asms in
  let res = flat (map (fun ev -> mapfilter (fun a ->
                    MATCH_MP CLOSP2AUX_ticks_HD_rel (CONJ ev a)) asms) evs) in
  let res = filter (fun th -> not (exists (fun a -> concl a = concl th) asms)) res in
  MAP_EVERY ASSUME_TAC res gl;;

let CLOSP2AUX_ticks_app = prove
 (el 10 CLOSP2AUX_ticks_cases,
  CLOSP2AUX_TICKS_INTRO_TAC THEN CLOSP2AUX_TICKS_SRC_TAC remove_ticks_App_IMP_mk_Ticks THEN
  CLOSP2AUX_TICKS_UNFOLD_TAC THEN
  CLOSP2AUX_TICKS_SYNC_COND_TAC[clos_ticks_LENGTH_remove_ticks] THEN
  COND_CASES_TAC THENL [ALL_TAC; CLOSP2AUX_TICKS_FIN_TAC] THEN
  CLOSP2AUX_TICKS_STEP_TAC THENL
   [ALL_TAC; CLOSP2AUX_TICKS_FIN_TAC; CLOSP2AUX_TICKS_FIN_TAC] THEN
  CLOSP2AUX_TICKS_STEP_TAC THENL
   [ALL_TAC; CLOSP2AUX_TICKS_FIN_TAC; CLOSP2AUX_TICKS_FIN_TAC] THEN
  CLOSP2AUX_TICKS_HD_TAC THEN
  CLOSP2AUX_TICKS_STEP_TAC THEN CLOSP2AUX_TICKS_FIN_TAC);;

let CLOSP2AUX_ticks_tick = prove
 (el 11 CLOSP2AUX_ticks_cases,
  CLOSP2AUX_TICKS_INTRO_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSPROPSAUX_is_app "clos_ticksProof_code_rel" o concl)) THEN
  REWRITE_TAC[CLOSP2AUX_ticks_code_sing] THEN MESON_TAC[remove_ticks_Tick]);;

let CLOSP2AUX_ticks_call = prove
 (el 12 CLOSP2AUX_ticks_cases,
  CLOSP2AUX_TICKS_INTRO_TAC THEN CLOSP2AUX_TICKS_SRC_TAC remove_ticks_Call_IMP_mk_Ticks THEN
  CLOSP2AUX_TICKS_UNFOLD_TAC THEN CLOSP2AUX_TICKS_STEP_TAC THENL
   [ALL_TAC; CLOSP2AUX_TICKS_FIN_TAC; CLOSP2AUX_TICKS_FIN_TAC] THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
  ASSUM_LIST(fun l -> REWRITE_TAC(flat (map (CONJUNCTS o MATCH_MP state_rel_IMP_code_FEMPTY)
    (filter (CLOSPROPSAUX_is_app "clos_ticksProof_state_rel" o concl) l)))) THEN
  REWRITE_TAC[clos_find_code_def; FLOOKUP_EMPTY] THEN CASE_REWRITE_TAC[] THEN
  CLOSP2AUX_TICKS_FIN_TAC);;

let CLOSP2AUX_ticks_app_nil = prove
 (el 13 CLOSP2AUX_ticks_cases,
  CLOSP2AUX_TICKS_INTRO_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOSPROPSAUX_is_app "ALL2" (concl th) &&
                                rand (concl th) = `[]:clos_v list`)) THEN
  REWRITE_TAC[LIST_REL_NIL] THEN DISCH_THEN SUBST1_TAC THEN
  CLOSP2AUX_TICKS_UNFOLD_TAC THEN REWRITE_TAC[evaluate_app_NIL] THEN
  CLOSP2AUX_TICKS_FIN_TAC);;

(* local helpers for the evaluate_app case *)
let CLOSP2AUX_ticks_state_rel_dec_clock_n = prove
 (`!n (s1:(C,FFI)clos_state) s2. clos_ticksProof_state_rel s1 s2 ==>
     clos_ticksProof_state_rel (clos_dec_clock n s1) (clos_dec_clock n s2)`,
  SIMP_TAC[clos_ticksProof_state_rel_def; clos_dec_clock_def; clos_state_INFO.ri_accfupds;
           K_THM]);;

let CLOSP2AUX_ticks_state_rel_with_clock = prove
 (`!k (s1:(C,FFI)clos_state) s2. clos_ticksProof_state_rel s1 s2 ==>
     clos_ticksProof_state_rel (clos_state_clock_fupd (K k) s1)
                               (clos_state_clock_fupd (K k) s2)`,
  SIMP_TAC[clos_ticksProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM]);;

let CLOSP2AUX_ticks_clock_ok = prove
 (`!(s1:(C,FFI)clos_state) s n.
     clos_ticksProof_state_rel s1 s /\ ~(clos_state_clock s < n) ==>
     (!ck. clos_state_clock s1 + ck < n <=> F) /\
     (!ck. clos_dec_clock n (clos_state_clock_fupd (K (clos_state_clock s1 + ck)) s1) =
           clos_state_clock_fupd (K (clos_state_clock (clos_dec_clock n s1) + ck))
             (clos_dec_clock n s1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_clock_eqs) THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN GEN_TAC THEN
  MATCH_MP_TAC CLOSPROPSAUX_dec_clock_add THEN ASM_ARITH_TAC);;

let CLOSP2AUX_TICKS_CLOCK_SYNC_TAC : tactic =
  ASSUM_LIST(fun l -> REWRITE_TAC(map (MATCH_MP state_rel_clock_eqs)
    (filter (CLOSPROPSAUX_is_app "clos_ticksProof_state_rel" o concl) l)));;

let CLOSP2AUX_TICKS_APP_FIN_TAC : tactic =
  CLOSP2AUX_TICKS_FIN_TAC THEN
  ASM_SIMP_TAC[CLOSP2AUX_ticks_state_rel_with_clock; CLOSP2AUX_ticks_state_rel_dec_clock_n];;

let CLOSP2AUX_ticks_app_cons = prove
 (el 14 CLOSP2AUX_ticks_cases,
  CLOSP2AUX_TICKS_INTRO_TAC THEN
  FIRST_X_ASSUM(fun th -> if CLOSPROPSAUX_is_app "ALL2" (concl th) &&
                             is_cons (rand (concl th))
                          then ASSUME_TAC (MATCH_MP LIST_REL_LENGTH th) THEN MP_TAC th
                          else NO_TAC) THEN
  REWRITE_TAC[LIST_REL_CONS2] THEN STRIP_TAC THEN RVEQ_TAC THEN
  CLOSP2AUX_TICKS_UNFOLD_TAC THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP state_rel_IMP_max_app_EQ th]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`clos_state_max_app (s:(C,FFI)clos_state)`; `loc_opt:num option`;
                 `f1:clos_v`; `f:clos_v`; `CONS (h':clos_v) t'`; `CONS (v4:clos_v) v5`]
                CLOSP2AUX_ticks_dest_closure_cases) THEN
  ASM_REWRITE_TAC[ALL2] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [CLOSP2AUX_TICKS_FIN_TAC;
    CLOSP2AUX_TICKS_EX0_TAC THEN CLOSP2AUX_TICKS_CLOCK_SYNC_TAC THEN
    COND_CASES_TAC THEN CLOSP2AUX_TICKS_APP_FIN_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if concl th = `ALL2 clos_ticksProof_v_rel rest1 rest2`
                        then REWRITE_TAC[MATCH_MP LIST_REL_LENGTH th] else NO_TAC) THEN
  ASM_CASES_TAC `clos_state_clock (s:(C,FFI)clos_state) <
                 LENGTH (CONS (v4:clos_v) v5) - LENGTH (rest2:clos_v list)` THENL
   [CLOSP2AUX_TICKS_EX0_TAC THEN CLOSP2AUX_TICKS_CLOCK_SYNC_TAC THEN
    ASM_REWRITE_TAC[] THEN CLOSP2AUX_TICKS_APP_FIN_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s1:(C,FFI)clos_state`; `s:(C,FFI)clos_state`;
                 `LENGTH (CONS (v4:clos_v) v5) - LENGTH (rest2:clos_v list)`]
                CLOSP2AUX_ticks_clock_ok) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `LENGTH (CONS (v4:clos_v) v5) - LENGTH (rest2:clos_v list)` o
              MATCH_MP CLOSP2AUX_ticks_state_rel_dec_clock_n o
              check (fun th -> concl th = `clos_ticksProof_state_rel (s1:(C,FFI)clos_state) s`)) THEN
  CLOSP2AUX_TICKS_STEP_TAC THENL
   [ALL_TAC; CLOSP2AUX_TICKS_FIN_TAC; CLOSP2AUX_TICKS_FIN_TAC] THEN
  CLOSP2AUX_TICKS_SING_TAC THEN CASE_REWRITE_TAC[] THEN
  CLOSP2AUX_TICKS_STEP_TAC THEN CLOSP2AUX_TICKS_FIN_TAC);;

(* HOL4: evaluate_remove_ticks *)
let clos_ticksProof_evaluate_remove_ticks = prove
 (`(!ys env2 (t1:(C,FFI)clos_state) res2 t2 env1 s1 xs.
      clos_evaluate (ys,env2,t1) = (res2,t2) /\
      ALL2 clos_ticksProof_v_rel env1 env2 /\
      clos_ticksProof_state_rel s1 t1 /\ clos_ticksProof_code_rel xs ys ==>
      ?ck res1 s2.
        clos_evaluate (xs,env1,clos_state_clock_fupd (K (clos_state_clock s1 + ck)) s1) =
        (res1,s2) /\
        result_rel (ALL2 clos_ticksProof_v_rel) clos_ticksProof_v_rel res1 res2 /\
        clos_ticksProof_state_rel s2 t2) /\
   (!loc_opt f2 args2 (t1:(C,FFI)clos_state) res2 t2 f1 args1 s1.
      evaluate_app loc_opt f2 args2 t1 = (res2,t2) /\
      clos_ticksProof_v_rel f1 f2 /\ ALL2 clos_ticksProof_v_rel args1 args2 /\
      clos_ticksProof_state_rel s1 t1 ==>
      ?ck res1 s2.
        evaluate_app loc_opt f1 args1
          (clos_state_clock_fupd (K (clos_state_clock s1 + ck)) s1) = (res1,s2) /\
        result_rel (ALL2 clos_ticksProof_v_rel) clos_ticksProof_v_rel res1 res2 /\
        clos_ticksProof_state_rel s2 t2)`,
  let th = MATCH_MP CLOSP2AUX_ticks_ind
             (end_itlist CONJ
                [CLOSP2AUX_ticks_nil; CLOSP2AUX_ticks_cons; CLOSP2AUX_ticks_var;
                 CLOSP2AUX_ticks_if; CLOSP2AUX_ticks_let; CLOSP2AUX_ticks_raise;
                 CLOSP2AUX_ticks_handle; CLOSP2AUX_ticks_op; CLOSP2AUX_ticks_fn;
                 CLOSP2AUX_ticks_letrec; CLOSP2AUX_ticks_app; CLOSP2AUX_ticks_tick;
                 CLOSP2AUX_ticks_call; CLOSP2AUX_ticks_app_nil; CLOSP2AUX_ticks_app_cons]) in
  CONJ_TAC THENL [MATCH_ACCEPT_TAC (CONJUNCT1 th); MATCH_ACCEPT_TAC (CONJUNCT2 th)]);;

(* HOL4: remove_ticks_correct *)
let remove_ticks_correct = prove
 (`!xs env2 (t1:(C,FFI)clos_state) res2 t2 env1 s1.
     clos_evaluate (clos_ticks_remove_ticks xs,env2,t1) = (res2,t2) /\
     ALL2 clos_ticksProof_v_rel env1 env2 /\ clos_ticksProof_state_rel s1 t1 ==>
     ?ck res1 s2.
       clos_evaluate (xs,env1,clos_state_clock_fupd (K (clos_state_clock s1 + ck)) s1) =
       (res1,s2) /\
       result_rel (ALL2 clos_ticksProof_v_rel) clos_ticksProof_v_rel res1 res2 /\
       clos_ticksProof_state_rel s2 t2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (CONJUNCT1 clos_ticksProof_evaluate_remove_ticks) THEN
  MAP_EVERY EXISTS_TAC [`clos_ticks_remove_ticks xs`; `env2:clos_v list`;
                        `t1:(C,FFI)clos_state`] THEN
  ASM_REWRITE_TAC[clos_ticksProof_code_rel_def]);;

(* preservation of observable semantics *)

(* a local helper: related results have the same shape *)
let CLOSP2AUX_ticks_result_shape = prove
 (`!(R1:A->B->bool) (R2:C->D->bool) x y.
     result_rel R1 R2 x y ==>
     result_rel (\(a:B) (b:A). T) (\(a:D) (b:C). T) y x`,
  REPEAT GEN_TAC THEN CASES_ON `x:(A,C)result` THEN CASES_ON `y:(B,D)result` THEN
  REWRITE_TAC[result_rel_def] THEN
  CASES_ON `a:(C)error_result` THEN CASES_ON `a':(D)error_result` THEN
  REWRITE_TAC[exc_rel_def] THEN MESON_TAC[]);;

(* HOL4: semantics_remove_ticks *)
let clos_ticksProof_semantics_remove_ticks = prove
 (`~(clos_semantics (ffi:(FFI)ffi_state) max_app FEMPTY (co:num -> C # clos_prog)
       (pure_cc (clos_ticks_compile_inc:clos_prog->clos_prog) cc) xs = Fail) ==>
   (!n. SND (SND (co n)) = []) /\ 1 <= max_app ==>
   clos_semantics ffi max_app FEMPTY co
     (pure_cc (clos_ticks_compile_inc:clos_prog->clos_prog) cc) xs =
   clos_semantics ffi max_app FEMPTY
     (pure_co (clos_ticks_compile_inc:clos_prog->clos_prog) o co) cc
     (clos_ticks_remove_ticks xs)`,
  DISCH_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] IMP_semantics_eq_no_fail) THEN
  EXISTS_TAC `\(c1:(num,num#clos_exp)fmap) (o1:num->C#clos_prog)
                (k1:C->clos_prog->(byte list # int64 list # C)option) (e1:clos_exp list)
                (c2:(num,num#clos_exp)fmap) (o2:num->C#clos_prog)
                (k2:C->clos_prog->(byte list # int64 list # C)option) (e2:clos_exp list). T` THEN
  REWRITE_TAC[clos_eval_sim_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`xs:clos_exp list`; `[]:clos_v list`;
                 `clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY
                    (pure_co (clos_ticks_compile_inc:clos_prog->clos_prog) o
                     (co:num -> C # clos_prog)) cc k`;
                 `res1:(clos_v list,clos_v)result`; `s2:(C,FFI)clos_state`;
                 `[]:clos_v list`;
                 `clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY
                    (co:num -> C # clos_prog)
                    (pure_cc (clos_ticks_compile_inc:clos_prog->clos_prog) cc) k`]
                remove_ticks_correct) THEN
  ASM_REWRITE_TAC[ALL2] THEN ANTS_TAC THENL
   [REWRITE_TAC[clos_ticksProof_state_rel_def; clos_initial_state_def;
                clos_state_INFO.ri_accessors; ALL2; clos_ticksProof_FMAP_REL_def;
                FLOOKUP_EMPTY; distinctness "option"] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[clos_initial_state_with_clock] THEN STRIP_TAC THEN
  EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP CLOSP2AUX_ticks_result_shape);
    RULE_ASSUM_TAC(REWRITE_RULE[clos_ticksProof_state_rel_def]) THEN ASM_REWRITE_TAC[]]);;

(* syntactic properties *)

(* local helpers: the properties of remove_ticks_sing, remove_ticks_list and *)
(* remove_ticks_let, proved together by their induction                    *)
let CLOSP2AUX_TICKS_SYN_TAC (thl:thm list) : tactic =
  MATCH_MP_TAC clos_ticks_remove_ticks_sing_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN
  REWRITE_TAC[clos_ticks_remove_ticks_sing_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC([MAP; LENGTH; ALL] @ thl);;

let CLOSP2AUX_ticks_syn = prove
 (`(!e. code_locs [clos_ticks_remove_ticks_sing e] = code_locs [e] /\
        (every_Fn_SOME [clos_ticks_remove_ticks_sing e] <=> every_Fn_SOME [e]) /\
        (every_Fn_vs_NONE [clos_ticks_remove_ticks_sing e] <=> every_Fn_vs_NONE [e]) /\
        (!m. obeys_max_app m (clos_ticks_remove_ticks_sing e) <=> obeys_max_app m e) /\
        (no_Labels (clos_ticks_remove_ticks_sing e) <=> no_Labels e) /\
        (!x. app_call_dests x [clos_ticks_remove_ticks_sing e] = app_call_dests x [e]) /\
        clos_get_code_labels (clos_ticks_remove_ticks_sing e) = clos_get_code_labels e) /\
   (!es. code_locs (clos_ticks_remove_ticks_list es) = code_locs es /\
         (every_Fn_SOME (clos_ticks_remove_ticks_list es) <=> every_Fn_SOME es) /\
         (every_Fn_vs_NONE (clos_ticks_remove_ticks_list es) <=> every_Fn_vs_NONE es) /\
         (!m. ALL (obeys_max_app m) (clos_ticks_remove_ticks_list es) <=>
              ALL (obeys_max_app m) es) /\
         (ALL no_Labels (clos_ticks_remove_ticks_list es) <=> ALL no_Labels es) /\
         (!x. app_call_dests x (clos_ticks_remove_ticks_list es) = app_call_dests x es) /\
         MAP clos_get_code_labels (clos_ticks_remove_ticks_list es) =
         MAP clos_get_code_labels es /\
         LENGTH (clos_ticks_remove_ticks_list es) = LENGTH es) /\
   (!fns. code_locs (MAP SND (remove_ticks_let fns)) = code_locs (MAP SND fns) /\
          (every_Fn_SOME (MAP SND (remove_ticks_let fns)) <=> every_Fn_SOME (MAP SND fns)) /\
          (every_Fn_vs_NONE (MAP SND (remove_ticks_let fns)) <=>
           every_Fn_vs_NONE (MAP SND fns)) /\
          (!m. ALL (obeys_max_app m) (MAP SND (remove_ticks_let fns)) <=>
               ALL (obeys_max_app m) (MAP SND fns)) /\
          (ALL no_Labels (MAP SND (remove_ticks_let fns)) <=> ALL no_Labels (MAP SND fns)) /\
          (!x. app_call_dests x (MAP SND (remove_ticks_let fns)) =
               app_call_dests x (MAP SND fns)) /\
          MAP (clos_get_code_labels o SND) (remove_ticks_let fns) =
          MAP (clos_get_code_labels o SND) fns /\
          LENGTH (remove_ticks_let fns) = LENGTH fns)`,
  CLOSP2AUX_TICKS_SYN_TAC[code_locs_def; every_Fn_SOME_def; every_Fn_vs_NONE_def;
                          obeys_max_app_def; no_Labels_def; app_call_dests_def;
                          clos_get_code_labels_def; o_THM] THEN
  ONCE_REWRITE_TAC[code_locs_cons; CLOSPROPSAUX_every_Fn_SOME_cons;
                   CLOSPROPSAUX_every_Fn_vs_NONE_cons; app_call_dests_cons] THEN
  ASM_REWRITE_TAC[]);;

let CLOSP2AUX_ticks_list = CONJUNCT1 (CONJUNCT2 remove_ticks_sing_eq);;

(* HOL4: code_locs_remove_ticks *)
let code_locs_remove_ticks = prove
 (`!xs. code_locs (clos_ticks_remove_ticks xs) = code_locs xs`,
  REWRITE_TAC[CLOSP2AUX_ticks_list; CLOSP2AUX_ticks_syn]);;

(* HOL4: remove_ticks_every_Fn_SOME [simp] *)
let remove_ticks_every_Fn_SOME = prove
 (`!ls. every_Fn_SOME (clos_ticks_remove_ticks ls) <=> every_Fn_SOME ls`,
  REWRITE_TAC[CLOSP2AUX_ticks_list; CLOSP2AUX_ticks_syn]);;
let _ = cake_add_simps [remove_ticks_every_Fn_SOME];;

(* HOL4: remove_ticks_every_Fn_vs_NONE [simp] *)
let remove_ticks_every_Fn_vs_NONE = prove
 (`!ls. every_Fn_vs_NONE (clos_ticks_remove_ticks ls) <=> every_Fn_vs_NONE ls`,
  REWRITE_TAC[CLOSP2AUX_ticks_list; CLOSP2AUX_ticks_syn]);;
let _ = cake_add_simps [remove_ticks_every_Fn_vs_NONE];;

(* HOL4: EVERY_remove_ticks_sing *)
let EVERY_remove_ticks_sing = prove
 (`ALL f (clos_ticks_remove_ticks [x]) <=> f (HD (clos_ticks_remove_ticks [x]))`,
  REWRITE_TAC[CONJUNCT1 remove_ticks_sing_eq; HD; ALL]);;

(* HOL4: remove_ticks_obeys_max_app *)
let remove_ticks_obeys_max_app = prove
 (`!xs. ALL (obeys_max_app m) xs ==> ALL (obeys_max_app m) (clos_ticks_remove_ticks xs)`,
  REWRITE_TAC[CLOSP2AUX_ticks_list; CLOSP2AUX_ticks_syn]);;

(* HOL4: remove_ticks_no_Labels *)
let remove_ticks_no_Labels = prove
 (`!xs. ALL no_Labels xs ==> ALL no_Labels (clos_ticks_remove_ticks xs)`,
  REWRITE_TAC[CLOSP2AUX_ticks_list; CLOSP2AUX_ticks_syn]);;

(* HOL4: remove_ticks_app_call_dests [simp] *)
let remove_ticks_app_call_dests = prove
 (`!es. app_call_dests x (clos_ticks_remove_ticks es) = app_call_dests x es`,
  REWRITE_TAC[CLOSP2AUX_ticks_list; CLOSP2AUX_ticks_syn]);;
let _ = cake_add_simps [remove_ticks_app_call_dests];;

(* HOL4: remove_ticks_code_labels [simp] *)
let clos_ticksProof_remove_ticks_code_labels = prove
 (`!es. MAP clos_get_code_labels (clos_ticks_remove_ticks es) =
        MAP clos_get_code_labels es`,
  REWRITE_TAC[CLOSP2AUX_ticks_list; CLOSP2AUX_ticks_syn]);;
let _ = cake_add_simps [clos_ticksProof_remove_ticks_code_labels];;
