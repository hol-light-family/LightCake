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
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `clos_v_to_list y` (cases "option")) THEN STRIP_TAC THENL
   [MP_TAC(SPECL [`x:clos_v`; `y:clos_v`; `clos_fvsProof_v_rel`] vr_list_NONE) THEN
    ASM_REWRITE_TAC[CLOSP1AUX_fvs_simple_val_rel] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[distinctness "option"];
    MP_TAC(MATCH_MP CLOSPROPSAUX_v_to_list_SOME CLOSP1AUX_fvs_simple_val_rel) THEN
    DISCH_THEN(MP_TAC o SPECL [`y:clos_v`; `a:clos_v list`; `x:clos_v`]) THEN
    ASM_REWRITE_TAC[injectivity "option"] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[injectivity "option"] THEN
    MP_TAC(MATCH_MP val_rel_to_words_lemma CLOSP1AUX_fvs_simple_val_rel) THEN
    DISCH_THEN(MP_TAC o SPECL [`xs:clos_v list`; `a:clos_v list`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

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
  UNDISCH_TAC `ALL2 clos_fvsProof_v_rel env1 env2` THEN
  REWRITE_TAC[LIST_REL_EL_EQN] THEN ASM_MESON_TAC[]);;

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
  CASES_ON `f2:clos_v` THEN REWRITE_TAC[dest_closure_def] THEN
  CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

(* local tactics: add LENGTH l1 = LENGTH l2 for every ALL2 R l1 l2;          *)
(* prove ALL2 goals on APPEND/REVERSE/TAKE/DROP/list_of_seq of related lists; *)
(* rewrite LENGTH (TAKE n l) to n after proving n <= LENGTH l                 *)
let CLOSP1AUX_is_app name tm =
  try fst(dest_const(fst(strip_comb tm))) = name with Failure _ -> false;;

let CLOSP1AUX_mentions name tm =
  can (find_term (fun t -> try fst(dest_const t) = name with Failure _ -> false)) tm;;

let CLOSP1AUX_ALL2_LENGTH_TAC : tactic = fun (asl,w as gl) ->
  let ths = mapfilter (fun (_,th) -> MATCH_MP LIST_REL_LENGTH th) asl in
  let ths = filter (fun th -> not (exists (fun (_,a) -> concl a = concl th) asl)) ths in
  MAP_EVERY ASSUME_TAC ths gl;;

(* a local helper: the functions of a Letrec and their remove_fvs images *)
let CLOSP1AUX_fvs_f_rel_MAP = prove
 (CASE_TERM `!n k fns.
     ALL2 (clos_fvsProof_f_rel (n + k)) fns
       (MAP (\p. match p with
                   (num_args,x) -> (num_args, HD (remove_fvs (num_args + k + n) [x])))
            fns)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ALL2] THEN
  SPEC_TAC(`h:num#clos_exp`,`h:num#clos_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; clos_fvsProof_f_rel_def;
              clos_fvsProof_code_rel_def; HD_remove_fvs_SING] THEN
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let CLOSP1AUX_ALL2_TAC : tactic =
  REPEAT((MATCH_MP_TAC EVERY2_APPEND_suff THEN CONJ_TAC) ORELSE
         MATCH_MP_TAC EVERY2_REVERSE ORELSE MATCH_MP_TAC EVERY2_TAKE ORELSE
         MATCH_MP_TAC EVERY2_DROP) THEN
  ASM_REWRITE_TAC[ALL2; LIST_REL_GENLIST] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[clos_fvsProof_v_rel_simps; injectivity "clos_v"; GSYM CONJ_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  ASM_REWRITE_TAC[ALL2; CLOSP1AUX_fvs_f_rel_MAP];;

let CLOSP1AUX_LENGTH_TAKE_TAC : tactic = fun (asl,w as gl) ->
  let t = find_term (fun t -> is_comb t && is_comb (rator t) &&
                              (try fst(dest_const(rator(rator t))) = "TAKE"
                               with Failure _ -> false)) w in
  let n = rand(rator t) and l = rand t in
  (SUBGOAL_THEN (mk_binop `(<=):num->num->bool` n (mk_comb(`LENGTH:clos_v list->num`, l)))
     (fun th -> REWRITE_TAC[MATCH_MP LENGTH_TAKE th]) THENL
   [REWRITE_TAC[LENGTH; LENGTH_REVERSE; LENGTH_APPEND] THEN ASM_ARITH_TAC; ALL_TAC]) gl;;

(* the dest_closure hypothesis, its conditions split in step with the goal *)
let CLOSP1AUX_DEST_SPLIT_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  ASM_REWRITE_TAC[LENGTH; LET_DEF; LET_END_DEF] THEN
  REPEAT(COND_CASES_TAC THEN
         REWRITE_TAC[distinctness "option"; injectivity "option"; injectivity "app_kind";
                     distinctness "app_kind"]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH_REVERSE; LENGTH_LIST_OF_SEQ] THEN
    CLOSP1AUX_LENGTH_TAKE_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (CLOSP1AUX_is_app "clos_fvsProof_code_rel" o concl)) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    CONJ_TAC THEN CLOSP1AUX_ALL2_TAC];;

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
  STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP clos_fvsProof_dest_closure_SOME_IMP) THEN
  FIRST_X_ASSUM(REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOSP1AUX_is_app "clos_fvsProof_v_rel" (concl th) &&
                                          is_comb(rand(rator(concl th))))) THEN
  REWRITE_TAC[clos_fvsProof_v_rel_simps] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dest_closure_def]) THEN REWRITE_TAC[dest_closure_def] THEN
  CASE_REWRITE_TAC[] THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  CLOSP1AUX_ALL2_LENGTH_TAC THENL
   [CLOSP1AUX_DEST_SPLIT_TAC; ALL_TAC] THEN
  REPEAT PAIRARG_TAC THEN
  ASM_CASES_TAC `LENGTH (fns:(num#clos_exp)list) <= i` THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
    ASM_REWRITE_TAC[distinctness "option"]; ALL_TAC] THEN
  SUBGOAL_THEN `~(LENGTH (funs2:(num#clos_exp)list) <= i)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o CONJUNCT2 o REWRITE_RULE[LIST_REL_EL_EQN] o
              check (fun th -> CLOSP1AUX_is_app "ALL2" (concl th) &&
                               CLOSP1AUX_mentions "clos_fvsProof_f_rel" (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[clos_fvsProof_f_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CLOSP1AUX_DEST_SPLIT_TAC);;

(* HOL4: simple_state_rel [local] *)
let clos_fvsProof_simple_state_rel = prove
 (`clos_simple_state_rel clos_fvsProof_v_rel
     (clos_fvsProof_state_rel:(C,FFI)clos_state->(C,FFI)clos_state->bool)`,
  REWRITE_TAC[clos_simple_state_rel_def; clos_fvsProof_state_rel_def] THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM; fmap_rel_def; FLOOKUP_DEF;
              FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_eq (concl th) && CLOSP1AUX_is_app "FDOM" (lhs (concl th))
                                 then SUBST_ALL_TAC th else NO_TAC)) THEN
  REWRITE_TAC[] THEN
  TRY(FIRST_X_ASSUM(MP_TAC o check (is_cond o lhs o concl)) THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[distinctness "option"; injectivity "option"] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `ptr:num` o
                    check (CLOSP1AUX_mentions "clos_fvsProof_ref_rel" o concl)) THEN
      ASM_REWRITE_TAC[clos_fvsProof_ref_rel_cases; distinctness "clos_ref";
                      injectivity "clos_ref"] THEN MESON_TAC[] THEN NO_TAC) THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[clos_fvsProof_ref_rel_rules]);;

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

(* a local helper: a case on dest_thunk that is NONE unless NotThunk *)
let CLOSP1AUX_dest_thunk_NONE = prove
 (CASE_TERM `!d (x:A option).
     ~(d = clos_NotThunk) ==>
     (match d with clos_BadRef -> NONE | clos_NotThunk -> x | clos_IsThunk m v -> NONE) =
     NONE`,
  GEN_TAC THEN CASES_ON `d:clos_dest_thunk_ret` THEN CASE_REWRITE_TAC[]);;

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
  STRIP_TAC THEN
  SUBGOAL_THEN `(vs = [] /\ ys = []) \/
                (?x y. vs = [x] /\ ys = [y] /\ clos_fvsProof_v_rel x y) \/
                (?x1 x2 r1 y1 y2 r2. vs = CONS x1 (CONS x2 r1) /\
                                     ys = CONS y1 (CONS y2 r2))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ALL2 clos_fvsProof_v_rel vs ys` THEN
    STRUCT_CASES_TAC(ISPEC `vs:clos_v list` list_CASES) THEN
    REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1] THENL [MESON_TAC[]; ALL_TAC] THEN
    STRUCT_CASES_TAC(ISPEC `t:clos_v list` list_CASES) THEN
    REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[CONS_11; NOT_CONS_NIL; UNWIND_THM1] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[clos_update_thunk_def; distinctness "option"];
    ALL_TAC;
    ASM_REWRITE_TAC[clos_update_thunk_def; distinctness "option"]] THEN
  ASM_REWRITE_TAC[clos_update_thunk_def] THEN
  SUBGOAL_THEN `(clos_dest_thunk [x] (clos_state_refs (s1:(C,FFI)clos_state)) =
                 clos_NotThunk) <=>
                (clos_dest_thunk [y] (clos_state_refs (s2:(C,FFI)clos_state)) =
                 clos_NotThunk)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`clos_fvsProof_v_rel`;
                   `clos_fvsProof_state_rel:(C,FFI)clos_state->(C,FFI)clos_state->bool`;
                   `s1:(C,FFI)clos_state`; `s2:(C,FFI)clos_state`;
                   `x:clos_v`; `y:clos_v`; `Evaluated`] CLOSPROPSAUX_bad_thunk_rel) THEN
    ASM_REWRITE_TAC[CLOSP1AUX_fvs_simple_val_rel; clos_fvsProof_simple_state_rel;
                    clos_bad_thunk_update_def] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  ASM_CASES_TAC `clos_dest_thunk [x] (clos_state_refs (s1:(C,FFI)clos_state)) =
                 clos_NotThunk` THENL
   [SUBGOAL_THEN `clos_dest_thunk [y] (clos_state_refs (s2:(C,FFI)clos_state)) =
                  clos_NotThunk`
      ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    SUBGOAL_THEN `~(clos_dest_thunk [y] (clos_state_refs (s2:(C,FFI)clos_state)) =
                    clos_NotThunk)`
      ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CLOSP1AUX_dest_thunk_NONE; distinctness "option"]] THEN
  REWRITE_TAC[store_thunk_def] THEN
  MP_TAC(ISPECL [`s1:(C,FFI)clos_state`; `s2:(C,FFI)clos_state`; `ptr:num`]
                CLOSP1AUX_fvs_flookup_rel) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (clos_state_refs (s1:(C,FFI)clos_state)) ptr` THEN
  CASES_ON `FLOOKUP (clos_state_refs (s2:(C,FFI)clos_state)) ptr` THEN
  REWRITE_TAC[OPTREL_THM; case_def "option"; distinctness "option"] THEN
  ONCE_REWRITE_TAC[clos_fvsProof_ref_rel_cases] THEN STRIP_TAC THEN RVEQ_TAC THEN
  CASE_REWRITE_TAC[] THEN
  CASES_ON `m:thunk_mode` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[UNWIND_THM1] THEN
  MATCH_MP_TAC CLOSP1AUX_fvs_state_rel_refs_upd THEN
  ASM_SIMP_TAC[clos_fvsProof_ref_rel_rules]);;

(* ------------------------------------------------------------------------- *)
(* The correctness of remove_fvs (HOL4: evaluate_remove_fvs), proved by the  *)
(* induction of closProps (CLOSPROPSAUX_evaluate_ind) with one lemma per     *)
(* case, and local tactics: an induction hypothesis is applied to a named   *)
(* sub-evaluation of the source, which gives the target sub-evaluation and  *)
(* its relation; the results are then split in step (HOL4: first_x_assum   *)
(* drule \\ disch_then drule ... \\ fs [case_eq_thms]).                     *)
(* ------------------------------------------------------------------------- *)

let CLOSP1AUX_fvs_ind =
  let p = `\xs env1 (s1:(C,FFI)clos_state).
     !res1 s2 ys env2 t1.
       clos_evaluate (xs,env1,s1) = (res1,s2) /\
       ALL2 clos_fvsProof_v_rel env1 env2 /\ clos_fvsProof_state_rel s1 t1 /\
       clos_fvsProof_code_rel (LENGTH env1) xs ys ==>
       ?res2 t2.
         clos_evaluate (ys,env2,t1) = (res2,t2) /\
         result_rel (ALL2 clos_fvsProof_v_rel) clos_fvsProof_v_rel res1 res2 /\
         clos_fvsProof_state_rel s2 t2`
  and q = `\loc_opt f1 args1 (s1:(C,FFI)clos_state).
     !res1 s2 f2 args2 t1.
       evaluate_app loc_opt f1 args1 s1 = (res1,s2) /\
       clos_fvsProof_v_rel f1 f2 /\ ALL2 clos_fvsProof_v_rel args1 args2 /\
       clos_fvsProof_state_rel s1 t1 ==>
       ?res2 t2.
         evaluate_app loc_opt f2 args2 t1 = (res2,t2) /\
         result_rel (ALL2 clos_fvsProof_v_rel) clos_fvsProof_v_rel res1 res2 /\
         clos_fvsProof_state_rel s2 t2` in
  CONV_RULE (DEPTH_CONV BETA_CONV) (ISPECL [p;q] CLOSPROPSAUX_evaluate_ind);;
let CLOSP1AUX_fvs_cases = conjuncts (lhand (concl CLOSP1AUX_fvs_ind));;

(* apply an induction hypothesis of P shape to an evaluate fact *)
let CLOSP1AUX_fvs_apply (asl:thm list) (ih:thm) (ev:thm) : thm =
  let th1 = MATCH_MP (REWRITE_RULE[IMP_CONJ] ih) ev in
  let th2 = tryfind (fun a -> MATCH_MP th1 a) asl in
  let th3 = tryfind (fun a -> MATCH_MP th2 a) asl in
  let ys,bod = dest_forall (concl th3) in
  let ant = lhand bod in
  let k = lhand (rator ant) and x = rand (rator ant) in
  let rm = mk_comb(mk_comb(`remove_fvs`, k), x) in
  let th4 = SPEC rm th3 in
  MP th4 (EQT_ELIM (REWRITE_CONV[clos_fvsProof_code_rel_def] (lhand (concl th4))));;


let CLOSP1AUX_counter = ref 0;;

(* the P-shaped facts: !res1 s2 ys env2 t1. clos_evaluate (X,E,S) = (res1,s2) /\ ... *)
let CLOSP1AUX_is_P th =
  let c = snd(strip_forall(concl th)) in
  is_imp c && is_conj (lhand c) &&
  (let a = lhand (lhand c) in is_eq a && CLOSP1AUX_is_app "clos_evaluate" (lhs a) &&
                               is_var (lhand (rhs a)));;

(* resolve the conditional induction hypotheses (whose conclusion is P-shaped) *)
(* with the assumptions, giving P-shaped facts                                 *)
(* the Q-shaped facts: !res1 s2 f2 args2 t1. evaluate_app lo f1 a1 s1 = (res1,s2) /\ ... *)
let CLOSP1AUX_is_Q th =
  let c = snd(strip_forall(concl th)) in
  is_imp c && is_conj (lhand c) &&
  (let a = lhand (lhand c) in is_eq a && CLOSP1AUX_is_app "evaluate_app" (lhs a) &&
                               is_var (lhand (rhs a)));;

let CLOSP1AUX_curry_top th =
  try let vs,bod = strip_forall (concl th) in
      let ant,con = dest_imp bod in
      let ants = conjuncts ant in
      let th1 = MP (SPECL vs th) (end_itlist CONJ (map ASSUME ants)) in
      GENL vs (itlist DISCH ants th1)
  with Failure _ -> th;;

(* resolve the conditional induction hypotheses (whose conclusion is P- or  *)
(* Q-shaped) with the assumptions                                           *)
let CLOSP1AUX_COND_IH_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let mentions_eval t =
    can (find_term (fun t -> try let n = fst(dest_const t) in
                                 n = "clos_evaluate" || n = "evaluate_app"
                             with Failure _ -> false)) t in
  let is_cond_ih th =
    not (CLOSP1AUX_is_P th) && not (CLOSP1AUX_is_Q th) &&
    (let c = snd(strip_forall(concl th)) in
     is_imp c && mentions_eval (rand c) && is_forall (rand c)) in
  let cihs = filter is_cond_ih asms in
  let rec resolve depth th =
    if CLOSP1AUX_is_P th || CLOSP1AUX_is_Q th then [th]
    else if depth = 0 then [] else
    let rs = mapfilter (fun a -> MATCH_MP th a) asms in
    flat (map (resolve (depth-1)) rs) in
  let res = flat (map (fun th -> resolve 4 (CLOSP1AUX_curry_top th)) cihs) in
  let res = filter (fun th -> not (exists (fun a -> aconv (concl a) (concl th)) asms)) res in
  MAP_EVERY ASSUME_TAC res gl;;

(* name the first clos_evaluate of the antecedent of the goal that is not   *)
(* yet the left side of an assumption                                       *)
let CLOSP1AUX_NAME_EVAL_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w in
  let fvs = frees w @ freesl (map (concl o snd) asl) in
  let named = mapfilter (fun (_,th) -> lhs (concl th)) asl in
  let evs = find_terms (fun t -> is_comb t && CLOSP1AUX_is_app "clos_evaluate" t &&
                                 not (mem t named) &&
                                 subset (frees t) fvs) ant in
  let tm = hd evs in
  let ty = type_of tm in
  let rty,sty = (match dest_type ty with (_,[a;b]) -> a,b | _ -> failwith "NAME") in
  incr CLOSP1AUX_counter;
  let k = string_of_int (!CLOSP1AUX_counter) in
  let r = mk_var("rr" ^ k, rty) and s = mk_var("ss" ^ k, sty) in
  (MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN r (X_CHOOSE_THEN s ASSUME_TAC)) THEN
   POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)) gl;;

(* after an induction hypothesis gave evaluate (target) = (res2,t2) and     *)
(* result_rel R1 R2 r res2: rewrite the target with it and split r         *)
let CLOSP1AUX_SPLIT_RES_TAC : tactic = fun (asl,w as gl) ->
  let rr = find (fun (_,th) -> CLOSP1AUX_is_app "result_rel" (concl th) &&
                               is_var (rand (rator (concl th)))) asl in
  let r = rand (rator (concl (snd rr))) in
  let r2 = rand (concl (snd rr)) in
  let tgt = find (fun (_,th) -> is_eq (concl th) && is_pair (rhs (concl th)) &&
                                fst (dest_pair (rhs (concl th))) = r2) asl in
  (REWRITE_TAC[snd tgt] THEN
   CASES_ON r THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOSP1AUX_is_app "result_rel" (concl th) &&
                                           rand (concl th) = r2)) THEN
   REWRITE_TAC[result_rel_Rval; result_rel_Rerr1] THEN
   DISCH_THEN(STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   CASE_REWRITE_TAC[]) gl;;

(* singleton results: clos_evaluate ([e],env,s) = (Rval a,s') gives a = [r] *)
let CLOSP1AUX_SING_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && CLOSP1AUX_is_app "clos_evaluate" (lhs c) &&
       (let r = fst(dest_pair(rhs c)) in
        CLOSP1AUX_is_app "Rval" r && is_var (rand r))
    then (STRIP_ASSUME_TAC(MATCH_MP clos_evaluate_SING th) THEN ASSUME_TAC th)
    else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_var (lhs (concl th)) &&
                              is_cons (rhs (concl th)) then SUBST_ALL_TAC th else NO_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if CLOSP1AUX_is_app "ALL2" c && is_cons (lhand c) && is_var (rand c)
    then MP_TAC th THEN REWRITE_TAC[LIST_REL_CONS1; LIST_REL_NIL] THEN STRIP_TAC THEN
         RVEQ_TAC
    else NO_TAC));;

let CLOSP1AUX_fvs_remove_AppUnit = prove
 (`!v:clos_v. remove_fvs (LENGTH [v]) [clos_AppUnit (clos_Var backend_common_None 0)] =
              [clos_AppUnit (clos_Var backend_common_None 0)]`,
  REWRITE_TAC[clos_AppUnit_def; remove_fvs_def; LENGTH; HD; ARITH_RULE `0 < SUC 0`]);;

let CLOSP1AUX_IH_ON_NEW_TAC : tactic = fun (asl,w as gl) ->
  let ev = snd (hd asl) in
  let asms = map snd asl in
  let ihs = filter CLOSP1AUX_is_P asms in
  let res = mapfilter (fun ih -> CLOSP1AUX_fvs_apply asms ih ev) ihs in
  (if res = [] then NO_TAC
   else STRIP_ASSUME_TAC (REWRITE_RULE[CLOSP1AUX_fvs_remove_AppUnit] (hd res))) gl;;

(* a local tactic: rewrite the lengths of target lists in the goal to those *)
(* of the source lists (from the ALL2 assumptions)                          *)
let CLOSP1AUX_LEN_TAC : tactic =
  CLOSP1AUX_ALL2_LENGTH_TAC THEN
  (fun (asl,w as gl) ->
     let eqs = filter (fun th -> let c = concl th in
                        is_eq c && CLOSP1AUX_is_app "LENGTH" (lhs c) &&
                        CLOSP1AUX_is_app "LENGTH" (rhs c) && is_var (rand (rhs c)))
                      (map snd asl) in
     REWRITE_TAC (map SYM eqs) gl);;

let CLOSP1AUX_FIN_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC] THEN CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  CLOSP1AUX_SING_TAC THEN
  ASM_REWRITE_TAC[result_rel_def; exc_rel_def; injectivity "result"; distinctness "result";
                  HD; ALL2];;

(* split a related pair of errors exc_rel R a e' (a a variable) *)
let CLOSP1AUX_SPLIT_EXC_TAC : tactic = fun (asl,w as gl) ->
  let er = find (fun (_,th) -> CLOSP1AUX_is_app "exc_rel" (concl th) &&
                               is_var (rand (rator (concl th)))) asl in
  let a = rand (rator (concl (snd er))) and e2 = rand (concl (snd er)) in
  (CASES_ON a THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOSP1AUX_is_app "exc_rel" (concl th) &&
                                           rand (concl th) = e2)) THEN
   REWRITE_TAC[exc_rel_raise1; exc_rel_type_error1] THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN CASE_REWRITE_TAC[]) gl;;

(* before an induction hypothesis is applied to the source evaluation of    *)
(* the antecedent: make the remove_fvs index of the matching target         *)
(* evaluation LENGTH of the source environment, and relate the two          *)
(* environments                                                             *)
let CLOSP1AUX_ENV_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w and con = rand w in
  let fvs = frees w @ freesl (map (concl o snd) asl) in
  let src = find_term (fun t -> is_comb t && CLOSP1AUX_is_app "clos_evaluate" t &&
                                subset (frees t) fvs) ant in
  let x,es = dest_pair (rand src) in
  let e = fst (dest_pair es) in
  let is_tgt t = is_comb t && CLOSP1AUX_is_app "clos_evaluate" t &&
                 (let r = fst (dest_pair (rand t)) in
                  r = x || (CLOSP1AUX_is_app "remove_fvs" r && rand r = x)) in
  let tgt = find_term is_tgt con in
  let r,et = dest_pair (rand tgt) in
  let e2 = fst (dest_pair et) in
  let lene = mk_comb(`LENGTH:clos_v list->num`, e) in
  let lens = mapfilter (MATCH_MP clos_evaluate_IMP_LENGTH) (map snd asl) in
  ((if r = x || rand (rator r) = lene then ALL_TAC else
    SUBGOAL_THEN (mk_eq(rand (rator r), lene))
      (fun th -> REWRITE_TAC[AP_THM (AP_TERM `remove_fvs` th) x]) THENL
     [MAP_EVERY MP_TAC lens THEN
      REWRITE_TAC[LENGTH; LENGTH_APPEND; LENGTH_LIST_OF_SEQ; LENGTH_MAP] THEN ARITH_TAC;
      ALL_TAC]) THEN
   (let all2 = list_mk_comb(`ALL2 clos_fvsProof_v_rel`, [e; e2]) in
    if exists (fun (_,th) -> concl th = all2) asl then ALL_TAC else
    SUBGOAL_THEN all2 ASSUME_TAC THENL [CLOSP1AUX_ALL2_TAC; ALL_TAC])) gl;;

let CLOSP1AUX_STEP_TAC : tactic =
  CLOSP1AUX_COND_IH_TAC THEN TRY CLOSP1AUX_ENV_TAC THEN
  CLOSP1AUX_NAME_EVAL_TAC THEN CLOSP1AUX_IH_ON_NEW_TAC THEN
  CLOSP1AUX_SPLIT_RES_TAC;;

let CLOSP1AUX_fvs_nil = prove
 (el 0 CLOSP1AUX_fvs_cases,
  REWRITE_TAC[clos_evaluate_def; clos_fvsProof_code_rel_def; remove_fvs_def; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`Rval []:(clos_v list,clos_v)result`; `t1:(C,FFI)clos_state`] THEN
  ASM_REWRITE_TAC[clos_evaluate_def; result_rel_def; ALL2]);;


let CLOSP1AUX_fvs_cons = prove
 (el 1 CLOSP1AUX_fvs_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[clos_fvsProof_code_rel_def; remove_fvs_def] o
                check (CLOSP1AUX_is_app "clos_fvsProof_code_rel" o concl)) THEN
  ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN REWRITE_TAC[HD_remove_fvs_SING] THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSP1AUX_is_app "clos_evaluate" o lhs o concl)) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN
  REPEAT CLOSP1AUX_STEP_TAC THEN CLOSP1AUX_FIN_TAC);;


let CLOSP1AUX_fvs_do_app_El_nil = prove
 (`!t1:(C,FFI)clos_state. clos_do_app (MemOp clos_El) [] t1 = Rerr (Rabort Rtype_error)`,
  REWRITE_TAC[clos_do_app_def] THEN CASE_REWRITE_TAC[]);;

let CLOSP1AUX_fvs_var = prove
 (el 2 CLOSP1AUX_fvs_cases,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[clos_fvsProof_code_rel_def; remove_fvs_def] o
                check (CLOSP1AUX_is_app "clos_fvsProof_code_rel" o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSP1AUX_is_app "clos_evaluate" o lhs o concl)) THEN
  REWRITE_TAC[clos_evaluate_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[clos_evaluate_def; distinctness "clos_op"] THEN
  CLOSP1AUX_LEN_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[REVERSE; CLOSP1AUX_fvs_do_app_El_nil] THEN CLOSP1AUX_FIN_TAC THEN
  ASM_MESON_TAC[LIST_REL_EL_EQN]);;


(* local helpers: booleans on the right of v_rel; related singleton results *)
(* agree on being a boolean                                                *)
(* local helpers: booleans on the right of v_rel; related singleton results *)
(* agree on being a boolean                                                *)
let CLOSP1AUX_fvs_v_rel_Boolv_right = prove
 (`!x b. clos_fvsProof_v_rel x (clos_Boolv b) <=> x = clos_Boolv b`,
  REWRITE_TAC[clos_Boolv_def] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_fvsProof_v_rel_cases] THEN
  REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"; GSYM CONJ_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[LIST_REL_NIL] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[]);;

let CLOSP1AUX_fvs_Boolv_HD = prove
 (`!a v' b. ALL2 clos_fvsProof_v_rel a v' /\ ~(a = []) ==>
            (clos_Boolv b = HD v' <=> clos_Boolv b = HD a)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; LIST_REL_CONS1] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[HD] THEN
  EQ_TAC THEN DISCH_THEN(ASSUME_TAC o SYM) THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_fvsProof_v_rel_simps; CLOSP1AUX_fvs_v_rel_Boolv_right]) THEN
  ASM_REWRITE_TAC[]);;

let CLOSP1AUX_eval_SING_NIL = prove
 (`!x env (s:(C,FFI)clos_state) r s2.
     clos_evaluate ([x],env,s) = (Rval r,s2) ==> ~(r = [])`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP clos_evaluate_SING) THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL]);;

(* rewrite the boolean tests on the head of a target result to the source *)
let CLOSP1AUX_BOOLV_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let nes = mapfilter (MATCH_MP CLOSP1AUX_eval_SING_NIL) asms in
  let ths = flat (map (fun ne -> mapfilter (fun a ->
               MATCH_MP CLOSP1AUX_fvs_Boolv_HD (CONJ a ne)) asms) nes) in
  REWRITE_TAC ths gl;;

let CLOSP1AUX_fvs_if = prove
 (el 3 CLOSP1AUX_fvs_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[clos_fvsProof_code_rel_def; remove_fvs_def] o
                check (CLOSP1AUX_is_app "clos_fvsProof_code_rel" o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSP1AUX_is_app "clos_evaluate" o lhs o concl)) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN REWRITE_TAC[HD_remove_fvs_SING] THEN
  CLOSP1AUX_STEP_TAC THENL [ALL_TAC; CLOSP1AUX_FIN_TAC] THEN
  CLOSP1AUX_BOOLV_TAC THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THEN
  REPEAT CLOSP1AUX_STEP_TAC THEN CLOSP1AUX_FIN_TAC);;

let CLOSP1AUX_fvs_let = prove
 (el 4 CLOSP1AUX_fvs_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[clos_fvsProof_code_rel_def; remove_fvs_def;
                                             LET_DEF; LET_END_DEF] o
                check (CLOSP1AUX_is_app "clos_fvsProof_code_rel" o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSP1AUX_is_app "clos_evaluate" o lhs o concl)) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN
  REWRITE_TAC[HD_remove_fvs_SING; clos_fvsProof_LENGTH_remove_fvs] THEN
  CLOSP1AUX_STEP_TAC THENL [ALL_TAC; CLOSP1AUX_FIN_TAC] THEN
  SUBGOAL_THEN `LENGTH (env:clos_v list) + LENGTH (xs:clos_exp list) =
                LENGTH (APPEND (a:clos_v list) env)` SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP clos_evaluate_IMP_LENGTH o
                check (fun th -> CLOSP1AUX_is_app "clos_evaluate" (lhs (concl th)) &&
                                 rand (lhs (concl th)) =
                                 `xs:clos_exp list,env:clos_v list,s:(C,FFI)clos_state`)) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL2 clos_fvsProof_v_rel (APPEND a env) (APPEND v' env2)` ASSUME_TAC THENL
   [MATCH_MP_TAC EVERY2_APPEND_suff THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CLOSP1AUX_STEP_TAC THEN CLOSP1AUX_FIN_TAC);;

let CLOSP1AUX_fvs_raise = prove
 (el 5 CLOSP1AUX_fvs_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[clos_fvsProof_code_rel_def; remove_fvs_def] o
                check (CLOSP1AUX_is_app "clos_fvsProof_code_rel" o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSP1AUX_is_app "clos_evaluate" o lhs o concl)) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN REWRITE_TAC[HD_remove_fvs_SING] THEN
  REPEAT CLOSP1AUX_STEP_TAC THEN CLOSP1AUX_FIN_TAC);;

let CLOSP1AUX_fvs_handle = prove
 (el 6 CLOSP1AUX_fvs_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[clos_fvsProof_code_rel_def; remove_fvs_def] o
                check (CLOSP1AUX_is_app "clos_fvsProof_code_rel" o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSP1AUX_is_app "clos_evaluate" o lhs o concl)) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN REWRITE_TAC[HD_remove_fvs_SING] THEN
  CLOSP1AUX_STEP_TAC THENL [CLOSP1AUX_FIN_TAC; ALL_TAC] THEN
  CLOSP1AUX_SPLIT_EXC_TAC THENL [ALL_TAC; CLOSP1AUX_FIN_TAC] THEN
  REPEAT CLOSP1AUX_STEP_TAC THEN CLOSP1AUX_FIN_TAC);;

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
let CLOSP1AUX_vr_RefPtr_shape = prove
 (`!vr xs ys.
     clos_simple_val_rel vr /\ ALL2 vr xs ys ==>
     (?b ptr. xs = [clos_RefPtr b ptr] /\ ys = [clos_RefPtr b ptr]) \/
     ((!b ptr. ~(xs = [clos_RefPtr b ptr])) /\ (!b ptr. ~(ys = [clos_RefPtr b ptr])))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSPROPSAUX_vr_left) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[clos_simple_val_rel_def] o
    check (fun th -> CLOSP1AUX_is_app "clos_simple_val_rel" (concl th))) THEN
  ASM_CASES_TAC `?b ptr. ys = [clos_RefPtr b ptr]` THENL
   [DISJ1_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `b:bool` (X_CHOOSE_THEN `ptr:num` SUBST_ALL_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`b:bool`; `ptr:num`] THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `ALL2 (vr:clos_v->clos_v->bool) xs [clos_RefPtr b ptr]` THEN
    REWRITE_TAC[LIST_REL_CONS2; LIST_REL_NIL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[CONS_11] THEN ASM_MESON_TAC[];
    DISJ2_TAC THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `ALL2 (vr:clos_v->clos_v->bool) [clos_RefPtr b ptr] ys` THEN
      REWRITE_TAC[LIST_REL_CONS1; LIST_REL_NIL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o
        check (fun th -> concl th = `~(?b ptr. ys = [clos_RefPtr b ptr])`)) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]]]);;
let CLOSP1AUX_dest_thunk_rel = prove
 (CASE_TERM `!vr (sr:(C,FFI)clos_state->(C,FFI)clos_state->bool) s t xs ys.
     clos_simple_val_rel vr /\ clos_simple_state_rel vr sr /\ sr s t /\ ALL2 vr xs ys ==>
     match clos_dest_thunk ys (clos_state_refs t) with
       clos_BadRef -> clos_dest_thunk xs (clos_state_refs s) = clos_BadRef
     | clos_NotThunk -> clos_dest_thunk xs (clos_state_refs s) = clos_NotThunk
     | clos_IsThunk m w -> ?v. clos_dest_thunk xs (clos_state_refs s) = clos_IsThunk m v /\
                              vr v w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`vr:clos_v->clos_v->bool`; `xs:clos_v list`; `ys:clos_v list`]
                CLOSP1AUX_vr_RefPtr_shape) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[CLOSP1AUX_dest_thunk_NotThunk] THEN CASE_REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[clos_dest_thunk_def] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[clos_simple_state_rel_def] o
    check (fun th -> CLOSP1AUX_is_app "clos_simple_state_rel" (concl th))) THEN
  CASES_ON `FLOOKUP (clos_state_refs (t:(C,FFI)clos_state)) ptr` THEN CASE_REWRITE_TAC[] THENL
   [RES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]; ALL_TAC] THEN
  CASES_ON `a:(clos_v)clos_ref` THEN CASE_REWRITE_TAC[] THEN
  RES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  TRY(CASES_ON `a0:thunk_mode` THEN CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN
      CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[]));;

(* the do_app of the antecedent and the consequent, related by do_app_lemma *)
(* split the pair p of an assumption tm = Rval p *)
let CLOSP1AUX_SPLIT_PAIR_TAC (tm:term) : tactic = fun (asl,w as gl) ->
  let th = snd (find (fun (_,th) -> is_eq (concl th) && lhs (concl th) = tm) asl) in
  let r = rhs (concl th) in
  if CLOSP1AUX_is_app "Rval" r && is_var (rand r) && is_type (type_of (rand r)) &&
     fst (dest_type (type_of (rand r))) = "prod"
  then (CASES_ON (rand r) THEN CASE_REWRITE_TAC[]) gl
  else ALL_TAC gl;;

let CLOSP1AUX_DO_APP_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w and con = rand w in
  let is_da t = is_comb t && CLOSP1AUX_is_app "clos_do_app" t &&
                length (snd (strip_comb t)) = 3 in
  let da = find_term is_da ant in
  let [op; xs; s] = snd (strip_comb da) in
  let db = find_term (fun t -> is_da t && hd (snd (strip_comb t)) = op) con in
  let [_; ys; t] = snd (strip_comb db) in
  let th = INST [s,`s:(C,FFI)clos_state`; t,`t:(C,FFI)clos_state`; xs,`xs:clos_v list`;
                 ys,`ys:clos_v list`; op,`opp:clos_op`] clos_fvsProof_do_app_lemma in
  (MP_TAC th THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CASES_ON da THEN CASE_REWRITE_TAC[] THEN
   CLOSP1AUX_SPLIT_PAIR_TAC da THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) gl;;

(* the do_install of the antecedent and the consequent, related by          *)
(* do_install_lemma                                                         *)
let CLOSP1AUX_DO_INSTALL_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w and con = rand w in
  let is_di t = is_comb t && CLOSP1AUX_is_app "clos_do_install" t &&
                length (snd (strip_comb t)) = 2 in
  let da = find_term is_di ant in
  let [xs; s] = snd (strip_comb da) in
  let db = find_term is_di con in
  let [ys; t] = snd (strip_comb db) in
  let th = INST [s,`s:(C,FFI)clos_state`; t,`t:(C,FFI)clos_state`; xs,`xs:clos_v list`;
                 ys,`ys:clos_v list`] clos_fvsProof_do_install_lemma in
  let rty,sty = (match dest_type (type_of da) with (_,[a;b]) -> a,b | _ -> failwith "DI") in
  incr CLOSP1AUX_counter;
  let k = string_of_int (!CLOSP1AUX_counter) in
  let r = mk_var("rr" ^ k, rty) and s' = mk_var("ss" ^ k, sty) in
  (MP_TAC th THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPEC da PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN r (X_CHOOSE_THEN s' ASSUME_TAC)) THEN
   POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
   CASES_ON r THEN CASE_REWRITE_TAC[] THEN
   DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   REPEAT(FIRST_X_ASSUM(fun th -> if CLOSP1AUX_is_app "clos_fvsProof_code_rel" (concl th)
            then SUBST_ALL_TAC (REWRITE_RULE[clos_fvsProof_code_rel_def] th) else NO_TAC))) gl;;

(* the dest_thunk of the antecedent and the consequent                      *)
let CLOSP1AUX_DEST_THUNK_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w and con = rand w in
  let is_dt t = is_comb t && CLOSP1AUX_is_app "clos_dest_thunk" t &&
                length (snd (strip_comb t)) = 2 in
  let da = find_term is_dt ant in
  let [xs; rs] = snd (strip_comb da) in
  let db = find_term is_dt con in
  let [ys; rt] = snd (strip_comb db) in
  let s = rand rs and t = rand rt in
  let th = ISPECL [`clos_fvsProof_v_rel`;
                   `clos_fvsProof_state_rel:(C,FFI)clos_state->(C,FFI)clos_state->bool`;
                   s; t; xs; ys] CLOSP1AUX_dest_thunk_rel in
  (MP_TAC th THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[CLOSP1AUX_fvs_simple_val_rel;
                                   clos_fvsProof_simple_state_rel]; ALL_TAC] THEN
   CASES_ON db THEN CASE_REWRITE_TAC[] THEN
   DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) gl;;

(* the arguments of a forced thunk are a single reference *)
let CLOSP1AUX_THUNK_ARGS_TAC : tactic = fun (asl,w as gl) ->
  let dt = snd (find (fun (_,th) -> is_eq (concl th) &&
                       CLOSP1AUX_is_app "clos_dest_thunk" (lhs (concl th)) &&
                       CLOSP1AUX_is_app "clos_IsThunk" (rhs (concl th)) &&
                       is_var (lhand (lhs (concl th)))) asl) in
  let xs = lhand (lhs (concl dt)) in
  let all2 = snd (find (fun (_,th) -> CLOSP1AUX_is_app "ALL2" (concl th) &&
                         lhand (concl th) = xs) asl) in
  let ys = rand (concl all2) in
  (MP_TAC(ISPECL [`clos_fvsProof_v_rel`; xs; ys] CLOSP1AUX_vr_RefPtr_shape) THEN
   ASM_REWRITE_TAC[CLOSP1AUX_fvs_simple_val_rel] THEN STRIP_TAC THENL
   [REPEAT(FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_var (lhs (concl th)) &&
             (lhs (concl th) = xs || lhs (concl th) = ys) then SUBST_ALL_TAC th else NO_TAC));
    MP_TAC(SPECL [xs; rand (lhs (concl dt))] CLOSP1AUX_dest_thunk_NotThunk) THEN
    ASM_REWRITE_TAC[distinctness "clos_dest_thunk_ret"]]) gl;;

(* the update_thunk of the antecedent and the consequent                    *)
let CLOSP1AUX_UPDATE_THUNK_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w and con = rand w in
  let is_ut t = is_comb t && CLOSP1AUX_is_app "clos_update_thunk" t &&
                length (snd (strip_comb t)) = 3 in
  let ua = find_term is_ut ant in
  let [xs; rs; vs] = snd (strip_comb ua) in
  let ub = find_term is_ut con in
  let [_; rt; ws] = snd (strip_comb ub) in
  let s1 = rand rs and s2 = rand rt in
  let [rp] = dest_list xs in
  let [b; ptr] = snd (strip_comb rp) in
  let th0 = INST [s1,`s1:(C,FFI)clos_state`; s2,`s2:(C,FFI)clos_state`; vs,`vs:clos_v list`;
                  ws,`ys:clos_v list`; b,`v:bool`; ptr,`ptr:num`]
                 clos_fvsProof_rel_update_thunk in
  (CASES_ON ua THEN CASE_REWRITE_TAC[] THEN
   (fun (asl,w as gl) ->
      let eq = snd (find (fun (_,th) -> is_eq (concl th) && lhs (concl th) = ua) asl) in
      let r = rhs (concl eq) in
      let th1 = if is_const r then th0
                else INST [rand r, `refs1:(num,(clos_v)clos_ref)fmap`] th0 in
      (MP_TAC th1 THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       ASM_REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
       DISCH_THEN(STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) gl)) gl;;

(* the last value of related result lists                                 *)
let CLOSP1AUX_LAST_TAC : tactic =
  MATCH_MP_TAC LIST_REL_LAST THEN ASM_REWRITE_TAC[] THEN
  (fun (asl,w as gl) ->
     let lens = mapfilter (MATCH_MP clos_evaluate_IMP_LENGTH) (map snd asl) in
     (MAP_EVERY MP_TAC lens THEN ASM_MESON_TAC[LENGTH_EQ_NIL]) gl);;

let CLOSP1AUX_fvs_op = prove
 (el 7 CLOSP1AUX_fvs_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[clos_fvsProof_code_rel_def; remove_fvs_def] o
                check (CLOSP1AUX_is_app "clos_fvsProof_code_rel" o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSP1AUX_is_app "clos_evaluate" o lhs o concl)) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN REWRITE_TAC[HD_remove_fvs_SING] THEN
  CLOSP1AUX_STEP_TAC THENL [ALL_TAC; CLOSP1AUX_FIN_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP EVERY2_REVERSE o
              check (fun th -> CLOSP1AUX_is_app "ALL2" (concl th) &&
                               not (lhand (concl th) = `env:clos_v list`))) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [CLOSP1AUX_DO_INSTALL_TAC THEN REPEAT CLOSP1AUX_STEP_TAC THEN CLOSP1AUX_FIN_TAC THEN
    CLOSP1AUX_LAST_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [CLOSP1AUX_DEST_THUNK_TAC THEN TRY(CLOSP1AUX_FIN_TAC THEN NO_TAC) THEN
    CASES_ON `a0:thunk_mode` THEN CASE_REWRITE_TAC[] THENL [CLOSP1AUX_FIN_TAC; ALL_TAC] THEN
    CLOSP1AUX_THUNK_ARGS_TAC THEN
    CLOSP1AUX_STEP_TAC THENL [CLOSP1AUX_UPDATE_THUNK_TAC; ALL_TAC] THEN CLOSP1AUX_FIN_TAC;
    CLOSP1AUX_DO_APP_TAC THEN CLOSP1AUX_FIN_TAC]);;

(* a related closure: the code relation up to the order of the sum *)
let CLOSP1AUX_CLOSURE_TAC : tactic =
  REWRITE_TAC[clos_fvsProof_v_rel_simps; injectivity "clos_v"; GSYM CONJ_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  ASM_REWRITE_TAC[ALL2; clos_fvsProof_code_rel_def; HD_remove_fvs_SING] THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP lookup_vars_SOME o
           check (fun th -> is_eq (concl th) &&
                            CLOSP1AUX_is_app "lookup_vars" (lhs (concl th))))) THEN
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* the lookup_vars of the antecedent and the consequent *)
let CLOSP1AUX_LOOKUP_VARS_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w and con = rand w in
  let is_lv t = is_comb t && CLOSP1AUX_is_app "lookup_vars" t &&
                length (snd (strip_comb t)) = 2 in
  let la = find_term is_lv ant in
  let [vs; e1] = snd (strip_comb la) in
  let lb = find_term (fun t -> is_lv t && lhand t = vs) con in
  let e2 = rand lb in
  (MP_TAC(SPECL [vs; e1; e2] clos_fvsProof_lookup_vars_lemma) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CASES_ON la THEN CASE_REWRITE_TAC[] THEN
   DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) gl;;

let CLOSP1AUX_fvs_fn = prove
 (el 8 CLOSP1AUX_fvs_cases,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[clos_fvsProof_code_rel_def; remove_fvs_def;
                                             LET_DEF; LET_END_DEF] o
                check (CLOSP1AUX_is_app "clos_fvsProof_code_rel" o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSP1AUX_is_app "clos_evaluate" o lhs o concl)) THEN
  REWRITE_TAC[clos_evaluate_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2
    (REWRITE_RULE[clos_fvsProof_state_rel_def] th))))]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL [ALL_TAC; CLOSP1AUX_FIN_TAC] THEN
  CASES_ON `vsopt:(num list)option` THEN CASE_REWRITE_TAC[] THEN
  TRY CLOSP1AUX_LOOKUP_VARS_TAC THEN CLOSP1AUX_FIN_TAC THEN CLOSP1AUX_CLOSURE_TAC);;

(* a local helper: a case on a pair built by a case on a pair *)
let CLOSP1AUX_pair_CASE_CASE = prove
 (`!(x:A#B) (f:A->B->C#D) (g:C->D->E).
     pair_CASE (pair_CASE x f) g = pair_CASE x (\a b. pair_CASE (f a b) g)`,
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE]);;

let CLOSP1AUX_fvs_letrec = prove
 (el 9 CLOSP1AUX_fvs_cases,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[clos_fvsProof_code_rel_def; remove_fvs_def;
                                             LET_DEF; LET_END_DEF] o
                check (CLOSP1AUX_is_app "clos_fvsProof_code_rel" o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSP1AUX_is_app "clos_evaluate" o lhs o concl)) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; HD_remove_fvs_SING] THEN BETA_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2
    (REWRITE_RULE[clos_fvsProof_state_rel_def] th))))]) THEN
  REWRITE_TAC[ALL_MAP; o_DEF; LENGTH_MAP] THEN
  REWRITE_TAC[CLOSP1AUX_pair_CASE_CASE] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL [ALL_TAC; CLOSP1AUX_FIN_TAC] THEN
  CASES_ON `namesopt:(num list)option` THEN CASE_REWRITE_TAC[] THENL
   [REPEAT CLOSP1AUX_STEP_TAC THEN CLOSP1AUX_FIN_TAC;
    CLOSP1AUX_LOOKUP_VARS_TAC THEN REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN
    TRY(CLOSP1AUX_FIN_TAC THEN NO_TAC) THEN
    FIRST_ASSUM(fun th -> if is_eq (concl th) &&
                             CLOSP1AUX_is_app "lookup_vars" (lhs (concl th)) &&
                             rand (lhs (concl th)) = `env:clos_v list`
                          then REWRITE_TAC[MATCH_MP lookup_vars_SOME th] else NO_TAC) THEN
    REPEAT CLOSP1AUX_STEP_TAC THEN CLOSP1AUX_FIN_TAC]);;

(* local helpers: clock updates of related states; the evaluate_app of the  *)
(* antecedent; the states with a decreased clock of the antecedent          *)
let CLOSP1AUX_fvs_state_rel_clock = prove
 (`!(s:(C,FFI)clos_state) t n.
     clos_fvsProof_state_rel s t ==>
     clos_fvsProof_state_rel (clos_state_clock_fupd (K n) s) (clos_state_clock_fupd (K n) t) /\
     clos_fvsProof_state_rel (clos_dec_clock n s) (clos_dec_clock n t)`,
  REWRITE_TAC[clos_fvsProof_state_rel_def; clos_dec_clock_def;
              clos_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[]);;
let CLOSP1AUX_STATE_CLOCK_TAC : tactic =
  FIRST_ASSUM(fun th -> if CLOSP1AUX_is_app "clos_fvsProof_state_rel" (concl th)
                        then MP_TAC (GEN `n:num` (MATCH_MP CLOSP1AUX_fvs_state_rel_clock th))
                        else NO_TAC) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC;;

let CLOSP1AUX_APP_Q_TAC : tactic =
  CLOSP1AUX_SING_TAC THEN REWRITE_TAC[HD] THEN CASE_REWRITE_TAC[] THEN
  CLOSP1AUX_COND_IH_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> if CLOSP1AUX_is_Q th then MATCH_MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[HD];;

(* the states with a decreased clock of the antecedent are related *)
let CLOSP1AUX_DEC_CLOCK_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w in
  let dcs = find_terms (fun t -> is_comb t && CLOSP1AUX_is_app "clos_dec_clock" t &&
                                 length (snd (strip_comb t)) = 2) ant in
  let srs = filter (fun th -> CLOSP1AUX_is_app "clos_fvsProof_state_rel" (concl th))
                   (map snd asl) in
  let ths = flat (map (fun dc ->
     let [k;x] = snd (strip_comb dc) in
     mapfilter (fun sr -> if lhand (concl sr) = x
                          then CONJUNCT2 (SPEC k (MATCH_MP CLOSP1AUX_fvs_state_rel_clock sr))
                          else failwith "DEC") srs) dcs) in
  MAP_EVERY ASSUME_TAC ths gl;;

let CLOSP1AUX_fvs_app = prove
 (el 10 CLOSP1AUX_fvs_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[clos_fvsProof_code_rel_def; remove_fvs_def] o
                check (CLOSP1AUX_is_app "clos_fvsProof_code_rel" o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSP1AUX_is_app "clos_evaluate" o lhs o concl)) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN
  REWRITE_TAC[HD_remove_fvs_SING; clos_fvsProof_LENGTH_remove_fvs] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL [ALL_TAC; CLOSP1AUX_FIN_TAC] THEN
  REPEAT CLOSP1AUX_STEP_TAC THEN TRY(CLOSP1AUX_FIN_TAC THEN NO_TAC) THEN
  CLOSP1AUX_APP_Q_TAC);;

let CLOSP1AUX_fvs_tick = prove
 (el 11 CLOSP1AUX_fvs_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[clos_fvsProof_code_rel_def; remove_fvs_def] o
                check (CLOSP1AUX_is_app "clos_fvsProof_code_rel" o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSP1AUX_is_app "clos_evaluate" o lhs o concl)) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN REWRITE_TAC[HD_remove_fvs_SING] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2
    (REWRITE_RULE[clos_fvsProof_state_rel_def] th))))))]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP clos_fvsProof_state_rel_dec_clock) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL [CLOSP1AUX_FIN_TAC; ALL_TAC] THEN
  REPEAT CLOSP1AUX_STEP_TAC THEN CLOSP1AUX_FIN_TAC);;

let CLOSP1AUX_fvs_call = prove
 (el 12 CLOSP1AUX_fvs_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[clos_fvsProof_code_rel_def; remove_fvs_def] o
                check (CLOSP1AUX_is_app "clos_fvsProof_code_rel" o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSP1AUX_is_app "clos_evaluate" o lhs o concl)) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN REWRITE_TAC[HD_remove_fvs_SING] THEN
  CLOSP1AUX_STEP_TAC THENL [ALL_TAC; CLOSP1AUX_FIN_TAC] THEN
  FIRST_ASSUM(fun th -> if CLOSP1AUX_is_app "clos_fvsProof_state_rel" (concl th) &&
                           not (rand (concl th) = `t1:(C,FFI)clos_state`)
                        then REWRITE_TAC[MATCH_MP clos_fvsProof_find_code_lemma th]
                        else NO_TAC) THEN
  CASE_REWRITE_TAC[] THEN CLOSP1AUX_FIN_TAC);;

let CLOSP1AUX_fvs_app_nil = prove
 (el 13 CLOSP1AUX_fvs_cases,
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_app_NIL; LIST_REL_NIL; PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`Rval [f2]:(clos_v list,clos_v)result`; `t1:(C,FFI)clos_state`] THEN
  ASM_REWRITE_TAC[evaluate_app_NIL; result_rel_def; ALL2]);;

(* unwind the equations c = x (x bound) in the antecedent of a hypothesis *)
let CLOSP1AUX_UNWIND_RULE th =
  let vs,bod = strip_forall (concl th) in
  let ant = lhand bod in
  let eqs = filter (fun t -> is_eq t && mem (rhs t) vs && not (mem (lhs t) vs))
                   (conjuncts ant) in
  if eqs = [] then failwith "UNWIND" else
  let th1 = INST (map (fun t -> (lhs t, rhs t)) eqs) (SPEC_ALL th) in
  let rest = filter (fun v -> not (mem v (map rhs eqs))) vs in
  GENL rest (REWRITE_RULE[] th1);;

(* a related closure value; dest_closure gives NONE or Partial_app for      *)
(* related arguments in step                                               *)
let CLOSP1AUX_VREL_TAC : tactic =
  REWRITE_TAC[clos_fvsProof_v_rel_simps; injectivity "clos_v"; GSYM CONJ_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE CLOSP1AUX_ALL2_TAC);;

let CLOSP1AUX_fvs_dest_closure_NONE_Partial = prove
 (`clos_fvsProof_v_rel f1 f2 /\ ALL2 clos_fvsProof_v_rel args1 args2 ==>
   (dest_closure max_app loc_opt f1 args1 = NONE ==>
    dest_closure max_app loc_opt f2 args2 = NONE) /\
   (!v. dest_closure max_app loc_opt f1 args1 = SOME (Partial_app v) ==>
        ?w. dest_closure max_app loc_opt f2 args2 = SOME (Partial_app w) /\
            clos_fvsProof_v_rel v w)`,
  CASES_ON `f1:clos_v` THEN REWRITE_TAC[clos_fvsProof_v_rel_simps] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN CLOSP1AUX_ALL2_LENGTH_TAC THEN
  REWRITE_TAC[dest_closure_def] THEN CASE_REWRITE_TAC[] THENL
   [CLOSP1AUX_LEN_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(COND_CASES_TAC THEN
           ASM_REWRITE_TAC[distinctness "option"; injectivity "option";
                           distinctness "app_kind"; injectivity "app_kind"]) THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[UNWIND_THM1] THEN CLOSP1AUX_VREL_TAC;
    ALL_TAC] THEN
  REPEAT PAIRARG_TAC THEN
  ASM_CASES_TAC `LENGTH (a3:(num#clos_exp)list) <= a4` THENL
   [SUBGOAL_THEN `LENGTH (funs2:(num#clos_exp)list) <= a4` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[distinctness "option"]; ALL_TAC] THEN
  SUBGOAL_THEN `~(LENGTH (funs2:(num#clos_exp)list) <= a4)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `a4:num` o CONJUNCT2 o REWRITE_RULE[LIST_REL_EL_EQN] o
              check (fun th -> CLOSP1AUX_is_app "ALL2" (concl th) &&
                               CLOSP1AUX_mentions "clos_fvsProof_f_rel" (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[clos_fvsProof_f_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CLOSP1AUX_LEN_TAC THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "option"; injectivity "option";
                                             distinctness "app_kind"; injectivity "app_kind"]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[UNWIND_THM1] THEN CLOSP1AUX_VREL_TAC);;

let CLOSP1AUX_fvs_app_cons = prove
 (el 14 CLOSP1AUX_fvs_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOSP1AUX_is_app "ALL2" (concl th) &&
                                          is_cons (lhand (concl th)))) THEN
  REWRITE_TAC[LIST_REL_CONS1] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSP1AUX_is_app "evaluate_app" o lhs o concl)) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2
    (REWRITE_RULE[clos_fvsProof_state_rel_def] th))))]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2
    (REWRITE_RULE[clos_fvsProof_state_rel_def] th))))))]) THEN
  REWRITE_TAC[LENGTH] THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
  CLOSP1AUX_LEN_TAC THEN CLOSP1AUX_STATE_CLOCK_TAC THEN
  MP_TAC(INST [`f:clos_v`,`f1:clos_v`; `CONS (v4:clos_v) v5`,`args1:clos_v list`;
               `CONS (h':clos_v) t'`,`args2:clos_v list`;
               `clos_state_max_app (s:(C,FFI)clos_state)`,`max_app:num`]
              CLOSP1AUX_fvs_dest_closure_NONE_Partial) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ALL2]; ALL_TAC] THEN
  CASES_ON `dest_closure (clos_state_max_app (s:(C,FFI)clos_state)) loc_opt f (CONS v4 v5)` THEN
  CASE_REWRITE_TAC[] THENL
   [DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CASE_REWRITE_TAC[] THEN CLOSP1AUX_FIN_TAC;
    ALL_TAC] THEN
  CASES_ON `a:app_kind` THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[MESON[] `!a:clos_v P. (!x. a = x ==> P x) <=> P a`] THEN
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN CLOSP1AUX_FIN_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "option"; injectivity "app_kind"]) THEN
  RULE_ASSUM_TAC(fun th -> try CLOSP1AUX_UNWIND_RULE th with Failure _ -> th) THEN
  MP_TAC(INST [`f:clos_v`,`f1:clos_v`; `v4:clos_v`,`a1:clos_v`; `h':clos_v`,`a2:clos_v`;
               `v5:clos_v list`,`args1:clos_v list`; `t':clos_v list`,`args2:clos_v list`;
               `clos_state_max_app (s:(C,FFI)clos_state)`,`max_app:num`;
               `a0:clos_exp`,`exp1:clos_exp`; `a1:clos_v list`,`env1:clos_v list`;
               `a2:clos_v list`,`rest_args1:clos_v list`]
              clos_fvsProof_dest_closure_SOME_Full_app) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CLOSP1AUX_LEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL [CLOSP1AUX_FIN_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if CLOSP1AUX_is_app "clos_fvsProof_code_rel" (concl th)
                          then REWRITE_TAC[REWRITE_RULE[clos_fvsProof_code_rel_def] th]
                          else NO_TAC) THEN
  CLOSP1AUX_DEC_CLOCK_TAC THEN
  CLOSP1AUX_STEP_TAC THENL [CLOSP1AUX_APP_Q_TAC; CLOSP1AUX_FIN_TAC]);;

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
  MATCH_ACCEPT_TAC(MATCH_MP CLOSP1AUX_fvs_ind (end_itlist CONJ
    [CLOSP1AUX_fvs_nil; CLOSP1AUX_fvs_cons; CLOSP1AUX_fvs_var; CLOSP1AUX_fvs_if;
     CLOSP1AUX_fvs_let; CLOSP1AUX_fvs_raise; CLOSP1AUX_fvs_handle; CLOSP1AUX_fvs_op;
     CLOSP1AUX_fvs_fn; CLOSP1AUX_fvs_letrec; CLOSP1AUX_fvs_app; CLOSP1AUX_fvs_tick;
     CLOSP1AUX_fvs_call; CLOSP1AUX_fvs_app_nil; CLOSP1AUX_fvs_app_cons])));;

let remove_fvs_correct = prove
 (`!xs env1 (s1:(C,FFI)clos_state) res1 s2 env2 t1.
     clos_evaluate (xs,env1,s1) = (res1,s2) /\
     ALL2 clos_fvsProof_v_rel env1 env2 /\ clos_fvsProof_state_rel s1 t1 ==>
     ?res2 t2.
       clos_evaluate (remove_fvs (LENGTH env1) xs,env2,t1) = (res2,t2) /\
       result_rel (ALL2 clos_fvsProof_v_rel) clos_fvsProof_v_rel res1 res2 /\
       clos_fvsProof_state_rel s2 t2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`xs:clos_exp list`; `env1:clos_v list`; `s1:(C,FFI)clos_state`;
                `res1:(clos_v list,clos_v)result`; `s2:(C,FFI)clos_state`;
                `remove_fvs (LENGTH (env1:clos_v list)) xs`; `env2:clos_v list`;
                `t1:(C,FFI)clos_state`] (CONJUNCT1 evaluate_remove_fvs)) THEN
  ASM_REWRITE_TAC[clos_fvsProof_code_rel_def]);;

(* preservation of observational semantics *)

(* HOL4: semantics_compile *)
let clos_fvsProof_semantics_compile = prove
 (`~(clos_semantics (ffi:(FFI)ffi_state) max_app FEMPTY (co:num->C#clos_prog)
       (pure_cc clos_fvs_compile_inc cc) xs = Fail) ==>
   (!n. SND (SND (co n)) = []) /\ 1 <= max_app ==>
   clos_semantics ffi max_app FEMPTY (pure_co clos_fvs_compile_inc o co) cc
     (clos_fvs_compile xs) =
   clos_semantics ffi max_app FEMPTY co (pure_cc clos_fvs_compile_inc cc) xs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ffi:(FFI)ffi_state`; `max_app:num`; `FEMPTY:(num,num#clos_exp)fmap`;
                 `co:num->C#clos_prog`;
                 `(pure_cc clos_fvs_compile_inc
                     (cc:C->clos_prog->(byte list#int64 list#C)option)):
                    C->clos_prog->(byte list#int64 list#C)option`;
                 `xs:clos_exp list`; `FEMPTY:(num,num#clos_exp)fmap`;
                 `(pure_co clos_fvs_compile_inc o (co:num->C#clos_prog)):num->C#clos_prog`;
                 `cc:C->clos_prog->(byte list#int64 list#C)option`;
                 `clos_fvs_compile xs`;
                 `\(c1:(num,num#clos_exp)fmap) (o1:num->C#clos_prog)
                   (k1:C->clos_prog->(byte list#int64 list#C)option) (e1:clos_exp list)
                   (c2:(num,num#clos_exp)fmap) (o2:num->C#clos_prog)
                   (k2:C->clos_prog->(byte list#int64 list#C)option) (e2:clos_exp list). T`]
                clos_IMP_semantics_eq) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[clos_eval_sim_def] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; clos_fvs_compile_def] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] remove_fvs_correct) o
              check (CLOSP1AUX_is_app "clos_evaluate" o lhs o concl)) THEN
  DISCH_THEN(MP_TAC o SPECL [`[]:clos_v list`;
    `clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY
       ((pure_co clos_fvs_compile_inc o (co:num->C#clos_prog)):num->C#clos_prog)
       (cc:C->clos_prog->(byte list#int64 list#C)option) k`]) THEN
  REWRITE_TAC[ALL2; LENGTH] THEN ANTS_TAC THENL
   [REWRITE_TAC[clos_fvsProof_state_rel_def; clos_initial_state_def;
                clos_state_INFO.ri_accessors; ALL2; fmap_rel_FEMPTY; o_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`res2:(clos_v list,clos_v)result`; `t2:(C,FFI)clos_state`] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[clos_fvsProof_state_rel_def] o
    check (CLOSP1AUX_is_app "clos_fvsProof_state_rel" o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSP1AUX_is_app "result_rel" o concl)) THEN
  CASES_ON `res1:(clos_v list,clos_v)result` THEN CASES_ON `res2:(clos_v list,clos_v)result` THEN
  REWRITE_TAC[result_rel_def] THEN
  TRY(CASES_ON `a:(clos_v)error_result` THEN CASES_ON `a':(clos_v)error_result`) THEN
  REWRITE_TAC[exc_rel_def]);;

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

let CLOSP1AUX_rfs_fv = prove
 (`(!fvs e. every_Fn_vs_NONE [e] ==> !v. fv1 v (remove_fvs_sing fvs e) ==> v < fvs) /\
   (!fvs es. every_Fn_vs_NONE es ==> !v. fv v (remove_fvs_list fvs es) ==> v < fvs) /\
   (!m fvs fns. every_Fn_vs_NONE (MAP SND fns) ==>
                !v n x. MEM (n,x) (remove_fvs_let m fvs fns) /\ fv1 v x ==> v < n + m + fvs)`,
  MATCH_MP_TAC remove_fvs_sing_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[remove_fvs_sing_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[fv1_thm; fv_def; every_Fn_vs_NONE_def; MEM; fv_cons; MAP;
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
      COND_CASES_TAC THEN REWRITE_TAC[fv1_thm; fv_def] THEN ASM_ARITH_TAC) THEN
  CLOSPROPSAUX_RES_TAC THEN TRY ASM_ARITH_TAC);;

let fv_max_remove_fvs = prove
 (`!fvs xs. every_Fn_vs_NONE xs ==> (!v. fv v (remove_fvs fvs xs) ==> v < fvs)`,
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
