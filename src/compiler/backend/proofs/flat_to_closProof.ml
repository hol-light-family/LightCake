(* ========================================================================= *)
(* flat_to_closProof: port of HOL4 compiler/backend/proofs/                  *)
(* flat_to_closProofScript.sml (CakeML v3479, HOL4 lines 1-2601).            *)
(* Correctness proof for flat_to_clos.                                       *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as in names.tsv: this script's v_rel, env_rel and state_rel are  *)
(*   flat_to_closProof_v_rel, flat_to_closProof_env_rel and                  *)
(*   flat_to_closProof_state_rel; flat_to_clos' compile, compile_decs,       *)
(*   compile_prog, compile_op and dest_Constant are flat_to_clos_compile ... *)
(* - flatSem values are flat_v (flat_Loc, flat_Litv, flat_Conv,              *)
(*   flat_Vectorv, flat_Closure, flat_Recclosure), closSem values clos_v     *)
(*   (clos_RefPtr, clos_Number, clos_Word64, clos_Block, ByteVector,         *)
(*   clos_Closure, clos_Recclosure); flatSem's evaluate env s es is          *)
(*   flat_evaluate env s es, closSem's evaluate (es,env,s) is clos_evaluate; *)
(*   the states are (C,FFI)flat_state and (C,FFI)clos_state.                 *)
(* - Library: EVERY = ALL, LIST_REL = ALL2, GENLIST = list_of_seq, LEAST =   *)
(*   minimal, n2w = word, w2n = val, the empty bag = EMPTY_BAG, bag union = *)
(*   BAG_UNION, the bag of 0 = BAG_INSERT 0 EMPTY_BAG, FOLDR f e l =        *)
(*   ITLIST f l e; r with f := x is RECTYPE_f_fupd (K x) r.                  *)
(* - HOL4's paired lambda of compile's Letrec clause, \(f,v,x). t, is       *)
(*   written as in flat_to_clos.ml (\p. match p with (f,v,x) -> t), also in *)
(*   v_rel.                                                                  *)
(* - inc_compile_decs' is polymorphic in the type of its empty list, as in  *)
(*   HOL4 (A list), and so is the cc argument of install_config_rel' (B     *)
(*   list); state_rel fixes them to (num # num # clos_exp) list.             *)
(* - HOL4's ML value op_goal (HOL4 line 634) is written out in each op_     *)
(*   theorem; compile_correct (HOL4 line 261, proved by suspend/Resume       *)
(*   blocks) is stated at its Finalise (HOL4 line 1995), after the lemmas    *)
(*   proved between the Resume blocks.  The derived theorems v_rel_def and   *)
(*   env_rel_def (SIMP_CONV/ONCE_REWRITE_CONV with v_rel_cases) and          *)
(*   compile_decs_correct (the last conjunct of compile_correct) are stated. *)
(* - contains_App_SOME_compile_init is bound twice, as in HOL4 (lines 2531  *)
(*   and 2549; the second rebinds the name).                                 *)
(* - F2CPAUX_ names are local helpers.                                       *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/bag.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/evaluate.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_interp.ml";;
needs "compiler/backend/flat_to_clos.ml";;
needs "compiler/backend/semantics/flatSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/flatProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/proofs/clos_interpProof.ml";;

prioritize_num();;
type_invention_error := true;;


(* HOL4 line 13 *)
let LIST_REL_EL = prove
 (`!xs ys (r:A->B->bool).
     ALL2 r xs ys <=>
     LENGTH xs = LENGTH ys /\
     (!n. n < LENGTH ys ==> r (EL n xs) (EL n ys))`,
  REWRITE_TAC[LIST_REL_EL_EQN] THEN MESON_TAC[]);;

(* HOL4 line 25 *)
let flat_to_closProof_v_rel_rules,flat_to_closProof_v_rel_ind,
    flat_to_closProof_v_rel_cases,flat_to_closProof_v_rel_strongind =
  cake_inductive
  `(!n b. flat_to_closProof_v_rel (flat_Loc b n) (clos_RefPtr b n)) /\
   (!i. flat_to_closProof_v_rel (flat_Litv (IntLit i)) (clos_Number i)) /\
   (!c. flat_to_closProof_v_rel (flat_Litv (Char c)) (clos_Number (&(ORD c)))) /\
   (!s. flat_to_closProof_v_rel (flat_Litv (StrLit s))
          (ByteVector (MAP (word o ORD) (explode s)))) /\
   (!b. flat_to_closProof_v_rel (flat_Litv (Word8 b)) (clos_Number (&(val b)))) /\
   (!w. flat_to_closProof_v_rel (flat_Litv (Word64 w)) (clos_Word64 w)) /\
   (!f. flat_to_closProof_v_rel (flat_Litv (Float64 f)) (clos_Word64 f)) /\
   (!vs ws. ALL2 flat_to_closProof_v_rel vs ws
            ==> flat_to_closProof_v_rel (flat_Conv NONE vs) (clos_Block 0 ws)) /\
   (!vs ws t r. ALL2 flat_to_closProof_v_rel vs ws
                ==> flat_to_closProof_v_rel (flat_Conv (SOME (t,r)) vs)
                      (clos_Block t ws)) /\
   (!vs ws. ALL2 flat_to_closProof_v_rel vs ws
            ==> flat_to_closProof_v_rel (flat_Vectorv vs) (clos_Block 0 ws)) /\
   (!env m db.
      (!n x. ALOOKUP (flat_environment_v env) n = SOME x
             ==> findi (SOME n) m < LENGTH db /\
                 flat_to_closProof_v_rel x (EL (findi (SOME n) m) db))
      ==> flat_to_closProof_env_rel env (m:(mlstring option)list)
            (db:clos_v list)) /\
   (!env m db n e.
      flat_to_closProof_env_rel env m db /\ no_Mat e
      ==> flat_to_closProof_v_rel (flat_Closure env n e)
            (clos_Closure NONE [] db 1
               (HD (flat_to_clos_compile (CONS (SOME n) m) [e])))) /\
   (!funs n env m db.
      n < LENGTH funs /\ flat_to_closProof_env_rel env m db /\
      ALL_DISTINCT (MAP FST funs) /\ ALL no_Mat (MAP (SND o SND) funs)
      ==> flat_to_closProof_v_rel (flat_Recclosure env funs (FST (EL n funs)))
            (clos_Recclosure NONE [] db
               (MAP (\p. match p with
                           (f,v,x) ->
                             (1, HD (flat_to_clos_compile
                                       (CONS (SOME v)
                                          (APPEND (MAP (\n. SOME (FST n)) funs) m))
                                       [x])))
                    funs) n))`;;

(* HOL4 line 55: v_rel_def is SIMP_CONV (srw_ss()) [Once v_rel_cases] of   *)
(* eleven patterns, LIST_CONJ; stated with the resulting right sides        *)
let flat_to_closProof_v_rel_def = prove
 (CASE_TERM
  `(!b n x1. flat_to_closProof_v_rel (flat_Loc b n) x1 <=> x1 = clos_RefPtr b n) /\
   (!l1 x1. flat_to_closProof_v_rel (flat_Litv (IntLit l1)) x1 <=>
            x1 = clos_Number l1) /\
   (!s x1. flat_to_closProof_v_rel (flat_Litv (StrLit s)) x1 <=>
           x1 = ByteVector (MAP (word o ORD) (explode s))) /\
   (!c x1. flat_to_closProof_v_rel (flat_Litv (Char c)) x1 <=>
           x1 = clos_Number (&(ORD c))) /\
   (!b x1. flat_to_closProof_v_rel (flat_Litv (Word8 b)) x1 <=>
           x1 = clos_Number (&(val b))) /\
   (!w x1. flat_to_closProof_v_rel (flat_Litv (Word64 w)) x1 <=>
           x1 = clos_Word64 w) /\
   (!w x1. flat_to_closProof_v_rel (flat_Litv (Float64 w)) x1 <=>
           x1 = clos_Word64 w) /\
   (!y x1. flat_to_closProof_v_rel (flat_Vectorv y) x1 <=>
           ?ws. x1 = clos_Block 0 ws /\ ALL2 flat_to_closProof_v_rel y ws) /\
   (!x y x1. flat_to_closProof_v_rel (flat_Conv x y) x1 <=>
             (?ws. x = NONE /\ x1 = clos_Block 0 ws /\
                   ALL2 flat_to_closProof_v_rel y ws) \/
             (?ws t r. x = SOME (t,r) /\ x1 = clos_Block t ws /\
                       ALL2 flat_to_closProof_v_rel y ws)) /\
   (!x y z x1. flat_to_closProof_v_rel (flat_Closure x y z) x1 <=>
               ?m db. x1 = clos_Closure NONE [] db 1
                             (HD (flat_to_clos_compile (CONS (SOME y) m) [z])) /\
                      flat_to_closProof_env_rel x m db /\ no_Mat z) /\
   (!x y t x1. flat_to_closProof_v_rel (flat_Recclosure x y t) x1 <=>
               ?n m db.
                 t = FST (EL n y) /\
                 x1 = clos_Recclosure NONE [] db
                        (MAP (\p. match p with
                                    (f,v,x') ->
                                      (1, HD (flat_to_clos_compile
                                                (CONS (SOME v)
                                                   (APPEND (MAP (\n. SOME (FST n)) y) m))
                                                [x'])))
                             y) n /\
                 n < LENGTH y /\ flat_to_closProof_env_rel x m db /\
                 ALL_DISTINCT (MAP FST y) /\ ALL no_Mat (MAP (SND o SND) y))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [CONJUNCT2 flat_to_closProof_v_rel_cases] THEN
  REWRITE_TAC[distinctness "flat_v"; injectivity "flat_v"; distinctness "lit";
              injectivity "lit"; distinctness "option"; injectivity "option"] THEN
  MESON_TAC[]);;

(* HOL4 line 70: env_rel_def = ONCE_REWRITE_CONV [v_rel_cases] of          *)
(* env_rel env m db                                                          *)
let flat_to_closProof_env_rel_def = prove
 (`!env m db.
     flat_to_closProof_env_rel env m db <=>
     !n x. ALOOKUP (flat_environment_v env) n = SOME x
           ==> findi (SOME n) m < LENGTH db /\
               flat_to_closProof_v_rel x (EL (findi (SOME n) m) db)`,
  MATCH_ACCEPT_TAC (CONJUNCT1 flat_to_closProof_v_rel_cases));;

(* HOL4 line 72 *)
let store_rel_def = cake_def
  `store_rel (refs:(flat_v store_v)list) (t_refs:(num,(clos_v)clos_ref)fmap) <=>
     !i. if LENGTH refs <= i then FLOOKUP t_refs i = NONE else
           match EL i refs with
             Refv v -> (?x. FLOOKUP t_refs i = SOME (clos_ValueArray [x]) /\
                            flat_to_closProof_v_rel v x)
           | Thunk m v -> (?x. FLOOKUP t_refs i = SOME (clos_Thunk m x) /\
                               flat_to_closProof_v_rel v x)
           | Varray vs -> (?xs. FLOOKUP t_refs i = SOME (clos_ValueArray xs) /\
                                ALL2 flat_to_closProof_v_rel vs xs)
           | W8array bs -> FLOOKUP t_refs i = SOME (clos_ByteArray bs)`;;

(* HOL4 line 83 *)
let inc_compile_decs'_def = cake_def
  `inc_compile_decs' decs =
     (APPEND (flat_to_clos_compile_decs decs)
             (flat_to_clos_compile_decs [flat_Con backend_common_None NONE []]),
      []:A list)`;;

(* HOL4 line 88 *)
let install_config_rel'_def = cake_def
  `install_config_rel' (ic:(C)install_config) (co:num -> C # clos_prog)
                       (cc:C -> clos_exp list # B list -> (byte list # int64 list # C)option) <=>
     (!i. no_Mat_decs (SND (install_config_compile_oracle ic i))) /\
     co = pure_co inc_compile_decs' o install_config_compile_oracle ic /\
     install_config_compile ic = pure_cc inc_compile_decs' cc`;;

(* HOL4 line 96 *)
let flat_to_closProof_state_rel_def = cake_def
  `flat_to_closProof_state_rel (s:(C,FFI)flat_state) (t:(C,FFI)clos_state) <=>
     1 <= clos_state_max_app t /\
     flat_state_ffi s = clos_state_ffi t /\
     flat_state_clock s = clos_state_clock t /\
     store_rel (flat_state_refs s) (clos_state_refs t) /\
     ~(LENGTH (clos_state_globals t) = 0) /\
     ALL2 (OPTREL flat_to_closProof_v_rel) (flat_state_globals s)
       (TL (clos_state_globals t)) /\
     install_config_rel' (flat_state_eval_config s) (clos_state_compile_oracle t)
       (clos_state_compile t)`;;

(* HOL4 line 108 *)
let v_rel_to_list = prove
 (`!x y xs. flat_to_closProof_v_rel x y /\ flat_v_to_list x = SOME xs
            ==> ?ys. clos_v_to_list y = SOME ys /\
                     ALL2 flat_to_closProof_v_rel xs ys`,
  MATCH_MP_TAC flat_v_to_list_ind THEN
  REWRITE_TAC[flat_v_to_list_def; distinctness "option"] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_to_closProof_v_rel_def]) THEN
  FS[COND_CASE_EQ; option_case_eq] THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN RES_TAC THEN
  ASM_REWRITE_TAC[clos_v_to_list_def; ALL2] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[option_INJ; ALL2; UNWIND_THM1]);;

(* HOL4 line 117 *)
let IMP_v_rel_to_list = prove
 (`!xs ys. ALL2 flat_to_closProof_v_rel xs ys
           ==> flat_to_closProof_v_rel (flat_list_to_v xs) (clos_list_to_v ys)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:clos_v list` list_CASES) THEN
  REWRITE_TAC[ALL2; flat_list_to_v_def; clos_list_to_v_def] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN
  ASM_SIMP_TAC[flat_to_closProof_v_rel_def; ALL2; injectivity "option"; PAIR_EQ;
               injectivity "clos_v"; distinctness "option"] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN SIMP[ALL2]);;

(* the store entry i of a state_rel pair (HOL4: gvs [state_rel_def,          *)
(* store_rel_def,store_lookup_def] then the store_rel conjunct at i)      *)
let F2CPAUX_LOOKUP_TAC : tactic =
  REWRITE_TAC[flat_to_closProof_state_rel_def; store_rel_def; store_lookup_def] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_CASE_EQ; distinctness "option";
                              injectivity "option"]) THEN
  ASM_REWRITE_TAC[GSYM NOT_LT] THEN CASE_REWRITE_TAC[] THEN MESON_TAC[];;

(* HOL4 line 126 *)
let lookup_refv = prove
 (`!s1 t1 i v.
     flat_to_closProof_state_rel (s1:(C,FFI)flat_state) (t1:(C,FFI)clos_state) /\
     store_lookup i (flat_state_refs s1) = SOME (Refv v)
     ==> ?w. FLOOKUP (clos_state_refs t1) i = SOME (clos_ValueArray [w]) /\
             flat_to_closProof_v_rel v w`,
  F2CPAUX_LOOKUP_TAC);;

(* HOL4 line 135 *)
let lookup_byte_array = prove
 (`!s1 t1 i bytes.
     flat_to_closProof_state_rel (s1:(C,FFI)flat_state) (t1:(C,FFI)clos_state) /\
     store_lookup i (flat_state_refs s1) = SOME (W8array bytes)
     ==> FLOOKUP (clos_state_refs t1) i = SOME (clos_ByteArray bytes)`,
  F2CPAUX_LOOKUP_TAC);;

(* HOL4 line 144 *)
let lookup_array = prove
 (`!s1 t1 i vs.
     flat_to_closProof_state_rel (s1:(C,FFI)flat_state) (t1:(C,FFI)clos_state) /\
     store_lookup i (flat_state_refs s1) = SOME (Varray vs)
     ==> ?ws. FLOOKUP (clos_state_refs t1) i = SOME (clos_ValueArray ws) /\
              ALL2 flat_to_closProof_v_rel vs ws`,
  F2CPAUX_LOOKUP_TAC);;

(* HOL4 line 153 *)
let lookup_thunk = prove
 (`!s1 t1 i m v.
     flat_to_closProof_state_rel (s1:(C,FFI)flat_state) (t1:(C,FFI)clos_state) /\
     store_lookup i (flat_state_refs s1) = SOME (Thunk m v)
     ==> ?w. FLOOKUP (clos_state_refs t1) i = SOME (clos_Thunk m w) /\
             flat_to_closProof_v_rel v w`,
  F2CPAUX_LOOKUP_TAC);;

(* HOL4 line 162 *)
let env_rel_CONS_upd = prove
 (`!env f m db v1 v2 n.
     flat_to_closProof_env_rel (flat_environment_v_fupd f env) m db /\
     flat_to_closProof_v_rel v1 v2
     ==> flat_to_closProof_env_rel
           (flat_environment_v_fupd (\xs. CONS (n,v1) (f xs)) env)
           (CONS (SOME n) m) (CONS v2 db)`,
  REWRITE_TAC[flat_to_closProof_env_rel_def; flat_environment_INFO.ri_accfupds] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `k:mlstring` THEN X_GEN_TAC `x:flat_v` THEN
  REWRITE_TAC[ALOOKUP_THM; findi_def; injectivity "option"] THEN
  ASM_CASES_TAC `k:mlstring = n` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[injectivity "option"] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[EL; HD; LENGTH; LT_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(n:mlstring = k)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:mlstring`; `x:flat_v`]) THEN
  ASM_REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] (GSYM ADD1); EL; TL; LENGTH; LT_SUC]);;

(* HOL4 line 170 *)
let env_rel_CONS = prove
 (`!env xs m db v1 v2 n.
     flat_to_closProof_env_rel (flat_environment_v_fupd (K xs) env) m db /\
     flat_to_closProof_v_rel v1 v2
     ==> flat_to_closProof_env_rel
           (flat_environment_v_fupd (K (CONS (n,v1) xs)) env)
           (CONS (SOME n) m) (CONS v2 db)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`env:(flat_v)flat_environment`;
                 `(K (xs:(mlstring#flat_v)list)):(mlstring#flat_v)list->(mlstring#flat_v)list`;
                 `m:(mlstring option)list`; `db:clos_v list`; `v1:flat_v`;
                 `v2:clos_v`; `n:mlstring`] env_rel_CONS_upd) THEN
  ASM_REWRITE_TAC[K_THM] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; K_THM]);;

(* HOL4 line 177 (env1 is free in HOL4: its v field is replaced) *)
let flat_to_closProof_env_rel_APPEND = prove
 (`!name_prefix prefix db_prefix env m db env1.
     flat_to_closProof_env_rel env m db /\
     ALL2 flat_to_closProof_v_rel (MAP SND prefix) db_prefix /\
     name_prefix = MAP (SOME o FST) prefix
     ==> flat_to_closProof_env_rel
           (flat_environment_v_fupd (K (APPEND prefix (flat_environment_v env)))
              (env1:(flat_v)flat_environment))
           (APPEND name_prefix m) (APPEND db_prefix db)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `prefix:(mlstring#flat_v)list` list_CASES) THEN
  GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `db_prefix:clos_v list` list_CASES) THEN
  REWRITE_TAC[MAP; NOT_CONS_NIL; ALL2; APPEND; CONS_11; o_THM] THENL
   [REWRITE_TAC[flat_to_closProof_env_rel_def; flat_environment_INFO.ri_accfupds;
                K_THM];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`env1:(flat_v)flat_environment`;
                 `APPEND (t':(mlstring#flat_v)list) (flat_environment_v env)`;
                 `APPEND (MAP (SOME o FST) (t':(mlstring#flat_v)list)) m`;
                 `APPEND (t'':clos_v list) db`; `SND (h':mlstring#flat_v)`;
                 `h'':clos_v`; `FST (h':mlstring#flat_v)`] env_rel_CONS) THEN
  REWRITE_TAC[PAIR] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 193 *)
let initial_state'_def = cake_def
  `initial_state' b (ffi:(FFI)ffi_state) ma code (co:num -> C # clos_prog) cc k =
     clos_state_REC
       [SOME (if b then clos_Closure NONE [] [] 1 clos_interpreter else clos_Unit)]
       FEMPTY ffi k cc co code ma`;;

(* HOL4 line 203 *)
let initate_state'_clock = prove
 (`!b ffi max_app co cc k' k.
     clos_state_clock_fupd (K k)
       (initial_state' b (ffi:(FFI)ffi_state) max_app FEMPTY
          (co:num -> C # clos_prog) cc k') =
     initial_state' b ffi max_app FEMPTY co cc k /\
     clos_state_clock (initial_state' b ffi max_app FEMPTY co cc k) = k`,
  REWRITE_TAC[initial_state'_def; clos_state_INFO.ri_fupds;
              clos_state_INFO.ri_accessors; K_THM]);;
let _ = cake_add_simps [initate_state'_clock];;

(* HOL4 line 211 *)
let flat_to_closProof_state_rel_initial_state = prove
 (`!max_app ec co cc ffi k b.
     0 < max_app /\ install_config_rel' (ec:(C)install_config) co cc
     ==> flat_to_closProof_state_rel (flat_initial_state (ffi:(FFI)ffi_state) k ec)
           (initial_state' b ffi max_app FEMPTY co cc k)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[flat_to_closProof_state_rel_def; flat_initial_state_def;
                  initial_state'_def; store_rel_def; flat_state_INFO.ri_accessors;
                  clos_state_INFO.ri_accessors; LENGTH; LE_0; FLOOKUP_EMPTY; TL;
                  ALL2; NOT_SUC] THEN
  ASM_ARITH_TAC);;

(* HOL4 line 219 *)
let flat_to_closProof_state_rel_IMP_clock = prove
 (`!s t. flat_to_closProof_state_rel (s:(C,FFI)flat_state) (t:(C,FFI)clos_state)
         ==> flat_state_clock s = clos_state_clock t`,
  SIMP_TAC[flat_to_closProof_state_rel_def]);;

(* HOL4 line 225 *)
let flat_to_closProof_state_rel_dec_clock = prove
 (`!s t. flat_to_closProof_state_rel (s:(C,FFI)flat_state) (t:(C,FFI)clos_state)
         ==> flat_state_clock s = clos_state_clock t /\
             flat_to_closProof_state_rel (flat_dec_clock s) (clos_dec_clock 1 t)`,
  REWRITE_TAC[flat_to_closProof_state_rel_def; flat_dec_clock_def; clos_dec_clock_def;
              flat_state_INFO.ri_accfupds; clos_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[]);;

(* HOL4 lines 232-252: ML values s, t, exps_goal and dec_goal (terms of the *)
(* induction in compile_correct's proof)                                     *)

(* HOL4 line 254 *)
let flat_to_closProof_evaluate_decs_sing = prove
 (`!s d. flat_evaluate_decs (s:(C,FFI)flat_state) [d] = evaluate_dec s d`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [flat_evaluate_def] THEN
  MP_TAC(ISPEC `evaluate_dec (s:(C,FFI)flat_state) d` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(C,FFI)flat_state`
    (X_CHOOSE_THEN `r:((flat_v)error_result)option` SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE] THEN CASES_ON `r:((flat_v)error_result)option` THEN
  REWRITE_TAC[option_CASE; flat_evaluate_def]);;

(* HOL4 line 261: Theorem compile_correct, stated at its Finalise (HOL4    *)
(* line 1995) below, after the lemmas proved between its Resume blocks      *)

(* HOL4 line 340 *)
let dest_pat_from_case = prove
 (CASE_TERM
  `!pes. (match (pes:(flat_pat # flat_exp)list) with
            [(flat_Pvar _, _)] -> T
          | _ -> F)
         ==> ?nm rhs. dest_pat pes = SOME (nm,rhs)`,
  REWRITE_TAC[dest_pat_thm] THEN GEN_TAC THEN
  REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[]) THEN MESON_TAC[]);;

(* HOL4 line 394 *)
let LIST_REL_MAP_GENLIST = prove
 (`!funs (f1:A->B) (f2:num->C) R.
     (!n. n < LENGTH funs ==> R (f1 (EL n funs)) (f2 n))
     ==> ALL2 R (MAP f1 funs) (list_of_seq f2 (LENGTH funs))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_REL_EL_EQN; LENGTH_MAP; LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[EL_MAP; EL_LIST_OF_SEQ]);;

(* HOL4 line 437 *)
let dest_Constant_IMP = prove
 (`!x c.
     flat_to_clos_dest_Constant x = SOME c <=>
     (?t. x = clos_Op t (BlockOp (Constant c)) []) \/
     (?t i. x = clos_Op t (IntOp (clos_Const i)) [] /\ c = ConstInt i) \/
     (?t n. x = clos_Op t (BlockOp (clos_Cons n)) [] /\ c = ConstCons n [])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_to_clos_dest_Constant_pmatch] THEN
  REPEAT (TOP_CASE_TAC THEN
          ASM_REWRITE_TAC[distinctness "option"; injectivity "option";
                          distinctness "clos_exp"; injectivity "clos_exp";
                          distinctness "clos_op"; injectivity "clos_op";
                          distinctness "block_op"; injectivity "block_op";
                          distinctness "int_op"; injectivity "int_op";
                          NOT_CONS_NIL; UNWIND_THM1; EXISTS_REFL]) THEN
  MESON_TAC[]);;

(* HOL4 line 450 *)
let dest_Constants_IMP = prove
 (`!xs ys. dest_Constants xs = SOME ys
           ==> ALL2 (\x y. flat_to_clos_dest_Constant x = SOME y) xs ys`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN REWRITE_TAC[dest_Constants_def] THEN
  REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[distinctness "option"]) THEN
  REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ALL2] THEN ASM_SIMP_TAC[]);;

(* HOL4 line 459 *)
let dest_Constant_evaluate = prove
 (`!x c db s.
     flat_to_clos_dest_Constant x = SOME c
     ==> clos_evaluate ([x],db,(s:(C,FFI)clos_state)) = (Rval [make_const c],s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dest_Constant_IMP] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[clos_evaluate_def] THEN CASE_REWRITE_TAC[distinctness "clos_op"] THEN
  REWRITE_TAC[REVERSE; clos_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_do_int_app_def; make_const_def; MAP] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 467 *)
let dest_Constants_evaluate = prove
 (`!xs x db s.
     dest_Constants xs = SOME x
     ==> clos_evaluate (xs,db,(s:(C,FFI)clos_state)) = (Rval (MAP make_const x),s)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[dest_Constants_def] THENL
   [REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[clos_evaluate_def; MAP];
    ALL_TAC] THEN
  STRIP_TAC THEN FS[option_case_eq; distinctness "option"; injectivity "option"] THEN
  RVEQ_TAC THEN ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN
  RES_TAC THEN IMP_RES_TAC dest_Constant_evaluate THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD; MAP]);;

(* HOL4 line 478 *)
let evaluate_SmartCons = prove
 (`!t tag xs db s.
     clos_evaluate ([SmartCons t tag xs],db,(s:(C,FFI)clos_state)) =
     clos_evaluate ([clos_Op t (BlockOp (clos_Cons tag)) xs],db,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SmartCons_def] THEN
  COND_CASES_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[NULL_EQ]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP dest_Constants_evaluate) THEN
  ASM_REWRITE_TAC[clos_evaluate_def] THEN CASE_REWRITE_TAC[distinctness "clos_op"] THEN
  REWRITE_TAC[REVERSE; clos_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[make_const_def; MAP_REVERSE]);;

(* HOL4 line 519 *)
let find_recfun_EL = prove
 (`!l0 n. n < LENGTH l0 /\ ALL_DISTINCT (MAP FST l0)
          ==> find_recfun (FST (EL n l0)) (l0:(mlstring#A#B)list) =
              SOME (SND (EL n l0))`,
  REWRITE_TAC[find_recfun_ALOOKUP] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[PAIR] THEN
  ASM_SIMP_TAC[MEM_EL]);;

(* HOL4 line 530 *)
let IMP_PAIR = prove
 (`!z (x:A) (y:B). z = (x,y) ==> x = FST z /\ y = SND z`,
  SIMP_TAC[FST; SND]);;

(* HOL4 line 560 *)
let state_rel_LEAST = prove
 (`!s1 t1.
     flat_to_closProof_state_rel (s1:(C,FFI)flat_state) (t1:(C,FFI)clos_state)
     ==> (minimal ptr. ~(ptr IN FDOM (clos_state_refs t1))) =
         LENGTH (flat_state_refs s1)`,
  REWRITE_TAC[flat_to_closProof_state_rel_def; store_rel_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN FDOM (clos_state_refs (t1:(C,FFI)clos_state)) <=>
                    i < LENGTH (flat_state_refs (s1:(C,FFI)flat_state))`
    (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `i:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    REWRITE_TAC[FLOOKUP_DEF; GSYM NOT_LT] THEN
    ASM_CASES_TAC `i < LENGTH (flat_state_refs (s1:(C,FFI)flat_state))` THEN
    ASM_REWRITE_TAC[distinctness "option"] THEN
    REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[]) THEN MESON_TAC[distinctness "option"];
    ALL_TAC] THEN
  MATCH_MP_TAC MINIMAL_UNIQUE THEN ARITH_TAC);;

(* HOL4 line 581 *)
let evaluate_Let_error = prove
 (`!es env s err s' t e.
     clos_evaluate (es,env,(s:(C,FFI)clos_state)) = (Rerr err,s')
     ==> clos_evaluate ([clos_Let t es e],env,s) = (Rerr err,s')`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[clos_evaluate_def] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 588 *)
let evaluate_Op_error = prove
 (`!es env s err s' t op.
     clos_evaluate (es,env,(s:(C,FFI)clos_state)) = (Rerr err,s')
     ==> clos_evaluate ([clos_Op t op es],env,s) = (Rerr err,s')`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[clos_evaluate_def] THEN CASE_REWRITE_TAC[]);;

(* helpers for compile_op_evaluates_args: the argument errors propagate     *)
(* through each shape of compiled op                                         *)
let F2CPAUX_OP_LET_ERR_TAC : tactic =
  FIRST [MATCH_MP_TAC evaluate_Op_error THEN FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC evaluate_Let_error THEN FIRST_ASSUM ACCEPT_TAC];;

let F2CPAUX_compile_arith_error = prove
 (`!xs db t err t1 tt a ty.
     clos_evaluate (xs,db,(t:(C,FFI)clos_state)) = (Rerr err,t1)
     ==> clos_evaluate ([compile_arith tt a ty xs],db,t) = (Rerr err,t1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[compile_arith_def] THEN
  REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[]) THEN F2CPAUX_OP_LET_ERR_TAC);;

let F2CPAUX_arg1_id_error = prove
 (`!xs db t err t1.
     clos_evaluate (xs,db,(t:(C,FFI)clos_state)) = (Rerr err,t1)
     ==> clos_evaluate ([flat_to_clos_arg1 xs (\x. x)],db,t) = (Rerr err,t1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[flat_to_clos_arg1_def] THEN
  REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[]) THEN
  TRY F2CPAUX_OP_LET_ERR_TAC THEN FIRST_X_ASSUM ACCEPT_TAC);;

let F2CPAUX_arg1_op_error = prove
 (`!xs db t err t1 tt op t2 i.
     clos_evaluate (xs,db,(t:(C,FFI)clos_state)) = (Rerr err,t1)
     ==> clos_evaluate ([flat_to_clos_arg1 xs
                           (\x. clos_Op tt op [clos_Op t2 (IntOp (clos_Const i)) []; x])],
                        db,t) = (Rerr err,t1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[flat_to_clos_arg1_def] THEN
  REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[]) THEN
  TRY F2CPAUX_OP_LET_ERR_TAC THEN
  MATCH_MP_TAC evaluate_Op_error THEN
  ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN
  REWRITE_TAC[clos_evaluate_def] THEN CASE_REWRITE_TAC[distinctness "clos_op"] THEN
  REWRITE_TAC[REVERSE; clos_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_do_int_app_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let F2CPAUX_evaluate_const_cons = prove
 (CASE_TERM
  `!t2 i ys db s.
     clos_evaluate (CONS (clos_Op t2 (IntOp (clos_Const i)) []) ys,db,
                    (s:(C,FFI)clos_state)) =
     match clos_evaluate (ys,db,s) with
       (Rval vs,s1) -> (Rval (CONS (clos_Number i) vs),s1)
     | res -> res`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN
  REWRITE_TAC[clos_evaluate_def] THEN CASE_REWRITE_TAC[distinctness "clos_op"] THEN
  REWRITE_TAC[REVERSE; clos_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_do_int_app_def] THEN CASE_REWRITE_TAC[HD]);;

let F2CPAUX_arg2_op_error = prove
 (`!xs db t err t1 tt op t2 i.
     clos_evaluate (xs,db,(t:(C,FFI)clos_state)) = (Rerr err,t1)
     ==> clos_evaluate ([flat_to_clos_arg2 xs
                           (\x y. clos_Op tt op
                                    [x; clos_Op t2 (IntOp (clos_Const i)) []; y])],
                        db,t) = (Rerr err,t1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_to_clos_arg2_def] THEN
  REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[]) THEN
  TRY (DISCH_TAC THEN F2CPAUX_OP_LET_ERR_TAC THEN NO_TAC) THEN
  DISCH_TAC THEN MATCH_MP_TAC evaluate_Op_error THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN
  REWRITE_TAC[F2CPAUX_evaluate_const_cons] THEN
  EVERY_CASE_TAC THEN FS[]);;

(* HOL4 line 595 *)
let compile_op_evaluates_args = prove
 (`!xs db t err t1 op tra.
     clos_evaluate (xs,db,(t:(C,FFI)clos_state)) = (Rerr err,t1) /\
     ~(op = Src Opapp) /\ ~(op = Src Eval) /\ ~(op = Src (ThunkOp ForceThunk))
     ==> clos_evaluate ([flat_to_clos_compile_op tra op xs],db,t) = (Rerr err,t1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CASES_ON `op:flat_op` THENL
   [CASES_ON `a:op`; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "flat_op"; distinctness "op";
                              injectivity "op"; injectivity "thunk_op"]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[flat_to_clos_compile_op_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "flat_op"; distinctness "op";
                              injectivity "op"; injectivity "thunk_op"]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  FIRST [F2CPAUX_OP_LET_ERR_TAC;
         MATCH_MP_TAC F2CPAUX_compile_arith_error THEN FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC F2CPAUX_arg1_id_error THEN FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC F2CPAUX_arg1_op_error THEN FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC F2CPAUX_arg2_op_error THEN FIRST_ASSUM ACCEPT_TAC]);;

(* HOL4 line 621 *)
let flat_to_closProof_v_rel_Boolv = prove
 (`!b v. flat_to_closProof_v_rel (flat_Boolv b) v <=> v = clos_Boolv b`,
  REWRITE_TAC[flat_Boolv_def; clos_Boolv_def; flat_to_closProof_v_rel_def;
              distinctness "option"; injectivity "option"; PAIR_EQ; LIST_REL_NIL] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [flat_to_closProof_v_rel_Boolv];;

(* HOL4 line 628 *)
let v_rel_Unitv = prove
 (`!v. flat_to_closProof_v_rel Unitv v <=> v = clos_Block 0 []`,
  REWRITE_TAC[flat_Unitv_def; flat_to_closProof_v_rel_def;
              distinctness "option"; injectivity "option"; LIST_REL_NIL] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [v_rel_Unitv];;

(* HOL4 line 634: the ML value op_goal, the conclusion of the op_ theorems *)
(* below (written out in each; its free variables are quantified there):    *)
(*   flat_do_app s1 op vs = SOME (s2,res2) /\                                *)
(*   flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\                *)
(*   clos_evaluate (xs,db,t) = (Rval ws,t1) /\                               *)
(*   ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\                         *)
(*   LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\                           *)
(*   ~(op = Src (ThunkOp ForceThunk))                                        *)
(*   ==> ?res2' t1. clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t)  *)
(*                  = (res2',t1) /\ flat_to_closProof_state_rel s2 t1 /\     *)
(*                  result_rel (ALL2 flat_to_closProof_v_rel)                *)
(*                    flat_to_closProof_v_rel (list_result res2) res2'       *)

(* ------------------------------------------------------------------------- *)
(* Infrastructure for the op_ theorems (local helpers).                      *)
(* ------------------------------------------------------------------------- *)

(* helpers for the op_ theorems: evaluation of a compiled Op or Let whose  *)
(* arguments evaluate to values, and state_rel after a store update        *)
let F2CPAUX_evaluate_Op = prove
 (CASE_TERM
  `!xs db t ws t1.
     clos_evaluate (xs,db,(t:(C,FFI)clos_state)) = (Rval ws,t1)
     ==> !tt op. ~(op = clos_Install) /\ ~(op = clos_ThunkOp ForceThunk)
     ==> clos_evaluate ([clos_Op tt op xs],db,t) =
         (match clos_do_app op (REVERSE ws) t1 with
            Rerr err -> (Rerr err,t1)
          | Rval (v,s) -> (Rval [v],s))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[clos_evaluate_def] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let F2CPAUX_evaluate_Let = prove
 (`!xs db t ws t1.
     clos_evaluate (xs,db,(t:(C,FFI)clos_state)) = (Rval ws,t1)
     ==> !tt e. clos_evaluate ([clos_Let tt xs e],db,t) = clos_evaluate ([e],APPEND ws db,t1)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[clos_evaluate_def] THEN CASE_REWRITE_TAC[]);;

let F2CPAUX_state_rel_refs = prove
 (`!s t refs trefs.
     flat_to_closProof_state_rel (s:(C,FFI)flat_state) (t:(C,FFI)clos_state) /\
     store_rel refs trefs
     ==> flat_to_closProof_state_rel (flat_state_refs_fupd (K refs) s)
           (clos_state_refs_fupd (K trefs) t)`,
  SIMP_TAC[flat_to_closProof_state_rel_def; flat_state_INFO.ri_accfupds;
           clos_state_INFO.ri_accfupds; K_THM]);;

let F2CPAUX_store_rel_APPEND = prove
 (CASE_TERM
  `!refs trefs sv cv.
     store_rel refs trefs /\
     (match sv with
        Refv v -> (?x. cv = clos_ValueArray [x] /\ flat_to_closProof_v_rel v x)
      | Thunk m v -> (?x. cv = clos_Thunk m x /\ flat_to_closProof_v_rel v x)
      | Varray vs -> (?xs. cv = clos_ValueArray xs /\
                           ALL2 flat_to_closProof_v_rel vs xs)
      | W8array bs -> cv = clos_ByteArray bs)
     ==> store_rel (APPEND refs [sv]) (trefs |+ (LENGTH refs,cv))`,
  REWRITE_TAC[store_rel_def] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; FLOOKUP_UPDATE; EL_APPEND] THEN
  ASM_CASES_TAC `i = LENGTH (refs:(flat_v store_v)list)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[ARITH_RULE `~(n + SUC 0 <= n)`; LT_REFL; SUB_REFL; EL; HD] THEN
    POP_ASSUM MP_TAC THEN CASES_ON `sv:(flat_v)store_v` THEN CASE_REWRITE_TAC[] THEN
    SIMP_TAC[injectivity "option"];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  SUBGOAL_THEN `~(LENGTH (refs:(flat_v store_v)list) = i)` (fun th -> REWRITE_TAC[th])
  THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH (refs:(flat_v store_v)list) + SUC 0 <= i` THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `LENGTH (refs:(flat_v store_v)list) <= i` (fun th -> REWRITE_TAC[th])
    THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i < LENGTH (refs:(flat_v store_v)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM NOT_LT]);;

let F2CPAUX_store_rel_LUPDATE = prove
 (CASE_TERM
  `!refs trefs i sv cv.
     store_rel refs trefs /\ i < LENGTH refs /\
     (match sv with
        Refv v -> (?x. cv = clos_ValueArray [x] /\ flat_to_closProof_v_rel v x)
      | Thunk m v -> (?x. cv = clos_Thunk m x /\ flat_to_closProof_v_rel v x)
      | Varray vs -> (?xs. cv = clos_ValueArray xs /\
                           ALL2 flat_to_closProof_v_rel vs xs)
      | W8array bs -> cv = clos_ByteArray bs)
     ==> store_rel (LUPDATE sv i refs) (trefs |+ (i,cv))`,
  REWRITE_TAC[store_rel_def] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_LUPDATE; FLOOKUP_UPDATE; EL_LUPDATE] THEN
  ASM_CASES_TAC `i' = i:num` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
    POP_ASSUM MP_TAC THEN CASES_ON `sv:(flat_v)store_v` THEN CASE_REWRITE_TAC[] THEN
    SIMP_TAC[injectivity "option"];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i':num`) THEN
  SUBGOAL_THEN `~(i:num = i')` (fun th -> ASM_REWRITE_TAC[th]) THEN ASM_MESON_TAC[]);;

let F2CPAUX_state_rel_store = prove
 (CASE_TERM
  `!s t i.
     flat_to_closProof_state_rel (s:(C,FFI)flat_state) (t:(C,FFI)clos_state) /\
     i < LENGTH (flat_state_refs s)
     ==> (match EL i (flat_state_refs s) with
            Refv v -> (?x. FLOOKUP (clos_state_refs t) i = SOME (clos_ValueArray [x]) /\
                           flat_to_closProof_v_rel v x)
          | Thunk m v -> (?x. FLOOKUP (clos_state_refs t) i = SOME (clos_Thunk m x) /\
                              flat_to_closProof_v_rel v x)
          | Varray vs -> (?xs. FLOOKUP (clos_state_refs t) i = SOME (clos_ValueArray xs) /\
                               ALL2 flat_to_closProof_v_rel vs xs)
          | W8array bs -> FLOOKUP (clos_state_refs t) i = SOME (clos_ByteArray bs))`,
  REWRITE_TAC[flat_to_closProof_state_rel_def; store_rel_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[GSYM NOT_LT]);;

let F2CPAUX_evaluate_CONS_Rval = prove
 (`!x y ys env s vs s'.
     clos_evaluate (CONS x (CONS y ys),env,(s:(C,FFI)clos_state)) = (Rval vs,s')
     ==> ?v1 s1 vs2. clos_evaluate ([x],env,s) = (Rval [v1],s1) /\
                     clos_evaluate (CONS y ys,env,s1) = (Rval vs2,s') /\
                     vs = CONS v1 vs2`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [clos_evaluate_CONS] THEN
  MP_TAC(ISPEC `clos_evaluate ([x],env,(s:(C,FFI)clos_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s1:(C,FFI)clos_state` (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th] THEN
                ASSUME_TAC th))) THEN
  REWRITE_TAC[pair_CASE] THEN CASES_ON `r1:(clos_v list,clos_v)result` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN
  MP_TAC(ISPEC `clos_evaluate (CONS y ys,env,(s1:(C,FFI)clos_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s2:(C,FFI)clos_state` (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th] THEN
                ASSUME_TAC th))) THEN
  CASES_ON `r2:(clos_v list,clos_v)result` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; distinctness "result"; injectivity "result"] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP clos_evaluate_SING) THEN
  MAP_EVERY EXISTS_TAC [`r1':clos_v`; `s1:(C,FFI)clos_state`; `a':clos_v list`] THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[HD]);;

(* small facts about the byte values of characters *)
let F2CPAUX_val_byte_lt = prove
 (`!w:byte. val w < 256`,
  GEN_TAC THEN MP_TAC(ISPEC `w:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV);;

let F2CPAUX_val_word_ORD = prove
 (`!c. val ((word:num->byte) (ORD c)) = ORD c`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT; ORD_BOUND]);;

let F2CPAUX_MAP_CHR_val_word_ORD = prove
 (`!l. MAP (CHR o val) (MAP ((word:num->byte) o ORD) l) = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; o_THM; F2CPAUX_val_word_ORD; CHR_ORD]);;

let F2CPAUX_word_ORD_11 = prove
 (`!a b. (word (ORD a):byte) = word (ORD b) <=> a = b`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT; ORD_BOUND; ORD_11]);;

(* HOL4's MAP_n2w_o_ORD_11 (proved again below at its place) *)
let F2CPAUX_MAP_word_ORD_11 = prove
 (`!l1 l2. MAP ((word:num->byte) o ORD) l1 = MAP (word o ORD) l2 <=> l1 = l2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11; o_THM; F2CPAUX_word_ORD_11]);;

let F2CPAUX_abs_pos = prove
 (`!x:int. ~(x < &0) ==> abs x = x`,
  INT_ARITH_TAC);;

(* HOL4: Num (ABS k) < LENGTH ws <=> k < &LENGTH ws by intLib.COOPER_TAC *)
let F2CPAUX_num_of_int_cmp = prove
 (`!i n. ~(i < &0)
         ==> (num_of_int i < n <=> i < &n) /\
             (num_of_int i >= n <=> ~(i < &n)) /\
             (n <= num_of_int i <=> ~(i < &n))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?m. (i:int) = &m` (CHOOSE_THEN SUBST1_TAC) THENL
   [EXISTS_TAC `num_of_int (i:int)` THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM; INT_OF_NUM_LT] THEN ARITH_TAC);;

let F2CPAUX_ALL2_EL = prove
 (`!R (l1:A list) (l2:B list) n. ALL2 R l1 l2 /\ n < LENGTH l1 ==> R (EL n l1) (EL n l2)`,
  SIMP_TAC[LIST_REL_EL_EQN]);;

(* stripping an assumption with fresh names: as the kit's CAKE_STRIP_ASSUME_TAC *)
(* but the names also avoid the variables of the hypotheses of the assumption  *)
(* theorems (after SUBST_ALL_TAC an assumption's hypotheses can mention a      *)
(* substituted variable, and reusing its name makes the justification fail     *)
(* with CHOOSE)                                                                 *)
let F2CPAUX_all_frees (asl,w) th =
  freesl (w :: concl th :: hyp th @
          flat (map (fun (_,t) -> concl t :: hyp t) asl));;

let rec F2CPAUX_STRIP_AV (av:term list) th : tactic =
  fun (asl,w as gl) ->
    let c = concl th in
    if c = `T` then ALL_TAC gl
    else if c = `F` then CONTR_TAC th gl
    else if is_conj c then
      let c1,c2 = dest_conj c in
      CONJUNCTS_THEN2 (F2CPAUX_STRIP_AV (union av (frees c2)))
                      (F2CPAUX_STRIP_AV av) th gl
    else if is_disj c then
      DISJ_CASES_THEN (F2CPAUX_STRIP_AV av) th gl
    else if is_exists c then
      let v,_ = dest_exists c in
      let v' = variant (union av (F2CPAUX_all_frees gl th)) v in
      X_CHOOSE_THEN v' (F2CPAUX_STRIP_AV (v'::av)) th gl
    else ASSUME_TAC th gl;;

let F2CPAUX_STRIP_ASSUME_TAC th = F2CPAUX_STRIP_AV [] th;;

(* the setup of the op_ theorems: the case split of the do_app equation and  *)
(* the shapes of the argument values (HOL4: fs [do_app_def,list_case_eq,     *)
(* CaseEq ...] \\ rw [] \\ fs [LENGTH_EQ_NUM_compute] ... fs [v_rel_def])    *)
let F2CPAUX_is_do_app_eq th =
  let c = concl th in
  is_eq c && (try fst(dest_const(fst(strip_comb(lhs c)))) = "flat_do_app"
              with Failure _ -> false);;

let F2CPAUX_OP_SPLIT_TAC : tactic =
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check F2CPAUX_is_do_app_eq) THEN
  REWRITE_TAC[flat_do_app_def] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  FLATSEMAUX_SPLIT_TAC THEN
  GVS[LIST_REL_CONS1; LIST_REL_NIL; SWAP_REVERSE_SYM; REVERSE; APPEND;
      store_alloc_def; flat_to_closProof_v_rel_def];;

(* the shape of the argument list xs from its LENGTH, and the evaluations of *)
(* its elements (HOL4: imp_res_tac evaluate_SING, fs [pair_case_eq,         *)
(* result_case_eq])                                                          *)
let F2CPAUX_SING_TAC : tactic =
  let ok th =
    try let l,r = dest_eq (concl th) in
        let f,args = strip_comb l in
        fst(dest_const f) = "clos_evaluate" &&
        length (dest_list (fst(dest_pair (hd args)))) = 1 &&
        (let res = fst(dest_pair r) in
         fst(dest_const(rator res)) = "Rval" && is_var (rand res))
    with Failure _ -> false in
  REPEAT (FIRST_X_ASSUM (fun th (asl,w as g) ->
    if ok th then
      let th' = MATCH_MP clos_evaluate_SING th in
      let v,_ = dest_exists (concl th') in
      let v' = variant (F2CPAUX_all_frees g th) v in
      X_CHOOSE_THEN v' (fun eq -> SUBST_ALL_TAC eq THEN ASSUME_TAC (REWRITE_RULE[eq] th))
        th' g
    else failwith "F2CPAUX_SING_TAC"));;

let F2CPAUX_SPLIT_EVAL_RULE th =
  try let l = lhs(concl th) in
      let f,args = strip_comb l in
      if fst(dest_const f) = "clos_evaluate" &&
         length (dest_list (fst(dest_pair (hd args)))) >= 2
      then ONCE_REWRITE_RULE[clos_evaluate_CONS] th else th
  with Failure _ -> th;;

(* LENGTH xs = n (a numeral) into xs = [x1; ...; xn], with fresh names *)
let F2CPAUX_LEN_TAC : tactic =
  let ok th = try let l,r = dest_eq (concl th) in
                  fst(dest_const(rator l)) = "LENGTH" && is_var (rand l) && is_numeral r
              with Failure _ -> false in
  let step th (asl,w as g) =
    let l,r = dest_eq (concl th) in
    let xs = rand l in
    let avoid = F2CPAUX_all_frees g th in
    if dest_numeral r =/ num_0 then
      SUBST_ALL_TAC (REWRITE_RULE[LENGTH_EQ_NIL] th) g
    else
      let th1 = REWRITE_RULE[LENGTH_EQ_CONS] (CONV_RULE (RAND_CONV num_CONV) th) in
      let ety = hd(snd(dest_type(type_of xs))) in
      let h = variant avoid (mk_var("x",ety)) in
      let t = variant (h::avoid) (mk_var("xs",type_of xs)) in
      (X_CHOOSE_THEN h (X_CHOOSE_THEN t (fun th2 ->
         let th3,th4 = CONJ_PAIR th2 in
         SUBST_ALL_TAC th3 THEN ASSUME_TAC th4))) th1 g in
  REPEAT (FIRST_X_ASSUM (fun th -> if ok th then step th else failwith "LEN"));;

let F2CPAUX_ARGS_TAC : tactic =
  F2CPAUX_LEN_TAC THEN
  REPEAT (FIRST_X_ASSUM (fun th ->
            F2CPAUX_STRIP_ASSUME_TAC (MATCH_MP F2CPAUX_evaluate_CONS_Rval th)) THEN
          RULE_ASSUM_TAC (REWRITE_RULE[CONS_11]) THEN
          REPEAT (FIRST_X_ASSUM (F2CPAUX_STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
          RVEQ_TAC);;

(* HOL4: imp_res_tac LIST_REL_LENGTH \ fs [LIST_REL_EL] *)
let F2CPAUX_ALL2_EL_TAC : tactic =
  IMP_RES_TAC LIST_REL_LENGTH THEN MATCH_MP_TAC F2CPAUX_ALL2_EL THEN
  CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[F2CPAUX_num_of_int_cmp] THEN ASM_ARITH_TAC];;

(* clos_do_eq x y unfolded only when x and y are constructor applications *)
let F2CPAUX_CLOS_DO_EQ_CONV tm =
  let f,args = strip_comb tm in
  if is_const f && fst(dest_const f) = "clos_do_eq" && length args = 2 &&
     forall (fun a -> is_constructor_app a) args
  then (REWR_CONV (CONJUNCT1 clos_do_eq_def) THENC CASE_REWRITE_CONV []) tm
  else failwith "F2CPAUX_CLOS_DO_EQ_CONV";;

(* flat_do_eq unfolded only when both arguments are constructor applications *)
let F2CPAUX_FLAT_DO_EQ_CONV tm =
  let f,args = strip_comb tm in
  if is_const f && fst(dest_const f) = "flat_do_eq" && length args = 2 &&
     forall (fun a -> is_constructor_app a) args
  then (REWRITE_CONV[flat_do_eq_def] THENC CASE_REWRITE_CONV []) tm
  else failwith "F2CPAUX_FLAT_DO_EQ_CONV";;

(* small facts for the evaluation of compiled code *)
let F2CPAUX_iword_val = prove
 (`!w:N word. iword (&(val w)) = w`,
  REWRITE_TAC[GSYM WORD_IWORD; WORD_VAL]);;

let F2CPAUX_ex_val = prove
 (`!b:N word. ?w:N word. &(val b):int = &(val w)`,
  MESON_TAC[]);;

let F2CPAUX_some_val = prove
 (`!b:N word. (some w:N word. &(val b):int = &(val w)) = SOME b`,
  REWRITE_TAC[INT_OF_NUM_EQ; VAL_EQ; some_EQ]);;

(* EL k l for a numeral k and a list literal; k < n and k <= n for a numeral *)
(* k when decided by ARITH_RULE                                             *)
let F2CPAUX_EL_NUM_CONV tm =
  let f,args = strip_comb tm in
  if is_const f && fst(dest_const f) = "EL" && length args = 2 &&
     is_numeral (hd args) && is_cons (el 1 args)
  then (REWR_CONV EL_CONS THENC NUM_REDUCE_CONV THENC REWRITE_CONV[]) tm
  else failwith "F2CPAUX_EL_NUM_CONV";;

let F2CPAUX_ARITH_CONV =
  let lt = `(<):num->num->bool` and le = `(<=):num->num->bool` in
  fun tm ->
    if (is_binop lt tm || is_binop le tm) && is_numeral (lhand tm)
    then (try EQT_INTRO (ARITH_RULE tm) with Failure _ ->
          EQF_INTRO (ARITH_RULE (mk_neg tm)))
    else failwith "F2CPAUX_ARITH_CONV";;

(* ------------------------------------------------------------------------- *)
(* A lazy evaluator for compiled closLang code (the job of HOL4's fs         *)
(* [evaluate_def,do_app_def,...] in the op_ proofs): rewriting only in head  *)
(* positions, i.e. never inside a lambda, the arms of a case or the branches *)
(* of an undecided conditional, so that the code of the branches is not      *)
(* unfolded before the guard is decided.                                     *)
(* ------------------------------------------------------------------------- *)

(* the normaliser: children in head positions first, then a rewrite at the *)
(* node, whose result is normalised again; a conditional is reduced when its *)
(* guard normalises to T or F or is decided by the decision procedure dec    *)
let F2CPAUX_HEAD_NORM (conv:conv) (dec:conv) =
  let rec nav n c = if n = 0 then c else RATOR_CONV (nav (n-1) c) in
  let rec hc tm =
    let th1 =
      if is_cond tm then RATOR_CONV(RATOR_CONV(RAND_CONV hc)) tm
      else if is_case_app tm then
        let _,_,fs = dest_case_app tm in nav (length fs) (RAND_CONV hc) tm
      else if is_abs tm then REFL tm
      else if is_comb tm then COMB_CONV hc tm
      else REFL tm in
    let tm1 = rhs(concl th1) in
    let th2 = try Some (conv tm1) with Failure _ ->
              (if is_cond tm1 then
                 try Some (RATOR_CONV(RATOR_CONV(RAND_CONV dec)) tm1)
                 with Failure _ -> None
               else None) in
    match th2 with
      None -> th1
    | Some th2 ->
        if rhs(concl th2) = tm1 then th1 else
        TRANS th1 (TRANS th2 (hc (rhs(concl th2)))) in
  hc;;

(* decide an int or num comparison from the arithmetic assumptions *)
let F2CPAUX_is_arith_atom =
  let ops = [`(<):int->int->bool`; `(<=):int->int->bool`; `(>):int->int->bool`;
             `(>=):int->int->bool`; `(<):num->num->bool`; `(<=):num->num->bool`]
  and ity = `:int` and nty = `:num` in
  fun tm ->
    (exists (fun op -> is_binop op tm) ops) ||
    (is_eq tm && (type_of (lhand tm) = ity || type_of (lhand tm) = nty));;

let F2CPAUX_DECIDE_CONV =
  let nty = `:num` and ity = `:int` in
  fun (facts:thm list) tm ->
  if not (F2CPAUX_is_arith_atom tm) then failwith "decide" else
  let hyps = filter (fun th -> let c = concl th in
                       F2CPAUX_is_arith_atom c ||
                       (is_neg c && F2CPAUX_is_arith_atom (dest_neg c))) facts in
  let ante = if hyps = [] then `T` else list_mk_conj (map concl hyps) in
  let prove_it t =
    let th = if type_of (lhand tm) = nty &&
                not (can (find_term (fun s -> type_of s = ity)) ante)
             then ARITH_RULE (mk_imp(ante,t)) else INT_ARITH (mk_imp(ante,t)) in
    MP th (end_itlist CONJ (if hyps = [] then [TRUTH] else hyps)) in
  try EQT_INTRO (prove_it tm) with Failure _ ->
  EQF_INTRO (prove_it (mk_neg tm));;

let F2CPAUX_EVAL_THMS =
  CONJUNCTS clos_evaluate_def @ [clos_do_app_def] @
  CONJUNCTS clos_do_int_app_def @ CONJUNCTS clos_do_word_app_def @
  CONJUNCTS REVERSE @ CONJUNCTS APPEND @ CONJUNCTS LENGTH @ [HD; TL] @
  [clos_Boolv_11; F2CPAUX_iword_val; F2CPAUX_some_val;
   EQT_INTRO (SPEC_ALL F2CPAUX_ex_val); INT_POS; NUM_OF_INT_OF_NUM;
   EQT_INTRO (SPEC_ALL ORD_BOUND); EQT_INTRO (SPEC_ALL F2CPAUX_val_byte_lt);
   F2CPAUX_val_word_ORD; F2CPAUX_MAP_CHR_val_word_ORD; implode_explode;
   INT_OF_NUM_LT; INT_OF_NUM_LE; INT_OF_NUM_EQ; HD_compile; evaluate_SmartCons];;

let F2CPAUX_EVAL_CONV (asl:thm list) : conv * conv =
  let evs = filter (fun th -> let c = concl th in
                     is_eq c && not (is_var (lhs c)) &&
                     not (F2CPAUX_is_arith_atom c) &&
                     (let h = fst(strip_comb(lhs c)) in
                      is_const h && mem (fst(dest_const h))
                        ["clos_evaluate"; "FLOOKUP"; "EL"; "store_lookup";
                         "flat_v_to_list"; "clos_v_to_list"; "flat_v_to_char_list";
                         "flat_vs_to_string"; "do_shift"; "copy_array";
                         "call_FFI"; "clos_do_eq"; "flat_do_eq"])) asl in
  let atoms = mapfilter (fun th -> let c = concl th in
                if F2CPAUX_is_arith_atom c then EQT_INTRO th
                else if is_neg c && F2CPAUX_is_arith_atom (dest_neg c) then EQF_INTRO th
                else fail()) asl in
  let nonneg = flat (mapfilter (fun th ->
                 CONJUNCTS (SPEC_ALL (MATCH_MP F2CPAUX_num_of_int_cmp th)) @
                 [MATCH_MP F2CPAUX_abs_pos th]) asl) in
  let net = itlist (net_of_thm false)
              (itlist (mk_rewrites false)
                 (evs @ atoms @ nonneg @ F2CPAUX_EVAL_THMS) [])
              empty_net in
  let rw = REWRITES_CONV net in
  let top = GENERAL_REWRITE_CONV true I (!cake_case_net) [] in
  (rw ORELSEC top ORELSEC let_CONV ORELSEC BETA_CONV ORELSEC
   F2CPAUX_EL_NUM_CONV ORELSEC F2CPAUX_ARITH_CONV ORELSEC F2CPAUX_CLOS_DO_EQ_CONV),
  (fun tm -> let th = (DEPTH_CONV (F2CPAUX_DECIDE_CONV asl) THENC REWRITE_CONV[]) tm in
             let r = rhs(concl th) in
             if r = `T` || r = `F` then th else failwith "dec");;

let F2CPAUX_EVAL_TAC : tactic = fun (asl,w as g) ->
  let conv,dec = F2CPAUX_EVAL_CONV (map snd asl) in
  let norm = F2CPAUX_HEAD_NORM conv dec in
  CONV_TAC (ONCE_DEPTH_CONV (fun tm ->
    if (try fst(dest_const(fst(strip_comb tm))) = "clos_evaluate"
        with Failure _ -> false) || is_case_app tm || is_cond tm
    then CHANGED_CONV norm tm else failwith "F2CPAUX_EVAL_TAC")) g;;

(* the evaluation of the compiled op: compile_op, arg1/arg2, then the lazy  *)
(* evaluation of the closLang code                                          *)
let F2CPAUX_CLOS_EVAL_TAC : tactic =
  REWRITE_TAC[flat_to_clos_compile_op_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[flat_to_clos_arg1_def; flat_to_clos_arg2_def; compile_arith_def] THEN
  CASE_REWRITE_TAC[] THEN F2CPAUX_EVAL_TAC;;

let F2CPAUX_LEAST_TAC : tactic =
  TRY (FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP state_rel_LEAST th])) THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[];;

(* state_rel after a store update (HOL4: fs [state_rel_def,store_rel_def]   *)
(* \\ strip_tac \\ first_x_assum (qspec_then i mp_tac) ...)                  *)
let F2CPAUX_state_rel_store_rel = prove
 (`!s t. flat_to_closProof_state_rel (s:(C,FFI)flat_state) (t:(C,FFI)clos_state)
         ==> store_rel (flat_state_refs s) (clos_state_refs t)`,
  SIMP_TAC[flat_to_closProof_state_rel_def]);;

let F2CPAUX_STORE_TAC : tactic =
  MATCH_MP_TAC F2CPAUX_state_rel_refs THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  (MATCH_MP_TAC F2CPAUX_store_rel_APPEND ORELSE
   MATCH_MP_TAC F2CPAUX_store_rel_LUPDATE) THEN
  CASE_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST [MATCH_MP_TAC F2CPAUX_state_rel_store_rel THEN FIRST_ASSUM ACCEPT_TAC;
         FIRST_ASSUM ACCEPT_TAC;
         SIMP[injectivity "clos_ref"; LIST_REL_REPLICATE_same] THEN NO_TAC;
         SIMP[injectivity "clos_ref"; LIST_REL_REPLICATE_same] THEN
         MATCH_MP_TAC EVERY2_LUPDATE_same THEN ASM_REWRITE_TAC[];
         SIMP[injectivity "clos_ref"] THEN ASM_MESON_TAC[]];;

(* the store entries that do_app looked up or assigned (HOL4: fs [state_rel_def, *)
(* store_rel_def] \\ first_x_assum (qspec_then i mp_tac) \\ Cases_on EL i ...)   *)
let F2CPAUX_STORE_FACTS_TAC : tactic = fun (asl,w as g) ->
  let is_srel tm = try fst(dest_const(fst(strip_comb tm))) =
                         "flat_to_closProof_state_rel" with Failure _ -> false in
  let srels = filter (is_srel o concl o snd) asl in
  let lts = filter (fun (_,th) -> try let l,r = dest_binop `(<):num->num->bool` (concl th) in
                                       fst(dest_const(fst(strip_comb r))) = "LENGTH"
                                   with Failure _ -> false) asl in
  let facts = flat (map (fun (_,s) -> mapfilter (fun (_,l) ->
                MATCH_MP F2CPAUX_state_rel_store (CONJ s l)) lts) srels) in
  (MAP_EVERY (fun th -> MP_TAC th THEN
                ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
                DISCH_THEN F2CPAUX_STRIP_ASSUME_TAC) facts) g;;

let F2CPAUX_thunk_mode_CASE_same = prove
 (CASE_TERM `!m (x:A). (match m with Evaluated -> x | NotEvaluated -> x) = x`,
  GEN_TAC THEN CASES_ON `m:thunk_mode` THEN CASE_REWRITE_TAC[]);;

(* HOL4: Cases_on EL i s1.refs \\ fs [store_v_same_type_def] *)
let F2CPAUX_SAME_TYPE_TAC : tactic = fun (asl,w as g) ->
  let tms = mapfilter (fun (_,th) ->
      let f,args = strip_comb (concl th) in
      if fst(dest_const f) = "store_v_same_type" then hd args else fail()) asl in
  (MAP_EVERY (fun tm -> CASES_ON tm THEN
                        FS[store_v_same_type_def; F2CPAUX_thunk_mode_CASE_same]) tms) g;;

(* the closing steps, each tried only on goals of its shape *)
let F2CPAUX_goal_head (asl,w) =
  try fst(dest_const(fst(strip_comb w))) with Failure _ -> "";;

let F2CPAUX_CLOSE_TAC : tactic = fun (asl,w as g) ->
  let h = F2CPAUX_goal_head g in
  if h = "flat_to_closProof_state_rel" &&
     (try fst(dest_const(fst(strip_comb(rand w)))) = "clos_state_refs_fupd"
      with Failure _ -> false)
  then TRY (F2CPAUX_STORE_TAC THEN NO_TAC) g
  else if h = "flat_to_closProof_v_rel" &&
          (try fst(dest_const(fst(strip_comb(rand w)))) = "EL" with Failure _ -> false)
  then TRY (F2CPAUX_ALL2_EL_TAC THEN NO_TAC) g
  else ALL_TAC g;;

(* the whole generic part of an op_ proof *)
let F2CPAUX_OP_BODY_GEN_TAC (extra:tactic) : tactic =
  F2CPAUX_OP_SPLIT_TAC THEN extra THEN
  GVS[store_lookup_def; store_assign_def; COND_CASE_EQ; F2CPAUX_abs_pos;
      F2CPAUX_num_of_int_cmp; subscript_exn_v_def; flat_div_exn_v_def;
      flat_chr_exn_v_def; flat_bind_exn_v_def; flat_to_closProof_v_rel_def] THEN
  RULE_ASSUM_TAC (CONV_RULE (TRY_CONV (ONCE_DEPTH_CONV F2CPAUX_FLAT_DO_EQ_CONV))) THEN
  GVS[COND_CASE_EQ; lit_same_type_def; flat_Boolv_def; flat_ctor_same_type_def] THEN
  F2CPAUX_SAME_TYPE_TAC THEN F2CPAUX_STORE_FACTS_TAC THEN
  F2CPAUX_ARGS_TAC THEN F2CPAUX_CLOS_EVAL_TAC THEN F2CPAUX_LEAST_TAC THEN
  IMP_RES_TAC LIST_REL_LENGTH THEN
  GVS[INT_POS; NUM_OF_INT_OF_NUM; flat_to_closProof_v_rel_def; F2CPAUX_abs_pos;
      F2CPAUX_num_of_int_cmp; INT_OF_NUM_LT; INT_OF_NUM_LE; INT_OF_NUM_EQ;
      GT; GE; INT_GT; INT_GE; ORD_11; VAL_EQ; F2CPAUX_MAP_word_ORD_11; explode_11] THEN
  TRY F2CPAUX_EVAL_TAC THEN
  CASE_REWRITE_TAC[LENGTH; HD; LUPDATE_DEF; clos_Unit_def; tuple_tag_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP[] THEN
  REPEAT CONJ_TAC THEN F2CPAUX_CLOSE_TAC;;

let F2CPAUX_OP_BODY_TAC = F2CPAUX_OP_BODY_GEN_TAC ALL_TAC;;

let F2CPAUX_OP_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN F2CPAUX_OP_BODY_TAC;;

(* unfold and split an assumption c args = v by the case tree of c's definition *)
let F2CPAUX_UNFOLD_SPLIT_TAC (c:string) (def:thm) : tactic =
  REPEAT (FIRST_X_ASSUM (fun th ->
    if (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = c with Failure _ -> false)
    then MP_TAC th THEN REWRITE_TAC[def] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
         FLATSEMAUX_SPLIT_TAC
    else failwith "F2CPAUX_UNFOLD_SPLIT_TAC"));;

(* case splits on every free variable of the given types (outermost first) *)
let F2CPAUX_CASES_TYPES_TAC (tys:hol_type list) : tactic =
  let one (asl,w as g) =
    let fv = freesl (w :: map (concl o snd) asl) in
    let v = find (fun v -> mem (type_of v) tys) fv in
    CASES_ON v g in
  REPEAT one;;

(* HOL4 line 645 *)
let op_refs = prove
 (`!op s1 vs s2 res2 t1 xs db t ws tt.
     (op = Src Opref \/ (?n. op = flat_El n) \/ op = Src Opassign)
     ==> flat_do_app (s1:(C,FFI)flat_state) op vs = SOME (s2,res2) /\
         flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\
         clos_evaluate (xs,db,t) = (Rval ws,t1) /\
         ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\
         LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\
         ~(op = Src (ThunkOp ForceThunk))
         ==> ?res2' t1.
               clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t) = (res2',t1) /\
               flat_to_closProof_state_rel s2 t1 /\
               result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel
                 (list_result res2) res2'`,
  F2CPAUX_OP_TAC);;

(* HOL4: Cases_on w \\ Cases_on s ... rename [v_rel (Litv ww) y] \\ Cases_on ww *)
let F2CPAUX_CASES_ARGS_TAC (c:string) (idx:int list) : tactic = fun (asl,w as g) ->
  let th = snd(find (fun (_,th) -> try
             fst(dest_const(fst(strip_comb(lhs(concl th))))) = c with Failure _ -> false) asl) in
  let args = snd(strip_comb(lhs(concl th))) in
  MAP_EVERY (fun i -> CASES_ON (el i args)) idx g;;

(* HOL4 line 713 *)
let op_shifts = prove
 (`!op s1 vs s2 res2 t1 xs db t ws tt.
     (?w s n. op = Src (Shift w s n))
     ==> flat_do_app (s1:(C,FFI)flat_state) op vs = SOME (s2,res2) /\
         flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\
         clos_evaluate (xs,db,t) = (Rval ws,t1) /\
         ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\
         LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\
         ~(op = Src (ThunkOp ForceThunk))
         ==> ?res2' t1.
               clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t) = (res2',t1) /\
               flat_to_closProof_state_rel s2 t1 /\
               result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel
                 (list_result res2) res2'`,
  F2CPAUX_OP_TAC THEN F2CPAUX_CASES_ARGS_TAC "do_shift" [2; 3] THEN
  GVS[do_shift_def; flat_to_closProof_v_rel_def] THEN F2CPAUX_EVAL_TAC THEN
  SIMP[flat_to_closProof_v_rel_def]);;

(* HOL4 line 727 *)
let op_byte_arrays = prove
 (`!op s1 vs s2 res2 t1 xs db t ws tt.
     (op = Src Aw8length \/ op = Src Aw8alloc \/ op = Src Aw8sub_unsafe \/
      op = Src Aw8sub \/ op = Src Aw8update_unsafe \/ op = Src Aw8update)
     ==> flat_do_app (s1:(C,FFI)flat_state) op vs = SOME (s2,res2) /\
         flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\
         clos_evaluate (xs,db,t) = (Rval ws,t1) /\
         ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\
         LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\
         ~(op = Src (ThunkOp ForceThunk))
         ==> ?res2' t1.
               clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t) = (res2',t1) /\
               flat_to_closProof_state_rel s2 t1 /\
               result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel
                 (list_result res2) res2'`,
  F2CPAUX_OP_TAC);;

(* the helpers of op_byte_copy (helper prefix F2CPAUX3_, agent F2COP) *)
(* the bounds test of copy_array (HOL4: Num (ABS k), decided by COOPER_TAC) *)
let F2CPAUX3_lt_num_of_int_abs = prove
 (`!n x:int. n < num_of_int (abs x) <=> &n < abs x`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `abs (x:int)` INT_OF_NUM_OF_INT) THEN
  REWRITE_TAC[INT_ABS_POS] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM th]) THEN
  REWRITE_TAC[INT_OF_NUM_LT]);;

(* the evaluation of the compiled byte copies CopyByteStr and CopyByteAw8   *)
(* (HOL4: fs [copy_array_def] \\ IF_CASES_TAC ... \\ intLib.COOPER_TAC):     *)
(* each bounds check is decided by a case split on its guard, then the lazy *)
(* evaluator runs; the result is the closLang copy_array of the arguments   *)
let F2CPAUX3_COPY_EVAL_TAC : tactic =
  REWRITE_TAC[copy_array_def; I_THM; F2CPAUX3_lt_num_of_int_abs] THEN
  F2CPAUX_EVAL_TAC THEN REWRITE_TAC[];;

let F2CPAUX3_COPY_CASES_TAC (tms:term list) : tactic =
  MAP_EVERY (fun tm -> ASM_CASES_TAC tm THENL
               [F2CPAUX3_COPY_EVAL_TAC THEN F2CPAUX3_COPY_EVAL_TAC THEN NO_TAC;
                ALL_TAC]) tms THEN
  F2CPAUX3_COPY_EVAL_TAC THEN F2CPAUX3_COPY_EVAL_TAC;;

let F2CPAUX3_eval_CopyByteStr_ByteVector = prove
 (CASE_TERM
  `!tt len off bs db (s:(C,FFI)clos_state).
     clos_evaluate ([CopyByteStr tt],
                    CONS (clos_Number len) (CONS (clos_Number off)
                      (CONS (ByteVector bs) db)),s) =
     (match copy_array (bs,off) len NONE with
        NONE -> (Rerr (Rraise (clos_Block subscript_tag [])),s)
      | SOME ds -> (Rval [ByteVector ds],s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CopyByteStr_def] THEN
  F2CPAUX3_COPY_CASES_TAC [`len:int < &0`; `off:int < &0`;
                           `&(LENGTH (bs:byte list)) < (off:int) + len`]);;

let F2CPAUX3_eval_CopyByteStr_RefPtr = prove
 (CASE_TERM
  `!tt len off p src ws db (s:(C,FFI)clos_state).
     FLOOKUP (clos_state_refs s) src = SOME (clos_ByteArray ws)
     ==> clos_evaluate ([CopyByteStr tt],
                        CONS (clos_Number len) (CONS (clos_Number off)
                          (CONS (clos_RefPtr p src) db)),s) =
         (match copy_array (ws,off) len NONE with
            NONE -> (Rerr (Rraise (clos_Block subscript_tag [])),s)
          | SOME ds -> (Rval [ByteVector ds],s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[CopyByteStr_def] THEN
  F2CPAUX3_COPY_CASES_TAC [`len:int < &0`; `off:int < &0`;
                           `&(LENGTH (ws:byte list)) < (off:int) + len`]);;

let F2CPAUX3_eval_CopyByteAw8_ByteVector = prove
 (CASE_TERM
  `!tt dstoff p dst len off bs db (s:(C,FFI)clos_state) ds.
     FLOOKUP (clos_state_refs s) dst = SOME (clos_ByteArray ds)
     ==> clos_evaluate ([CopyByteAw8 tt],
                        CONS (clos_Number dstoff) (CONS (clos_RefPtr p dst)
                          (CONS (clos_Number len) (CONS (clos_Number off)
                            (CONS (ByteVector bs) db)))),s) =
         (match copy_array (bs,off) len (SOME (ds,dstoff)) with
            NONE -> (Rerr (Rraise (clos_Block subscript_tag [])),s)
          | SOME ds' ->
              (Rval [clos_Unit],
               clos_state_refs_fupd
                 (K (clos_state_refs s |+ (dst,clos_ByteArray ds'))) s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[CopyByteAw8_def] THEN
  F2CPAUX3_COPY_CASES_TAC [`len:int < &0`; `off:int < &0`;
                           `&(LENGTH (bs:byte list)) < (off:int) + len`;
                           `dstoff:int < &0`;
                           `&(LENGTH (ds:byte list)) < (dstoff:int) + len`]);;

let F2CPAUX3_eval_CopyByteAw8_RefPtr = prove
 (CASE_TERM
  `!tt dstoff p dst len off q src ws db (s:(C,FFI)clos_state) ds.
     FLOOKUP (clos_state_refs s) src = SOME (clos_ByteArray ws)
     ==> FLOOKUP (clos_state_refs s) dst = SOME (clos_ByteArray ds)
     ==> clos_evaluate ([CopyByteAw8 tt],
                        CONS (clos_Number dstoff) (CONS (clos_RefPtr p dst)
                          (CONS (clos_Number len) (CONS (clos_Number off)
                            (CONS (clos_RefPtr q src) db)))),s) =
         (match copy_array (ws,off) len (SOME (ds,dstoff)) with
            NONE -> (Rerr (Rraise (clos_Block subscript_tag [])),s)
          | SOME ds' ->
              (Rval [clos_Unit],
               clos_state_refs_fupd
                 (K (clos_state_refs s |+ (dst,clos_ByteArray ds'))) s))`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REWRITE_TAC[CopyByteAw8_def] THEN
  F2CPAUX3_COPY_CASES_TAC [`len:int < &0`; `off:int < &0`;
                           `&(LENGTH (ws:byte list)) < (off:int) + len`;
                           `dstoff:int < &0`;
                           `&(LENGTH (ds:byte list)) < (dstoff:int) + len`]);;

(* copy_array commutes with MAP, and the byte/character conversions of the  *)
(* string copies (HOL4: fs [chars_to_ws_def,MAP_TAKE,MAP_DROP,MAP_MAP_o,     *)
(* o_DEF,ORD_CHR,i2w_pos])                                                    *)
let F2CPAUX3_copy_array_MAP = prove
 (`(!(f:A->B) l off len.
      copy_array (MAP f l,off) len NONE =
      OPTION_MAP (MAP f) (copy_array (l,off) len NONE)) /\
   (!(f:A->B) l off len d doff.
      copy_array (MAP f l,off) len (SOME (MAP f d,doff)) =
      OPTION_MAP (MAP f) (copy_array (l,off) len (SOME (d,doff))))`,
  REWRITE_TAC[copy_array_def; I_THM] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH_MAP] THEN REPEAT STRIP_TAC THEN
  REPEAT COND_CASES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; MAP_APPEND; MAP_TAKE; MAP_DROP]);;

let F2CPAUX3_MAP_word_ORD_ws_to_chars = prove
 (`!ws. MAP ((word:num->byte) o ORD) (ws_to_chars ws) = ws`,
  REWRITE_TAC[ws_to_chars_def] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; o_THM; CONS_11] THEN
  SIMP_TAC[ORD_CHR_RWT; F2CPAUX_val_byte_lt; WORD_VAL]);;

let F2CPAUX3_chars_to_ws = prove
 (`!cs. chars_to_ws cs = MAP ((word:num->byte) o ORD) cs`,
  REWRITE_TAC[chars_to_ws_def; GSYM WORD_IWORD; o_DEF]);;

let F2CPAUX3_copy_array_MAP_ws = prove
 (`!str off len ds doff.
     copy_array (MAP ((word:num->byte) o ORD) str,off) len (SOME (ds,doff)) =
     OPTION_MAP (MAP (word o ORD))
       (copy_array (str,off) len (SOME (ws_to_chars ds,doff)))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o LAND_CONV)
    [GSYM F2CPAUX3_MAP_word_ORD_ws_to_chars] THEN
  REWRITE_TAC[F2CPAUX3_copy_array_MAP]);;

(* rewrite the evaluation of the compiled copy in the goal with the matching *)
(* lemma above, instantiated with the store lookups of the assumptions      *)
let F2CPAUX3_EVAL_COPY_TAC : tactic =
  FIRST [CHANGED_TAC (REWRITE_TAC[F2CPAUX3_eval_CopyByteStr_ByteVector]);
         FIRST_ASSUM(fun th -> CHANGED_TAC
           (REWRITE_TAC[MATCH_MP F2CPAUX3_eval_CopyByteStr_RefPtr th]));
         FIRST_ASSUM(fun th -> CHANGED_TAC
           (REWRITE_TAC[MATCH_MP F2CPAUX3_eval_CopyByteAw8_ByteVector th]));
         FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 -> CHANGED_TAC
           (REWRITE_TAC[MATCH_MP (MATCH_MP F2CPAUX3_eval_CopyByteAw8_RefPtr th1)
                          th2])))];;

(* HOL4 line 804 *)
let op_byte_copy = prove
 (`!op s1 vs s2 res2 t1 xs db t ws tt.
     (op = Src CopyStrAw8 \/ op = Src CopyAw8Str \/ op = Src CopyAw8Aw8 \/
      op = Src CopyStrStr \/ op = Src XorAw8Str_unsafe)
     ==> flat_do_app (s1:(C,FFI)flat_state) op vs = SOME (s2,res2) /\
         flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\
         clos_evaluate (xs,db,t) = (Rval ws,t1) /\
         ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\
         LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\
         ~(op = Src (ThunkOp ForceThunk))
         ==> ?res2' t1.
               clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t) = (res2',t1) /\
               flat_to_closProof_state_rel s2 t1 /\
               result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel
                 (list_result res2) res2'`,
  F2CPAUX_OP_TAC THEN
  REWRITE_TAC[F2CPAUX3_chars_to_ws; F2CPAUX3_MAP_word_ORD_ws_to_chars] THEN
  F2CPAUX3_EVAL_COPY_TAC THEN
  REWRITE_TAC[F2CPAUX3_copy_array_MAP; F2CPAUX3_copy_array_MAP_ws] THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[PAIR_EQ; clos_Unit_def; tuple_tag_def; UNWIND_THM1] THEN
  F2CPAUX_STORE_TAC);;

(* case splits on the variables of the list that are free in the goal *)
let F2CPAUX_CASES_FREE_TAC (vs:term list) : tactic = fun (asl,w as g) ->
  let fv = freesl (w :: map (concl o snd) asl) in
  MAP_EVERY (fun v -> if mem v fv then CASES_ON v else ALL_TAC) vs g;;

(* HOL4 line 879 *)
let MAP_n2w_o_ORD_11 = prove
 (`!l1 l2. MAP ((word:num->byte) o ORD) l1 = MAP (word o ORD) l2 <=> l1 = l2`,
  REWRITE_TAC[F2CPAUX_MAP_word_ORD_11]);;

let F2CPAUX_clos_do_eq_list_clauses = end_itlist CONJ (tl (CONJUNCTS clos_do_eq_def));;

(* HOL4: the two facts of op_eq_gc's qsuff_tac (v_rel preserves equality) *)
let F2CPAUX_do_eq_v_rel = prove
 (`(!v1 v2 x1 x2 b.
      flat_to_closProof_v_rel v1 x1 /\ flat_to_closProof_v_rel v2 x2 /\
      flat_do_eq v1 v2 = Eq_val b
      ==> clos_do_eq x1 x2 = Eq_val b) /\
   (!v1 v2 x1 x2 b.
      ALL2 flat_to_closProof_v_rel v1 x1 /\ ALL2 flat_to_closProof_v_rel v2 x2 /\
      flat_do_eq_list v1 v2 = Eq_val b
      ==> clos_do_eq_list x1 x2 = Eq_val b)`,
  MATCH_MP_TAC flat_do_eq_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_do_eq_def; distinctness "eq_result"]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  F2CPAUX_CASES_FREE_TAC [`l1:lit`; `l2:lit`] THEN
  FS[lit_same_type_def; flat_to_closProof_v_rel_def; COND_CASE_EQ;
     distinctness "eq_result"; injectivity "eq_result"; LIST_REL_NIL; LIST_REL_CONS1] THEN
  RVEQ_TAC THEN IMP_RES_TAC LIST_REL_LENGTH THEN
  GVS[flat_ctor_same_type_def; INT_OF_NUM_EQ; ORD_11; MAP_n2w_o_ORD_11; explode_11;
      VAL_EQ] THEN
  REWRITE_TAC[F2CPAUX_clos_do_eq_list_clauses] THEN
  CONV_TAC (ONCE_DEPTH_CONV F2CPAUX_CLOS_DO_EQ_CONV) THEN CASE_REWRITE_TAC[] THEN
  GVS[INT_OF_NUM_EQ; ORD_11; MAP_n2w_o_ORD_11; explode_11; VAL_EQ] THEN
  (* the list cons case (HOL4: fs [CaseEq"eq_result",bool_case_eq]) *)
  TRY (CASES_ON `flat_do_eq (v1:flat_v) v2` THEN
       FS[distinctness "eq_result"; injectivity "eq_result"] THEN RES_TAC THEN
       ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
       RULE_ASSUM_TAC(REWRITE_RULE[COND_CASE_EQ]) THEN FS[] THEN NO_TAC));;

(* HOL4 line 885 *)
let op_eq_gc = prove
 (`!op s1 vs s2 res2 t1 xs db t ws tt.
     (op = Src ConfigGC \/ op = Src Equality)
     ==> flat_do_app (s1:(C,FFI)flat_state) op vs = SOME (s2,res2) /\
         flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\
         clos_evaluate (xs,db,t) = (Rval ws,t1) /\
         ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\
         LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\
         ~(op = Src (ThunkOp ForceThunk))
         ==> ?res2' t1.
               clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t) = (res2',t1) /\
               flat_to_closProof_state_rel s2 t1 /\
               result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel
                 (list_result res2) res2'`,
  F2CPAUX_OP_TAC THEN
  IMP_RES_TAC (CONJUNCT1 F2CPAUX_do_eq_v_rel) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN SIMP[]);;

(* HOL4 line 923 *)
let v_rel_v_to_char_list = prove
 (`!x ls y.
     flat_v_to_char_list x = SOME ls /\ flat_to_closProof_v_rel x y
     ==> clos_v_to_list y = SOME (MAP (clos_Number o int_of_num) (MAP ORD ls))`,
  MATCH_MP_TAC flat_v_to_char_list_ind THEN
  REWRITE_TAC[flat_v_to_char_list_def; distinctness "option"] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_to_closProof_v_rel_def]) THEN
  FS[COND_CASE_EQ; option_case_eq; LIST_REL_CONS1; LIST_REL_NIL] THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_to_closProof_v_rel_def]) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN RES_TAC THEN
  ASM_REWRITE_TAC[clos_v_to_list_def; MAP; o_THM] THEN CASE_REWRITE_TAC[]);;

(* helpers for op_str *)
let F2CPAUX_strsub_EL = prove
 (`!s i. strsub s i = EL i (explode s)`,
  MATCH_MP_TAC mlstring_INDUCT THEN REWRITE_TAC[strsub_def; explode_thm]);;

let F2CPAUX_ALL2_chars = prove
 (`!l. ALL2 flat_to_closProof_v_rel (MAP (\c. flat_Litv (Char c)) l)
          (MAP (\b. clos_Number (&(val b))) (MAP ((word:num->byte) o ORD) l))`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; ALL2; o_THM; flat_to_closProof_v_rel_def; F2CPAUX_val_word_ORD]);;

let F2CPAUX_MAP_Number_11 = prove
 (`!l1 l2. MAP (clos_Number o int_of_num) l1 = MAP (clos_Number o int_of_num) l2 <=>
           l1 = l2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11; o_THM; injectivity "clos_v";
                  INT_OF_NUM_EQ]);;

let F2CPAUX_some_ORD = prove
 (`!ls. (some ns. SOME (MAP (clos_Number o int_of_num) (MAP ORD ls)) =
                  SOME (MAP (clos_Number o int_of_num) ns) /\ ALL (\n. n < 256) ns) =
        SOME (MAP ORD ls)`,
  GEN_TAC THEN
  REWRITE_TAC[injectivity "option"; F2CPAUX_MAP_Number_11] THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[some_DEF] THEN
  SUBGOAL_THEN `ALL (\n. n < 256) (MAP ORD ls)` ASSUME_TAC THENL
   [REWRITE_TAC[ALL_MAP; o_DEF; ORD_BOUND; ALL_T]; ALL_TAC] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[injectivity "option"] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[]);;

(* HOL4 op_str's qsuff_tac for Strcat *)
let F2CPAUX_strcat = prove
 (`!x vs str y.
     flat_v_to_list x = SOME vs /\ flat_vs_to_string vs = SOME str /\
     flat_to_closProof_v_rel x y
     ==> ?wss. clos_v_to_list y = SOME (MAP ByteVector wss) /\
               FLAT wss = MAP ((word:num->byte) o ORD) (explode str)`,
  MATCH_MP_TAC flat_v_to_list_ind THEN
  REWRITE_TAC[flat_v_to_list_def; distinctness "option"] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_to_closProof_v_rel_def]) THEN
  FS[COND_CASE_EQ; option_case_eq; LIST_REL_CONS1; LIST_REL_NIL] THEN RVEQ_TAC THENL
   [FS[flat_vs_to_string_def; injectivity "option"] THEN RVEQ_TAC THEN
    EXISTS_TAC `[]:(byte list)list` THEN
    REWRITE_TAC[clos_v_to_list_def; MAP; FLAT; explode_thm] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  CASES_ON `v1:flat_v` THEN F2CPAUX_CASES_TYPES_TAC [`:lit`] THEN
  FS[flat_vs_to_string_def; option_case_eq; distinctness "option";
     injectivity "option"] THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_to_closProof_v_rel_def]) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN RES_TAC THEN
  (fun (asl,w as g) ->
     let bv = find_term (fun t -> try fst(dest_const(rator t)) = "ByteVector"
                                  with Failure _ -> false) w in
     let wss = find (fun v -> fst(dest_var v) = "wss") (frees w @ freesl (map (concl o snd) asl)) in
     EXISTS_TAC (mk_comb(mk_comb(`CONS:(byte list)->(byte list)list->(byte list)list`,
                                 rand bv), wss)) g) THEN
  ASM_REWRITE_TAC[clos_v_to_list_def; MAP; FLAT; explode_strcat; MAP_APPEND] THEN
  CASE_REWRITE_TAC[]);;

let F2CPAUX_MAP_ByteVector_11 = prove
 (`!l1 l2. MAP ByteVector l1 = MAP ByteVector l2 <=> l1 = l2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11; injectivity "clos_v"]);;

let F2CPAUX_some_ByteVector = prove
 (`!y wss. clos_v_to_list y = SOME (MAP ByteVector wss)
           ==> (some wss'. clos_v_to_list y = SOME (MAP ByteVector wss')) = SOME wss`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[injectivity "option"; F2CPAUX_MAP_ByteVector_11; some_EQ]);;

(* HOL4 line 933 *)
let op_str = prove
 (`!op s1 vs s2 res2 t1 xs db t ws tt.
     (op = Src Explode \/ op = Src Implode \/ op = Src Strlen \/
      op = Src Strsub \/ op = Src Strcat)
     ==> flat_do_app (s1:(C,FFI)flat_state) op vs = SOME (s2,res2) /\
         flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\
         clos_evaluate (xs,db,t) = (Rval ws,t1) /\
         ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\
         LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\
         ~(op = Src (ThunkOp ForceThunk))
         ==> ?res2' t1.
               clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t) = (res2',t1) /\
               flat_to_closProof_state_rel s2 t1 /\
               result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel
                 (list_result res2) res2'`,
  F2CPAUX_OP_TAC THEN
  TRY (MATCH_MP_TAC IMP_v_rel_to_list THEN REWRITE_TAC[F2CPAUX_ALL2_chars] THEN NO_TAC) THEN
  IMP_RES_TAC v_rel_v_to_char_list THEN IMP_RES_TAC F2CPAUX_strcat THEN
  IMP_RES_TAC F2CPAUX_some_ByteVector THEN
  ASM_REWRITE_TAC[F2CPAUX_some_ORD] THEN TRY F2CPAUX_EVAL_TAC THEN
  SIMP[flat_to_closProof_v_rel_def; MAP_MAP_o; explode_implode] THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_explode; F2CPAUX_num_of_int_cmp; o_THM;
               F2CPAUX_val_word_ORD; F2CPAUX_strsub_EL]);;

(* HOL4 op_globals: the global variables of a state_rel pair (HOL4: fs       *)
(* [state_rel_def] \\ Cases_on t.globals \\ fs [GSYM ADD1,EL,LIST_REL_EL] ...) *)
let F2CPAUX_state_rel_globals = prove
 (`!s t. flat_to_closProof_state_rel (s:(C,FFI)flat_state) (t:(C,FFI)clos_state)
         ==> ?g0 gs. clos_state_globals t = CONS g0 gs /\
                     ALL2 (OPTREL flat_to_closProof_v_rel) (flat_state_globals s) gs`,
  REWRITE_TAC[flat_to_closProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`HD (clos_state_globals (t:(C,FFI)clos_state))`;
                        `TL (clos_state_globals (t:(C,FFI)clos_state))`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONS_HD_TL THEN
  ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL]);;

let F2CPAUX_globals_lookup = prove
 (`!s t n. flat_to_closProof_state_rel (s:(C,FFI)flat_state) (t:(C,FFI)clos_state)
           ==> n < LENGTH (flat_state_globals s)
           ==> IS_SOME (EL n (flat_state_globals s))
           ==> ?y. get_global (n + 1) (clos_state_globals t) = SOME (SOME y) /\
                   flat_to_closProof_v_rel (THE (EL n (flat_state_globals s))) y`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP F2CPAUX_state_rel_globals) THEN
  ASM_REWRITE_TAC[get_global_def; LENGTH; GSYM ADD1; LT_SUC; EL; TL] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  SUBGOAL_THEN `n < LENGTH (gs:(clos_v option)list)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o CONJUNCT2 o REWRITE_RULE[LIST_REL_EL_EQN]) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `IS_SOME (EL n (flat_state_globals (s:(C,FFI)flat_state)))` THEN
  POP_ASSUM_LIST (K ALL_TAC) THEN
  STRUCT_CASES_TAC (ISPEC `EL n (flat_state_globals (s:(C,FFI)flat_state))` option_CASES) THEN
  STRUCT_CASES_TAC (ISPEC `EL n (gs:(clos_v option)list)` option_CASES) THEN
  REWRITE_TAC[OPTREL_THM; IS_SOME_DEF; THE_DEF; injectivity "option"; distinctness "option"] THEN
  MESON_TAC[]);;

let F2CPAUX_globals_init = prove
 (`!s t n v w.
     flat_to_closProof_state_rel (s:(C,FFI)flat_state) (t:(C,FFI)clos_state)
     ==> n < LENGTH (flat_state_globals s)
     ==> EL n (flat_state_globals s) = NONE
     ==> flat_to_closProof_v_rel v w
     ==> get_global (n + 1) (clos_state_globals t) = SOME NONE /\
         flat_to_closProof_state_rel
           (flat_state_globals_fupd (K (LUPDATE (SOME v) n (flat_state_globals s))) s)
           (clos_state_globals_fupd
              (K (LUPDATE (SOME w) (n + 1) (clos_state_globals t))) t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP F2CPAUX_state_rel_globals) THEN
  REPEAT DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  ASM_REWRITE_TAC[get_global_def; LENGTH; GSYM ADD1; LT_SUC; EL; TL; LUPDATE_DEF] THEN
  REWRITE_TAC[NOT_SUC; PRE; SUC_SUB1] THEN
  SUBGOAL_THEN `n < LENGTH (gs:(clos_v option)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o CONJUNCT2 o REWRITE_RULE[LIST_REL_EL_EQN] o
                  check (is_comb o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    STRUCT_CASES_TAC (ISPEC `EL n (gs:(clos_v option)list)` option_CASES) THEN
    REWRITE_TAC[OPTREL_THM];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_to_closProof_state_rel_def]) THEN
  ASM_REWRITE_TAC[flat_to_closProof_state_rel_def; flat_state_INFO.ri_accfupds;
                  clos_state_INFO.ri_accfupds; K_THM; LENGTH; NOT_SUC; TL] THEN
  MATCH_MP_TAC EVERY2_LUPDATE_same THEN ASM_REWRITE_TAC[OPTREL_THM]);;

let F2CPAUX_globals_alloc = prove
 (`!s t n.
     flat_to_closProof_state_rel (s:(C,FFI)flat_state) (t:(C,FFI)clos_state)
     ==> flat_to_closProof_state_rel
           (flat_state_globals_fupd
              (K (APPEND (flat_state_globals s) (REPLICATE n NONE))) s)
           (clos_state_globals_fupd
              (K (APPEND (clos_state_globals t) (REPLICATE n NONE))) t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP F2CPAUX_state_rel_globals) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_to_closProof_state_rel_def]) THEN
  ASM_REWRITE_TAC[flat_to_closProof_state_rel_def; flat_state_INFO.ri_accfupds;
                  clos_state_INFO.ri_accfupds; K_THM; APPEND; LENGTH; NOT_SUC; TL] THEN
  MATCH_MP_TAC EVERY2_APPEND_suff THEN
  ASM_REWRITE_TAC[LIST_REL_REPLICATE_same; OPTREL_THM]);;

(* HOL4 line 998 *)
let op_globals = prove
 (`!op s1 vs s2 res2 t1 xs db t ws tt.
     ((?n. op = GlobalVarLookup n) \/ (?n. op = GlobalVarInit n) \/
      (?n. op = GlobalVarAlloc n))
     ==> flat_do_app (s1:(C,FFI)flat_state) op vs = SOME (s2,res2) /\
         flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\
         clos_evaluate (xs,db,t) = (Rval ws,t1) /\
         ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\
         LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\
         ~(op = Src (ThunkOp ForceThunk))
         ==> ?res2' t1.
               clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t) = (res2',t1) /\
               flat_to_closProof_state_rel s2 t1 /\
               result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel
                 (list_result res2) res2'`,
  F2CPAUX_OP_TAC THEN
  IMP_RES_TAC F2CPAUX_globals_lookup THEN IMP_RES_TAC F2CPAUX_globals_init THEN
  ASM_SIMP_TAC[F2CPAUX_globals_alloc] THEN TRY F2CPAUX_EVAL_TAC THEN SIMP[]);;

(* HOL4: imp_res_tac v_rel_to_list: the closLang list of each related value *)
(* whose flatLang list is known                                              *)
let F2CPAUX_V_TO_LIST_TAC : tactic = fun (asl,w as g) ->
  let hd_is c th = try fst(dest_const(fst(strip_comb(concl th)))) = c
                   with Failure _ -> false in
  let lhs_is c th = try fst(dest_const(fst(strip_comb(lhs(concl th))))) = c
                    with Failure _ -> false in
  let vrels = filter (hd_is "flat_to_closProof_v_rel") (map snd asl)
  and vtls = filter (lhs_is "flat_v_to_list") (map snd asl) in
  let facts = flat (map (fun r -> mapfilter (fun l ->
                MATCH_MP v_rel_to_list (CONJ r l)) vtls) vrels) in
  MAP_EVERY F2CPAUX_STRIP_ASSUME_TAC facts g;;

(* HOL4 line 1039 *)
let op_vectors = prove
 (`!op s1 vs s2 res2 t1 xs db t ws tt.
     (op = Src Vlength \/ op = Src Vsub \/ op = Src Vsub_unsafe \/
      op = Src VfromList)
     ==> flat_do_app (s1:(C,FFI)flat_state) op vs = SOME (s2,res2) /\
         flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\
         clos_evaluate (xs,db,t) = (Rval ws,t1) /\
         ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\
         LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\
         ~(op = Src (ThunkOp ForceThunk))
         ==> ?res2' t1.
               clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t) = (res2',t1) /\
               flat_to_closProof_state_rel s2 t1 /\
               result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel
                 (list_result res2) res2'`,
  F2CPAUX_OP_TAC THEN F2CPAUX_V_TO_LIST_TAC THEN
  TRY F2CPAUX_EVAL_TAC THEN SIMP[flat_to_closProof_v_rel_def] THEN
  TRY (F2CPAUX_ALL2_EL_TAC THEN NO_TAC));;

(* HOL4 line 1071 *)
let op_arrays = prove
 (`!op s1 vs s2 res2 t1 xs db t ws tt.
     (op = Src Aalloc \/ op = Src AallocFixed \/ op = Src Asub_unsafe \/
      op = Src Asub \/ op = Src Alength \/ op = Src Aupdate_unsafe \/
      op = Src Aupdate)
     ==> flat_do_app (s1:(C,FFI)flat_state) op vs = SOME (s2,res2) /\
         flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\
         clos_evaluate (xs,db,t) = (Rval ws,t1) /\
         ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\
         LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\
         ~(op = Src (ThunkOp ForceThunk))
         ==> ?res2' t1.
               clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t) = (res2',t1) /\
               flat_to_closProof_state_rel s2 t1 /\
               result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel
                 (list_result res2) res2'`,
  F2CPAUX_OP_TAC);;

(* HOL4 line 1170 *)
let op_blocks = prove
 (`!op s1 vs s2 res2 t1 xs db t ws tt.
     ((?n0 n1. op = flat_TagLenEq n0 n1) \/ (?l. op = flat_LenEq l) \/
      op = Src ListAppend)
     ==> flat_do_app (s1:(C,FFI)flat_state) op vs = SOME (s2,res2) /\
         flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\
         clos_evaluate (xs,db,t) = (Rval ws,t1) /\
         ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\
         LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\
         ~(op = Src (ThunkOp ForceThunk))
         ==> ?res2' t1.
               clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t) = (res2',t1) /\
               flat_to_closProof_state_rel s2 t1 /\
               result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel
                 (list_result res2) res2'`,
  F2CPAUX_OP_TAC THEN F2CPAUX_V_TO_LIST_TAC THEN
  TRY F2CPAUX_EVAL_TAC THEN SIMP[] THEN
  MATCH_MP_TAC IMP_v_rel_to_list THEN MATCH_MP_TAC EVERY2_APPEND_suff THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 1190 *)
let MAP_n2w_ORD_eq = prove
 (`!s s'. MAP (word o ORD) s = (MAP (word o ORD) s':byte list) <=> s = s'`,
  REWRITE_TAC[F2CPAUX_MAP_word_ORD_11]);;

(* HOL4 line 1196 *)
let imp_cmp_eq_num_cmp = prove
 (`!cmp m n. int_cmp cmp (&m) (&n) <=> num_cmp cmp m n`,
  GEN_TAC THEN CASES_ON `cmp:opb` THEN
  REWRITE_TAC[int_cmp_def; num_cmp_def; INT_OF_NUM_LT; INT_OF_NUM_LE; INT_GT; INT_GE;
              GT; GE]);;

let F2CPAUX_CHECK_TYPE_TAC : tactic =
  GEN_TAC THEN CASES_ON `v:flat_v` THEN REWRITE_TAC[flat_to_v_def] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[check_type_def; semanticPrimitives_Boolv_def; distinctness "v";
              injectivity "v"; distinctness "lit"; injectivity "lit";
              injectivity "flat_v"; distinctness "flat_v"] THEN
  MESON_TAC[];;

(* HOL4 line 1202 *)
let check_type_IntT_flat_to_v = prove
 (`!v. check_type IntT (flat_to_v (v:flat_v)) ==> ?i. v = flat_Litv (IntLit i)`,
  F2CPAUX_CHECK_TYPE_TAC);;

(* HOL4 line 1211 *)
let check_type_Float64T_flat_to_v = prove
 (`!v. check_type Float64T (flat_to_v (v:flat_v)) ==> ?w. v = flat_Litv (Float64 w)`,
  F2CPAUX_CHECK_TYPE_TAC);;

(* HOL4 line 1220 *)
let check_type_WordT_W8_flat_to_v = prove
 (`!v. check_type (WordT W8) (flat_to_v (v:flat_v)) ==> ?w. v = flat_Litv (Word8 w)`,
  F2CPAUX_CHECK_TYPE_TAC);;

(* HOL4 line 1229 *)
let check_type_WordT_W64_flat_to_v = prove
 (`!v. check_type (WordT W64) (flat_to_v (v:flat_v)) ==> ?w. v = flat_Litv (Word64 w)`,
  F2CPAUX_CHECK_TYPE_TAC);;

(* HOL4 line 1238 *)
let check_type_CharT_flat_to_v = prove
 (`!v. check_type CharT (flat_to_v (v:flat_v)) ==> ?c. v = flat_Litv (Char c)`,
  F2CPAUX_CHECK_TYPE_TAC);;

(* HOL4 line 1247 *)
let check_type_BoolT_flat_to_v = prove
 (`!v. check_type BoolT (flat_to_v (v:flat_v)) ==> v = flat_Boolv F \/ v = flat_Boolv T`,
  F2CPAUX_CHECK_TYPE_TAC);;

(* the flat values of a check_type list (HOL4: rpt (first_x_assum (strip_assume_tac *)
(* o MATCH_MP check_type_IntT_flat_to_v) ORELSE ...))                             *)
let F2CPAUX_CHECK_TYPES_TAC : tactic =
  let ths = [check_type_IntT_flat_to_v; check_type_Float64T_flat_to_v;
             check_type_WordT_W8_flat_to_v; check_type_WordT_W64_flat_to_v;
             check_type_CharT_flat_to_v; check_type_BoolT_flat_to_v] in
  REPEAT (FIRST_X_ASSUM (fun th ->
    FIRST (map (fun l g -> F2CPAUX_STRIP_ASSUME_TAC (MATCH_MP l th) g) ths))) THEN
  RVEQ_TAC;;

let F2CPAUX_CONS_EQ_MAP = prove
 (`(!(f:A->B) l h t. CONS h t = MAP f l <=>
                     ?x0 t0. l = CONS x0 t0 /\ h = f x0 /\ t = MAP f t0) /\
   (!(f:A->B) l. [] = MAP f l <=> l = [])`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
  REWRITE_TAC[MAP_EQ_CONS; MAP_EQ_NIL]);;

(* the shapes of the arguments of do_arith and do_conversion: the value list, *)
(* the check_type facts, the related closLang values                          *)
let F2CPAUX_ARGS_SHAPE_TAC : tactic =
  REPEAT (CHANGED_TAC
    (GVS[MAP_EQ_CONS; MAP_EQ_NIL; F2CPAUX_CONS_EQ_MAP; ALL; LIST_REL_CONS1;
         LIST_REL_NIL; SWAP_REVERSE_SYM; REVERSE; APPEND] THEN
     F2CPAUX_CHECK_TYPES_TAC THEN
     GVS[flat_to_v_def; the_Litv_IntLit_def; the_Litv_Float64_def;
         the_Litv_Word8_def; the_Litv_Word64_def; the_Litv_Char_def;
         flat_to_closProof_v_rel_def]));;

let F2CPAUX_flat_to_v_Boolv = prove
 (`!b. flat_to_v (flat_Boolv b) = Boolv b`,
  GEN_TAC THEN REWRITE_TAC[flat_Boolv_def; flat_to_v_def] THEN
  BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[injectivity "flat_v"; injectivity "option"; PAIR_EQ;
              true_tag_def; false_tag_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let F2CPAUX_v_to_flat_Boolv = prove
 (`!b. v_to_flat (Boolv b) = flat_Boolv b`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[v_to_flat_def; semanticPrimitives_Boolv_def] THEN SIMP[]);;

let F2CPAUX_some_pair = prove
 (`!a:A b:B. (some (w1,w2). a = w1 /\ b = w2) = SOME (a,b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[some_DEF; EXISTS_PAIR_THM] THEN
  CONV_TAC (DEPTH_CONV GEN_BETA_CONV) THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[injectivity "option"] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC (DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 1257 *)
let op_arith = prove
 (`!op s1 vs s2 res2 t1 xs db t ws tt.
     (?a ty. op = Src (Arith a ty))
     ==> flat_do_app (s1:(C,FFI)flat_state) op vs = SOME (s2,res2) /\
         flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\
         clos_evaluate (xs,db,t) = (Rval ws,t1) /\
         ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\
         LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\
         ~(op = Src (ThunkOp ForceThunk))
         ==> ?res2' t1.
               clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t) = (res2',t1) /\
               flat_to_closProof_state_rel s2 t1 /\
               result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel
                 (list_result res2) res2'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `a:arith` (X_CHOOSE_THEN `ty:prim_type` ASSUME_TAC)) THEN
  F2CPAUX_CASES_TYPES_TAC [`:arith`; `:prim_type`; `:word_size`] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  F2CPAUX_OP_BODY_GEN_TAC
    (F2CPAUX_UNFOLD_SPLIT_TAC "do_arith" do_arith_def THEN
     F2CPAUX_ARGS_SHAPE_TAC) THEN
  GVS[v_to_flat_def; F2CPAUX_flat_to_v_Boolv; F2CPAUX_v_to_flat_Boolv;
      semanticPrimitivesProps_Boolv_11; F2CPAUX_some_pair; fp_uop_comp_def;
      fp_bop_comp_def; fp_top_comp_def; fpfma_def; flat_to_closProof_v_rel_def] THEN
  TRY F2CPAUX_EVAL_TAC THEN SIMP[flat_to_closProof_v_rel_def] THEN
  REWRITE_TAC[flat_to_v_def; flat_Boolv_def; injectivity "flat_v"; injectivity "option";
              PAIR_EQ; true_tag_def; false_tag_def; semanticPrimitivesProps_Boolv_11] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[semanticPrimitivesProps_Boolv_11]);;

let F2CPAUX_ORD_CHR_int = prove
 (`!i. ~(i < &0) /\ ~(&255 < i) ==> &(ORD (CHR (num_of_int (abs i)))) = i`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[F2CPAUX_abs_pos] THEN
  SUBGOAL_THEN `num_of_int i < 256` ASSUME_TAC THENL
   [ASM_SIMP_TAC[F2CPAUX_num_of_int_cmp] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ORD_CHR_RWT] THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC);;

(* HOL4 line 1319 *)
let op_from_to = prove
 (`!op s1 vs s2 res2 t1 xs db t ws tt.
     (?ty1 ty2. op = Src (FromTo ty1 ty2))
     ==> flat_do_app (s1:(C,FFI)flat_state) op vs = SOME (s2,res2) /\
         flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\
         clos_evaluate (xs,db,t) = (Rval ws,t1) /\
         ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\
         LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\
         ~(op = Src (ThunkOp ForceThunk))
         ==> ?res2' t1.
               clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t) = (res2',t1) /\
               flat_to_closProof_state_rel s2 t1 /\
               result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel
                 (list_result res2) res2'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `ty1:prim_type` (X_CHOOSE_THEN `ty2:prim_type` ASSUME_TAC)) THEN
  F2CPAUX_CASES_TYPES_TAC [`:prim_type`; `:word_size`] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  F2CPAUX_OP_BODY_GEN_TAC
    (F2CPAUX_UNFOLD_SPLIT_TAC "do_conversion" do_conversion_def THEN
     F2CPAUX_ARGS_SHAPE_TAC) THEN
  GVS[v_to_flat_def; F2CPAUX_flat_to_v_Boolv; F2CPAUX_v_to_flat_Boolv;
      semanticPrimitivesProps_Boolv_11; flat_to_closProof_v_rel_def;
      char_to_word8_def; word8_to_char_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT (FIRST_X_ASSUM (F2CPAUX_STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  TRY F2CPAUX_EVAL_TAC THEN SIMP[flat_to_closProof_v_rel_def] THEN
  REWRITE_TAC[w2n_i2w; dimword_def; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ORD_BOUND; ORD_CHR_RWT; F2CPAUX_val_byte_lt;
               F2CPAUX_ORD_CHR_int]);;

let F2CPAUX_dest_Litv_SOME = prove
 (`!v l. flat_dest_Litv v = SOME l <=> v = flat_Litv l`,
  GEN_TAC THEN CASES_ON `v:flat_v` THEN
  REWRITE_TAC[flat_dest_Litv_def; injectivity "option"; injectivity "flat_v";
              distinctness "option"; distinctness "flat_v"]);;

(* HOL4 line 1467 *)
let op_test = prove
 (`!op s1 vs s2 res2 t1 xs db t ws tt.
     (?test ty. op = Src (Test test ty))
     ==> flat_do_app (s1:(C,FFI)flat_state) op vs = SOME (s2,res2) /\
         flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\
         clos_evaluate (xs,db,t) = (Rval ws,t1) /\
         ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\
         LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\
         ~(op = Src (ThunkOp ForceThunk))
         ==> ?res2' t1.
               clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t) = (res2',t1) /\
               flat_to_closProof_state_rel s2 t1 /\
               result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel
                 (list_result res2) res2'`,
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `test:test` (X_CHOOSE_THEN `ty:prim_type` ASSUME_TAC)) THEN
  F2CPAUX_CASES_TYPES_TAC [`:test`; `:prim_type`; `:opb`; `:word_size`] THEN
  REWRITE_TAC[GSYM RIGHT_EXISTS_AND_THM] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  F2CPAUX_OP_BODY_GEN_TAC
    (F2CPAUX_UNFOLD_SPLIT_TAC "flat_do_test" flat_do_test_def THEN
     GVS[F2CPAUX_dest_Litv_SOME; flat_check_type_def; flat_the_Litv_Float64_def;
         flat_Boolv_def]) THEN
  GVS[fp_cmp_comp_def; fp_cmp_def; true_tag_def; false_tag_def; clos_Boolv_def] THEN
  TRY F2CPAUX_EVAL_TAC THEN SIMP[injectivity "clos_v"]);;

let F2CPAUX_state_rel_ffi = prove
 (`!s t. flat_to_closProof_state_rel (s:(C,FFI)flat_state) (t:(C,FFI)clos_state)
         ==> clos_state_ffi t = flat_state_ffi s`,
  SIMP_TAC[flat_to_closProof_state_rel_def]);;

let F2CPAUX_state_rel_refs_ffi = prove
 (`!s t refs trefs f.
     flat_to_closProof_state_rel (s:(C,FFI)flat_state) (t:(C,FFI)clos_state) /\
     store_rel refs trefs
     ==> flat_to_closProof_state_rel
           (flat_state_refs_fupd (K refs) (flat_state_ffi_fupd (K f) s))
           (clos_state_refs_fupd (K trefs) (clos_state_ffi_fupd (K f) t))`,
  SIMP_TAC[flat_to_closProof_state_rel_def; flat_state_INFO.ri_accfupds;
           clos_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 line 1536 *)
let op_ffi = prove
 (`!op s1 vs s2 res2 t1 xs db t ws tt.
     (?n. op = Src (FFI n))
     ==> flat_do_app (s1:(C,FFI)flat_state) op vs = SOME (s2,res2) /\
         flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\
         clos_evaluate (xs,db,t) = (Rval ws,t1) /\
         ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\
         LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\
         ~(op = Src (ThunkOp ForceThunk))
         ==> ?res2' t1.
               clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t) = (res2',t1) /\
               flat_to_closProof_state_rel s2 t1 /\
               result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel
                 (list_result res2) res2'`,
  F2CPAUX_OP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP F2CPAUX_state_rel_ffi th]) THEN
  ASM_REWRITE_TAC[o_DEF] THEN CASE_REWRITE_TAC[] THEN SIMP[] THEN
  TRY (MATCH_MP_TAC F2CPAUX_state_rel_refs_ffi THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC F2CPAUX_store_rel_LUPDATE THEN CASE_REWRITE_TAC[] THEN
       ASM_SIMP_TAC[F2CPAUX_state_rel_store_rel]));;

(* HOL4 line 1558 *)
let op_id = prove
 (`!op s1 vs s2 res2 t1 xs db t ws tt.
     op = Id
     ==> flat_do_app (s1:(C,FFI)flat_state) op vs = SOME (s2,res2) /\
         flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\
         clos_evaluate (xs,db,t) = (Rval ws,t1) /\
         ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\
         LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\
         ~(op = Src (ThunkOp ForceThunk))
         ==> ?res2' t1.
               clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t) = (res2',t1) /\
               flat_to_closProof_state_rel s2 t1 /\
               result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel
                 (list_result res2) res2'`,
  F2CPAUX_OP_TAC THEN TRY F2CPAUX_EVAL_TAC THEN SIMP[]);;

(* HOL4 line 1569 *)
let op_eval = prove
 (`!op s1 vs s2 res2 t1 xs db t ws tt.
     op = Src Eval
     ==> flat_do_app (s1:(C,FFI)flat_state) op vs = SOME (s2,res2) /\
         flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\
         clos_evaluate (xs,db,t) = (Rval ws,t1) /\
         ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\
         LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\
         ~(op = Src (ThunkOp ForceThunk))
         ==> ?res2' t1.
               clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t) = (res2',t1) /\
               flat_to_closProof_state_rel s2 t1 /\
               result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel
                 (list_result res2) res2'`,
  F2CPAUX_OP_TAC);;

(* dest_thunk on related values and stores (HOL4: gvs [oneline dest_thunk_def, *)
(* AllCaseEqs()] \\ Cases_on y \\ gvs [Once v_rel_cases] ...)                    *)
let F2CPAUX_dest_thunk_rel = prove
 (CASE_TERM
  `!s t vs ws.
     flat_to_closProof_state_rel (s:(C,FFI)flat_state) (t:(C,FFI)clos_state) /\
     ALL2 flat_to_closProof_v_rel vs ws
     ==> (match flat_dest_thunk vs (flat_state_refs s) with
            flat_BadRef -> clos_dest_thunk ws (clos_state_refs t) = clos_BadRef
          | flat_NotThunk -> clos_dest_thunk ws (clos_state_refs t) = clos_NotThunk
          | flat_IsThunk m v ->
              ?w. clos_dest_thunk ws (clos_state_refs t) = clos_IsThunk m w /\
                  flat_to_closProof_v_rel v w)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `vs:flat_v list` list_CASES) THEN
  STRUCT_CASES_TAC (ISPEC `ws:clos_v list` list_CASES) THEN
  REWRITE_TAC[ALL2] THEN
  TRY (REWRITE_TAC[flat_dest_thunk_def; clos_dest_thunk_def] THEN CASE_REWRITE_TAC[] THEN
       NO_TAC) THEN
  STRUCT_CASES_TAC (ISPEC `t':flat_v list` list_CASES) THEN
  STRUCT_CASES_TAC (ISPEC `t'':clos_v list` list_CASES) THEN
  REWRITE_TAC[ALL2] THEN
  TRY (REWRITE_TAC[flat_dest_thunk_def; clos_dest_thunk_def] THEN CASE_REWRITE_TAC[] THEN
       NO_TAC) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP F2CPAUX_state_rel_store_rel) THEN
  CASES_ON `h:flat_v` THEN F2CPAUX_CASES_FREE_TAC [`a:lit`] THEN
  FS[flat_to_closProof_v_rel_def] THEN RVEQ_TAC THEN
  REWRITE_TAC[flat_dest_thunk_def; clos_dest_thunk_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[store_lookup_def] THEN
  ASM_CASES_TAC `a1 < LENGTH (flat_state_refs (s:(C,FFI)flat_state))` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    UNDISCH_TAC `store_rel (flat_state_refs (s:(C,FFI)flat_state))
                           (clos_state_refs (t:(C,FFI)clos_state))` THEN
    REWRITE_TAC[store_rel_def] THEN DISCH_THEN(MP_TAC o SPEC `a1:num`) THEN
    ASM_REWRITE_TAC[GSYM NOT_LT] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`s:(C,FFI)flat_state`; `t:(C,FFI)clos_state`; `a1:num`]
           F2CPAUX_state_rel_store) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `EL a1 (flat_state_refs (s:(C,FFI)flat_state))` THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  F2CPAUX_CASES_TYPES_TAC [`:thunk_mode`; `:bool`] THEN CASE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let F2CPAUX_bad_thunk_update_rel = prove
 (`!s t v w m.
     flat_to_closProof_state_rel (s:(C,FFI)flat_state) (t:(C,FFI)clos_state) /\
     flat_to_closProof_v_rel v w
     ==> (clos_bad_thunk_update m w (clos_state_refs t) <=>
          flat_bad_thunk_update m v (flat_state_refs s))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[clos_bad_thunk_update_def; flat_bad_thunk_update_def] THEN
  MP_TAC(ISPECL [`s:(C,FFI)flat_state`; `t:(C,FFI)clos_state`; `[v:flat_v]`; `[w:clos_v]`]
           F2CPAUX_dest_thunk_rel) THEN
  ASM_REWRITE_TAC[ALL2] THEN
  CASES_ON `flat_dest_thunk [v] (flat_state_refs (s:(C,FFI)flat_state))` THEN
  CASE_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* HOL4: gvs [bad_thunk_update_def, ...] on the related values of the goal *)
let F2CPAUX_BAD_THUNK_TAC : tactic = fun (asl,w as g) ->
  let hd_is c th = try fst(dest_const(fst(strip_comb(concl th)))) = c
                   with Failure _ -> false in
  let srels = filter (hd_is "flat_to_closProof_state_rel") (map snd asl)
  and vrels = filter (hd_is "flat_to_closProof_v_rel") (map snd asl) in
  let ths = flat (map (fun s -> mapfilter (fun v ->
              SPEC_ALL (MATCH_MP F2CPAUX_bad_thunk_update_rel (CONJ s v))) vrels) srels) in
  REWRITE_TAC ths g;;

(* HOL4 line 1576 *)
let op_thunk = prove
 (`!th_op op s1 vs s2 res2 t1 xs db t ws tt.
     op = Src (ThunkOp th_op)
     ==> flat_do_app (s1:(C,FFI)flat_state) op vs = SOME (s2,res2) /\
         flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\
         clos_evaluate (xs,db,t) = (Rval ws,t1) /\
         ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\
         LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\
         ~(op = Src (ThunkOp ForceThunk))
         ==> ?res2' t1.
               clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t) = (res2',t1) /\
               flat_to_closProof_state_rel s2 t1 /\
               result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel
                 (list_result res2) res2'`,
  F2CPAUX_OP_TAC THEN F2CPAUX_BAD_THUNK_TAC THEN ASM_REWRITE_TAC[] THEN
  F2CPAUX_CASES_TYPES_TAC [`:thunk_mode`] THEN FS[] THEN
  TRY F2CPAUX_EVAL_TAC THEN F2CPAUX_LEAST_TAC THEN SIMP[] THEN
  REPEAT CONJ_TAC THEN F2CPAUX_CLOSE_TAC);;

(* op_thunk with its thunk operation existentially quantified *)
let F2CPAUX_op_thunk = prove
 (`!op s1 vs s2 res2 t1 xs db t ws tt.
     (?th_op. op = Src (ThunkOp th_op))
     ==> flat_do_app (s1:(C,FFI)flat_state) op vs = SOME (s2,res2) /\
         flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\
         clos_evaluate (xs,db,t) = (Rval ws,t1) /\
         ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\
         LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\
         ~(op = Src (ThunkOp ForceThunk))
         ==> ?res2' t1.
               clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t) = (res2',t1) /\
               flat_to_closProof_state_rel s2 t1 /\
               result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel
                 (list_result res2) res2'`,
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC `th_op:thunk_op`) THEN
  MATCH_MP_TAC op_thunk THEN EXISTS_TAC `th_op:thunk_op` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 1630 *)
let compile_op_correct = prove
 (`!s1 op vs s2 res2 t1 xs db t ws tt.
     flat_do_app (s1:(C,FFI)flat_state) op vs = SOME (s2,res2) /\
     flat_to_closProof_state_rel s1 (t1:(C,FFI)clos_state) /\
     clos_evaluate (xs,db,t) = (Rval ws,t1) /\
     ALL2 flat_to_closProof_v_rel vs (REVERSE ws) /\
     LENGTH xs = LENGTH vs /\ ~(op = Src Opapp) /\
     ~(op = Src (ThunkOp ForceThunk))
     ==> ?res2' t1.
           clos_evaluate ([flat_to_clos_compile_op tt op xs],db,t) = (res2',t1) /\
           flat_to_closProof_state_rel s2 t1 /\
           result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel
             (list_result res2) res2'`,
  let lemmas = [op_refs; op_str; op_shifts; F2CPAUX_op_thunk; op_eq_gc; op_byte_arrays;
                op_arrays; op_test; op_arith; op_from_to; op_globals; op_blocks;
                op_ffi; op_byte_copy; op_eval; op_vectors; op_id] in
  let use th =
    MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] (SPEC_ALL th)) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "flat_op"; injectivity "flat_op"; distinctness "op";
                injectivity "op"; UNWIND_THM1; EXISTS_REFL] THEN
    TRY (MESON_TAC[]) THEN NO_TAC in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CASES_ON `op:flat_op` THENL
   [CASES_ON `a:op`; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  FIRST (map use lemmas @
         [FIRST_X_ASSUM(MP_TAC o check F2CPAUX_is_do_app_eq) THEN
          REWRITE_TAC[flat_do_app_def] THEN CASE_REWRITE_TAC[distinctness "option"] THEN
          NO_TAC;
          FIRST_ASSUM(CONTR_TAC o REWRITE_RULE[])]));;

let F2CPAUX_some_SOME = prove
 (`!P (y:A). (some) P = SOME y ==> P y`,
  REWRITE_TAC[some_DEF] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC[]);;

let F2CPAUX_ALL2_Word64 = prove
 (`!l ys. ALL2 flat_to_closProof_v_rel (MAP (flat_Litv o Word64) l) ys <=>
          ys = MAP clos_Word64 l`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:clos_v list` list_CASES) THEN
  ASM_REWRITE_TAC[MAP; ALL2; NOT_CONS_NIL; CONS_11; o_THM;
                  flat_to_closProof_v_rel_def] THEN MESON_TAC[]);;

let F2CPAUX_ALL2_Word8 = prove
 (`!l ys. ALL2 flat_to_closProof_v_rel (MAP (flat_Litv o Word8) l) ys <=>
          ys = MAP (clos_Number o int_of_num o val) l`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:clos_v list` list_CASES) THEN
  ASM_REWRITE_TAC[MAP; ALL2; NOT_CONS_NIL; CONS_11; o_THM;
                  flat_to_closProof_v_rel_def] THEN MESON_TAC[]);;

let F2CPAUX_MAP_Word64_11 = prove
 (`!l1 l2. MAP clos_Word64 l1 = MAP clos_Word64 l2 <=> l1 = l2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11; injectivity "clos_v"]);;

let F2CPAUX_MAP_Number_val_11 = prove
 (`!l1 l2:byte list. MAP (clos_Number o int_of_num o val) l1 =
                     MAP (clos_Number o int_of_num o val) l2 <=> l1 = l2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11; injectivity "clos_v"; o_THM;
                  INT_OF_NUM_EQ; VAL_EQ]);;

(* HOL4 line 1643 (HOL4's unused binder ?ys is left out) *)
let v_rel_to_words = prove
 (`!x y xs. flat_to_closProof_v_rel x y /\ flat_v_to_words x = SOME xs
            ==> clos_v_to_words y = SOME xs`,
  REWRITE_TAC[flat_v_to_words_def; clos_v_to_words_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o BETA_RULE o MATCH_MP F2CPAUX_some_SOME) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:flat_v`; `y:clos_v`; `MAP (flat_Litv o Word64) xs`] v_rel_to_list) THEN
  ASM_REWRITE_TAC[F2CPAUX_ALL2_Word64] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[injectivity "option"; F2CPAUX_MAP_Word64_11; some_EQ]);;

(* HOL4 line 1670 (HOL4's unused binder ?ys is left out) *)
let v_rel_to_bytes = prove
 (`!x y xs. flat_to_closProof_v_rel x y /\ flat_v_to_bytes x = SOME xs
            ==> clos_v_to_bytes y = SOME xs`,
  REWRITE_TAC[flat_v_to_bytes_def; clos_v_to_bytes_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o BETA_RULE o MATCH_MP F2CPAUX_some_SOME) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:flat_v`; `y:clos_v`; `MAP (flat_Litv o Word8) xs`] v_rel_to_list) THEN
  ASM_REWRITE_TAC[F2CPAUX_ALL2_Word8] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[injectivity "option"; F2CPAUX_MAP_Number_val_11; some_EQ]);;

(* the assumptions with head constant c (or whose lhs has head c) *)
let F2CPAUX_head_is c th =
  let h t = try fst(dest_const(fst(strip_comb t))) = c with Failure _ -> false in
  let tm = concl th in h tm || (is_eq tm && h (lhs tm));;

let F2CPAUX_HEAD_ASSUM (c:string) (ttac:thm_tactic) : tactic =
  FIRST_ASSUM (fun th -> if F2CPAUX_head_is c th then ttac th else failwith c);;

let F2CPAUX_HEAD_X_ASSUM (c:string) (ttac:thm_tactic) : tactic =
  FIRST_X_ASSUM (fun th -> if F2CPAUX_head_is c th then ttac th else failwith c);;

(* HOL4 line 1697 *)
let do_eval_install = prove
 (`!xs s res t ys.
     flat_do_eval xs (flat_state_eval_config (s:(C,FFI)flat_state)) = SOME res /\
     flat_to_closProof_state_rel s (t:(C,FFI)clos_state) /\
     ALL2 flat_to_closProof_v_rel xs ys
     ==> ?decs exps eval_config t'.
           flat_to_closProof_state_rel (flat_state_eval_config_fupd (K eval_config) s) t' /\
           res = (decs,eval_config,Unitv) /\
           clos_do_install ys t =
             (if clos_state_clock t' = 0
              then (Rerr (Rabort Rtimeout_error),t')
              else (Rval (APPEND exps
                            (flat_to_clos_compile [] [flat_Con backend_common_None NONE []])),
                    clos_dec_clock 1 t')) /\
           no_Mat_decs decs /\
           (?envv dsv. xs = [envv; dsv]) /\
           (~(clos_state_clock t' = 0) ==> exps = flat_to_clos_compile_decs decs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  F2CPAUX_HEAD_ASSUM "flat_to_closProof_state_rel"
    (STRIP_ASSUME_TAC o REWRITE_RULE[flat_to_closProof_state_rel_def]) THEN
  F2CPAUX_HEAD_X_ASSUM "install_config_rel'"
    (STRIP_ASSUME_TAC o REWRITE_RULE[install_config_rel'_def]) THEN
  F2CPAUX_HEAD_X_ASSUM "flat_do_eval" MP_TAC THEN
  REWRITE_TAC[flat_do_eval_def] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  FLATSEMAUX_SPLIT_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
  REPEAT (FIRST_X_ASSUM (F2CPAUX_STRIP_ASSUME_TAC o
                         check (fun th -> is_exists (concl th) || is_conj (concl th)))) THEN
  RVEQ_TAC THEN IMP_RES_TAC v_rel_to_bytes THEN IMP_RES_TAC v_rel_to_words THEN
  FIRST_X_ASSUM(fun th ->
    if F2CPAUX_head_is "install_config_compile" th && is_comb (rhs (concl th)) &&
       (try fst(dest_const(rator(rhs(concl th)))) = "SOME" with Failure _ -> false)
    then MP_TAC th else failwith "install_config_compile") THEN
  ASM_REWRITE_TAC[pure_cc_def; inc_compile_decs'_def] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`y:flat_exp list`; `flat_to_clos_compile_decs y`;
    `install_config_compile_oracle_fupd
       (K (shift_seq 1 (install_config_compile_oracle
                          (flat_state_eval_config (s:(C,FFI)flat_state)))))
       (flat_state_eval_config s)`;
    `clos_state_code_fupd (K (clos_state_code (t:(C,FFI)clos_state) |++ []))
       (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle t))) t)`] THEN
  ASM_REWRITE_TAC[CONS_11; PAIR_EQ] THEN
  REWRITE_TAC[clos_do_install_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[o_THM; pure_co_def; PAIR_MAP_THM; I_THM; inc_compile_decs'_def] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAP; set_of_list; DISJOINT_EMPTY; ALL_DISTINCT] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[shift_seq_def; o_THM; PAIR_MAP_DEF; FST; SND; I_THM] THEN
  REWRITE_TAC[flat_to_clos_compile_decs_def; APPEND_NIL; APPEND_EQ_NIL; compile_NOT_NIL] THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM; clos_dec_clock_def; FUPDATE_LIST_THM] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[flat_to_closProof_state_rel_def; flat_state_INFO.ri_accfupds;
                clos_state_INFO.ri_accfupds; K_THM; install_config_rel'_def;
                install_config_INFO.ri_accfupds] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; pure_co_def; PAIR_MAP_DEF; I_THM; shift_seq_def] THEN
    ASM_REWRITE_TAC[];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    SIMP[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM] THEN
    ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (is_forall o concl)) THEN ASM_REWRITE_TAC[SND];
    MESON_TAC[]]);;

(* HOL4 line 1737 *)
let compile_single_DEEP_INTRO = prove
 (`!P m exp.
     (!exp'. flat_to_clos_compile m [exp] = [exp'] ==> P [exp'])
     ==> P (flat_to_clos_compile m [exp])`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM HD_compile] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[HD_compile]);;

(* HOL4 line 1745 *)
let flat_to_closProof_rel_update_thunk = prove
 (`!s1 s2 vs ys v ptr refs1.
     flat_to_closProof_state_rel (s1:(C,FFI)flat_state) (s2:(C,FFI)clos_state) /\
     ALL2 flat_to_closProof_v_rel vs ys
     ==> (flat_update_thunk [flat_Loc v ptr] (flat_state_refs s1) vs = SOME refs1
          ==> ?refs2. clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s2) ys =
                      SOME refs2 /\
                      flat_to_closProof_state_rel (flat_state_refs_fupd (K refs1) s1)
                        (clos_state_refs_fupd (K refs2) s2))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `vs:flat_v list` list_CASES) THEN
  REWRITE_TAC[flat_update_thunk_def; distinctness "option"] THEN
  STRUCT_CASES_TAC (ISPEC `t:flat_v list` list_CASES) THEN
  REWRITE_TAC[flat_update_thunk_def; distinctness "option"] THEN
  REWRITE_TAC[LIST_REL_CONS1; LIST_REL_NIL] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[clos_update_thunk_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  MP_TAC(ISPECL [`s1:(C,FFI)flat_state`; `s2:(C,FFI)clos_state`; `[h:flat_v]`; `[h':clos_v]`]
           F2CPAUX_dest_thunk_rel) THEN
  ASM_REWRITE_TAC[ALL2] THEN
  CASES_ON `flat_dest_thunk [h] (flat_state_refs (s1:(C,FFI)flat_state))` THEN
  CASE_REWRITE_TAC[distinctness "option"] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[store_assign_def; store_thunk_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  CASES_ON `EL ptr (flat_state_refs (s1:(C,FFI)flat_state))` THEN
  FS[store_v_same_type_def; F2CPAUX_thunk_mode_CASE_same] THEN
  F2CPAUX_CASES_TYPES_TAC [`:thunk_mode`] THEN FS[] THEN
  F2CPAUX_STORE_FACTS_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[] THEN F2CPAUX_STORE_TAC);;

(* HOL4 lines 232-252: the ML values exps_goal and dec_goal, the induction  *)
(* of compile_correct's proof (HOL4: evaluate_ind |> list_single_induct;     *)
(* here the dec predicate is dec_goal, the decs predicate the second         *)
(* conjunct of compile_correct)                                              *)
let F2CPAUX_exps_goal =
 `\env (s:(C,FFI)flat_state) es.
    !m db res1 s1 (t:(C,FFI)clos_state).
      flat_evaluate env s es = (s1,res1) /\ flat_to_closProof_state_rel s t /\
      flat_to_closProof_env_rel env m db /\
      ALL no_Mat es /\ ~(res1 = Rerr (Rabort Rtype_error))
      ==> ?res2 t1.
            clos_evaluate (flat_to_clos_compile m es,db,t) = (res2,t1) /\
            flat_to_closProof_state_rel s1 t1 /\
            result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel res1 res2`;;

let F2CPAUX_dec_goal = CASE_TERM
 `\(s:(C,FFI)flat_state) d.
    !res1 s1 (t:(C,FFI)clos_state).
      evaluate_dec s d = (s1,res1) /\ flat_to_closProof_state_rel s t /\
      no_Mat_decs [d] /\ ~(res1 = SOME (Rabort Rtype_error))
      ==> ?res2 t1.
            clos_evaluate (flat_to_clos_compile_decs [d],[],t) = (res2,t1) /\
            flat_to_closProof_state_rel s1 t1 /\
            ?v:(A)list.
              (let res1' = (match res1 with NONE -> Rval v | SOME e -> Rerr e) in
               result_rel (ALL2 (\x y. T)) flat_to_closProof_v_rel res1' res2)`;;

let F2CPAUX_decs_goal = CASE_TERM
 `\(s:(C,FFI)flat_state) ds.
    !res1 s1 (t:(C,FFI)clos_state).
      flat_evaluate_decs s ds = (s1,res1) /\ flat_to_closProof_state_rel s t /\
      no_Mat_decs ds /\ ~(res1 = SOME (Rabort Rtype_error))
      ==> ?res2 t1.
            clos_evaluate (flat_to_clos_compile_decs ds,[],t) = (res2,t1) /\
            flat_to_closProof_state_rel s1 t1 /\
            ?v:(A)list.
              (let res1' = (match res1 with NONE -> Rval v | SOME e -> Rerr e) in
               result_rel (ALL2 (\x y. T)) flat_to_closProof_v_rel res1' res2)`;;

let F2CPAUX_cc_ind =
  CONV_RULE (DEPTH_CONV BETA_CONV)
    (ISPECL [F2CPAUX_exps_goal; F2CPAUX_dec_goal; F2CPAUX_decs_goal] flat_evaluate_ind);;

(* the k-th case of the induction (HOL4's suspend blocks), checked to contain *)
(* the constant c                                                              *)
let F2CPAUX_cc_case k c =
  let tm = el k (conjuncts (lhand (concl F2CPAUX_cc_ind))) in
  if can (find_term (fun t -> is_const t && fst(dest_const t) = c)) tm then tm
  else failwith ("F2CPAUX_cc_case: " ^ c);;

(* applying an induction hypothesis of compile_correct (HOL4: first_x_assum   *)
(* drule \\ disch_then drule \\ impl_tac THEN1 (CCONTR_TAC \\ fs []) \\ strip_tac): *)
(* the antecedents that match assumptions are discharged in order, the rest   *)
(* (if any) are proved by side                                               *)
let F2CPAUX_is_ih tm =
  let rec concl_of t =
    let _,b = strip_forall t in if is_imp b then concl_of (rand b) else b in
  let _,b = strip_forall tm in
  is_imp b &&
  (let c = concl_of tm in
   is_exists c &&
   can (find_term (fun t -> is_const t && fst(dest_const t) = "clos_evaluate")) c);;

let F2CPAUX_IH_THEN (side:tactic) (ttac:thm_tactic) : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  let ihs = filter (F2CPAUX_is_ih o concl) ths in
  let rec chain n th =
    let c = snd(strip_forall(concl th)) in
    if not (is_imp c) then n,th else
    let th' = IMP_CURRY_RULE (GEN_ALL th) in
    match mapfilter (fun a -> MATCH_MP th' a) ths with
      th2::_ -> chain (n+1) th2
    | [] -> n,th in
  let tryone ih g =
    let n,th = chain 0 ih in
    if n = 0 then failwith "F2CPAUX_IH_THEN" else
    let th' = REWRITE_RULE[IMP_IMP] (SPEC_ALL th) in
    (UNDISCH_THEN (concl ih) (K ALL_TAC) THEN
     (if is_imp (concl th') then
        MP_TAC th' THEN ANTS_TAC THENL [side; DISCH_THEN ttac]
      else ttac th')) g in
  FIRST (map tryone ihs) g;;

let F2CPAUX_IH_TAC (side:tactic) : tactic =
  F2CPAUX_IH_THEN side F2CPAUX_STRIP_ASSUME_TAC;;

(* the usual side conditions: no_Mat of the subterms, and the subresult is   *)
(* not a type error since the whole result is not one                       *)
let F2CPAUX_SIDE_TAC : tactic =
  ASM_REWRITE_TAC[ALL; no_Mat_def; no_Mat_decs_def] THEN
  TRY (CONJ_TAC) THEN
  REWRITE_TAC[distinctness "result"; injectivity "result"; distinctness "error_result";
              injectivity "error_result"; distinctness "abort"] THEN
  ASM_MESON_TAC[];;

(* the common steps of a case of compile_correct (HOL4: rpt strip_tac \\ fs     *)
(* [evaluate_def,compile_def,flatSemTheory.evaluate_def] \\ fs [pair_case_eq] *)
(* \\ first_x_assum drule ...)                                                *)
let F2CPAUX_state_rel_max_app = prove
 (`!s t. flat_to_closProof_state_rel (s:(C,FFI)flat_state) (t:(C,FFI)clos_state)
         ==> 1 <= clos_state_max_app t`,
  SIMP_TAC[flat_to_closProof_state_rel_def]);;

let F2CPAUX_CC_INTRO_TAC : tactic =
  REPEAT STRIP_TAC THEN
  F2CPAUX_HEAD_ASSUM "flat_to_closProof_state_rel"
    (ASSUME_TAC o MATCH_MP F2CPAUX_state_rel_max_app) THEN
  F2CPAUX_HEAD_X_ASSUM "flat_evaluate" (MP_TAC o ONCE_REWRITE_RULE[flat_evaluate_def]) THEN
  DISCH_TAC THEN GVS[pair_case_eq; case_eq "result"; option_case_eq; flat_do_if_def;
                     COND_CASE_EQ] THEN
  REPEAT (F2CPAUX_IH_TAC F2CPAUX_SIDE_TAC THEN RVEQ_TAC);;

let F2CPAUX_CC_EVAL_TAC : tactic =
  REWRITE_TAC[flat_to_clos_compile_def] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN
  CASE_REWRITE_TAC[] THEN F2CPAUX_EVAL_TAC THEN
  IMP_RES_TAC flat_evaluate_sing THEN IMP_RES_TAC clos_evaluate_SING THEN RVEQ_TAC THEN
  GVS[ALL2; APPEND; HD; LIST_REL_CONS1];;

(* split a free variable of pair type into its components (HOL4 PairCases_on) *)
let F2CPAUX_PAIR_CASES_TAC (name:string) : tactic = fun (asl,w as g) ->
  let v = find (fun v -> fst(dest_var v) = name)
            (freesl (w :: map (concl o snd) asl)) in
  let ty1,ty2 = (match dest_type (type_of v) with (_,[t1;t2]) -> t1,t2 | _ -> failwith "pair") in
  let avoid = freesl (w :: map (concl o snd) asl) in
  let a = variant avoid (mk_var(name ^ "0",ty1)) in
  let b = variant (a::avoid) (mk_var(name ^ "1",ty2)) in
  (MP_TAC(ISPEC v PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN a (X_CHOOSE_THEN b SUBST_ALL_TAC))) g;;

(* HOL4 line 300: Resume compile_correct[nil] *)
let F2CPAUX_cc_nil = prove
 (F2CPAUX_cc_case 0 "flat_evaluate",
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_evaluate_def; flat_to_clos_compile_def;
                                  clos_evaluate_def; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN SIMP[ALL2]);;

(* HOL4 line 304: Resume compile_correct[cons] *)
let F2CPAUX_cc_cons = prove
 (F2CPAUX_cc_case 1 "CONS",
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  F2CPAUX_HEAD_X_ASSUM "flat_evaluate" (MP_TAC o ONCE_REWRITE_RULE[flat_evaluate_def]) THEN
  DISCH_TAC THEN GVS[pair_case_eq; case_eq "result"] THEN
  REPEAT (F2CPAUX_IH_TAC F2CPAUX_SIDE_TAC THEN RVEQ_TAC) THEN
  REWRITE_TAC[flat_to_clos_compile_def] THEN
  ONCE_REWRITE_TAC[clos_evaluate_APPEND] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  IMP_RES_TAC flat_evaluate_sing THEN IMP_RES_TAC clos_evaluate_SING THEN RVEQ_TAC THEN
  GVS[ALL2; APPEND; HD; LIST_REL_CONS1]);;

(* HOL4 line 325: Resume compile_correct[Lit] *)
let F2CPAUX_cc_Lit = prove
 (F2CPAUX_cc_case 2 "flat_Lit",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  F2CPAUX_HEAD_X_ASSUM "flat_evaluate" (MP_TAC o ONCE_REWRITE_RULE[flat_evaluate_def]) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[flat_to_clos_compile_def; compile_lit_def] THEN
  CASES_ON `l:lit` THEN CASE_REWRITE_TAC[] THEN F2CPAUX_EVAL_TAC THEN
  SIMP[flat_to_closProof_v_rel_def; make_const_def]);;

(* HOL4 line 332: Resume compile_correct[Raise] *)
let F2CPAUX_cc_Raise = prove
 (F2CPAUX_cc_case 3 "flat_Raise",
  F2CPAUX_CC_INTRO_TAC THEN F2CPAUX_CC_EVAL_TAC);;

(* HOL4 line 514: Resume compile_correct[Var_local] *)
let F2CPAUX_cc_Var_local = prove
 (F2CPAUX_cc_case 7 "Var_local",
  F2CPAUX_CC_INTRO_TAC THEN
  CASES_ON `ALOOKUP (flat_environment_v (env:(flat_v)flat_environment)) n` THEN
  FS[distinctness "result"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_to_closProof_env_rel_def]) THEN RES_TAC THEN
  F2CPAUX_CC_EVAL_TAC);;

(* HOL4 line 430: Resume compile_correct[Fun] *)
let F2CPAUX_cc_Fun = prove
 (F2CPAUX_cc_case 8 "flat_Fun",
  F2CPAUX_CC_INTRO_TAC THEN F2CPAUX_CC_EVAL_TAC THEN
  REWRITE_TAC[flat_to_closProof_v_rel_def] THEN ASM_MESON_TAC[]);;

(* HOL4 line 487: Resume compile_correct[Con_NONE] *)
let F2CPAUX_cc_Con_NONE = prove
 (F2CPAUX_cc_case 5 "flat_Con",
  F2CPAUX_CC_INTRO_TAC THEN F2CPAUX_CC_EVAL_TAC THEN
  SIMP[flat_to_closProof_v_rel_def; LIST_REL_REVERSE_EQ] THEN ASM_MESON_TAC[]);;

(* HOL4 line 500: Resume compile_correct[Con_SOME] *)
let F2CPAUX_cc_Con_SOME = prove
 (F2CPAUX_cc_case 6 "flat_Con",
  F2CPAUX_CC_INTRO_TAC THEN
  F2CPAUX_PAIR_CASES_TAC "cn" THEN
  F2CPAUX_CC_EVAL_TAC THEN
  SIMP[flat_to_closProof_v_rel_def; LIST_REL_REVERSE_EQ] THEN ASM_MESON_TAC[]);;

(* HOL4 line 536: Resume compile_correct[If] *)
let F2CPAUX_cc_If = prove
 (F2CPAUX_cc_case 10 "flat_If",
  F2CPAUX_CC_INTRO_TAC THEN F2CPAUX_CC_EVAL_TAC);;

(* HOL4 Resume compile_correct[Let]: env_rel (env with v updated_by opt_bind n v1) *)
let F2CPAUX_env_rel_opt_bind = prove
 (`!env m db n v1 v2.
     flat_to_closProof_env_rel env m db /\ flat_to_closProof_v_rel v1 v2
     ==> flat_to_closProof_env_rel (flat_environment_v_fupd (opt_bind n v1) env)
           (CONS n m) (CONS v2 db)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[flat_to_closProof_env_rel_def; flat_environment_INFO.ri_accfupds] THEN
  X_GEN_TAC `k:mlstring` THEN X_GEN_TAC `x:flat_v` THEN
  CASES_ON `n:mlstring option` THEN REWRITE_TAC[opt_bind_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ALOOKUP_THM; findi_def; distinctness "option"; injectivity "option"] THENL
   [DISCH_TAC;
    ASM_CASES_TAC `a:mlstring = k` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[injectivity "option"] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[EL; HD; LENGTH; LT_0];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(k:mlstring = a)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_to_closProof_env_rel_def]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:mlstring`; `x:flat_v`]) THEN
  ASM_REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] (GSYM ADD1); EL; TL; LENGTH; LT_SUC]);;

(* HOL4 line 373: Resume compile_correct[Let] *)
let F2CPAUX_cc_Let = prove
 (F2CPAUX_cc_case 12 "flat_Let",
  F2CPAUX_CC_INTRO_TAC THEN
  IMP_RES_TAC flat_evaluate_sing THEN IMP_RES_TAC clos_evaluate_SING THEN RVEQ_TAC THEN
  GVS[ALL2; LIST_REL_CONS1; LIST_REL_NIL] THEN
  TRY (MP_TAC (SPECL [`env:(flat_v)flat_environment`; `m:(mlstring option)list`;
                      `db:clos_v list`; `n:mlstring option`; `y:flat_v`; `y:clos_v`]
                 F2CPAUX_env_rel_opt_bind) THEN
       ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
       F2CPAUX_IH_TAC F2CPAUX_SIDE_TAC THEN RVEQ_TAC) THEN
  F2CPAUX_CC_EVAL_TAC);;

(* HOL4 line 556: Resume compile_correct[Mat] *)
let F2CPAUX_cc_Mat = prove
 (F2CPAUX_cc_case 11 "flat_Mat",
  F2CPAUX_CC_INTRO_TAC THEN F2CPAUX_CC_EVAL_TAC);;

(* HOL4 Resume compile_correct[Letrec]: the closure environment of a Letrec *)
let F2CPAUX_Recclosure_rule = last (CONJUNCTS flat_to_closProof_v_rel_rules);;

let F2CPAUX_env_rel_letrec = prove
 (CASE_TERM
  `!env m db funs.
     flat_to_closProof_env_rel env m db /\ ALL_DISTINCT (MAP FST funs) /\
     ALL no_Mat (MAP (SND o SND) funs)
     ==> flat_to_closProof_env_rel
           (flat_environment_v_fupd
              (K (flat_build_rec_env funs env (flat_environment_v env))) env)
           (APPEND (MAP (\n. SOME (FST n)) funs) m)
           (APPEND (list_of_seq
                      (clos_Recclosure NONE [] db
                         (MAP (\p. match p with
                                     (f,v,x) ->
                                       (1, HD (flat_to_clos_compile
                                                 (CONS (SOME v)
                                                    (APPEND (MAP (\n. SOME (FST n)) funs) m))
                                                 [x]))) funs))
                      (LENGTH funs)) db)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[build_rec_env_eq_MAP] THEN
  MATCH_MP_TAC flat_to_closProof_env_rel_APPEND THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAP_MAP_o] THEN MATCH_MP_TAC LIST_REL_MAP_GENLIST THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN (CASE_TERM
      `!p:mlstring#mlstring#flat_exp.
         (match p with (f,x,e) -> (f,flat_Recclosure env funs f)) =
         (FST p,flat_Recclosure env funs (FST p))`) (fun th -> REWRITE_TAC[th; SND]) THENL
     [REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[FST]; ALL_TAC] THEN
    MATCH_MP_TAC F2CPAUX_Recclosure_rule THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[MAP_MAP_o; o_DEF] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[]]);;

let F2CPAUX_ALL_arity = prove
 (CASE_TERM
  `!(l:(mlstring#mlstring#flat_exp)list) mm n.
     1 <= n
     ==> ALL (\p. match p with (num_args,e) -> num_args <= n /\ ~(num_args = 0))
             (MAP (\p. match p with (f,v,x) ->
                     (1, HD (flat_to_clos_compile (CONS (SOME v) mm) [x]))) l)`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[MAP; ALL] THEN REPEAT STRIP_TAC THEN
  SPEC_TAC(`h:mlstring#mlstring#flat_exp`,`h:mlstring#mlstring#flat_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* HOL4 line 408: Resume compile_correct[Letrec] *)
let F2CPAUX_cc_Letrec = prove
 (F2CPAUX_cc_case 13 "flat_Letrec",
  F2CPAUX_CC_INTRO_TAC THEN
  MP_TAC (SPECL [`env:(flat_v)flat_environment`; `m:(mlstring option)list`;
                 `db:clos_v list`; `funs:(mlstring#mlstring#flat_exp)list`]
            F2CPAUX_env_rel_letrec) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  F2CPAUX_IH_TAC F2CPAUX_SIDE_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[flat_to_clos_compile_def] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN
  CASE_REWRITE_TAC[] THEN F2CPAUX_EVAL_TAC THEN
  ASM_SIMP_TAC[F2CPAUX_ALL_arity; LENGTH_MAP] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[HD_compile] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

(* HOL4 Resume compile_correct[Handle]: the env_rel of the handler          *)
let F2CPAUX_env_rel_handle = prove
 (`!env m db v1 v2.
     flat_to_closProof_env_rel env m db /\ flat_to_closProof_v_rel v1 v2
     ==> !nm. flat_to_closProof_env_rel
                (flat_environment_v_fupd
                   (K (CONS (nm,v1) (flat_environment_v env))) env)
                (CONS (SOME nm) m) (CONS v2 db)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  MP_TAC (SPECL [`env:(flat_v)flat_environment`; `m:(mlstring option)list`;
                 `db:clos_v list`; `SOME (nm:mlstring)`; `v1:flat_v`; `v2:clos_v`]
            F2CPAUX_env_rel_opt_bind) THEN
  ASM_REWRITE_TAC[flat_to_closProof_env_rel_def; flat_environment_INFO.ri_accfupds;
                  K_THM; APPEND] THEN
  REWRITE_TAC[opt_bind_def] THEN CASE_REWRITE_TAC[]);;

let F2CPAUX_pmatch_rows_Pvar = prove
 (`!nm (rhs:flat_exp) s v.
     pmatch_rows [(flat_Pvar nm, rhs)] (s:(C,FFI)flat_state) v =
     Match ([(nm,v)], flat_Pvar nm, rhs)`,
  REWRITE_TAC[pmatch_rows_def; CONJUNCT1 flat_pmatch_def] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 347: Resume compile_correct[Handle]; the IH of the handler is  *)
(* specialised to the only pattern Pvar nm and kept out of the GVS          *)
let F2CPAUX_cc_Handle = prove
 (F2CPAUX_cc_case 4 "flat_Handle",
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih1")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  F2CPAUX_HEAD_X_ASSUM "ALL" (STRIP_ASSUME_TAC o REWRITE_RULE[ALL; no_Mat_def]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP dest_pat_from_case) THEN
  REWRITE_TAC[dest_pat_thm] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  F2CPAUX_HEAD_ASSUM "flat_to_closProof_state_rel"
    (ASSUME_TAC o MATCH_MP F2CPAUX_state_rel_max_app) THEN
  F2CPAUX_HEAD_X_ASSUM "flat_evaluate" (MP_TAC o ONCE_REWRITE_RULE[flat_evaluate_def]) THEN
  DISCH_TAC THEN
  REMOVE_THEN "ih1" (fun ih1 ->
    let ih1' = REWRITE_RULE[F2CPAUX_pmatch_rows_Pvar; flat_pat_bindings_def;
                            ALL_DISTINCT; MEM; APPEND]
                 (GEN `v:flat_v` (GEN `s':(C,FFI)flat_state`
                    (SPECL [`v:flat_v`; `flat_Pvar nm`; `[(nm:mlstring,v:flat_v)]`;
                            `s':(C,FFI)flat_state`; `rhs:flat_exp`] ih1))) in
    GVS[pair_case_eq; case_eq "result"; case_eq "error_result";
        F2CPAUX_pmatch_rows_Pvar; flat_pat_bindings_def; ALL_DISTINCT; MEM] THEN
    F2CPAUX_IH_TAC F2CPAUX_SIDE_TAC THEN RVEQ_TAC THEN ASSUME_TAC ih1') THEN
  TRY (FIRST_ASSUM (fun vth ->
         let c = concl vth in
         if is_comb c && is_comb (rator c) &&
            rator(rator c) = `flat_to_closProof_v_rel` && rand(rator c) = `a:flat_v`
         then ASSUME_TAC (SPEC `nm:mlstring` (MATCH_MP F2CPAUX_env_rel_handle
                (CONJ (ASSUME `flat_to_closProof_env_rel env m db`) vth)))
         else failwith "F2CPAUX_cc_Handle") THEN
       F2CPAUX_IH_TAC F2CPAUX_SIDE_TAC THEN RVEQ_TAC) THEN
  REWRITE_TAC[flat_to_clos_compile_def; dest_pat_def] THEN
  F2CPAUX_CC_EVAL_TAC);;

(* the App case of compile_correct in parts: F2CPAUX_cc_App_case p is the   *)
(* App case under the extra hypothesis p (on op and es)                     *)
let F2CPAUX_cc_App_case (p:term) =
  let tm = F2CPAUX_cc_case 9 "flat_App" in
  let vs,body = strip_forall tm in
  list_mk_forall(vs, mk_imp(p, body));;

(* the IHs of the later evaluations (HOL4: they are only used by the cases  *)
(* that need them) are kept out of the simplifier                           *)
let F2CPAUX_is_dep_ih tm =
  let _,b = strip_forall tm in
  is_imp b && is_forall (rand b) && F2CPAUX_is_ih tm;;

let F2CPAUX_HIDE_DEP_IHS_THEN (tac:tactic) : tactic = fun (asl,w as g) ->
  let ihs = filter (fun (_,th) -> F2CPAUX_is_dep_ih (concl th)) asl in
  (MAP_EVERY (fun (_,th) -> UNDISCH_THEN (concl th) (K ALL_TAC)) ihs THEN tac THEN
   MAP_EVERY (fun (l,th) -> LABEL_TAC l th) (rev ihs)) g;;

let F2CPAUX_APP_SIDE_TAC : tactic =
  ASM_REWRITE_TAC[ALL; no_Mat_def; EVERY_REVERSE; flat_AppUnit_def] THEN
  TRY (CONJ_TAC) THEN
  REWRITE_TAC[distinctness "result"; injectivity "result"; distinctness "error_result";
              injectivity "error_result"; distinctness "abort"; distinctness "option";
              injectivity "option"] THEN
  ASM_MESON_TAC[];;

(* HOL4: rpt strip_tac \\ fs [evaluate_def,compile_def,flatSemTheory.evaluate_def] *)
(* \\ rfs [pair_case_eq] \\ first_x_assum drule ... strip_tac                     *)
let F2CPAUX_APP_INTRO_TAC : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN (fun th -> SUBST_ALL_TAC th ORELSE (fun g -> CONJUNCTS_THEN SUBST_ALL_TAC th g) ORELSE
                        STRIP_ASSUME_TAC th) THEN
  REPEAT STRIP_TAC THEN
  F2CPAUX_HEAD_ASSUM "flat_to_closProof_state_rel"
    (ASSUME_TAC o MATCH_MP F2CPAUX_state_rel_max_app) THEN
  F2CPAUX_HEAD_X_ASSUM "flat_evaluate" (MP_TAC o ONCE_REWRITE_RULE[flat_evaluate_def]) THEN
  DISCH_TAC THEN
  F2CPAUX_HIDE_DEP_IHS_THEN
    (GVS[pair_case_eq; case_eq "result"; EVERY_REVERSE] THEN
     F2CPAUX_IH_TAC F2CPAUX_APP_SIDE_TAC THEN RVEQ_TAC);;

(* helpers of the App case of compile_correct (HOL4 Resume compile_correct[App]) *)
let F2CPAUX_arg2_app_error = prove
 (`!xs db t err t1 tt.
     clos_evaluate (xs,db,(t:(C,FFI)clos_state)) = (Rerr err,t1)
     ==> clos_evaluate ([flat_to_clos_arg2 xs (\x f. clos_App tt NONE f [x])],db,t) =
         (Rerr err,t1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_to_clos_arg2_def] THEN
  REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[]) THEN
  TRY (DISCH_TAC THEN F2CPAUX_OP_LET_ERR_TAC THEN NO_TAC) THEN
  ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN
  REWRITE_TAC[clos_evaluate_def; LENGTH; GT; LT_0] THEN
  EVERY_CASE_TAC THEN FS[]);;

let F2CPAUX_do_opapp_SOME = prove
 (CASE_TERM
  `!vs env' e.
     flat_do_opapp vs = SOME (env',e)
     ==> (?env1 n v. vs = [flat_Closure env1 n e; v] /\
                     env' = flat_environment_v_fupd (\env. CONS (n,v) env) env1) \/
         (?env1 funs n v n'.
            vs = [flat_Recclosure env1 funs n; v] /\ ALL_DISTINCT (MAP FST funs) /\
            find_recfun n funs = SOME (n',e) /\
            env' = flat_environment_v_fupd
                     (K (CONS (n',v) (flat_build_rec_env funs env1
                                        (flat_environment_v env1)))) env1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_do_opapp_def] THEN
  REPEAT (TOP_CASE_TAC THEN
          ASM_REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ]) THEN
  STRIP_TAC THEN GVS[]);;

let F2CPAUX_compile_pair = prove
 (`!m e1 e2. flat_to_clos_compile m [e1; e2] =
             [HD (flat_to_clos_compile m [e1]); HD (flat_to_clos_compile m [e2])]`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[flat_to_clos_compile_def] THEN
  MP_TAC (SPECL [`m:(mlstring option)list`; `e1:flat_exp`] HD_compile) THEN
  MP_TAC (SPECL [`m:(mlstring option)list`; `e2:flat_exp`] HD_compile) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[HD; APPEND]);;

let F2CPAUX_evaluate_pair = prove
 (`!x y env (s:(C,FFI)clos_state) ws s1.
     clos_evaluate ([x;y],env,s) = (Rval ws,s1)
     ==> ?w1 w2 s0. ws = [w1;w2] /\ clos_evaluate ([x],env,s) = (Rval [w1],s0) /\
                    clos_evaluate ([y],env,s0) = (Rval [w2],s1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[clos_evaluate_CONS]) THEN
  MP_TAC (ISPECL [`x:clos_exp`; `env:clos_v list`; `s:(C,FFI)clos_state`] clos_evaluate_SING) THEN
  MP_TAC (ISPEC `clos_evaluate ([x],env,s:(C,FFI)clos_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s2:(C,FFI)clos_state` SUBST1_TAC)) THEN
  CASES_ON `r1:(clos_v list,clos_v)result` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "result"; injectivity "result"; PAIR_EQ] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:clos_v list`; `s2:(C,FFI)clos_state`]) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[HD] THEN
  MP_TAC (ISPECL [`y:clos_exp`; `env:clos_v list`; `s2:(C,FFI)clos_state`] clos_evaluate_SING) THEN
  MP_TAC (ISPEC `clos_evaluate ([y],env,s2:(C,FFI)clos_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s3:(C,FFI)clos_state` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))) THEN
  CASES_ON `r2:(clos_v list,clos_v)result` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "result"; injectivity "result"; PAIR_EQ] THEN
  DISCH_THEN(MP_TAC o SPECL [`a':clos_v list`; `s3:(C,FFI)clos_state`]) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[HD] THEN
  REWRITE_TAC[clos_evaluate_def; PAIR_EQ; injectivity "result"] THEN
  CASE_REWRITE_TAC[PAIR_EQ; injectivity "result"] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`r1:clos_v`; `r1':clos_v`; `s2:(C,FFI)clos_state`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_REWRITE_TAC[]);;

let F2CPAUX_env_rel_CONS_fun = prove
 (`!env m db n v1 v2.
     flat_to_closProof_env_rel env m db /\ flat_to_closProof_v_rel v1 v2
     ==> flat_to_closProof_env_rel
           (flat_environment_v_fupd (\env. CONS (n,v1) env) env)
           (CONS (SOME n) m) (CONS v2 db)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`env:(flat_v)flat_environment`; `m:(mlstring option)list`;
                 `db:clos_v list`; `SOME (n:mlstring)`; `v1:flat_v`; `v2:clos_v`]
            F2CPAUX_env_rel_opt_bind) THEN
  ASM_REWRITE_TAC[flat_to_closProof_env_rel_def; flat_environment_INFO.ri_accfupds] THEN
  REWRITE_TAC[opt_bind_def] THEN CASE_REWRITE_TAC[]);;

let F2CPAUX_state_rel_clock0 = prove
 (`!s t. flat_to_closProof_state_rel (s:(C,FFI)flat_state) (t:(C,FFI)clos_state) /\
         flat_state_clock s = 0
         ==> flat_to_closProof_state_rel s (clos_state_clock_fupd (K 0) t)`,
  REWRITE_TAC[flat_to_closProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[]);;

(* helpers of the App case of compile_correct (continued) *)
let F2CPAUX_EVAL_WITH_TAC (extra:thm list) : tactic = fun (asl,w as g) ->
  let conv,dec = F2CPAUX_EVAL_CONV (map snd asl) in
  let net = itlist (net_of_thm false) (itlist (mk_rewrites false) extra []) empty_net in
  let conv' = REWRITES_CONV net ORELSEC conv in
  let norm = F2CPAUX_HEAD_NORM conv' dec in
  CONV_TAC (ONCE_DEPTH_CONV (fun tm ->
    if (try fst(dest_const(fst(strip_comb tm))) = "clos_evaluate"
        with Failure _ -> false) || is_case_app tm || is_cond tm
    then CHANGED_CONV norm tm else failwith "F2CPAUX_EVAL_WITH_TAC")) g;;

(* the evaluation of an application: dest_closure, check_loc, the argument *)
(* lists, EL of the compiled functions                                     *)
let F2CPAUX_APP_EVAL_TAC : tactic = fun (asl,w as g) ->
  let elmaps = mapfilter (fun (_,th) -> MATCH_MP EL_MAP th) asl in
  F2CPAUX_EVAL_WITH_TAC
    ([dest_closure_def; check_loc_def; TAKE_DEF; DROP_DEF; SUB_0; LENGTH_compile;
      GT; LENGTH_MAP] @ elmaps) g;;

let F2CPAUX_APP_COMPILE_TAC : tactic =
  REWRITE_TAC[flat_to_clos_compile_def; dest_nop_def; injectivity "flat_op";
              distinctness "op"; injectivity "op"] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[flat_to_clos_compile_op_def] THEN CASE_REWRITE_TAC[];;

let F2CPAUX_LENGTH_2 = prove
 (`!l:A list. LENGTH l = 2 ==> ?x y. l = [x;y]`,
  GEN_TAC THEN ONCE_REWRITE_TAC[ARITH_RULE `2 = SUC(SUC 0)`] THEN
  REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[]);;

(* the clock and max_app facts of the related states *)
let F2CPAUX_CLOCK_FACTS_TAC : tactic = fun (asl,w as g) ->
  let ths = mapfilter (fun (_,th) ->
              if F2CPAUX_head_is "flat_to_closProof_state_rel" th then th else fail()) asl in
  let eqs = map (MATCH_MP flat_to_closProof_state_rel_IMP_clock) ths in
  let old = map (concl o snd) asl in
  let nw = flat (map (fun eq ->
             let l = lhs(concl eq) in
             mapfilter (fun (_,a) ->
               if free_in l (concl a) && not (F2CPAUX_head_is "flat_to_closProof_state_rel" a)
               then let a' = REWRITE_RULE[eq] a in
                    if mem (concl a') old || concl a' = `T` then fail() else a'
               else fail()) asl) eqs) in
  let mx = map (MATCH_MP F2CPAUX_state_rel_max_app) ths in
  MAP_EVERY (fun t -> if mem (concl t) old then ALL_TAC else ASSUME_TAC t) (nw @ mx) g;;

(* the shape of the arguments of Opapp (HOL4: `?f x. vs = [x;f]` by fs     *)
(* [list_case_eq,SWAP_REVERSE_SYM], `?ef ex. es = [ex;ef]` by               *)
(* evaluate_IMP_LENGTH, compile m [ef; ex] = ..., evaluate_CONS, v_rel_cases) *)
let F2CPAUX_OPAPP_SHAPE_TAC : tactic =
  F2CPAUX_HEAD_X_ASSUM "REVERSE"
    (fun th -> SUBST_ALL_TAC (REWRITE_RULE[REVERSE; APPEND]
                                (ONCE_REWRITE_RULE[SWAP_REVERSE_SYM] th))) THEN
  F2CPAUX_HEAD_ASSUM "flat_evaluate"
    (fun th -> if (try fst(dest_const(rator(rand (lhs (concl th))))) = "REVERSE"
                   with Failure _ -> false)
               then MP_TAC (MATCH_MP flat_evaluate_length th) else failwith "len") THEN
  REWRITE_TAC[LENGTH; LENGTH_REVERSE; ARITH_RULE `SUC(SUC 0) = 2`] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP F2CPAUX_LENGTH_2 o SYM) THEN
  FIRST_X_ASSUM (SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  F2CPAUX_HEAD_X_ASSUM "clos_evaluate"
    (STRIP_ASSUME_TAC o MATCH_MP F2CPAUX_evaluate_pair o
     REWRITE_RULE[REVERSE; APPEND; F2CPAUX_compile_pair]) THEN
  FIRST_X_ASSUM (SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL2; HD_compile]) THEN
  FIRST_X_ASSUM (fun th -> if is_conj (concl th) &&
                              F2CPAUX_head_is "flat_to_closProof_v_rel" (CONJUNCT1 th)
                           then STRIP_ASSUME_TAC th else failwith "conj") THEN
  REWRITE_TAC[REVERSE; APPEND; F2CPAUX_compile_pair; flat_to_clos_arg2_def] THEN
  CASE_REWRITE_TAC[] THEN
  F2CPAUX_HEAD_X_ASSUM "flat_to_closProof_v_rel"
    (fun th -> if can (find_term (fun t -> try let c = fst(dest_const(fst(strip_comb t))) in
                                               c = "flat_Closure" || c = "flat_Recclosure"
                                           with Failure _ -> false)) (concl th)
               then F2CPAUX_STRIP_ASSUME_TAC (REWRITE_RULE[flat_to_closProof_v_rel_def] th)
               else failwith "vrel") THEN
  FIRST_X_ASSUM (SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  F2CPAUX_CLOCK_FACTS_TAC;;

let F2CPAUX_recfun_EL = prove
 (`!(funs:(mlstring#mlstring#flat_exp)list) i (n:mlstring) (n':mlstring) (e:flat_exp).
     ALL_DISTINCT (MAP FST funs) /\ i < LENGTH funs /\ n = FST (EL i funs) /\
     find_recfun n funs = SOME (n',e)
     ==> EL i funs = (n,n',e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`funs:(mlstring#mlstring#flat_exp)list`; `i:num`] find_recfun_EL) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `n:mlstring = FST (EL i funs:mlstring#mlstring#flat_exp)` THEN
  DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[injectivity "option"] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PAIR]);;

let F2CPAUX_no_Mat_EL = prove
 (`!(funs:(mlstring#mlstring#flat_exp)list) i (n:mlstring) (n':mlstring) (e:flat_exp).
     ALL no_Mat (MAP (SND o SND) funs) /\ i < LENGTH funs /\
     EL i funs = (n,n',e)
     ==> no_Mat e`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `ALL no_Mat (MAP (SND o SND) (funs:(mlstring#mlstring#flat_exp)list))` THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN
  DISCH_THEN(MP_TAC o SPEC `e:flat_exp`) THEN DISCH_THEN MATCH_MP_TAC THEN
  EXISTS_TAC `EL i funs:mlstring#mlstring#flat_exp` THEN
  UNDISCH_TAC `EL i funs = (n:mlstring,n':mlstring,e:flat_exp)` THEN
  DISCH_THEN(fun th -> REWRITE_TAC[o_DEF; th; SND] THEN REWRITE_TAC[SYM th]) THEN
  ASM_SIMP_TAC[MEM_EL]);;

(* HOL4: fs [find_recfun_EL] \\ drule IMP_PAIR ...; the equation n = FST (EL *)
(* i funs) is dropped afterwards (with EL i funs = (n,n',e) it would loop)    *)
let F2CPAUX_RECCLOSURE_FACTS_TAC : tactic =
  IMP_RES_TAC F2CPAUX_recfun_EL THEN IMP_RES_TAC F2CPAUX_no_Mat_EL THEN
  REPEAT (FIRST_X_ASSUM (K ALL_TAC o check (fun th ->
    let c = concl th in is_eq c && is_var (lhs c) && type_of (lhs c) = `:mlstring` &&
    can (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "EL"
                             with Failure _ -> false)) (rhs c))));;

let F2CPAUX_SUBST_ENV_TAC : tactic =
  FIRST_X_ASSUM (fun th -> if is_var (lhs (concl th)) &&
                              type_of (lhs (concl th)) = `:(flat_v)flat_environment`
                           then SUBST_ALL_TAC th else failwith "F2CPAUX_SUBST_ENV_TAC");;

let F2CPAUX_DEC_CLOCK_TAC (tn:string) : tactic =
  FIRST_ASSUM (fun th -> if F2CPAUX_head_is "flat_to_closProof_state_rel" th &&
                            fst(dest_var(rand(concl th))) = tn
                         then ASSUME_TAC (CONJUNCT2 (MATCH_MP
                                flat_to_closProof_state_rel_dec_clock th))
                         else failwith "F2CPAUX_DEC_CLOCK_TAC");;

(* the result of the body: HOL4 Cases_on `res1` \\ fs [] \\ imp_res_tac      *)
(* evaluate_sing, then the evaluation of evaluate_app                       *)
let F2CPAUX_APP_FINISH_TAC : tactic =
  CASES_ON `res1:(flat_v list,flat_v)result` THEN
  F2CPAUX_HIDE_DEP_IHS_THEN
    (GVS[] THEN IMP_RES_TAC flat_evaluate_sing THEN RVEQ_TAC THEN
     GVS[LIST_REL_CONS1; ALL2] THEN F2CPAUX_APP_EVAL_TAC THEN GVS[]);;

(* HOL4 line 1778: Resume compile_correct[App], the case op = Opapp *)
let F2CPAUX_cc_App_Opapp = prove
 (F2CPAUX_cc_App_case `(op:flat_op) = Src Opapp`,
  F2CPAUX_APP_INTRO_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "flat_op"; distinctness "op"]) THEN
  F2CPAUX_APP_COMPILE_TAC THENL
   [F2CPAUX_HIDE_DEP_IHS_THEN (GVS[option_case_eq; pair_case_eq; COND_CASE_EQ]) THEN
    F2CPAUX_HEAD_ASSUM "flat_do_opapp"
      (F2CPAUX_STRIP_ASSUME_TAC o MATCH_MP F2CPAUX_do_opapp_SOME) THEN
    F2CPAUX_OPAPP_SHAPE_TAC THENL
     [(* clock 0, Closure *)
      F2CPAUX_APP_EVAL_TAC THEN REWRITE_TAC[PAIR_EQ; injectivity "result"] THEN
      ASM_MESON_TAC[F2CPAUX_state_rel_clock0];
      (* clock 0, Recclosure *)
      F2CPAUX_RECCLOSURE_FACTS_TAC THEN
      F2CPAUX_APP_EVAL_TAC THEN REWRITE_TAC[PAIR_EQ; injectivity "result"] THEN
      ASM_MESON_TAC[F2CPAUX_state_rel_clock0];
      (* Closure *)
      F2CPAUX_SUBST_ENV_TAC THEN
      SUBGOAL_THEN `flat_to_closProof_env_rel
                      (flat_environment_v_fupd (\env. CONS (n,v) env) env1)
                      (CONS (SOME n) m') (CONS w1 db')` ASSUME_TAC THENL
       [MATCH_MP_TAC F2CPAUX_env_rel_CONS_fun THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      F2CPAUX_DEC_CLOCK_TAC "t1" THEN
      F2CPAUX_IH_TAC F2CPAUX_APP_SIDE_TAC THEN RVEQ_TAC THEN
      F2CPAUX_APP_FINISH_TAC;
      (* Recclosure *)
      F2CPAUX_SUBST_ENV_TAC THEN F2CPAUX_RECCLOSURE_FACTS_TAC THEN
      SUBGOAL_THEN (CASE_TERM
        `flat_to_closProof_env_rel
           (flat_environment_v_fupd
              (K (CONS (n',v) (flat_build_rec_env funs env1 (flat_environment_v env1))))
              env1)
           (CONS (SOME n') (APPEND (MAP (\n. SOME (FST n)) funs) m'))
           (CONS w1 (APPEND (list_of_seq (clos_Recclosure NONE [] db'
              (MAP (\p. match p with
                          (f,v,x) ->
                            (1, HD (flat_to_clos_compile
                                      (CONS (SOME v) (APPEND (MAP (\n. SOME (FST n)) funs) m'))
                                      [x]))) funs)) (LENGTH funs)) db'))`) ASSUME_TAC THENL
       [MATCH_MP_TAC env_rel_CONS THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC F2CPAUX_env_rel_letrec THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      F2CPAUX_DEC_CLOCK_TAC "t1" THEN
      F2CPAUX_IH_TAC F2CPAUX_APP_SIDE_TAC THEN RVEQ_TAC THEN
      F2CPAUX_APP_FINISH_TAC];
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP F2CPAUX_arg2_app_error th]) THEN
    REWRITE_TAC[PAIR_EQ; injectivity "result"] THEN ASM_MESON_TAC[]]);;

(* the ForceThunk case of the App case of compile_correct (HOL4: gvs           *)
(* [dest_nop_def, compile_op_def, evaluate_def, AllCaseEqs()] \\ gvs [oneline  *)
(* dest_thunk_def ...] \\ drule_all lookup_thunk ... drule_all rel_update_thunk) *)
let F2CPAUX_compile_AppUnit = prove
 (`flat_to_clos_compile [SOME (implode "f")]
     [flat_AppUnit (Var_local backend_common_None (implode "f"))] =
   [clos_AppUnit (clos_Var backend_common_None 0)]`,
  REWRITE_TAC[flat_AppUnit_def; clos_AppUnit_def] THEN
  F2CPAUX_APP_COMPILE_TAC THEN
  REWRITE_TAC[REVERSE; APPEND; F2CPAUX_compile_pair; flat_to_clos_arg2_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[flat_to_clos_compile_def; findi_def; REVERSE; HD] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[SmartCons_def; NULL; HD]);;

let F2CPAUX_env_rel_thunk = prove
 (`!v w. flat_to_closProof_v_rel v w
         ==> flat_to_closProof_env_rel (flat_environment_REC [(implode "f",v)])
               [SOME (implode "f")] [w]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[flat_to_closProof_env_rel_def; flat_environment_INFO.ri_accessors] THEN
  REWRITE_TAC[ALOOKUP_THM] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[findi_def; LENGTH; EL; HD; ARITH]);;

let F2CPAUX_dest_thunk_IsThunk = prove
 (`!vs st md v. flat_dest_thunk vs st = flat_IsThunk md v ==> ?b n. vs = [flat_Loc b n]`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `vs:flat_v list` list_CASES) THEN
  REWRITE_TAC[flat_dest_thunk_def; distinctness "flat_dest_thunk_ret"] THEN
  STRUCT_CASES_TAC (ISPEC `t:flat_v list` list_CASES) THEN
  REWRITE_TAC[flat_dest_thunk_def; distinctness "flat_dest_thunk_ret"] THEN
  CASES_ON `h:flat_v` THEN
  REWRITE_TAC[flat_dest_thunk_def; distinctness "flat_dest_thunk_ret"; CONS_11;
              injectivity "flat_v"; distinctness "flat_v"] THEN
  MESON_TAC[]);;

let F2CPAUX_ALL2_Loc = prove
 (`!b n ws. ALL2 flat_to_closProof_v_rel [flat_Loc b n] ws <=> ws = [clos_RefPtr b n]`,
  REWRITE_TAC[LIST_REL_CONS1; LIST_REL_NIL; flat_to_closProof_v_rel_def] THEN
  MESON_TAC[]);;

(* split a pair-valued term tm into (n1,n2), rewriting the assumptions *)
let F2CPAUX_PAIR_SPLIT_TAC (tm:term) (n1:string) (n2:string) : tactic =
  let ty1,ty2 = (match dest_type (type_of tm) with (_,[a;b]) -> a,b
                 | _ -> failwith "F2CPAUX_PAIR_SPLIT_TAC") in
  MP_TAC (ISPEC tm PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN (mk_var(n1,ty1)) (X_CHOOSE_THEN (mk_var(n2,ty2))
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th)));;

(* split an option-valued term tm into NONE and SOME n *)
let F2CPAUX_OPTION_SPLIT_TAC (tm:term) (n:string) : tactic =
  let ty = hd(snd(dest_type(type_of tm))) in
  DISJ_CASES_THEN2
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th)
    (X_CHOOSE_THEN (mk_var(n,ty))
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th))
    (ISPEC tm option_nchotomy);;

let F2CPAUX_THUNK_EVAL_TAC : tactic = fun (asl,w as g) ->
  F2CPAUX_EVAL_WITH_TAC (filter (fun th -> F2CPAUX_head_is "clos_dest_thunk" th ||
                                           F2CPAUX_head_is "clos_update_thunk" th)
                           (map snd asl)) g;;

(* HOL4 line 1778: Resume compile_correct[App], the case op = ForceThunk *)
let F2CPAUX_cc_App_Force = prove
 (F2CPAUX_cc_App_case `(op:flat_op) = Src (ThunkOp ForceThunk)`,
  F2CPAUX_APP_INTRO_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "flat_op"; distinctness "op"]) THEN
  F2CPAUX_APP_COMPILE_TAC THENL
   [F2CPAUX_HIDE_DEP_IHS_THEN (GVS[case_eq "flat_dest_thunk_ret"]) THEN
    F2CPAUX_HEAD_ASSUM "flat_to_closProof_state_rel" (fun sth ->
      if fst(dest_var(rand(concl sth))) = "t1" then
      F2CPAUX_HEAD_ASSUM "ALL2" (fun vth ->
        MP_TAC (MATCH_MP F2CPAUX_dest_thunk_rel (CONJ sth vth)))
      else failwith "F2CPAUX_cc_App_Force") THEN
    F2CPAUX_HEAD_ASSUM "flat_dest_thunk" (fun th -> REWRITE_TAC[th]) THEN
    CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
    CASES_ON `a0:thunk_mode` THEN CASE_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THENL
     [FIRST_X_ASSUM (STRIP_ASSUME_TAC o check (is_conj o concl)) THEN RVEQ_TAC THEN
      F2CPAUX_EVAL_TAC THEN
      F2CPAUX_HEAD_ASSUM "clos_dest_thunk" (fun th -> REWRITE_TAC[th]) THEN
      CASE_REWRITE_TAC[] THEN GVS[];
      F2CPAUX_HEAD_ASSUM "flat_dest_thunk"
        (STRIP_ASSUME_TAC o MATCH_MP F2CPAUX_dest_thunk_IsThunk) THEN
      FIRST_X_ASSUM (SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[F2CPAUX_ALL2_Loc]) THEN
      FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th ->
        is_eq (concl th) && is_var (lhs (concl th)) &&
        type_of (lhs (concl th)) = `:clos_v list`)) THEN
      F2CPAUX_PAIR_SPLIT_TAC
        `flat_evaluate (flat_environment_REC [implode "f",a1:flat_v])
           (x:(C,FFI)flat_state)
           [flat_AppUnit (Var_local backend_common_None (implode "f"))]` "s2" "r2" THEN
      RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
      FIRST_ASSUM (fun th -> if F2CPAUX_head_is "flat_to_closProof_v_rel" th &&
                                rand(rator(concl th)) = `a1:flat_v`
                             then ASSUME_TAC (MATCH_MP F2CPAUX_env_rel_thunk th)
                             else failwith "F2CPAUX_cc_App_Force") THEN
      CASES_ON `r2:(flat_v list,flat_v)result` THEN
      RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THENL
       [F2CPAUX_OPTION_SPLIT_TAC
          `flat_update_thunk [flat_Loc b n] (flat_state_refs (s2:(C,FFI)flat_state)) a'`
          "refs" THEN
        RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
        FIRST_X_ASSUM (STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th))) THEN
        RVEQ_TAC THENL
         [RULE_ASSUM_TAC(REWRITE_RULE[distinctness "result"; injectivity "result"]) THEN
          FIRST_ASSUM CONTR_TAC;
          RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
          F2CPAUX_IH_TAC F2CPAUX_APP_SIDE_TAC THEN RVEQ_TAC THEN
          RULE_ASSUM_TAC(REWRITE_RULE[F2CPAUX_compile_AppUnit; result_rel_Rval]) THEN
          FIRST_X_ASSUM (F2CPAUX_STRIP_ASSUME_TAC o check (fun th -> is_exists (concl th))) THEN
          FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th ->
            is_eq (concl th) && is_var (lhs (concl th)))) THEN
          F2CPAUX_HEAD_ASSUM "flat_to_closProof_state_rel" (fun sth ->
            if rand(concl sth) = `t1':(C,FFI)clos_state` then
            F2CPAUX_HEAD_ASSUM "ALL2" (fun vth ->
              if rand(rator(concl vth)) = `a':flat_v list` then
              F2CPAUX_HEAD_ASSUM "flat_update_thunk" (fun uth ->
                F2CPAUX_STRIP_ASSUME_TAC (MATCH_MP (MATCH_MP
                  flat_to_closProof_rel_update_thunk (CONJ sth vth)) uth))
              else failwith "F2CPAUX_cc_App_Force")
            else failwith "F2CPAUX_cc_App_Force") THEN
          F2CPAUX_THUNK_EVAL_TAC THEN
          REWRITE_TAC[PAIR_EQ; result_rel_Rval] THEN ASM_MESON_TAC[]];
        FIRST_X_ASSUM (STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th))) THEN
        RVEQ_TAC THEN
        F2CPAUX_IH_TAC F2CPAUX_APP_SIDE_TAC THEN RVEQ_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[F2CPAUX_compile_AppUnit; result_rel_Rerr1]) THEN
        FIRST_X_ASSUM (F2CPAUX_STRIP_ASSUME_TAC o check (fun th -> is_exists (concl th))) THEN
        FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th ->
          is_eq (concl th) && is_var (lhs (concl th)))) THEN
        F2CPAUX_THUNK_EVAL_TAC THEN
        REWRITE_TAC[PAIR_EQ; result_rel_Rerr1] THEN ASM_MESON_TAC[]]];
    F2CPAUX_EVAL_TAC THEN REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]]);;

(* the Eval case of the App case of compile_correct (HOL4: simp [compile_op_def, *)
(* evaluate_def, dest_nop_def] \\ fs [case_eq_thms, pair_case_eq] \\ drule     *)
(* do_eval_install ... \\ last_x_assum drule ... simp [evaluate_append, ...])    *)
let F2CPAUX_ASM_EVAL_TAC : tactic = fun (asl,w as g) ->
  F2CPAUX_EVAL_WITH_TAC (filter (fun th -> F2CPAUX_head_is "clos_dest_thunk" th ||
                                           F2CPAUX_head_is "clos_update_thunk" th ||
                                           F2CPAUX_head_is "clos_do_install" th)
                           (map snd asl) @ [clos_evaluate_APPEND; evaluate_SmartCons]) g;;

let F2CPAUX_CASES_REWRITE_TAC (tm:term) : tactic =
  ASM_CASES_TAC tm THEN
  POP_ASSUM (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th);;

(* the result relation of a decs IH: let res1' = ... in result_rel ... *)
let F2CPAUX_EVAL_RES_TAC (rr:thm) : tactic =
  FIRST_X_ASSUM (fun th -> if is_let (concl th) then
     F2CPAUX_STRIP_ASSUME_TAC (REWRITE_RULE[rr] (CASE_REWRITE_RULE[]
       (CONV_RULE (DEPTH_CONV let_CONV) th)))
     else failwith "F2CPAUX_EVAL_RES_TAC") THEN
  FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th ->
    is_eq (concl th) && is_var (lhs (concl th))));;

let F2CPAUX_EVAL_DECS_FINISH_TAC (rr:thm) : tactic =
  F2CPAUX_EVAL_RES_TAC rr THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_to_clos_compile_def; REVERSE]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV let_CONV)) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  F2CPAUX_ASM_EVAL_TAC THEN REWRITE_TAC[LAST_APPEND; LAST; NOT_CONS_NIL] THEN
  F2CPAUX_HIDE_DEP_IHS_THEN (GVS[]);;

(* HOL4 line 1778: Resume compile_correct[App], the case op = Eval *)
let F2CPAUX_cc_App_Eval = prove
 (F2CPAUX_cc_App_case `(op:flat_op) = Src Eval`,
  F2CPAUX_APP_INTRO_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "flat_op"; distinctness "op"]) THEN
  F2CPAUX_APP_COMPILE_TAC THENL
   [F2CPAUX_HIDE_DEP_IHS_THEN (GVS[option_case_eq; pair_case_eq]) THEN
    F2CPAUX_HEAD_ASSUM "flat_do_eval" (fun dth ->
      F2CPAUX_HEAD_ASSUM "flat_to_closProof_state_rel" (fun sth ->
        if fst(dest_var(rand(concl sth))) = "t1" then
        F2CPAUX_HEAD_ASSUM "ALL2" (fun vth ->
          F2CPAUX_STRIP_ASSUME_TAC (MATCH_MP do_eval_install
            (CONJ dth (CONJ sth (ONCE_REWRITE_RULE[GSYM LIST_REL_REVERSE_EQ] vth)))))
        else failwith "F2CPAUX_cc_App_Eval")) THEN
    FIRST_X_ASSUM (fun th -> let c = concl th in
                     if is_eq c && is_pair (lhs c)
                     then STRIP_ASSUME_TAC (REWRITE_RULE[PAIR_EQ] th)
                     else failwith "F2CPAUX_cc_App_Eval") THEN
    RVEQ_TAC THEN
    F2CPAUX_HEAD_ASSUM "flat_to_closProof_state_rel" (fun sth ->
      if fst(dest_var(rand(concl sth))) = "t'" then
        ASSUME_TAC (REWRITE_RULE[flat_state_INFO.ri_accfupds; K_THM]
                      (MATCH_MP flat_to_closProof_state_rel_IMP_clock sth))
      else failwith "F2CPAUX_cc_App_Eval") THEN
    F2CPAUX_CASES_REWRITE_TAC `flat_state_clock (x:(C,FFI)flat_state) = 0` THENL
     [FIRST_X_ASSUM (fun th -> if is_eq (concl th) && is_numeral (lhs (concl th)) then
        (RULE_ASSUM_TAC(REWRITE_RULE[SYM th]) THEN ASSUME_TAC (SYM th))
        else failwith "F2CPAUX_cc_App_Eval") THEN
      FIRST_X_ASSUM (fun th -> let c = concl th in
                       if is_eq c && is_pair (lhs c)
                       then STRIP_ASSUME_TAC (REWRITE_RULE[PAIR_EQ] th)
                       else failwith "F2CPAUX_cc_App_Eval") THEN
      RVEQ_TAC THEN F2CPAUX_ASM_EVAL_TAC THEN F2CPAUX_HIDE_DEP_IHS_THEN (GVS[]);
      SUBGOAL_THEN `~(clos_state_clock (t':(C,FFI)clos_state) = 0)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM (fun th -> if is_imp (concl th) && not (is_forall (concl th)) then
        FIRST_ASSUM (fun nth -> SUBST_ALL_TAC (MP th nth))
        else failwith "F2CPAUX_cc_App_Eval") THEN
      POP_ASSUM (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
      SUBGOAL_THEN `~(flat_state_clock (flat_state_eval_config_fupd
                       (K (eval_config:(C)install_config)) (x:(C,FFI)flat_state)) = 0)`
        ASSUME_TAC THENL
       [REWRITE_TAC[flat_state_INFO.ri_accfupds; K_THM] THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      F2CPAUX_DEC_CLOCK_TAC "t'" THEN
      F2CPAUX_PAIR_SPLIT_TAC
        `flat_evaluate_decs (flat_dec_clock (flat_state_eval_config_fupd
           (K (eval_config:(C)install_config)) (x:(C,FFI)flat_state))) decs` "s2" "r2" THEN
      RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
      CASES_ON `r2:(flat_v error_result) option` THEN
      RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th))) THEN
      RVEQ_TAC THEN
      F2CPAUX_IH_TAC F2CPAUX_APP_SIDE_TAC THEN RVEQ_TAC THENL
       [F2CPAUX_EVAL_DECS_FINISH_TAC result_rel_Rval;
        F2CPAUX_EVAL_DECS_FINISH_TAC result_rel_Rerr1]];
    F2CPAUX_EVAL_TAC THEN REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]]);;

(* HOL4 line 1778: Resume compile_correct[App], the case dest_nop op es = NONE *)
(* of the other ops (HOL4: drule compile_op_evaluates_args, match_mp_tac      *)
(* (GEN_ALL compile_op_correct))                                             *)
let F2CPAUX_cc_App_op = prove
 (F2CPAUX_cc_App_case
    `dest_nop (op:flat_op) es = NONE /\ ~(op = Src Opapp) /\ ~(op = Src Eval) /\
     ~(op = Src (ThunkOp ForceThunk))`,
  F2CPAUX_APP_INTRO_TAC THEN ASM_REWRITE_TAC[flat_to_clos_compile_def] THEN
  CASE_REWRITE_TAC[] THENL
   [F2CPAUX_HIDE_DEP_IHS_THEN (GVS[option_case_eq; pair_case_eq]) THEN
    F2CPAUX_HEAD_ASSUM "ALL2" (fun th ->
      ASSUME_TAC (ONCE_REWRITE_RULE[GSYM LIST_REL_REVERSE_EQ] th)) THEN
    F2CPAUX_HEAD_ASSUM "flat_evaluate" (fun th ->
      if (try fst(dest_const(rator(rand (lhs (concl th))))) = "REVERSE"
          with Failure _ -> false)
      then ASSUME_TAC (REWRITE_RULE[LENGTH_REVERSE] (MATCH_MP flat_evaluate_length th))
      else failwith "F2CPAUX_cc_App_op") THEN
    MATCH_MP_TAC compile_op_correct THEN
    MAP_EVERY EXISTS_TAC [`x:(C,FFI)flat_state`; `REVERSE (a:flat_v list)`;
                          `t1:(C,FFI)clos_state`; `v':clos_v list`] THEN
    ASM_REWRITE_TAC[LENGTH_compile; LENGTH_REVERSE];
    IMP_RES_TAC compile_op_evaluates_args THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    ASM_MESON_TAC[]]);;

(* the nop cases (HOL4: gvs [dest_nop_thm,AllCaseEqs()] ... DEEP_INTRO_TAC   *)
(* compile_single_DEEP_INTRO ... fs [flatSemTheory.do_app_def, ...])          *)
let F2CPAUX_compile_SING = prove
 (`!m e. ?c. flat_to_clos_compile m [e] = [c]`,
  REPEAT GEN_TAC THEN EXISTS_TAC `HD (flat_to_clos_compile m [e])` THEN
  REWRITE_TAC[HD_compile]);;

let F2CPAUX_evaluate_nop_inner = prove
 (`!m tt yy db (t:(C,FFI)clos_state).
     clos_evaluate (flat_to_clos_compile m [flat_App tt (Src (FromTo CharT IntT)) [yy]],db,t) =
     clos_evaluate (flat_to_clos_compile m [yy],db,t) /\
     clos_evaluate (flat_to_clos_compile m
                      [flat_App tt (Src (FromTo (WordT W8) IntT)) [yy]],db,t) =
     clos_evaluate (flat_to_clos_compile m [yy],db,t)`,
  REPEAT GEN_TAC THEN F2CPAUX_APP_COMPILE_TAC THEN REWRITE_TAC[REVERSE; APPEND] THEN
  X_CHOOSE_THEN `c:clos_exp` SUBST1_TAC
    (SPECL [`m:(mlstring option)list`; `yy:flat_exp`] F2CPAUX_compile_SING) THEN
  REWRITE_TAC[flat_to_clos_arg1_def; REVERSE] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_evaluate_def] THEN
  MP_TAC (ISPECL [`c:clos_exp`; `db:clos_v list`; `t:(C,FFI)clos_state`]
            clos_evaluate_SING) THEN
  F2CPAUX_PAIR_SPLIT_TAC `clos_evaluate ([c],db,t:(C,FFI)clos_state)` "r" "s1" THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `r:(clos_v list,clos_v)result` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "result"] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:clos_v list`; `s1:(C,FFI)clos_state`]) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[APPEND; LENGTH; EL; HD; LT_0]);;

let F2CPAUX_BYTE_FINISH_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[INT_GT; INT_OF_NUM_LT; INT_OF_NUM_EQ]) THEN
  REWRITE_TAC[GSYM WORD_IWORD; VAL_WORD; DIMINDEX_8; INT_OF_NUM_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ORD_BOUND; ORD_CHR_RWT; F2CPAUX_val_byte_lt] THEN
  ASM_MESON_TAC[F2CPAUX_val_byte_lt; ARITH_RULE `~(n < 0)`;
                ARITH_RULE `n < 256 ==> ~(255 < n)`];;

let F2CPAUX_NOP_CONV_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  DISCH_TAC THEN FLATSEMAUX_SPLIT_TAC THEN
  F2CPAUX_UNFOLD_SPLIT_TAC "do_conversion" do_conversion_def THEN GVS[] THEN
  TRY (FIRST_X_ASSUM (F2CPAUX_STRIP_ASSUME_TAC o MATCH_MP check_type_CharT_flat_to_v)) THEN
  TRY (FIRST_X_ASSUM (F2CPAUX_STRIP_ASSUME_TAC o MATCH_MP check_type_WordT_W8_flat_to_v)) THEN
  TRY (FIRST_X_ASSUM (F2CPAUX_STRIP_ASSUME_TAC o MATCH_MP check_type_IntT_flat_to_v)) THEN
  RVEQ_TAC THEN
  GVS[flat_to_v_def; the_Litv_Char_def; the_Litv_IntLit_def; the_Litv_Word8_def;
      v_to_flat_def; flat_to_closProof_v_rel_def];;

let F2CPAUX_nop_char_int = prove
 (`!s v s' r. flat_do_app (s:(C,FFI)flat_state) (Src (FromTo CharT IntT)) [v] = SOME (s',r)
              ==> ?c. v = flat_Litv (Char c) /\ s' = s /\
                      r = Rval (flat_Litv (IntLit (&(ORD c))))`,
  F2CPAUX_NOP_CONV_TAC);;

let F2CPAUX_nop_w8_int = prove
 (`!s v s' r. flat_do_app (s:(C,FFI)flat_state) (Src (FromTo (WordT W8) IntT)) [v] =
              SOME (s',r)
              ==> ?b. v = flat_Litv (Word8 b) /\ s' = s /\
                      r = Rval (flat_Litv (IntLit (&(val b))))`,
  F2CPAUX_NOP_CONV_TAC);;

let F2CPAUX_nop_int_w8 = prove
 (`!s c s' r. flat_do_app (s:(C,FFI)flat_state) (Src (FromTo IntT (WordT W8)))
                [flat_Litv (IntLit (&(ORD c)))] = SOME (s',r)
              ==> s' = s /\ ?w. r = Rval w /\
                                flat_to_closProof_v_rel w (clos_Number (&(ORD c)))`,
  F2CPAUX_NOP_CONV_TAC THEN F2CPAUX_BYTE_FINISH_TAC);;

let F2CPAUX_nop_int_char = prove
 (`!s b s' r. flat_do_app (s:(C,FFI)flat_state) (Src (FromTo IntT CharT))
                [flat_Litv (IntLit (&(val (b:8 word))))] = SOME (s',r)
              ==> s' = s /\ ?w. r = Rval w /\
                                flat_to_closProof_v_rel w (clos_Number (&(val b)))`,
  F2CPAUX_NOP_CONV_TAC THEN F2CPAUX_BYTE_FINISH_TAC);;

let F2CPAUX_NOP_TAC (inner:thm) (outer:thm) : tactic =
  F2CPAUX_APP_INTRO_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "flat_op"; distinctness "op"; injectivity "op";
                              REVERSE; APPEND]) THEN
  F2CPAUX_APP_COMPILE_TAC THENL
   [F2CPAUX_HEAD_X_ASSUM "flat_evaluate" (fun th ->
      if can (find_term (fun t -> try fst(dest_const t) = "flat_App"
                                  with Failure _ -> false)) (lhs (concl th))
      then MP_TAC (ONCE_REWRITE_RULE[flat_evaluate_def] th)
      else failwith "F2CPAUX_NOP_TAC") THEN
    REWRITE_TAC[REVERSE; APPEND; injectivity "flat_op"; distinctness "op"] THEN DISCH_TAC THEN
    F2CPAUX_HIDE_DEP_IHS_THEN (GVS[pair_case_eq; case_eq "result"; option_case_eq]) THEN
    IMP_RES_TAC flat_evaluate_sing THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REVERSE; APPEND]) THEN
    FIRST_ASSUM (F2CPAUX_STRIP_ASSUME_TAC o MATCH_MP inner) THEN RVEQ_TAC THEN
    F2CPAUX_HIDE_DEP_IHS_THEN (GVS[list_result_def]) THEN
    FIRST_ASSUM (F2CPAUX_STRIP_ASSUME_TAC o MATCH_MP outer) THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[F2CPAUX_evaluate_nop_inner; flat_to_closProof_v_rel_def]) THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[PAIR_EQ; list_result_def] THEN
    F2CPAUX_HIDE_DEP_IHS_THEN (GVS[]);
    RULE_ASSUM_TAC(REWRITE_RULE[F2CPAUX_evaluate_nop_inner]) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]];;

let F2CPAUX_cc_App_nop1 = prove
 (F2CPAUX_cc_App_case
    `(op:flat_op) = Src (FromTo IntT (WordT W8)) /\
     es = [flat_App tt (Src (FromTo CharT IntT)) [yy]]`,
  F2CPAUX_NOP_TAC F2CPAUX_nop_char_int F2CPAUX_nop_int_w8);;

let F2CPAUX_cc_App_nop2 = prove
 (F2CPAUX_cc_App_case
    `(op:flat_op) = Src (FromTo IntT CharT) /\
     es = [flat_App tt (Src (FromTo (WordT W8) IntT)) [yy]]`,
  F2CPAUX_NOP_TAC F2CPAUX_nop_w8_int F2CPAUX_nop_int_char);;

(* HOL4 line 1778: Resume compile_correct[App], from its parts *)
let F2CPAUX_cc_App = prove
 (F2CPAUX_cc_case 9 "flat_App",
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(op:flat_op) = Src (ThunkOp ForceThunk)` THENL
   [MATCH_MP_TAC F2CPAUX_cc_App_Force THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(op:flat_op) = Src Opapp` THENL
   [MATCH_MP_TAC F2CPAUX_cc_App_Opapp THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(op:flat_op) = Src Eval` THENL
   [MATCH_MP_TAC F2CPAUX_cc_App_Eval THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC (ISPEC `dest_nop (op:flat_op) es` option_nchotomy) THEN STRIP_TAC THENL
   [MATCH_MP_TAC F2CPAUX_cc_App_op THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM (DISJ_CASES_TAC o REWRITE_RULE[dest_nop_thm]) THENL
     [MATCH_MP_TAC (GEN_ALL F2CPAUX_cc_App_nop1) THEN ASM_MESON_TAC[];
      MATCH_MP_TAC (GEN_ALL F2CPAUX_cc_App_nop2) THEN ASM_MESON_TAC[]]]);;

(* HOL4 line 1951: Resume compile_correct[dec] *)
let F2CPAUX_ALL2_T = prove
 (`!l:B list. ?v:(A)list. ALL2 (\x y. T) v l`,
  LIST_INDUCT_TAC THENL
   [EXISTS_TAC `[]:(A)list` THEN REWRITE_TAC[ALL2];
    FIRST_X_ASSUM(X_CHOOSE_TAC `v:(A)list`) THEN
    EXISTS_TAC `CONS (ARB:A) v` THEN ASM_REWRITE_TAC[ALL2]]);;

let F2CPAUX_ALL2_T_EQ = prove
 (`!l:B list. (?v:(A)list. ALL2 (\x y. T) v l) <=> T`,
  REWRITE_TAC[F2CPAUX_ALL2_T]);;

let F2CPAUX_env_rel_nil = prove
 (`flat_to_closProof_env_rel (flat_environment_REC []) [] []`,
  REWRITE_TAC[flat_to_closProof_env_rel_def; flat_environment_INFO.ri_accessors;
              ALOOKUP_THM; distinctness "option"]);;

let F2CPAUX_cc_dec = prove
 (F2CPAUX_cc_case 14 "evaluate_dec",
  REPEAT STRIP_TAC THEN
  F2CPAUX_HEAD_X_ASSUM "evaluate_dec" (MP_TAC o ONCE_REWRITE_RULE[flat_evaluate_def]) THEN
  DISCH_TAC THEN
  GVS[pair_case_eq; case_eq "result"; COND_CASE_EQ; no_Mat_decs_def] THEN
  ASSUME_TAC F2CPAUX_env_rel_nil THEN
  F2CPAUX_IH_TAC F2CPAUX_SIDE_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[flat_to_clos_compile_decs_def; APPEND_NIL] THEN
  F2CPAUX_HIDE_DEP_IHS_THEN (GVS[F2CPAUX_ALL2_T_EQ]));;

(* HOL4 line 1964: Resume compile_correct[decs_nil] *)
let F2CPAUX_cc_decs_nil = prove
 (F2CPAUX_cc_case 15 "flat_evaluate_decs",
  REPEAT STRIP_TAC THEN
  F2CPAUX_HEAD_X_ASSUM "flat_evaluate_decs" (MP_TAC o ONCE_REWRITE_RULE[flat_evaluate_def]) THEN
  DISCH_TAC THEN
  GVS[flat_to_clos_compile_decs_def; clos_evaluate_def; F2CPAUX_ALL2_T_EQ]);;

(* HOL4 line 1970: Resume compile_correct[decs_cons] *)
let F2CPAUX_cc_decs_cons = prove
 (F2CPAUX_cc_case 16 "flat_evaluate_decs",
  REPEAT STRIP_TAC THEN
  F2CPAUX_HEAD_X_ASSUM "flat_evaluate_decs" (MP_TAC o ONCE_REWRITE_RULE[flat_evaluate_def]) THEN
  DISCH_TAC THEN
  F2CPAUX_HIDE_DEP_IHS_THEN (GVS[pair_case_eq; option_case_eq; no_Mat_decs_def]) THEN
  F2CPAUX_IH_TAC F2CPAUX_APP_SIDE_TAC THEN RVEQ_TAC THENL
   [F2CPAUX_IH_TAC F2CPAUX_APP_SIDE_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[flat_to_clos_compile_decs_def; APPEND_NIL]) THEN
    REWRITE_TAC[flat_to_clos_compile_decs_def] THEN
    CASES_ON `res1:(flat_v error_result) option` THEN
    F2CPAUX_HIDE_DEP_IHS_THEN (GVS[]) THEN
    ONCE_REWRITE_TAC[clos_evaluate_APPEND] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    F2CPAUX_HIDE_DEP_IHS_THEN (GVS[F2CPAUX_ALL2_T_EQ]);
    RULE_ASSUM_TAC(REWRITE_RULE[flat_to_clos_compile_decs_def; APPEND_NIL]) THEN
    REWRITE_TAC[flat_to_clos_compile_decs_def] THEN
    ONCE_REWRITE_TAC[clos_evaluate_APPEND] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    F2CPAUX_HIDE_DEP_IHS_THEN (GVS[])]);;

(* HOL4 line 1995: Finalise compile_correct *)
let F2CPAUX_cc_all = MP F2CPAUX_cc_ind
  (end_itlist CONJ
     [F2CPAUX_cc_nil; F2CPAUX_cc_cons; F2CPAUX_cc_Lit; F2CPAUX_cc_Raise; F2CPAUX_cc_Handle;
      F2CPAUX_cc_Con_NONE; F2CPAUX_cc_Con_SOME; F2CPAUX_cc_Var_local; F2CPAUX_cc_Fun;
      F2CPAUX_cc_App; F2CPAUX_cc_If; F2CPAUX_cc_Mat; F2CPAUX_cc_Let; F2CPAUX_cc_Letrec;
      F2CPAUX_cc_dec; F2CPAUX_cc_decs_nil; F2CPAUX_cc_decs_cons]);;

(* HOL4 lines 261-1995: compile_correct (Theorem at HOL4 line 261, proved  *)
(* by the suspend/Resume blocks of HOL4 lines 300-1994, Finalise at line    *)
(* 1995); the decs conjunct has a value list of any type (A list)           *)
let flat_to_closProof_compile_correct = prove
 (CASE_TERM
  `(!env (s:(C,FFI)flat_state) es m db res1 s1 (t:(C,FFI)clos_state).
      flat_evaluate env s es = (s1,res1) /\ flat_to_closProof_state_rel s t /\
      flat_to_closProof_env_rel env m db /\
      ALL no_Mat es /\ ~(res1 = Rerr (Rabort Rtype_error))
      ==> ?res2 t1.
            clos_evaluate (flat_to_clos_compile m es,db,t) = (res2,t1) /\
            flat_to_closProof_state_rel s1 t1 /\
            result_rel (ALL2 flat_to_closProof_v_rel) flat_to_closProof_v_rel res1 res2) /\
   (!(s:(C,FFI)flat_state) ds res1 s1 (t:(C,FFI)clos_state).
      flat_evaluate_decs s ds = (s1,res1) /\ flat_to_closProof_state_rel s t /\
      no_Mat_decs ds /\ ~(res1 = SOME (Rabort Rtype_error))
      ==> ?res2 t1.
            clos_evaluate (flat_to_clos_compile_decs ds,[],t) = (res2,t1) /\
            flat_to_closProof_state_rel s1 t1 /\
            ?v:(A)list.
              (let res1' = (match res1 with NONE -> Rval v | SOME e -> Rerr e) in
               result_rel (ALL2 (\x y. T)) flat_to_closProof_v_rel res1' res2))`,
  ACCEPT_TAC (CONJ (CONJUNCT1 F2CPAUX_cc_all) (CONJUNCT2 (CONJUNCT2 F2CPAUX_cc_all))));;

(* HOL4 line 1997: compile_decs_correct = last (CONJUNCTS compile_correct) *)
let flat_to_closProof_compile_decs_correct = prove
 (CASE_TERM
  `!(s:(C,FFI)flat_state) ds res1 s1 (t:(C,FFI)clos_state).
     flat_evaluate_decs s ds = (s1,res1) /\ flat_to_closProof_state_rel s t /\
     no_Mat_decs ds /\ ~(res1 = SOME (Rabort Rtype_error))
     ==> ?res2 t1.
           clos_evaluate (flat_to_clos_compile_decs ds,[],t) = (res2,t1) /\
           flat_to_closProof_state_rel s1 t1 /\
           ?v:(A)list.
             (let res1' = (match res1 with NONE -> Rval v | SOME e -> Rerr e) in
              result_rel (ALL2 (\x y. T)) flat_to_closProof_v_rel res1' res2)`,
  ACCEPT_TAC (CONJUNCT2 flat_to_closProof_compile_correct));;

(* HOL4 line 1999 *)
let compile_decs_correct2 = prove
 (CASE_TERM
  `!s1 decs res_tup res2 s2 t2.
     flat_evaluate_decs (s1:(C,FFI)flat_state) decs = res_tup /\
     clos_evaluate (flat_to_clos_compile_decs decs,[],(s2:(C,FFI)clos_state)) =
       (res2,t2) /\
     flat_to_closProof_state_rel s1 s2 /\ no_Mat_decs decs /\
     ~(SND res_tup = SOME (Rabort Rtype_error))
     ==> flat_to_closProof_state_rel (FST res_tup) t2 /\
         result_rel (\x y. T) flat_to_closProof_v_rel
           (match SND res_tup with NONE -> Rval ([]:(A)list) | SOME e -> Rerr e) res2`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`res_tup:(C,FFI)flat_state # (flat_v error_result) option`,
           `res_tup:(C,FFI)flat_state # (flat_v error_result) option`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`p1:(C,FFI)flat_state`; `p2:(flat_v error_result) option`] THEN
  STRIP_TAC THEN
  MP_TAC (ISPECL [`s1:(C,FFI)flat_state`; `decs:flat_exp list`;
                  `p2:(flat_v error_result) option`; `p1:(C,FFI)flat_state`;
                  `s2:(C,FFI)clos_state`]
            (INST_TYPE [`:A`,`:A`] flat_to_closProof_compile_decs_correct)) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  POP_ASSUM MP_TAC THEN CONV_TAC(DEPTH_CONV let_CONV) THEN
  CASES_ON `p2:(flat_v error_result) option` THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN MESON_TAC[]);;

(* HOL4 line 2016 *)
let flat_to_closProof_FST_SND_EQ_CASE = prove
 (`FST = (\(a:A,b:B). a) /\ SND = (\(a:A,b:B). b)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; FST; SND] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let F2CPAUX_REPLICATE_1 = prove
 (`!x:A. REPLICATE 1 x = [x]`,
  REWRITE_TAC[num_CONV `1`; REPLICATE]);;

(* HOL4 line 2022 *)
let evaluate_compile_prog_initial_state = prove
 (CASE_TERM
  `!max_app ds ffi co cc k.
     0 < max_app
     ==> clos_evaluate (flat_to_clos_compile_prog ds,[],
                        clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY
                          (co:num -> C # clos_prog) cc k) =
         (match clos_evaluate (flat_to_clos_compile_decs ds,[],
                   initial_state' (has_install_list (flat_to_clos_compile_decs ds))
                     ffi max_app FEMPTY co cc k) with
            (Rval vs1,s1) -> (Rval (CONS clos_Unit vs1),s1)
          | res -> res)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= max_app` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[flat_to_clos_compile_prog_def; attach_interpreter_def] THEN
  ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN
  REWRITE_TAC[compile_init_def; clos_initial_state_def; initial_state'_def] THEN
  ASM_CASES_TAC `has_install_list (flat_to_clos_compile_decs ds)` THEN ASM_REWRITE_TAC[] THEN
  F2CPAUX_EVAL_WITH_TAC [clos_state_INFO.ri_accessors; clos_state_INFO.ri_fupds;
                         clos_state_INFO.ri_accfupds; F2CPAUX_REPLICATE_1; get_global_def;
                         LUPDATE_DEF; K_THM; clos_Unit_def; tuple_tag_def] THEN
  REWRITE_TAC[HD; clos_Unit_def; tuple_tag_def]);;

let F2CPAUX_SPLIT_GOAL_EVAL_TAC (p:term -> bool) (n1:string) (n2:string) : tactic =
  fun (asl,w as g) ->
    let tm = find_term (fun t -> (try fst(dest_const(fst(strip_comb t))) = "clos_evaluate"
                                  with Failure _ -> false) && p t) w in
    F2CPAUX_PAIR_SPLIT_TAC tm n1 n2 g;;

(* HOL4 line 2040 *)
let evaluate_compile_prog_initial_state_FST_Err = prove
 (`!max_app ds ffi co cc k e.
     0 < max_app
     ==> (FST (clos_evaluate (flat_to_clos_compile_prog ds,[],
                 clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY
                   (co:num -> C # clos_prog) cc k)) = Rerr e <=>
          FST (clos_evaluate (flat_to_clos_compile_decs ds,[],
                 initial_state' (has_install_list (flat_to_clos_compile_decs ds))
                   ffi max_app FEMPTY co cc k)) = Rerr e)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[evaluate_compile_prog_initial_state] THEN
  F2CPAUX_SPLIT_GOAL_EVAL_TAC
    (fun t -> can (find_term (fun u -> try fst(dest_const u) = "flat_to_clos_compile_decs"
                                       with Failure _ -> false)) t) "r" "s1" THEN
  ASM_REWRITE_TAC[] THEN CASES_ON `r:(clos_v list,clos_v)result` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[FST; distinctness "result"]);;

(* compile_decs_correct2 on the initial states (HOL4: drule_then drule        *)
(* compile_decs_correct2 \\ simp [state_rel_initial_state])                    *)
let F2CPAUX_DECS_CORRECT2_TAC : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  let dth = find (fun th -> F2CPAUX_head_is "clos_evaluate" th) ths in
  let sth = find (fun th -> F2CPAUX_head_is "flat_to_closProof_state_rel" th) ths in
  let nth = find (fun th -> F2CPAUX_head_is "no_Mat_decs" th) ths in
  let fth = find (fun th -> is_neg (concl th) &&
                    (try fst(dest_const(rator(lhs(dest_neg(concl th))))) = "SND"
                     with Failure _ -> false)) ths in
  let fe = rand(lhs(dest_neg(concl fth))) in
  MP_TAC (MATCH_MP (INST_TYPE [`:num`,`:A`] compile_decs_correct2)
            (end_itlist CONJ [REFL fe; dth; sth; nth; fth])) g;;

(* for each clock: the io events, no type error, and the outcomes agree (the *)
(* body of HOL4's compile_semantics' proof, which is by cases on the clock)   *)
let F2CPAUX_semantics_k = prove
 (CASE_TERM
  `!max_app ds ec co cc (ffi:(FFI)ffi_state) k.
     0 < max_app /\ no_Mat_decs ds /\ install_config_rel' (ec:(C)install_config) co cc /\
     ~(SND (flat_evaluate_decs (flat_initial_state ffi k ec) ds) = SOME (Rabort Rtype_error))
     ==> clos_state_ffi (SND (clos_evaluate (flat_to_clos_compile_prog ds,[],
                                clos_initial_state ffi max_app FEMPTY co cc k))) =
         flat_state_ffi (FST (flat_evaluate_decs (flat_initial_state ffi k ec) ds)) /\
         ~(FST (clos_evaluate (flat_to_clos_compile_prog ds,[],
                  clos_initial_state ffi max_app FEMPTY co cc k)) = Rerr (Rabort Rtype_error)) /\
         (!outcome.
            (match FST (clos_evaluate (flat_to_clos_compile_prog ds,[],
                          clos_initial_state ffi max_app FEMPTY co cc k)) with
               Rerr (Rabort Rtimeout_error) -> F
             | Rerr (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
             | _ -> outcome = Success) <=>
            (match SND (flat_evaluate_decs (flat_initial_state ffi k ec) ds) with
               SOME (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
             | SOME (Rabort _) -> F
             | _ -> outcome = Success))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[evaluate_compile_prog_initial_state] THEN
  MP_TAC (ISPECL [`max_app:num`; `ec:(C)install_config`;
                  `co:num->C#(clos_exp)list#(num#num#clos_exp)list`;
                  `cc:C->(clos_exp)list#(num#num#clos_exp)list->
                      (((8)word)list#((64)word)list#C)option`;
                  `ffi:(FFI)ffi_state`; `k:num`;
                  `has_install_list (flat_to_clos_compile_decs ds)`]
            flat_to_closProof_state_rel_initial_state) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  F2CPAUX_SPLIT_GOAL_EVAL_TAC
    (fun t -> can (find_term (fun u -> try fst(dest_const u) = "flat_to_clos_compile_decs"
                                       with Failure _ -> false)) t) "dr" "dsk" THEN
  ASM_REWRITE_TAC[] THEN F2CPAUX_DECS_CORRECT2_TAC THEN
  F2CPAUX_PAIR_SPLIT_TAC
    `flat_evaluate_decs (flat_initial_state (ffi:(FFI)ffi_state) k (ec:(C)install_config)) ds`
    "fs" "fr" THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  FIRST_ASSUM (fun th -> if F2CPAUX_head_is "flat_to_closProof_state_rel" th &&
                            rand (concl th) = `dsk:(C,FFI)clos_state`
                         then ASSUME_TAC (MATCH_MP F2CPAUX_state_rel_ffi th)
                         else failwith "F2CPAUX_semantics_k") THEN
  CASES_ON `fr:(flat_v error_result) option` THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THENL
   [ALL_TAC; CASES_ON `a:flat_v error_result` THEN TRY (CASES_ON `a':abort`)] THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  F2CPAUX_HIDE_DEP_IHS_THEN (GVS[]) THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let F2CPAUX_EXISTS_PAIR_EQ = prove
 (`!(X:A#B) P. (?r s. X = (r,s) /\ P r s) <=> P (FST X) (SND X)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[FST; SND];
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`FST (X:A#B)`; `SND (X:A#B)`] THEN
    ASM_REWRITE_TAC[PAIR]]);;

(* HOL4 line 2058 *)
let compile_semantics' = prove
 (`!max_app ds ec co cc ffi.
     0 < max_app /\ no_Mat_decs ds /\ install_config_rel' (ec:(C)install_config) co cc
     ==> ~(flat_semantics ec (ffi:(FFI)ffi_state) ds = Fail)
     ==> clos_semantics ffi max_app FEMPTY co cc (flat_to_clos_compile_prog ds) =
         flat_semantics ec ffi ds`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[flat_semantics_def] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN (CASE_TERM
   `!k. clos_state_ffi (SND (clos_evaluate (flat_to_clos_compile_prog ds,[],
          clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY
            (co:num -> C # clos_prog) cc k))) =
        flat_state_ffi (FST (flat_evaluate_decs
          (flat_initial_state ffi k (ec:(C)install_config)) ds)) /\
        ~(FST (clos_evaluate (flat_to_clos_compile_prog ds,[],
                 clos_initial_state ffi max_app FEMPTY co cc k)) = Rerr (Rabort Rtype_error)) /\
        (!outcome.
           (match FST (clos_evaluate (flat_to_clos_compile_prog ds,[],
                         clos_initial_state ffi max_app FEMPTY co cc k)) with
              Rerr (Rabort Rtimeout_error) -> F
            | Rerr (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
            | _ -> outcome = Success) <=>
           (match SND (flat_evaluate_decs (flat_initial_state ffi k ec) ds) with
              SOME (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
            | SOME (Rabort _) -> F
            | _ -> outcome = Success))`) ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC F2CPAUX_semantics_k THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[clos_semantics_def] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  (fun (asl,w as g) ->
     let somes = find_terms (fun t -> is_comb t &&
                   (try fst(dest_const(rator t)) = "some" with Failure _ -> false)) w in
     let has_clos t = can (find_term (fun u -> try fst(dest_const u) = "clos_evaluate"
                                               with Failure _ -> false)) t in
     let sc = find has_clos somes and sf = find (not o has_clos) somes in
     (SUBGOAL_THEN (mk_eq(sc,sf)) ASSUME_TAC THENL
        [AP_TERM_TAC THEN ABS_TAC THEN
         REWRITE_TAC[RIGHT_EXISTS_AND_THM; F2CPAUX_EXISTS_PAIR_EQ] THEN ASM_REWRITE_TAC[];
         ASM_REWRITE_TAC[]]) g));;

(* HOL4 line 2167 *)
let inc_compile_decs_intro = prove
 (`!f cc.
     pure_co (insert_interp ## I) o pure_co inc_compile_decs' o
       (f:A -> B # flat_exp list) =
     pure_co inc_compile_decs o f /\
     pure_cc inc_compile_decs'
       (pure_cc (insert_interp ## I)
          (cc:C -> clos_exp list # (num # num # clos_exp) list -> R)) =
     pure_cc inc_compile_decs cc`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pure_co_def; pure_cc_def; FUN_EQ_THM; o_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN
    SPEC_TAC(`(f:A -> B # flat_exp list) x`,`p:B # flat_exp list`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM; I_THM; inc_compile_decs_def;
                inc_compile_decs'_def] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[PAIR_MAP_THM; I_THM];
    REPEAT GEN_TAC THEN CONV_TAC(DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[inc_compile_decs_def; inc_compile_decs'_def] THEN
    CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_MAP_THM; I_THM]]);;

(* HOL4 line 2179 *)
let install_config_rel_def = cake_def
  `install_config_rel (ic:(C)install_config) (co:num -> C # clos_prog) cc <=>
     (!i. no_Mat_decs (SND (install_config_compile_oracle ic i))) /\
     co = pure_co inc_compile_decs o install_config_compile_oracle ic /\
     install_config_compile ic = pure_cc inc_compile_decs cc`;;

(* HOL4 line 2186 *)
let flat_to_closProof_compile_semantics = prove
 (`!max_app ds ec co cc ffi.
     0 < max_app /\ no_Mat_decs ds /\ install_config_rel (ec:(C)install_config) co cc
     ==> ~(flat_semantics ec (ffi:(FFI)ffi_state) ds = Fail)
     ==> clos_semantics ffi max_app FEMPTY co cc (flat_to_clos_compile_prog ds) =
         flat_semantics ec ffi ds`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  F2CPAUX_HEAD_X_ASSUM "install_config_rel"
    (STRIP_ASSUME_TAC o REWRITE_RULE[install_config_rel_def]) THEN
  MP_TAC (ISPECL [`max_app:num`; `ds:flat_exp list`; `ec:(C)install_config`;
                  `pure_co (inc_compile_decs':flat_exp list ->
                              clos_exp list # (num#num#clos_exp) list) o
                   install_config_compile_oracle (ec:(C)install_config)`;
                  `pure_cc (insert_interp ## I)
                     (cc:C->(clos_exp)list#(num#num#clos_exp)list->
                         (((8)word)list#((64)word)list#C)option)`;
                  `ffi:(FFI)ffi_state`] compile_semantics') THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[install_config_rel'_def; inc_compile_decs_intro]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC (INST [`pure_co (inc_compile_decs':flat_exp list ->
                            clos_exp list # (num#num#clos_exp) list) o
                 install_config_compile_oracle (ec:(C)install_config)`,
                `co:num -> C # clos_prog`;
                `flat_to_clos_compile_decs ds`, `xs:clos_exp list`]
            semantics_attach_interpreter) THEN
  REWRITE_TAC[GSYM flat_to_clos_compile_prog_def; inc_compile_decs_intro] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[o_THM; pure_co_def] THEN GEN_TAC THEN
    SPEC_TAC(`install_config_compile_oracle (ec:(C)install_config) n`,
             `p:C # flat_exp list`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM; inc_compile_decs'_def; SND];
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The syntactic group (HOL4 lines 2206-2601): set_globals, esgc_free,      *)
(* contains_App_SOME, every_Fn_vs_NONE and no_mti over the flat_to_clos     *)
(* compile functions (proved by agent F2CSYN; F2CPAUX2_ names are its local *)
(* helpers).                                                                 *)
(* ------------------------------------------------------------------------- *)

(* HOL4 line 2206 *)
let contains_App_SOME_APPEND = prove
 (`!ma xs ys.
     contains_App_SOME ma (APPEND xs ys) <=>
     contains_App_SOME ma xs \/ contains_App_SOME ma ys`,
  ONCE_REWRITE_TAC[contains_App_SOME_EXISTS] THEN REWRITE_TAC[EXISTS_APPEND]);;

(* HOL4 line 2214: val props_defs (an ML list of closProps definitions) *)

(* HOL4 line 2219 *)
let EVERY_IMP_HD = prove
 (`!P (xs:A list). ALL P xs /\ ~NULL xs ==> P (HD xs)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN SIMP_TAC[ALL; NULL; HD]);;

(* HOL4 line 2225 *)
let flat_to_closProof_elist_globals_empty = prove
 (`!es. clos_elist_globals es = EMPTY_BAG <=>
        !e. MEM e es ==> clos_set_globals e = EMPTY_BAG`,
  MATCH_ACCEPT_TAC elglobals_EQ_EMPTY);;

(* the elements of a list of constants (HOL4: drule dest_Constants_IMP, then *)
(* imp_res_tac dest_Constant_IMP in each SmartCons theorem)                  *)
let F2CPAUX2_dest_Constant_props = prove
 (`!x c. flat_to_clos_dest_Constant x = SOME c
         ==> clos_set_globals x = EMPTY_BAG /\ clos_esgc_free x /\
             (!max_app. ~contains_App_SOME max_app [x]) /\
             every_Fn_vs_NONE [x] /\ no_mti x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dest_Constant_IMP] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[clos_set_globals_def; clos_op_gbag_def; clos_esgc_free_def;
                  contains_App_SOME_def; every_Fn_vs_NONE_def; no_mti_def; ALL;
                  BAG_UNION_EMPTY]);;

let F2CPAUX2_dest_Constants_props = prove
 (`!xs ys. dest_Constants xs = SOME ys
           ==> ALL (\x. clos_set_globals x = EMPTY_BAG /\ clos_esgc_free x /\
                        (!max_app. ~contains_App_SOME max_app [x]) /\
                        every_Fn_vs_NONE [x] /\ no_mti x) xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THEN GEN_TAC THEN
  REWRITE_TAC[dest_Constants_def] THEN
  REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[distinctness "option"]) THEN
  ASM_MESON_TAC[F2CPAUX2_dest_Constant_props]);;

(* HOL4 line 2232 *)
let set_globals_SmartCons = prove
 (`!t tag xs. clos_set_globals (SmartCons t tag xs) = clos_elist_globals xs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SmartCons_def] THEN COND_CASES_TAC THENL
   [FS[NULL_EQ; clos_op_gbag_def] THEN
    REWRITE_TAC[clos_set_globals_def; clos_op_gbag_def; BAG_UNION_EMPTY];
    ALL_TAC] THEN
  TOP_CASE_TAC THEN
  REWRITE_TAC[clos_set_globals_def; clos_op_gbag_def; BAG_UNION_EMPTY] THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP F2CPAUX2_dest_Constants_props) THEN
  CONV_TAC (RAND_CONV SYM_CONV) THEN
  REWRITE_TAC[GSYM ALL_MEM; elglobals_EQ_EMPTY] THEN MESON_TAC[]);;

(* HOL4 line 2242 *)
let esgc_free_SmartCons = prove
 (`!t tag xs. clos_esgc_free (SmartCons t tag xs) <=> ALL clos_esgc_free xs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SmartCons_def] THEN COND_CASES_TAC THENL
   [FS[NULL_EQ] THEN REWRITE_TAC[clos_esgc_free_def; ALL]; ALL_TAC] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[clos_esgc_free_def; ALL] THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP F2CPAUX2_dest_Constants_props) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[]);;

let F2CPAUX2_FINITE_BAG_flat_op_gbag = prove
 (`!op. FINITE_BAG (flat_op_gbag op)`,
  GEN_TAC THEN CASES_ON `op:flat_op` THEN
  REWRITE_TAC[flat_op_gbag_def; FINITE_BAG_THM]);;

(* HOL4 line 2252 *)
let flat_FINITE_BAG_set_globals = prove
 (`(!e. FINITE_BAG (flat_set_globals e)) /\
   (!e. FINITE_BAG (flat_elist_globals e))`,
  MATCH_MP_TAC flat_set_globals_ind THEN
  REWRITE_TAC[flat_set_globals_def; FINITE_BAG_UNION; FINITE_BAG_THM;
              F2CPAUX2_FINITE_BAG_flat_op_gbag] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;
let _ = cake_add_simps [flat_FINITE_BAG_set_globals];;

let F2CPAUX2_FINITE_BAG_clos_op_gbag = prove
 (`!op. FINITE_BAG (clos_op_gbag op)`,
  GEN_TAC THEN CASES_ON `op:clos_op` THEN
  REWRITE_TAC[clos_op_gbag_def; FINITE_BAG_THM] THEN
  CASES_ON `a:glob_op` THEN REWRITE_TAC[clos_op_gbag_def; FINITE_BAG_THM]);;

(* HOL4 line 2261 *)
let clos_FINITE_BAG_set_globals = prove
 (`(!e. FINITE_BAG (clos_set_globals e)) /\
   (!e. FINITE_BAG (clos_elist_globals e))`,
  MATCH_MP_TAC clos_set_globals_ind THEN
  REWRITE_TAC[clos_set_globals_def; FINITE_BAG_UNION; FINITE_BAG_THM;
              F2CPAUX2_FINITE_BAG_clos_op_gbag] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;
let _ = cake_add_simps [clos_FINITE_BAG_set_globals];;

(* HOL4 line 2272 *)
let BAG_IMAGE_FOLDR_lemma = prove
 (`!xs. BAG_IMAGE SUC (ITLIST BAG_UNION (MAP flat_set_globals xs) EMPTY_BAG) =
        ITLIST BAG_UNION (MAP (BAG_IMAGE SUC o flat_set_globals) xs) EMPTY_BAG /\
        FINITE_BAG (ITLIST BAG_UNION (MAP flat_set_globals xs) EMPTY_BAG)`,
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[MAP; ITLIST; BAG_IMAGE_EMPTY; FINITE_BAG_THM; FINITE_BAG_UNION;
               BAG_IMAGE_FINITE_UNION; o_THM; flat_FINITE_BAG_set_globals]);;

(* compile_op, compile_lit and HD (compile m [e]) for the induction proofs  *)
(* below (HOL4: Cases_on op, simp [compile_op_def, compile_arith_def], rpt  *)
(* CASE_TAC; compile_single_DEEP_INTRO)                                      *)
let F2CPAUX2_set_globals_compile_op = prove
 (`!t op xs. clos_set_globals (flat_to_clos_compile_op t op xs) =
             BAG_UNION (clos_elist_globals xs) (BAG_IMAGE SUC (flat_op_gbag op))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[flat_to_clos_compile_op_def; compile_arith_def; flat_to_clos_arg1_def;
              flat_to_clos_arg2_def] THEN
  EVERY_CASE_TAC THEN
  REWRITE_TAC[clos_set_globals_def; clos_op_gbag_def; flat_op_gbag_def;
              CopyByteStr_def; CopyByteAw8_def; BAG_UNION_EMPTY; BAG_IMAGE_EMPTY] THEN
  SIMP_TAC[BAG_IMAGE_FINITE_INSERT; FINITE_BAG_THM; BAG_IMAGE_EMPTY; ADD1] THEN
  REWRITE_TAC[BAG_UNION_INSERT; BAG_UNION_EMPTY] THEN
  TRY (MATCH_ACCEPT_TAC COMM_BAG_UNION));;

let F2CPAUX2_dest_Constant_compile_lit = prove
 (`!t l. ?c. flat_to_clos_dest_Constant (compile_lit t l) = SOME c`,
  REPEAT GEN_TAC THEN CASES_ON `l:lit` THEN REWRITE_TAC[compile_lit_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[flat_to_clos_dest_Constant_def] THEN
  MESON_TAC[]);;

let F2CPAUX2_compile_lit_props = prove
 (`!t l. clos_set_globals (compile_lit t l) = EMPTY_BAG /\
         clos_esgc_free (compile_lit t l) /\
         (!max_app. ~contains_App_SOME max_app [compile_lit t l]) /\
         every_Fn_vs_NONE [compile_lit t l] /\ no_mti (compile_lit t l)`,
  MESON_TAC[F2CPAUX2_dest_Constant_compile_lit; F2CPAUX2_dest_Constant_props]);;

let F2CPAUX2_HD_compile_props = prove
 (`!m e. clos_set_globals (HD (flat_to_clos_compile m [e])) =
         clos_elist_globals (flat_to_clos_compile m [e]) /\
         (clos_esgc_free (HD (flat_to_clos_compile m [e])) <=>
          ALL clos_esgc_free (flat_to_clos_compile m [e])) /\
         (no_mti (HD (flat_to_clos_compile m [e])) <=>
          ALL no_mti (flat_to_clos_compile m [e]))`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC (SYM (SPECL [`m:(mlstring option)list`; `e:flat_exp`] HD_compile)) THEN
  REWRITE_TAC[HD; clos_set_globals_def; BAG_UNION_EMPTY; ALL]);;

(* the function bodies of a Letrec (HOL4: FOLDR_CONG, MAP_CONG) *)
let F2CPAUX2_set_globals_MAP = prove
 (`!(funs:(mlstring # mlstring # flat_exp)list) h.
     (!p. MEM p funs
          ==> clos_set_globals (h p) = BAG_IMAGE SUC (flat_set_globals (SND (SND p))))
     ==> clos_elist_globals (MAP h funs) =
         BAG_IMAGE SUC (flat_elist_globals (MAP (SND o SND) funs))`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; MEM; clos_set_globals_def; flat_set_globals_def; BAG_IMAGE_EMPTY] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[BAG_IMAGE_FINITE_UNION; flat_FINITE_BAG_set_globals; o_THM]);;

(* the start of each case of the compile_ind proofs: the induction          *)
(* hypotheses and the no_Mat assumption simplified, compile unfolded         *)
let F2CPAUX2_SG_PRE_TAC : tactic =
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[ALL; no_Mat_def; EVERY_REVERSE; flat_set_globals_def;
                               BAG_UNION_EMPTY; elist_globals_REVERSE]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[flat_to_clos_compile_def] THEN CONV_TAC (TOP_DEPTH_CONV let_CONV);;

let F2CPAUX2_SG_THMS =
  [clos_set_globals_def; flat_set_globals_def; BAG_UNION_EMPTY; BAG_IMAGE_EMPTY;
   F2CPAUX2_HD_compile_props; set_globals_SmartCons; F2CPAUX2_set_globals_compile_op;
   clos_elist_globals_append; elist_globals_REVERSE; BAG_IMAGE_FINITE_UNION;
   FINITE_BAG_UNION; flat_FINITE_BAG_set_globals; F2CPAUX2_compile_lit_props;
   F2CPAUX2_FINITE_BAG_flat_op_gbag; flat_op_gbag_def];;

let F2CPAUX2_is_dest_nop th =
  try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "dest_nop"
  with Failure _ -> false;;

let F2CPAUX2_is_dest_pat th =
  try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "dest_pat"
  with Failure _ -> false;;

(* HOL4 line 2281 *)
let compile_set_globals = prove
 (`!m e. ALL no_Mat e
         ==> clos_elist_globals (flat_to_clos_compile m e) =
             BAG_IMAGE SUC (flat_elist_globals e)`,
  MATCH_MP_TAC flat_to_clos_compile_ind THEN REPEAT CONJ_TAC THEN
  F2CPAUX2_SG_PRE_TAC THEN ASM_SIMP_TAC F2CPAUX2_SG_THMS THENL
   [(* App: dest_nop *)
    TOP_CASE_TAC THENL
     [ASM_SIMP_TAC F2CPAUX2_SG_THMS;
      FIRST_ASSUM (DISJ_CASES_THEN (X_CHOOSE_THEN `tt:tra` STRIP_ASSUME_TAC) o
                   REWRITE_RULE[dest_nop_thm] o check F2CPAUX2_is_dest_nop) THEN
      RVEQ_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE[ALL; no_Mat_def]) THEN
      ASM_SIMP_TAC F2CPAUX2_SG_THMS];
    (* Let *)
    MATCH_ACCEPT_TAC COMM_BAG_UNION;
    (* Handle: dest_pat *)
    TOP_CASE_TAC THENL
     [MP_TAC (SPEC `pes:(flat_pat # flat_exp) list` dest_pat_from_case) THEN
      ASM_REWRITE_TAC[distinctness "option"];
      TOP_CASE_TAC THEN
      FIRST_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[dest_pat_thm] o
                   check F2CPAUX2_is_dest_pat) THEN
      RVEQ_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE[ALL; MAP; no_Mat_def]) THEN
      RULE_ASSUM_TAC (CAKE_SIMP_RULE []) THEN
      ASM_SIMP_TAC (MAP :: SND :: F2CPAUX2_SG_THMS)];
    (* Letrec *)
    AP_TERM_TAC THEN REWRITE_TAC[GSYM MAP_o] THEN
    MATCH_MP_TAC F2CPAUX2_set_globals_MAP THEN
    REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN CASE_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[F2CPAUX2_HD_compile_props] THEN
    SUBGOAL_THEN `no_Mat p2` ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o CONJUNCT1 o check (is_conj o concl)) THEN
      REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; EXISTS_PAIR_THM; o_THM; SND] THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]]]);;

(* HOL4 line 2344 *)
let compile_eq_set_globals = prove
 (`!m exps exps'.
     flat_to_clos_compile m exps = exps' /\ ALL no_Mat exps
     ==> clos_elist_globals exps' = BAG_IMAGE SUC (flat_elist_globals exps)`,
  MESON_TAC[compile_set_globals]);;

(* HOL4 line 2352 *)
let compile_decs_set_globals = prove
 (`!decs. no_Mat_decs decs
          ==> clos_elist_globals (flat_to_clos_compile_decs decs) =
              BAG_IMAGE SUC (flat_elist_globals decs)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[flat_to_clos_compile_decs_def; no_Mat_decs_def; clos_set_globals_def;
              flat_set_globals_def; BAG_IMAGE_EMPTY; clos_elist_globals_append] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[compile_set_globals; ALL; BAG_IMAGE_FINITE_UNION;
               flat_FINITE_BAG_set_globals; flat_set_globals_def; BAG_UNION_EMPTY]);;

(* HOL4: EVAL of set_globals clos_interpreter *)
let F2CPAUX2_set_globals_clos_interpreter = prove
 (`clos_set_globals clos_interpreter = EMPTY_BAG`,
  REWRITE_TAC[clos_interpreter_def; clos_interpreter_body_def; clos_interp_el_def;
              clos_interp_rev_def; clos_set_globals_def;
              clos_op_gbag_def; BAG_UNION_EMPTY; MAP; SND]);;

let F2CPAUX2_set_globals_compile_init = prove
 (`!b. clos_set_globals (compile_init b) = BAG_INSERT 0 EMPTY_BAG`,
  GEN_TAC THEN REWRITE_TAC[compile_init_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[clos_set_globals_def; clos_op_gbag_def; BAG_UNION_EMPTY;
              F2CPAUX2_set_globals_clos_interpreter]);;

(* HOL4 line 2364 *)
let compile_prog_set_globals = prove
 (`!decs. no_Mat_decs decs
          ==> clos_elist_globals (flat_to_clos_compile_prog decs) =
              BAG_UNION (BAG_INSERT 0 EMPTY_BAG)
                (BAG_IMAGE SUC (flat_elist_globals decs))`,
  SIMP_TAC[flat_to_clos_compile_prog_def; attach_interpreter_def; clos_set_globals_def;
           F2CPAUX2_set_globals_compile_init; compile_decs_set_globals]);;

(* the function bodies of a compiled Letrec *)
let F2CPAUX2_set_globals_Letrec = prove
 (CASE_TERM
  `!(funs:(mlstring # mlstring # flat_exp)list) new_m.
     ALL no_Mat (MAP (SND o SND) funs)
     ==> clos_elist_globals
           (MAP SND
              (MAP (\p. match p with
                          (f,v,x) ->
                            (1, HD (flat_to_clos_compile (CONS (SOME v) new_m) [x])))
                   funs)) =
         BAG_IMAGE SUC (flat_elist_globals (MAP (SND o SND) funs))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM MAP_o] THEN
  MATCH_MP_TAC F2CPAUX2_set_globals_MAP THEN
  REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN CASE_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[F2CPAUX2_HD_compile_props] THEN
  SUBGOAL_THEN `no_Mat p2` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL no_Mat (MAP (SND o SND) (funs:(mlstring # mlstring # flat_exp)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; EXISTS_PAIR_THM; o_THM; SND] THEN
    ASM_MESON_TAC[];
    ASM_SIMP_TAC[compile_set_globals; ALL; flat_set_globals_def; BAG_UNION_EMPTY]]);;

let F2CPAUX2_esgc_free_compile_op = prove
 (`!t op xs. ALL clos_esgc_free xs ==> clos_esgc_free (flat_to_clos_compile_op t op xs)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[flat_to_clos_compile_op_def; compile_arith_def; flat_to_clos_arg1_def;
              flat_to_clos_arg2_def] THEN
  EVERY_CASE_TAC THEN
  REWRITE_TAC[clos_esgc_free_def; CopyByteStr_def; CopyByteAw8_def; ALL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let F2CPAUX2_ESGC_PRE_TAC : tactic =
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[ALL; no_Mat_def; flat_esgc_free_def; EVERY_REVERSE]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[flat_to_clos_compile_def] THEN CONV_TAC (TOP_DEPTH_CONV let_CONV);;

let F2CPAUX2_ESGC_THMS =
  [ALL; clos_esgc_free_def; F2CPAUX2_HD_compile_props; esgc_free_SmartCons;
   F2CPAUX2_esgc_free_compile_op; ALL_APPEND; EVERY_REVERSE; F2CPAUX2_compile_lit_props;
   compile_set_globals; flat_set_globals_def; BAG_IMAGE_EMPTY; BAG_UNION_EMPTY];;

(* HOL4 line 2374 *)
let flat_to_closProof_compile_esgc_free = prove
 (`!m e. ALL flat_esgc_free e /\ ALL no_Mat e
         ==> ALL clos_esgc_free (flat_to_clos_compile m e)`,
  MATCH_MP_TAC flat_to_clos_compile_ind THEN REPEAT CONJ_TAC THEN
  F2CPAUX2_ESGC_PRE_TAC THEN ASM_SIMP_TAC F2CPAUX2_ESGC_THMS THENL
   [(* App: dest_nop *)
    TOP_CASE_TAC THENL
     [ASM_SIMP_TAC F2CPAUX2_ESGC_THMS;
      FIRST_ASSUM (DISJ_CASES_THEN (X_CHOOSE_THEN `tt:tra` STRIP_ASSUME_TAC) o
                   REWRITE_RULE[dest_nop_thm] o check F2CPAUX2_is_dest_nop) THEN
      RVEQ_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE[ALL; no_Mat_def; flat_esgc_free_def]) THEN
      ASM_SIMP_TAC F2CPAUX2_ESGC_THMS];
    (* Handle: dest_pat *)
    TOP_CASE_TAC THENL
     [MP_TAC (SPEC `pes:(flat_pat # flat_exp) list` dest_pat_from_case) THEN
      ASM_REWRITE_TAC[distinctness "option"];
      TOP_CASE_TAC THEN
      FIRST_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[dest_pat_thm] o
                   check F2CPAUX2_is_dest_pat) THEN
      RVEQ_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE[ALL; MAP; no_Mat_def]) THEN
      RULE_ASSUM_TAC (CAKE_SIMP_RULE []) THEN
      ASM_SIMP_TAC (MAP :: SND :: F2CPAUX2_ESGC_THMS)];
    (* Letrec *)
    ASM_SIMP_TAC[F2CPAUX2_set_globals_Letrec; BAG_IMAGE_EMPTY]]);;

(* HOL4 line 2422 *)
let flat_to_closProof_compile_decs_esgc_free = prove
 (`!decs. ALL flat_esgc_free decs /\ no_Mat_decs decs
          ==> ALL clos_esgc_free (flat_to_clos_compile_decs decs)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[flat_to_clos_compile_decs_def; no_Mat_decs_def; ALL; ALL_APPEND] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[flat_to_closProof_compile_esgc_free; ALL]);;

(* HOL4: EVAL_TAC on compile_init *)
let F2CPAUX2_esgc_free_compile_init = prove
 (`!b. clos_esgc_free (compile_init b)`,
  GEN_TAC THEN REWRITE_TAC[compile_init_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[clos_esgc_free_def; ALL; F2CPAUX2_set_globals_clos_interpreter]);;

(* HOL4 line 2434 *)
let flat_to_closProof_compile_prog_esgc_free = prove
 (`!decs. ALL flat_esgc_free decs /\ no_Mat_decs decs
          ==> ALL clos_esgc_free (flat_to_clos_compile_prog decs)`,
  SIMP_TAC[flat_to_clos_compile_prog_def; attach_interpreter_def; ALL;
           F2CPAUX2_esgc_free_compile_init; flat_to_closProof_compile_decs_esgc_free]);;

(* HOL4 line 2445 *)
let contains_App_SOME_SmartCons = prove
 (`!max_app t tag xs.
     contains_App_SOME max_app [SmartCons t tag xs] <=> contains_App_SOME max_app xs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SmartCons_def] THEN COND_CASES_TAC THENL
   [FS[NULL_EQ] THEN REWRITE_TAC[contains_App_SOME_def]; ALL_TAC] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[contains_App_SOME_def] THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP F2CPAUX2_dest_Constants_props) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[contains_App_SOME_EXISTS] THEN REWRITE_TAC[GSYM EX_MEM] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 2460 *)
let every_Fn_vs_NONE_SmartCons = prove
 (`!t tag xs. every_Fn_vs_NONE [SmartCons t tag xs] <=> every_Fn_vs_NONE xs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SmartCons_def] THEN COND_CASES_TAC THENL
   [FS[NULL_EQ] THEN REWRITE_TAC[every_Fn_vs_NONE_def]; ALL_TAC] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[every_Fn_vs_NONE_def] THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP F2CPAUX2_dest_Constants_props) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 2472 *)
let no_mti_SmartCons = prove
 (`!t tag xs. no_mti (SmartCons t tag xs) <=> ALL no_mti xs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SmartCons_def] THEN COND_CASES_TAC THENL
   [FS[NULL_EQ] THEN REWRITE_TAC[no_mti_def; ALL]; ALL_TAC] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[no_mti_def; ALL] THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP F2CPAUX2_dest_Constants_props) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[]);;

(* the closLang operations of compile_op (HOL4: Cases_on op, rpt CASE_TAC) *)
let F2CPAUX2_contains_App_SOME_Op = prove
 (`!max_app t op xs.
     0 < max_app
     ==> (contains_App_SOME max_app [clos_Op t op xs] <=> contains_App_SOME max_app xs)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CASES_ON `op:clos_op` THEN
  REWRITE_TAC[contains_App_SOME_def] THEN
  CASES_ON `a:thunk_op` THEN REWRITE_TAC[contains_App_SOME_def] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n < 1)`]);;

let F2CPAUX2_syntactic_compile_op = prove
 (`!max_app t op xs.
     (0 < max_app /\ ~contains_App_SOME max_app xs
      ==> ~contains_App_SOME max_app [flat_to_clos_compile_op t op xs]) /\
     (ALL no_mti xs ==> no_mti (flat_to_clos_compile_op t op xs)) /\
     (every_Fn_vs_NONE xs ==> every_Fn_vs_NONE [flat_to_clos_compile_op t op xs])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[flat_to_clos_compile_op_def; compile_arith_def; flat_to_clos_arg1_def;
              flat_to_clos_arg2_def] THEN
  EVERY_CASE_TAC THEN REPEAT CONJ_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[CopyByteStr_def; CopyByteAw8_def] THEN
  ASM_SIMP_TAC[F2CPAUX2_contains_App_SOME_Op; contains_App_SOME_def; no_mti_def;
               every_Fn_vs_NONE_def; ALL; LENGTH; GSYM ONE; IS_SOME_DEF; IS_NONE_DEF;
               ARITH_RULE `0 < n ==> ~(n < 1)`] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[contains_App_SOME_def; ALL; every_Fn_vs_NONE_def;
                               DE_MORGAN_THM]) THEN
  ASM_REWRITE_TAC[]);;

let F2CPAUX2_SYN_PRE_TAC : tactic =
  REPEAT GEN_TAC THEN TRY (DISCH_THEN STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[flat_to_clos_compile_def] THEN CONV_TAC (TOP_DEPTH_CONV let_CONV);;

let F2CPAUX2_SYN_THMS =
  [contains_App_SOME_def; no_mti_def; every_Fn_vs_NONE_def; ALL; HD_compile;
   F2CPAUX2_HD_compile_props; contains_App_SOME_APPEND; ALL_APPEND;
   every_Fn_vs_NONE_APPEND; contains_App_SOME_SmartCons; no_mti_SmartCons;
   every_Fn_vs_NONE_SmartCons; F2CPAUX2_compile_lit_props;
   F2CPAUX2_syntactic_compile_op; IS_NONE_DEF; IS_SOME_DEF];;

(* HOL4 line 2482 *)
let compile_syntactic_props = prove
 (`!max_app. 0 < max_app
     ==> !m e. ~contains_App_SOME max_app (flat_to_clos_compile m e) /\
               ALL no_mti (flat_to_clos_compile m e) /\
               every_Fn_vs_NONE (flat_to_clos_compile m e)`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC flat_to_clos_compile_ind THEN REPEAT CONJ_TAC THEN
  F2CPAUX2_SYN_PRE_TAC THEN ASM_SIMP_TAC F2CPAUX2_SYN_THMS THENL
   [(* App: dest_nop *)
    TOP_CASE_TAC THEN ASM_SIMP_TAC F2CPAUX2_SYN_THMS;
    (* Handle: dest_pat *)
    TOP_CASE_TAC THENL
     [ASM_SIMP_TAC F2CPAUX2_SYN_THMS;
      TOP_CASE_TAC THEN RULE_ASSUM_TAC (CAKE_SIMP_RULE []) THEN
      ASM_SIMP_TAC F2CPAUX2_SYN_THMS];
    (* Letrec *)
    ONCE_REWRITE_TAC[contains_App_SOME_EXISTS; every_Fn_vs_NONE_EVERY] THEN
    REWRITE_TAC[GSYM MAP_o; NOT_EX; ALL_MAP] THEN
    REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[HD_compile; F2CPAUX2_HD_compile_props; FST; SND] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[]]);;

(* HOL4 line 2519 *)
let compile_decs_syntactic_props = prove
 (`!decs max_app.
     ALL no_mti (flat_to_clos_compile_decs decs) /\
     every_Fn_vs_NONE (flat_to_clos_compile_decs decs) /\
     (0 < max_app ==> ~contains_App_SOME max_app (flat_to_clos_compile_decs decs))`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[flat_to_clos_compile_decs_def; ALL; every_Fn_vs_NONE_def;
              contains_App_SOME_def; ALL_APPEND; every_Fn_vs_NONE_APPEND;
              contains_App_SOME_APPEND; DE_MORGAN_THM] THEN
  MP_TAC (REWRITE_RULE[ARITH_RULE `0 < 1`] (SPEC `1` compile_syntactic_props)) THEN
  ASM_SIMP_TAC[compile_syntactic_props]);;

(* HOL4: EVAL_TAC on compile_init *)
let F2CPAUX2_INTERP_THMS =
  [compile_init_def; clos_interpreter_def; clos_interpreter_body_def;
   clos_interp_el_def; clos_interp_rev_def];;

(* HOL4 line 2531 *)
let contains_App_SOME_compile_init = prove
 (`!max_app b. 0 < max_app ==> ~contains_App_SOME max_app [compile_init b]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC F2CPAUX2_INTERP_THMS THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[F2CPAUX2_contains_App_SOME_Op; contains_App_SOME_def; LENGTH; MAP; SND;
               IS_SOME_DEF; ARITH_RULE `0 < n ==> ~(n < SUC 0)`]);;

(* HOL4 line 2537 *)
let no_mti_compile_init = prove
 (`!b. no_mti (compile_init b)`,
  GEN_TAC THEN REWRITE_TAC F2CPAUX2_INTERP_THMS THEN COND_CASES_TAC THEN
  REWRITE_TAC[no_mti_def; ALL; LENGTH; GSYM ONE; FST; SND]);;

(* HOL4 line 2543 *)
let every_Fn_vs_NONE_compile_init = prove
 (`!b. every_Fn_vs_NONE [compile_init b]`,
  GEN_TAC THEN REWRITE_TAC F2CPAUX2_INTERP_THMS THEN COND_CASES_TAC THEN
  REWRITE_TAC[every_Fn_vs_NONE_def; IS_NONE_DEF; MAP; SND]);;

(* HOL4 line 2549: rebinds contains_App_SOME_compile_init (as in HOL4); the *)
(* proof uses the first binding                                             *)
let contains_App_SOME_compile_init = prove
 (`!max_app b. 1 <= max_app ==> (contains_App_SOME max_app [compile_init b] <=> F)`,
  REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
  MESON_TAC[contains_App_SOME_compile_init]);;

(* HOL4: Cases_on compile_decs decs, then the CONS clauses *)
let F2CPAUX2_CONS_props = prove
 (`!ma x xs.
     (contains_App_SOME ma (CONS x xs) <=>
      contains_App_SOME ma [x] \/ contains_App_SOME ma xs) /\
     (every_Fn_vs_NONE (CONS x xs) <=> every_Fn_vs_NONE [x] /\ every_Fn_vs_NONE xs)`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`ma:num`; `[x:clos_exp]`; `xs:clos_exp list`] contains_App_SOME_APPEND) THEN
  MP_TAC (SPECL [`[x:clos_exp]`; `xs:clos_exp list`] every_Fn_vs_NONE_APPEND) THEN
  REWRITE_TAC[APPEND] THEN SIMP_TAC[]);;

(* HOL4 line 2556 *)
let compile_prog_syntactic_props = prove
 (`!decs max_app.
     ALL no_mti (flat_to_clos_compile_prog decs) /\
     every_Fn_vs_NONE (flat_to_clos_compile_prog decs) /\
     (0 < max_app ==> ~contains_App_SOME max_app (flat_to_clos_compile_prog decs))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[flat_to_clos_compile_prog_def; attach_interpreter_def] THEN
  ONCE_REWRITE_TAC[F2CPAUX2_CONS_props] THEN
  REWRITE_TAC[ALL; DE_MORGAN_THM; no_mti_compile_init; every_Fn_vs_NONE_compile_init;
              compile_decs_syntactic_props] THEN
  SIMP_TAC[compile_decs_syntactic_props] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[contains_App_SOME_compile_init; ARITH_RULE `0 < n ==> 1 <= n`]);;

(* HOL4 line 2570 *)
let FST_inc_compile_syntactic_props = prove
 (`!decs max_app.
     ALL no_mti (FST (inc_compile_decs decs)) /\
     every_Fn_vs_NONE (FST (inc_compile_decs decs)) /\
     (0 < max_app ==> ~contains_App_SOME max_app (FST (inc_compile_decs decs)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[inc_compile_decs_def] THEN
  CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FST] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP insert_interp_no_mti) THEN
    REWRITE_TAC[ALL_APPEND; compile_decs_syntactic_props];
    MATCH_MP_TAC every_Fn_vs_NONE_insert_interp THEN
    REWRITE_TAC[every_Fn_vs_NONE_APPEND; compile_decs_syntactic_props];
    DISCH_TAC THEN MATCH_MP_TAC contains_App_SOME_insert_interp THEN
    ASM_SIMP_TAC[contains_App_SOME_APPEND; compile_decs_syntactic_props;
                 ARITH_RULE `0 < n ==> 1 <= n`]]);;

(* HOL4 line 2584 *)
let FST_inc_compile_set_globals = prove
 (`!decs. no_Mat_decs decs
          ==> clos_elist_globals (FST (inc_compile_decs decs)) =
              BAG_IMAGE SUC (flat_elist_globals decs)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inc_compile_decs_def] THEN
  CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; elist_globals_insert_interp; clos_elist_globals_append] THEN
  ASM_SIMP_TAC[compile_decs_set_globals; no_Mat_decs_def; no_Mat_def; ALL;
               flat_set_globals_def; BAG_UNION_EMPTY; BAG_IMAGE_EMPTY]);;

(* HOL4 line 2594 *)
let FST_inc_compile_esgc_free = prove
 (`!decs. ALL flat_esgc_free decs /\ no_Mat_decs decs
          ==> ALL clos_esgc_free (FST (inc_compile_decs decs))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inc_compile_decs_def] THEN
  CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; insert_interp_esgc_free; ALL_APPEND] THEN
  ASM_SIMP_TAC[flat_to_closProof_compile_decs_esgc_free; no_Mat_decs_def; no_Mat_def;
               flat_esgc_free_def; ALL]);;
