(* ========================================================================= *)
(* candle_prover_inv: port of HOL4 candle/prover/candle_prover_invScript.sml *)
(* (CakeML v3479).  Definitions of invariants that are to be maintained      *)
(* during evaluate of Candle prover.                                         *)
(* ========================================================================= *)

needs "candle/prover/candle_kernel_vals.ml";;
needs "candle/prover/ast_extras.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "candle/prover/perms.ml";;
needs "candle/standard/monadic/holKernelProof.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "misc/misc.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "hol4/sptree.ml";;
needs "candle/prover/candle_kernelProg.ml";;
needs "candle/standard/ml_kernel/ml_hol_kernel_funsProg.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Expressions are safe if they do not construct anything with a name from  *)
(* the kernel type constructors (i.e. one of TYPE, TERM, THM), and if they   *)
(* do not write to the kernel ffi channel.                                   *)
(*                                                                           *)
(* We can't keep track on whether or not the constructors have been brought  *)
(* into scope (i.e., by 'open Kernel;'), so we just forbid their short names *)
(* everywhere.                                                               *)
(* ------------------------------------------------------------------------- *)

let safe_exp_def = cake_def
  `safe_exp =
     every_exp (\x. match x with
                      Con opt xs -> (!id. opt = SOME id ==> ~(id_to_n id IN kernel_ctors))
                    | App op xs -> ~(op = FFI kernel_ffi)
                    | _ -> T)`;;

(* HOL4: the clauses of safe_exp, by simplification with safe_exp_def *)
let safe_exp_simps = prove
 (`(!e. safe_exp (Raise e) <=> safe_exp e) /\
   (!e pes. safe_exp (Handle e pes) <=>
      safe_exp e /\ ALL safe_exp (MAP SND pes)) /\
   (!lit. safe_exp (Lit lit)) /\
   (!opt xs. safe_exp (Con opt xs) <=>
      (!id. opt = SOME id ==> ~(id_to_n id IN kernel_ctors)) /\ ALL safe_exp xs) /\
   (!n. safe_exp (Var n)) /\
   (!n x. safe_exp (Fun n x) <=> safe_exp x) /\
   (!op xs. safe_exp (App op xs) <=> ~(op = FFI kernel_ffi) /\ ALL safe_exp xs) /\
   (!lop x y. safe_exp (Log lop x y) <=> safe_exp x /\ safe_exp y) /\
   (!x y z. safe_exp (If x y z) <=> safe_exp x /\ safe_exp y /\ safe_exp z) /\
   (!e pes. safe_exp (Mat e pes) <=> safe_exp e /\ ALL safe_exp (MAP SND pes)) /\
   (!opt x y. safe_exp (Let opt x y) <=> safe_exp x /\ safe_exp y) /\
   (!f x. safe_exp (Letrec f x) <=> safe_exp x /\ ALL safe_exp (MAP (SND o SND) f)) /\
   (!e t. safe_exp (Tannot e t) <=> safe_exp e) /\
   (!e l. safe_exp (Lannot e l) <=> safe_exp e)`,
  REWRITE_TAC[safe_exp_def] THEN SIMP[ast_extras_every_exp_def]);;
let _ = cake_add_simps [safe_exp_simps];;

let safe_dec_def = cake_def
  `safe_dec =
     every_dec (\d. match d with
                      Dlet locs pat x -> safe_exp x
                    | Dletrec locs funs -> ALL safe_exp (MAP (SND o SND) funs)
                    | _ -> T)`;;

(* HOL4: the clauses of safe_dec, by simplification with safe_dec_def *)
let safe_dec_simps = prove
 (`(!l p x. safe_dec (Dlet l p x) <=> safe_exp x) /\
   (!l f. safe_dec (Dletrec l f) <=> ALL safe_exp (MAP (SND o SND) f)) /\
   (!l tds. safe_dec (Dtype l tds)) /\
   (!l ns n t. safe_dec (Dtabbrev l ns n t)) /\
   (!l n ts. safe_dec (Dexn l n ts)) /\
   (!mn ds. safe_dec (Dmod mn ds) <=> ALL safe_dec ds) /\
   (!ds1 ds2. safe_dec (Dlocal ds1 ds2) <=> ALL safe_dec ds1 /\ ALL safe_dec ds2) /\
   (!n. safe_dec (Denv n))`,
  REWRITE_TAC[safe_dec_def] THEN SIMP[every_dec_def]);;
let _ = cake_add_simps [safe_dec_simps];;

(* HOL4: Inductive v_ok (the relations kernel_vals, v_ok and env_ok), with *)
(* the rules v_ok_Inferred .. v_ok_Env and env_ok                           *)
let candle_v_ok_rules,candle_v_ok_ind,candle_v_ok_cases,candle_v_ok_strongind =
  cake_inductive
  `(!ctxt v.
      candle_inferred ctxt v ==>
        candle_kernel_vals ctxt v) /\
   (!ctxt f v g.
      candle_kernel_vals ctxt f /\
      candle_v_ok ctxt v /\
      do_partial_app f v = SOME g ==>
        candle_kernel_vals ctxt g) /\
   (!ctxt v.
      candle_kernel_vals ctxt v ==>
        candle_v_ok ctxt v) /\
   (!ctxt opt vs.
      ALL (candle_v_ok ctxt) vs /\
      (!tag x. opt = SOME (TypeStamp tag x) ==> ~(x IN kernel_types)) ==>
        candle_v_ok ctxt (Conv opt vs)) /\
   (!ctxt env n x.
      candle_env_ok ctxt env /\
      safe_exp x ==>
        candle_v_ok ctxt (Closure env n x)) /\
   (!ctxt env f n.
      candle_env_ok ctxt env /\
      ALL safe_exp (MAP (SND o SND) f) ==>
        candle_v_ok ctxt (Recclosure env f n)) /\
   (!ctxt vs.
      ALL (candle_v_ok ctxt) vs ==>
        candle_v_ok ctxt (Vectorv vs)) /\
   (!ctxt lit.
      candle_v_ok ctxt (Litv lit)) /\
   (!ctxt loc b.
      ~(loc IN kernel_locs) ==>
        candle_v_ok ctxt (Loc b loc)) /\
   (!ctxt env ns.
      candle_env_ok ctxt env ==>
        candle_v_ok ctxt (Env env ns)) /\
   (!(ctxt:update list) env.
      (!id len tag tn.
         nsLookup (sem_env_c env) id = SOME (len,TypeStamp tag tn) /\
         tn IN kernel_types ==>
           id_to_n id IN kernel_ctors) /\
      (!n v. nsLookup (sem_env_v env) n = SOME v ==> candle_v_ok ctxt v) ==>
        candle_env_ok ctxt env)`;;

let candle_v_ok_Inferred = el 0 (CONJUNCTS candle_v_ok_rules);;
let candle_v_ok_PartialApp = el 1 (CONJUNCTS candle_v_ok_rules);;
let candle_v_ok_KernelVals = el 2 (CONJUNCTS candle_v_ok_rules);;
let candle_v_ok_Conv = el 3 (CONJUNCTS candle_v_ok_rules);;
let candle_v_ok_Closure = el 4 (CONJUNCTS candle_v_ok_rules);;
let candle_v_ok_Recclosure = el 5 (CONJUNCTS candle_v_ok_rules);;
let candle_v_ok_Vectorv = el 6 (CONJUNCTS candle_v_ok_rules);;
let candle_v_ok_Lit = el 7 (CONJUNCTS candle_v_ok_rules);;
let candle_v_ok_Loc = el 8 (CONJUNCTS candle_v_ok_rules);;
let candle_v_ok_Env = el 9 (CONJUNCTS candle_v_ok_rules);;
let env_ok = el 10 (CONJUNCTS candle_v_ok_rules);;

(* do_partial_app gives a closure, from a closure of a Fun *)
let CAN2AAUX_do_partial_app_SOME = prove
 (`do_partial_app f v = SOME g <=>
   ?env n n' e. f = Closure env n (Fun n' e) /\
                g = Closure (sem_env_v_fupd (combin_K (nsBind n v (sem_env_v env))) env) n' e`,
  REWRITE_TAC[do_partial_app_def] THEN
  CASES_ON `f:v` THEN SIMP[] THEN
  MATCH_GOALSUB_RENAME_TAC "exp_CASE xx" THEN CASES_ON `xx:exp` THEN SIMP[] THEN
  MESON_TAC[]);;

let kernel_vals_Vectorv = prove
 (`~candle_kernel_vals ctxt (Vectorv vs)`,
  ONCE_REWRITE_TAC[candle_v_ok_cases] THEN
  REWRITE_TAC[inferred_Vectorv; CAN2AAUX_do_partial_app_SOME] THEN
  MESON_TAC[distinctness "v"]);;
let _ = cake_add_simps [kernel_vals_Vectorv];;

let kernel_vals_Env = prove
 (`~candle_kernel_vals ctxt1 (Env env id)`,
  ONCE_REWRITE_TAC[candle_v_ok_cases] THEN
  REWRITE_TAC[inferred_Env; CAN2AAUX_do_partial_app_SOME] THEN
  MESON_TAC[distinctness "v"]);;
let _ = cake_add_simps [kernel_vals_Env];;

let kernel_vals_Conv = prove
 (`candle_kernel_vals ctxt (Conv (SOME stamp) vs) ==>
   ?tag m. stamp = TypeStamp tag m /\ m IN kernel_types`,
  ONCE_REWRITE_TAC[candle_v_ok_cases] THEN
  REWRITE_TAC[CAN2AAUX_do_partial_app_SOME] THEN
  MESON_TAC[inferred_Conv; distinctness "v"]);;

let kernel_vals_Conv_NONE = prove
 (`~candle_kernel_vals ctxt (Conv NONE vs)`,
  ONCE_REWRITE_TAC[candle_v_ok_cases] THEN
  REWRITE_TAC[inferred_Conv_NONE; CAN2AAUX_do_partial_app_SOME] THEN
  MESON_TAC[distinctness "v"]);;
let _ = cake_add_simps [kernel_vals_Conv_NONE];;

let kernel_vals_Loc = prove
 (`~candle_kernel_vals ctxt (Loc b loc)`,
  ONCE_REWRITE_TAC[candle_v_ok_cases] THEN
  REWRITE_TAC[inferred_Loc; CAN2AAUX_do_partial_app_SOME] THEN
  MESON_TAC[distinctness "v"]);;
let _ = cake_add_simps [kernel_vals_Loc];;

(* HOL4: v_ok_def, the cases of v_ok on each value constructor, by           *)
(* simplification with Once v_ok_cases                                       *)
let candle_v_ok_def =
  end_itlist CONJ
    (map (CAKE_SIMP_CONV [ONCE candle_v_ok_cases])
       [`candle_v_ok ctxt (Conv opt vs)`;
        `candle_v_ok ctxt (Closure env n x)`;
        `candle_v_ok ctxt (Recclosure env f n)`;
        `candle_v_ok ctxt (Vectorv vs)`;
        `candle_v_ok ctxt (Litv lit)`;
        `candle_v_ok ctxt (Loc b loc)`;
        `candle_v_ok ctxt (Env env ns)`]);;

let v_ok_div_exn_v = prove
 (`candle_v_ok ctxt div_exn_v`,
  RW[candle_v_ok_def; div_exn_v_def; div_stamp_def; distinctness "stamp"]);;
let _ = cake_add_simps [v_ok_div_exn_v];;

let v_ok_chr_exn_v = prove
 (`candle_v_ok ctxt chr_exn_v`,
  RW[candle_v_ok_def; chr_exn_v_def; chr_stamp_def; distinctness "stamp"]);;
let _ = cake_add_simps [v_ok_chr_exn_v];;

let v_ok_bind_exn_v = prove
 (`candle_v_ok ctxt bind_exn_v`,
  RW[candle_v_ok_def; bind_exn_v_def; bind_stamp_def; distinctness "stamp"]);;
let _ = cake_add_simps [v_ok_bind_exn_v];;

let v_ok_sub_exn_v = prove
 (`candle_v_ok ctxt sub_exn_v`,
  RW[candle_v_ok_def; sub_exn_v_def; subscript_stamp_def; distinctness "stamp"]);;
let _ = cake_add_simps [v_ok_sub_exn_v];;

(* HOL4: env_ok_def, by simplification with Once v_ok_cases *)
let candle_env_ok_def =
  CAKE_SIMP_CONV [ONCE candle_v_ok_cases] `candle_env_ok ctxt env`;;

(* HOL4: v_ok_ind for the predicates P, \_ _. T and \_ _. T *)
let candle_kernel_vals_ind =
  GEN_ALL (CAKE_SIMP_RULE []
    (ISPECL [`P:update list->v->bool`; `\(c:update list) (x:v). T`;
             `\(c:update list) (e:v sem_env). T`] candle_v_ok_ind));;

let candle_ref_ok_def = cake_def
  `(candle_ref_ok ctxt (Varray vs) <=> ALL (candle_v_ok ctxt) vs) /\
   (candle_ref_ok ctxt (Refv v) <=> candle_v_ok ctxt v) /\
   (candle_ref_ok ctxt (W8array (ws:byte list)) <=> T) /\
   (candle_ref_ok ctxt (Thunk m v) <=> candle_v_ok ctxt v)`;;

(* HOL4 LLOOKUP refs loc is oEL loc refs (misc) *)
let candle_kernel_loc_ok_def = cake_def
  `candle_kernel_loc_ok s loc refs <=>
     ?v. oEL loc refs = SOME (Refv v) /\
         (the_type_constants = Loc T loc ==>
            LIST_TYPE (PAIR_TYPE STRING_TYPE ml_NUM)
              (hol_refs_the_type_constants s) v) /\
         (the_term_constants = Loc T loc ==>
            LIST_TYPE (PAIR_TYPE STRING_TYPE TYPE_TYPE)
              (hol_refs_the_term_constants s) v) /\
         (the_axioms = Loc T loc ==>
            LIST_TYPE THM_TYPE (hol_refs_the_axioms s) v) /\
         (the_context = Loc T loc ==>
            LIST_TYPE UPDATE_TYPE (hol_refs_the_context s) v)`;;

let kernel_loc_ok_LENGTH = prove
 (`candle_kernel_loc_ok st loc refs ==> loc < LENGTH refs`,
  RW[candle_kernel_loc_ok_def] THEN GVS[oEL_EQ_EL]);;

let kernel_loc_ok_LUPDATE1 = prove
 (`candle_kernel_loc_ok st loc refs /\ ~(n = loc) ==>
   candle_kernel_loc_ok st loc (LUPDATE v n refs)`,
  RW[candle_kernel_loc_ok_def] THEN GVS[oEL_EQ_EL; EL_LUPDATE; LENGTH_LUPDATE] THEN
  ASM_MESON_TAC[]);;

let candle_eval_state_ok_def = cake_def
  `(candle_eval_state_ok NONE <=> T) /\
   (candle_eval_state_ok (SOME (EvalDecs s)) <=>
      (!v ds. eval_decs_state_decode_decs s v = SOME ds ==> ALL safe_dec ds)) /\
   (candle_eval_state_ok (SOME (EvalOracle s')) <=> F)`;;

let candle_state_ok_def = cake_def
  `candle_state_ok ctxt (s:(FFI)state) <=>
     (!n. n IN kernel_types ==> n < state_next_type_stamp s) /\
     ALL ok_event (ffi_state_io_events (state_ffi s)) /\
     candle_eval_state_ok (state_eval_state s) /\
     ?state.
       holKernelProof_STATE ctxt state /\
       (!loc. loc IN kernel_locs ==> candle_kernel_loc_ok state loc (state_refs s)) /\
       (!loc r. ~(loc IN kernel_locs) /\ oEL loc (state_refs s) = SOME r ==>
                candle_ref_ok ctxt r)`;;

let state_ok_dec_clock = prove
 (`candle_state_ok ctxt (dec_clock (s:(FFI)state)) <=> candle_state_ok ctxt s`,
  RW[candle_state_ok_def; dec_clock_def]);;

(* ------------------------------------------------------------------------- *)
(* Proving env_ok/v_ok/ref_ok/state_ok for things                            *)
(* ------------------------------------------------------------------------- *)

let env_ok_extend_dec_env = prove
 (`candle_env_ok ctxt env1 /\ candle_env_ok ctxt env2 ==>
   candle_env_ok ctxt (extend_dec_env env1 env2)`,
  RW[candle_env_ok_def; extend_dec_env_def; nsLookup_nsAppend_some] THEN
  ASM_MESON_TAC[]);;

let env_ok_write_cons = prove
 (`candle_env_ok ctxt env /\ (t IN kernel_types ==> nm IN kernel_ctors) ==>
   candle_env_ok ctxt (ml_write_cons nm (n,TypeStamp s t) env)`,
  SIMP[candle_env_ok_def; ml_write_cons_def] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  REPEAT GEN_TAC THEN QCASES_ON "id" THEN
  RW[nsLookup_nsBind_compute; id_to_n_def] THEN GVS[] THEN ASM_MESON_TAC[id_to_n_def]);;

let env_ok_write_Exn = prove
 (`candle_env_ok ctxt env ==>
   candle_env_ok ctxt (ml_write_cons nm (n,ExnStamp m) env)`,
  SIMP[candle_env_ok_def; ml_write_cons_def] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  REPEAT GEN_TAC THEN QCASES_ON "id" THEN
  RW[nsLookup_nsBind_compute; distinctness "stamp"] THEN ASM_MESON_TAC[]);;

let env_ok_write_mod = prove
 (`candle_env_ok ctxt env1 /\ candle_env_ok ctxt env2 ==>
   candle_env_ok ctxt (ml_write_mod mn env1 env2)`,
  RW[candle_env_ok_def; ml_write_mod_def; nsLookup_nsAppend_some; nsLookup_nsLift;
     case_eq "id"] THEN
  GVS[id_to_n_def] THEN ASM_MESON_TAC[id_to_n_def]);;

let env_ok_write = prove
 (`candle_env_ok ctxt env /\ candle_v_ok ctxt v ==>
   candle_env_ok ctxt (ml_write nm v env)`,
  SIMP[candle_env_ok_def; ml_write_def] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN QCASES_ON "n" THEN
  RW[nsLookup_nsBind_compute] THEN ASM_MESON_TAC[]);;

let env_ok_merge_env = prove
 (`candle_env_ok ctxt env1 /\ candle_env_ok ctxt env2 ==>
   candle_env_ok ctxt (merge_env env1 env2)`,
  SIMP[candle_env_ok_def; merge_env_def; nsLookup_nsAppend_some] THEN
  STRIP_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THEN RW[] THEN ASM_MESON_TAC[]);;

let env_ok_with = prove
 (`candle_env_ok ctxt (sem_env_c_fupd (combin_K (sem_env_c env)) env1) ==>
   candle_env_ok ctxt (sem_env_v_fupd (combin_K (sem_env_v env1)) env)`,
  RW[candle_env_ok_def] THEN ASM_MESON_TAC[]);;

let env_ok_with_nsBind = prove
 (`candle_v_ok ctxt v /\
   candle_env_ok ctxt (sem_env_c_fupd (combin_K (sem_env_c env)) env2) ==>
   candle_env_ok ctxt (sem_env_v_fupd (combin_K (nsBind n v (sem_env_v env2))) env)`,
  SIMP[candle_env_ok_def] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN QCASES_ON "n'" THEN
  RW[nsLookup_nsBind_compute] THEN ASM_MESON_TAC[]);;

(* HOL4 <| v := nsEmpty; c := nsEmpty |> *)
let env_ok_nsEmpty = prove
 (`candle_env_ok ctxt (sem_env_REC nsEmpty nsEmpty)`,
  RW[candle_env_ok_def]);;

let env_ok_empty_env = prove
 (`candle_env_ok ctxt empty_env`,
  RW[candle_env_ok_def; empty_env_def]);;

let env_ok_init_env = prove
 (`candle_env_ok ctxt ml_init_env`,
  RW[candle_env_ok_def; ml_init_env_def] THEN
  GVS[nsLookup_Bind_v_some; kernel_types_def; IN_INSERT; NOT_IN_EMPTY] THEN
  GVS[COND_CASE_EQ; option_INJ; PAIR_EQ; injectivity "stamp"; distinctness "stamp";
      option_DISTINCT]);;

(* a constructor value with a stamp outside kernel_types is not a kernel value *)
let CAN2AAUX_not_kernel_type_Conv = prove
 (`~(n IN kernel_types) ==> ~candle_kernel_vals ctxt (Conv (SOME (TypeStamp tag n)) vs)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o MATCH_MP kernel_vals_Conv) THEN
  ASM_REWRITE_TAC[injectivity "stamp"] THEN ASM_MESON_TAC[]);;

let v_ok_Cons = prove
 (`candle_v_ok ctxt (Conv (SOME (TypeStamp (implode "::") 1)) [x; y]) <=>
   candle_v_ok ctxt x /\ candle_v_ok ctxt y`,
  REWRITE_TAC[candle_v_ok_def] THEN
  SIMP[CAN2AAUX_not_kernel_type_Conv; kernel_types_def; IN_INSERT; NOT_IN_EMPTY; ALL;
       option_INJ; injectivity "stamp"] THEN
  MESON_TAC[ARITH_RULE `~(1 = 21) /\ ~(1 = 22) /\ ~(1 = 23)`]);;

let v_ok_Conv_NONE = prove
 (`candle_v_ok ctxt (Conv NONE ls) <=> ALL (candle_v_ok ctxt) ls`,
  RW[candle_v_ok_def; option_DISTINCT]);;

let NUM_v_ok = prove
 (`ml_NUM x v ==> candle_v_ok ctxt v`,
  RW[ml_NUM_def; ml_INT_def] THEN RW[candle_v_ok_def]);;

let BOOL_v_ok = prove
 (`ml_BOOL x v ==> candle_v_ok ctxt v`,
  RW[ml_BOOL_def; semanticPrimitives_Boolv_def] THEN
  SIMP[candle_v_ok_def; CAN2AAUX_not_kernel_type_Conv; bool_type_NOTIN_kernel_types; ALL;
       option_INJ; injectivity "stamp"] THEN
  MESON_TAC[bool_type_NOTIN_kernel_types]);;

let STRING_TYPE_v_ok = prove
 (`STRING_TYPE x v ==> candle_v_ok ctxt v`,
  RW[STRING_TYPE_def] THEN RW[candle_v_ok_def]);;

let PAIR_TYPE_v_ok = prove
 (`PAIR_TYPE (A:A->v->bool) (B:B->v->bool) p v /\
   (!v. A (FST p) v ==> candle_v_ok ctxt v) /\
   (!v. B (SND p) v ==> candle_v_ok ctxt v) ==>
   candle_v_ok ctxt v`,
  PAIR_CASES_ON `p:A#B` THEN RW[PAIR_TYPE_def] THEN
  MATCH_MP_TAC candle_v_ok_Conv THEN RW[ALL; option_DISTINCT]);;

let LIST_TYPE_v_ok = prove
 (`!(A:A->v->bool) ls v.
     LIST_TYPE A ls v /\ ALL (\x. !v. A x v ==> candle_v_ok ctxt v) ls ==>
     candle_v_ok ctxt v`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN RW[LIST_TYPE_def; ALL] THEN
  MATCH_MP_TAC candle_v_ok_Conv THEN
  RW[ALL; option_INJ; injectivity "stamp"; kernel_types_def; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Lemmas about v_ok and {TYPE,TERM,THM}_TYPE{,_HEAD}                        *)
(* ------------------------------------------------------------------------- *)

let TYPE_IMP_v_ok = prove
 (`holKernelProof_TYPE ctxt th /\ TYPE_TYPE th v ==> candle_v_ok ctxt v`,
  MESON_TAC[candle_v_ok_KernelVals; candle_v_ok_Inferred; candle_inferred_TYPE]);;

let TERM_IMP_v_ok = prove
 (`holKernelProof_TERM ctxt th /\ TERM_TYPE th v ==> candle_v_ok ctxt v`,
  MESON_TAC[candle_v_ok_KernelVals; candle_v_ok_Inferred; candle_inferred_TERM]);;

let THM_IMP_v_ok = prove
 (`holKernelProof_THM ctxt th /\ THM_TYPE th v ==> candle_v_ok ctxt v`,
  MESON_TAC[candle_v_ok_KernelVals; candle_v_ok_Inferred; candle_inferred_THM]);;

(* a v_ok constructor value with a kernel type stamp is inferred *)
let CAN2AAUX_v_ok_kernel_Conv = prove
 (`candle_v_ok ctxt (Conv (SOME (TypeStamp tag n)) vs) /\ n IN kernel_types ==>
   candle_inferred ctxt (Conv (SOME (TypeStamp tag n)) vs)`,
  REWRITE_TAC[candle_v_ok_def; option_INJ; injectivity "stamp"] THEN
  ONCE_REWRITE_TAC[candle_v_ok_cases] THEN
  REWRITE_TAC[CAN2AAUX_do_partial_app_SOME] THEN
  MESON_TAC[distinctness "v"]);;

let CAN2AAUX_kernel_types_IN = prove
 (can2aaux_stamps `type_stamp_n IN kernel_types /\ term_stamp_n IN kernel_types /\
                   thm_stamp_n IN kernel_types`,
  REWRITE_TAC[kernel_types_def; IN_INSERT]);;

(* v_ok and a HEAD predicate of the k-th kernel type: the cases of inferred *)
let CAN2AAUX_V_OK_HEAD_TAC head_def k =
  REWRITE_TAC[head_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM (fun th -> try
      MP_TAC (MATCH_MP CAN2AAUX_v_ok_kernel_Conv
                (CONJ th (el k (CONJUNCTS CAN2AAUX_kernel_types_IN))))
    with Failure _ -> failwith "CAN2AAUX_V_OK_HEAD_TAC") THEN
  ONCE_REWRITE_TAC[candle_inferred_cases] THEN
  REWRITE_TAC[Conv_NOT_IN_kernel_funs] THEN STRIP_TAC THENL
   [TRY (CASES_ON `ty:hol_type` THEN GVS[TYPE_TYPE_def] THEN NO_TAC);
    TRY (CASES_ON `tm:hol_term` THEN GVS[TERM_TYPE_def] THEN NO_TAC);
    TRY (CASES_ON `th:thm` THEN GVS[THM_TYPE_def] THEN NO_TAC)] THEN
  ASM_MESON_TAC[];;

let v_ok_THM_TYPE_HEAD = prove
 (`candle_v_ok ctxt v /\ THM_TYPE_HEAD v ==> ?th. THM_TYPE th v`,
  CAN2AAUX_V_OK_HEAD_TAC THM_TYPE_HEAD_def 2);;

let v_ok_TERM_TYPE_HEAD = prove
 (`candle_v_ok ctxt v /\ TERM_TYPE_HEAD v ==> ?tm. TERM_TYPE tm v`,
  CAN2AAUX_V_OK_HEAD_TAC TERM_TYPE_HEAD_def 1);;

let v_ok_TYPE_TYPE_HEAD = prove
 (`candle_v_ok ctxt v /\ TYPE_TYPE_HEAD v ==> ?ty. TYPE_TYPE ty v`,
  CAN2AAUX_V_OK_HEAD_TAC TYPE_TYPE_HEAD_def 0);;

(* HOL4 by complete induction on v_size v; here by induction on the list of *)
(* LIST_TYPE_HEAD                                                            *)
let v_ok_LIST_TYPE_HEAD = prove
 (`candle_v_ok ctxt v /\
   (!v. candle_v_ok ctxt v /\ A_HEAD v ==> ?a. (A:A->v->bool) a v) /\
   LIST_TYPE_HEAD A_HEAD v ==>
   ?tms. LIST_TYPE A tms v`,
  REWRITE_TAC[LIST_TYPE_HEAD_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!(l:1 list) w. candle_v_ok ctxt w /\ LIST_TYPE (combin_K A_HEAD) l w ==>
                               ?tms. LIST_TYPE (A:A->v->bool) tms w`
    (fun th -> ASM_MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LIST_TYPE_def; K_THM] THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC `[]:A list` THEN ASM_REWRITE_TAC[LIST_TYPE_def]; ALL_TAC] THEN
  FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th -> lhs (concl th) = `w:v`)) THEN
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[v_ok_Cons] o
                 check (fun th -> can (find_term ((=) `v2_2:v`)) (concl th) &&
                                  is_comb (concl th) &&
                                  fst (strip_comb (concl th)) = `candle_v_ok`)) THEN
  SUBGOAL_THEN `?tms. LIST_TYPE (A:A->v->bool) tms v2_2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?a. (A:A->v->bool) a v2_1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `CONS (a:A) tms` THEN REWRITE_TAC[LIST_TYPE_def] THEN ASM_MESON_TAC[]);;

let v_ok_LIST_TERM_TYPE_HEAD = prove
 (`candle_v_ok ctxt v /\ LIST_TYPE_HEAD TERM_TYPE_HEAD v ==>
   ?tms. LIST_TYPE TERM_TYPE tms v`,
  STRIP_TAC THEN MATCH_MP_TAC (GEN_ALL v_ok_LIST_TYPE_HEAD) THEN
  EXISTS_TAC `ctxt:update list` THEN EXISTS_TAC `TERM_TYPE_HEAD` THEN
  ASM_MESON_TAC[v_ok_TERM_TYPE_HEAD]);;

let v_ok_LIST_THM_TYPE_HEAD = prove
 (`candle_v_ok ctxt v /\ LIST_TYPE_HEAD THM_TYPE_HEAD v ==>
   ?ths. LIST_TYPE THM_TYPE ths v`,
  STRIP_TAC THEN MATCH_MP_TAC (GEN_ALL v_ok_LIST_TYPE_HEAD) THEN
  EXISTS_TAC `ctxt:update list` THEN EXISTS_TAC `THM_TYPE_HEAD` THEN
  ASM_MESON_TAC[v_ok_THM_TYPE_HEAD]);;

let v_ok_PAIR_TYPE_HEAD = prove
 (`candle_v_ok ctxt v /\
   (!v. candle_v_ok ctxt v /\ A_HEAD v ==> ?a. (A:A->v->bool) a v) /\
   (!v. candle_v_ok ctxt v /\ B_HEAD v ==> ?b. (B:B->v->bool) b v) /\
   PAIR_TYPE_HEAD A_HEAD B_HEAD v ==>
   ?p. PAIR_TYPE A B p v`,
  REWRITE_TAC[PAIR_TYPE_HEAD_def; PAIR_TYPE_def; K_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[v_ok_Conv_NONE; ALL]) THEN
  SUBGOAL_THEN `?a. (A:A->v->bool) a v1_1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?b. (B:B->v->bool) b v1_2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(a:A,b:B)` THEN REWRITE_TAC[PAIR_TYPE_def] THEN ASM_MESON_TAC[]);;

let v_ok_LIST_PAIR_TYPE_HEAD = prove
 (`candle_v_ok ctxt v /\
   (!v. candle_v_ok ctxt v /\ A_HEAD v ==> ?a. (A:A->v->bool) a v) /\
   (!v. candle_v_ok ctxt v /\ B_HEAD v ==> ?b. (B:B->v->bool) b v) /\
   LIST_TYPE_HEAD (PAIR_TYPE_HEAD A_HEAD B_HEAD) v ==>
   ?ls. LIST_TYPE (PAIR_TYPE A B) ls v`,
  STRIP_TAC THEN MATCH_MP_TAC (GEN_ALL v_ok_LIST_TYPE_HEAD) THEN
  MAP_EVERY EXISTS_TAC [`ctxt:update list`; `PAIR_TYPE_HEAD A_HEAD B_HEAD`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC (GEN_ALL v_ok_PAIR_TYPE_HEAD) THEN
  MAP_EVERY EXISTS_TAC [`ctxt:update list`; `A_HEAD:v->bool`; `B_HEAD:v->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* v_ok and an invariant of the k-th kernel type: the value is inferred *)
let CAN2AAUX_V_OK_INFERRED_TAC (def,ty,k) from_th =
  STRIP_TAC THEN
  SUBGOAL_THEN `candle_inferred ctxt v` (fun th -> ASM_MESON_TAC[th; from_th]) THEN
  CASES_ON ty THEN FS[def] THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MATCH_MP_TAC CAN2AAUX_v_ok_kernel_Conv THEN
  ASM_REWRITE_TAC[el k (CONJUNCTS CAN2AAUX_kernel_types_IN)];;

let v_ok_TYPE = prove
 (`candle_v_ok ctxt v /\ TYPE_TYPE ty v ==> holKernelProof_TYPE ctxt ty`,
  CAN2AAUX_V_OK_INFERRED_TAC (TYPE_TYPE_def,`ty:hol_type`,0) TYPE_from_TYPE_TYPE);;

let v_ok_TERM = prove
 (`candle_v_ok ctxt v /\ TERM_TYPE tm v ==> holKernelProof_TERM ctxt tm`,
  CAN2AAUX_V_OK_INFERRED_TAC (TERM_TYPE_def,`tm:hol_term`,1) TERM_from_TERM_TYPE);;

let v_ok_THM = prove
 (`candle_v_ok ctxt v /\ THM_TYPE th v ==> holKernelProof_THM ctxt th`,
  CAN2AAUX_V_OK_INFERRED_TAC (THM_TYPE_def,`th:thm`,2) THM_from_THM_TYPE);;

let v_ok_LIST = prove
 (`(!x v. (A_TYPE:A->v->bool) x v /\ candle_v_ok ctxt v ==> A ctxt x) ==>
   !ls v. LIST_TYPE A_TYPE ls v /\ candle_v_ok ctxt v ==> ALL (A ctxt) ls`,
  DISCH_TAC THEN LIST_INDUCT_TAC THEN RW[LIST_TYPE_def; ALL] THEN
  FS[v_ok_Cons] THEN ASM_MESON_TAC[]);;

let v_ok_LIST_TERM = prove
 (`!tms v ctxt. LIST_TYPE TERM_TYPE tms v /\ candle_v_ok ctxt v ==>
                ALL (holKernelProof_TERM ctxt) tms`,
  REPEAT STRIP_TAC THEN IRULE v_ok_LIST THEN
  MAP_EVERY EXISTS_TAC [`TERM_TYPE`; `v:v`] THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[v_ok_TERM]);;

let v_ok_LIST_THM = prove
 (`!ths v ctxt. LIST_TYPE THM_TYPE ths v /\ candle_v_ok ctxt v ==>
                ALL (holKernelProof_THM ctxt) ths`,
  REPEAT STRIP_TAC THEN IRULE v_ok_LIST THEN
  MAP_EVERY EXISTS_TAC [`THM_TYPE`; `v:v`] THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[v_ok_THM]);;

let v_ok_LIST_TYPE = prove
 (`!tms v ctxt. LIST_TYPE TYPE_TYPE tms v /\ candle_v_ok ctxt v ==>
                ALL (holKernelProof_TYPE ctxt) tms`,
  REPEAT STRIP_TAC THEN IRULE v_ok_LIST THEN
  MAP_EVERY EXISTS_TAC [`TYPE_TYPE`; `v:v`] THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[v_ok_TYPE]);;

let v_ok_PAIR = prove
 (`(!x v. (A_TYPE:A->v->bool) x v /\ candle_v_ok ctxt v ==> A ctxt x) /\
   (!x v. (B_TYPE:B->v->bool) x v /\ candle_v_ok ctxt v ==> B ctxt x) /\
   PAIR_TYPE A_TYPE B_TYPE x v /\ candle_v_ok ctxt v ==>
   (\ctxt p. A ctxt (FST p) /\ B ctxt (SND p)) ctxt x`,
  PAIR_CASES_ON `x:A#B` THEN RW[PAIR_TYPE_def] THEN
  FIRST_X_ASSUM (MP_TAC o REWRITE_RULE[v_ok_Conv_NONE; ALL] o
                 check (fun th -> is_comb (concl th) &&
                                  fst (strip_comb (concl th)) = `candle_v_ok`)) THEN
  ASM_MESON_TAC[]);;

let LIST_TYPE_perms_ok = prove
 (`!xs xsv.
     (!x v. (A:A->v->bool) x v /\ MEM x xs ==> perms_ok ps v) /\
     LIST_TYPE A xs xsv ==>
     perms_ok ps xsv`,
  LIST_INDUCT_TAC THEN RW[LIST_TYPE_def; perms_ok_def; ALL; MEM] THEN
  ASM_MESON_TAC[]);;

let PAIR_TYPE_perms_ok = prove
 (`(!x v. (A:A->v->bool) x v ==> perms_ok ps v) /\
   (!x v. (B:B->v->bool) x v ==> perms_ok ps v) /\
   PAIR_TYPE A B x v ==>
   perms_ok ps v`,
  PAIR_CASES_ON `x:A#B` THEN RW[PAIR_TYPE_def; perms_ok_def; ALL] THEN
  ASM_MESON_TAC[]);;

let UNIT_TYPE_perms_ok = prove
 (`!u v. UNIT_TYPE u v ==> perms_ok ps v`,
  RW[UNIT_TYPE_def; perms_ok_def; ALL]);;

let INT_perms_ok = prove
 (`!s v. ml_INT s v ==> perms_ok ps v`,
  RW[ml_INT_def; perms_ok_def]);;

let NUM_perms_ok = prove
 (`!s v. ml_NUM s v ==> perms_ok ps v`,
  RW[ml_NUM_def; ml_INT_def; perms_ok_def]);;

let STRING_TYPE_perms_ok = prove
 (`!s v. STRING_TYPE s v ==> perms_ok ps v`,
  RW[STRING_TYPE_def; perms_ok_def]);;

let TYPE_TYPE_perms_ok = prove
 (`!ty v. TYPE_TYPE ty v ==> perms_ok ps v`,
  MATCH_MP_TAC TYPE_TYPE_ind THEN RW[TYPE_TYPE_def; perms_ok_def; ALL] THEN
  ASM_MESON_TAC[STRING_TYPE_perms_ok; LIST_TYPE_perms_ok]);;

let TERM_TYPE_perms_ok = prove
 (`!tm v. TERM_TYPE tm v ==> perms_ok ps v`,
  MATCH_MP_TAC hol_term_INDUCT THEN RW[TERM_TYPE_def; perms_ok_def; ALL] THEN
  ASM_MESON_TAC[STRING_TYPE_perms_ok; TYPE_TYPE_perms_ok]);;

let THM_TYPE_perms_ok = prove
 (`!th v. THM_TYPE th v ==> perms_ok ps v`,
  MATCH_MP_TAC thm_INDUCT THEN RW[THM_TYPE_def; perms_ok_def; ALL] THEN
  ASM_MESON_TAC[TERM_TYPE_perms_ok; LIST_TYPE_perms_ok]);;

let LIST_TERM_TYPE_perms_ok = prove
 (`!tm v. LIST_TYPE TERM_TYPE tm v ==> perms_ok ps v`,
  MESON_TAC[LIST_TYPE_perms_ok; TERM_TYPE_perms_ok]);;

let LIST_TYPE_TYPE_perms_ok = prove
 (`!tm v. LIST_TYPE TYPE_TYPE tm v ==> perms_ok ps v`,
  MESON_TAC[LIST_TYPE_perms_ok; TYPE_TYPE_perms_ok]);;

(* HOL4 quantifies a vacuous tm and leaves th free *)
let LIST_TYPE_THM_perms_ok = prove
 (`!th v. LIST_TYPE THM_TYPE th v ==> perms_ok ps v`,
  MESON_TAC[LIST_TYPE_perms_ok; THM_TYPE_perms_ok]);;

let UPDATE_TYPE_perms_ok = prove
 (`!u v. UPDATE_TYPE u v ==> perms_ok ps v`,
  MATCH_MP_TAC update_INDUCT THEN RW[UPDATE_TYPE_def; perms_ok_def; ALL] THEN
  ASM_MESON_TAC[TYPE_TYPE_perms_ok; TERM_TYPE_perms_ok; STRING_TYPE_perms_ok;
                NUM_perms_ok; LIST_TYPE_perms_ok; PAIR_TYPE_perms_ok]);;

let sub_conv_rules,sub_conv_ind,sub_conv_cases,sub_conv_strongind = cake_inductive
  `!v vs cn. MEM v vs ==> sub_conv (v:v) (Conv cn vs)`;;

let CAN2AAUX_kernel_vals_Conv_inferred = prove
 (`candle_kernel_vals ctxt (Conv cn vs) ==> candle_inferred ctxt (Conv cn vs)`,
  ONCE_REWRITE_TAC[candle_v_ok_cases] THEN
  REWRITE_TAC[CAN2AAUX_do_partial_app_SOME] THEN MESON_TAC[distinctness "v"]);;

let CAN2AAUX_LIST_v_ok = prove
 (`!P (A:A->v->bool) ls v.
     LIST_TYPE A ls v /\ ALL P ls /\ (!x v. P x /\ A x v ==> candle_v_ok ctxt v) ==>
     candle_v_ok ctxt v`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIST_TYPE_v_ok THEN
  MAP_EVERY EXISTS_TAC [`A:A->v->bool`; `ls:A list`] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ALL (P:A->bool) ls` THEN MATCH_MP_TAC MONO_ALL THEN
  ASM_MESON_TAC[]);;

let CAN2AAUX_TERM_Abs = prove
 (`holKernelProof_TERM ctxt (hol_Abs t x) ==>
   holKernelProof_TERM ctxt t /\ holKernelProof_TERM ctxt x`,
  REWRITE_TAC[holKernelProof_TERM_def; hol_term_ok_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[hol_term_ok_def]);;

let sub_conv_ok = prove
 (`!v w. sub_conv v w ==> candle_v_ok ctxt w ==> candle_v_ok ctxt v`,
  MATCH_MP_TAC sub_conv_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_v_ok_def] THEN STRIP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[ALL_MEM]] THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP CAN2AAUX_kernel_vals_Conv_inferred) THEN
  ONCE_REWRITE_TAC[candle_inferred_cases] THEN
  REWRITE_TAC[Conv_NOT_IN_kernel_funs] THEN STRIP_TAC THENL
   [CASES_ON `ty:hol_type` THEN FS[TYPE_TYPE_def] THEN GVS[MEM] THEN
    ASM_MESON_TAC[STRING_TYPE_v_ok; CAN2AAUX_LIST_v_ok; TYPE; TYPE_IMP_v_ok];
    CASES_ON `tm:hol_term` THEN FS[TERM_TYPE_def] THEN GVS[MEM] THEN
    ASM_MESON_TAC[STRING_TYPE_v_ok; TERM; TYPE_IMP_v_ok; TERM_IMP_v_ok; CAN2AAUX_TERM_Abs];
    CASES_ON `th:thm` THEN FS[THM_TYPE_def] THEN GVS[MEM] THEN
    ASM_MESON_TAC[THM; TERM_IMP_v_ok; CAN2AAUX_LIST_v_ok]]);;

let v_ok_Conv_alt = prove
 (`candle_v_ok ctxt (Conv (SOME stamp) vs) ==> ALL (candle_v_ok ctxt) vs`,
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[sub_conv_rules; sub_conv_ok]);;
