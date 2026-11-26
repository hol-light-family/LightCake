(* ========================================================================= *)
(* candle_basis_evaluate: port of HOL4 candle/prover/                        *)
(* candle_basis_evaluateScript.sml (CakeML v3479).  Proving that the basis   *)
(* program only produces v_ok values.                                        *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 proves evaluate_basis_v_ok by match_mp_tac with an instance of     *)
(*   full_evaluate_ind and one suspended goal per case; here the instance is *)
(*   can2dbaux_ind_thm and each case is a lemma                              *)
(*   CAN2DBAUX_evaluate_basis_v_ok_NAME of its antecedent (the cases HOL4    *)
(*   closes by simp [] are CAN2DBAUX_evaluate_basis_v_ok_other k).           *)
(* - simple_exp_simps and simple_dec_simps are HOL4's simplifier output      *)
(*   written out.                                                            *)
(* - The cases are proved with the kit's kit_distinct_names (restored        *)
(*   afterwards).                                                            *)
(* - Local helpers that are not HOL4 theorems are CAN2DBAUX_ (OCaml values   *)
(*   can2dbaux_); candle_prover_evaluate's CAN2DAUX_ helpers are used too.   *)
(* ========================================================================= *)

needs "candle/prover/candle_prover_inv.ml";;
needs "candle/prover/ast_extras.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "candle/prover/perms.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "misc/misc.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "hol4/sptree.ml";;
needs "candle/prover/candle_kernelProg.ml";;
needs "candle/prover/candle_prover_evaluate.ml";;

type_invention_error := true;;

(* HOL4 temp_send_to_back_overload of compute_syntax's and compute_exec's    *)
(* If, App, Var, Let: the port's compute constructors have the prefixes      *)
(* compute_ and compute_exec_ (nothing to do)                                *)

(* ------------------------------------------------------------------------- *)
(* Local helpers (not HOL4 theorems): CAN2DBAUX_ theorems and tactics,       *)
(* can2dbaux_ OCaml values.                                                  *)
(* ------------------------------------------------------------------------- *)

let candle_simple_exp_def = cake_def
  `candle_simple_exp =
     every_exp (\x. match x with
                      App op xs -> (match op with
                                      VfromList -> T
                                    | Aw8alloc -> T
                                    | Test _ _ -> T
                                    | Arith _ _ -> T
                                    | FromTo _ _ -> T
                                    | _ -> F)
                    | Lit lit -> T
                    | Var v -> T
                    | Con opt xs -> T
                    | _ -> F)`;;

(* HOL4: the simplification of simple_exp on each constructor (srw_ss with   *)
(* simple_exp_def, then GSYM simple_exp_def)                                 *)
let simple_exp_simps = prove
 (CASE_TERM
  `(!e. ~candle_simple_exp (Raise e)) /\
   (!e pes. ~candle_simple_exp (Handle e pes)) /\
   (!lit. candle_simple_exp (Lit lit)) /\
   (!opt xs. candle_simple_exp (Con opt xs) <=> ALL candle_simple_exp xs) /\
   (!n. candle_simple_exp (Var n)) /\
   (!n x. ~candle_simple_exp (Fun n x)) /\
   (!op xs. candle_simple_exp (App op xs) <=>
      (match op with
         VfromList -> T
       | Aw8alloc -> T
       | Test _ _ -> T
       | Arith _ _ -> T
       | FromTo _ _ -> T
       | _ -> F) /\
      ALL candle_simple_exp xs) /\
   (!lop x y. ~candle_simple_exp (Log lop x y)) /\
   (!x y z. ~candle_simple_exp (If x y z)) /\
   (!e pes. ~candle_simple_exp (Mat e pes)) /\
   (!opt x y. ~candle_simple_exp (Let opt x y)) /\
   (!f x. ~candle_simple_exp (Letrec f x)) /\
   (!e t. ~candle_simple_exp (Tannot e t)) /\
   (!e l. ~candle_simple_exp (Lannot e l))`,
  REWRITE_TAC[candle_simple_exp_def; ast_extras_every_exp_def] THEN
  CAKE_REWRITE_TAC[]);;
let _ = cake_add_simps [simple_exp_simps];;

let candle_simple_pat_def = cake_def
  `(candle_simple_pat (Pvar p) <=> T) /\
   (candle_simple_pat Pany <=> T) /\
   (candle_simple_pat _ <=> F)`;;
let _ = cake_add_simps [candle_simple_pat_def];;

let candle_simple_dec_def = cake_def
  `candle_simple_dec =
     every_dec (\d. match d with
                      Dlet l p (Fun n x) -> candle_simple_pat p
                    | Dlet l p x -> candle_simple_exp x /\ candle_simple_pat p
                    | Dletrec l f -> T
                    | _ -> T)`;;

let simple_dec_Dlet = prove
 (`candle_simple_dec (Dlet l p x) <=>
   ((?n e. x = Fun n e) \/ candle_simple_exp x) /\ candle_simple_pat p`,
  REWRITE_TAC[candle_simple_dec_def; every_dec_def] THEN CAKE_REWRITE_TAC[] THEN
  QCASES_ON "x" THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[simple_exp_simps; injectivity "exp"; distinctness "exp"] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [simple_dec_Dlet];;

(* HOL4: ONCE_REWRITE_CONV [simple_dec_def], then GSYM simple_dec_def *)
let simple_dec_simps = prove
 (`(!l f. candle_simple_dec (Dletrec l f)) /\
   (!l tds. candle_simple_dec (Dtype l tds)) /\
   (!l ns n t. candle_simple_dec (Dtabbrev l ns n t)) /\
   (!l n ts. candle_simple_dec (Dexn l n ts)) /\
   (!mn ds. candle_simple_dec (Dmod mn ds) <=> ALL candle_simple_dec ds) /\
   (!ds1 ds2. candle_simple_dec (Dlocal ds1 ds2) <=>
              ALL candle_simple_dec ds1 /\ ALL candle_simple_dec ds2) /\
   (!n. candle_simple_dec (Denv n))`,
  REWRITE_TAC[candle_simple_dec_def; every_dec_def] THEN CAKE_REWRITE_TAC[]);;
let _ = cake_add_simps [simple_dec_simps];;

let post_state_ok_def = cake_def
  `post_state_ok (s:(FFI)state) <=>
     (!n. n IN kernel_types ==> state_next_type_stamp s <= n) /\
     (!loc. loc IN kernel_locs ==> LENGTH (state_refs s) <= loc)`;;

let evaluate_post_state_mono = prove
 (`evaluate (s:(FFI)state) env xs = (s',res) /\ post_state_ok s' ==> post_state_ok s`,
  REWRITE_TAC[post_state_ok_def] THEN STRIP_TAC THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP (CONJUNCT1 evaluate_refs_length_mono)) THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP (GEN_ALL (CONJUNCT1 evaluate_next_type_stamp_mono))) THEN
  ASM_MESON_TAC[LE_TRANS]);;
let evaluate_decs_post_state_mono = prove
 (`!(s:(FFI)state) env ds s' res.
     evaluate_decs s env ds = (s',res) /\ post_state_ok s' ==> post_state_ok s`,
  MATCH_MP_TAC evaluate_decs_ind THEN RW[evaluate_decs_def] THEN
  GVS(all_case_eqs()) THEN
  TRY (DRULE_ALL evaluate_post_state_mono THEN REWRITE_TAC[] THEN NO_TAC) THEN
  RULE_ASSUM_TAC (REWRITE_RULE[post_state_ok_def; state_INFO.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[post_state_ok_def] THEN
  ASM_MESON_TAC[ARITH_RULE `a + b <= n ==> a <= n:num`]);;

(* ------------------------------------------------------------------------- *)
(* evaluate_basis_v_ok: HOL4 states it as the conclusion of                  *)
(* full_evaluate_ind for the predicates below and proves it by match_mp_tac  *)
(* with that instance, one suspended goal per case; here each case is a      *)
(* lemma CAN2DBAUX_evaluate_basis_v_ok_NAME of the instance's antecedent.    *)
(* ------------------------------------------------------------------------- *)

let can2dbaux_evaluate_P = CASE_TERM
 `\(s:(FFI)state) (env:v sem_env) (xs:exp list).
    !(res:(v list,v)result) (s':(FFI)state) (ctxt:update list).
      evaluate s env xs = (s',res) /\
      post_state_ok s' /\
      (!id len tag tn.
         nsLookup (sem_env_c env) id = SOME (len,TypeStamp tag tn) ==>
           ~(tn IN kernel_types)) /\
      candle_env_ok ctxt env /\
      ALL candle_simple_exp xs ==>
        (match res with
           Rval vs -> ALL (candle_v_ok ctxt) vs
         | Rerr (Rraise v) -> candle_v_ok ctxt v
         | _ -> T)`;;

let can2dbaux_evaluate_match_P =
 `\(s:(FFI)state) (env:v sem_env) (v:v) (ps:(pat#exp)list) (errv:v). T`;;

let can2dbaux_evaluate_decs_P = CASE_TERM
 `\(s:(FFI)state) (env:v sem_env) (ds:dec list).
    !(res:(v sem_env,v)result) (s':(FFI)state) (ctxt:update list).
      evaluate_decs s env ds = (s',res) /\
      post_state_ok s' /\
      (!id len tag tn.
         nsLookup (sem_env_c env) id = SOME (len,TypeStamp tag tn) ==>
           ~(tn IN kernel_types)) /\
      candle_env_ok ctxt env /\
      ALL candle_simple_dec ds /\
      ALL safe_dec ds ==>
        (match res with
           Rval env1 ->
             candle_env_ok ctxt (extend_dec_env env1 env) /\
             (!id len tag tn.
                nsLookup (sem_env_c (extend_dec_env env1 env)) id =
                SOME (len,TypeStamp tag tn) ==>
                  ~(tn IN kernel_types))
         | Rerr (Rraise v) -> candle_v_ok ctxt v
         | _ -> T)`;;

let can2dbaux_ind_thm =
  CONV_RULE (DEPTH_CONV BETA_CONV)
    (ISPECL [can2dbaux_evaluate_P; can2dbaux_evaluate_match_P; can2dbaux_evaluate_decs_P]
       full_evaluate_ind);;

(* the k-th case of the induction (numbered as can2daux_case) *)
let can2dbaux_case k = el k (conjuncts (lhand (concl can2dbaux_ind_thm)));;

(* post_state_ok s for every evaluation s -> s' with post_state_ok s', to a  *)
(* fixpoint (HOL4 drule_all_then assume_tac evaluate_post_state_mono, ..)    *)
let can2dbaux_post_rules =
  map (IMP_CURRY_RULE o GEN_ALL) [evaluate_post_state_mono; evaluate_decs_post_state_mono];;

let rec CAN2DBAUX_POST_TAC : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  let cs = map concl ths in
  let news = flat (map (fun r ->
      mapfilter (fun e ->
        let r1 = MATCH_MP r e in
        tryfind (fun p -> let th = MATCH_MP r1 p in
                          if mem (concl th) cs then failwith "old" else th) ths) ths)
      can2dbaux_post_rules) in
  let rec dedup l = match l with
      [] -> []
    | th::t -> th :: dedup (filter (fun th' -> concl th' <> concl th) t) in
  let news = dedup news in
  if news = [] then ALL_TAC g
  else (MAP_EVERY ASSUME_TAC news THEN CAN2DBAUX_POST_TAC) g;;

(* an induction hypothesis for ctxt (HOL4 first_x_assum (drule_all_then ..)) *)
let CAN2DBAUX_IH_TAC : tactic =
  FIRST_X_ASSUM (fun th -> DRULE_ALL th) THEN STRIP_TAC;;

let CAN2DBAUX_IH0_TAC : tactic =
  FIRST_X_ASSUM (MP_TAC o SPEC `ctxt:update list`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let CAN2DBAUX_POST_UNFOLD_TAC =
  RULE_ASSUM_TAC (REWRITE_RULE[post_state_ok_def; state_INFO.ri_accfupds; K_THM]);;

(* the constructor environment condition of the theorem, for the environment *)
(* updates of evaluate_decs                                                  *)
let CAN2DBAUX_c_ok_extend = prove
 (`(!id len tag tn. nsLookup (sem_env_c env1) id = SOME (len,TypeStamp tag tn) ==>
                    ~(tn IN kernel_types)) /\
   (!id len tag tn. nsLookup (sem_env_c env2) id = SOME (len,TypeStamp tag tn) ==>
                    ~(tn IN kernel_types)) ==>
   (!id len tag tn. nsLookup (sem_env_c (extend_dec_env env1 env2)) id =
                    SOME (len,TypeStamp tag tn) ==> ~(tn IN kernel_types))`,
  REWRITE_TAC[extend_dec_env_def; sem_env_INFO.ri_accessors; nsLookup_nsAppend_some] THEN
  MESON_TAC[]);;

let CAN2DBAUX_c_ok_extend_IMP = prove
 (`(!id len tag tn. nsLookup (sem_env_c (extend_dec_env env1 env2)) id =
                    SOME (len,TypeStamp tag tn) ==> ~(tn IN kernel_types)) ==>
   (!id len tag tn. nsLookup (sem_env_c env1) id = SOME (len,TypeStamp tag tn) ==>
                    ~(tn IN kernel_types))`,
  REWRITE_TAC[extend_dec_env_def; sem_env_INFO.ri_accessors; nsLookup_nsAppend_some] THEN
  MESON_TAC[]);;

let CAN2DBAUX_c_ok_nsEmpty = prove
 (`!id len tag tn. nsLookup (sem_env_c (sem_env_REC e nsEmpty:v sem_env)) id =
                   SOME (len,TypeStamp tag tn) ==> ~(tn IN kernel_types)`,
  REWRITE_TAC[sem_env_INFO.ri_accessors; nsLookup_nsEmpty; option_DISTINCT]);;

let CAN2DBAUX_c_ok_nsLift = prove
 (`(!id len tag tn. nsLookup (sem_env_c env1) id = SOME (len,TypeStamp tag tn) ==>
                    ~(tn IN kernel_types)) ==>
   (!id len tag tn.
      nsLookup (sem_env_c (sem_env_REC (nsLift (mn:mlstring) (sem_env_v (env1:v sem_env)))
                                       (nsLift mn (sem_env_c env1)))) id =
      SOME (len,TypeStamp tag tn) ==> ~(tn IN kernel_types))`,
  REWRITE_TAC[sem_env_INFO.ri_accessors] THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[nsLookup_nsLift] THEN
  TOP_CASE_TAC THEN RW[option_DISTINCT] THEN ASM_MESON_TAC[]);;

let CAN2DBAUX_nsSing_Exn = prove
 (`!id len tag tn.
     ~(nsLookup (nsSing cn (l,ExnStamp k):(mlstring,mlstring,num#stamp)namespace) id =
       SOME (len,TypeStamp tag tn))`,
  GEN_TAC THEN QCASES_ON "id" THEN
  REWRITE_TAC[nsSing_def; nsLookup_def; ALOOKUP_DEF; option_DISTINCT] THEN
  RW[option_INJ; PAIR_EQ; distinctness "stamp"]);;

(* pattern matching with a simple pattern (Pvar, Pany) *)
let CAN2DBAUX_pmatch_simple = prove
 (`candle_simple_pat p /\ pmatch envC s p v [] = Match env1 /\ candle_v_ok ctxt v ==>
   ALL (candle_v_ok ctxt) (MAP SND env1)`,
  QCASES_ON "p" THEN REWRITE_TAC[candle_simple_pat_def; pmatch_def] THEN
  RW[injectivity "match_result"] THEN ASM_REWRITE_TAC[MAP; ALL]);;

let CAN2DBAUX_pmatch_Closure = prove
 (`candle_simple_pat p /\ pmatch envC s p (Closure env n e) [] = Match env1 /\
   candle_env_ok ctxt env /\ safe_exp e ==>
   ALL (candle_v_ok ctxt) (MAP SND env1)`,
  STRIP_TAC THEN
  MP_TAC (INST [`Closure env n e`,`v:v`] CAN2DBAUX_pmatch_simple) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC candle_v_ok_Closure THEN ASM_REWRITE_TAC[]);;

let CAN2DBAUX_declare_env_v_ok = prove
 (`declare_env es env = SOME (x,es') /\ candle_env_ok ctxt env ==> candle_v_ok ctxt x`,
  QCASES_ON "es" THEN REWRITE_TAC[declare_env_def; option_CASE; option_DISTINCT] THEN
  MATCH_GOALSUB_RENAME_TAC "eval_state_CASE e" THEN QCASES_ON "e" THEN
  CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN
  GVS[pair_case_eq; option_case_eq; candle_v_ok_def; v_ok_Conv_NONE; ALL; nat_to_v_def]);;

(* the operations simple_exp allows *)
let CAN2DBAUX_simple_op = prove
 (CASE_TERM
  `(match op with
      VfromList -> T
    | Aw8alloc -> T
    | Test _ _ -> T
    | Arith _ _ -> T
    | FromTo _ _ -> T
    | _ -> F) <=>
   op = VfromList \/ op = Aw8alloc \/ (?t ty. op = Test t ty) \/
   (?a ty. op = Arith a ty) \/ (?t1 t2. op = FromTo t1 t2)`,
  QCASES_ON "op" THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "op"; injectivity "op"] THEN MESON_TAC[]);;

(* the results of do_arith and do_conversion *)
let can2dbaux_result_rules =
  map GEN_ALL (CONJUNCTS CAN2DAUX_do_arith_ok @ CONJUNCTS CAN2DAUX_do_conversion_ok);;

let CAN2DBAUX_RESULT_TAC : tactic =
  FIRST_ASSUM (fun th -> FIRST (map (fun r g -> MATCH_ACCEPT_TAC (MATCH_MP r th) g)
                                     can2dbaux_result_rules));;

(* the end of the App case, chosen by the shape of the goal *)
let CAN2DBAUX_APP_FIN_TAC : tactic = fun (asl,w as g) ->
  (if can2daux_has "Vectorv" w then
     CAN2DBAUX_POST_UNFOLD_TAC THEN CAN2DBAUX_IH0_TAC THEN
     REWRITE_TAC can2daux_v_ok_basic THEN ASM_MESON_TAC[v_ok_v_to_list]
   else if can2daux_has "Loc" w then
     REWRITE_TAC can2daux_v_ok_basic THEN
     RULE_ASSUM_TAC (REWRITE_RULE[post_state_ok_def; state_INFO.ri_accfupds; K_THM;
                                  store_alloc_def; PAIR_EQ]) THEN
     GVS[LENGTH_APPEND; LENGTH] THEN STRIP_TAC THEN RES_TAC THEN ASM_ARITH_TAC
   else if can2daux_has "Boolv" w then REWRITE_TAC[CAN2DAUX_v_ok_Boolv]
   else if can2daux_has "list_result" w then GVS[sum_case_eq] THEN CAN2DBAUX_RESULT_TAC
   else CAN2DBAUX_IH0_TAC THEN FIRST_ASSUM ACCEPT_TAC) g;;

let CAN2DBAUX_DLET_FIN_TAC =
  (DRULE_ALL CAN2DBAUX_pmatch_simple ORELSE DRULE_ALL CAN2DBAUX_pmatch_Closure) THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC env_ok_extend_dec_env THEN ASM_SIMP_TAC[CAN2DAUX_env_ok_alist_to_ns];
    MATCH_MP_TAC CAN2DBAUX_c_ok_extend THEN ASM_REWRITE_TAC[CAN2DBAUX_c_ok_nsEmpty]];;

(* the case splits name new variables apart (the kit's default can give a   *)
(* v and a v list the same name)                                             *)
let can2dbaux_distinct_names = !kit_distinct_names;;
kit_distinct_names := true;;

let CAN2DBAUX_evaluate_basis_v_ok_Nil = prove
 (can2dbaux_case 0,
  RW[evaluate_def]);;

let CAN2DBAUX_evaluate_basis_v_ok_Cons = prove
 (can2dbaux_case 1,
  RW[evaluate_def] THEN GVS[pair_case_eq; case_eq "result"] THEN
  CAN2DBAUX_POST_TAC THEN
  TRY (FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP evaluate_sing) THEN GVS[ALL]) THEN
  ASM_MESON_TAC[]);;

let CAN2DBAUX_evaluate_basis_v_ok_Lit = prove
 (can2dbaux_case 2,
  RW[evaluate_def; candle_v_ok_Lit; ALL]);;

let CAN2DBAUX_evaluate_basis_v_ok_Con = prove
 (can2dbaux_case 5,
  RW[evaluate_def] THEN GVS(all_case_eqs()) THEN CAN2DBAUX_POST_TAC THEN
  TRY (ASM_MESON_TAC[] THEN NO_TAC) THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `ctxt:update list`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  QPAT_X_ASSUM "build_conv _ _ _ = SOME _" MP_TAC THEN
  REWRITE_TAC[build_conv_def] THEN QCASES_ON "cn" THEN RW[option_case_eq; pair_case_eq] THEN
  MATCH_MP_TAC candle_v_ok_Conv THEN
  ASM_REWRITE_TAC[EVERY_REVERSE; option_DISTINCT; option_INJ] THEN
  ASM_MESON_TAC[]);;

let CAN2DBAUX_evaluate_basis_v_ok_Var = prove
 (can2dbaux_case 6,
  RW[evaluate_def] THEN GVS[option_case_eq; ALL] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[candle_env_ok_def]) THEN ASM_MESON_TAC[]);;

let CAN2DBAUX_evaluate_basis_v_ok_App = prove
 (can2dbaux_case 8,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ALL; simple_exp_simps; CAN2DBAUX_simple_op] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  QPAT_X_ASSUM "evaluate _ _ [App _ _] = _" (MP_TAC o ONCE_REWRITE_RULE[evaluate_def]) THEN
  REWRITE_TAC[getOpClass_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "thunk_op"; distinctness "op"] THEN DISCH_TAC THEN
  GVS[pair_case_eq; case_eq "result"; option_case_eq] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[do_app_cases]) THEN GVS[] THEN
  CAN2DBAUX_POST_TAC THEN CAN2DBAUX_APP_FIN_TAC);;

(* the cases where the expressions are not simple *)
let CAN2DBAUX_evaluate_basis_v_ok_other k = prove
 (can2dbaux_case k,
  RW[evaluate_def; evaluate_decs_def]);;

let CAN2DBAUX_evaluate_basis_v_ok_decs_Nil = prove
 (can2dbaux_case 18,
  RW[evaluate_decs_def] THEN ASM_SIMP_TAC[env_ok_extend_dec_env; env_ok_nsEmpty] THEN
  MATCH_MP_TAC CAN2DBAUX_c_ok_extend THEN
  ASM_REWRITE_TAC[sem_env_INFO.ri_accessors; nsLookup_nsEmpty; option_DISTINCT]);;

let CAN2DBAUX_evaluate_basis_v_ok_decs_Cons = prove
 (can2dbaux_case 19,
  RW[evaluate_decs_def] THEN GVS(all_case_eqs()) THEN CAN2DBAUX_POST_TAC THEN
  CAN2DBAUX_IH_TAC THEN CAN2DBAUX_IH_TAC THEN
  MATCH_GOALSUB_RENAME_TAC "combine_dec_result _ r" THEN QCASES_ON "r" THEN
  FS[combine_dec_result_def; extend_dec_env_def] THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

let CAN2DBAUX_evaluate_basis_v_ok_decs_Dlet = prove
 (can2dbaux_case 20,
  RW[evaluate_decs_def] THEN GVS(all_case_eqs()) THEN CAN2DBAUX_POST_TAC THEN
  TRY (CAN2DBAUX_IH0_TAC THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  RULE_ASSUM_TAC (REWRITE_RULE[evaluate_def]) THEN GVS[] THEN
  TRY (CAN2DBAUX_IH0_TAC THEN
       FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP evaluate_sing) THEN GVS[ALL; HD]) THEN
  CAN2DBAUX_DLET_FIN_TAC);;

let CAN2DBAUX_evaluate_basis_v_ok_decs_Dletrec = prove
 (can2dbaux_case 21,
  RW[evaluate_decs_def] THEN GVS(all_case_eqs()) THEN CONJ_TAC THENL
   [MATCH_MP_TAC env_ok_extend_dec_env THEN
    ASM_SIMP_TAC[CAN2DAUX_env_ok_build_rec_env_nsEmpty];
    MATCH_MP_TAC CAN2DBAUX_c_ok_extend THEN ASM_REWRITE_TAC[CAN2DBAUX_c_ok_nsEmpty]]);;

let CAN2DBAUX_evaluate_basis_v_ok_decs_Dtype = prove
 (can2dbaux_case 22,
  RW[evaluate_decs_def] THEN GVS(all_case_eqs()) THEN
  SUBGOAL_THEN `!id len tag tn.
     nsLookup (build_tdefs (state_next_type_stamp (st:(FFI)state)) tds) id =
     SOME (len,TypeStamp tag tn) ==> ~(tn IN kernel_types)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP CAN2DAUX_build_tdefs_stamp) THEN
    QPAT_X_ASSUM "post_state_ok _"
      (STRIP_ASSUME_TAC o REWRITE_RULE[post_state_ok_def; state_INFO.ri_accfupds; K_THM]) THEN
    RES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC env_ok_extend_dec_env THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[candle_env_ok_def; sem_env_INFO.ri_accessors; nsLookup_nsEmpty;
                option_DISTINCT] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CAN2DBAUX_c_ok_extend THEN
    ASM_REWRITE_TAC[sem_env_INFO.ri_accessors]]);;

let CAN2DBAUX_evaluate_basis_v_ok_decs_Dtabbrev = prove
 (can2dbaux_case 23,
  RW[evaluate_decs_def] THEN
  ASM_SIMP_TAC[env_ok_extend_dec_env; env_ok_nsEmpty] THEN
  MATCH_MP_TAC CAN2DBAUX_c_ok_extend THEN
  ASM_REWRITE_TAC[sem_env_INFO.ri_accessors; nsLookup_nsEmpty; option_DISTINCT]);;

let CAN2DBAUX_evaluate_basis_v_ok_decs_Denv = prove
 (can2dbaux_case 24,
  RW[evaluate_decs_def] THEN GVS(all_case_eqs()) THEN
  DRULE_ALL CAN2DBAUX_declare_env_v_ok THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC env_ok_extend_dec_env THEN ASM_SIMP_TAC[CAN2DAUX_env_ok_nsSing];
    MATCH_MP_TAC CAN2DBAUX_c_ok_extend THEN ASM_REWRITE_TAC[CAN2DBAUX_c_ok_nsEmpty]]);;

let CAN2DBAUX_evaluate_basis_v_ok_decs_Dexn = prove
 (can2dbaux_case 25,
  RW[evaluate_decs_def] THEN GVS(all_case_eqs()) THEN CONJ_TAC THENL
   [MATCH_MP_TAC env_ok_extend_dec_env THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[candle_env_ok_def; sem_env_INFO.ri_accessors; nsLookup_nsEmpty;
                option_DISTINCT; CAN2DBAUX_nsSing_Exn];
    MATCH_MP_TAC CAN2DBAUX_c_ok_extend THEN
    ASM_REWRITE_TAC[sem_env_INFO.ri_accessors; CAN2DBAUX_nsSing_Exn]]);;

let CAN2DBAUX_evaluate_basis_v_ok_decs_Dmod = prove
 (can2dbaux_case 26,
  RW[evaluate_decs_def] THEN GVS(all_case_eqs()) THEN CAN2DBAUX_POST_TAC THEN
  CAN2DBAUX_IH_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN CONJ_TAC THENL
   [MATCH_MP_TAC env_ok_extend_dec_env THEN
    ASM_MESON_TAC[CAN2DAUX_env_ok_nsLift; CAN2DAUX_env_ok_extend_dec_env_IMP];
    MATCH_MP_TAC CAN2DBAUX_c_ok_extend THEN
    ASM_MESON_TAC[CAN2DBAUX_c_ok_nsLift; CAN2DBAUX_c_ok_extend_IMP]]);;

let CAN2DBAUX_evaluate_basis_v_ok_decs_Dlocal = prove
 (can2dbaux_case 27,
  RW[evaluate_decs_def] THEN GVS(all_case_eqs()) THEN CAN2DBAUX_POST_TAC THEN
  CAN2DBAUX_IH_TAC THEN FIRST_X_ASSUM (fun th -> DRULE_ALL th) THEN DISCH_TAC THEN
  QCASES_ON "res" THEN FS[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC env_ok_extend_dec_env THEN
    ASM_MESON_TAC[CAN2DAUX_env_ok_extend_dec_env_IMP];
    MATCH_MP_TAC CAN2DBAUX_c_ok_extend THEN
    ASM_MESON_TAC[CAN2DBAUX_c_ok_extend_IMP]]);;

kit_distinct_names := can2dbaux_distinct_names;;

(* ------------------------------------------------------------------------- *)
(* evaluate_basis_v_ok (HOL4: Finalise evaluate_basis_v_ok)                  *)
(* ------------------------------------------------------------------------- *)

let evaluate_basis_v_ok = prove
 (rand (concl can2dbaux_ind_thm),
  MATCH_MP_TAC can2dbaux_ind_thm THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC
   ([CAN2DBAUX_evaluate_basis_v_ok_Nil; CAN2DBAUX_evaluate_basis_v_ok_Cons;
     CAN2DBAUX_evaluate_basis_v_ok_Lit; CAN2DBAUX_evaluate_basis_v_ok_Con;
     CAN2DBAUX_evaluate_basis_v_ok_Var; CAN2DBAUX_evaluate_basis_v_ok_App;
     CAN2DBAUX_evaluate_basis_v_ok_decs_Nil; CAN2DBAUX_evaluate_basis_v_ok_decs_Cons;
     CAN2DBAUX_evaluate_basis_v_ok_decs_Dlet; CAN2DBAUX_evaluate_basis_v_ok_decs_Dletrec;
     CAN2DBAUX_evaluate_basis_v_ok_decs_Dtype; CAN2DBAUX_evaluate_basis_v_ok_decs_Dtabbrev;
     CAN2DBAUX_evaluate_basis_v_ok_decs_Denv; CAN2DBAUX_evaluate_basis_v_ok_decs_Dexn;
     CAN2DBAUX_evaluate_basis_v_ok_decs_Dmod; CAN2DBAUX_evaluate_basis_v_ok_decs_Dlocal] @
    map CAN2DBAUX_evaluate_basis_v_ok_other [3; 4; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17])));;

(* HOL4: el 3 (CONJUNCTS evaluate_basis_v_ok) *)
let evaluate_basis_v_ok_decs = el 2 (CONJUNCTS evaluate_basis_v_ok);;

let post_state_ok_with_clock = prove
 (`post_state_ok (state_clock_fupd (combin_K ck) (s:(FFI)state)) <=> post_state_ok s`,
  REWRITE_TAC[post_state_ok_def; state_INFO.ri_accfupds]);;
let _ = cake_add_simps [post_state_ok_with_clock];;
