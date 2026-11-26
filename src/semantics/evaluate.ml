(* ========================================================================= *)
(* evaluate: port of HOL4 semantics/evaluateScript.sml (CakeML v3479).       *)
(* Functional big-step semantics for evaluation of CakeML programs.         *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The semantics is defined with fix_clock (as in HOL4) so that the        *)
(*   termination conditions are provable; HOL4 then rebinds evaluate_def and *)
(*   evaluate_ind to the versions without fix_clock.  Here the definition    *)
(*   with fix_clock and its induction theorem are EVALAUX_evaluate_fix_def   *)
(*   and EVALAUX_evaluate_fix_ind (HOL4's first evaluate_def/evaluate_ind),  *)
(*   and evaluate_def, evaluate_ind, ... are HOL4's final theorems.          *)
(* - The clauses are parsed in four quotations (HOL4 types each clause on    *)
(*   its own: l, n and cn have different types in different clauses).       *)
(* - HOL4's r with <| f1 := x; f2 := y |> is f1_fupd (K x) (f2_fupd (K y) r).*)
(* ========================================================================= *)

needs "semantics/fpSem.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/semanticPrimitives.ml";;

type_invention_error := true;;

(* The semantics is defined here using fix_clock so that HOL4 generates     *)
(* provable termination conditions.  However, after termination is proved, *)
(* we clean up the definition (in HOL4) to remove occurrences of fix_clock. *)

(* HOL4 infers the most general type: s and s' are states of independent *)
(* types                                                                     *)
let fix_clock_def = cake_def
  `fix_clock (s:(A)state) ((s':(B)state),(res:C)) =
     (state_clock_fupd
        (combin_K (if state_clock s' <= state_clock s then state_clock s'
            else state_clock s)) s',res)`;;

let dec_clock_def = cake_def
  `dec_clock (s:(FFI)state) = state_clock_fupd (combin_K (state_clock s - 1)) s`;;

let do_eval_res_def = cake_def
  `do_eval_res vs (s:(FFI)state) =
     match do_eval vs (state_eval_state s) with
       NONE -> (s,(Rerr (Rabort Rtype_error):(v sem_env # dec list,A)result))
     | SOME (env1,decs,es1) -> (state_eval_state_fupd (combin_K es1) s,Rval (env1,decs))`;;

(* list_result is equivalent to map_result (\v. [v]) I, where map_result is *)
(* defined in evalPropsTheory                                                *)

let list_result_def = cake_def
  `(list_result (Rval (v:A)) = (Rval [v]:(A list,B)result)) /\
   (list_result (Rerr e) = Rerr e)`;;
let _ = cake_add_simps [list_result_def];;

(* HOL4 [local] *)
let fix_clock_IMP = prove
 (`!s x s1 res. fix_clock (s:(A)state) (x:(B)state#C) = (s1,res)
                ==> state_clock s1 <= state_clock s`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `x:(B)state#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s':(B)state` (X_CHOOSE_THEN `r:C` SUBST1_TAC)) THEN
  REWRITE_TAC[fix_clock_def; PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
  REWRITE_TAC[state_INFO.ri_accfupds; K_THM] THEN ARITH_TAC);;

(* HOL4 [local]; the library has it as list_size_reverse *)
let list_size_REVERSE = prove
 (`!xs. list_size (f:A->num) (REVERSE xs) = list_size f xs`,
  REWRITE_TAC[list_size_reverse]);;

let sing_env_def = cake_def
  `sing_env (n:varN) (v:v) = sem_env_REC (nsBind n v nsEmpty) nsEmpty : v sem_env`;;

(* ------------------------------------------------------------------------- *)
(* The termination tactic (HOL4: rw [do_if_def,do_log_def,do_eval_res_def,   *)
(* dec_clock_def] \\ imp_res_tac fix_clock_IMP \\ fs [] \\ fs [list_size_def,*)
(* list_size_REVERSE]).  It handles both kinds of termination conditions    *)
(* (R a' a, and !y. R y a' ==> R y a for a tail call).                       *)
(* ------------------------------------------------------------------------- *)

let EVALAUX_do_log_Exp = prove
 (`!l v e2 e. do_log l v e2 = SOME (Exp e) ==> e = e2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[do_log_def] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; injectivity "exp_or_val";
              distinctness "exp_or_val"] THEN
  MESON_TAC[]);;

let EVALAUX_do_if_SOME = prove
 (`!v (e1:exp) e2 e. do_if v e1 e2 = SOME e ==> e = e1 \/ e = e2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[do_if_def] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  MESON_TAC[]);;

let EVALAUX_is_num_fact tm =
  let t = if is_neg tm then dest_neg tm else tm in
  try let h,args = strip_comb t in
      length args = 2 && type_of (hd args) = `:num` &&
      mem (fst(dest_const h)) ["="; "<"; "<="; ">"; ">="]
  with Failure _ -> false;;

let EVALAUX_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP fix_clock_IMP)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP EVALAUX_do_log_Exp)) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o
                       MATCH_MP EVALAUX_do_if_SOME)) THEN
  REPEAT GEN_TAC THEN
  (fun g -> let ths = [inv_image_THM; LEX_DEF; sum_CASE; FST; SND;
                       dec_clock_def; state_INFO.ri_accfupds; K_THM;
                       list_size_reverse; pair_size_THM] @
                      !the_size_defs @ flat (map snd (!the_size_aux_eqs)) in
            (RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths) g) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (EVALAUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* The semantics (HOL4 evaluate_def before the clean-up below).              *)
(* ------------------------------------------------------------------------- *)

let EVALAUX_evaluate_clauses1 =
  `(evaluate (st:(FFI)state) (env:v sem_env) [] = (st,Rval []:(v list,v)result)) /\
   (evaluate st env (CONS e1 (CONS e2 es)) =
      match fix_clock st (evaluate st env [e1]) with
        (st',Rval v1) ->
          (match evaluate st' env (CONS e2 es) with
             (st'',Rval vs) -> (st'',Rval (CONS (HD v1) vs))
           | (st'',Rerr v8) -> (st'',Rerr v8))
      | (st',Rerr v10) -> (st',Rerr v10)) /\
   (evaluate st env [Lit l] = (st,Rval [Litv l])) /\
   (evaluate st env [Raise e] =
      match evaluate st env [e] with
        (st',Rval v) -> (st',Rerr (Rraise (HD v)))
      | (st',Rerr v8) -> (st',Rerr v8)) /\
   (evaluate st env [Handle e pes] =
      match fix_clock st (evaluate st env [e]) with
        (st',Rval v7) -> (st',Rval v7)
      | (st',Rerr (Rraise v)) ->
          (if can_pmatch_all (sem_env_c env) (state_refs st') (MAP FST pes) v
           then evaluate_match st' env v pes v
           else (st',Rerr (Rabort Rtype_error)))
      | (st',Rerr (Rabort v12)) -> (st',Rerr (Rabort v12))) /\
   (evaluate st env [Con cn es] =
      if do_con_check (sem_env_c env) cn (LENGTH es) then
        (match evaluate st env (REVERSE es) with
           (st',Rval vs) ->
             (match build_conv (sem_env_c env) cn (REVERSE vs) with
                NONE -> (st',Rerr (Rabort Rtype_error))
              | SOME v -> (st',Rval [v]))
         | (st',Rerr v8) -> (st',Rerr v8))
      else (st,Rerr (Rabort Rtype_error))) /\
   (evaluate st env [Var n] =
      match nsLookup (sem_env_v env) n with
        NONE -> (st,Rerr (Rabort Rtype_error))
      | SOME v -> (st,Rval [v])) /\
   (evaluate st env [Fun x e] = (st,Rval [Closure env x e])) /\
   (evaluate st env [App op es] =
      match fix_clock st (evaluate st env (REVERSE es)) with
        (st',Rval vs) ->
          (match getOpClass op with
             FunApp ->
               (match do_opapp (REVERSE vs) with
                  SOME (env',e) ->
                    (if state_clock st' = 0 then (st',Rerr (Rabort Rtimeout_error))
                     else evaluate (dec_clock st') env' [e])
                | NONE -> (st',Rerr (Rabort Rtype_error)))
           | Force ->
               (match dest_thunk (REVERSE vs) (state_refs st') with
                  BadRef -> (st',Rerr (Rabort Rtype_error))
                | NotThunk -> (st',Rerr (Rabort Rtype_error))
                | IsThunk Evaluated v -> (st',Rval [v])
                | IsThunk NotEvaluated f ->
                    (match do_opapp [f; Conv NONE []] with
                       SOME (env',e) ->
                         (if state_clock st' = 0
                          then (st',Rerr (Rabort Rtimeout_error))
                          else
                            (match evaluate (dec_clock st') env' [e] with
                               (st2,Rval vs2) ->
                                 (match update_thunk (REVERSE vs) (state_refs st2) vs2
                                  with
                                    NONE -> (st2,Rerr (Rabort Rtype_error))
                                  | SOME refs -> (state_refs_fupd (combin_K refs) st2,Rval vs2))
                             | (st2,Rerr e) -> (st2,Rerr e)))
                     | NONE -> (st',Rerr (Rabort Rtype_error))))
           | EvalOp ->
               (match fix_clock st' (do_eval_res (REVERSE vs) st') with
                  (st1,Rval (env1,decs)) ->
                    (if state_clock st1 = 0 then (st1,Rerr (Rabort Rtimeout_error))
                     else
                       (match fix_clock (dec_clock st1)
                                (evaluate_decs (dec_clock st1) env1 decs) with
                          (st2,Rval env2) ->
                            (match declare_env (state_eval_state st2)
                                     (extend_dec_env env2 env1) with
                               SOME (x,es2) ->
                                 (state_eval_state_fupd
                                    (combin_K (reset_env_generation (state_eval_state st') es2))
                                    st2,
                                  Rval [x])
                             | NONE -> (st2,Rerr (Rabort Rtype_error)))
                        | (st2,Rerr (Rabort a)) -> (st2,Rerr (Rabort a))
                        | (st2,Rerr e) ->
                            (state_eval_state_fupd
                               (combin_K (reset_env_generation (state_eval_state st')
                                     (state_eval_state st2))) st2,
                             Rerr e)))
                | (st1,Rerr e) -> (st1,Rerr e))
           | Simple ->
               (match do_app (state_refs st',state_ffi st') op (REVERSE vs) with
                  NONE -> (st',Rerr (Rabort Rtype_error))
                | SOME ((refs,ffi),r) ->
                    (state_refs_fupd (combin_K refs) (state_ffi_fupd (combin_K ffi) st'),
                     list_result r)))
      | res -> res) /\
   (evaluate st env [Log lop e1 e2] =
      match fix_clock st (evaluate st env [e1]) with
        (st',Rval v1) ->
          (match do_log lop (HD v1) e2 with
             NONE -> (st',Rerr (Rabort Rtype_error))
           | SOME (Exp e) -> evaluate st' env [e]
           | SOME (Val v) -> (st',Rval [v]))
      | (st',Rerr v9) -> (st',Rerr v9)) /\
   (evaluate st env [If e1 e2 e3] =
      match fix_clock st (evaluate st env [e1]) with
        (st',Rval v) ->
          (match do_if (HD v) e2 e3 with
             NONE -> (st',Rerr (Rabort Rtype_error))
           | SOME e -> evaluate st' env [e])
      | (st',Rerr v8) -> (st',Rerr v8)) /\
   (evaluate st env [Mat e pes] =
      match fix_clock st (evaluate st env [e]) with
        (st',Rval v) ->
          (if can_pmatch_all (sem_env_c env) (state_refs st') (MAP FST pes) (HD v)
           then evaluate_match st' env (HD v) pes bind_exn_v
           else (st',Rerr (Rabort Rtype_error)))
      | (st',Rerr v8) -> (st',Rerr v8)) /\
   (evaluate st env [Let xo e1 e2] =
      match fix_clock st (evaluate st env [e1]) with
        (st',Rval v) ->
          evaluate st' (sem_env_v_fupd (combin_K (nsOptBind xo (HD v) (sem_env_v env))) env)
            [e2]
      | (st',Rerr v8) -> (st',Rerr v8)) /\
   (evaluate st env [Letrec funs e] =
      if ALL_DISTINCT (MAP (\xyz. match xyz with (x,y,z) -> x) funs) then
        evaluate st (sem_env_v_fupd (combin_K (build_rec_env funs env (sem_env_v env))) env)
          [e]
      else (st,Rerr (Rabort Rtype_error))) /\
   (evaluate st env [Tannot e t] = evaluate st env [e])`;;

let EVALAUX_evaluate_clauses2 =
  `(evaluate (st:(FFI)state) (env:v sem_env) [Lannot e l]
      :(FFI)state # (v list,v)result) =
   evaluate st env [e]`;;

let EVALAUX_evaluate_clauses3 =
  `(evaluate_match (st:(FFI)state) (env:v sem_env) (v:v) [] err_v =
      (st,Rerr (Rraise err_v):(v list,v)result)) /\
   (evaluate_match st env v (CONS (p,(e:exp)) pes) err_v =
      if ALL_DISTINCT (pat_bindings p) then
        (match pmatch (sem_env_c env) (state_refs st) p v [] with
           No_match -> evaluate_match st env v pes err_v
         | Match_type_error -> (st,Rerr (Rabort Rtype_error))
         | Match env_v' ->
             evaluate st (sem_env_v_fupd (combin_K (nsAppend (alist_to_ns env_v') (sem_env_v env)))
                            env) [e])
      else (st,Rerr (Rabort Rtype_error)))`;;

let EVALAUX_evaluate_clauses4 =
  `(evaluate_decs (st:(FFI)state) (env:v sem_env) [] =
      (st,Rval (sem_env_REC nsEmpty nsEmpty):(v sem_env,v)result)) /\
   (evaluate_decs st env (CONS d1 (CONS d2 ds)) =
      match fix_clock st (evaluate_decs st env [d1]) with
        (st1,Rval env1) ->
          (match evaluate_decs st1 (extend_dec_env env1 env) (CONS d2 ds) with
             (st2,r) -> (st2,combine_dec_result env1 r))
      | (st1,Rerr v7) -> (st1,Rerr v7)) /\
   (evaluate_decs st env [Dlet locs p e] =
      if ALL_DISTINCT (pat_bindings p) /\ every_exp (one_con_check (sem_env_c env)) e
      then
        (match evaluate st env [e] with
           (st',Rval v) ->
             (st',
              (match pmatch (sem_env_c env) (state_refs st') p (HD v) [] with
                 No_match -> Rerr (Rraise bind_exn_v)
               | Match_type_error -> Rerr (Rabort Rtype_error)
               | Match new_vals -> Rval (sem_env_REC (alist_to_ns new_vals) nsEmpty)))
         | (st',Rerr err) -> (st',Rerr err))
      else (st,Rerr (Rabort Rtype_error))) /\
   (evaluate_decs st env [Dletrec locs funs] =
      (st,
       if ALL_DISTINCT (MAP (\xyz. match xyz with (x,y,z) -> x) funs) /\
          ALL (\fne. match fne with
                       (f,n,e) -> every_exp (one_con_check (sem_env_c env)) e) funs
       then Rval (sem_env_REC (build_rec_env funs env nsEmpty) nsEmpty)
       else Rerr (Rabort Rtype_error))) /\
   (evaluate_decs st env [Dtype locs tds] =
      if ALL check_dup_ctors tds then
        (state_next_type_stamp_fupd (combin_K (state_next_type_stamp st + LENGTH tds)) st,
         Rval (sem_env_REC nsEmpty (build_tdefs (state_next_type_stamp st) tds)))
      else (st,Rerr (Rabort Rtype_error))) /\
   (evaluate_decs st env [Dtabbrev locs tvs tn t] =
      (st,Rval (sem_env_REC nsEmpty nsEmpty))) /\
   (evaluate_decs st env [Denv n] =
      match declare_env (state_eval_state st) env with
        NONE -> (st,Rerr (Rabort Rtype_error))
      | SOME (x,es') ->
          (state_eval_state_fupd (combin_K es') st,Rval (sem_env_REC (nsSing n x) nsEmpty))) /\
   (evaluate_decs st env [Dexn locs cn ts] =
      (state_next_exn_stamp_fupd (combin_K (state_next_exn_stamp st + 1)) st,
       Rval (sem_env_REC nsEmpty
               (nsSing cn (LENGTH ts,ExnStamp (state_next_exn_stamp st)))))) /\
   (evaluate_decs st env [Dmod mn ds] =
      match evaluate_decs st env ds with
        (st',r) ->
          (st',
           (match r with
              Rval env' ->
                Rval (sem_env_REC (nsLift mn (sem_env_v env'))
                                  (nsLift mn (sem_env_c env')))
            | Rerr err -> Rerr err))) /\
   (evaluate_decs st env [Dlocal lds ds] =
      match fix_clock st (evaluate_decs st env lds) with
        (st1,Rval env1) -> evaluate_decs st1 (extend_dec_env env1 env) ds
      | (st1,Rerr v7) -> (st1,Rerr v7))`;;

(* The clauses in HOL4's order *)

let EVALAUX_evaluate_clauses =
  list_mk_conj (conjuncts EVALAUX_evaluate_clauses1 @ [EVALAUX_evaluate_clauses2] @
                conjuncts EVALAUX_evaluate_clauses3 @
                conjuncts EVALAUX_evaluate_clauses4);;

(* HOL4's termination relation:                                              *)
(*   inv_image ($< LEX $<) (\x. case x of                                   *)
(*     | INL (s,_,es) => (s.clock,list_size exp_size es)                    *)
(*     | INR (INL (s,_,_,pes,_)) =>                                          *)
(*         (s.clock,list_size (pair_size pat_size exp_size) pes)             *)
(*     | INR (INR (s,_,ds)) => (s.clock,list_size dec_size ds))             *)

let EVALAUX_evaluate_rel =
  `inv_image ((<) LEX (<))
     (\x:((FFI)state # v sem_env # exp list) +
         (((FFI)state # v sem_env # v # (pat # exp) list # v) +
          ((FFI)state # v sem_env # dec list)).
        sum_CASE x (\t. state_clock (FST t),list_size exp_size (SND (SND t)))
          (\y. sum_CASE y
                 (\t. state_clock (FST t),
                      list_size (pair_size ast_pat_size exp_size)
                        (FST (SND (SND (SND t)))))
                 (\t. state_clock (FST t),list_size dec_size (SND (SND t)))))`;;

(* HOL4 evaluate_def (the first one, with fix_clock); defined with          *)
(* sem1aux_def_wf (the kit's casewise package would need hours for the 28   *)
(* clauses); about 7 minutes                                                 *)

let EVALAUX_evaluate_fix_def =
  sem1aux_def_wf EVALAUX_evaluate_rel EVALAUX_TC_TAC EVALAUX_evaluate_clauses;;

(* ------------------------------------------------------------------------- *)
(* The induction theorem (HOL4's first evaluate_ind).  sem1aux_def derives   *)
(* it only for one or two functions (its sem1aux_mutual_ind does not reduce  *)
(* the nested sum cases of three); this is its step 5 with that fixed.      *)
(* ------------------------------------------------------------------------- *)

let EVALAUX_mutual_ind (fns:term list) (ns:int list) (argtups:hol_type list)
                       (ind:thm) =
  let k = length fns in
  let ps = map2 (fun f ty ->
                   let atys = fst(chop_list (el (index f fns) ns)
                                    (fst(splitlist dest_fun_ty (type_of f)))) in
                   mk_var("P"^fst(dest_var f),itlist mk_fun_ty atys bool_ty))
                fns argtups in
  let pfun i =
    let n = el i ns in
    let t = mk_var("t_mr",el i argtups) in
    mk_abs(t,list_mk_comb(el i ps,if n = 1 then [t] else tuple_selectors n t)) in
  let rec qterm l i = match l with
      [_] -> pfun i
    | _::rest ->
        let s = mk_var("s_mr",mk_sum_ty l) in
        let a = pfun i and b = qterm rest (i+1) in
        mk_abs(s,list_mk_icomb "sum_CASE" [s;a;b])
    | [] -> failwith "EVALAUX_mutual_ind" in
  let th1 = ISPEC (qterm argtups 0) ind in
  let th2 = CONV_RULE (TOP_DEPTH_CONV (BETA_CONV ORELSEC
                         GEN_REWRITE_CONV I [sum_CASE; FST; SND])) th1 in
  let rec split_conv l = match l with
      [] | [_] -> ALL_CONV
    | _::rest -> GEN_REWRITE_CONV I [SUM_CASE_FORALL] THENC
                 RAND_CONV (BINDER_CONV BETA_CONV THENC split_conv rest) in
  let th3 = CONV_RULE (RAND_CONV (split_conv argtups THENC
                                  TOP_DEPTH_CONV BETA_CONV)) th2 in
  let concl_conv =
    let rec go i tm =
      if i = k - 1 then FORALL_TUPLE_CONV (el i ns) tm
      else let l,r = dest_conj tm in
           MK_CONJ (FORALL_TUPLE_CONV (el i ns) l) (go (i+1) r) in
    go 0 in
  let th4 = CONV_RULE (RAND_CONV (concl_conv THENC
                                  PURE_REWRITE_CONV[FST; SND])) th3 in
  let rename_binders tm =
    let rec go i tm =
      if is_forall tm then
        let v = fst(dest_forall tm) in
        (GEN_ALPHA_CONV (mk_var("x"^string_of_int i,type_of v)) THENC
         BINDER_CONV (go (i+1))) tm
      else REFL tm in
    go 1 tm in
  let th5 = CONV_RULE (RAND_CONV (DEPTH_BINOP_CONV `(/\)` rename_binders)) th4 in
  GENL ps th5;;

(* the clause-shaped induction theorem of a mutual sem1aux definition from  *)
(* its clauses, relation and termination tactic (sem1aux_def_gen, step 5)    *)

let EVALAUX_mutual_clause_ind (rel:term) (tac:tactic) (tm:term) =
  let tm1 = complete_all_clauses (rename_wildcards (cases_of_matches tm)) in
  let cls1 = dest_clauses tm1 in
  let rec order acc l = match l with
      [] -> rev acc
    | (_,f,_,_)::t -> if mem f acc then order acc t else order (f::acc) t in
  let fns = order [] cls1 in
  let arity f = match find (fun (_,g,_,_) -> g = f) cls1 with
                  (_,_,args,_) -> length args in
  let ns = map arity fns in
  let tm2 = itlist2 (fun f k t -> eta_expand_bare k f t) fns ns tm1 in
  let cls = dest_clauses (close_clauses fns tm2) in
  let sigs = map2 (fun f n -> let tys,r = splitlist dest_fun_ty (type_of f) in
                              let a,b = chop_list n tys in
                              a, itlist mk_fun_ty b r) fns ns in
  let consts = map (fun f -> let c = mk_const(fst(dest_var f),[]) in
                             inst (type_match (type_of c) (type_of f) []) c) fns in
  let csubst = zip consts fns in
  let argtups = map (fun (a,_) -> mk_tuple_ty a) sigs in
  let sty = mk_sum_ty argtups in
  let r = inst (type_match (fst(dest_fun_ty(type_of rel))) sty []) rel in
  let enc i args = mk_sum_inj argtups i (mk_tuple_term args) in
  let tcs = flat (map (fun (vs,f,args,rhs_) ->
      let i = index f fns in
      let calls = sem1aux_calls fns (vs @ fns) rhs_ in
      map (fun (ctx,call) ->
             let g,cargs = strip_comb call in
             let j = index g fns in
             let rr = mk_comb(mk_comb(r,enc j cargs),enc i args) in
             let body = if ctx = [] then rr else mk_imp(list_mk_conj(rev ctx),rr) in
             let body = vsubst csubst body in
             list_mk_forall(frees_in_order body,body)) calls) cls) in
  let tc_thms = map (fun tc -> prove(tc,tac)) (setify tcs) in
  let wfth = prove(mk_comb(mk_const("WF",[sty,aty]),r),WF_TAC) in
  let c = mk_var("sem1aux_enc",mk_fun_ty sty bool_ty) in
  let ecls = map (fun (vs,f,args,_) -> vs,[enc (index f fns) args]) cls in
  let ind0 = derive_induction c ecls tc_thms wfth in
  CONV_RULE sem1aux_rename_marked_conv (EVALAUX_mutual_ind fns ns argtups ind0);;

let EVALAUX_evaluate_fix_ind =
  EVALAUX_mutual_clause_ind EVALAUX_evaluate_rel EVALAUX_TC_TAC
    EVALAUX_evaluate_clauses;;

let () =
  cake_ind_store := ["evaluate",EVALAUX_evaluate_fix_ind;
                     "evaluate_match",EVALAUX_evaluate_fix_ind;
                     "evaluate_decs",EVALAUX_evaluate_fix_ind] @ !cake_ind_store;;

(* ------------------------------------------------------------------------- *)
(* Tidy up evaluate_def and evaluate_ind.                                    *)
(* ------------------------------------------------------------------------- *)

(* HOL4: ho_match_mp_tac evaluate_ind >> rw[evaluate_def] >>                 *)
(* gvs [AllCaseEqs()] >> fs[dec_clock_def,fix_clock_def] >> simp[] >>       *)
(* imp_res_tac fix_clock_IMP >> fs[] >> COND_CASES_TAC >> gs[]              *)

(* the case equations of the types the clauses split on (all_case_eqs()   *)
(* works too, five times slower)                                            *)
let EVALAUX_clock_case_eqs =
  [pair_case_eq; option_case_eq; list_case_eq; COND_CASE_EQ] @
  map case_eq ["result"; "error_result"; "op_class"; "dest_thunk_ret";
               "thunk_mode"; "match_result"; "exp_or_val"];;

let EVALAUX_CLOCK_TAC (def:thm) : tactic =
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[def] THEN
  DISCH_TAC THEN GVS(EVALAUX_clock_case_eqs @ [dec_clock_def]) THEN
  ASSUM_LIST (fun ths -> MAP_EVERY ASSUME_TAC (mapfilter (MATCH_MP fix_clock_IMP) ths)) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (EVALAUX_is_num_fact o concl))) THEN
  REWRITE_TAC[state_INFO.ri_accfupds; K_THM] THEN ARITH_TAC;;

let evaluate_clock = prove
 (`(!(s1:(FFI)state) env e r s2.
      evaluate s1 env e = (s2,r) ==> state_clock s2 <= state_clock s1) /\
   (!(s1:(FFI)state) env v p v' r s2.
      evaluate_match s1 env v p v' = (s2,r) ==> state_clock s2 <= state_clock s1) /\
   (!(s1:(FFI)state) env ds r s2.
      evaluate_decs s1 env ds = (s2,r) ==> state_clock s2 <= state_clock s1)`,
  MATCH_MP_TAC EVALAUX_evaluate_fix_ind THEN REPEAT CONJ_TAC THEN
  EVALAUX_CLOCK_TAC EVALAUX_evaluate_fix_def);;

let fix_clock_do_eval_res = prove
 (`!(s:(FFI)state) vs.
     fix_clock s (do_eval_res vs s) =
     (do_eval_res vs s:(FFI)state # (v sem_env # dec list,A)result)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[do_eval_res_def] THEN
  CASES_ON `do_eval vs (state_eval_state (s:(FFI)state))` THEN
  REWRITE_TAC[option_CASE] THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[fix_clock_def; state_INFO.ri_accfupds; K_THM; LE_REFL; PAIR_EQ] THEN
  REWRITE_TAC[state_component_equality; state_INFO.ri_accfupds; K_THM]);;

let EVALAUX_fix_clock_id = prove
 (`!(s:(A)state) (x:(B)state#C).
     state_clock (FST x) <= state_clock s ==> fix_clock s x = x`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `x:(B)state#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s':(B)state` (X_CHOOSE_THEN `r:C` SUBST1_TAC)) THEN
  REWRITE_TAC[fix_clock_def; FST; PAIR_EQ] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[state_component_equality; state_INFO.ri_accfupds; K_THM]);;

let fix_clock_evaluate = prove
 (`!(s1:(FFI)state) env e ds.
     fix_clock s1 (evaluate s1 env e) = evaluate s1 env e /\
     fix_clock s1 (evaluate_decs s1 env ds) = evaluate_decs s1 env ds`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC EVALAUX_fix_clock_id THEN
  MESON_TAC[evaluate_clock; PAIR]);;

let full_evaluate_def =
  REWRITE_RULE[fix_clock_evaluate; fix_clock_do_eval_res] EVALAUX_evaluate_fix_def;;

let full_evaluate_ind =
  REWRITE_RULE[fix_clock_evaluate; fix_clock_do_eval_res] EVALAUX_evaluate_fix_ind;;

(* store evaluate_def and evaluate_ind in parts *)

let EVALAUX_conjs_of names th =
  end_itlist CONJ
    (filter (fun c -> let f = fst(strip_comb(lhs(snd(strip_forall(concl c))))) in
                      mem (fst(dest_const f)) names)
            (CONJUNCTS th));;

(* HOL4 rebinds evaluate_def to these clauses (evaluate and evaluate_match) *)
let evaluate_def = EVALAUX_conjs_of ["evaluate"; "evaluate_match"] full_evaluate_def;;

let evaluate_match_def = EVALAUX_conjs_of ["evaluate_match"] full_evaluate_def;;

let evaluate_decs_def = EVALAUX_conjs_of ["evaluate_decs"] full_evaluate_def;;

(* HOL4 rebinds evaluate_ind to this one (evaluate and evaluate_match) *)
let evaluate_ind =
  GENL [`P1:(FFI)state->v sem_env->exp list->bool`;
        `P2:(FFI)state->v sem_env->v->(pat#exp)list->v->bool`]
   (REWRITE_RULE[]
     (SPECL [`P1:(FFI)state->v sem_env->exp list->bool`;
             `P2:(FFI)state->v sem_env->v->(pat#exp)list->v->bool`;
             `\(v1:(FFI)state) (v2:v sem_env) (v3:dec list). T`] full_evaluate_ind));;

let evaluate_match_ind =
  GEN `P2:(FFI)state->v sem_env->v->(pat#exp)list->v->bool`
   (REWRITE_RULE[]
     (SPECL [`\(v1:(FFI)state) (v2:v sem_env) (v3:exp list). T`;
             `P2:(FFI)state->v sem_env->v->(pat#exp)list->v->bool`;
             `\(v1:(FFI)state) (v2:v sem_env) (v3:dec list). T`] full_evaluate_ind));;

let evaluate_decs_ind =
  GEN `P:(FFI)state->v sem_env->dec list->bool`
   (REWRITE_RULE[]
     (SPECL [`\(v1:(FFI)state) (v2:v sem_env) (v3:exp list). T`;
             `\(v1:(FFI)state) (v2:v sem_env) (v3:v) (v4:(pat#exp)list) (v5:v). T`;
             `P:(FFI)state->v sem_env->dec list->bool`] full_evaluate_ind));;

(* cake_ind returns HOL4's final induction theorems *)
let () =
  cake_ind_store := ["evaluate",evaluate_ind; "evaluate_match",evaluate_match_ind;
                     "evaluate_decs",evaluate_decs_ind] @ !cake_ind_store;;
