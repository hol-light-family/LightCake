(* ========================================================================= *)
(* clos_to_bvlProof_p2: part 2 of 3 (HOL4 lines 3433-6083) of the port of   *)
(* HOL4 compiler/backend/proofs/clos_to_bvlProofScript.sml (CakeML v3479).   *)
(* Correctness proof for clos_to_bvl.                                        *)
(* The parts _p1 ... _p3 are loaded one after the other (each needs the     *)
(* previous one); see the header of clos_to_bvlProof_p1.ml for the notes on *)
(* the rendering.                                                            *)
(* ========================================================================= *)

needs "compiler/backend/proofs/clos_to_bvlProof_p1.ml";;

prioritize_num();;
type_invention_error := true;;

(* C2BP2AUX_ names are local helpers. *)
(* ===== PART 2: HOL4 lines 3433-6083 ===== *)

(* ------------------------------------------------------------------------- *)
(* Helpers for compile_exps_correct (HOL4 lines 3433-5666).                   *)
(* ------------------------------------------------------------------------- *)

(* Using an induction hypothesis !vs. A1 /\ ... /\ An ==> C (also with      *)
(* implications and quantifiers nested in the conclusion): the variables vs  *)
(* are instantiated by matching the Ai against the assumptions (in any       *)
(* order, until nothing changes; pre gives instances by variable name), and  *)
(* the instance Ai' ==> C' is given to ttac, with the Ai' that are           *)
(* assumptions removed (HOL4's drule_all with the rest left to impl_tac).    *)
let C2BP2AUX_IH_INST pre ih asl =
  let ih0 = REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] ih in
  let vs0,_ = strip_forall (concl ih0) in
  let asms = map (concl o snd) asl in
  let maeqs = map snd (filter (fun (_,th) ->
      let c = concl th in
      is_eq c && is_comb (lhs c) && is_const (rator (lhs c)) &&
      fst(dest_const(rator(lhs c))) = "clos_state_max_app") asl) in
  let normconv = REWRITE_CONV([HD; TL] @ maeqs) in
  (* the bound variables renamed apart from the free variables around *)
  let avoid = freesl (concl ih0 :: asms @ flat (map (hyp o snd) asl)) in
  let vs = rev(snd(itlist (fun v (av,acc) -> let v' = variant av v in (v'::av, v'::acc))
                          (rev vs0) (avoid,[]))) in
  let ih' = CONV_RULE (fun t -> let body = snd(strip_forall t) in
                         ALPHA t (list_mk_forall(vs,vsubst (zip vs vs0) body))) ih0 in
  let vs,body = strip_forall (concl ih') in
  let ant,_ = dest_imp body in
  let cs = conjuncts ant in
  let inst0 = map (fun (t,n) ->
      let i = index (find (fun v -> fst(dest_var v) = n) vs0) vs0 in (t,el i vs)) pre in
  let rec loop inst =
    let rest = filter (fun v -> not (exists (fun (_,v') -> v' = v) inst)) vs in
    if rest = [] then inst else
    let try_c c =
      let c' = rhs(concl(normconv (vsubst inst c))) in
      if not (exists (fun v -> vfree_in v c') rest) then None else
      let fixed = subtract (frees c') rest in
      let rec try_a l = match l with
          [] -> None
        | a::t ->
            (try let _,tmin,tyin = term_match fixed c' a in
                 if exists (fun (t1,t2) -> t1 <> t2) tyin then try_a t else
                 if forall (fun (_,v) -> mem v rest) tmin then
                   Some (map (fun v -> (try rev_assoc v tmin with Failure _ -> v),v)
                             (filter (fun v -> vfree_in v c') rest))
                 else try_a t
             with Failure _ -> try_a t) in
      try_a asms in
    let rec first l = match l with [] -> None | c::t -> (match try_c c with Some x -> Some x | None -> first t) in
    match first cs with
      None -> failwith ("C2BP2AUX_IH_INST: uninstantiated " ^ String.concat " " (map (fst o dest_var) rest))
    | Some tmin -> loop (tmin @ inst) in
  let inst = loop inst0 in
  let th = SPECL (map (fun v -> rev_assoc v inst) vs) ih' in
  let a,c = dest_imp (concl th) in
  let normth t = normconv t in
  let norm t = rhs(concl(normth t)) in
  let in_asl t = exists (aconv (norm t)) asms in
  let from_asl t = EQ_MP (SYM (normth t))
                     (snd(find (fun (_,th) -> aconv (concl th) (norm t)) asl)) in
  let keep = filter (fun t -> not (in_asl t)) (conjuncts a) in
  if keep = [] then MP th (end_itlist CONJ (map from_asl (conjuncts a)))
  else
    let k = list_mk_conj keep in
    let th2 = DISCH k (MP th (end_itlist CONJ (map (fun t ->
                 if exists (aconv t) keep then
                   (let ks = CONJUNCTS (ASSUME k) in find (fun th -> aconv (concl th) t) ks)
                 else from_asl t) (conjuncts a)))) in
    th2;;

let C2BP2AUX_IH_THEN pre (pick:term->bool) (ttac:thm_tactic) : tactic = fun (asl,w as g) ->
  let ihs = filter (fun (_,th) -> pick (concl th)) asl in
  tryfind (fun (_,ih) -> ttac (C2BP2AUX_IH_INST pre ih asl) g) ihs;;

(* an induction hypothesis of compile_exps_correct: its conclusion (under   *)
(* quantifiers and implications) is ?ck res' t2 f2. ...                     *)
let C2BP2AUX_is_ih t =
  let rec concl_of t =
    if is_forall t then concl_of (snd(dest_forall t))
    else if is_imp t then concl_of (snd(dest_imp t)) else t in
  let c = concl_of t in
  is_exists c && fst(dest_var(fst(dest_exists c))) = "ck";;

let C2BP2AUX_IH_TAC pre = C2BP2AUX_IH_THEN pre C2BP2AUX_is_ih MP_TAC;;

(* the same for the induction hypotheses in which tm occurs *)
let C2BP2AUX_IH_ON_TAC tm pre =
  C2BP2AUX_IH_THEN pre (fun t -> C2BP2AUX_is_ih t && free_in tm t) MP_TAC;;

(* rewrite everything with the assumptions max_app s' = max_app s (HOL4's   *)
(* imp_res_tac evaluate_const \\ fs [])                                      *)
let C2BP2AUX_MAX_APP_TAC : tactic = fun (asl,w as g) ->
  let is_ma t = try is_eq t && fst(dest_const(fst(strip_comb(lhs t)))) = "clos_state_max_app"
                with Failure _ -> false in
  let ths = map snd (filter (fun (_,th) -> is_ma (concl th)) asl) in
  if ths = [] then ALL_TAC g else
  (RULE_ASSUM_TAC(fun th -> if is_ma (concl th) then th else REWRITE_RULE ths th) THEN
   REWRITE_TAC ths) g;;

(* the same for the induction hypotheses in which a constant of this name occurs *)
let C2BP2AUX_IH_ON_CONST_TAC name pre =
  C2BP2AUX_IH_THEN pre (fun t -> C2BP2AUX_is_ih t &&
    can (find_term (fun u -> is_const u && fst(dest_const u) = name)) t) MP_TAC;;

(* MP_TAC of an instance of th, its antecedents matched against the        *)
(* assumptions (as for an induction hypothesis)                             *)
let C2BP2AUX_MP_INST_TAC pre th : tactic = fun (asl,w as g) ->
  MP_TAC (C2BP2AUX_IH_INST pre th asl) g;;

(* helpers for compile_exps_correct: moving the relations to bigger maps,  *)
(* refs and code, and adding to the clock                                   *)

let C2BP2AUX_v_rel_mono = prove
 (`!max_app f1 refs1 code1 f2 refs2 code2 x y.
     clos_to_bvlProof_v_rel max_app f1 refs1 code1 x y /\
     f1 SUBMAP f2 /\ FDIFF refs1 (FRANGE f1) SUBMAP FDIFF refs2 (FRANGE f2) /\
     subspt code1 code2
     ==> clos_to_bvlProof_v_rel max_app f2 refs2 code2 x y`,
  MESON_TAC[clos_to_bvlProof_v_rel_SUBMAP; clos_to_bvlProof_v_rel_subspt]);;

let C2BP2AUX_ALL2_v_rel_mono = prove
 (`!max_app f1 refs1 code1 f2 refs2 code2 xs ys.
     ALL2 (clos_to_bvlProof_v_rel max_app f1 refs1 code1) xs ys /\
     f1 SUBMAP f2 /\ FDIFF refs1 (FRANGE f1) SUBMAP FDIFF refs2 (FRANGE f2) /\
     subspt code1 code2
     ==> ALL2 (clos_to_bvlProof_v_rel max_app f2 refs2 code2) xs ys`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th ->
    fst(dest_const(fst(strip_comb(concl th)))) = "ALL2")) THEN
  MATCH_MP_TAC MONO_ALL2 THEN ASM_MESON_TAC[C2BP2AUX_v_rel_mono]);;

let C2BP2AUX_env_rel_mono = prove
 (`!max_app f1 refs1 code1 f2 refs2 code2 xs ys.
     clos_to_bvlProof_env_rel max_app f1 refs1 code1 xs ys /\
     f1 SUBMAP f2 /\ FDIFF refs1 (FRANGE f1) SUBMAP FDIFF refs2 (FRANGE f2) /\
     subspt code1 code2
     ==> clos_to_bvlProof_env_rel max_app f2 refs2 code2 xs ys`,
  MESON_TAC[clos_to_bvlProof_env_rel_SUBMAP; env_rel_subspt]);;

let C2BP2AUX_bvl_evaluate_add_clock = prove
 (`!xs env (t:(C,FFI)bvl_state) c ck res t2 ck'.
     bvl_evaluate (xs,env,bvl_state_clock_fupd (combin_K (c + ck)) t) = (res,t2) /\
     ~(res = Rerr (Rabort Rtimeout_error))
     ==> bvl_evaluate (xs,env,bvl_state_clock_fupd (combin_K (c + ck + ck')) t) =
         (res,bvl_state_clock_fupd (combin_K (bvl_state_clock t2 + ck')) t2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`xs:bvl_exp list`; `env:bvl_v list`;
                 `bvl_state_clock_fupd (combin_K (c + ck)) (t:(C,FFI)bvl_state)`;
                 `res:(bvl_v list,bvl_v)result`; `t2:(C,FFI)bvl_state`]
                bvl_evaluate_add_clock) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `ck':num`) THEN
  REWRITE_TAC[bvl_inc_clock_def; bvl_state_INFO.ri_accfupds; bvl_state_INFO.ri_fupdfupds;
              K_THM; K_o_THM; ADD_ASSOC]);;

let C2BP2AUX_bvl_evaluate_add_clock2 = prove
 (`!xs env (t:(C,FFI)bvl_state) c ck res t2 c2 ck'.
     bvl_evaluate (xs,env,bvl_state_clock_fupd (combin_K (c + ck)) t) = (res,t2) /\
     ~(res = Rerr (Rabort Rtimeout_error)) /\ bvl_state_clock t2 = c2
     ==> bvl_evaluate (xs,env,bvl_state_clock_fupd (combin_K (c + ck + ck')) t) =
         (res,bvl_state_clock_fupd (combin_K (c2 + ck')) t2)`,
  MESON_TAC[C2BP2AUX_bvl_evaluate_add_clock]);;

let C2BP2AUX_bvl_evaluate_add_clock_Rval = prove
 (`!xs env (t:(C,FFI)bvl_state) c ck v t2.
     bvl_evaluate (xs,env,bvl_state_clock_fupd (combin_K (c + ck)) t) = (Rval v,t2)
     ==> !ck'. bvl_evaluate (xs,env,bvl_state_clock_fupd (combin_K (c + ck + ck')) t) =
               (Rval v,bvl_state_clock_fupd (combin_K (bvl_state_clock t2 + ck')) t2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C2BP2AUX_bvl_evaluate_add_clock THEN
  ASM_REWRITE_TAC[distinctness "result"]);;

let C2BP2AUX_bvl_evaluate_add_clock_Rraise = prove
 (`!xs env (t:(C,FFI)bvl_state) c ck v t2.
     bvl_evaluate (xs,env,bvl_state_clock_fupd (combin_K (c + ck)) t) = (Rerr (Rraise v),t2)
     ==> !ck'. bvl_evaluate (xs,env,bvl_state_clock_fupd (combin_K (c + ck + ck')) t) =
               (Rerr (Rraise v),bvl_state_clock_fupd (combin_K (bvl_state_clock t2 + ck')) t2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C2BP2AUX_bvl_evaluate_add_clock THEN
  ASM_REWRITE_TAC[distinctness "result"; injectivity "result"; distinctness "error_result"]);;

let C2BP2AUX_result_cases = prove
 (`!r:(A,B)result. (?vs. r = Rval vs) \/ (?v. r = Rerr (Rraise v)) \/
                   (?a. r = Rerr (Rabort a))`,
  GEN_TAC THEN CASES_ON `r:(A,B)result` THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"] THENL
   [MESON_TAC[];
    CASES_ON `a:(B)error_result` THEN
    REWRITE_TAC[injectivity "error_result"; distinctness "error_result"] THEN MESON_TAC[]]);;

let C2BP2AUX_state_rel_code = prove
 (`!f (s:(C,FFI)clos_state) (t:(C,FFI)bvl_state) name arity c.
     clos_to_bvlProof_state_rel f s t /\ FLOOKUP (clos_state_code s) name = SOME (arity,c)
     ==> ?aux1 c2 aux2.
           clos_to_bvl_compile_exps (clos_state_max_app s) [c] aux1 = ([c2],aux2) /\
           lookup (name + num_stubs (clos_state_max_app s)) (bvl_state_code t) =
             SOME (arity,c2) /\
           clos_to_bvlProof_code_installed aux2 (bvl_state_code t)`,
  REWRITE_TAC[clos_to_bvlProof_state_rel_def] THEN MESON_TAC[]);;

let C2BP2AUX_ALL2_IMP_env_rel = prove
 (`!xs ys max_app f refs code.
     ALL2 (clos_to_bvlProof_v_rel max_app f refs code) xs ys
     ==> clos_to_bvlProof_env_rel max_app f refs code xs ys`,
  MESON_TAC[list_rel_IMP_env_rel; APPEND_NIL]);;

(* the second evaluation of a sequence: the induction hypothesis on tm      *)
(* (state t2, map f2 and bvl environment env' of the first step), its side  *)
(* conditions, the clock ck + ck' of both steps and the result              *)
let C2BP2AUX_is_eval_ck' th =
  try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "bvl_evaluate" &&
      free_in `ck':num` (concl th)
  with Failure _ -> false;;

let C2BP2AUX_head t = try fst(dest_const(fst(strip_comb t))) with Failure _ -> "";;

(* env_rel in a bigger state: from an assumption on the same environments, *)
(* or for APPEND vs env from the relation of vs and env_rel of env          *)
let rec C2BP2AUX_ENV_REL_TAC (asl,w as g) =
  let _,args = strip_comb w in
  let m = el 0 args and e1 = el 4 args and e2 = el 5 args in
  let ok th = let c = concl th in C2BP2AUX_head c = "clos_to_bvlProof_env_rel" &&
              (let _,a = strip_comb c in el 0 a = m && el 4 a = e1 && el 5 a = e2) in
  try
    let th = snd(find (fun (_,th) -> ok th) asl) in
    let _,a = strip_comb (concl th) in
    (MATCH_MP_TAC C2BP2AUX_env_rel_mono THEN
     MAP_EVERY EXISTS_TAC [el 1 a; el 2 a; el 3 a] THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[SUBMAP_TRANS; subspt_trans]) g
  with Failure _ ->
    if exists (fun (_,th) -> let c = concl th in C2BP2AUX_head c = "ALL2" &&
                 (let _,a = strip_comb c in el 1 a = e1 && el 2 a = e2)) asl then
      (MATCH_MP_TAC C2BP2AUX_ALL2_IMP_env_rel THEN FIRST_ASSUM ACCEPT_TAC) g
    else if is_cons e1 then
      (REWRITE_TAC[clos_to_bvlProof_env_rel_def] THEN CONJ_TAC THENL
        [FIRST_ASSUM ACCEPT_TAC; C2BP2AUX_ENV_REL_TAC]) g
    else
      (MATCH_MP_TAC clos_to_bvlProof_env_rel_APPEND THEN CONJ_TAC THENL
        [FIRST_ASSUM ACCEPT_TAC; C2BP2AUX_ENV_REL_TAC]) g;;

(* every_Fn_SOME [e] (or every_Fn_vs_SOME) from FEVERY on a code map and a  *)
(* FLOOKUP of e in it                                                       *)
let C2BP2AUX_FEVERY_TAC : tactic = fun (asl,w as g) ->
  let fes = filter (fun (_,th) -> C2BP2AUX_head (concl th) = "FEVERY") asl in
  let fls = filter (fun (_,th) -> is_eq (concl th) &&
                                  C2BP2AUX_head (lhs(concl th)) = "FLOOKUP") asl in
  let cands = flat (map (fun (_,fe) -> mapfilter (fun (_,fl) ->
      CONV_RULE (TOP_DEPTH_CONV BETA_CONV THENC REWRITE_CONV[SND])
        (MATCH_MP FEVERY_FLOOKUP (CONJ fe fl))) fls) fes) in
  MAP_FIRST ACCEPT_TAC cands g;;

(* v_rel or ALL2 v_rel in a bigger state, from an assumption on the same    *)
(* values (in a smaller state)                                              *)
let C2BP2AUX_V_REL_TAC : tactic = fun (asl,w as g) ->
  let is_all2 = C2BP2AUX_head w = "ALL2" in
  let rel t = if is_all2 then hd(snd(strip_comb t)) else t in
  let vals t = let _,a = strip_comb t in
               if is_all2 then tl a else [el 4 a; el 5 a] in
  let m = el 0 (snd(strip_comb (rel w))) in
  let ok th = let c = concl th in
    C2BP2AUX_head c = C2BP2AUX_head w &&
    (not is_all2 || C2BP2AUX_head (rel c) = "clos_to_bvlProof_v_rel") &&
    vals c = vals w && el 0 (snd(strip_comb (rel c))) = m in
  let th = snd(find (fun (_,th) -> ok th) asl) in
  let _,a = strip_comb (rel (concl th)) in
  (MATCH_MP_TAC (if is_all2 then C2BP2AUX_ALL2_v_rel_mono else C2BP2AUX_v_rel_mono) THEN
   MAP_EVERY EXISTS_TAC [el 1 a; el 2 a; el 3 a] THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[SUBMAP_TRANS; subspt_trans]) g;;

(* side conditions of an induction hypothesis: not a type error (from the   *)
(* hypothesis on the result), code_installed and env_rel in a bigger state *)
let C2BP2AUX_SIDE_TAC : tactic =
  let one (asl,w as g) =
    if is_neg w then (DISCH_THEN SUBST_ALL_TAC THEN FS[]) g
    else if C2BP2AUX_head w = "clos_to_bvlProof_code_installed" then
      ASM_MESON_TAC[code_installed_subspt; subspt_trans] g
    else if C2BP2AUX_head w = "clos_to_bvlProof_env_rel" then C2BP2AUX_ENV_REL_TAC g
    else if C2BP2AUX_head w = "clos_to_bvlProof_state_rel" then
      (ASM_REWRITE_TAC[clos_to_bvlProof_state_rel_clock; clos_dec_clock_def;
                       bvl_dec_clock_def]) g
    else if mem (C2BP2AUX_head w) ["every_Fn_SOME"; "every_Fn_vs_SOME"] then
      C2BP2AUX_FEVERY_TAC g
    else if C2BP2AUX_head w = "clos_to_bvlProof_v_rel" ||
            (C2BP2AUX_head w = "ALL2" &&
             C2BP2AUX_head (hd(snd(strip_comb w))) = "clos_to_bvlProof_v_rel") then
      C2BP2AUX_V_REL_TAC g
    else ALL_TAC g in
  let ma_tac (asl,w as g) =
    let maeqs = map snd (filter (fun (_,th) ->
        let c = concl th in
        is_eq c && is_comb (lhs c) && is_const (rator (lhs c)) &&
        fst(dest_const(rator(lhs c))) = "clos_state_max_app") asl) in
    REWRITE_TAC (HD :: TL :: maeqs) g in
  REPEAT CONJ_TAC THEN ma_tac THEN one;;



let C2BP2AUX_FINISH_TAC f3 =
  FS[] THEN EXISTS_TAC f3 THEN ASM_REWRITE_TAC[] THEN
  (* what is left is a chain of SUBMAP facts: MESON with those alone first *)
  (* (ASM_MESON_TAC with all the assumptions took 2 s and more)             *)
  (fun (asl,w as g) ->
     let subs = filter (fun th -> is_binary "SUBMAP" (concl th)) (map snd asl) in
     (MESON_TAC (SUBMAP_TRANS :: subs) ORELSE ASM_MESON_TAC[SUBMAP_TRANS]) g);;

(* a case split whose hypothesis also rewrites the assumptions *)
let C2BP2AUX_ASM_CASES_TAC t =
  ASM_CASES_TAC t THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th);;

(* the same with the instantiation computed from the goal *)


(* the raised bvl value y of an assumption bvl_evaluate .. = (Rerr (Rraise y),_) *)
let C2BP2AUX_bvl_raised (asl,w) =
  let ok th = let c = concl th in
    is_eq c && C2BP2AUX_head (lhs c) = "bvl_evaluate" &&
    (try let r = fst(dest_pair(rhs c)) in
         C2BP2AUX_head r = "Rerr" && C2BP2AUX_head (rand r) = "Rraise"
     with Failure _ -> false) in
  let th = snd(find (fun (_,th) -> ok th) asl) in
  rand(rand(fst(dest_pair(rhs(concl th)))));;

(* after an induction hypothesis was MP_TAC'd: prove its remaining side      *)
(* conditions, if any                                                       *)
let C2BP2AUX_ANTS_TAC : tactic = fun (asl,w as g) ->
  if is_imp w && is_imp (fst(dest_imp w)) then (ANTS_TAC THENL [C2BP2AUX_SIDE_TAC; ALL_TAC]) g
  else ALL_TAC g;;

let C2BP2AUX_STEP2_TAC tm t2 f2 env2 =
  C2BP2AUX_IH_ON_TAC tm [(t2,"t1"); (f2,"f1"); (env2,"env'")] THEN
  C2BP2AUX_ANTS_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `ck':num` (X_CHOOSE_THEN `r2:(bvl_v list,bvl_v)result`
   (X_CHOOSE_THEN `t3:(C,FFI)bvl_state` (X_CHOOSE_THEN `f3:(num,num)fmap`
    STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `ck + ck'` THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[HD; bvl_Boolv_11] THEN
  FIRST_X_ASSUM(MP_TAC o check C2BP2AUX_is_eval_ck') THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[];;

let C2BP2AUX_STEP2_TAC_F tm f : tactic = fun g ->
  let t2,f2,env2 = f g in C2BP2AUX_STEP2_TAC tm t2 f2 env2 g;;

(* case split on tm with the equation also rewriting the assumptions *)
let C2BP2AUX_CASES_ON tm =
  CASES_ON tm THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th);;

(* split a pair variable p into (v1,v2) with the given names *)
let C2BP2AUX_PAIR_CASES_TAC p v1 v2 =
  MP_TAC(ISPEC p PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN v1 (X_CHOOSE_THEN v2 SUBST_ALL_TAC));;

(* the value y of an assumption bvl_evaluate (xs,..) = (Rval [y],_), xs given *)
let C2BP2AUX_bvl_val1 xs (asl,w) =
  let ok th = let c = concl th in
    is_eq c && C2BP2AUX_head (lhs c) = "bvl_evaluate" &&
    (try fst(dest_pair(rand(lhs c))) = xs &&
         let r = fst(dest_pair(rhs c)) in
         C2BP2AUX_head r = "Rval" && length (dest_list (rand r)) = 1
     with Failure _ -> false) in
  let th = snd(find (fun (_,th) -> ok th) asl) in
  hd(dest_list(rand(fst(dest_pair(rhs(concl th))))));;

let C2BP2AUX_IH_ON_CONST_TAC_F name f : tactic = fun g ->
  C2BP2AUX_IH_ON_CONST_TAC name (f g) g;;

(* substitute the assumptions v = t for the variables v with these names *)
let C2BP2AUX_SUBST_VARS_TAC names =
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    let c = concl th in
    is_eq c && is_var (lhs c) && mem (fst(dest_var(lhs c))) names &&
    not (vfree_in (lhs c) (rhs c)))));;

let C2BP2AUX_eval_Fn_code = prove
 (`!vs env (t:(C,FFI)bvl_state) ys k p tag.
     bvl_evaluate (MAP bvl_Var vs,env,t) = (Rval ys,t) /\ p IN domain (bvl_state_code t)
     ==> bvl_evaluate
           ([bvl_Op (BlockOp (clos_Cons tag))
              (APPEND (APPEND (REVERSE (MAP bvl_Var vs)) [bvl_Op (IntOp (clos_Const k)) []])
                 [bvl_Op (clos_Label p) []])],env,t) =
         (Rval [bvl_Block tag (CONS (bvl_CodePtr p) (CONS (bvl_Number k) ys))],t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP evaluate_var_reverse) THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  ASM_REWRITE_TAC[bvl_evaluate_APPEND] THEN CAKE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN REWRITE_TAC[bvl_evaluate_def] THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[REVERSE_APPEND; REVERSE; REVERSE_REVERSE; APPEND] THEN
  REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[CONJUNCT1 bvl_do_int_app_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE_APPEND; REVERSE; REVERSE_REVERSE; APPEND]);;

let C2BP2AUX_code_installed_CONS = prove
 (`!n a e aux code.
     clos_to_bvlProof_code_installed (CONS (n,a,e) aux) code <=>
     lookup n code = SOME (a,e) /\ clos_to_bvlProof_code_installed aux code`,
  REWRITE_TAC[clos_to_bvlProof_code_installed_def; ALL] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let C2BP2AUX_v_rel_Fn = prove
 (`!max_app f refs code loc env ys num_args exp aux d aux1.
     ALL2 (clos_to_bvlProof_v_rel max_app f refs code) env ys /\
     num_args <= max_app /\ ~(num_args = 0) /\
     every_Fn_SOME [exp] /\ every_Fn_vs_SOME [exp] /\
     clos_to_bvl_compile_exps max_app [exp] aux = ([d],aux1) /\
     clos_to_bvlProof_code_installed aux1 code /\
     lookup (loc + num_stubs max_app) code =
       SOME (num_args + 1,
             bvl_Let (APPEND (list_of_seq bvl_Var num_args)
                        (free_let (bvl_Var num_args) (LENGTH env))) d)
     ==> clos_to_bvlProof_v_rel max_app f refs code
           (clos_Closure (SOME loc) [] env num_args exp)
           (bvl_Block closure_tag
              (CONS (bvl_CodePtr (loc + num_stubs max_app))
                 (CONS (bvl_Number (&(num_args - 1))) ys)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (el 5 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
  EXISTS_TAC `env:clos_v list` THEN EXISTS_TAC `ys:bvl_v list` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (el 0 (CONJUNCTS cl_rel_rules)) THEN
  MAP_EVERY EXISTS_TAC [`aux:(num#num#bvl_exp)list`; `d:bvl_exp`;
                        `aux1:(num#num#bvl_exp)list`] THEN
  ASM_REWRITE_TAC[]);;

let C2BP2AUX_app_NONE = prove
 (`!c2 d env (s:(C,FFI)bvl_state) vs s1 y s2.
     bvl_evaluate (c2,env,s) = (Rval vs,s1) /\
     bvl_evaluate ([d],env,s1) = (Rval [y],s2)
     ==> bvl_evaluate ([bvl_Let (APPEND c2 [d])
                         (mk_cl_call (bvl_Var (LENGTH vs)) (list_of_seq bvl_Var (LENGTH vs)))],
                       env,s) =
         bvl_evaluate ([mk_cl_call (bvl_Var (LENGTH vs)) (list_of_seq bvl_Var (LENGTH vs))],
                       APPEND (APPEND vs [y]) env,s2)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  ASM_REWRITE_TAC[bvl_evaluate_APPEND] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

let C2BP2AUX_app_SOME = prove
 (CASE_TERM `!c2 d env (s:(C,FFI)bvl_state) vs s1 y s2 l.
     bvl_evaluate (c2,env,s) = (Rval vs,s1) /\
     bvl_evaluate ([d],env,s1) = (Rval [y],s2) /\ ~(vs = [])
     ==> bvl_evaluate ([bvl_Call (LENGTH vs - 1) (SOME l) (APPEND c2 [d])],env,s) =
         (match bvl_find_code (SOME l) (APPEND vs [y]) (bvl_state_code s2) with
            NONE -> (Rerr (Rabort Rtype_error),s2)
          | SOME (args,exp) ->
              if bvl_state_clock s2 < LENGTH vs
              then (Rerr (Rabort Rtimeout_error),bvl_state_clock_fupd (combin_K 0) s2)
              else bvl_evaluate ([exp],args,
                     bvl_state_clock_fupd (combin_K (bvl_state_clock s2 - LENGTH vs)) s2))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  ASM_REWRITE_TAC[bvl_evaluate_APPEND] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(LENGTH (vs:bvl_v list) - 1) + 1 = LENGTH vs` SUBST1_TAC THENL
   [UNDISCH_TAC `~(vs:bvl_v list = [])` THEN REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[bvl_dec_clock_def]);;

let C2BP2AUX_LENGTH_LT_APPEND = prove
 (`!(l:A list) x l2. LENGTH l < LENGTH (APPEND (APPEND l [x]) l2)`,
  REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC);;

let C2BP2AUX_EL_CONS_ONE = prove
 (`!(a:A) b l. EL 1 (CONS a (CONS b l)) = b`,
  REWRITE_TAC[num_CONV `1`; EL; HD; TL]);;

let C2BP2AUX_eval_genlist_vars_cl = prove
 (`!args' x env (t:(C,FFI)bvl_state).
     ~(LENGTH args' = 0)
     ==> bvl_evaluate (APPEND (list_of_seq bvl_Var (LENGTH args')) [bvl_Var (LENGTH args')],
                       APPEND (APPEND args' [x]) env,t) = (Rval (APPEND args' [x]),t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvl_evaluate_APPEND] THEN
  MP_TAC(ISPECL [`args':bvl_v list`; `APPEND [x:bvl_v] env`; `t:(C,FFI)bvl_state`]
    evaluate_simple_genlist_vars) THEN
  ASM_REWRITE_TAC[LT_NZ; APPEND_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN
  CAKE_REWRITE_TAC[bvl_evaluate_def; el_append3; C2BP2AUX_LENGTH_LT_APPEND]);;

let C2BP2AUX_mk_cl_call_partial = prove
 (`!args' tag ptr m rest env (t:(C,FFI)bvl_state) max_app.
     ~(LENGTH args' = 0) /\ ~(m = &(LENGTH args' - 1)) /\
     lookup (generic_app_fn_location (LENGTH args' - 1)) (bvl_state_code t) =
       SOME (LENGTH args' + 1,generate_generic_app max_app (LENGTH args' - 1))
     ==> bvl_evaluate
           ([mk_cl_call (bvl_Var (LENGTH args')) (list_of_seq bvl_Var (LENGTH args'))],
            APPEND (APPEND args'
              [bvl_Block tag (CONS (bvl_CodePtr ptr) (CONS (bvl_Number m) rest))]) env,t) =
         if bvl_state_clock t = 0
         then (Rerr (Rabort Rtimeout_error),bvl_state_clock_fupd (combin_K 0) t)
         else bvl_evaluate ([generate_generic_app max_app (LENGTH args' - 1)],
                APPEND args' [bvl_Block tag (CONS (bvl_CodePtr ptr) (CONS (bvl_Number m) rest))],
                bvl_dec_clock 1 t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mk_cl_call_def; LENGTH_LIST_OF_SEQ] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  REWRITE_TAC[bvl_evaluate_def; el_append3; C2BP2AUX_LENGTH_LT_APPEND] THEN
  REPEAT(CHANGED_TAC(CAKE_REWRITE_TAC[REVERSE; APPEND; C2BP1AUX_do_app_ElemAt; LENGTH;
    ARITH_RULE `1 < SUC (SUC n)`; C2BP2AUX_EL_CONS_ONE; C2BP1AUX_do_app_EqualConst_Int; HD] THEN
    ASM_REWRITE_TAC[bvl_Boolv_11])) THEN
  ASM_SIMP_TAC[C2BP2AUX_eval_genlist_vars_cl] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[bvl_find_code_def; LENGTH_APPEND; LENGTH] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `x < 0 + 1 <=> x = 0`; ARITH_RULE `0 + 1 = 1`; GSYM ONE] THEN
  CAKE_REWRITE_TAC[]);;

let C2BP2AUX_v_rel_partial_rule = prove
 (`!max_app f refs code env fvs arg_env ys num_args cl cl_app cl' loc_arg num_arg.
     ALL2 (clos_to_bvlProof_v_rel max_app f refs code) env fvs /\
     ALL2 (clos_to_bvlProof_v_rel max_app f refs code) arg_env ys /\
     ~(arg_env = []) /\
     LENGTH arg_env < num_args /\
     lookup (partial_app_fn_location max_app (num_args - 1) (LENGTH ys - 1)) code =
       SOME ((num_args - LENGTH arg_env) + 1,
             generate_partial_app_closure_fn (num_args - 1) (LENGTH ys - 1)) /\
     add_args cl arg_env = SOME cl_app /\
     get_num_args cl = SOME num_args /\
     cl_rel max_app (FRANGE f) refs code (env,fvs) cl cl' /\
     loc_arg = partial_app_fn_location max_app (num_args - 1) (LENGTH ys - 1) /\
     num_arg = &((num_args - 1) - LENGTH arg_env)
     ==> clos_to_bvlProof_v_rel max_app f refs code cl_app
           (bvl_Block partial_app_tag
              (CONS (bvl_CodePtr loc_arg) (CONS (bvl_Number num_arg) (CONS cl' ys))))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (el 6 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
  MAP_EVERY EXISTS_TAC [`env:clos_v list`; `fvs:bvl_v list`; `cl:clos_v`] THEN
  ASM_REWRITE_TAC[]);;

(* the value of a partial application (HOL4: the Partial application case *)
(* of compile_exps_correct, the result part)                             *)
let C2BP2AUX_v_rel_partial = prove
 (`!max_app f refs code func args args' tag ptr n rest c prev_args total_args clo.
     clos_to_bvlProof_v_rel max_app f refs code func
       (bvl_Block tag (CONS (bvl_CodePtr ptr) (CONS (bvl_Number (&n - &1)) rest))) /\
     num_remaining_args func = SOME n /\ SOME c = add_args func args /\ LENGTH args < n /\
     ~(args = []) /\
     ALL2 (clos_to_bvlProof_v_rel max_app f refs code) args args' /\
     unpack_closure (bvl_Block tag (CONS (bvl_CodePtr ptr) (CONS (bvl_Number (&n - &1)) rest)))
       (prev_args,total_args,clo) /\
     n = (total_args - LENGTH prev_args) + 1 /\ total_args < max_app /\
     (tag = closure_tag
      ==> prev_args = [] /\
          clo = bvl_Block tag (CONS (bvl_CodePtr ptr) (CONS (bvl_Number (&n - &1)) rest))) /\
     lookup (partial_app_fn_location max_app total_args (LENGTH prev_args + (LENGTH args' - 1)))
       code =
       SOME ((total_args - (LENGTH prev_args + (LENGTH args' - 1))) + 1,
             generate_partial_app_closure_fn total_args
               (LENGTH prev_args + (LENGTH args' - 1)))
     ==> clos_to_bvlProof_v_rel max_app f refs code c
           (bvl_Block partial_app_tag
              (CONS (bvl_CodePtr (partial_app_fn_location max_app total_args
                                    (LENGTH prev_args + (LENGTH args' - 1))))
                 (CONS (bvl_Number (&(total_args - (LENGTH prev_args + LENGTH args'))))
                    (CONS clo (APPEND args' prev_args)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> C2BP2AUX_head (concl th) = "clos_to_bvlProof_v_rel")) THEN
  GEN_REWRITE_TAC LAND_CONV [clos_to_bvlProof_v_rel_cases] THEN
  REWRITE_TAC[distinctness "bvl_v"; injectivity "bvl_v"; CONS_11] THEN
  STRIP_TAC THEN RVEQ_TAC THENL
   [FS[num_remaining_args_def];
    (FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
       RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; SUB_0; APPEND_NIL; ADD_CLAUSES]) THEN
       REWRITE_TAC[LENGTH; SUB_0; APPEND_NIL; ADD_CLAUSES]) THEN
    (FIRST_ASSUM(ASSUME_TAC o MATCH_MP cl_rel_get_num_args) THEN
       IMP_RES_TAC LIST_REL_LENGTH THEN
       MATCH_MP_TAC C2BP2AUX_v_rel_partial_rule THEN
       MAP_EVERY EXISTS_TAC [`env:clos_v list`; `fvs:bvl_v list`; `args:clos_v list`;
         `total_args + 1`; `func:clos_v`] THEN
       ASM_REWRITE_TAC[ADD_SUB] THEN
       REWRITE_TAC[injectivity "option"; PAIR_EQ; INT_OF_NUM_EQ] THEN
       MAP_EVERY UNDISCH_TAC [`LENGTH (args:clos_v list) = LENGTH (args':bvl_v list)`;
         `~(args:clos_v list = [])`; `LENGTH (args:clos_v list) < total_args + 1`] THEN
       REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC);
    (FIRST_X_ASSUM(MP_TAC o check (fun th -> C2BP2AUX_head (concl th) = "unpack_closure")) THEN
       ONCE_REWRITE_TAC[unpack_closure_cases] THEN
       REWRITE_TAC[injectivity "bvl_v"; CONS_11; PAIR_EQ; partial_app_tag_neq_closure_tag] THEN
       STRIP_TAC THEN RVEQ_TAC THEN
       IMP_RES_TAC LIST_REL_LENGTH THEN
       FIRST_X_ASSUM(fun th -> if is_eq (concl th) && rhs (concl th) = `rem_args:int`
                                then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
       FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
                                                      lhs (concl th) = `rem_args:int`)) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[NUM_OF_INT_OF_NUM]) THEN REWRITE_TAC[NUM_OF_INT_OF_NUM]) THEN
    (SUBGOAL_THEN `(num_args - 1 - LENGTH (arg_env:clos_v list)) + LENGTH (prev_args':bvl_v list) =
                     num_args - 1` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
        [UNDISCH_TAC `LENGTH (arg_env:clos_v list) = LENGTH (prev_args':bvl_v list)` THEN
         UNDISCH_TAC `LENGTH (arg_env:clos_v list) < num_args` THEN ARITH_TAC; ALL_TAC] THEN
       MATCH_MP_TAC C2BP2AUX_v_rel_partial_rule THEN
       MAP_EVERY EXISTS_TAC [`env:clos_v list`; `fvs:bvl_v list`;
         `APPEND (args:clos_v list) arg_env`; `num_args:num`; `cl:clos_v`] THEN
       ASM_REWRITE_TAC[APPEND_EQ_NIL; LENGTH_APPEND] THEN
       SUBGOAL_THEN `LENGTH (args:clos_v list) + LENGTH (arg_env:clos_v list) < num_args /\
                     ~(LENGTH (args':bvl_v list) = 0)` STRIP_ASSUME_TAC THENL
        [MAP_EVERY UNDISCH_TAC [`LENGTH (args:clos_v list) = LENGTH (args':bvl_v list)`;
           `LENGTH (arg_env:clos_v list) = LENGTH (prev_args':bvl_v list)`;
           `~(args:clos_v list = [])`; `LENGTH (arg_env:clos_v list) < num_args`] THEN
         FIRST_X_ASSUM(MP_TAC o check (fun th -> C2BP2AUX_head (concl th) = "<" &&
                                         lhand (concl th) = `LENGTH (args:clos_v list)`)) THEN
         REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC; ALL_TAC] THEN
       ASM_REWRITE_TAC[] THEN
       SUBGOAL_THEN `LENGTH (prev_args':bvl_v list) + LENGTH (args':bvl_v list) - 1 =
                     (LENGTH args' + LENGTH prev_args') - 1 /\
                     (num_args - 1) - ((LENGTH args' + LENGTH prev_args') - 1) + 1 =
                     num_args - (LENGTH args' + LENGTH prev_args') + 1 /\
                     LENGTH args' + LENGTH prev_args' < num_args /\
                     num_args - 1 - (LENGTH prev_args' + LENGTH args') =
                     num_args - 1 - (LENGTH args' + LENGTH prev_args')`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
        [MAP_EVERY UNDISCH_TAC [`LENGTH (args:clos_v list) = LENGTH (args':bvl_v list)`;
           `LENGTH (arg_env:clos_v list) = LENGTH (prev_args':bvl_v list)`;
           `LENGTH (args:clos_v list) + LENGTH (arg_env:clos_v list) < num_args`;
           `~(LENGTH (args':bvl_v list) = 0)`] THEN ARITH_TAC;
         ALL_TAC]) THEN
    (ASM_REWRITE_TAC[]) THEN
    (CONJ_TAC THENL [MATCH_MP_TAC LIST_REL_APPEND_suff THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    (FIRST_ASSUM(fun th -> if C2BP2AUX_head (lhs (concl th)) = "add_args" &&
                                C2BP2AUX_head (rhs (concl th)) = "SOME"
                             then MATCH_ACCEPT_TAC(MATCH_MP add_args_append th) else NO_TAC))]);;

let C2BP2AUX_state_rel_generic = prove
 (`!f (s:(C,FFI)clos_state) (t:(C,FFI)bvl_state) k.
     clos_to_bvlProof_state_rel f s t /\ ~(k = 0) /\ k <= clos_state_max_app s
     ==> lookup (generic_app_fn_location (k - 1)) (bvl_state_code t) =
         SOME (k + 1,generate_generic_app (clos_state_max_app s) (k - 1))`,
  REWRITE_TAC[clos_to_bvlProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k - 1` o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "n" &&
        C2BP2AUX_head (rand(snd(dest_forall(concl th)))) = "=" with Failure _ -> false)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN ASM_ARITH_TAC);;

let C2BP2AUX_state_rel_partial = prove
 (`!f (s:(C,FFI)clos_state) (t:(C,FFI)bvl_state) tot n.
     clos_to_bvlProof_state_rel f s t /\ tot < clos_state_max_app s /\ n < tot
     ==> lookup (partial_app_fn_location (clos_state_max_app s) tot n) (bvl_state_code t) =
         SOME ((tot - n) + 1,generate_partial_app_closure_fn tot n)`,
  REWRITE_TAC[clos_to_bvlProof_state_rel_def] THEN MESON_TAC[]);;

(* HOL4: the Partial application case of compile_exps_correct, as a lemma *)
let C2BP2AUX_app_partial = prove
 (`!loc_opt func args (s1:(C,FFI)clos_state) res s2 env (t1:(C,FFI)bvl_state) args' func' f1 c.
     dest_closure (clos_state_max_app s1) loc_opt func args = SOME (Partial_app c) /\
     (if clos_state_clock s1 < LENGTH args
      then (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (combin_K 0) s1)
      else (Rval [c],clos_dec_clock (LENGTH args) s1)) = (res,s2) /\
     clos_to_bvlProof_v_rel (clos_state_max_app s1) f1 (bvl_state_refs t1) (bvl_state_code t1)
       func func' /\
     ALL2 (clos_to_bvlProof_v_rel (clos_state_max_app s1) f1 (bvl_state_refs t1)
             (bvl_state_code t1)) args args' /\
     clos_to_bvlProof_state_rel f1 s1 t1 /\ ~(LENGTH args' = 0)
     ==> loc_opt = NONE /\
         ?ck res' t2 f2.
           bvl_evaluate ([mk_cl_call (bvl_Var (LENGTH args')) (list_of_seq bvl_Var (LENGTH args'))],
                         APPEND (APPEND args' [func']) env,
                         bvl_state_clock_fupd (combin_K (clos_state_clock s1 + ck)) t1) = (res',t2) /\
           result_rel (ALL2 (clos_to_bvlProof_v_rel (clos_state_max_app s1) f2
                               (bvl_state_refs t2) (bvl_state_code t2)))
             (clos_to_bvlProof_v_rel (clos_state_max_app s1) f2 (bvl_state_refs t2)
                (bvl_state_code t2)) res res' /\
           clos_to_bvlProof_state_rel f2 s2 t2 /\ f1 SUBMAP f2 /\
           FDIFF (bvl_state_refs t1) (FRANGE f1) SUBMAP FDIFF (bvl_state_refs t2) (FRANGE f2) /\
           clos_state_clock s2 = bvl_state_clock t2`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN IMP_RES_TAC LIST_REL_LENGTH THEN
     SUBGOAL_THEN `~(LENGTH (args:clos_v list) = 0)` ASSUME_TAC THENL
      [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o MATCH_MP dest_closure_part_app o
       CONJ (ASSUME `~(LENGTH (args:clos_v list) = 0)`) o
       check (fun th -> C2BP2AUX_head (lhs (concl th)) = "dest_closure")) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     FIRST_ASSUM(MP_TAC o MATCH_MP v_rel_num_rem_args o
       CONJ (ASSUME `clos_to_bvlProof_v_rel (clos_state_max_app (s1:(C,FFI)clos_state)) f1 (bvl_state_refs (t1:(C,FFI)bvl_state))
                       (bvl_state_code (t1:(C,FFI)bvl_state)) func func'`) o
       check (fun th -> C2BP2AUX_head (lhs (concl th)) = "num_remaining_args")) THEN
     STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES]) THEN
  (MP_TAC(ISPECL [`args':bvl_v list`; `tag:num`; `ptr:num`; `&n - &1:int`; `rest:bvl_v list`;
       `env:bvl_v list`;
       `bvl_state_clock_fupd (combin_K (clos_state_clock (s1:(C,FFI)clos_state))) (t1:(C,FFI)bvl_state)`;
       `clos_state_max_app (s1:(C,FFI)clos_state)`] C2BP2AUX_mk_cl_call_partial) THEN
     ANTS_TAC THENL
      [ASM_REWRITE_TAC[bvl_state_INFO.ri_accfupds] THEN CONJ_TAC THENL
        [SUBGOAL_THEN `&n - &1:int = &(n - 1)` SUBST1_TAC THENL
          [MATCH_MP_TAC INT_OF_NUM_SUB THEN UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC; ALL_TAC] THEN
         REWRITE_TAC[INT_OF_NUM_EQ] THEN
         MAP_EVERY UNDISCH_TAC [`LENGTH (args:clos_v list) < n`;
           `LENGTH (args:clos_v list) = LENGTH (args':bvl_v list)`;
           `~(LENGTH (args:clos_v list) = 0)`] THEN ARITH_TAC;
         MATCH_MP_TAC C2BP2AUX_state_rel_generic THEN
         EXISTS_TAC `f1:(num,num)fmap` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
       DISCH_THEN SUBST1_TAC]) THEN
  (REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM; bvl_state_INFO.ri_fupdfupds; K_o_THM] THEN
     FIRST_ASSUM(fun vth -> FIRST_ASSUM(fun nth ->
       MP_TAC(MATCH_MP unpack_closure_thm (CONJ vth nth)))) THEN
     STRIP_TAC THEN
     C2BP2AUX_ASM_CASES_TAC `clos_state_clock (s1:(C,FFI)clos_state) = 0` THEN
     ASM_REWRITE_TAC[]) THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[LT_NZ; ASSUME `~(LENGTH (args:clos_v list) = 0)`]) THEN
      FS[] THEN RVEQ_TAC THEN FS[] THEN EXISTS_TAC `f1:(num,num)fmap` THEN
      ASM_REWRITE_TAC[SUBMAP_REFL];
    (FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) && lhs (concl th) = `n:num`)) THEN
       SUBGOAL_THEN `LENGTH (prev_args:bvl_v list) + (LENGTH (args':bvl_v list) - 1) < total_args /\
                     LENGTH args' < (total_args + 1) - LENGTH prev_args`
         STRIP_ASSUME_TAC THENL
        [MAP_EVERY UNDISCH_TAC [`LENGTH (args:clos_v list) < total_args - LENGTH (prev_args:bvl_v list) + 1`;
           `LENGTH (args:clos_v list) = LENGTH (args':bvl_v list)`;
           `~(LENGTH (args:clos_v list) = 0)`] THEN ARITH_TAC; ALL_TAC] THEN
       MP_TAC(ISPECL [`total_args:num`; `prev_args:bvl_v list`;
         `bvl_dec_clock 1 (bvl_state_clock_fupd (combin_K (clos_state_clock (s1:(C,FFI)clos_state)))
            (t1:(C,FFI)bvl_state))`;
         `args':bvl_v list`;
         `bvl_Block tag (CONS (bvl_CodePtr ptr)
            (CONS (bvl_Number (&(total_args - LENGTH (prev_args:bvl_v list) + 1) - &1)) rest))`;
         `clo:bvl_v`; `clos_state_max_app (s1:(C,FFI)clos_state)`] evaluate_generic_app_partial) THEN
       ANTS_TAC THENL
        [ASM_REWRITE_TAC[bvl_dec_clock_def; bvl_state_INFO.ri_accfupds; domain_lookup] THEN
         CONJ_TAC THENL
          [EXISTS_TAC `(total_args - (LENGTH (prev_args:bvl_v list) + (LENGTH (args':bvl_v list) - 1))) + 1,
                       generate_partial_app_closure_fn total_args
                         (LENGTH prev_args + (LENGTH args' - 1))` THEN
           MATCH_MP_TAC C2BP2AUX_state_rel_partial THEN EXISTS_TAC `f1:(num,num)fmap` THEN
           ASM_REWRITE_TAC[];
           ASM_MESON_TAC[clos_to_bvlProof_state_rel_globals]];
         DISCH_THEN SUBST1_TAC]) THEN
    (REWRITE_TAC[bvl_dec_clock_def; bvl_state_INFO.ri_accfupds; K_THM;
                   bvl_state_INFO.ri_fupdfupds; K_o_THM] THEN
       SUBGOAL_THEN `(clos_state_clock (s1:(C,FFI)clos_state) - 1 < LENGTH (args':bvl_v list) - 1 <=>
                      clos_state_clock s1 < LENGTH (args:clos_v list)) /\
                     (clos_state_clock s1 - 1) - (LENGTH args' - 1) =
                     clos_state_clock s1 - LENGTH args`
         (fun th -> REWRITE_TAC[th]) THENL
        [MAP_EVERY UNDISCH_TAC [`~(clos_state_clock (s1:(C,FFI)clos_state) = 0)`;
           `LENGTH (args:clos_v list) = LENGTH (args':bvl_v list)`;
           `~(LENGTH (args:clos_v list) = 0)`] THEN ARITH_TAC; ALL_TAC] THEN
       C2BP2AUX_ASM_CASES_TAC `clos_state_clock (s1:(C,FFI)clos_state) < LENGTH (args:clos_v list)` THEN
       ASM_REWRITE_TAC[] THEN FS[] THEN RVEQ_TAC THEN
       FS[clos_dec_clock_def] THEN EXISTS_TAC `f1:(num,num)fmap` THEN
       ASM_REWRITE_TAC[SUBMAP_REFL]) THEN
    (SUBGOAL_THEN `~(args:clos_v list = [])` ASSUME_TAC THENL
        [ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL]; ALL_TAC] THEN
       MATCH_MP_TAC C2BP2AUX_v_rel_partial THEN
       MAP_EVERY EXISTS_TAC [`func:clos_v`; `args:clos_v list`; `tag:num`; `ptr:num`;
         `total_args - LENGTH (prev_args:bvl_v list) + 1`; `rest:bvl_v list`] THEN
       ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
        [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
         MATCH_MP_TAC C2BP2AUX_state_rel_partial THEN EXISTS_TAC `f1:(num,num)fmap` THEN
         ASM_REWRITE_TAC[]])]);;

let C2BP2AUX_every_Fn_EL = prove
 (`!(exps:(num#clos_exp)list) k na ex.
     k < LENGTH exps /\ EL k exps = (na,ex)
     ==> (every_Fn_SOME (MAP SND exps) ==> every_Fn_SOME [ex]) /\
         (every_Fn_vs_SOME (MAP SND exps) ==> every_Fn_vs_SOME [ex])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `MEM (na:num,ex:clos_exp) exps` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM_EL]; ALL_TAC] THEN
  CONJ_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [every_Fn_SOME_EVERY; every_Fn_vs_SOME_EVERY] THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(na:num,ex:clos_exp)`) THEN ASM_REWRITE_TAC[SND]);;

(* the body of a closure that dest_closure applies satisfies every_Fn_SOME *)
(* and every_Fn_vs_SOME (HOL4: a step of the Full_app case)                *)
let C2BP2AUX_dest_closure_every_Fn = prove
 (`!max_app loc func args e l rest f refs code func'.
     dest_closure max_app loc func args = SOME (Full_app e l rest) /\
     clos_to_bvlProof_v_rel max_app f refs code func func'
     ==> every_Fn_SOME [e] /\ every_Fn_vs_SOME [e]`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[dest_closure_def] THEN
     CASES_ON `func:clos_v` THEN CAKE_REWRITE_TAC[] THEN
     ONCE_REWRITE_TAC[clos_to_bvlProof_v_rel_cases] THEN
     REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"]) THENL
   [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      REPEAT COND_CASES_TAC THEN REWRITE_TAC[injectivity "option"; distinctness "option";
        injectivity "app_kind"; distinctness "app_kind"] THEN
      STRIP_TAC THEN RVEQ_TAC THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> C2BP2AUX_head (concl th) = "cl_rel")) THEN
      ONCE_REWRITE_TAC[cl_rel_cases] THEN
      REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"; PAIR_EQ] THEN
      STRIP_TAC THEN RVEQ_TAC THEN FS[add_args_def];
    (MP_TAC(ISPEC `EL a4 (a3:(num#clos_exp)list)` PAIR_SURJECTIVE) THEN
       DISCH_THEN(X_CHOOSE_THEN `na:num` (X_CHOOSE_THEN `ex:clos_exp` ASSUME_TAC)) THEN
       ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
       DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
       REPEAT COND_CASES_TAC THEN REWRITE_TAC[injectivity "option"; distinctness "option";
         injectivity "app_kind"; distinctness "app_kind"] THEN
       STRIP_TAC THEN RVEQ_TAC THEN
       FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
       FIRST_X_ASSUM(MP_TAC o check (fun th -> C2BP2AUX_head (concl th) = "cl_rel")) THEN
       ONCE_REWRITE_TAC[cl_rel_cases] THEN
       REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"; PAIR_EQ] THEN
       STRIP_TAC THEN RVEQ_TAC THEN FS[add_args_def] THEN RVEQ_TAC THEN FS[]) THEN
    (RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LE]) THEN
       FIRST_ASSUM(fun th -> let l,r = dest_eq (concl th) in
         if C2BP2AUX_head l = "EL" then
           let na,ex = dest_pair r in
           MP_TAC(ISPECL [rand l; lhand l; na; ex] C2BP2AUX_every_Fn_EL) THEN
           ASM_REWRITE_TAC[LENGTH_MAP]
         else NO_TAC) THEN
       ASM_SIMP_TAC[])]);;

let C2BP2AUX_mk_cl_call_full = prove
 (CASE_TERM `!(s:(C,FFI)bvl_state) env tag p ra args exp xs max_app.
     lookup p (bvl_state_code s) = SOME (ra + 1,exp) /\
     lookup (generic_app_fn_location (LENGTH args - 1)) (bvl_state_code s) =
       SOME (LENGTH args + 1,generate_generic_app max_app (LENGTH args - 1)) /\
     ra <= LENGTH args /\ ~(ra = 0) /\ LENGTH args <= max_app
     ==> bvl_evaluate
           ([mk_cl_call (bvl_Var (LENGTH args)) (list_of_seq bvl_Var (LENGTH args))],
            APPEND (APPEND args
                      [bvl_Block tag (CONS (bvl_CodePtr p) (CONS (bvl_Number (&(ra - 1))) xs))])
              env,
            s) =
         if ra = LENGTH args then
           if bvl_state_clock s < LENGTH args
           then (Rerr (Rabort Rtimeout_error),bvl_state_clock_fupd (combin_K 0) s)
           else bvl_evaluate
                  ([exp],
                   APPEND args
                     [bvl_Block tag (CONS (bvl_CodePtr p)
                                       (CONS (bvl_Number (&(LENGTH args - 1))) xs))],
                   bvl_dec_clock (LENGTH args) s)
         else
           if bvl_state_clock s < ra + 1
           then (Rerr (Rabort Rtimeout_error),bvl_state_clock_fupd (combin_K 0) s)
           else
             match bvl_evaluate
                     ([exp],
                      APPEND (DROP (LENGTH args - ra) args)
                        [bvl_Block tag (CONS (bvl_CodePtr p) (CONS (bvl_Number (&(ra - 1))) xs))],
                      bvl_dec_clock (ra + 1) s) with
               (Rval [v],st') ->
                 (match bvl_evaluate
                          ([mk_cl_call (bvl_Var 0)
                              (list_of_seq (\n. bvl_Var (n + 1)) (LENGTH args - ra))],
                           CONS v (APPEND args
                                     [bvl_Block tag
                                        (CONS (bvl_CodePtr p)
                                           (CONS (bvl_Number (&(ra - 1))) xs))]),
                           st') with
                    (Rval v,s2) -> (Rval [HD v],s2)
                  | x -> x)
             | x -> x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(C,FFI)bvl_state`; `env:bvl_v list`; `tag:num`; `p:num`; `ra - 1`;
                 `args:bvl_v list`; `exp:bvl_exp`; `xs:bvl_v list`; `max_app:num`]
                evaluate_mk_cl_call_spec) THEN
  SUBGOAL_THEN `(ra - 1) + 2 = ra + 1 /\ (ra - 1 = LENGTH (args:bvl_v list) - 1 <=> ra = LENGTH args) /\
                LENGTH args - ((ra - 1) + 1) = LENGTH args - ra /\
                LENGTH args - 1 >= ra - 1 /\ ra - 1 < max_app /\ ~(LENGTH args = 0)`
    (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY UNDISCH_TAC [`ra <= LENGTH (args:bvl_v list)`; `~(ra = 0)`;
                           `LENGTH (args:bvl_v list) <= max_app`] THEN ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

let C2BP2AUX_bvl_fupd_same = prove
 (`!(t:(C,FFI)bvl_state) c.
     bvl_state_refs_fupd (combin_K (bvl_state_refs t))
       (bvl_state_code_fupd (combin_K (bvl_state_code t)) (bvl_state_clock_fupd (combin_K c) t)) =
     bvl_state_clock_fupd (combin_K c) t`,
  REWRITE_TAC[bvl_state_INFO.ri_component_equality; bvl_state_INFO.ri_accfupds;
              bvl_state_INFO.ri_fupdfupds; K_THM]);;

let C2BP2AUX_ptr_loc = prove
 (`!max_app f refs code func tag ptr k rest x l.
     clos_to_bvlProof_v_rel max_app f refs code func
       (bvl_Block tag (CONS (bvl_CodePtr ptr) (CONS k rest))) /\
     num_remaining_args func = SOME x /\ get_num_args func = SOME x /\ ~(x = 0) /\
     get_loc func = SOME l
     ==> ptr = l + num_stubs max_app`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[clos_to_bvlProof_v_rel_cases] THEN
  REWRITE_TAC[distinctness "bvl_v"; injectivity "bvl_v"; CONS_11] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THENL
   [FS[num_remaining_args_def];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP cl_rel_get_loc) THEN ASM_REWRITE_TAC[injectivity "option"] THEN
    ARITH_TAC;
    FIRST_X_ASSUM(fun th -> FIRST_ASSUM(fun th2 -> FIRST_ASSUM(fun th3 ->
      if C2BP2AUX_head (lhs (concl th)) = "add_args" then
        MP_TAC(MATCH_MP no_partial_args (CONJ th2 (CONJ th3 (CONJ
          (ASSUME `~(x = 0)`) th)))) else NO_TAC))) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* compile_exps_correct by induction on closSem's evaluate: one lemma per     *)
(* case of the induction theorem (the order of clos_evaluate_ind).           *)
(* ------------------------------------------------------------------------- *)

(* the statement of compile_exps_correct (a copy, for the case lemmas)  *)
let C2BP2AUX_cer_stmt = CASE_TERM
  `(!tmp xs env (s1:(C,FFI)clos_state) aux1 (t1:(C,FFI)bvl_state) env' f1 res s2 ys aux2.
      tmp = (xs,env,s1) /\
      clos_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) /\
      clos_to_bvl_compile_exps (clos_state_max_app s1) xs aux1 = (ys,aux2) /\
      every_Fn_SOME xs /\ FEVERY (\p. every_Fn_SOME [SND (SND p)]) (clos_state_code s1) /\
      every_Fn_vs_SOME xs /\ FEVERY (\p. every_Fn_vs_SOME [SND (SND p)]) (clos_state_code s1) /\
      clos_to_bvlProof_code_installed aux2 (bvl_state_code t1) /\
      clos_to_bvlProof_env_rel (clos_state_max_app s1) f1 (bvl_state_refs t1)
        (bvl_state_code t1) env env' /\
      clos_to_bvlProof_state_rel f1 s1 t1
      ==> ?ck res' t2 f2.
            bvl_evaluate (ys,env',bvl_state_clock_fupd (combin_K (clos_state_clock s1 + ck)) t1) =
              (res',t2) /\
            result_rel (ALL2 (clos_to_bvlProof_v_rel (clos_state_max_app s1) f2
                                (bvl_state_refs t2) (bvl_state_code t2)))
              (clos_to_bvlProof_v_rel (clos_state_max_app s1) f2 (bvl_state_refs t2)
                 (bvl_state_code t2)) res res' /\
            clos_to_bvlProof_state_rel f2 s2 t2 /\
            f1 SUBMAP f2 /\
            FDIFF (bvl_state_refs t1) (FRANGE f1) SUBMAP FDIFF (bvl_state_refs t2) (FRANGE f2) /\
            FEVERY (\p. every_Fn_SOME [SND (SND p)]) (clos_state_code s2) /\
            FEVERY (\p. every_Fn_vs_SOME [SND (SND p)]) (clos_state_code s2) /\
            clos_state_clock s2 = bvl_state_clock t2) /\
   (!loc_opt func args (s1:(C,FFI)clos_state) res s2 env (t1:(C,FFI)bvl_state) args' func'
      f1.
      evaluate_app loc_opt func args s1 = (res,s2) /\
      ~(res = Rerr (Rabort Rtype_error)) /\
      FEVERY (\p. every_Fn_SOME [SND (SND p)]) (clos_state_code s1) /\
      FEVERY (\p. every_Fn_vs_SOME [SND (SND p)]) (clos_state_code s1) /\
      clos_to_bvlProof_v_rel (clos_state_max_app s1) f1 (bvl_state_refs t1)
        (bvl_state_code t1) func func' /\
      ALL2 (clos_to_bvlProof_v_rel (clos_state_max_app s1) f1 (bvl_state_refs t1)
              (bvl_state_code t1)) args args' /\
      clos_to_bvlProof_state_rel f1 s1 t1
      ==> ?ck res' t2 f2.
            (~(LENGTH args' = 0)
             ==> (match loc_opt with
                    NONE ->
                      bvl_evaluate
                        ([mk_cl_call (bvl_Var (LENGTH args'))
                            (list_of_seq bvl_Var (LENGTH args'))],
                         APPEND (APPEND args' [func']) env,
                         bvl_state_clock_fupd (combin_K (clos_state_clock s1 + ck)) t1) =
                      (res',t2)
                  | SOME loc ->
                      (match bvl_find_code (SOME (loc + num_stubs (clos_state_max_app s1)))
                               (APPEND args' [func']) (bvl_state_code t1) with
                         NONE -> (Rerr (Rabort Rtype_error),t2)
                       | SOME (args,exp) ->
                           if clos_state_clock s1 + ck < LENGTH args'
                           then (Rerr (Rabort Rtimeout_error),bvl_state_clock_fupd (combin_K 0) t1)
                           else bvl_evaluate
                                  ([exp],args,
                                   bvl_state_clock_fupd
                                     (combin_K ((clos_state_clock s1 + ck) - LENGTH args')) t1)) =
                      (res',t2))) /\
            result_rel (ALL2 (clos_to_bvlProof_v_rel (clos_state_max_app s1) f2
                                (bvl_state_refs t2) (bvl_state_code t2)))
              (clos_to_bvlProof_v_rel (clos_state_max_app s1) f2 (bvl_state_refs t2)
                 (bvl_state_code t2)) res res' /\
            clos_to_bvlProof_state_rel f2 s2 t2 /\
            f1 SUBMAP f2 /\
            FDIFF (bvl_state_refs t1) (FRANGE f1) SUBMAP FDIFF (bvl_state_refs t2) (FRANGE f2) /\
            FEVERY (\p. every_Fn_SOME [SND (SND p)]) (clos_state_code s2) /\
            FEVERY (\p. every_Fn_vs_SOME [SND (SND p)]) (clos_state_code s2) /\
            clos_state_clock s2 = bvl_state_clock t2)`;;

(* the 15 goals of the induction on closSem's evaluate *)
let C2BP2AUX_cer_goals =
  let _,gl,_ = (MATCH_MP_TAC clos_evaluate_ind THEN REPEAT CONJ_TAC) ([],C2BP2AUX_cer_stmt) in
  map snd gl;;

let C2BP2AUX_cer_goal k = el k C2BP2AUX_cer_goals;;

(* the steps at the start of each case: the hypotheses into the            *)
(* assumptions, the tuple equation substituted, the induction hypotheses in *)
(* their simple form                                                         *)
let C2BP2AUX_CER_INTRO_TAC =
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]);;

(* HOL4: THEN1 (* NIL *) *)
let C2BP2AUX_cer_NIL = prove
 (C2BP2AUX_cer_goal 0,
  C2BP2AUX_CER_INTRO_TAC THEN
  FS[clos_evaluate_def; clos_to_bvl_compile_exps_def] THEN RVEQ_TAC THEN
  FS[bvl_evaluate_def] THEN
  MAP_EVERY EXISTS_TAC [`0`; `f1:(num,num)fmap`] THEN
  ASM_REWRITE_TAC[SUBMAP_REFL; ADD_CLAUSES]);;

(* HOL4: THEN1 (* CONS *) *)
let C2BP2AUX_cer_CONS = prove
 (C2BP2AUX_cer_goal 1,
  C2BP2AUX_CER_INTRO_TAC THEN
  FS[clos_evaluate_def; clos_to_bvl_compile_exps_def] THEN
  REPEAT PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN
  IMP_RES_TAC compile_exps_IMP_code_installed THEN
  C2BP2AUX_IH_TAC [] THEN
  ANTS_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN FS[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
   (X_CHOOSE_THEN `t2:(C,FFI)bvl_state` (X_CHOOSE_THEN `f2:(num,num)fmap`
    STRIP_ASSUME_TAC)))) THEN
  REWRITE_TAC[bvl_evaluate_APPEND] THEN
  CASES_ON `x':(clos_v list,clos_v)result` THEN FS[] THENL
   [IMP_RES_TAC evaluate_const THEN IMP_RES_TAC bvl_evaluate_mono THEN FS[] THEN
    C2BP2AUX_MAX_APP_TAC THEN
    C2BP2AUX_IH_ON_TAC `CONS (y:clos_exp) xs`
      [(`t2:(C,FFI)bvl_state`,"t1"); (`f2:(num,num)fmap`,"f1"); (`env'':bvl_v list`,"env'")] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN FS[];
        MATCH_MP_TAC code_installed_subspt THEN
        EXISTS_TAC `bvl_state_code (t1:(C,FFI)bvl_state)` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC C2BP2AUX_env_rel_mono THEN
        MAP_EVERY EXISTS_TAC [`f1:(num,num)fmap`; `bvl_state_refs (t1:(C,FFI)bvl_state)`;
                              `bvl_state_code (t1:(C,FFI)bvl_state)`] THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck':num` (X_CHOOSE_THEN `r2:(bvl_v list,bvl_v)result`
     (X_CHOOSE_THEN `t3:(C,FFI)bvl_state` (X_CHOOSE_THEN `f3:(num,num)fmap`
      STRIP_ASSUME_TAC)))) THEN
    RVEQ_TAC THEN EXISTS_TAC `ck + ck'` THEN
    MP_TAC(ISPECL [`c1:bvl_exp list`; `env'':bvl_v list`; `t1:(C,FFI)bvl_state`;
                   `clos_state_clock (s1:(C,FFI)clos_state)`; `ck:num`;
                   `Rval v':(bvl_v list,bvl_v)result`; `t2:(C,FFI)bvl_state`;
                   `clos_state_clock (s1':(C,FFI)clos_state)`; `ck':num`]
                  C2BP2AUX_bvl_evaluate_add_clock2) THEN
    ASM_REWRITE_TAC[distinctness "result"] THEN DISCH_THEN SUBST1_TAC THEN
    CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    CASES_ON `x:(clos_v list,clos_v)result` THEN FS[] THENL
     [EXISTS_TAC `f3:(num,num)fmap` THEN ASM_REWRITE_TAC[] THEN
      IMP_RES_TAC bvl_evaluate_mono THEN
      RULE_ASSUM_TAC(REWRITE_RULE[bvl_state_INFO.ri_accfupds]) THEN
      IMP_RES_TAC clos_evaluate_SING THEN RVEQ_TAC THEN
      REWRITE_TAC[HD; result_rel_def] THEN REPEAT CONJ_TAC THENL
       [ONCE_REWRITE_TAC[CONS_APPEND] THEN MATCH_MP_TAC LIST_REL_APPEND_suff THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C2BP2AUX_ALL2_v_rel_mono THEN
        MAP_EVERY EXISTS_TAC [`f2:(num,num)fmap`; `bvl_state_refs (t2:(C,FFI)bvl_state)`;
                              `bvl_state_code (t2:(C,FFI)bvl_state)`] THEN
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[SUBMAP_TRANS];
        ASM_MESON_TAC[SUBMAP_TRANS]];
      RVEQ_TAC THEN EXISTS_TAC `f3:(num,num)fmap` THEN
      ASM_REWRITE_TAC[injectivity "result"] THEN ASM_MESON_TAC[SUBMAP_TRANS]];
    RVEQ_TAC THEN MAP_EVERY EXISTS_TAC [`ck:num`; `Rerr e':(bvl_v list,bvl_v)result`;
      `t2:(C,FFI)bvl_state`; `f2:(num,num)fmap`] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN FS[]]);;
(* HOL4: THEN1 (* Var *) *)
let C2BP2AUX_cer_Var = prove
 (C2BP2AUX_cer_goal 2,
  C2BP2AUX_CER_INTRO_TAC THEN
  FS[clos_evaluate_def; clos_to_bvl_compile_exps_def] THEN RVEQ_TAC THEN
  ASM_CASES_TAC `n < LENGTH (env':clos_v list)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  FS[] THEN RVEQ_TAC THEN
  IMP_RES_TAC env_rel_IMP_LENGTH THEN
  SUBGOAL_THEN `n < LENGTH (env'':bvl_v list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[bvl_evaluate_def] THEN EXISTS_TAC `0` THEN
  FS[SUBMAP_REFL; bvl_state_INFO.ri_accfupds] THEN
  EXISTS_TAC `f1:(num,num)fmap` THEN ASM_REWRITE_TAC[SUBMAP_REFL] THEN
  MATCH_MP_TAC env_rel_IMP_EL THEN ASM_REWRITE_TAC[]);;
(* HOL4: THEN1 (* If *) *)
let C2BP2AUX_cer_If = prove
 (C2BP2AUX_cer_goal 3,
  let branch_tac tm =
    RVEQ_TAC THEN FS[] THEN RVEQ_TAC THEN
    C2BP2AUX_STEP2_TAC tm `t2:(C,FFI)bvl_state` `f2:(num,num)fmap` `env'':bvl_v list` THEN
    C2BP2AUX_FINISH_TAC `f3:(num,num)fmap` in
  C2BP2AUX_CER_INTRO_TAC THEN
  FS[clos_evaluate_def; clos_to_bvl_compile_exps_def] THEN
  REPEAT PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN
  IMP_RES_TAC clos_to_bvl_compile_exps_SING THEN RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_exists(concl th) then CAKE_STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  RVEQ_TAC THEN FS[HD] THEN
  IMP_RES_TAC compile_exps_IMP_code_installed THEN
  C2BP2AUX_IH_ON_TAC `[tmp:clos_exp]` [] THEN
  ANTS_TAC THENL [CONJ_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN FS[]; ASM_MESON_TAC[]];
                  ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
   (X_CHOOSE_THEN `t2:(C,FFI)bvl_state` (X_CHOOSE_THEN `f2:(num,num)fmap`
    STRIP_ASSUME_TAC)))) THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  CASES_ON `x:(clos_v list,clos_v)result` THEN FS[] THENL
   [IMP_RES_TAC clos_evaluate_SING THEN RVEQ_TAC THEN FS[LIST_REL_CONS1; LIST_REL_NIL] THEN
    RVEQ_TAC THEN IMP_RES_TAC C2BP2AUX_bvl_evaluate_add_clock_Rval THEN
    IMP_RES_TAC evaluate_const THEN IMP_RES_TAC bvl_evaluate_mono THEN FS[] THEN
    C2BP2AUX_MAX_APP_TAC THEN
    C2BP2AUX_ASM_CASES_TAC `clos_Boolv T = r1` THEN FS[] THENL
     [branch_tac `[func:clos_exp]`;
      C2BP2AUX_ASM_CASES_TAC `clos_Boolv F = r1` THEN FS[] THEN branch_tac `[args:clos_exp]`];
    RVEQ_TAC THEN MAP_EVERY EXISTS_TAC [`ck:num`; `Rerr e':(bvl_v list,bvl_v)result`;
      `t2:(C,FFI)bvl_state`; `f2:(num,num)fmap`] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN FS[]]);;
(* HOL4: THEN1 (* Let *) *)
let C2BP2AUX_cer_Let = prove
 (C2BP2AUX_cer_goal 4,
  C2BP2AUX_CER_INTRO_TAC THEN
  FS[clos_evaluate_def; clos_to_bvl_compile_exps_def] THEN
  REPEAT PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN
  IMP_RES_TAC clos_to_bvl_compile_exps_SING THEN RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_exists(concl th) then CAKE_STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  RVEQ_TAC THEN FS[HD] THEN
  IMP_RES_TAC compile_exps_IMP_code_installed THEN
  C2BP2AUX_IH_ON_TAC `xs:clos_exp list` [] THEN
  ANTS_TAC THENL [C2BP2AUX_SIDE_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
   (X_CHOOSE_THEN `t2:(C,FFI)bvl_state` (X_CHOOSE_THEN `f2:(num,num)fmap`
    STRIP_ASSUME_TAC)))) THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  CASES_ON `x:(clos_v list,clos_v)result` THEN FS[] THENL
   [RVEQ_TAC THEN IMP_RES_TAC C2BP2AUX_bvl_evaluate_add_clock_Rval THEN
    IMP_RES_TAC evaluate_const THEN IMP_RES_TAC bvl_evaluate_mono THEN FS[] THEN
    C2BP2AUX_MAX_APP_TAC THEN
    C2BP2AUX_STEP2_TAC `[func:clos_exp]` `t2:(C,FFI)bvl_state` `f2:(num,num)fmap`
      `APPEND (v':bvl_v list) env''` THEN
    C2BP2AUX_FINISH_TAC `f3:(num,num)fmap`;
    RVEQ_TAC THEN MAP_EVERY EXISTS_TAC [`ck:num`; `Rerr e':(bvl_v list,bvl_v)result`;
      `t2:(C,FFI)bvl_state`; `f2:(num,num)fmap`] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN FS[]]);;
(* HOL4: THEN1 (* Raise *) *)
let C2BP2AUX_cer_Raise = prove
 (C2BP2AUX_cer_goal 5,
  C2BP2AUX_CER_INTRO_TAC THEN
  FS[clos_evaluate_def; clos_to_bvl_compile_exps_def] THEN
  REPEAT PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN
  IMP_RES_TAC clos_to_bvl_compile_exps_SING THEN RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_exists(concl th) then CAKE_STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  RVEQ_TAC THEN FS[HD] THEN
  IMP_RES_TAC compile_exps_IMP_code_installed THEN
  C2BP2AUX_IH_TAC [] THEN
  ANTS_TAC THENL [C2BP2AUX_SIDE_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
   (X_CHOOSE_THEN `t2:(C,FFI)bvl_state` (X_CHOOSE_THEN `f2:(num,num)fmap`
    STRIP_ASSUME_TAC)))) THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  CASES_ON `x:(clos_v list,clos_v)result` THEN FS[] THEN RVEQ_TAC THENL
   [IMP_RES_TAC clos_evaluate_SING THEN RVEQ_TAC THEN FS[LIST_REL_CONS1; LIST_REL_NIL] THEN
    RVEQ_TAC THEN EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[HD] THEN
    FS[] THEN EXISTS_TAC `f2:(num,num)fmap` THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`ck:num`; `Rerr e':(bvl_v list,bvl_v)result`;
      `t2:(C,FFI)bvl_state`; `f2:(num,num)fmap`] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN FS[]]);;
(* HOL4: THEN1 (* Handle *) *)
let C2BP2AUX_cer_Handle = prove
 (C2BP2AUX_cer_goal 6,
  C2BP2AUX_CER_INTRO_TAC THEN
  FS[clos_evaluate_def; clos_to_bvl_compile_exps_def] THEN
  REPEAT PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN
  IMP_RES_TAC clos_to_bvl_compile_exps_SING THEN RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_exists(concl th) then CAKE_STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  RVEQ_TAC THEN FS[HD] THEN
  IMP_RES_TAC compile_exps_IMP_code_installed THEN
  C2BP2AUX_IH_ON_TAC `[tmp:clos_exp]` [] THEN
  ANTS_TAC THENL [C2BP2AUX_SIDE_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
   (X_CHOOSE_THEN `t2:(C,FFI)bvl_state` (X_CHOOSE_THEN `f2:(num,num)fmap`
    STRIP_ASSUME_TAC)))) THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  MP_TAC(ISPEC `x:(clos_v list,clos_v)result` C2BP2AUX_result_cases) THEN
  STRIP_TAC THEN RVEQ_TAC THEN FS[] THEN RVEQ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`ck:num`; `Rval v':(bvl_v list,bvl_v)result`;
      `t2:(C,FFI)bvl_state`; `f2:(num,num)fmap`] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN FS[];
    IMP_RES_TAC C2BP2AUX_bvl_evaluate_add_clock_Rraise THEN
    IMP_RES_TAC evaluate_const THEN IMP_RES_TAC bvl_evaluate_mono THEN FS[] THEN
    C2BP2AUX_MAX_APP_TAC THEN
    C2BP2AUX_STEP2_TAC_F `[func:clos_exp]` (fun g ->
      `t2:(C,FFI)bvl_state`, `f2:(num,num)fmap`,
      mk_cons (C2BP2AUX_bvl_raised g) `env'':bvl_v list`) THEN
    C2BP2AUX_FINISH_TAC `f3:(num,num)fmap`;
    EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN FS[] THEN
    EXISTS_TAC `f2:(num,num)fmap` THEN ASM_REWRITE_TAC[]]);;
(* HOL4: THEN1 (* Tick *) *)
let C2BP2AUX_cer_Tick = prove
 (C2BP2AUX_cer_goal 11,
  C2BP2AUX_CER_INTRO_TAC THEN
  FS[clos_evaluate_def; clos_to_bvl_compile_exps_def; clos_dec_clock_def] THEN
  REPEAT PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN
  IMP_RES_TAC clos_to_bvl_compile_exps_SING THEN RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_exists(concl th) then CAKE_STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  RVEQ_TAC THEN FS[HD] THEN
  C2BP2AUX_ASM_CASES_TAC `clos_state_clock (s1:(C,FFI)clos_state) = 0` THEN FS[] THENL
   [EXISTS_TAC `0` THEN ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
    FS[bvl_state_INFO.ri_accfupds] THEN
    EXISTS_TAC `f1:(num,num)fmap` THEN ASM_REWRITE_TAC[SUBMAP_REFL];
    C2BP2AUX_IH_TAC [] THEN C2BP2AUX_ANTS_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
     (X_CHOOSE_THEN `t2:(C,FFI)bvl_state` (X_CHOOSE_THEN `f2:(num,num)fmap`
      STRIP_ASSUME_TAC)))) THEN
    EXISTS_TAC `ck:num` THEN
    ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
    ASM_REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM; bvl_dec_clock_def;
                    bvl_state_INFO.ri_fupdfupds; K_o_THM; ADD_EQ_0] THEN
    SUBGOAL_THEN `(clos_state_clock (s1:(C,FFI)clos_state) + ck) - 1 =
                  (clos_state_clock s1 - 1) + ck` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN C2BP2AUX_FINISH_TAC `f2:(num,num)fmap`]);;
(* HOL4: THEN1 (* Call *) *)
let C2BP2AUX_cer_Call = prove
 (C2BP2AUX_cer_goal 12,
  C2BP2AUX_CER_INTRO_TAC THEN
  FS[clos_evaluate_def; clos_to_bvl_compile_exps_def] THEN
  REPEAT PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN
  IMP_RES_TAC compile_exps_IMP_code_installed THEN
  C2BP2AUX_IH_ON_TAC `xs:clos_exp list` [] THEN C2BP2AUX_ANTS_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
   (X_CHOOSE_THEN `t2:(C,FFI)bvl_state` (X_CHOOSE_THEN `f2:(num,num)fmap`
    STRIP_ASSUME_TAC)))) THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  CASES_ON `x:(clos_v list,clos_v)result` THEN FS[] THENL
   [RVEQ_TAC THEN IMP_RES_TAC C2BP2AUX_bvl_evaluate_add_clock_Rval THEN
    IMP_RES_TAC evaluate_const THEN IMP_RES_TAC bvl_evaluate_mono THEN FS[] THEN
    C2BP2AUX_MAX_APP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[clos_find_code_def]) THEN
    C2BP2AUX_CASES_ON `FLOOKUP (clos_state_code (s:(C,FFI)clos_state)) dest` THEN FS[] THEN
    C2BP2AUX_PAIR_CASES_TAC `a':num#clos_exp` `arity:num` `exp:clos_exp` THEN FS[] THEN
    C2BP2AUX_ASM_CASES_TAC `LENGTH (a:clos_v list) = arity` THEN FS[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP C2BP2AUX_state_rel_code o
      CONJ (ASSUME `clos_to_bvlProof_state_rel f2 (s:(C,FFI)clos_state) t2`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `aux1'':(num#num#bvl_exp)list` (X_CHOOSE_THEN `c2:bvl_exp`
      (X_CHOOSE_THEN `aux2'':(num#num#bvl_exp)list` STRIP_ASSUME_TAC))) THEN
    C2BP2AUX_MAX_APP_TAC THEN
    IMP_RES_TAC LIST_REL_LENGTH THEN
    C2BP2AUX_ASM_CASES_TAC `clos_state_clock (s:(C,FFI)clos_state) < ticks + 1` THEN
    FS[] THENL
     [EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[bvl_find_code_def] THEN CAKE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN FS[] THEN EXISTS_TAC `f2:(num,num)fmap` THEN
      ASM_REWRITE_TAC[] THEN RVEQ_TAC THEN FS[];
      RULE_ASSUM_TAC(REWRITE_RULE[clos_dec_clock_def; clos_state_INFO.ri_accfupds;
                                  clos_state_INFO.ri_fupdfupds]) THEN
      C2BP2AUX_MAX_APP_TAC THEN
      C2BP2AUX_IH_ON_TAC `[exp:clos_exp]`
        [(`t2:(C,FFI)bvl_state`,"t1"); (`f2:(num,num)fmap`,"f1"); (`v':bvl_v list`,"env'")] THEN
      C2BP2AUX_ANTS_TAC THEN
      DISCH_THEN(X_CHOOSE_THEN `ck':num` (X_CHOOSE_THEN `r2:(bvl_v list,bvl_v)result`
       (X_CHOOSE_THEN `t3:(C,FFI)bvl_state` (X_CHOOSE_THEN `f3:(num,num)fmap`
        STRIP_ASSUME_TAC)))) THEN
      EXISTS_TAC `ck + ck'` THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[bvl_find_code_def; bvl_state_INFO.ri_accfupds; K_THM] THEN
      CAKE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[bvl_dec_clock_def; bvl_state_INFO.ri_accfupds; K_THM;
                      bvl_state_INFO.ri_fupdfupds; K_o_THM] THEN
      SUBGOAL_THEN `~(bvl_state_clock (t2:(C,FFI)bvl_state) + ck' < ticks + 1) /\
                    (bvl_state_clock t2 + ck') - (ticks + 1) =
                    (bvl_state_clock t2 - (ticks + 1)) + ck'`
        (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `~(bvl_state_clock (t2:(C,FFI)bvl_state) < ticks + 1)` THEN ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check C2BP2AUX_is_eval_ck') THEN
      ASM_REWRITE_TAC[K_THM] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      C2BP2AUX_FINISH_TAC `f3:(num,num)fmap`];
    RVEQ_TAC THEN MAP_EVERY EXISTS_TAC [`ck:num`; `Rerr e':(bvl_v list,bvl_v)result`;
      `t2:(C,FFI)bvl_state`; `f2:(num,num)fmap`] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN FS[]]);;
(* HOL4: THEN1 (* Fn *) *)
let C2BP2AUX_cer_Fn = prove
 (C2BP2AUX_cer_goal 8,
  C2BP2AUX_CER_INTRO_TAC THEN
  FS[clos_evaluate_def; clos_to_bvl_compile_exps_def] THEN
  REPEAT PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN
  CASES_ON `loc:num option` THEN FS[] THEN CASES_ON `vsopt:(num list)option` THEN FS[] THEN
  C2BP2AUX_ASM_CASES_TAC `num_args <= clos_state_max_app (s1:(C,FFI)clos_state) /\ ~(num_args = 0)` THEN
  FS[] THEN
  C2BP2AUX_CASES_ON `lookup_vars a' (env':clos_v list)` THEN FS[] THEN RVEQ_TAC THEN
  IMP_RES_TAC clos_to_bvl_compile_exps_SING THEN RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_exists(concl th) then CAKE_STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  RVEQ_TAC THEN FS[HD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C2BP2AUX_code_installed_CONS]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
  FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
    MP_TAC(MATCH_MP lookup_vars_IMP2 (CONJ th1 th2)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ys:bvl_v list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `0` THEN
  MP_TAC(ISPECL [`a':num list`; `env'':bvl_v list`;
    `bvl_state_clock_fupd (combin_K (clos_state_clock (s2:(C,FFI)clos_state) + 0)) (t1:(C,FFI)bvl_state)`;
    `ys:bvl_v list`; `&(num_args - 1):int`;
    `a + num_stubs (clos_state_max_app (s2:(C,FFI)clos_state))`; `closure_tag`]
    C2BP2AUX_eval_Fn_code) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[bvl_state_INFO.ri_accfupds; domain_lookup] THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  FS[] THEN EXISTS_TAC `f1:(num,num)fmap` THEN ASM_REWRITE_TAC[SUBMAP_REFL] THEN
  MATCH_MP_TAC C2BP2AUX_v_rel_Fn THEN
  MAP_EVERY EXISTS_TAC [`aux1:(num#num#bvl_exp)list`; `d:bvl_exp`;
                        `aux1':(num#num#bvl_exp)list`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
(* HOL4: THEN1 ((* cEvalApp [] *) ...) *)
let C2BP2AUX_cer_app_NIL = prove
 (C2BP2AUX_cer_goal 13,
  REPEAT STRIP_TAC THEN FS[clos_evaluate_def] THEN RVEQ_TAC THEN FS[] THEN
  MAP_EVERY EXISTS_TAC [`Rval [func']:(bvl_v list,bvl_v)result`;
    `bvl_state_clock_fupd (combin_K (clos_state_clock (s2:(C,FFI)clos_state))) (t1:(C,FFI)bvl_state)`;
    `f1:(num,num)fmap`] THEN
  ASM_REWRITE_TAC[injectivity "result"; CONS_11; SUBMAP_REFL; bvl_state_INFO.ri_accfupds;
                  K_THM; clos_to_bvlProof_state_rel_clock] THEN
  ASM_MESON_TAC[]);;
(* HOL4: THEN1 (* App *) *)
let C2BP2AUX_cer_App = prove
 (C2BP2AUX_cer_goal 10,
  C2BP2AUX_CER_INTRO_TAC THEN
  FS[clos_evaluate_def; clos_to_bvl_compile_exps_def] THEN
  REPEAT PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN
  IMP_RES_TAC clos_to_bvl_compile_exps_SING THEN RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_exists(concl th) then CAKE_STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  RVEQ_TAC THEN FS[HD] THEN
  C2BP2AUX_ASM_CASES_TAC `LENGTH (args:clos_exp list) > 0` THEN FS[] THEN
  IMP_RES_TAC compile_exps_IMP_code_installed THEN
  C2BP2AUX_IH_ON_TAC `args:clos_exp list` [] THEN C2BP2AUX_ANTS_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
   (X_CHOOSE_THEN `t2:(C,FFI)bvl_state` (X_CHOOSE_THEN `f2:(num,num)fmap`
    STRIP_ASSUME_TAC)))) THEN
  CASES_ON `x:(clos_v list,clos_v)result` THEN FS[] THENL
   [(RVEQ_TAC THEN IMP_RES_TAC C2BP2AUX_bvl_evaluate_add_clock_Rval THEN
      IMP_RES_TAC evaluate_const THEN IMP_RES_TAC bvl_evaluate_mono THEN FS[] THEN
      C2BP2AUX_MAX_APP_TAC THEN
      C2BP2AUX_IH_ON_TAC `[tmp:clos_exp]`
        [(`t2:(C,FFI)bvl_state`,"t1"); (`f2:(num,num)fmap`,"f1"); (`env'':bvl_v list`,"env'")] THEN
      C2BP2AUX_ANTS_TAC THEN
      DISCH_THEN(X_CHOOSE_THEN `ck':num` (X_CHOOSE_THEN `r2:(bvl_v list,bvl_v)result`
       (X_CHOOSE_THEN `t3:(C,FFI)bvl_state` (X_CHOOSE_THEN `f3:(num,num)fmap`
        STRIP_ASSUME_TAC)))) THEN
      CASES_ON `x':(clos_v list,clos_v)result` THEN FS[]) THENL
     [(RVEQ_TAC THEN IMP_RES_TAC C2BP2AUX_bvl_evaluate_add_clock_Rval THEN
        IMP_RES_TAC evaluate_const THEN IMP_RES_TAC bvl_evaluate_mono THEN FS[] THEN
        C2BP2AUX_MAX_APP_TAC THEN
        IMP_RES_TAC clos_evaluate_SING THEN RVEQ_TAC THEN FS[LIST_REL_CONS1; LIST_REL_NIL] THEN
        RVEQ_TAC THEN FS[HD]) THEN
      (C2BP2AUX_IH_ON_CONST_TAC_F "evaluate_app" (fun g ->
          [(`t3:(C,FFI)bvl_state`,"t1"); (`f3:(num,num)fmap`,"f1"); (`env'':bvl_v list`,"env");
           (`v':bvl_v list`,"args'"); (C2BP2AUX_bvl_val1 `[d:bvl_exp]` g,"func'")]) THEN
        C2BP2AUX_ANTS_TAC THEN
        DISCH_THEN(X_CHOOSE_THEN `ck'':num` (X_CHOOSE_THEN `r3:(bvl_v list,bvl_v)result`
         (X_CHOOSE_THEN `t4:(C,FFI)bvl_state` (X_CHOOSE_THEN `f4:(num,num)fmap`
          STRIP_ASSUME_TAC)))) THEN
        IMP_RES_TAC clos_to_bvl_compile_exps_LENGTH THEN IMP_RES_TAC clos_evaluate_IMP_LENGTH THEN
        IMP_RES_TAC LIST_REL_LENGTH THEN
        SUBGOAL_THEN `LENGTH (c2:bvl_exp list) = LENGTH (v':bvl_v list) /\ ~(LENGTH v' = 0)`
          STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ARITH_RULE `n > 0 ==> ~(n = 0)`]; ALL_TAC] THEN
        SUBGOAL_THEN `~(v':bvl_v list = [])` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL]; ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
           fst(dest_imp(concl th)) = `~(v':bvl_v list = [])`)) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        EXISTS_TAC `ck + ck' + ck''` THEN
        CASES_ON `loc_opt:num option` THEN FS[]) THENL
       [(MP_TAC(ISPECL [`c2:bvl_exp list`; `d:bvl_exp`; `env'':bvl_v list`;
           `bvl_state_clock_fupd (combin_K (clos_state_clock (s1:(C,FFI)clos_state) + ck + ck' + ck''))
              (t1:(C,FFI)bvl_state)`; `v':bvl_v list`;
           `bvl_state_clock_fupd (combin_K (bvl_state_clock (t2:(C,FFI)bvl_state) + ck' + ck'')) t2`;
           `y:bvl_v`; `bvl_state_clock_fupd (combin_K (bvl_state_clock (t3:(C,FFI)bvl_state) + ck'')) t3`]
           C2BP2AUX_app_NONE) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
          C2BP2AUX_FINISH_TAC `f4:(num,num)fmap`);
        (MP_TAC(ISPECL [`c2:bvl_exp list`; `d:bvl_exp`; `env'':bvl_v list`;
           `bvl_state_clock_fupd (combin_K (clos_state_clock (s1:(C,FFI)clos_state) + ck + ck' + ck''))
              (t1:(C,FFI)bvl_state)`; `v':bvl_v list`;
           `bvl_state_clock_fupd (combin_K (bvl_state_clock (t2:(C,FFI)bvl_state) + ck' + ck'')) t2`;
           `y:bvl_v`; `bvl_state_clock_fupd (combin_K (bvl_state_clock (t3:(C,FFI)bvl_state) + ck'')) t3`;
           `a'' + num_stubs (clos_state_max_app (s1:(C,FFI)clos_state))`]
           C2BP2AUX_app_SOME) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC[bvl_state_INFO.ri_accfupds; bvl_state_INFO.ri_fupdfupds; K_THM; K_o_THM] THEN
          C2BP2AUX_CASES_ON `bvl_find_code (SOME (a'' + num_stubs (clos_state_max_app (s1:(C,FFI)clos_state))))
             (APPEND v' [y:bvl_v]) (bvl_state_code (t3:(C,FFI)bvl_state))` THEN FS[]) THENL
         [(RVEQ_TAC THEN FS[]);
          (C2BP2AUX_FINISH_TAC `f4:(num,num)fmap`)]];
      (RVEQ_TAC THEN EXISTS_TAC `ck + ck'` THEN
        MP_TAC(ISPECL [`Rerr e':(bvl_v list,bvl_v)result`; `c2:bvl_exp list`; `env'':bvl_v list`;
         `bvl_state_clock_fupd (combin_K (clos_state_clock (s1:(C,FFI)clos_state) + ck + ck'))
            (t1:(C,FFI)bvl_state)`; `v':bvl_v list`;
         `bvl_state_clock_fupd (combin_K (bvl_state_clock (t2:(C,FFI)bvl_state) + ck')) t2`;
         `d:bvl_exp`; `t3:(C,FFI)bvl_state`; `loc_opt:num option`;
         `clos_state_max_app (s1:(C,FFI)clos_state)`] evaluate_app_helper2) THEN
        ASM_REWRITE_TAC[distinctness "result"] THEN DISCH_THEN SUBST1_TAC THEN
        C2BP2AUX_FINISH_TAC `f3:(num,num)fmap`)];
    (RVEQ_TAC THEN EXISTS_TAC `ck:num` THEN
      MP_TAC(ISPECL [`Rerr e':(bvl_v list,bvl_v)result`; `c2:bvl_exp list`; `env'':bvl_v list`;
       `bvl_state_clock_fupd (combin_K (clos_state_clock (s1:(C,FFI)clos_state) + ck))
          (t1:(C,FFI)bvl_state)`; `t2:(C,FFI)bvl_state`; `loc_opt:num option`;
       `d:bvl_exp`; `clos_state_max_app (s1:(C,FFI)clos_state)`] evaluate_app_helper) THEN
      ASM_REWRITE_TAC[distinctness "result"] THEN DISCH_THEN SUBST1_TAC THEN
      C2BP2AUX_FINISH_TAC `f2:(num,num)fmap`)]);;

(* used in the Full_app case of evaluate_app: the first application fails *)
let C2BP2AUX_app_fail_tac =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `res:(clos_v list,clos_v)result,s2:(C,FFI)clos_state`)) THEN
  CAKE_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> C2BP2AUX_head (concl th) = "result_rel")) THEN
  REWRITE_TAC[result_rel_Rerr1] THEN
  DISCH_THEN(X_CHOOSE_THEN `ee:(bvl_v)error_result` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    ASSUME_TAC)) THEN
  EXISTS_TAC `ck'' + ck' + 1` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(clos_state_clock (s:(C,FFI)clos_state) + ck'' + ck' + 1 < rem_args + 1) /\
                (clos_state_clock s + ck'' + ck' + 1) - (rem_args + 1) =
                (clos_state_clock s - rem_args + ck'') + ck'`
    (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `~(clos_state_clock (s:(C,FFI)clos_state) < rem_args)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  C2BP2AUX_FINISH_TAC `f2:(num,num)fmap`;;

(* HOL4: (* cEvalApp real app *) *)
let C2BP2AUX_cer_app_CONS = prove
 (C2BP2AUX_cer_goal 14,
(REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(fun th -> if C2BP2AUX_is_ih (concl th) then CAKE_SIMP_RULE[] th else th) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> C2BP2AUX_head (lhs (concl th)) = "evaluate_app")) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN DISCH_TAC THEN
  IMP_RES_TAC LIST_REL_LENGTH THEN
  SUBGOAL_THEN `~(LENGTH (args':bvl_v list) = 0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[LENGTH; NOT_SUC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  C2BP2AUX_CASES_ON `dest_closure (clos_state_max_app (s:(C,FFI)clos_state)) loc_opt f (CONS v4 v5)` THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[])) THENL
 [(RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN FS[]);
  (CASES_ON `a:app_kind` THEN RULE_ASSUM_TAC(CAKE_REWRITE_RULE[])) THENL
   [(C2BP2AUX_MP_INST_TAC [(`env:bvl_v list`,"env")] C2BP2AUX_app_partial) THEN
(DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `ck:num`
    (X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result` (X_CHOOSE_THEN `t2:(C,FFI)bvl_state`
     (X_CHOOSE_THEN `f2:(num,num)fmap` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `clos_state_code (s2:(C,FFI)clos_state) = clos_state_code (s:(C,FFI)clos_state)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
    COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ; clos_dec_clock_def] THEN STRIP_TAC THEN
    RVEQ_TAC THEN REWRITE_TAC[clos_state_INFO.ri_accfupds]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `r1:(bvl_v list,bvl_v)result`; `t2:(C,FFI)bvl_state`;
                        `f2:(num,num)fmap`] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);
    (RULE_ASSUM_TAC(fun th -> if C2BP2AUX_is_ih (concl th) then CAKE_SIMP_RULE[] th else th) THEN
  FIRST_ASSUM(fun dth -> FIRST_ASSUM(fun vth ->
    STRIP_ASSUME_TAC(MATCH_MP C2BP2AUX_dest_closure_every_Fn (CONJ dth vth)))) THEN
  FIRST_ASSUM(fun dth -> STRIP_ASSUME_TAC(MATCH_MP dest_closure_full_app dth)) THEN
  FIRST_ASSUM(fun vth -> FIRST_ASSUM(fun nth ->
    STRIP_ASSUME_TAC(MATCH_MP v_rel_num_rem_args (CONJ vth nth)))) THEN
  RVEQ_TAC) THEN
(RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
  FIRST_X_ASSUM(fun th -> if concl th = `SUC (LENGTH (v5:clos_v list)) = LENGTH (args':bvl_v list)`
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th else NO_TAC) THEN
  SUBGOAL_THEN `LENGTH (args':bvl_v list) - LENGTH (a2:clos_v list) = rem_args`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `LENGTH (a2:clos_v list) = LENGTH (args':bvl_v list) - rem_args` THEN
    UNDISCH_TAC `rem_args <= LENGTH (args':bvl_v list)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&rem_args - &1:int = &(rem_args - 1)` (fun th -> REWRITE_TAC[th] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC INT_OF_NUM_SUB THEN UNDISCH_TAC `~(rem_args = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  CASES_ON `loc_opt:num option` THEN CAKE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[check_loc_def])) THENL
     [(SUBGOAL_THEN (CASE_TERM `!ck. bvl_evaluate ([mk_cl_call (bvl_Var (LENGTH (args':bvl_v list)))
       (list_of_seq bvl_Var (LENGTH args'))],
     APPEND (APPEND args' [bvl_Block tag (CONS (bvl_CodePtr ptr)
       (CONS (bvl_Number (&(rem_args - 1))) rest))]) env,
     bvl_state_clock_fupd (combin_K (clos_state_clock (s:(C,FFI)clos_state) + ck))
       (t1:(C,FFI)bvl_state)) =
     if rem_args = LENGTH args' then
       if clos_state_clock s + ck < LENGTH args'
       then (Rerr (Rabort Rtimeout_error),bvl_state_clock_fupd (combin_K 0) t1)
       else bvl_evaluate ([exp],APPEND args' [bvl_Block tag (CONS (bvl_CodePtr ptr)
              (CONS (bvl_Number (&(LENGTH args' - 1))) rest))],
              bvl_state_clock_fupd (combin_K ((clos_state_clock s + ck) - LENGTH args')) t1)
     else
       if clos_state_clock s + ck < rem_args + 1
       then (Rerr (Rabort Rtimeout_error),bvl_state_clock_fupd (combin_K 0) t1)
       else
         (match bvl_evaluate ([exp],APPEND (DROP (LENGTH args' - rem_args) args')
                 [bvl_Block tag (CONS (bvl_CodePtr ptr) (CONS (bvl_Number (&(rem_args - 1))) rest))],
                 bvl_state_clock_fupd (combin_K ((clos_state_clock s + ck) - (rem_args + 1))) t1) with
            (Rval [v],st') ->
              (match bvl_evaluate ([mk_cl_call (bvl_Var 0)
                       (list_of_seq (\n. bvl_Var (n + 1)) (LENGTH args' - rem_args))],
                     CONS v (APPEND args' [bvl_Block tag (CONS (bvl_CodePtr ptr)
                       (CONS (bvl_Number (&(rem_args - 1))) rest))]),st') with
                 (Rval v,s2) -> (Rval [HD v],s2)
               | x -> x)
          | x -> x)`) ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`bvl_state_clock_fupd (combin_K (clos_state_clock (s:(C,FFI)clos_state) + ck))
                      (t1:(C,FFI)bvl_state)`; `env:bvl_v list`; `tag:num`; `ptr:num`;
                   `rem_args:num`; `args':bvl_v list`; `exp:bvl_exp`; `rest:bvl_v list`;
                   `clos_state_max_app (s:(C,FFI)clos_state)`] C2BP2AUX_mk_cl_call_full) THEN
    ASM_REWRITE_TAC[bvl_state_INFO.ri_accfupds] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      FIRST [MATCH_MP_TAC C2BP2AUX_state_rel_generic THEN EXISTS_TAC `f1:(num,num)fmap` THEN
             ASM_REWRITE_TAC[];
             ASM_REWRITE_TAC[] THEN NO_TAC];
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[bvl_dec_clock_def; bvl_state_INFO.ri_accfupds; bvl_state_INFO.ri_fupdfupds;
                  K_THM; K_o_THM]];
    ALL_TAC]) THEN
(C2BP2AUX_ASM_CASES_TAC `clos_state_clock (s:(C,FFI)clos_state) < rem_args`) THENL
       [(EXISTS_TAC `0` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `clos_state_clock (s:(C,FFI)clos_state) + 0 < LENGTH (args':bvl_v list) /\
                clos_state_clock s + 0 < rem_args + 1` (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY UNDISCH_TAC [`clos_state_clock (s:(C,FFI)clos_state) < rem_args`;
      `rem_args <= LENGTH (args':bvl_v list)`] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[COND_ID] THEN FS[] THEN RVEQ_TAC THEN
  EXISTS_TAC `f1:(num,num)fmap` THEN
  ASM_REWRITE_TAC[SUBMAP_REFL; clos_state_INFO.ri_accfupds; clos_to_bvlProof_state_rel_clock; K_THM]);
        (MP_TAC(ISPEC `clos_evaluate ([a0:clos_exp],a1,clos_dec_clock rem_args (s:(C,FFI)clos_state))`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(clos_v list,clos_v)result` (X_CHOOSE_THEN `s3:(C,FFI)clos_state`
    ASSUME_TAC))) THEN
(FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
      rhs (concl th) = `res:(clos_v list,clos_v)result,s2:(C,FFI)clos_state` then
    MP_TAC (CAKE_REWRITE_RULE[ASSUME `clos_evaluate ([a0:clos_exp],a1,clos_dec_clock rem_args
       (s:(C,FFI)clos_state)) = r1,s3`] th)
    else NO_TAC) THEN DISCH_TAC) THEN
(SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `res:(clos_v list,clos_v)result,s2:(C,FFI)clos_state`)) THEN
    CAKE_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  C2BP2AUX_MP_INST_TAC [(`tag:num`,"tag"); (`ptr:num`,"ptr"); (`rem_args - 1`,"n");
                        (`rest:bvl_v list`,"env'")] v_rel_run THEN
  ANTS_TAC THENL [REWRITE_TAC[LENGTH; NOT_SUC]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck':num` (X_CHOOSE_THEN `body':bvl_exp`
    (X_CHOOSE_THEN `aux1:(num#num#bvl_exp)list` (X_CHOOSE_THEN `aux2:(num#num#bvl_exp)list`
    (X_CHOOSE_THEN `newenv':bvl_v list` (X_CHOOSE_THEN `exp':bvl_exp` STRIP_ASSUME_TAC))))))) THEN
(RULE_ASSUM_TAC(REWRITE_RULE[clos_dec_clock_def; clos_state_INFO.ri_accfupds;
                              clos_to_bvlProof_state_rel_clock]) THEN
  C2BP2AUX_IH_ON_TAC `[a0:clos_exp]`
    [(`t1:(C,FFI)bvl_state`,"t1"); (`f1:(num,num)fmap`,"f1"); (`newenv':bvl_v list`,"env'")] THEN
  C2BP2AUX_ANTS_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `ck'':num` (X_CHOOSE_THEN `r2:(bvl_v list,bvl_v)result`
   (X_CHOOSE_THEN `t2:(C,FFI)bvl_state` (X_CHOOSE_THEN `f2:(num,num)fmap`
    STRIP_ASSUME_TAC))))) THEN
(SUBGOAL_THEN `exp':bvl_exp = exp` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
      `lookup ptr (bvl_state_code (t1:(C,FFI)bvl_state)) = SOME (rem_args - 1 + 2,exp')`)) THEN
    ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `bvl_evaluate ([exp],
      APPEND (DROP (LENGTH (args':bvl_v list) - rem_args) args')
        [bvl_Block tag (CONS (bvl_CodePtr ptr) (CONS (bvl_Number (&(rem_args - 1))) rest))],
      bvl_state_clock_fupd (combin_K (((clos_state_clock (s:(C,FFI)clos_state) - rem_args) + ck'') + ck'))
        (t1:(C,FFI)bvl_state)) = (r2,t2)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `bvl_state_clock_fupd (combin_K ((clos_state_clock (s:(C,FFI)clos_state)
       - rem_args) + ck'')) (t1:(C,FFI)bvl_state)` o check (fun th ->
       is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "t1'")) THEN
    REWRITE_TAC[C2BP2AUX_bvl_fupd_same; bvl_inc_clock_def; bvl_state_INFO.ri_accfupds;
                bvl_state_INFO.ri_fupdfupds; K_THM; K_o_THM;
                ARITH_RULE `rem_args - 1 + 1 = rem_args <=> ~(rem_args = 0)`] THEN
    SUBGOAL_THEN `rem_args - 1 + 1 = rem_args` SUBST1_TAC THENL
     [UNDISCH_TAC `~(rem_args = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> try rhs (concl th) =
       `(r2:(bvl_v list,bvl_v)result),(t2:(C,FFI)bvl_state)` with Failure _ -> false)) THEN
    REWRITE_TAC[K_THM];
    ALL_TAC]) THEN
(ASM_CASES_TAC `rem_args = LENGTH (args':bvl_v list)`) THENL
         [(SUBGOAL_THEN `(a2:clos_v list) = []` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[SUB_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `res = r1:(clos_v list,clos_v)result /\ s2 = s3:(C,FFI)clos_state`
    STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `res:(clos_v list,clos_v)result,s2:(C,FFI)clos_state`)) THEN
    MP_TAC(ISPEC `r1:(clos_v list,clos_v)result` C2BP2AUX_result_cases) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    TRY(CASES_ON `vs:clos_v list` THEN CAKE_REWRITE_TAC[] THEN
        TRY(CASES_ON `a1':clos_v list` THEN CAKE_REWRITE_TAC[])) THEN
    REWRITE_TAC[evaluate_app_NIL; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  RVEQ_TAC THEN EXISTS_TAC `ck'' + ck'` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(clos_state_clock (s:(C,FFI)clos_state) + ck'' + ck' < LENGTH (args':bvl_v list)) /\
                (clos_state_clock s + ck'' + ck') - LENGTH args' =
                ((clos_state_clock s - LENGTH args') + ck'') + ck'` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `~(clos_state_clock (s:(C,FFI)clos_state) < LENGTH (args':bvl_v list))` THEN
    ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try rhs (concl th) =
       `(r2:(bvl_v list,bvl_v)result),(t2:(C,FFI)bvl_state)` &&
       C2BP2AUX_head (lhs (concl th)) = "bvl_evaluate" &&
       free_in `exp:bvl_exp` (concl th) with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[SUB_REFL; DROP] THEN DISCH_THEN SUBST1_TAC THEN
  C2BP2AUX_FINISH_TAC `f2:(num,num)fmap`);
          (SUBGOAL_THEN `rem_args < LENGTH (args':bvl_v list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `r1:(clos_v list,clos_v)result` C2BP2AUX_result_cases) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `r1:(clos_v list,clos_v)result`))) THENL
           [(FIRST_ASSUM(fun th -> if is_eq (concl th) && C2BP2AUX_head (lhs (concl th)) = "clos_evaluate"
                           && rhs (concl th) = `Rval vs:(clos_v list,clos_v)result,s3:(C,FFI)clos_state`
    then CHOOSE_THEN SUBST_ALL_TAC (MATCH_MP clos_evaluate_SING th) else NO_TAC) THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> C2BP2AUX_head (concl th) = "result_rel")) THEN
  REWRITE_TAC[result_rel_Rval; LIST_REL_CONS1; LIST_REL_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:bvl_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `v':bvl_v` (X_CHOOSE_THEN `vt:bvl_v list` STRIP_ASSUME_TAC)))) THEN
  C2BP2AUX_SUBST_VARS_TAC ["vv"; "vt"] THEN
  IMP_RES_TAC evaluate_const THEN RULE_ASSUM_TAC(REWRITE_RULE[clos_state_INFO.ri_accfupds]) THEN
  C2BP2AUX_MAX_APP_TAC) THEN
(IMP_RES_TAC bvl_evaluate_mono THEN RULE_ASSUM_TAC(REWRITE_RULE[bvl_state_INFO.ri_accfupds]) THEN
  C2BP2AUX_IH_ON_CONST_TAC "evaluate_app"
    [(`t2:(C,FFI)bvl_state`,"t1"); (`f2:(num,num)fmap`,"f1"); (`[]:bvl_v list`,"env");
     (`TAKE (LENGTH (args':bvl_v list) - rem_args) args'`,"args'"); (`v':bvl_v`,"func'")] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC list_rel_app THEN
    MAP_EVERY EXISTS_TAC [`CONS (v4:clos_v) v5`; `a0:clos_exp`; `a1:clos_v list`; `f:clos_v`;
                          `clos_state_max_app (s:(C,FFI)clos_state)`] THEN
    ASM_REWRITE_TAC[] THEN C2BP2AUX_SIDE_TAC;
    ALL_TAC]) THEN
(DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `r3:(bvl_v list,bvl_v)result`
   (X_CHOOSE_THEN `t3:(C,FFI)bvl_state` (X_CHOOSE_THEN `f3:(num,num)fmap`
    STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `LENGTH (TAKE (LENGTH (args':bvl_v list) - rem_args) args') =
                LENGTH args' - rem_args /\
                ~(TAKE (LENGTH args' - rem_args) args' = [])` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
    SIMP_TAC[LENGTH_TAKE; ARITH_RULE `n - r <= n`] THEN
    UNDISCH_TAC `rem_args < LENGTH (args':bvl_v list)` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    fst(dest_imp(concl th)) = `~(TAKE (LENGTH (args':bvl_v list) - rem_args) args' = [])`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) && C2BP2AUX_head (lhs (concl th)) = "bvl_evaluate"
                           && rhs (concl th) = `r3:(bvl_v list,bvl_v)result,t3:(C,FFI)bvl_state`
    then ALL_TAC else NO_TAC)) THEN
(SUBGOAL_THEN `bvl_evaluate ([mk_cl_call (bvl_Var 0)
       (list_of_seq (\n. bvl_Var (n + 1)) (LENGTH (args':bvl_v list) - rem_args))],
     CONS v' (APPEND args' [bvl_Block tag (CONS (bvl_CodePtr ptr)
       (CONS (bvl_Number (&(rem_args - 1))) rest))]),
     bvl_state_clock_fupd (combin_K (bvl_state_clock (t2:(C,FFI)bvl_state) + ck3)) t2) = (r3,t3)`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq (concl th) && C2BP2AUX_head (lhs (concl th)) = "bvl_evaluate"
       && rhs (concl th) = `r3:(bvl_v list,bvl_v)result,t3:(C,FFI)bvl_state`
     then SUBST1_TAC (SYM th) else NO_TAC) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC mk_call_simp2 THEN
    REWRITE_TAC[LENGTH; NOT_SUC] THEN ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `ck'' + ck' + ck3 + 1` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(clos_state_clock (s:(C,FFI)clos_state) + ck'' + ck' + ck3 + 1 < rem_args + 1) /\
                (clos_state_clock s + ck'' + ck' + ck3 + 1) - (rem_args + 1) =
                (clos_state_clock s - rem_args + ck'') + ck' + ck3`
    (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `~(clos_state_clock (s:(C,FFI)clos_state) < rem_args)` THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) && C2BP2AUX_head (lhs (concl th)) = "bvl_evaluate"
       && free_in `exp:bvl_exp` (lhs (concl th)) &&
       rhs (concl th) = `Rval [v']:(bvl_v list,bvl_v)result,t2:(C,FFI)bvl_state`
     then REWRITE_TAC[MATCH_MP C2BP2AUX_bvl_evaluate_add_clock_Rval th] else NO_TAC) THEN
  CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]) THEN
(C2BP2AUX_MAX_APP_TAC THEN CAKE_REWRITE_TAC[] THEN
  CASES_ON `r3:(bvl_v list,bvl_v)result` THEN CAKE_REWRITE_TAC[] THENL
   [FIRST_ASSUM(fun th -> if is_eq (concl th) && C2BP2AUX_head (lhs (concl th)) = "bvl_evaluate"
       && (try let r,t = dest_pair (rhs (concl th)) in
               C2BP2AUX_head r = "Rval" && t = `t3:(C,FFI)bvl_state` with Failure _ -> false)
       && (try length (dest_list (fst(dest_pair(rand(lhs(concl th)))))) = 1 with Failure _ -> false)
     then CHOOSE_THEN SUBST_ALL_TAC (MATCH_MP bvl_evaluate_SING th) else NO_TAC) THEN
    REWRITE_TAC[HD];
    ALL_TAC] THEN
  C2BP2AUX_FINISH_TAC `f3:(num,num)fmap`);
            (C2BP2AUX_app_fail_tac);
            (C2BP2AUX_app_fail_tac)]]];
      (FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
     can (find_term (fun t -> t = `get_loc (f:clos_v)`)) (concl th))) THEN
  SUBGOAL_THEN `rem_args = LENGTH (args':bvl_v list)` ASSUME_TAC THENL
   [(* only the facts needed (ASM_ARITH_TAC took 28 s here) *)
    MAP_EVERY UNDISCH_TAC [`num_args = LENGTH (args':bvl_v list)`; `num_args - rem_args = 0`;
                           `rem_args <= num_args`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ptr = a' + num_stubs (clos_state_max_app (s:(C,FFI)clos_state))` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC C2BP2AUX_ptr_loc THEN
    MAP_EVERY EXISTS_TAC [`f1:(num,num)fmap`;
      `bvl_state_refs (t1:(C,FFI)bvl_state)`; `bvl_state_code (t1:(C,FFI)bvl_state)`;
      `f:clos_v`; `tag:num`; `bvl_Number (&(rem_args - 1))`; `rest:bvl_v list`; `rem_args:num`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[bvl_find_code_def; LENGTH_APPEND; LENGTH] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `rem_args + SUC 0 = rem_args + 1`] THEN
  C2BP2AUX_ASM_CASES_TAC `clos_state_clock (s:(C,FFI)clos_state) < rem_args`) THENL
       [(CAKE_REWRITE_TAC[] THEN EXISTS_TAC `0` THEN
  SUBGOAL_THEN `clos_state_clock (s:(C,FFI)clos_state) + 0 < LENGTH (args':bvl_v list)`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FS[] THEN RVEQ_TAC THEN EXISTS_TAC `f1:(num,num)fmap` THEN
  ASM_REWRITE_TAC[SUBMAP_REFL; clos_state_INFO.ri_accfupds; clos_to_bvlProof_state_rel_clock; K_THM]);
        (CAKE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `rem_args = LENGTH (args':bvl_v list)`)) THEN
  MP_TAC(ISPEC `clos_evaluate ([a0:clos_exp],a1,clos_dec_clock (LENGTH (args':bvl_v list))
      (s:(C,FFI)clos_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(clos_v list,clos_v)result` (X_CHOOSE_THEN `s3:(C,FFI)clos_state`
    ASSUME_TAC)) THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
      rhs (concl th) = `res:(clos_v list,clos_v)result,s2:(C,FFI)clos_state` then
    MP_TAC (CAKE_REWRITE_RULE[ASSUME `clos_evaluate ([a0:clos_exp],a1,clos_dec_clock
       (LENGTH (args':bvl_v list)) (s:(C,FFI)clos_state)) = r1,s3`] th)
    else NO_TAC) THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `res:(clos_v list,clos_v)result,s2:(C,FFI)clos_state`)) THEN
    CAKE_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  C2BP2AUX_MP_INST_TAC [(`tag:num`,"tag");
    (`a' + num_stubs (clos_state_max_app (s:(C,FFI)clos_state))`,"ptr");
    (`LENGTH (args':bvl_v list) - 1`,"n"); (`rest:bvl_v list`,"env'")] v_rel_run THEN
  ANTS_TAC THENL [REWRITE_TAC[LENGTH; NOT_SUC]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck':num` (X_CHOOSE_THEN `body':bvl_exp`
    (X_CHOOSE_THEN `aux1:(num#num#bvl_exp)list` (X_CHOOSE_THEN `aux2:(num#num#bvl_exp)list`
    (X_CHOOSE_THEN `newenv':bvl_v list` (X_CHOOSE_THEN `exp':bvl_exp` STRIP_ASSUME_TAC))))))) THEN
(RULE_ASSUM_TAC(REWRITE_RULE[clos_dec_clock_def; clos_state_INFO.ri_accfupds;
                              clos_to_bvlProof_state_rel_clock]) THEN
  C2BP2AUX_IH_ON_TAC `[a0:clos_exp]`
    [(`t1:(C,FFI)bvl_state`,"t1"); (`f1:(num,num)fmap`,"f1"); (`newenv':bvl_v list`,"env'")] THEN
  C2BP2AUX_ANTS_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `ck'':num` (X_CHOOSE_THEN `r2:(bvl_v list,bvl_v)result`
   (X_CHOOSE_THEN `t2:(C,FFI)bvl_state` (X_CHOOSE_THEN `f2:(num,num)fmap`
    STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `exp':bvl_exp = exp` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
      `lookup (a' + num_stubs (clos_state_max_app (s:(C,FFI)clos_state)))
         (bvl_state_code (t1:(C,FFI)bvl_state)) = SOME (LENGTH (args':bvl_v list) - 1 + 2,exp')`)) THEN
    ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `bvl_evaluate ([exp],
      APPEND (args':bvl_v list)
        [bvl_Block tag (CONS (bvl_CodePtr (a' + num_stubs (clos_state_max_app (s:(C,FFI)clos_state))))
           (CONS (bvl_Number (&(LENGTH args' - 1))) rest))],
      bvl_state_clock_fupd (combin_K (((clos_state_clock s - LENGTH args') + ck'') + ck'))
        (t1:(C,FFI)bvl_state)) = (r2,t2)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `bvl_state_clock_fupd (combin_K ((clos_state_clock (s:(C,FFI)clos_state)
       - LENGTH (args':bvl_v list)) + ck'')) (t1:(C,FFI)bvl_state)` o check (fun th ->
       is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "t1'")) THEN
    REWRITE_TAC[C2BP2AUX_bvl_fupd_same; bvl_inc_clock_def; bvl_state_INFO.ri_accfupds;
                bvl_state_INFO.ri_fupdfupds; K_THM; K_o_THM] THEN
    SUBGOAL_THEN `LENGTH (args':bvl_v list) - (LENGTH args' - 1 + 1) = 0` SUBST1_TAC THENL
     [UNDISCH_TAC `~(LENGTH (args':bvl_v list) = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[DROP] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> try rhs (concl th) =
       `(r2:(bvl_v list,bvl_v)result),(t2:(C,FFI)bvl_state)` with Failure _ -> false)) THEN
    REWRITE_TAC[K_THM];
    ALL_TAC]) THEN
(SUBGOAL_THEN `(a2:clos_v list) = []` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[SUB_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `res = r1:(clos_v list,clos_v)result /\ s2 = s3:(C,FFI)clos_state`
    STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `res:(clos_v list,clos_v)result,s2:(C,FFI)clos_state`)) THEN
    MP_TAC(ISPEC `r1:(clos_v list,clos_v)result` C2BP2AUX_result_cases) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    TRY(CASES_ON `vs:clos_v list` THEN CAKE_REWRITE_TAC[] THEN
        TRY(CASES_ON `a1':clos_v list` THEN CAKE_REWRITE_TAC[])) THEN
    REWRITE_TAC[evaluate_app_NIL; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `res = r1:(clos_v list,clos_v)result`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s2 = s3:(C,FFI)clos_state`)) THEN
  EXISTS_TAC `ck'' + ck'` THEN
  SUBGOAL_THEN `~(clos_state_clock (s:(C,FFI)clos_state) + ck'' + ck' < LENGTH (args':bvl_v list)) /\
                (clos_state_clock s + ck'' + ck') - LENGTH args' =
                ((clos_state_clock s - LENGTH args') + ck'') + ck'` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `~(clos_state_clock (s:(C,FFI)clos_state) < LENGTH (args':bvl_v list))` THEN
    ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN C2BP2AUX_FINISH_TAC `f2:(num,num)fmap`)]]]]);;

(* helpers for the Letrec case *)

(* a singly-recursive closure and its code (cl_rel rule 2) *)
let C2BP2AUX_v_rel_Rec1 = prove
 (`!max_app f refs code loc env ys num_args exp aux d aux1.
     ALL2 (clos_to_bvlProof_v_rel max_app f refs code) env ys /\
     num_args <= max_app /\ ~(num_args = 0) /\
     every_Fn_SOME [exp] /\ every_Fn_vs_SOME [exp] /\
     clos_to_bvl_compile_exps max_app [exp] aux = ([d],aux1) /\
     clos_to_bvlProof_code_installed aux1 code /\
     lookup (loc + num_stubs max_app) code =
       SOME (num_args + 1,
             bvl_Let (APPEND (APPEND (list_of_seq bvl_Var num_args) [bvl_Var num_args])
                        (free_let (bvl_Var num_args) (LENGTH env))) d)
     ==> clos_to_bvlProof_v_rel max_app f refs code
           (clos_Recclosure (SOME loc) [] env [(num_args,exp)] 0)
           (bvl_Block closure_tag
              (CONS (bvl_CodePtr (loc + num_stubs max_app))
                 (CONS (bvl_Number (&(num_args - 1))) ys)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (el 5 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
  EXISTS_TAC `env:clos_v list` THEN EXISTS_TAC `ys:bvl_v list` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (el 1 (CONJUNCTS cl_rel_rules)) THEN
  MAP_EVERY EXISTS_TAC [`aux:(num#num#bvl_exp)list`; `d:bvl_exp`;
                        `aux1:(num#num#bvl_exp)list`] THEN
  ASM_REWRITE_TAC[GSYM ADD1; list_of_seq]);;

(* the evaluation of build_recc_lets (HOL4 does it inline in the Letrec   *)
(* case of compile_exps_correct)                                           *)

let C2BP2AUX_HD_TL_REVERSE_SNOC = prove
 (`!l (a:A). HD (REVERSE (APPEND l [a])) = a /\ TL (REVERSE (APPEND l [a])) = REVERSE l`,
  REWRITE_TAC[REVERSE_APPEND; REVERSE; APPEND; HD; TL]);;

let C2BP2AUX_LUPDATE_MAP_SNOC = prove
 (`!(v:C) (f:B->C) (g:A->B) l y l2.
     LUPDATE v (LENGTH l) (APPEND (APPEND (MAP f (MAP g l)) [y]) l2) =
     APPEND (APPEND (MAP f (MAP g l)) [v]) l2`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPECL [`v:C`; `MAP (f:B->C) (MAP (g:A->B) l)`; `y:C`; `l2:C list`]
                 lupdate_append2) THEN
  REWRITE_TAC[LENGTH_MAP]);;

let C2BP2AUX_eval_Ref_zeros = prove
 (`!(nargs:num list) names env (t:(C,FFI)bvl_state) fvs.
     (!t:(C,FFI)bvl_state. bvl_evaluate (MAP bvl_Var names,env,t) = (Rval fvs,t))
     ==> bvl_evaluate ([bvl_Op (MemOp clos_Ref)
                          (REVERSE (APPEND (MAP (combin_K (mk_const 0)) nargs) (MAP bvl_Var names)))],
                       env,t) =
         (Rval [bvl_RefPtr T (minimal ptr. ~(ptr IN FDOM (bvl_state_refs t)))],
          bvl_state_refs_fupd
            (combin_K (bvl_state_refs t |+
                ((minimal ptr. ~(ptr IN FDOM (bvl_state_refs t))),
                 bvl_ValueArray (APPEND (MAP (combin_K (bvl_Number (&0))) nargs) fvs)))) t)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_TAC (MATCH_MP evaluate_var_reverse (SPEC `t:(C,FFI)bvl_state` th))) THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  REWRITE_TAC[REVERSE_APPEND; bvl_evaluate_APPEND] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[MAP_REVERSE; mk_const_def; evaluate_MAP_Const] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvl_do_app_Ref; REVERSE_APPEND; REVERSE_REVERSE; GSYM MAP_REVERSE] THEN
  CAKE_REWRITE_TAC[]);;

let C2BP2AUX_eval_recc_Let0 = prove
 (`!m a i env (s:(C,FFI)bvl_state) rr xs.
     FLOOKUP (bvl_state_refs s) rr = SOME (bvl_ValueArray xs) /\ i < LENGTH xs /\
     m IN domain (bvl_state_code s)
     ==> bvl_evaluate ([recc_Let0 m a i],CONS (bvl_RefPtr T rr) env,s) =
         (Rval [bvl_Block closure_tag [bvl_CodePtr m; bvl_Number (&(a - 1)); bvl_RefPtr T rr]],
          bvl_state_refs_fupd
            (combin_K (bvl_state_refs s |+
                (rr,bvl_ValueArray (LUPDATE (bvl_Block closure_tag
                    [bvl_CodePtr m; bvl_Number (&(a - 1)); bvl_RefPtr T rr]) i xs)))) s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[recc_Let0_def; mk_const_def; mk_label_def] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN REWRITE_TAC[bvl_evaluate_def] THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH; LT_0; EL; HD; TL; REVERSE; APPEND] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[CONJUNCT1 bvl_do_int_app_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH; LT_0; EL; HD; TL; REVERSE; APPEND; bvl_do_app_Cons] THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `!n. 1 < SUC (SUC n)`; C2BP2AUX_EL_CONS_ONE] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH; LT_0; EL; HD; TL; REVERSE; APPEND] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[bvl_state_INFO.ri_accfupds] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[INT_POS; INT_OF_NUM_LT; NUM_OF_INT_OF_NUM] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[APPEND; LENGTH; ARITH_RULE `!n. 1 < SUC (SUC n)`; C2BP2AUX_EL_CONS_ONE]);;

let C2BP2AUX_eval_recc_Let0_ref = prove
 (`!m a i env (s0:(C,FFI)bvl_state) rr xs.
     i < LENGTH xs /\ m IN domain (bvl_state_code s0)
     ==> bvl_evaluate ([recc_Let0 m a i],CONS (bvl_RefPtr T rr) env,
                       bvl_state_refs_fupd (combin_K (bvl_state_refs s0 |+ (rr,bvl_ValueArray xs))) s0) =
         (Rval [bvl_Block closure_tag [bvl_CodePtr m; bvl_Number (&(a - 1)); bvl_RefPtr T rr]],
          bvl_state_refs_fupd
            (combin_K (bvl_state_refs s0 |+
                (rr,bvl_ValueArray (LUPDATE (bvl_Block closure_tag
                    [bvl_CodePtr m; bvl_Number (&(a - 1)); bvl_RefPtr T rr]) i xs)))) s0)`,
  REPEAT STRIP_TAC THEN
  W(fun (asl,w) -> MP_TAC (PART_MATCH (lhs o rand) C2BP2AUX_eval_recc_Let0 (lhs w))) THEN
  ASM_REWRITE_TAC[bvl_state_INFO.ri_accfupds; bvl_state_INFO.ri_fupdfupds; K_THM;
                  FLOOKUP_UPDATE_SAME; FUPDATE_EQ; K_o_THM]);;

let C2BP2AUX_eval_build_recc_lets_SNOC = prove
 (`!ll (x:num#clos_exp) names env (t1:(C,FFI)bvl_state) fvs loc ns c3 ck.
     (!t:(C,FFI)bvl_state. bvl_evaluate (MAP bvl_Var names,env,t) = (Rval fvs,t)) /\
     (!k. k <= LENGTH ll ==> loc + ns + 2 * k IN domain (bvl_state_code t1))
     ==> bvl_evaluate ([build_recc_lets (MAP FST (APPEND ll [x])) names (loc + ns) (LENGTH ll + 1) c3],
                       env,bvl_state_clock_fupd (combin_K ck) t1) =
         bvl_evaluate ([c3],
           APPEND (MAP2 (\n args. bvl_Block closure_tag
                     [bvl_CodePtr (loc + ns + 2 * n); bvl_Number (&(args - 1));
                      bvl_RefPtr T (minimal ptr. ~(ptr IN FDOM (bvl_state_refs t1)))])
                   (list_of_seq I (LENGTH ll + 1)) (APPEND (MAP FST ll) [FST x])) env,
           bvl_state_refs_fupd (combin_K (bvl_state_refs t1 |+
             ((minimal ptr. ~(ptr IN FDOM (bvl_state_refs t1))),
              bvl_ValueArray (APPEND (MAP2 (\n args. bvl_Block closure_tag
                     [bvl_CodePtr (loc + ns + 2 * n); bvl_Number (&(args - 1));
                      bvl_RefPtr T (minimal ptr. ~(ptr IN FDOM (bvl_state_refs t1)))])
                   (list_of_seq I (LENGTH ll + 1)) (APPEND (MAP FST ll) [FST x])) fvs))))
             (bvl_state_clock_fupd (combin_K ck) t1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[build_recc_lets_def] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP C2BP2AUX_eval_Ref_zeros th]) THEN
  CAKE_REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[ADD_SUB] THEN
  W(fun (asl,w) ->
    let tm = find_term (can (PART_MATCH (lhs o rand) C2BP2AUX_eval_recc_Let0_ref)) w in
    MP_TAC (PART_MATCH (lhs o rand) C2BP2AUX_eval_recc_Let0_ref tm)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH_MAP; LENGTH; bvl_state_INFO.ri_accfupds;
                GSYM ADD_ASSOC] THEN
    CONJ_TAC THENL [ARITH_TAC; FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  CAKE_REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; C2BP2AUX_HD_TL_REVERSE_SNOC; MAP_APPEND; MAP; K_THM;
              GSYM ADD_ASSOC] THEN
  REWRITE_TAC[C2BP2AUX_LUPDATE_MAP_SNOC] THEN
  MP_TAC (ISPECL [`ll:(num#clos_exp)list`; `loc:num`;
    `minimal ptr. ~(ptr IN FDOM (bvl_state_refs (t1:(C,FFI)bvl_state)))`; `env:bvl_v list`;
    `t1:(C,FFI)bvl_state`; `fvs:bvl_v list`; `[c3:bvl_exp]`; `x:num#clos_exp`;
    `x:num#clos_exp`; `ck:num`; `ns:num`] evaluate_recc_Lets) THEN
  REWRITE_TAC[HD] THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM ALL_EL; LENGTH_LIST_OF_SEQ] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; I_THM; LT_IMP_LE];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

let C2BP2AUX_eval_build_recc_lets = prove
 (`!(fns:(num#clos_exp)list) names env (t1:(C,FFI)bvl_state) fvs loc ns c3 ck.
     ~(fns = []) /\
     (!t:(C,FFI)bvl_state. bvl_evaluate (MAP bvl_Var names,env,t) = (Rval fvs,t)) /\
     (!k. k < LENGTH fns ==> loc + ns + 2 * k IN domain (bvl_state_code t1))
     ==> bvl_evaluate ([build_recc_lets (MAP FST fns) names (loc + ns) (LENGTH fns) c3],
                       env,bvl_state_clock_fupd (combin_K ck) t1) =
         bvl_evaluate ([c3],
           APPEND (MAP2 (\n args. bvl_Block closure_tag
                     [bvl_CodePtr (loc + ns + 2 * n); bvl_Number (&(args - 1));
                      bvl_RefPtr T (minimal ptr. ~(ptr IN FDOM (bvl_state_refs t1)))])
                   (list_of_seq I (LENGTH fns)) (MAP FST fns)) env,
           bvl_state_refs_fupd (combin_K (bvl_state_refs t1 |+
             ((minimal ptr. ~(ptr IN FDOM (bvl_state_refs t1))),
              bvl_ValueArray (APPEND (MAP2 (\n args. bvl_Block closure_tag
                     [bvl_CodePtr (loc + ns + 2 * n); bvl_Number (&(args - 1));
                      bvl_RefPtr T (minimal ptr. ~(ptr IN FDOM (bvl_state_refs t1)))])
                   (list_of_seq I (LENGTH fns)) (MAP FST fns)) fvs))))
             (bvl_state_clock_fupd (combin_K ck) t1))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP APPEND_BUTLAST_LAST) THEN
  SUBGOAL_THEN `LENGTH (BUTLAST (fns:(num#clos_exp)list)) + 1 = LENGTH fns` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:(num#clos_exp)list->num`) THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `APPEND (MAP FST (BUTLAST (fns:(num#clos_exp)list))) [FST (LAST fns)] =
                MAP FST fns` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM th]) THEN
    REWRITE_TAC[MAP_APPEND; MAP];
    ALL_TAC] THEN
  MP_TAC (ISPECL [`BUTLAST (fns:(num#clos_exp)list)`; `LAST (fns:(num#clos_exp)list)`;
    `names:num list`; `env:bvl_v list`; `t1:(C,FFI)bvl_state`; `fvs:bvl_v list`; `loc:num`;
    `ns:num`; `c3:bvl_exp`; `ck:num`] C2BP2AUX_eval_build_recc_lets_SNOC) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

(* the closure blocks of mutually recursive closures, in the two forms of *)
(* cl_rel and of the evaluation of build_recc_lets                          *)
let C2BP2AUX_recc_blocks = prove
 (`!(fns:(num#clos_exp)list) loc ns r.
     MAP (\((n,e),p). bvl_Block closure_tag [bvl_CodePtr p; bvl_Number (&(n - 1));
                                             bvl_RefPtr T r])
       (ZIP fns (list_of_seq (\n. loc + ns + 2 * n) (LENGTH fns))) =
     MAP2 (\n args. bvl_Block closure_tag [bvl_CodePtr (loc + ns + 2 * n);
                                           bvl_Number (&(args - 1)); bvl_RefPtr T r])
       (list_of_seq I (LENGTH fns)) (MAP FST fns)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIST_EQ] THEN
  SIMP_TAC[LENGTH_MAP; LENGTH_ZIP; LENGTH_MAP2; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_MAP; EL_ZIP; EL_MAP2; EL_LIST_OF_SEQ; LENGTH_ZIP; LENGTH_LIST_OF_SEQ;
               LENGTH_MAP; I_THM] THEN
  MP_TAC (ISPEC `EL i (fns:(num#clos_exp)list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `e:clos_exp` SUBST1_TAC)) THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

(* the code of mutually recursive closures is installed *)
let C2BP2AUX_closure_code_installed_recc = prove
 (CASE_TERM
  `!max_app fns aux1 cs auxa loc n2 auxb (t1:(C,FFI)bvl_state) env1 names.
     ALL (\p. match p with (num_args:num,e:clos_exp) ->
                num_args <= max_app /\ ~(num_args = 0)) fns /\
     clos_to_bvl_compile_exps max_app (MAP SND fns) aux1 = (cs,auxa) /\
     build_aux (loc + num_stubs max_app)
       (MAP2 (code_for_recc_case (LENGTH fns + LENGTH names)) (MAP FST fns) cs) auxa =
       (n2,auxb) /\
     clos_to_bvlProof_code_installed auxb (bvl_state_code t1) /\
     LENGTH (names:num list) = LENGTH (env1:clos_v list)
     ==> closure_code_installed max_app (bvl_state_code t1)
           (ZIP fns (list_of_seq (\n. loc + num_stubs max_app + 2 * n) (LENGTH fns))) env1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[closure_code_installed_def] THEN
  MATCH_MP_TAC EVERY_ZIP_GENLIST THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC (ISPEC `EL i (fns:(num#clos_exp)list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `num_args:num` (X_CHOOSE_THEN `e:clos_exp` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  SUBGOAL_THEN `num_args <= max_app /\ ~(num_args = 0)` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o REWRITE_RULE[GSYM ALL_EL] o
      check (is_comb o concl)) THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  MP_TAC (ISPECL [`fns:(num#clos_exp)list`; `aux1:(num#num#bvl_exp)list`; `cs:bvl_exp list`;
    `auxa:(num#num#bvl_exp)list`; `i:num`; `loc + num_stubs max_app`; `n2:num`;
    `auxb:(num#num#bvl_exp)list`; `num_args:num`; `e:clos_exp`; `max_app:num`;
    `LENGTH (fns:(num#clos_exp)list) + LENGTH (names:num list)`; `t1:(C,FFI)bvl_state`]
    compile_exps_LIST_IMP_compile_exps_EL) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[LENGTH_ZIP; LENGTH_LIST_OF_SEQ; GSYM ADD_ASSOC] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[ADD_SYM]);;

(* a new ref does not shrink the refs outside the range of f *)
let C2BP2AUX_FDIFF_SUBMAP_NEW = prove
 (`!(m:(A,B)fmap) s k v. ~(k IN FDOM m) ==> FDIFF m s SUBMAP FDIFF (m |+ (k,v)) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FDIFF_FUPDATE] THEN COND_CASES_TAC THEN
  REWRITE_TAC[SUBMAP_REFL; SUBMAP_FUPDATE_EQN; FDOM_FDIFF] THEN ASM_REWRITE_TAC[]);;

let C2BP2AUX_closure_code_installed_domain = prove
 (`!max_app code (fns:(num#clos_exp)list) loc ns env.
     closure_code_installed max_app code
       (ZIP fns (list_of_seq (\n. loc + ns + 2 * n) (LENGTH fns))) env
     ==> !k. k < LENGTH fns ==> loc + ns + 2 * k IN domain code`,
  REWRITE_TAC[closure_code_installed_def; GSYM ALL_EL] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  ASM_SIMP_TAC[LENGTH_ZIP; LENGTH_LIST_OF_SEQ; EL_ZIP; EL_LIST_OF_SEQ] THEN
  MP_TAC (ISPEC `EL k (fns:(num#clos_exp)list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `e:clos_exp` SUBST1_TAC)) THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[domain_lookup] THEN MESON_TAC[]);;

(* the values of mutually recursive closures (cl_rel rule 3) *)
let C2BP2AUX_v_rel_recc = prove
 (`!max_app f refs code (fns:(num#clos_exp)list) loc env1 fvs rr.
     ALL2 (clos_to_bvlProof_v_rel max_app f
             (refs |+ (rr,bvl_ValueArray (APPEND
                (MAP2 (\n args. bvl_Block closure_tag
                         [bvl_CodePtr (loc + num_stubs max_app + 2 * n);
                          bvl_Number (&(args - 1)); bvl_RefPtr T rr])
                   (list_of_seq I (LENGTH fns)) (MAP FST fns)) fvs))) code) env1 fvs /\
     ~(rr IN FRANGE f) /\
     1 < LENGTH fns /\
     every_Fn_SOME (MAP SND fns) /\ every_Fn_vs_SOME (MAP SND fns) /\
     closure_code_installed max_app code
       (ZIP fns (list_of_seq (\n. loc + num_stubs max_app + 2 * n) (LENGTH fns))) env1
     ==> ALL2 (clos_to_bvlProof_v_rel max_app f
                (refs |+ (rr,bvl_ValueArray (APPEND
                   (MAP2 (\n args. bvl_Block closure_tag
                            [bvl_CodePtr (loc + num_stubs max_app + 2 * n);
                             bvl_Number (&(args - 1)); bvl_RefPtr T rr])
                      (list_of_seq I (LENGTH fns)) (MAP FST fns)) fvs))) code)
           (list_of_seq (clos_Recclosure (SOME loc) [] env1 fns) (LENGTH fns))
           (MAP2 (\n args. bvl_Block closure_tag
                    [bvl_CodePtr (loc + num_stubs max_app + 2 * n);
                     bvl_Number (&(args - 1)); bvl_RefPtr T rr])
              (list_of_seq I (LENGTH fns)) (MAP FST fns))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM C2BP2AUX_recc_blocks] THEN STRIP_TAC THEN
  REWRITE_TAC[LIST_REL_EL_EQN; LENGTH_LIST_OF_SEQ] THEN
  CONJ_TAC THENL
   [SIMP_TAC[LENGTH_MAP; LENGTH_ZIP; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  MP_TAC (ISPECL [`max_app:num`; `FRANGE (f:(num,num)fmap)`;
    `(refs:(num,bvl_v bvl_ref)fmap) |+ (rr,bvl_ValueArray (APPEND
       (MAP (\((n,e),p). bvl_Block closure_tag [bvl_CodePtr p; bvl_Number (&(n - 1));
                                                bvl_RefPtr T rr])
          (ZIP (fns:(num#clos_exp)list)
             (list_of_seq (\n. loc + num_stubs max_app + 2 * n) (LENGTH fns)))) fvs))`;
    `code:(num#bvl_exp)spt`; `env1:clos_v list`; `fvs:bvl_v list`; `fns:(num#clos_exp)list`;
    `ZIP (fns:(num#clos_exp)list) (list_of_seq (\n. loc + num_stubs max_app + 2 * n) (LENGTH fns))`;
    `MAP SND (ZIP (fns:(num#clos_exp)list) (list_of_seq (\n. loc + num_stubs max_app + 2 * n) (LENGTH fns)))`;
    `loc:num`;
    `MAP (\((n,e),p). bvl_Block closure_tag [bvl_CodePtr p; bvl_Number (&(n - 1));
                                             bvl_RefPtr T rr])
       (ZIP (fns:(num#clos_exp)list) (list_of_seq (\n. loc + num_stubs max_app + 2 * n) (LENGTH fns)))`;
    `rr:num`; `k:num`] (el 2 (CONJUNCTS cl_rel_rules))) THEN
  ASM_SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP; LENGTH_ZIP; LENGTH_LIST_OF_SEQ; FLOOKUP_UPDATE_SAME] THEN
  ASM_SIMP_TAC[EL_MAP; EL_ZIP; LENGTH_ZIP; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ] THEN
  MP_TAC (ISPEC `EL k (fns:(num#clos_exp)list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `e:clos_exp` SUBST1_TAC)) THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN DISCH_TAC THEN
  MATCH_MP_TAC (el 5 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
  MAP_EVERY EXISTS_TAC [`env1:clos_v list`; `fvs:bvl_v list`] THEN ASM_REWRITE_TAC[]);;

(* HOL4: (* general case for mutually recursive closures *), as a lemma *)
let C2BP2AUX_letrec_mutual_stmt = CASE_TERM
 `!fns exp loc names env1 env (s1:(C,FFI)clos_state) res s2 aux1 cs auxa n2 auxb c3 aux2
     (t1:(C,FFI)bvl_state) env'' f1.
     (!ed aux1 (t1:(C,FFI)bvl_state) env' f1 res s2 ys aux2.
        clos_evaluate ([exp],APPEND ed env,s1) = (res,s2) /\
        ~(res = Rerr (Rabort Rtype_error)) /\
        clos_to_bvl_compile_exps (clos_state_max_app s1) [exp] aux1 = (ys,aux2) /\
        every_Fn_SOME [exp] /\ FEVERY (\p. every_Fn_SOME [SND (SND p)]) (clos_state_code s1) /\
        every_Fn_vs_SOME [exp] /\
        FEVERY (\p. every_Fn_vs_SOME [SND (SND p)]) (clos_state_code s1) /\
        clos_to_bvlProof_code_installed aux2 (bvl_state_code t1) /\
        clos_to_bvlProof_env_rel (clos_state_max_app s1) f1 (bvl_state_refs t1)
          (bvl_state_code t1) (APPEND ed env) env' /\
        clos_to_bvlProof_state_rel f1 s1 t1
        ==> ?ck res' t2 f2.
              bvl_evaluate (ys,env',bvl_state_clock_fupd (combin_K (clos_state_clock s1 + ck)) t1) =
                (res',t2) /\
              result_rel (ALL2 (clos_to_bvlProof_v_rel (clos_state_max_app s1) f2
                                  (bvl_state_refs t2) (bvl_state_code t2)))
                (clos_to_bvlProof_v_rel (clos_state_max_app s1) f2 (bvl_state_refs t2)
                   (bvl_state_code t2)) res res' /\
              clos_to_bvlProof_state_rel f2 s2 t2 /\
              f1 SUBMAP f2 /\
              FDIFF (bvl_state_refs t1) (FRANGE f1) SUBMAP
                FDIFF (bvl_state_refs t2) (FRANGE f2) /\
              FEVERY (\p. every_Fn_SOME [SND (SND p)]) (clos_state_code s2) /\
              FEVERY (\p. every_Fn_vs_SOME [SND (SND p)]) (clos_state_code s2) /\
              clos_state_clock s2 = bvl_state_clock t2) /\
     1 < LENGTH fns /\
     clos_evaluate ([exp],
                    APPEND (list_of_seq (clos_Recclosure (SOME loc) [] env1 fns) (LENGTH fns))
                      env,s1) = (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error)) /\
     every_Fn_SOME (MAP SND fns) /\ every_Fn_SOME [exp] /\
     FEVERY (\p. every_Fn_SOME [SND (SND p)]) (clos_state_code s1) /\
     every_Fn_vs_SOME (MAP SND fns) /\ every_Fn_vs_SOME [exp] /\
     FEVERY (\p. every_Fn_vs_SOME [SND (SND p)]) (clos_state_code s1) /\
     clos_to_bvl_compile_exps (clos_state_max_app s1) (MAP SND fns) aux1 = (cs,auxa) /\
     build_aux (loc + num_stubs (clos_state_max_app s1))
       (MAP2 (code_for_recc_case (LENGTH fns + LENGTH names)) (MAP FST fns) cs) auxa =
       (n2,auxb) /\
     clos_to_bvl_compile_exps (clos_state_max_app s1) [exp] auxb = ([c3],aux2) /\
     clos_to_bvlProof_code_installed aux2 (bvl_state_code t1) /\
     clos_to_bvlProof_env_rel (clos_state_max_app s1) f1 (bvl_state_refs t1)
       (bvl_state_code t1) env env'' /\
     clos_to_bvlProof_state_rel f1 s1 t1 /\
     ALL (\p. match p with (num_args:num,e:clos_exp) ->
                num_args <= clos_state_max_app s1 /\ ~(num_args = 0)) fns /\
     lookup_vars names env = SOME env1
     ==> ?ck res' t2 f2.
           bvl_evaluate ([build_recc_lets (MAP FST fns) names
                            (loc + num_stubs (clos_state_max_app s1)) (LENGTH fns) c3],env'',
                         bvl_state_clock_fupd (combin_K (clos_state_clock s1 + ck)) t1) = (res',t2) /\
           result_rel (ALL2 (clos_to_bvlProof_v_rel (clos_state_max_app s1) f2
                               (bvl_state_refs t2) (bvl_state_code t2)))
             (clos_to_bvlProof_v_rel (clos_state_max_app s1) f2 (bvl_state_refs t2)
                (bvl_state_code t2)) res res' /\
           clos_to_bvlProof_state_rel f2 s2 t2 /\
           f1 SUBMAP f2 /\
           FDIFF (bvl_state_refs t1) (FRANGE f1) SUBMAP FDIFF (bvl_state_refs t2) (FRANGE f2) /\
           FEVERY (\p. every_Fn_SOME [SND (SND p)]) (clos_state_code s2) /\
           FEVERY (\p. every_Fn_vs_SOME [SND (SND p)]) (clos_state_code s2) /\
           clos_state_clock s2 = bvl_state_clock t2`;;
let C2BP2AUX_letrec_mutual = prove
 (C2BP2AUX_letrec_mutual_stmt,
  let rs = `MAP2 (\n args. bvl_Block closure_tag
       [bvl_CodePtr (loc + num_stubs (clos_state_max_app (s1:(C,FFI)clos_state)) + 2 * n);
        bvl_Number (&(args - 1)); bvl_RefPtr T rr])
     (list_of_seq I (LENGTH (fns:(num#clos_exp)list))) (MAP FST fns)` in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* the values of the free variables *)
  FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
    MP_TAC(MATCH_MP lookup_vars_IMP2 (CONJ th1 th2)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `fvs:bvl_v list` STRIP_ASSUME_TAC) THEN
  (* the code of the closures *)
  FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
    MP_TAC(MATCH_MP compile_exps_IMP_code_installed (CONJ th1 th2)))) THEN DISCH_TAC THEN
  SUBGOAL_THEN `closure_code_installed (clos_state_max_app (s1:(C,FFI)clos_state))
     (bvl_state_code (t1:(C,FFI)bvl_state))
     (ZIP fns (list_of_seq (\n. loc + num_stubs (clos_state_max_app s1) + 2 * n) (LENGTH fns)))
     env1` ASSUME_TAC THENL
   [MATCH_MP_TAC C2BP2AUX_closure_code_installed_recc THEN
    MAP_EVERY EXISTS_TAC [`aux1:(num#num#bvl_exp)list`; `cs:bvl_exp list`;
      `auxa:(num#num#bvl_exp)list`; `n2:num`; `auxb:(num#num#bvl_exp)list`; `names:num list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C2BP2AUX_closure_code_installed_domain) THEN
  (* the new ref rr *)
  ABBREV_TAC `rr = minimal ptr. ~(ptr IN FDOM (bvl_state_refs (t1:(C,FFI)bvl_state)))` THEN
  SUBGOAL_THEN `~(rr IN FDOM (bvl_state_refs (t1:(C,FFI)bvl_state))) /\
                ~(rr IN FRANGE (f1:(num,num)fmap))` STRIP_ASSUME_TAC THENL
   [MP_TAC (ISPEC `bvl_state_refs (t1:(C,FFI)bvl_state)` LEAST_NOTIN_FDOM) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      C2BP2AUX_head (concl th) = "clos_to_bvlProof_state_rel")) THEN
    REWRITE_TAC[clos_to_bvlProof_state_rel_def] THEN SET_TAC[];
    ALL_TAC] THEN
  (* the induction hypothesis for the body, in the extended environment *)
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`list_of_seq (clos_Recclosure (SOME loc) [] env1 fns) (LENGTH (fns:(num#clos_exp)list))`;
    `auxb:(num#num#bvl_exp)list`;
    mk_comb(mk_comb(`bvl_state_refs_fupd:((num,bvl_v bvl_ref)fmap->(num,bvl_v bvl_ref)fmap)->
                       (C,FFI)bvl_state->(C,FFI)bvl_state`,
      mk_comb(`combin_K:(num,bvl_v bvl_ref)fmap->(num,bvl_v bvl_ref)fmap->(num,bvl_v bvl_ref)fmap`,
        subst [rs, `rs:bvl_v list`]
          `bvl_state_refs (t1:(C,FFI)bvl_state) |+ (rr,bvl_ValueArray (APPEND rs fvs))`)),
      `t1:(C,FFI)bvl_state`);
    subst [rs, `rs:bvl_v list`] `APPEND rs (env'':bvl_v list)`;
    `f1:(num,num)fmap`; `res:(clos_v list,clos_v)result`; `s2:(C,FFI)clos_state`;
    `[c3:bvl_exp]`; `aux2:(num#num#bvl_exp)list`] o check (C2BP2AUX_is_ih o concl)) THEN
  ASM_REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC clos_to_bvlProof_env_rel_APPEND THEN CONJ_TAC THENL
       [MATCH_MP_TAC C2BP2AUX_v_rel_recc THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC C2BP2AUX_ALL2_v_rel_mono THEN
        MAP_EVERY EXISTS_TAC [`f1:(num,num)fmap`; `bvl_state_refs (t1:(C,FFI)bvl_state)`;
                              `bvl_state_code (t1:(C,FFI)bvl_state)`] THEN
        ASM_SIMP_TAC[SUBMAP_REFL; subspt_refl; C2BP2AUX_FDIFF_SUBMAP_NEW];
        MATCH_MP_TAC env_rel_NEW_REF THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC state_rel_NEW_REF THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `res':(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `t2:(C,FFI)bvl_state` (X_CHOOSE_THEN `f2:(num,num)fmap`
      STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `ck:num` THEN
  (* the evaluation of build_recc_lets *)
  MP_TAC (ISPECL [`fns:(num#clos_exp)list`; `names:num list`; `env'':bvl_v list`;
    `t1:(C,FFI)bvl_state`; `fvs:bvl_v list`; `loc:num`;
    `num_stubs (clos_state_max_app (s1:(C,FFI)clos_state))`; `c3:bvl_exp`;
    `clos_state_clock (s1:(C,FFI)clos_state) + ck`] C2BP2AUX_eval_build_recc_lets) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvl_state_INFO.ri_fupdcanon]) THEN
  REWRITE_TAC[bvl_state_INFO.ri_fupdcanon] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`res':(bvl_v list,bvl_v)result`; `t2:(C,FFI)bvl_state`;
                        `f2:(num,num)fmap`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBMAP_TRANS THEN
  EXISTS_TAC (subst [rs, `rs:bvl_v list`]
    `FDIFF (bvl_state_refs (t1:(C,FFI)bvl_state) |+ (rr,bvl_ValueArray (APPEND rs fvs)))
           (FRANGE (f1:(num,num)fmap))`) THEN
  ASM_SIMP_TAC[C2BP2AUX_FDIFF_SUBMAP_NEW] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> C2BP2AUX_head (concl th) = "SUBMAP" &&
                                          C2BP2AUX_head (lhand (concl th)) = "FDIFF")) THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM]);;

(* HOL4: THEN1 (* Letrec *) *)
let C2BP2AUX_cer_Letrec = prove
 (C2BP2AUX_cer_goal 9,
  C2BP2AUX_CER_INTRO_TAC THEN
  FS[clos_evaluate_def; clos_to_bvl_compile_exps_def] THEN
  C2BP2AUX_ASM_CASES_TAC (CASE_TERM `ALL (\p. match p with (num_args:num,e:clos_exp) ->
      num_args <= clos_state_max_app (s1:(C,FFI)clos_state) /\ ~(num_args = 0)) fns`) THEN
  FS[] THEN
  CASES_ON `loc:num option` THEN FS[] THEN CASES_ON `namesopt:(num list)option` THEN FS[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LET_DEF; LET_END_DEF]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
  C2BP2AUX_CASES_ON `lookup_vars a' (env':clos_v list)` THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[OPTION_MAP_DEF]) THEN FS[] THEN
  CASES_ON `fns:(num#clos_exp)list` THENL
   [(* no functions: the induction hypothesis with ed = [] *)
    FS[LIST_OF_SEQ; LENGTH; APPEND] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `[]:clos_v list`) THEN REWRITE_TAC[APPEND] THEN DISCH_TAC THEN
    C2BP2AUX_IH_TAC [] THEN REWRITE_TAC[];
    ALL_TAC] THEN
  C2BP2AUX_PAIR_CASES_TAC `a0:num#clos_exp` `num_args:num` `body:clos_exp` THEN
  CASES_ON `a1:(num#clos_exp)list` THENL
   [(* special case for singly-recursive closure *)
    FS[LIST_OF_SEQ; LENGTH; APPEND; MAP; ALL] THEN REPEAT PAIRARG_TAC THEN FS[] THEN
    RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LISTAUX_list_of_seq_1; APPEND]) THEN
    IMP_RES_TAC clos_to_bvl_compile_exps_SING THEN RVEQ_TAC THEN
    REPEAT(FIRST_X_ASSUM(fun th -> if is_exists(concl th) then CAKE_STRIP_ASSUME_TAC th
                                   else NO_TAC)) THEN
    RVEQ_TAC THEN FS[HD] THEN
    FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
      MP_TAC(MATCH_MP compile_exps_IMP_code_installed (CONJ th1 th2)))) THEN
    REWRITE_TAC[C2BP2AUX_code_installed_CONS] THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
      MP_TAC(MATCH_MP lookup_vars_IMP2 (CONJ th1 th2)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `fvs:bvl_v list` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `[clos_Recclosure (SOME a) [] a'' [num_args,body] 0]` o
                  check (C2BP2AUX_is_ih o concl)) THEN
    REWRITE_TAC[APPEND] THEN DISCH_TAC THEN
    C2BP2AUX_IH_TAC
      [(`CONS (bvl_Block closure_tag
           (CONS (bvl_CodePtr (a + num_stubs (clos_state_max_app (s1:(C,FFI)clos_state))))
              (CONS (bvl_Number (&(num_args - 1))) fvs))) env''`, "env'");
       (`t1:(C,FFI)bvl_state`, "t1")] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[clos_to_bvlProof_env_rel_def] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC C2BP2AUX_v_rel_Rec1 THEN
      MAP_EVERY EXISTS_TAC [`aux1:(num#num#bvl_exp)list`; `d':bvl_exp`;
                            `aux1':(num#num#bvl_exp)list`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH (a':num list) = LENGTH (a'':clos_v list)`]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `ck:num` THEN
    MP_TAC(ISPECL [`a':num list`; `env'':bvl_v list`;
      `bvl_state_clock_fupd (combin_K (clos_state_clock (s1:(C,FFI)clos_state) + ck))
         (t1:(C,FFI)bvl_state)`;
      `fvs:bvl_v list`; `&(num_args - 1):int`;
      `a + num_stubs (clos_state_max_app (s1:(C,FFI)clos_state))`; `closure_tag`]
      C2BP2AUX_eval_Fn_code) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[bvl_state_INFO.ri_accfupds; domain_lookup] THEN ASM_MESON_TAC[];
      DISCH_TAC] THEN
    ONCE_REWRITE_TAC[bvl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
    CAKE_REWRITE_TAC[APPEND] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`res':(bvl_v list,bvl_v)result`; `t2:(C,FFI)bvl_state`;
                          `f2:(num,num)fmap`] THEN ASM_REWRITE_TAC[];
    (* general case for mutually recursive closures *)
    RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN REPEAT PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN
    IMP_RES_TAC clos_to_bvl_compile_exps_SING THEN RVEQ_TAC THEN
    REPEAT(FIRST_X_ASSUM(fun th -> if is_exists(concl th) then CAKE_STRIP_ASSUME_TAC th
                                   else NO_TAC)) THEN
    RVEQ_TAC THEN REWRITE_TAC[HD] THEN
    MP_TAC (ISPECL [`CONS (num_args,body) (CONS a0' a1'):(num#clos_exp)list`; `exp:clos_exp`;
      `a:num`; `a':num list`; `a'':clos_v list`; `env':clos_v list`; `s1:(C,FFI)clos_state`;
      `res:(clos_v list,clos_v)result`; `s2:(C,FFI)clos_state`; `aux1:(num#num#bvl_exp)list`;
      `cs:bvl_exp list`; `aux1':(num#num#bvl_exp)list`; `n2:num`;
      `aux2':(num#num#bvl_exp)list`; `d:bvl_exp`; `aux2:(num#num#bvl_exp)list`;
      `t1:(C,FFI)bvl_state`; `env'':bvl_v list`; `f1:(num,num)fmap`]
      C2BP2AUX_letrec_mutual) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
      REWRITE_TAC[LENGTH; MAP; ALL; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
      TRY ARITH_TAC THEN FS[];
      REWRITE_TAC[LENGTH; MAP]]]);;

(* helpers for the Op case *)

(* a new ref on both sides, related by f |+ (pp,qq) (HOL4 does this inline *)
(* in the Ref, RefArray, RefByte and AllocThunk cases)                      *)

let C2BP2AUX_v_rel_NEW_BOTH = prove
 (`!max_app f (t:(C,FFI)bvl_state) a b pp qq y.
     clos_to_bvlProof_v_rel max_app f (bvl_state_refs t) (bvl_state_code t) a b /\
     ~(pp IN FDOM f) /\ ~(qq IN FDOM (bvl_state_refs t))
     ==> clos_to_bvlProof_v_rel max_app (f |+ (pp,qq)) (bvl_state_refs t |+ (qq,y))
           (bvl_state_code t) a b`,
  MESON_TAC[v_rel_NEW_F; v_rel_NEW_REF]);;

let C2BP2AUX_ALL2_v_rel_NEW_BOTH = prove
 (`!max_app f (t:(C,FFI)bvl_state) xs ys pp qq y.
     ALL2 (clos_to_bvlProof_v_rel max_app f (bvl_state_refs t) (bvl_state_code t)) xs ys /\
     ~(pp IN FDOM f) /\ ~(qq IN FDOM (bvl_state_refs t))
     ==> ALL2 (clos_to_bvlProof_v_rel max_app (f |+ (pp,qq)) (bvl_state_refs t |+ (qq,y))
                 (bvl_state_code t)) xs ys`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th ->
    C2BP2AUX_head (concl th) = "ALL2")) THEN
  MATCH_MP_TAC MONO_ALL2 THEN ASM_MESON_TAC[C2BP2AUX_v_rel_NEW_BOTH]);;

let C2BP2AUX_OPTREL_v_rel_NEW_BOTH = prove
 (`!max_app f (t:(C,FFI)bvl_state) x z pp qq y.
     OPTREL (clos_to_bvlProof_v_rel max_app f (bvl_state_refs t) (bvl_state_code t)) x z /\
     ~(pp IN FDOM f) /\ ~(qq IN FDOM (bvl_state_refs t))
     ==> OPTREL (clos_to_bvlProof_v_rel max_app (f |+ (pp,qq)) (bvl_state_refs t |+ (qq,y))
                   (bvl_state_code t)) x z`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th ->
    C2BP2AUX_head (concl th) = "OPTREL")) THEN
  MATCH_MP_TAC OPTREL_MONO THEN ASM_MESON_TAC[C2BP2AUX_v_rel_NEW_BOTH]);;

let C2BP2AUX_ref_rel_mono = prove
 (`!(R:A->B->bool) Q x y.
     (!a b. R a b ==> Q a b) /\ clos_to_bvlProof_ref_rel R x y
     ==> clos_to_bvlProof_ref_rel Q x y`,
  REPEAT GEN_TAC THEN CASES_ON `x:A clos_ref` THEN CASES_ON `y:B bvl_ref` THEN
  REWRITE_TAC[clos_to_bvlProof_ref_rel_def] THEN
  MESON_TAC[MONO_ALL2]);;

let C2BP2AUX_state_rel_NEW_BOTH = prove
 (`!f (s1:(C,FFI)clos_state) (t1:(C,FFI)bvl_state) pp qq x y.
     clos_to_bvlProof_state_rel f s1 t1 /\
     ~(pp IN FDOM (clos_state_refs s1)) /\ ~(qq IN FDOM (bvl_state_refs t1)) /\
     clos_to_bvlProof_ref_rel (clos_to_bvlProof_v_rel (clos_state_max_app s1) f
        (bvl_state_refs t1) (bvl_state_code t1)) x y /\
     (!bs. ~(y = bvl_ByteArray T bs))
     ==> clos_to_bvlProof_state_rel (f |+ (pp,qq))
           (clos_state_refs_fupd (combin_K (clos_state_refs s1 |+ (pp,x))) s1)
           (bvl_state_refs_fupd (combin_K (bvl_state_refs t1 |+ (qq,y))) t1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_to_bvlProof_state_rel_def] THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; bvl_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(pp IN FDOM (f:(num,num)fmap)) /\ ~(qq IN FRANGE (f:(num,num)fmap))`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> C2BP2AUX_head (concl th) = "ALL2")) THEN
    MATCH_MP_TAC MONO_ALL2 THEN ASM_MESON_TAC[C2BP2AUX_OPTREL_v_rel_NEW_BOTH];
    UNDISCH_TAC `INJ (FAPPLY (f:(num,num)fmap)) (FDOM f) (FRANGE f)` THEN
    UNDISCH_TAC `~(pp IN FDOM (f:(num,num)fmap))` THEN
    UNDISCH_TAC `~(qq IN FRANGE (f:(num,num)fmap))` THEN
    REWRITE_TAC[INJ; IN_FRANGE; FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM] THEN
    MESON_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP_UPDATE] THEN COND_CASES_TAC THENL
     [REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[option_INJ];
      DISCH_TAC THEN
      SUBGOAL_THEN `~(qq = (y':num))` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[FRANGE_FLOOKUP]; ASM_MESON_TAC[]]];
    ASM_REWRITE_TAC[FDOM_FUPDATE];
    UNDISCH_TAC `FRANGE (f:(num,num)fmap) SUBSET FDOM (bvl_state_refs (t1:(C,FFI)bvl_state))` THEN
    REWRITE_TAC[SUBSET; FRANGE_FLOOKUP; FDOM_FUPDATE; IN_INSERT; FLOOKUP_UPDATE] THEN
    MESON_TAC[option_INJ];
    X_GEN_TAC `n:num` THEN X_GEN_TAC `z:clos_v clos_ref` THEN REWRITE_TAC[FLOOKUP_UPDATE] THEN
    COND_CASES_TAC THENL
     [REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MAP_EVERY EXISTS_TAC [`y:bvl_v bvl_ref`; `qq:num`] THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC C2BP2AUX_ref_rel_mono THEN
      EXISTS_TAC `clos_to_bvlProof_v_rel (clos_state_max_app (s1:(C,FFI)clos_state)) f
        (bvl_state_refs (t1:(C,FFI)bvl_state)) (bvl_state_code t1)` THEN
      ASM_SIMP_TAC[C2BP2AUX_v_rel_NEW_BOTH];
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `z:clos_v clos_ref`] o check (fun th ->
        can (find_term (fun t -> try fst(dest_const t) = "clos_to_bvlProof_ref_rel"
                                 with Failure _ -> false)) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `y0:bvl_v bvl_ref` (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`y0:bvl_v bvl_ref`; `m:num`] THEN
      SUBGOAL_THEN `~(qq = (m:num))` ASSUME_TAC THENL
       [ASM_MESON_TAC[FLOOKUP_DEF; distinctness "option"]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC C2BP2AUX_ref_rel_mono THEN
      EXISTS_TAC `clos_to_bvlProof_v_rel (clos_state_max_app (s1:(C,FFI)clos_state)) f
        (bvl_state_refs (t1:(C,FFI)bvl_state)) (bvl_state_code t1)` THEN
      ASM_SIMP_TAC[C2BP2AUX_v_rel_NEW_BOTH]]]);;
let C2BP2AUX_FDIFF_NEW_BOTH = prove
 (`!(refs:(num,B)fmap) (f:(num,num)fmap) pp qq y.
     ~(pp IN FDOM f) /\ ~(qq IN FDOM refs)
     ==> FDIFF refs (FRANGE f) SUBMAP FDIFF (refs |+ (qq,y)) (FRANGE (f |+ (pp,qq)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBMAP_FLOOKUP_EQN; FLOOKUP_FDIFF; IN_FRANGE_FLOOKUP; FLOOKUP_UPDATE] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(qq = (x:num))` ASSUME_TAC THENL
   [ASM_MESON_TAC[FLOOKUP_DEF; distinctness "option"]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_MESON_TAC[option_INJ; FLOOKUP_DEF]);;

(* the cases of the operations: the result of closSem's do_app, related to *)
(* the result of bvlSem's do_app on the compiled operation, with f extended *)
let C2BP2AUX_op_goal op =
  let tm = vsubst [op, `opx:clos_op`]
   `!xs (s1:(C,FFI)clos_state) v s2 f (t1:(C,FFI)bvl_state) ys.
      clos_do_app opx xs s1 = Rval (v,s2) /\
      clos_to_bvlProof_state_rel f s1 t1 /\
      ALL2 (clos_to_bvlProof_v_rel (clos_state_max_app s1) f (bvl_state_refs t1)
              (bvl_state_code t1)) xs ys
      ==> ?w t2 f2.
            bvl_do_app (clos_to_bvl_compile_op opx) ys t1 = Rval (w,t2) /\
            clos_to_bvlProof_v_rel (clos_state_max_app s1) f2 (bvl_state_refs t2)
              (bvl_state_code t2) v w /\
            clos_to_bvlProof_state_rel f2 s2 t2 /\
            f SUBMAP f2 /\
            FDIFF (bvl_state_refs t1) (FRANGE f) SUBMAP
              FDIFF (bvl_state_refs t2) (FRANGE f2)` in
  list_mk_forall (frees op, tm);;

(* HOL4: Cases_on `op = MemOp Ref` *)
let C2BP2AUX_op_Ref = prove
 (C2BP2AUX_op_goal `MemOp clos_Ref`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; injectivity "result"; PAIR_EQ] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN RVEQ_TAC THEN
  FS[] THEN
  MP_TAC (ISPEC `clos_state_refs (s1:(C,FFI)clos_state)` LEAST_NOTIN_FDOM) THEN
  MP_TAC (ISPEC `bvl_state_refs (t1:(C,FFI)bvl_state)` LEAST_NOTIN_FDOM) THEN
  ABBREV_TAC `pp = minimal ptr. ~(ptr IN FDOM (clos_state_refs (s1:(C,FFI)clos_state)))` THEN
  ABBREV_TAC `qq = minimal ptr. ~(ptr IN FDOM (bvl_state_refs (t1:(C,FFI)bvl_state)))` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `~(pp IN FDOM (f:(num,num)fmap))` ASSUME_TAC THENL
   [ASM_MESON_TAC[clos_to_bvlProof_state_rel_def]; ALL_TAC] THEN
  EXISTS_TAC `(f:(num,num)fmap) |+ (pp,qq)` THEN
  ASM_SIMP_TAC[C2BP2AUX_state_rel_NEW_BOTH; C2BP2AUX_FDIFF_NEW_BOTH; SUBMAP_FUPDATE_EQN;
               clos_to_bvlProof_ref_rel_def; distinctness "bvl_ref"] THEN
  MATCH_MP_TAC (el 4 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
  REWRITE_TAC[FLOOKUP_UPDATE]);;

(* v_rel for given shapes of the clos value (v_rel_SIMP without the        *)
(* closure cases)                                                           *)
let C2BP2AUX_v_rel_inv = end_itlist CONJ
  (map GEN_ALL (butlast (butlast (CONJUNCTS (SPEC_ALL v_rel_SIMP)))));;

(* HOL4: Cases_on `op = MemOp Update` *)
let C2BP2AUX_op_Update = prove
 (C2BP2AUX_op_goal `MemOp Update`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  STRIP_TAC THEN GVS[clos_case_eq_thms; COND_CASE_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C2BP2AUX_v_rel_inv]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_exists(concl th) then CAKE_STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN RVEQ_TAC THEN
  FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 -> FIRST_ASSUM(fun th3 ->
    MP_TAC (MATCH_MP state_rel_refs_lookup (CONJ th1 (CONJ th2 th3)))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:bvl_v bvl_ref` STRIP_ASSUME_TAC) THEN
  CASES_ON `z:bvl_v bvl_ref` THEN RULE_ASSUM_TAC(REWRITE_RULE[clos_to_bvlProof_ref_rel_def]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  ASM_REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH o check (fun th ->
    C2BP2AUX_head (concl th) = "ALL2")) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM((fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) o check (fun th ->
    is_eq (concl th) && C2BP2AUX_head (lhs (concl th)) = "LENGTH")) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`bvl_state_refs_fupd (combin_K (bvl_state_refs t1 |+
      (r2,bvl_ValueArray (LUPDATE (y'':bvl_v) (num_of_int a) a')))) (t1:(C,FFI)bvl_state)`;
    `f:(num,num)fmap`] THEN
  REWRITE_TAC[SUBMAP_REFL; bvl_state_INFO.ri_accfupds; K_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC state_rel_UPDATE_REF THEN
    EXISTS_TAC `clos_ValueArray (a:clos_v list)` THEN
    ASM_REWRITE_TAC[distinctness "bvl_ref"; clos_to_bvlProof_ref_rel_def] THEN
    MATCH_MP_TAC EVERY2_LUPDATE_same THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(r2:num) IN FRANGE (f:(num,num)fmap)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FRANGE_FLOOKUP]; ASM_REWRITE_TAC[FDIFF_FUPDATE; SUBMAP_REFL]]]);;

(* the steps of the cases with a new ref on both sides *)
let C2BP2AUX_NEW_REF_OP_TAC extra =
  MP_TAC (ISPEC `clos_state_refs (s1:(C,FFI)clos_state)` LEAST_NOTIN_FDOM) THEN
  MP_TAC (ISPEC `bvl_state_refs (t1:(C,FFI)bvl_state)` LEAST_NOTIN_FDOM) THEN
  ABBREV_TAC `pp = minimal ptr. ~(ptr IN FDOM (clos_state_refs (s1:(C,FFI)clos_state)))` THEN
  ABBREV_TAC `qq = minimal ptr. ~(ptr IN FDOM (bvl_state_refs (t1:(C,FFI)bvl_state)))` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `~(pp IN FDOM (f:(num,num)fmap))` ASSUME_TAC THENL
   [ASM_MESON_TAC[clos_to_bvlProof_state_rel_def]; ALL_TAC] THEN
  EXISTS_TAC `(f:(num,num)fmap) |+ (pp,qq)` THEN
  ASM_SIMP_TAC([C2BP2AUX_state_rel_NEW_BOTH; C2BP2AUX_FDIFF_NEW_BOTH; SUBMAP_FUPDATE_EQN;
                clos_to_bvlProof_ref_rel_def; distinctness "bvl_ref"] @ extra) THEN
  MATCH_MP_TAC (el 4 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
  REWRITE_TAC[FLOOKUP_UPDATE];;

(* closSem's do_app of the given shape, unfolded, its result substituted *)
let C2BP2AUX_OP_UNFOLD_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  STRIP_TAC THEN GVS[clos_case_eq_thms; COND_CASE_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LET_DEF; LET_END_DEF]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C2BP2AUX_v_rel_inv; injectivity "result"; PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_exists(concl th) then CAKE_STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[injectivity "result"; PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1];;

(* HOL4: Cases_on `op = MemOp RefArray` *)
let C2BP2AUX_op_RefArray = prove
 (C2BP2AUX_op_goal `MemOp RefArray`,
  C2BP2AUX_OP_UNFOLD_TAC THEN FS[] THEN
  C2BP2AUX_NEW_REF_OP_TAC [LIST_REL_REPLICATE_same]);;

(* HOL4: Cases_on `?flag. op = MemOp (RefByte flag)` *)
let C2BP2AUX_op_RefByte = prove
 (C2BP2AUX_op_goal `MemOp (RefByte fl)`,
  C2BP2AUX_OP_UNFOLD_TAC THEN
  SUBGOAL_THEN `?w':byte. &(val (w:byte)) = (&(val w'):int)` (fun th -> REWRITE_TAC[th]) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  FS[] THEN C2BP2AUX_NEW_REF_OP_TAC [injectivity "bvl_ref"]);;

(* the ref of a clos RefPtr argument and the related bvl ref *)
let C2BP2AUX_REF_LOOKUP_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[C2BP2AUX_v_rel_inv]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_exists(concl th) then CAKE_STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN RVEQ_TAC THEN
  FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 -> FIRST_ASSUM(fun th3 ->
    MP_TAC (MATCH_MP state_rel_refs_lookup (CONJ th1 (CONJ th2 th3)))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:bvl_v bvl_ref` STRIP_ASSUME_TAC) THEN
  CASES_ON `z:bvl_v bvl_ref` THEN RULE_ASSUM_TAC(REWRITE_RULE[clos_to_bvlProof_ref_rel_def]) THEN
  TRY(FIRST_ASSUM CONTR_TAC);;

(* HOL4: Cases_on `op = MemOp UpdateByte` *)
let C2BP2AUX_op_UpdateByte = prove
 (C2BP2AUX_op_goal `MemOp UpdateByte`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  STRIP_TAC THEN GVS[clos_case_eq_thms; COND_CASE_EQ] THEN
  C2BP2AUX_REF_LOOKUP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[i2w_pos; WORD_VAL] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?w':byte. &(val (w:byte)) = (&(val w'):int)` (fun th -> REWRITE_TAC[th]) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[injectivity "result"; PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  EXISTS_TAC `f:(num,num)fmap` THEN
  REWRITE_TAC[SUBMAP_REFL; bvl_state_INFO.ri_accfupds; K_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC state_rel_UPDATE_REF THEN
    EXISTS_TAC `clos_ByteArray a1':clos_v clos_ref` THEN
    ASM_REWRITE_TAC[distinctness "bvl_ref"; injectivity "bvl_ref";
                    clos_to_bvlProof_ref_rel_def];
    SUBGOAL_THEN `(r2:num) IN FRANGE (f:(num,num)fmap)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FRANGE_FLOOKUP]; ASM_REWRITE_TAC[FDIFF_FUPDATE; SUBMAP_REFL]]]);;
let C2BP2AUX_state_rel_ffi = prove
 (`!f (s:(C,FFI)clos_state) (t:(C,FFI)bvl_state) ffi.
     clos_to_bvlProof_state_rel f s t
     ==> clos_to_bvlProof_state_rel f (clos_state_ffi_fupd (combin_K ffi) s)
           (bvl_state_ffi_fupd (combin_K ffi) t)`,
  REWRITE_TAC[clos_to_bvlProof_state_rel_def; clos_state_INFO.ri_accfupds;
              bvl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT GEN_TAC THEN CONV_TAC TAUT);;

(* HOL4: Cases_on `?n. op = FFI n` *)
let C2BP2AUX_op_FFI = prove
 (C2BP2AUX_op_goal `clos_FFI n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  STRIP_TAC THEN GVS[clos_case_eq_thms; COND_CASE_EQ] THEN
  C2BP2AUX_REF_LOOKUP_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[clos_to_bvlProof_state_rel_def] o
    check (fun th -> C2BP2AUX_head (concl th) = "clos_to_bvlProof_state_rel")) THEN
  ASM_REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM (ASSUME `clos_state_ffi (s1:(C,FFI)clos_state) =
                            bvl_state_ffi (t1:(C,FFI)bvl_state)`)] THEN
  C2BP2AUX_CASES_ON `call_FFI (clos_state_ffi (s1:(C,FFI)clos_state)) (ExtCall n) a a1'` THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[injectivity "result"; distinctness "result"; PAIR_EQ]) THEN
  CAKE_REWRITE_TAC[] THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN RVEQ_TAC THEN FS[] THEN
  EXISTS_TAC `f:(num,num)fmap` THEN
  REWRITE_TAC[SUBMAP_REFL; bvl_state_INFO.ri_accfupds; K_THM] THEN
  CONJ_TAC THENL
   [MP_TAC (ISPECL [`f:(num,num)fmap`; `clos_state_ffi_fupd (combin_K a0) (s1:(C,FFI)clos_state)`;
      `bvl_state_ffi_fupd (combin_K a0) (t1:(C,FFI)bvl_state)`; `a1:num`; `r2:num`;
      `clos_ByteArray a1':clos_v clos_ref`; `clos_ByteArray a1'':clos_v clos_ref`;
      `bvl_ByteArray F a1'':bvl_v bvl_ref`] state_rel_UPDATE_REF) THEN
    REWRITE_TAC[clos_state_INFO.ri_accfupds; bvl_state_INFO.ri_accfupds; K_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[C2BP2AUX_state_rel_ffi; distinctness "bvl_ref"; injectivity "bvl_ref";
                 clos_to_bvlProof_ref_rel_def];
    SUBGOAL_THEN `(r2:num) IN FRANGE (f:(num,num)fmap)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FRANGE_FLOOKUP]; ASM_REWRITE_TAC[FDIFF_FUPDATE; SUBMAP_REFL]]]);;
let C2BP2AUX_MAP_Number_11 = prove
 (`!x y:num list. MAP (bvl_Number o int_of_num) x = MAP (bvl_Number o int_of_num) y <=> x = y`,
  MP_TAC (ISPEC `bvl_Number o int_of_num` INJECTIVE_MAP) THEN
  REWRITE_TAC[o_THM; injectivity "bvl_v"; INT_OF_NUM_EQ] THEN MESON_TAC[]);;

let C2BP2AUX_ALL2_v_rel_Numbers = prove
 (`!max_app f refs code (ns:num list) l.
     ALL2 (clos_to_bvlProof_v_rel max_app f refs code) (MAP (clos_Number o int_of_num) ns) l <=>
     l = MAP (bvl_Number o int_of_num) ns`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; LIST_REL_NIL] THEN
  GEN_TAC THEN REWRITE_TAC[LIST_REL_CONS1; C2BP2AUX_v_rel_inv; o_THM] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* the steps of the cases with a new ref (an immutable byte array) on the bvl side only *)
let C2BP2AUX_NEW_BVL_REF_TAC =
  FS[] THEN
  MP_TAC (ISPEC `bvl_state_refs (t1:(C,FFI)bvl_state)` LEAST_NOTIN_FDOM) THEN
  ABBREV_TAC `qq = minimal ptr. ~(ptr IN FDOM (bvl_state_refs (t1:(C,FFI)bvl_state)))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(qq IN FRANGE (f:(num,num)fmap))` ASSUME_TAC THENL
   [ASM_MESON_TAC[clos_to_bvlProof_state_rel_def; SUBSET]; ALL_TAC] THEN
  EXISTS_TAC `f:(num,num)fmap` THEN
  ASM_SIMP_TAC[state_rel_NEW_REF; C2BP2AUX_FDIFF_SUBMAP_NEW; SUBMAP_REFL] THEN
  MATCH_MP_TAC (el 3 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
  ASM_REWRITE_TAC[FLOOKUP_UPDATE];;

(* HOL4: Cases_on`op = MemOp FromListByte` *)
let C2BP2AUX_op_FromListByte = prove
 (C2BP2AUX_op_goal `MemOp FromListByte`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  STRIP_TAC THEN GVS[clos_case_eq_thms; COND_CASE_EQ] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o BETA_RULE o MATCH_MP BASICAUX_some_SOME) THEN
  FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
    MP_TAC (MATCH_MP clos_to_bvlProof_v_to_list (CONJ th1 th2)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `l':bvl_v list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[C2BP2AUX_ALL2_v_rel_Numbers] o check (fun th ->
    C2BP2AUX_head (concl th) = "ALL2")) THEN
  ASM_REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(some ns. bvl_v_to_list y = SOME (MAP (bvl_Number o int_of_num) ns) /\
                          ALL (\n. n < 256) ns) = SOME (a:num list)` SUBST1_TAC THENL
   [MATCH_MP_TAC BASICAUX_some_unique THEN BETA_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
    MESON_TAC[C2BP2AUX_MAP_Number_11];
    ALL_TAC] THEN
  CAKE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  C2BP2AUX_NEW_BVL_REF_TAC);;
let C2BP2AUX_ALL2_v_rel_ByteVectors = prove
 (`!max_app f refs code wss l.
     ALL2 (clos_to_bvlProof_v_rel max_app f refs code) (MAP ByteVector wss) l <=>
     ?ps. l = MAP (bvl_RefPtr T) ps /\
          MAP (FLOOKUP refs) ps = MAP (SOME o bvl_ByteArray T) wss /\
          ALL (\p. ~(p IN FRANGE f)) ps`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; LIST_REL_NIL] THENL
   [REWRITE_TAC[MAP_EQ_NIL] THEN MESON_TAC[MAP; ALL]; ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[LIST_REL_CONS1; C2BP2AUX_v_rel_inv; o_THM] THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `CONS (p:num) ps` THEN ASM_REWRITE_TAC[MAP; ALL];
    DISCH_THEN(X_CHOOSE_THEN `ps:num list` MP_TAC) THEN
    STRUCT_CASES_TAC(ISPEC `ps:num list` list_CASES) THEN
    REWRITE_TAC[MAP; ALL; NOT_CONS_NIL; CONS_11; o_THM] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`bvl_RefPtr T h'`; `MAP (bvl_RefPtr T) t'`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `h':num` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `t':num list` THEN ASM_REWRITE_TAC[]]]);;

let C2BP2AUX_MAP_INJ = prove
 (`!(f:A->B) l m. (!x y. f x = f y ==> x = y) /\ MAP f l = MAP f m ==> l = m`,
  MESON_TAC[INJECTIVE_MAP]);;

(* HOL4: Cases_on`op = MemOp ConcatByteVec` *)
let C2BP2AUX_op_ConcatByteVec = prove
 (C2BP2AUX_op_goal `MemOp ConcatByteVec`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  STRIP_TAC THEN GVS[clos_case_eq_thms; COND_CASE_EQ] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o BETA_RULE o MATCH_MP BASICAUX_some_SOME) THEN
  FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
    MP_TAC (MATCH_MP clos_to_bvlProof_v_to_list (CONJ th1 th2)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `l':bvl_v list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[C2BP2AUX_ALL2_v_rel_ByteVectors] o
    check (fun th -> C2BP2AUX_head (concl th) = "ALL2")) THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(some wss. ?ps. bvl_v_to_list y = SOME (MAP (bvl_RefPtr T) ps) /\
     MAP (FLOOKUP (bvl_state_refs (t1:(C,FFI)bvl_state))) ps = MAP (SOME o bvl_ByteArray T) wss) =
     SOME (a:(byte list) list)` SUBST1_TAC THENL
   [MATCH_MP_TAC BASICAUX_some_unique THEN BETA_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC `ps:num list` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:(byte list) list` THEN
      DISCH_THEN(X_CHOOSE_THEN `ps':num list` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `ps':num list = ps` SUBST_ALL_TAC THENL
       [MATCH_MP_TAC (ISPEC `bvl_RefPtr T` C2BP2AUX_MAP_INJ) THEN
        REWRITE_TAC[injectivity "bvl_v"] THEN ASM_MESON_TAC[option_INJ];
        ALL_TAC] THEN
      MATCH_MP_TAC (ISPEC `(SOME o bvl_ByteArray T):byte list->(bvl_v bvl_ref)option` C2BP2AUX_MAP_INJ) THEN
      REWRITE_TAC[o_THM; option_INJ; injectivity "bvl_ref"] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  CAKE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[injectivity "result"; PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  C2BP2AUX_NEW_BVL_REF_TAC);;

(* the steps after bvlSem's do_app of the cases that update a ref *)
let C2BP2AUX_UPDATE_REF_FINISH_TAC v0 =
  REWRITE_TAC[injectivity "result"; PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  EXISTS_TAC `f:(num,num)fmap` THEN
  REWRITE_TAC[SUBMAP_REFL; bvl_state_INFO.ri_accfupds; K_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC state_rel_UPDATE_REF THEN EXISTS_TAC v0 THEN
    ASM_REWRITE_TAC[distinctness "bvl_ref"; injectivity "bvl_ref";
                    clos_to_bvlProof_ref_rel_def];
    SUBGOAL_THEN `(r2:num) IN FRANGE (f:(num,num)fmap)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FRANGE_FLOOKUP]; ASM_REWRITE_TAC[FDIFF_FUPDATE; SUBMAP_REFL]]];;

(* HOL4: Cases_on`?fl. op = MemOp XorByte` *)
let C2BP2AUX_op_XorByte = prove
 (C2BP2AUX_op_goal `MemOp XorByte`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  STRIP_TAC THEN GVS[clos_case_eq_thms; COND_CASE_EQ] THEN
  C2BP2AUX_REF_LOOKUP_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  C2BP2AUX_UPDATE_REF_FINISH_TAC `clos_ByteArray a1':clos_v clos_ref`);;
(* ref_rel for given shapes of the clos ref *)
let C2BP2AUX_ref_rel_inv = prove
 (`!(R:A->B->bool) vs as m v y.
     (clos_to_bvlProof_ref_rel R (clos_ValueArray vs) y <=>
      ?ws. y = bvl_ValueArray ws /\ ALL2 R vs ws) /\
     (clos_to_bvlProof_ref_rel R (clos_ByteArray as) y <=> y = bvl_ByteArray F as) /\
     (clos_to_bvlProof_ref_rel R (clos_Thunk m v) y <=> ?w. y = bvl_Thunk m w /\ R v w)`,
  REPEAT GEN_TAC THEN CASES_ON `y:B bvl_ref` THEN
  REWRITE_TAC[clos_to_bvlProof_ref_rel_def; distinctness "bvl_ref"; injectivity "bvl_ref"] THEN
  MESON_TAC[]);;

(* state_rel_refs_lookup for every clos ref p with FLOOKUP f p = SOME r in the *)
(* assumptions whose bvl ref r is not looked up yet, the bvl refs inverted   *)
let C2BP2AUX_ALL_LOOKUPS_TAC : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  let is_lk name th = let c = concl th in
    is_eq c && C2BP2AUX_head (lhs c) = "FLOOKUP" &&
    (try C2BP2AUX_head (lhand (lhs c)) = name with Failure _ -> false) in
  let srel = find (fun th -> C2BP2AUX_head (concl th) = "clos_to_bvlProof_state_rel") ths in
  let clos_lk = filter (is_lk "clos_state_refs") ths in
  let f_lk = filter (fun th -> let c = concl th in
    is_eq c && C2BP2AUX_head (lhs c) = "FLOOKUP" && is_var (lhand (lhs c)) &&
    type_of (lhand (lhs c)) = `:(num,num)fmap`) ths in
  let bvl_has r = exists (fun th -> is_lk "bvl_state_refs" th && rand (lhs (concl th)) = r) ths in
  let pairs = itlist (fun c acc -> map (fun fl -> (c,fl)) f_lk @ acc) clos_lk [] in
  let res = mapfilter (fun (c,fl) ->
    let r = rand (rhs (concl fl)) in
    if bvl_has r then failwith "done" else
    MATCH_MP state_rel_refs_lookup (CONJ srel (CONJ c fl))) pairs in
  if res = [] then ALL_TAC g else
  (MAP_EVERY (fun th -> STRIP_ASSUME_TAC (REWRITE_RULE[C2BP2AUX_ref_rel_inv] th)) res THEN
   RVEQ_TAC) g;;
(* the witness of ?v. ... /\ FLOOKUP m p = SOME v /\ ... from an assumption *)
(* FLOOKUP m' p = SOME t                                                      *)
let C2BP2AUX_EXISTS_FROM_ASM_TAC : tactic = fun (asl,w as g) ->
  let v,body = dest_exists w in
  let c = find (fun c -> vfree_in v c && is_eq c && C2BP2AUX_head (lhs c) = "FLOOKUP")
               (conjuncts body) in
  let th = find (fun th -> let a = concl th in
                   is_eq a && C2BP2AUX_head (lhs a) = "FLOOKUP" &&
                   rand (lhs a) = rand (lhs c) && C2BP2AUX_head (rhs a) = "SOME" &&
                   type_of (rhs a) = type_of (rhs c)) (map snd asl) in
  EXISTS_TAC (rand (rhs (concl th))) g;;

(* the steps after bvlSem's do_app of the cases that update a ref *)
let C2BP2AUX_UPDATE_REF_FINISH2_TAC =
  REWRITE_TAC[injectivity "result"; PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  EXISTS_TAC `f:(num,num)fmap` THEN
  REWRITE_TAC[SUBMAP_REFL; bvl_state_INFO.ri_accfupds; K_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC state_rel_UPDATE_REF THEN C2BP2AUX_EXISTS_FROM_ASM_TAC THEN
    ASM_REWRITE_TAC[distinctness "bvl_ref"; injectivity "bvl_ref";
                    clos_to_bvlProof_ref_rel_def];
    REWRITE_TAC[FDIFF_FUPDATE] THEN COND_CASES_TAC THEN REWRITE_TAC[SUBMAP_REFL] THEN
    ASM_MESON_TAC[FRANGE_FLOOKUP]];;
(* HOL4: Cases_on`?fl. op = MemOp (CopyByte fl)` *)
let C2BP2AUX_op_CopyByte = prove
 (C2BP2AUX_op_goal `MemOp (CopyByte fl)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  STRIP_TAC THEN GVS[clos_case_eq_thms; COND_CASE_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C2BP2AUX_v_rel_inv]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_exists(concl th) then CAKE_STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN RVEQ_TAC THEN
  C2BP2AUX_ALL_LOOKUPS_TAC THEN
  ASM_REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  FIRST [C2BP2AUX_UPDATE_REF_FINISH2_TAC;
         REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
         C2BP2AUX_NEW_BVL_REF_TAC]);;
let C2BP2AUX_bad_thunk_update = prove
 (`!f (s:(C,FFI)clos_state) (t:(C,FFI)bvl_state) m v y.
     clos_to_bvlProof_state_rel f s t /\
     clos_to_bvlProof_v_rel (clos_state_max_app s) f (bvl_state_refs t) (bvl_state_code t) v y /\
     ~clos_bad_thunk_update m v (clos_state_refs s)
     ==> ~bvl_bad_thunk_update m y (bvl_state_refs t)`,
  REWRITE_TAC[clos_bad_thunk_update_def; bvl_bad_thunk_update_def] THEN
  MESON_TAC[rel_dest_thunk_NotThunk]);;
(* HOL4: Cases_on `?t. op = ThunkOp t` (ForceThunk is not an operation of do_app) *)
let C2BP2AUX_op_ThunkOp = prove
 (C2BP2AUX_op_goal `clos_ThunkOp th`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  STRIP_TAC THEN GVS[clos_case_eq_thms; COND_CASE_EQ] THENL
   [(* AllocThunk *)
    FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 -> FIRST_ASSUM(fun th3 ->
      ASSUME_TAC (MATCH_MP C2BP2AUX_bad_thunk_update (CONJ th1 (CONJ th2 th3)))))) THEN
    ASM_REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    FS[] THEN C2BP2AUX_NEW_REF_OP_TAC [];
    (* UpdateThunk *)
    CASES_ON `a0:thunk_mode` THEN
    RULE_ASSUM_TAC(CAKE_REWRITE_RULE[injectivity "result"; distinctness "result"; PAIR_EQ]) THEN
    TRY(FIRST_ASSUM CONTR_TAC) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[C2BP2AUX_v_rel_inv]) THEN
    REPEAT(FIRST_X_ASSUM(fun th -> if is_exists(concl th) then CAKE_STRIP_ASSUME_TAC th
                                   else NO_TAC)) THEN RVEQ_TAC THEN
    C2BP2AUX_ALL_LOOKUPS_TAC THEN
    FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 -> FIRST_ASSUM(fun th3 ->
      ASSUME_TAC (MATCH_MP C2BP2AUX_bad_thunk_update (CONJ th1 (CONJ th2 th3)))))) THEN
    ASM_REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    FS[] THEN C2BP2AUX_UPDATE_REF_FINISH2_TAC]);;

(* HOL4: Cases_on `?c. op = BlockOp (Constant c)` *)
let C2BP2AUX_op_Constant = prove
 (C2BP2AUX_op_goal `BlockOp (Constant c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  STRIP_TAC THEN GVS[clos_case_eq_thms; COND_CASE_EQ] THEN
  REWRITE_TAC[clos_to_bvl_compile_op_def] THEN
  ASM_CASES_TAC `?i. c = ConstCons i []` THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC) THEN
    REWRITE_TAC[compile_const_def; NULL; make_const_def; MAP] THEN
    REWRITE_TAC[bvl_do_app_Cons] THEN FS[] THEN
    EXISTS_TAC `f:(num,num)fmap` THEN ASM_REWRITE_TAC[SUBMAP_REFL] THEN
    MATCH_MP_TAC (el 2 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN REWRITE_TAC[ALL2];
    ALL_TAC] THEN
  ASM_CASES_TAC `?i. c = ConstInt i` THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC) THEN
    REWRITE_TAC[compile_const_def; make_const_def] THEN
    REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[CONJUNCT1 bvl_do_int_app_def] THEN CAKE_REWRITE_TAC[] THEN FS[] THEN
    EXISTS_TAC `f:(num,num)fmap` THEN ASM_REWRITE_TAC[SUBMAP_REFL] THEN
    REWRITE_TAC[clos_to_bvlProof_v_rel_rules];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!i. ~(c = ConstInt i)) /\ (!t. ~(c = ConstCons t []))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP compile_const_thm th]) THEN
  REWRITE_TAC[make_const_thm; bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  MP_TAC (ISPEC `bvl_do_build_const (MAP update_tag (clos_constantProof_to_parts c))
      (bvl_state_refs (t1:(C,FFI)bvl_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:bvl_v` (X_CHOOSE_THEN `rs:(num,bvl_v bvl_ref)fmap`
    (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))) THEN
  CAKE_REWRITE_TAC[] THEN
  MP_TAC (ISPECL [`clos_constantProof_to_parts c`; `t1:(C,FFI)bvl_state`; `v:bvl_v`;
    `rs:(num,bvl_v bvl_ref)fmap`; `f:(num,num)fmap`; `s2:(C,FFI)clos_state`;
    `f:(num,num)fmap`; `t1:(C,FFI)bvl_state`] do_build_const_thm) THEN
  ASM_REWRITE_TAC[SUBMAP_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:(num,num)fmap` STRIP_ASSUME_TAC) THEN
  FS[] THEN EXISTS_TAC `f2:(num,num)fmap` THEN ASM_REWRITE_TAC[]);;

(* one case of C2BP2AUX_do_app_Rval: op of the shape tm, by the lemma *)
let C2BP2AUX_OP_CASE_TAC tm lemma =
  ASM_CASES_TAC tm THENL
   [FIRST_X_ASSUM(REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
    MATCH_MP_TAC lemma THEN EXISTS_TAC `xs:clos_v list` THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(* the operations other than ForceThunk (HOL4: the cases on op after the   *)
(* arguments of Op are evaluated)                                           *)
let C2BP2AUX_do_app_Rval = prove
 (`!op xs (s1:(C,FFI)clos_state) v s2 f (t1:(C,FFI)bvl_state) ys.
     clos_do_app op xs s1 = Rval (v,s2) /\
     clos_to_bvlProof_state_rel f s1 t1 /\
     ALL2 (clos_to_bvlProof_v_rel (clos_state_max_app s1) f (bvl_state_refs t1)
             (bvl_state_code t1)) xs ys /\
     ~(op = clos_ThunkOp ForceThunk)
     ==> ?w t2 f2.
           bvl_do_app (clos_to_bvl_compile_op op) ys t1 = Rval (w,t2) /\
           clos_to_bvlProof_v_rel (clos_state_max_app s1) f2 (bvl_state_refs t2)
             (bvl_state_code t2) v w /\
           clos_to_bvlProof_state_rel f2 s2 t2 /\
           f SUBMAP f2 /\
           FDIFF (bvl_state_refs t1) (FRANGE f) SUBMAP FDIFF (bvl_state_refs t2) (FRANGE f2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C2BP2AUX_OP_CASE_TAC `?c. op = BlockOp (Constant c)` C2BP2AUX_op_Constant THEN
  C2BP2AUX_OP_CASE_TAC `op = MemOp clos_Ref` C2BP2AUX_op_Ref THEN
  C2BP2AUX_OP_CASE_TAC `op = MemOp Update` C2BP2AUX_op_Update THEN
  C2BP2AUX_OP_CASE_TAC `op = MemOp RefArray` C2BP2AUX_op_RefArray THEN
  C2BP2AUX_OP_CASE_TAC `?fl. op = MemOp (RefByte fl)` C2BP2AUX_op_RefByte THEN
  C2BP2AUX_OP_CASE_TAC `op = MemOp UpdateByte` C2BP2AUX_op_UpdateByte THEN
  C2BP2AUX_OP_CASE_TAC `?n. op = clos_FFI n` C2BP2AUX_op_FFI THEN
  C2BP2AUX_OP_CASE_TAC `op = MemOp FromListByte` C2BP2AUX_op_FromListByte THEN
  C2BP2AUX_OP_CASE_TAC `op = MemOp ConcatByteVec` C2BP2AUX_op_ConcatByteVec THEN
  C2BP2AUX_OP_CASE_TAC `op = MemOp XorByte` C2BP2AUX_op_XorByte THEN
  C2BP2AUX_OP_CASE_TAC `?fl. op = MemOp (CopyByte fl)` C2BP2AUX_op_CopyByte THEN
  C2BP2AUX_OP_CASE_TAC `?th. op = clos_ThunkOp th` C2BP2AUX_op_ThunkOp THEN
  (* the other operations: f unchanged *)
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
  MP_TAC (ISPECL [`op:clos_op`; `xs:clos_v list`; `s1:(C,FFI)clos_state`; `v:clos_v`;
    `s2:(C,FFI)clos_state`; `f:(num,num)fmap`; `t1:(C,FFI)bvl_state`; `ys:bvl_v list`]
    clos_to_bvlProof_do_app) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:bvl_v` (X_CHOOSE_THEN `t2:(C,FFI)bvl_state`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`w:bvl_v`; `t2:(C,FFI)bvl_state`; `f:(num,num)fmap`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th =
    `bvl_state_refs (t1:(C,FFI)bvl_state) = bvl_state_refs (t2:(C,FFI)bvl_state)`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th =
    `bvl_state_code (t1:(C,FFI)bvl_state) = bvl_state_code (t2:(C,FFI)bvl_state)`)) THEN
  ASM_REWRITE_TAC[SUBMAP_REFL]);;

(* the evaluation of force_thunk_code (HOL4 does it inline in the          *)
(* ForceThunk case): it runs the compiled AppUnit (Var None 0) and updates  *)
(* the thunk                                                                *)

let C2BP2AUX_compile_AppUnit = prove
 (`!max_app aux.
     clos_to_bvl_compile_exps max_app [clos_AppUnit (clos_Var backend_common_None 0)] aux =
     ([bvl_Let [bvl_Op (BlockOp (clos_Cons 0)) []; bvl_Var 0]
         (mk_cl_call (bvl_Var 1) [bvl_Var 0])],aux)`,
  REWRITE_TAC[clos_AppUnit_def] THEN ONCE_REWRITE_TAC[clos_to_bvl_compile_exps_def] THEN
  REWRITE_TAC[clos_to_bvl_compile_exps_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_to_bvl_compile_op_def; clos_tag_shift_def; HD; APPEND; LENGTH;
              LISTAUX_list_of_seq_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LISTAUX_list_of_seq_1]);;

let C2BP2AUX_case_Rerr_same = prove
 (CASE_TERM
  `!(p:(bvl_v list,bvl_v)result#(C,FFI)bvl_state)
    (f:bvl_v list->(C,FFI)bvl_state->((bvl_v list,bvl_v)result#(C,FFI)bvl_state)).
     (match p with (x,s1) -> (match x with Rval vs -> f vs s1 | Rerr a -> (x,s1))) =
     (match p with (x,s1) -> (match x with Rval vs -> f vs s1 | Rerr e -> (Rerr e,s1)))`,
  REPEAT GEN_TAC THEN
  C2BP2AUX_PAIR_CASES_TAC `p:(bvl_v list,bvl_v)result#(C,FFI)bvl_state`
    `r:(bvl_v list,bvl_v)result` `s1:(C,FFI)bvl_state` THEN
  CASES_ON `r:(bvl_v list,bvl_v)result` THEN CAKE_REWRITE_TAC[]);;

let C2BP2AUX_If_Let = prove
 (CASE_TERM
  `!x y z k env (s:(C,FFI)bvl_state).
     bvl_evaluate ([bvl_If x (bvl_Let [y] k) (bvl_Let [z] k)],env,s) =
     match bvl_evaluate ([bvl_If x y z],env,s) with
       (Rval vs,s1) -> bvl_evaluate ([k],APPEND vs env,s1)
     | (Rerr e,s1) -> (Rerr e,s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_evaluate_def] THEN
  C2BP2AUX_PAIR_CASES_TAC `bvl_evaluate ([x],env,(s:(C,FFI)bvl_state))`
    `r:(bvl_v list,bvl_v)result` `s1:(C,FFI)bvl_state` THEN
  CASES_ON `r:(bvl_v list,bvl_v)result` THEN CAKE_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  CAKE_REWRITE_TAC[C2BP2AUX_case_Rerr_same]);;

let C2BP2AUX_eval_force_thunk_code = prove
 (CASE_TERM
  `!thv clv (s:(C,FFI)bvl_state).
     bvl_evaluate ([force_thunk_code],[thv; clv],s) =
     match bvl_evaluate ([bvl_Let [bvl_Op (BlockOp (clos_Cons 0)) []; bvl_Var 0]
                            (mk_cl_call (bvl_Var 1) [bvl_Var 0])],[clv],s) with
       (Rval vs,s1) ->
         (match bvl_do_app (clos_ThunkOp (UpdateThunk Evaluated)) [thv; HD vs] s1 with
            Rval (u,s2) -> (Rval [HD vs],s2)
          | Rerr e -> (Rerr e,s1))
     | (Rerr e,s1) -> (Rerr e,s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[force_thunk_code_def; C2BP2AUX_If_Let] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [bvl_evaluate_def] THEN
  CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bvl_evaluate ([bvl_Op (BlockOp (clos_Cons 0)) []; bvl_Var 0],[clv],
                              (s:(C,FFI)bvl_state)) = (Rval [bvl_Block 0 []; clv],s)`
    SUBST1_TAC THENL
   [REWRITE_TAC[bvl_evaluate_def] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[LENGTH; LT_0; EL; HD; REVERSE; APPEND; bvl_do_app_Cons] THEN
    CAKE_REWRITE_TAC[] THEN REWRITE_TAC[HD];
    ALL_TAC] THEN
  CAKE_REWRITE_TAC[APPEND] THEN
  SUBGOAL_THEN `bvl_evaluate ([mk_cl_call (bvl_Var 1) [bvl_Var 0]],[bvl_Block 0 []; clv; clv],
                  (s:(C,FFI)bvl_state)) =
                bvl_evaluate ([bvl_If (bvl_Op (BlockOp (EqualConst (clos_Int (&0))))
                                         [bvl_Op (BlockOp (ElemAt 1)) [bvl_Var 1]])
                    (bvl_Call 0 NONE [bvl_Op (BlockOp (clos_Cons 0)) []; bvl_Var 1;
                                      bvl_Op (BlockOp (ElemAt 0)) [bvl_Var 1]])
                    (bvl_Call 0 (SOME 0) [bvl_Op (BlockOp (clos_Cons 0)) []; bvl_Var 1])],
                  [thv; clv],s)` SUBST1_TAC THENL
   [REWRITE_TAC[mk_cl_call_def; LENGTH; generic_app_fn_location_def; APPEND] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bvl_evaluate_def] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[LENGTH; LT_0; EL; HD; TL; REVERSE; APPEND; bvl_do_app_Cons;
                C2BP2AUX_EL_CONS_ONE; ARITH_RULE `1 < SUC (SUC n)`] THEN
    CAKE_REWRITE_TAC[] THEN REWRITE_TAC[HD];
    ALL_TAC] THEN
  W(fun (asl,w) ->
    let tm = find_term (fun t -> C2BP2AUX_head t = "bvl_evaluate" &&
                         (try C2BP2AUX_head (hd (dest_list (fst (dest_pair (rand t))))) = "bvl_If"
                          with Failure _ -> false)) (lhs w) in
    MP_TAC (ISPEC tm PAIR_SURJECTIVE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(bvl_v list,bvl_v)result` (X_CHOOSE_THEN `s1:(C,FFI)bvl_state`
    (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))) THEN
  CASES_ON `r:(bvl_v list,bvl_v)result` THEN CAKE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP bvl_evaluate_SING) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:bvl_v` SUBST1_TAC) THEN
  REWRITE_TAC[bvl_evaluate_def; APPEND; HD] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH; LT_0; EL; HD; TL; REVERSE; APPEND; C2BP2AUX_EL_CONS_ONE;
              ARITH_RULE `1 < SUC (SUC n)`] THEN
  CAKE_REWRITE_TAC[] THEN
  C2BP2AUX_CASES_ON `bvl_do_app (clos_ThunkOp (UpdateThunk Evaluated)) [thv; v]
                       (s1:(C,FFI)bvl_state)` THEN
  CAKE_REWRITE_TAC[] THEN
  TRY(C2BP2AUX_PAIR_CASES_TAC `a:bvl_v#(C,FFI)bvl_state` `u:bvl_v` `s2:(C,FFI)bvl_state`) THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH; LT_0; EL; HD; TL; REVERSE; APPEND; C2BP2AUX_EL_CONS_ONE;
              ARITH_RULE `1 < SUC (SUC n)`] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH; LT_0; EL; HD; TL; REVERSE; APPEND; C2BP2AUX_EL_CONS_ONE;
              ARITH_RULE `1 < SUC (SUC n)`]);;
let C2BP2AUX_dest_thunk_IsThunk = prove
 (`!vs refs m v.
     clos_dest_thunk vs refs = clos_IsThunk m v
     ==> ?ptr. vs = [clos_RefPtr F ptr] /\ FLOOKUP refs ptr = SOME (clos_Thunk m v)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[clos_dest_thunk_def; distinctness "dest_thunk_ret"] THEN
  CASES_ON `t:clos_v list` THEN REWRITE_TAC[clos_dest_thunk_def; distinctness "dest_thunk_ret"] THEN
  CASES_ON `h:clos_v` THEN REWRITE_TAC[clos_dest_thunk_def; distinctness "dest_thunk_ret"] THEN
  REPEAT GEN_TAC THEN
  C2BP2AUX_CASES_ON `FLOOKUP (refs:(num,clos_v clos_ref)fmap) a1` THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "dest_thunk_ret"] THEN
  REPEAT (TOP_CASE_TAC THEN
          ASM_REWRITE_TAC[distinctness "dest_thunk_ret"; injectivity "dest_thunk_ret"]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `a1:num` THEN ASM_REWRITE_TAC[]);;

let C2BP2AUX_update_thunk_SOME = prove
 (`!b ptr refs vs refs'.
     clos_update_thunk [clos_RefPtr b ptr] refs vs = SOME refs'
     ==> ~b /\ ?v x. vs = [v] /\ clos_dest_thunk [v] refs = clos_NotThunk /\
                     FLOOKUP refs ptr = SOME (clos_Thunk NotEvaluated x) /\
                     refs' = refs |+ (ptr,clos_Thunk Evaluated v)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `vs:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_update_thunk_def; distinctness "option"] THEN
  STRUCT_CASES_TAC(ISPEC `t:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_update_thunk_def; distinctness "option"] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "option"] THEN
  C2BP2AUX_CASES_ON `clos_dest_thunk [h] (refs:(num,clos_v clos_ref)fmap)` THEN
  CAKE_REWRITE_TAC[distinctness "option"] THEN
  REWRITE_TAC[store_thunk_def] THEN
  C2BP2AUX_CASES_ON `FLOOKUP (refs:(num,clos_v clos_ref)fmap) ptr` THEN
  CAKE_REWRITE_TAC[distinctness "option"] THEN
  REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[distinctness "option"; injectivity "option"]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MAP_EVERY EXISTS_TAC [`h:clos_v`; `a1:clos_v`] THEN
  ASM_REWRITE_TAC[]);;

(* Lemmas for the Install case of the Op case (HOL4 lines 3703-4005) *)

(* closSem's do_install, when it does not fail with a type error *)
let C2BP2AUX_do_install_inv = prove
 (`!vs (s:(C,FFI)clos_state) res s'.
     clos_do_install vs s = (res,s') /\ ~(res = Rerr (Rabort Rtype_error))
     ==> ?v1 v2 cfg exps aux cfg'.
           vs = [v1; v2] /\
           clos_state_compile_oracle s 0 = (cfg,exps,aux) /\
           DISJOINT (FDOM (clos_state_code s)) (set_of_list (MAP FST aux)) /\
           ALL_DISTINCT (MAP FST aux) /\
           clos_state_compile s cfg (exps,aux) =
             SOME (THE (clos_v_to_bytes v1),THE (clos_v_to_words v2),cfg') /\
           IS_SOME (clos_v_to_bytes v1) /\ IS_SOME (clos_v_to_words v2) /\
           FST (clos_state_compile_oracle s 1) = cfg' /\ ~(exps = []) /\
           s' = clos_state_code_fupd (combin_K (clos_state_code s |++ aux))
                  (clos_state_compile_oracle_fupd (combin_K (shift_seq 1 (clos_state_compile_oracle s)))
                     (clos_state_clock_fupd (combin_K (clos_state_clock s - 1)) s)) /\
           res = (if clos_state_clock s = 0 then Rerr (Rabort Rtimeout_error) else Rval exps)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_install_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"]) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  TRY (MESON_TAC[] THEN NO_TAC) THEN
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`a0:clos_v`; `a0':clos_v`; `x:C`; `x''':clos_exp list`;
    `y''':(num#num#clos_exp)list`; `y'':C`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[shift_seq_def; ADD_CLAUSES]) THEN RULE_ASSUM_TAC BETA_RULE THEN
  ASM_REWRITE_TAC[THE_DEF; IS_SOME_DEF; shift_seq_def]);;

let C2BP2AUX_I_PAIR_MAP = prove
 (`!(g:A->B) (p:C#A). (I ## g) p = (FST p,g (SND p))`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM; I_THM]);;

(* the compile oracles and compilers of related states (compile_oracle_inv) *)
let C2BP2AUX_oracle_facts = prove
 (`!f (s:(C,FFI)clos_state) (t:(C,FFI)bvl_state).
     clos_to_bvlProof_state_rel f s t
     ==> (!n. bvl_state_compile_oracle t n =
              (FST (clos_state_compile_oracle s n),
               clos_to_bvl_compile_inc' (clos_state_max_app s)
                 (SND (clos_state_compile_oracle s n)))) /\
         (!cfg p. clos_state_compile s cfg p =
                  bvl_state_compile t cfg (clos_to_bvl_compile_inc' (clos_state_max_app s) p)) /\
         (!n. ALL_DISTINCT (MAP FST (SND (bvl_state_compile_oracle t n)))) /\
         DISJOINT (domain (bvl_state_code t))
           (set_of_list (MAP FST (SND (bvl_state_compile_oracle t 0))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_to_bvlProof_state_rel_def; compile_oracle_inv_def] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!n. ALL_DISTINCT (MAP FST (SND (bvl_state_compile_oracle (t:(C,FFI)bvl_state) n)))`
    ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `FST (bvl_state_compile_oracle (t:(C,FFI)bvl_state) n)`;
      `SND (bvl_state_compile_oracle (t:(C,FFI)bvl_state) n)`] o check (fun th ->
        can (find_term ((=) `ALL_DISTINCT:num list->bool`)) (concl th) &&
        is_forall (concl th))) THEN
    REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (domain (bvl_state_code (t:(C,FFI)bvl_state)))
     (set_of_list (MAP FST (SND (bvl_state_compile_oracle t 0))))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th ->
      can (find_term ((=) `domain:(num#bvl_exp)spt->num->bool`)) (concl th) &&
      is_forall (concl th))) THEN
    REWRITE_TAC[clos_to_bvlProof_nth_code_def; union_LN];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[o_THM; pure_co_def; C2BP2AUX_I_PAIR_MAP; pure_cc_def; LET_DEF; LET_END_DEF]);;

(* the code that clos_to_bvl's compile_inc makes starts with a function of no *)
(* arguments (the first of chain_exps)                                         *)
let C2BP2AUX_compile_inc_CONS = prove
 (`!max_app exps aux. ?k d rest.
     clos_to_bvl_compile_inc' max_app (exps,aux) = CONS (k,0,d) rest`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_to_bvl_compile_inc'_def; clos_to_bvl_compile_prog_def] THEN
  MP_TAC (ISPEC `extract_name exps` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `res:clos_exp list` SUBST1_TAC)) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CAKE_REWRITE_TAC[] THEN
  X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `k2:clos_exp` (X_CHOOSE_THEN `other:(num#num#clos_exp)list`
    SUBST1_TAC)) (SPECL [`n:num`; `res:clos_exp list`] chain_exps_cons) THEN
  REWRITE_TAC[APPEND; MAP; o_THM] THEN
  MP_TAC (ISPEC `clos_to_bvl_compile_exps max_app
     (CONS k2 (MAP (SND o SND) (APPEND other (aux:(num#num#clos_exp)list)))) []` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ne:bvl_exp list` (X_CHOOSE_THEN `au:(num#num#bvl_exp)list`
    (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))) THEN
  CAKE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP clos_to_bvl_compile_exps_LENGTH) THEN
  STRUCT_CASES_TAC(ISPEC `ne:bvl_exp list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC] THEN DISCH_TAC THEN
  REWRITE_TAC[MAP2_DEF; APPEND; HD; TL] THEN CAKE_REWRITE_TAC[] THEN
  MESON_TAC[]);;
let C2BP2AUX_MEM_MAP2_prog = prove
 (CASE_TERM
  `!(prog:(num#num#clos_exp)list) (ne:bvl_exp list) j ns a b c.
     j < LENGTH prog /\ LENGTH ne = LENGTH prog /\ EL j prog = (a,b,c)
     ==> MEM (a + ns,b,EL j ne)
           (MAP2 (\p (exp:bvl_exp). match p with (loc,args,_) -> (loc + ns,args,exp)) prog ne)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN (CASE_TERM `(a + ns,b,EL j (ne:bvl_exp list)) =
     EL j (MAP2 (\p (exp:bvl_exp). match p with (loc,args,_) -> (loc + ns,args,exp))
             (prog:(num#num#clos_exp)list) ne)`) SUBST1_TAC THENL
   [ASM_SIMP_TAC[EL_MAP2] THEN CAKE_REWRITE_TAC[];
    MATCH_MP_TAC MEM_EL THEN ASM_SIMP_TAC[LENGTH_MAP2]]);;

(* bvlSem's do_install on the values related to those of closSem's *)
let C2BP2AUX_bvl_do_install = prove
 (`!f (s:(C,FFI)clos_state) (t:(C,FFI)bvl_state) v1 v2 w1 w2 cfg exps aux cfg'.
     clos_to_bvlProof_state_rel f s t /\
     clos_to_bvlProof_v_rel (clos_state_max_app s) f (bvl_state_refs t) (bvl_state_code t) v1 w1 /\
     clos_to_bvlProof_v_rel (clos_state_max_app s) f (bvl_state_refs t) (bvl_state_code t) v2 w2 /\
     clos_state_compile_oracle s 0 = (cfg,exps,aux) /\
     clos_state_compile s cfg (exps,aux) =
       SOME (THE (clos_v_to_bytes v1),THE (clos_v_to_words v2),cfg') /\
     IS_SOME (clos_v_to_bytes v1) /\ IS_SOME (clos_v_to_words v2) /\
     FST (clos_state_compile_oracle s 1) = cfg'
     ==> ?k d rest.
           clos_to_bvl_compile_inc' (clos_state_max_app s) (exps,aux) = CONS (k,0,d) rest /\
           bvl_do_install [w1; w2] t =
             (Rval (bvl_CodePtr k,
                   bvl_state_code_fupd (combin_K (sptree_union (bvl_state_code t)
                     (fromAList (clos_to_bvl_compile_inc' (clos_state_max_app s) (exps,aux)))))
                     (bvl_state_compile_oracle_fupd
                        (combin_K (shift_seq 1 (bvl_state_compile_oracle t))) t))
              :(bvl_v#(C,FFI)bvl_state,bvl_v)result)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C2BP2AUX_oracle_facts) THEN
  X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `d:bvl_exp` (X_CHOOSE_THEN `rest:(num#num#bvl_exp)list`
    ASSUME_TAC)) (SPECL [`clos_state_max_app (s:(C,FFI)clos_state)`; `exps:clos_exp list`;
      `aux:(num#num#clos_exp)list`] C2BP2AUX_compile_inc_CONS) THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `d:bvl_exp`; `rest:(num#num#bvl_exp)list`] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_EXISTS]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `dt:int64 list` ASSUME_TAC o check (fun th ->
    is_exists (concl th) && can (find_term (fun t -> try fst(dest_const t) = "clos_v_to_words"
                                                      with Failure _ -> false)) (concl th))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `bs:byte list` ASSUME_TAC o check (fun th ->
    is_exists (concl th) && can (find_term (fun t -> try fst(dest_const t) = "clos_v_to_bytes"
                                                      with Failure _ -> false)) (concl th))) THEN
  SUBGOAL_THEN `bvl_state_compile (t:(C,FFI)bvl_state) cfg (CONS (k,0,d) rest) =
                SOME (bs,dt,cfg')` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`cfg:C`; `(exps,aux):clos_prog`] o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "bvl_state_compile"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[THE_DEF] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[bvl_do_install_def] THEN CAKE_REWRITE_TAC[] THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP clos_to_bvlProof_v_rel_IMP_v_to_bytes th]) o
    check (fun th -> rand (concl th) = `w1:bvl_v`)) THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP clos_to_bvlProof_v_rel_IMP_v_to_words th]) o
    check (fun th -> rand (concl th) = `w2:bvl_v`)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall (concl th) &&
    can (find_term ((=) `ALL_DISTINCT:num list->bool`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term ((=) `DISJOINT:(num->bool)->(num->bool)->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[shift_seq_def; ADD_CLAUSES] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES]);;

let C2BP2AUX_bvl_do_install_k = prove
 (`!f (s:(C,FFI)clos_state) (t:(C,FFI)bvl_state) v1 v2 w1 w2 cfg exps aux cfg' k d rest.
     clos_to_bvlProof_state_rel f s t /\
     clos_to_bvlProof_v_rel (clos_state_max_app s) f (bvl_state_refs t) (bvl_state_code t) v1 w1 /\
     clos_to_bvlProof_v_rel (clos_state_max_app s) f (bvl_state_refs t) (bvl_state_code t) v2 w2 /\
     clos_state_compile_oracle s 0 = (cfg,exps,aux) /\
     clos_state_compile s cfg (exps,aux) =
       SOME (THE (clos_v_to_bytes v1),THE (clos_v_to_words v2),cfg') /\
     IS_SOME (clos_v_to_bytes v1) /\ IS_SOME (clos_v_to_words v2) /\
     FST (clos_state_compile_oracle s 1) = cfg' /\
     clos_to_bvl_compile_inc' (clos_state_max_app s) (exps,aux) = CONS (k,0,d) rest
     ==> bvl_do_install [w1; w2] t =
           (Rval (bvl_CodePtr k,
                  bvl_state_code_fupd (combin_K (sptree_union (bvl_state_code t)
                    (fromAList (CONS (k,0,d) rest))))
                    (bvl_state_compile_oracle_fupd
                       (combin_K (shift_seq 1 (bvl_state_compile_oracle t))) t))
            :(bvl_v#(C,FFI)bvl_state,bvl_v)result)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL C2BP2AUX_bvl_do_install) THEN
  ASM_REWRITE_TAC[CONS_11; PAIR_EQ] THEN MESON_TAC[]);;

(* the states after an Install (the code and the oracles) are related *)
let C2BP2AUX_state_rel_install = prove
 (`!f (s:(C,FFI)clos_state) (t:(C,FFI)bvl_state) cfg exps aux.
     clos_to_bvlProof_state_rel f s t /\
     clos_state_compile_oracle s 0 = (cfg,exps,aux) /\
     DISJOINT (FDOM (clos_state_code s)) (set_of_list (MAP FST aux)) /\
     ALL_DISTINCT (MAP FST aux)
     ==> clos_to_bvlProof_state_rel f
           (clos_state_code_fupd (combin_K (clos_state_code s |++ aux))
              (clos_state_compile_oracle_fupd (combin_K (shift_seq 1 (clos_state_compile_oracle s))) s))
           (bvl_state_code_fupd (combin_K (sptree_union (bvl_state_code t)
               (fromAList (clos_to_bvl_compile_inc' (clos_state_max_app s) (exps,aux)))))
              (bvl_state_compile_oracle_fupd (combin_K (shift_seq 1 (bvl_state_compile_oracle t))) t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C2BP2AUX_oracle_facts) THEN
  ABBREV_TAC `nw = clos_to_bvl_compile_inc' (clos_state_max_app (s:(C,FFI)clos_state)) (exps,aux)` THEN
  SUBGOAL_THEN `bvl_state_compile_oracle (t:(C,FFI)bvl_state) 0 = (cfg,nw)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "nw" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `clos_to_bvlProof_state_rel f (s:(C,FFI)clos_state) (t:(C,FFI)bvl_state)` THEN
  REWRITE_TAC[clos_to_bvlProof_state_rel_def; clos_state_INFO.ri_accfupds;
              bvl_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* the globals *)
    FIRST_X_ASSUM(MP_TAC o check (fun th -> C2BP2AUX_head (concl th) = "ALL2")) THEN
      MATCH_MP_TAC MONO_ALL2 THEN REPEAT GEN_TAC THEN MATCH_MP_TAC OPTREL_MONO THEN
      REWRITE_TAC[v_rel_union];
    (* the refs *)
    REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:clos_v clos_ref`] o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> try fst(dest_const t) =
          "clos_to_bvlProof_ref_rel" with Failure _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`y:bvl_v bvl_ref`; `m:num`] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC C2BP2AUX_ref_rel_mono THEN
      EXISTS_TAC `clos_to_bvlProof_v_rel (clos_state_max_app (s:(C,FFI)clos_state)) f
        (bvl_state_refs (t:(C,FFI)bvl_state)) (bvl_state_code t)` THEN
      ASM_REWRITE_TAC[v_rel_union];
    (* the stubs *)
    REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[lookup_union; option_CASE];
    REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[lookup_union; option_CASE];
    ASM_REWRITE_TAC[lookup_union; option_CASE];
    (* the compile oracle *)
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[compile_oracle_inv_def] o check (fun th ->
        C2BP2AUX_head (concl th) = "compile_oracle_inv")) THEN
      REWRITE_TAC[compile_oracle_inv_def] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; shift_seq_def; o_THM] THEN ASM_REWRITE_TAC[o_THM];
        REWRITE_TAC[shift_seq_def] THEN ASM_MESON_TAC[];
        X_GEN_TAC `n:num` THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `SUC n` o check (fun th ->
          can (find_term ((=) `domain:(num#bvl_exp)spt->num->bool`)) (concl th) &&
          is_forall (concl th))) THEN
        REWRITE_TAC[clos_to_bvlProof_nth_code_def; shift_seq_def; ADD1; union_assoc] THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_THM; pure_co_def; C2BP2AUX_I_PAIR_MAP];
        REWRITE_TAC[shift_seq_def] THEN ASM_MESON_TAC[]];
    (* the code *)
    REPEAT GEN_TAC THEN REWRITE_TAC[flookup_fupdate_list] THEN
      C2BP2AUX_CASES_ON `ALOOKUP (REVERSE (aux:(num#num#clos_exp)list)) name` THEN
      REWRITE_TAC[option_CASE] THENL
       [DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`name:num`; `arity:num`; `c:clos_exp`] o check (fun th ->
          is_forall (concl th) && can (find_term (fun t -> try fst(dest_const t) = "FLOOKUP"
            with Failure _ -> false)) (concl th) &&
          can (find_term ((=) `clos_to_bvlProof_code_installed`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        MAP_EVERY EXISTS_TAC [`aux1:(num#num#bvl_exp)list`; `c2:bvl_exp`;
                              `aux2:(num#num#bvl_exp)list`] THEN
        ASM_SIMP_TAC[code_installed_union1; lookup_union; option_CASE];
        ALL_TAC] THEN
    REWRITE_TAC[option_INJ] THEN DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM o REWRITE_RULE[MATCH_MP alookup_distinct_reverse
        (ASSUME `ALL_DISTINCT (MAP FST (aux:(num#num#clos_exp)list))`)] o check (fun th ->
          is_eq (concl th) && C2BP2AUX_head (lhs (concl th)) = "ALOOKUP")) THEN
      REWRITE_TAC[MEM_EXISTS_EL] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `clos_to_bvl_compile_inc' (clos_state_max_app (s:(C,FFI)clos_state)) (exps,aux) = nw` THEN
      REWRITE_TAC[clos_to_bvl_compile_inc'_def; clos_to_bvl_compile_prog_def] THEN
      MP_TAC (ISPEC `extract_name exps` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `res:clos_exp list` SUBST1_TAC)) THEN
      REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CAKE_REWRITE_TAC[] THEN
      MP_TAC (ISPEC `clos_to_bvl_compile_exps (clos_state_max_app (s:(C,FFI)clos_state))
         (MAP (SND o SND) (APPEND (chain_exps n0 res) (aux:(num#num#clos_exp)list))) []`
         PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `ne:bvl_exp list` (X_CHOOSE_THEN `au:(num#num#bvl_exp)list`
        (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))) THEN
      CAKE_REWRITE_TAC[] THEN DISCH_TAC THEN
    ABBREV_TAC `ce = chain_exps n0 res` THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP clos_to_bvl_compile_exps_LENGTH o check (fun th ->
        is_eq (concl th) && C2BP2AUX_head (lhs (concl th)) = "clos_to_bvl_compile_exps" &&
        rand (rhs (concl th)) = `au:(num#num#bvl_exp)list`)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP; LENGTH_APPEND]) THEN
      MP_TAC (ISPECL [`MAP (SND o SND) (APPEND ce (aux:(num#num#clos_exp)list))`;
        `[]:(num#num#bvl_exp)list`; `ne:bvl_exp list`; `au:(num#num#bvl_exp)list`;
        `LENGTH (ce:(num#num#clos_exp)list) + i`; `clos_state_max_app (s:(C,FFI)clos_state)`]
        compile_exps_EL) THEN
      ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_APPEND; LT_ADD_LCANCEL] THEN
      ASM_SIMP_TAC[EL_MAP; LENGTH_APPEND; LT_ADD_LCANCEL; EL_APPEND; ARITH_RULE `~(a + i < a)`;
                   ADD_SUB2] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
        rhs (concl th) = `EL i (aux:(num#num#clos_exp)list)`)) THEN
      REWRITE_TAC[o_THM; SND] THEN
      DISCH_THEN(X_CHOOSE_THEN `auxn:(num#num#bvl_exp)list` (X_CHOOSE_THEN `aux2n:(num#num#bvl_exp)list`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`auxn:(num#num#bvl_exp)list`;
        `EL (LENGTH (ce:(num#num#clos_exp)list) + i) (ne:bvl_exp list)`;
        `aux2n:(num#num#bvl_exp)list`] THEN
      ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `MEM (name + num_stubs (clos_state_max_app (s:(C,FFI)clos_state)),arity:num,
          EL (LENGTH (ce:(num#num#clos_exp)list) + i) (ne:bvl_exp list))
          (nw:(num#num#bvl_exp)list)` ASSUME_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
          rhs (concl th) = `nw:(num#num#bvl_exp)list`)) THEN
        REWRITE_TAC[MEM_APPEND] THEN DISJ1_TAC THEN
        MATCH_MP_TAC C2BP2AUX_MEM_MAP2_prog THEN EXISTS_TAC `c:clos_exp` THEN
        ASM_REWRITE_TAC[LENGTH_APPEND; LT_ADD_LCANCEL; EL_APPEND; ARITH_RULE `~(a + i < a)`;
                        ADD_SUB2] THEN
        FIRST_ASSUM(ACCEPT_TAC o SYM o check (fun th -> is_eq (concl th) &&
          rhs (concl th) = `EL i (aux:(num#num#clos_exp)list)`));
        ALL_TAC] THEN
      SUBGOAL_THEN `ALL_DISTINCT (MAP FST (nw:(num#num#bvl_exp)list)) /\
                    DISJOINT (domain (bvl_state_code (t:(C,FFI)bvl_state))) (set_of_list (MAP FST nw))`
        STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall (concl th) &&
          can (find_term ((=) `ALL_DISTINCT:num list->bool`)) (concl th) &&
          can (find_term (fun t -> try fst(dest_const t) = "bvl_state_compile_oracle"
                                   with Failure _ -> false)) (concl th))) THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th ->
          can (find_term ((=) `DISJOINT:(num->bool)->(num->bool)->bool`)) (concl th) &&
          can (find_term (fun t -> try fst(dest_const t) = "bvl_state_compile_oracle"
                                   with Failure _ -> false)) (concl th))) THEN
        ASM_REWRITE_TAC[SND] THEN MESON_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `lookup (name + num_stubs (clos_state_max_app (s:(C,FFI)clos_state)))
                        (bvl_state_code (t:(C,FFI)bvl_state)) = NONE` ASSUME_TAC THENL
         [REWRITE_TAC[GSYM not_domain_lookup] THEN
          UNDISCH_TAC `DISJOINT (domain (bvl_state_code (t:(C,FFI)bvl_state)))
                         (set_of_list (MAP FST (nw:(num#num#bvl_exp)list)))` THEN
          REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_SET_OF_LIST; MEM_MAP] THEN
          ASM_MESON_TAC[FST];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[lookup_union; option_CASE; lookup_fromAList] THEN
        MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC code_installed_union THEN CONJ_TAC THENL
         [MATCH_MP_TAC code_installed_fromAList THEN ASM_REWRITE_TAC[] THEN
          FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
            rhs (concl th) = `nw:(num#num#bvl_exp)list`)) THEN
          MATCH_MP_TAC IS_SUBLIST_APPEND2 THEN ASM_REWRITE_TAC[];
          UNDISCH_TAC `DISJOINT (domain (bvl_state_code (t:(C,FFI)bvl_state)))
                         (set_of_list (MAP FST (nw:(num#num#bvl_exp)list)))` THEN
          SUBGOAL_THEN `!x. MEM x (aux2n:(num#num#bvl_exp)list) ==> MEM x nw` MP_TAC THENL
           [REPEAT STRIP_TAC THEN MATCH_MP_TAC IS_SUBLIST_MEM THEN
            EXISTS_TAC `aux2n:(num#num#bvl_exp)list` THEN ASM_REWRITE_TAC[] THEN
            FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
              rhs (concl th) = `nw:(num#num#bvl_exp)list`)) THEN
            MATCH_MP_TAC IS_SUBLIST_APPEND2 THEN ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_SET_OF_LIST; MEM_MAP] THEN
          MESON_TAC[]]]]);;

let C2BP2AUX_find_code_install = prove
 (`!(code:(num#bvl_exp)spt) k d rest.
     DISJOINT (domain code) (set_of_list (MAP FST (CONS (k,0,d) rest))) /\
     ALL_DISTINCT (MAP FST (CONS (k,0,d) rest))
     ==> bvl_find_code NONE [bvl_CodePtr k] (sptree_union code (fromAList (CONS (k,0,d) rest))) =
         SOME ([],d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvl_find_code_def; NOT_CONS_NIL; LAST] THEN
  CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `lookup k (code:(num#bvl_exp)spt) = NONE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM not_domain_lookup] THEN
    UNDISCH_TAC `DISJOINT (domain (code:(num#bvl_exp)spt))
                   (set_of_list (MAP FST (CONS (k,0,d) (rest:(num#num#bvl_exp)list))))` THEN
    REWRITE_TAC[MAP; set_of_list] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[lookup_union; option_CASE; lookup_fromAList; ALOOKUP_THM] THEN
  CAKE_REWRITE_TAC[LENGTH; BUTLAST] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;
let C2BP2AUX_oracle_every_Fn = prove
 (`!f (s:(C,FFI)clos_state) (t:(C,FFI)bvl_state) n cfg e ps.
     clos_to_bvlProof_state_rel f s t /\ clos_state_compile_oracle s n = (cfg,e,ps)
     ==> every_Fn_SOME e /\ every_Fn_vs_SOME e /\
         ALL (\p. every_Fn_SOME [SND (SND p)]) ps /\
         ALL (\p. every_Fn_vs_SOME [SND (SND p)]) ps`,
  REWRITE_TAC[clos_to_bvlProof_state_rel_def; compile_oracle_inv_def] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `cfg:C`; `e:clos_exp list`;
    `ps:(num#num#clos_exp)list`] o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "every_Fn_vs_SOME" with Failure _ -> false))
        (concl th))) THEN
  ASM_SIMP_TAC[]);;
let C2BP2AUX_code_installed_new = prove
 (`!(code:(num#bvl_exp)spt) nw l.
     ALL_DISTINCT (MAP FST nw) /\ DISJOINT (domain code) (set_of_list (MAP FST nw)) /\
     IS_SUBLIST nw l
     ==> clos_to_bvlProof_code_installed l (sptree_union code (fromAList nw))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC code_installed_union THEN CONJ_TAC THENL
   [MATCH_MP_TAC code_installed_fromAList THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `DISJOINT (domain (code:(num#bvl_exp)spt)) (set_of_list (MAP FST (nw:(num#num#bvl_exp)list)))` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_SET_OF_LIST; MEM_MAP] THEN
    ASM_MESON_TAC[IS_SUBLIST_MEM]]);;

(* HOL4: THEN1 (* Op *) *)
let C2BP2AUX_cer_Op = prove
 (C2BP2AUX_cer_goal 7,
  C2BP2AUX_CER_INTRO_TAC THEN
  FS[clos_evaluate_def; clos_to_bvl_compile_exps_def] THEN
  REPEAT PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN
  C2BP2AUX_ASM_CASES_TAC `op = clos_Install` THENL
   [(* Install *)
    FS[] THEN
    (* the IH for the arguments; an error in them is passed on *)
    C2BP2AUX_IH_ON_TAC `xs:clos_exp list` [] THEN ANTS_TAC THENL [C2BP2AUX_SIDE_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
     (X_CHOOSE_THEN `t2:(C,FFI)bvl_state` (X_CHOOSE_THEN `f2:(num,num)fmap`
      STRIP_ASSUME_TAC)))) THEN
    ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
    ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
    CASES_ON `x:(clos_v list,clos_v)result` THEN FS[] THENL
     [ALL_TAC;
      RVEQ_TAC THEN EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`Rerr e':(bvl_v list,bvl_v)result`; `t2:(C,FFI)bvl_state`;
                            `f2:(num,num)fmap`] THEN FS[]] THEN
    (* closSem do_install succeeds: invert it; the BVL arguments are related *)
    MP_TAC (ISPEC `clos_do_install (REVERSE (a:clos_v list)) (s':(C,FFI)clos_state)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r2:(clos_exp list,clos_v)result` (X_CHOOSE_THEN `s3:(C,FFI)clos_state`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th))) THEN
    RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN
    SUBGOAL_THEN `~(r2 = Rerr (Rabort Rtype_error):(clos_exp list,clos_v)result)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(CAKE_REWRITE_RULE[PAIR_EQ]) THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN RVEQ_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th))) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
      MP_TAC (MATCH_MP C2BP2AUX_do_install_inv (CONJ th1 th2)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `v1:clos_v` (X_CHOOSE_THEN `v2:clos_v` (X_CHOOSE_THEN `cfg:C`
      (X_CHOOSE_THEN `exps:clos_exp list` (X_CHOOSE_THEN `aux:(num#num#clos_exp)list`
        (X_CHOOSE_THEN `cfg':C` STRIP_ASSUME_TAC)))))) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP EVERY2_REVERSE o check (fun th ->
      C2BP2AUX_head (concl th) = "ALL2")) THEN
    ASM_REWRITE_TAC[LIST_REL_CONS1; LIST_REL_NIL] THEN
    DISCH_THEN(X_CHOOSE_THEN `w1:bvl_v` (X_CHOOSE_THEN `wt:bvl_v list` (CONJUNCTS_THEN2
      ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w2:bvl_v` (X_CHOOSE_THEN `wt2:bvl_v list`
        STRIP_ASSUME_TAC)))))) THEN RVEQ_TAC THEN
    (* bvl do_install on the related state *)
    IMP_RES_TAC evaluate_const THEN C2BP2AUX_MAX_APP_TAC THEN
    MP_TAC (ISPECL [`f2:(num,num)fmap`; `s':(C,FFI)clos_state`; `t2:(C,FFI)bvl_state`;
      `v1:clos_v`; `v2:clos_v`; `w1:bvl_v`; `w2:bvl_v`; `cfg:C`; `exps:clos_exp list`;
      `aux:(num#num#clos_exp)list`; `FST (clos_state_compile_oracle (s':(C,FFI)clos_state) 1)`]
      C2BP2AUX_bvl_do_install) THEN
    C2BP2AUX_MAX_APP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `d:bvl_exp` (X_CHOOSE_THEN `rest:(num#num#bvl_exp)list`
      STRIP_ASSUME_TAC))) THEN
    (* the installed code is fresh and its names are distinct *)
    FIRST_ASSUM(MP_TAC o MATCH_MP C2BP2AUX_oracle_facts o check (fun th ->
      concl th = `clos_to_bvlProof_state_rel f2 (s':(C,FFI)clos_state) (t2:(C,FFI)bvl_state)`)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `DISJOINT (domain (bvl_state_code (t2:(C,FFI)bvl_state)))
         (set_of_list (MAP FST (CONS (k,0,d) (rest:(num#num#bvl_exp)list)))) /\
       ALL_DISTINCT (MAP FST (CONS (k,0,d) rest))` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `ALL_DISTINCT:num list->bool`)) (concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        can (find_term ((=) `DISJOINT:(num->bool)->(num->bool)->bool`)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "bvl_state_compile_oracle"
                                 with Failure _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[SND] THEN MESON_TAC[];
      ALL_TAC] THEN
    (* the new states are related; first the clock runs out *)
    MP_TAC (ISPECL [`f2:(num,num)fmap`; `s':(C,FFI)clos_state`; `t2:(C,FFI)bvl_state`; `cfg:C`;
      `exps:clos_exp list`; `aux:(num#num#clos_exp)list`] C2BP2AUX_state_rel_install) THEN
    MP_TAC (ISPECL [`f2:(num,num)fmap`; `s':(C,FFI)clos_state`; `t2:(C,FFI)bvl_state`; `0`; `cfg:C`;
      `exps:clos_exp list`; `aux:(num#num#clos_exp)list`] C2BP2AUX_oracle_every_Fn) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `clos_state_clock (s':(C,FFI)clos_state) = 0` THENL
     [(* the clock runs out *)
      SUBGOAL_THEN `bvl_state_clock (t2:(C,FFI)bvl_state) = 0` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
        rhs (concl th) = `res:(clos_v list,clos_v)result,s2:(C,FFI)clos_state`)) THEN
      ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
      RVEQ_TAC THEN EXISTS_TAC `ck:num` THEN
      ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
      REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM] THEN
      MP_TAC (ISPECL [`bvl_state_code (t2:(C,FFI)bvl_state)`; `k:num`; `d:bvl_exp`;
        `rest:(num#num#bvl_exp)list`] C2BP2AUX_find_code_install) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM] THEN
      FS[] THEN EXISTS_TAC `f2:(num,num)fmap` THEN
        REWRITE_TAC[clos_state_INFO.ri_accfupds; bvl_state_INFO.ri_accfupds; K_THM] THEN
        ASM_REWRITE_TAC[clos_state_INFO.ri_fupdcanon; bvl_state_INFO.ri_fupdcanon;
                        clos_to_bvlProof_state_rel_clock] THEN
        CONJ_TAC THEN MATCH_MP_TAC FEVERY_FUPDATE_LIST_SUFF THEN ASM_REWRITE_TAC[];
      (* the code is run *)
      ALL_TAC] THEN
    (* the clock does not run out: the installed expressions are run *)
    ABBREV_TAC `sI = clos_state_code_fupd (combin_K (clos_state_code s' |++ aux))
       (clos_state_compile_oracle_fupd (combin_K (shift_seq 1 (clos_state_compile_oracle s')))
          (clos_state_clock_fupd (combin_K (clos_state_clock s' - 1)) (s':(C,FFI)clos_state)))` THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `res:(clos_v list,clos_v)result,s2:(C,FFI)clos_state`)) THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    MP_TAC (ISPEC `clos_evaluate (exps,[],(sI:(C,FFI)clos_state))` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r4:(clos_v list,clos_v)result` (X_CHOOSE_THEN `s4:(C,FFI)clos_state`
      (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))) THEN
    CAKE_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC (ISPEC `clos_to_bvl_compile_exps (clos_state_max_app (s1:(C,FFI)clos_state)) exps []`
      PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `x6:bvl_exp list` (X_CHOOSE_THEN `x7:(num#num#bvl_exp)list`
      ASSUME_TAC)) THEN
    (* the IH for the installed expressions *)
    FIRST_X_ASSUM(MP_TAC o SPECL [`exps:clos_exp list`; `sI:(C,FFI)clos_state`] o
      check (C2BP2AUX_is_ih o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C2BP2AUX_IH_TAC [(`[]:(num#num#bvl_exp)list`,"aux1");
      (`bvl_state_code_fupd (combin_K (sptree_union (bvl_state_code t2) (fromAList (CONS (k,0,d) rest))))
         (bvl_state_compile_oracle_fupd (combin_K (shift_seq 1 (bvl_state_compile_oracle t2)))
            (t2:(C,FFI)bvl_state))`,"t1");
      (`[]:bvl_v list`,"env'"); (`f2:(num,num)fmap`,"f1");
      (`r4:(clos_v list,clos_v)result`,"res"); (`s4:(C,FFI)clos_state`,"s2");
      (`x6:bvl_exp list`,"ys"); (`x7:(num#num#bvl_exp)list`,"aux2")] THEN
    (* the shape of the installed BVL code (compile_inc) *)
    MP_TAC (ISPEC `extract_name exps` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `res0:clos_exp list` ASSUME_TAC)) THEN
    MP_TAC (ISPEC `clos_to_bvl_compile_exps (clos_state_max_app (s1:(C,FFI)clos_state))
       (MAP (SND o SND) (APPEND (chain_exps n0 res0) (aux:(num#num#clos_exp)list))) []`
       PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `ne:bvl_exp list` (X_CHOOSE_THEN `au:(num#num#bvl_exp)list`
      ASSUME_TAC)) THEN
    ABBREV_TAC (CASE_TERM `pr = MAP2 (\p (exp:bvl_exp). match p with (loc,args,_) ->
                       (loc + num_stubs (clos_state_max_app (s1:(C,FFI)clos_state)),args,exp))
                     (APPEND (chain_exps n0 res0) (aux:(num#num#clos_exp)list)) ne`) THEN
    SUBGOAL_THEN `APPEND pr au = CONS (k,0,d) (rest:(num#num#bvl_exp)list)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
        rhs (concl th) = `CONS (k,0,d) (rest:(num#num#bvl_exp)list)` &&
        C2BP2AUX_head (lhs (concl th)) = "clos_to_bvl_compile_inc'")) THEN
      ASM_REWRITE_TAC[clos_to_bvl_compile_inc'_def; clos_to_bvl_compile_prog_def; LET_DEF;
                      LET_END_DEF] THEN
      CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    (* the code of the installed expressions is in the new code *)
    SUBGOAL_THEN `IS_SUBLIST (au:(num#num#bvl_exp)list) (x7:(num#num#bvl_exp)list)` ASSUME_TAC THENL
     [MATCH_MP_TAC compile_exps_twice_IS_SUBLIST THEN
      MAP_EVERY EXISTS_TAC [`exps:clos_exp list`; `n0:num`; `res0:clos_exp list`;
        `clos_state_max_app (s1:(C,FFI)clos_state)`; `MAP (SND o SND) (aux:(num#num#clos_exp)list)`;
        `ne:bvl_exp list`; `x6:bvl_exp list`] THEN
      ASM_REWRITE_TAC[GSYM MAP_APPEND];
      ALL_TAC] THEN
    SUBGOAL_THEN `clos_to_bvlProof_code_installed x7
         (sptree_union (bvl_state_code (t2:(C,FFI)bvl_state)) (fromAList (CONS (k,0,d) rest))) /\
       clos_to_bvlProof_code_installed pr
         (sptree_union (bvl_state_code (t2:(C,FFI)bvl_state)) (fromAList (CONS (k,0,d) rest)))`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC C2BP2AUX_code_installed_new THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
        lhs (concl th) = `APPEND pr (au:(num#num#bvl_exp)list)`)) THENL
       [MATCH_MP_TAC IS_SUBLIST_APPEND2 THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC IS_SUBLIST_APPEND1 THEN REWRITE_TAC[IS_SUBLIST_REFL]];
      ALL_TAC] THEN
    (* the antecedents of the IH *)
    ANTS_TAC THENL
     [REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM; clos_to_bvlProof_env_rel_def] THEN
      ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "sI" THEN
      REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM; clos_state_INFO.ri_fupdcanon;
                  clos_to_bvlProof_state_rel_clock] THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
          rhs (concl th) = `res:(clos_v list,clos_v)result,s2:(C,FFI)clos_state`)) THEN
        CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `~(res = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)`)) THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC FEVERY_FUPDATE_LIST_SUFF THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC FEVERY_FUPDATE_LIST_SUFF THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[clos_state_INFO.ri_fupdcanon] o check (fun th ->
          C2BP2AUX_head (concl th) = "clos_to_bvlProof_state_rel" &&
          can (find_term ((=) `fromAList:(num#num#bvl_exp)list->(num#bvl_exp)spt`)) (concl th)))];
      ALL_TAC] THEN
    (* max_app and clock of the new closSem state *)
    DISCH_THEN(X_CHOOSE_THEN `ck':num` (X_CHOOSE_THEN `res3:(bvl_v list,bvl_v)result`
      (X_CHOOSE_THEN `t4:(C,FFI)bvl_state` (X_CHOOSE_THEN `f3:(num,num)fmap` STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `clos_state_max_app (sI:(C,FFI)clos_state) = clos_state_max_app (s1:(C,FFI)clos_state)`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
     [EXPAND_TAC "sI" THEN REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `clos_state_clock (sI:(C,FFI)clos_state) = clos_state_clock (s':(C,FFI)clos_state) - 1`
      ASSUME_TAC THENL
     [EXPAND_TAC "sI" THEN REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
    (* the chained code of the installed expressions (evaluate_IMP_evaluate_chained) *)
    MP_TAC (ISPECL [`x6:bvl_exp list`;
      `bvl_state_clock_fupd (combin_K (clos_state_clock (sI:(C,FFI)clos_state) + ck'))
        (bvl_state_code_fupd (combin_K (sptree_union (bvl_state_code t2) (fromAList (CONS (k,0,d) rest))))
          (bvl_state_compile_oracle_fupd (combin_K (shift_seq 1 (bvl_state_compile_oracle t2)))
            (t2:(C,FFI)bvl_state)))`;
      `res3:(bvl_v list,bvl_v)result`; `t4:(C,FFI)bvl_state`; `pr:(num#num#bvl_exp)list`;
      `au:(num#num#bvl_exp)list`; `k:num`; `d:bvl_exp`; `rest:(num#num#bvl_exp)list`;
      `clos_state_max_app (s1:(C,FFI)clos_state)`; `n0:num`; `res0:clos_exp list`;
      `aux:(num#num#clos_exp)list`; `ne:bvl_exp list`; `exps:clos_exp list`;
      `x7:(num#num#bvl_exp)list`] evaluate_IMP_evaluate_chained) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM; GSYM MAP_APPEND] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP clos_to_bvl_compile_exps_LENGTH o check (fun th ->
        concl th = `clos_to_bvl_compile_exps (clos_state_max_app (s1:(C,FFI)clos_state)) exps [] = x6,x7`)) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM LENGTH_EQ_NIL; th]) THEN
      ASM_REWRITE_TAC[LENGTH_EQ_NIL];
      DISCH_THEN(X_CHOOSE_THEN `ck8:num` (X_CHOOSE_THEN `res8:(bvl_v list,bvl_v)result`
        STRIP_ASSUME_TAC))] THEN
    (* the BVL side: add the clock, then do_install *)
    SUBGOAL_THEN `~(bvl_state_clock (t2:(C,FFI)bvl_state) = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `ck + ck' + ck8:num` THEN
    FIRST_ASSUM(MP_TAC o SPEC `ck' + ck8:num` o MATCH_MP C2BP2AUX_bvl_evaluate_add_clock_Rval o
      check (fun th -> concl th = `bvl_evaluate (c1,env'',bvl_state_clock_fupd
        (combin_K (clos_state_clock (s1:(C,FFI)clos_state) + ck)) (t1:(C,FFI)bvl_state)) = Rval v',t2`)) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
    MP_TAC (ISPECL [`f2:(num,num)fmap`; `s':(C,FFI)clos_state`;
      `bvl_state_clock_fupd (combin_K (bvl_state_clock t2 + ck' + ck8)) (t2:(C,FFI)bvl_state)`;
      `v1:clos_v`; `v2:clos_v`; `w1:bvl_v`; `w2:bvl_v`; `cfg:C`; `exps:clos_exp list`;
      `aux:(num#num#clos_exp)list`; `FST (clos_state_compile_oracle (s':(C,FFI)clos_state) 1)`;
      `k:num`; `d:bvl_exp`; `rest:(num#num#bvl_exp)list`] C2BP2AUX_bvl_do_install_k) THEN
    ASM_REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM; clos_to_bvlProof_state_rel_clock] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[] THEN
    (* find_code of the new code pointer, then the call *)
    REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM] THEN
    MP_TAC (ISPECL [`bvl_state_code (t2:(C,FFI)bvl_state)`; `k:num`; `d:bvl_exp`;
        `rest:(num#num#bvl_exp)list`] C2BP2AUX_find_code_install) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[ADD_EQ_0; bvl_dec_clock_def; bvl_state_INFO.ri_accfupds; K_THM] THEN
    SUBGOAL_THEN `(bvl_state_clock (t2:(C,FFI)bvl_state) + ck' + ck8) - 1 =
                  (clos_state_clock (sI:(C,FFI)clos_state) + ck') + ck8` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(bvl_state_clock (t2:(C,FFI)bvl_state) = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      can (find_term ((=) `[d:bvl_exp]`)) (lhs (concl th)))) THEN
    REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM; bvl_state_INFO.ri_fupdcanon;
                bvl_state_INFO.ri_fupdfupds; K_o_THM] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; bvl_state_INFO.ri_fupdcanon;
                bvl_state_INFO.ri_fupdfupds; K_o_THM]) THEN
    (* the results are related *)
    MAP_EVERY EXISTS_TAC [`res8:(bvl_v list,bvl_v)result`; `t4:(C,FFI)bvl_state`;
                          `f3:(num,num)fmap`] THEN
    REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[bvl_state_INFO.ri_accfupds; K_THM]) THEN
    SUBGOAL_THEN `f1 SUBMAP (f3:(num,num)fmap) /\
       FDIFF (bvl_state_refs (t1:(C,FFI)bvl_state)) (FRANGE f1) SUBMAP
       FDIFF (bvl_state_refs (t4:(C,FFI)bvl_state)) (FRANGE f3)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[SUBMAP_TRANS]; ALL_TAC] THEN
    CASES_ON `r4:(clos_v list,clos_v)result` THEN
    RULE_ASSUM_TAC(CAKE_REWRITE_RULE[PAIR_EQ]) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th -> is_conj (concl th) &&
       can (find_term ((=) `s2:(C,FFI)clos_state`)) (concl th))) THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CASES_ON `res3:(bvl_v list,bvl_v)result` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[result_rel_def; distinctness "result"; injectivity "result"]) THEN
    TRY(FIRST_ASSUM CONTR_TAC) THEN RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[result_rel_def; ALL2] THEN
    (* LAST of related value lists *)
    MATCH_MP_TAC LIST_REL_IMP_LAST THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP clos_evaluate_IMP_LENGTH o check (fun th ->
      is_eq (concl th) && C2BP2AUX_head (lhs (concl th)) = "clos_evaluate" &&
      can (find_term ((=) `exps:clos_exp list`)) (concl th))) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM LENGTH_EQ_NIL; GSYM th]) THEN
    ASM_REWRITE_TAC[LENGTH_EQ_NIL];
    ALL_TAC] THEN
  C2BP2AUX_ASM_CASES_TAC `op = clos_ThunkOp ForceThunk` THENL
   [(* ForceThunk *)
    FS[] THEN
      C2BP2AUX_IH_ON_TAC `xs:clos_exp list` [] THEN ANTS_TAC THENL [C2BP2AUX_SIDE_TAC; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
         (X_CHOOSE_THEN `t2:(C,FFI)bvl_state` (X_CHOOSE_THEN `f2:(num,num)fmap`
          STRIP_ASSUME_TAC)))) THEN
        ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
        CASES_ON `x:(clos_v list,clos_v)result` THEN FS[] THENL
         [ALL_TAC;
          RVEQ_TAC THEN EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
          MAP_EVERY EXISTS_TAC [`Rerr e':(bvl_v list,bvl_v)result`; `t2:(C,FFI)bvl_state`;
                                `f2:(num,num)fmap`] THEN FS[]] THEN
      C2BP2AUX_CASES_ON `clos_dest_thunk a (clos_state_refs (s':(C,FFI)clos_state))` THEN FS[] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP C2BP2AUX_dest_thunk_IsThunk) THEN
        DISCH_THEN(X_CHOOSE_THEN `ptr:num` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
        REPEAT(FIRST_X_ASSUM(fun th -> if is_exists(concl th) then CAKE_STRIP_ASSUME_TAC th
                                       else NO_TAC)) THEN RVEQ_TAC THEN
        IMP_RES_TAC evaluate_const THEN C2BP2AUX_MAX_APP_TAC THEN
        MP_TAC (ISPECL [`f2:(num,num)fmap`; `s':(C,FFI)clos_state`; `t2:(C,FFI)bvl_state`;
          `clos_RefPtr F ptr`; `h':bvl_v`; `a0:thunk_mode`; `a1:clos_v`] rel_dest_thunk) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `r2:bvl_v` STRIP_ASSUME_TAC) THEN
        CASES_ON `a0:thunk_mode` THEN FS[] THENL
       [(* the thunk is evaluated *)
        RVEQ_TAC THEN EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[APPEND] THEN
          REWRITE_TAC[bvl_evaluate_def; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
          REWRITE_TAC[LENGTH; LT_0; EL; HD] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
          MAP_EVERY EXISTS_TAC [`Rval [r2]:(bvl_v list,bvl_v)result`; `t2:(C,FFI)bvl_state`;
                                `f2:(num,num)fmap`] THEN FS[];
        (* the thunk is not evaluated: the closure is applied to unit *)
        MP_TAC (ISPEC `clos_evaluate ([clos_AppUnit (clos_Var backend_common_None 0)],[a1],
                           (s':(C,FFI)clos_state))` PAIR_SURJECTIVE) THEN
          DISCH_THEN(X_CHOOSE_THEN `r3:(clos_v list,clos_v)result` (X_CHOOSE_THEN `s3:(C,FFI)clos_state`
            (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th))) THEN
          FIRST_X_ASSUM(MP_TAC o SPECL [`[]:(num#num#bvl_exp)list`; `t2:(C,FFI)bvl_state`;
            `[r2:bvl_v]`; `f2:(num,num)fmap`; `r3:(clos_v list,clos_v)result`; `s3:(C,FFI)clos_state`;
            `[bvl_Let [bvl_Op (BlockOp (clos_Cons 0)) []; bvl_Var 0] (mk_cl_call (bvl_Var 1) [bvl_Var 0])]`;
            `[]:(num#num#bvl_exp)list`] o check (C2BP2AUX_is_ih o concl)) THEN
          ASM_REWRITE_TAC[C2BP2AUX_compile_AppUnit] THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
             [DISCH_THEN SUBST_ALL_TAC THEN FS[];
              REWRITE_TAC[clos_AppUnit_def] THEN FS[];
              REWRITE_TAC[clos_AppUnit_def] THEN FS[];
              REWRITE_TAC[clos_to_bvlProof_code_installed_def; ALL];
              ASM_REWRITE_TAC[clos_to_bvlProof_env_rel_def]];
          ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `ck2:num` (X_CHOOSE_THEN `res2:(bvl_v list,bvl_v)result`
            (X_CHOOSE_THEN `t3:(C,FFI)bvl_state` (X_CHOOSE_THEN `f3:(num,num)fmap`
              STRIP_ASSUME_TAC)))) THEN
          EXISTS_TAC `ck + ck2 + 1` THEN
          FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP C2BP2AUX_bvl_evaluate_add_clock_Rval th]) THEN
          CAKE_REWRITE_TAC[APPEND] THEN
          REWRITE_TAC[bvl_evaluate_def; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
          REWRITE_TAC[LENGTH; LT_0; EL; HD; bvl_state_INFO.ri_accfupds; K_THM] THEN
          ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
        FIRST_ASSUM(fun th ->
            if C2BP2AUX_head (concl th) = "clos_to_bvlProof_state_rel" &&
               rand(concl th) = `t2:(C,FFI)bvl_state`
            then ASSUME_TAC (find (fun c -> can (find_term ((=) `force_thunk_code`)) (concl c))
                                  (CONJUNCTS (REWRITE_RULE[clos_to_bvlProof_state_rel_def] th)))
            else NO_TAC) THEN
          C2BP2AUX_MAX_APP_TAC THEN
          REWRITE_TAC[bvl_find_code_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[LENGTH] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          REWRITE_TAC[ARITH_RULE `~(a + b + 1 = 0)`; bvl_dec_clock_def; bvl_state_INFO.ri_accfupds;
                      bvl_state_INFO.ri_fupdfupds; K_THM; K_o_THM; ARITH_RULE `(a + b + 1) - 1 = a + b`] THEN
          REWRITE_TAC[C2BP2AUX_eval_force_thunk_code] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
        REWRITE_TAC[C2BP2AUX_eval_force_thunk_code] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
          CASES_ON `r3:(clos_v list,clos_v)result` THEN
          RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THENL
         [(* the application returns: the thunk is updated *)
          C2BP2AUX_CASES_ON `clos_update_thunk [clos_RefPtr F ptr] (clos_state_refs (s3:(C,FFI)clos_state)) a'` THEN
            RULE_ASSUM_TAC(CAKE_REWRITE_RULE[PAIR_EQ]) THEN
            TRY(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
                RVEQ_TAC THEN FIRST_ASSUM(fun th -> CONTR_TAC (REWRITE_RULE[] th)) THEN NO_TAC) THEN
            FIRST_ASSUM(MP_TAC o MATCH_MP C2BP2AUX_update_thunk_SOME o check (fun th ->
              try C2BP2AUX_head (lhs (concl th)) = "clos_update_thunk" with Failure _ -> false)) THEN
            REWRITE_TAC[] THEN
            DISCH_THEN(X_CHOOSE_THEN `v:clos_v` (X_CHOOSE_THEN `x0:clos_v` STRIP_ASSUME_TAC)) THEN
            RVEQ_TAC THEN
          FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN RVEQ_TAC THEN
            CASES_ON `res2:(bvl_v list,bvl_v)result` THEN
            RULE_ASSUM_TAC(REWRITE_RULE[result_rel_def; distinctness "result"; injectivity "result"]) THEN
            TRY(FIRST_ASSUM CONTR_TAC) THEN
            RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
            FIRST_X_ASSUM(X_CHOOSE_THEN `w:bvl_v` (X_CHOOSE_THEN `tl:bvl_v list` STRIP_ASSUME_TAC) o
              check (is_exists o concl)) THEN RVEQ_TAC THEN
            REWRITE_TAC[HD] THEN
            FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[C2BP2AUX_v_rel_inv] o check (fun th ->
              can (find_term ((=) `clos_RefPtr F ptr`)) (concl th) &&
              C2BP2AUX_head (concl th) = "clos_to_bvlProof_v_rel")) THEN
            DISCH_THEN(X_CHOOSE_THEN `rp:num` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
          CAKE_REWRITE_TAC[HD] THEN
            IMP_RES_TAC evaluate_const THEN C2BP2AUX_MAX_APP_TAC THEN
            SUBGOAL_THEN `FLOOKUP (f3:(num,num)fmap) ptr = SOME rp` ASSUME_TAC THENL
             [ASM_MESON_TAC[FLOOKUP_SUBMAP]; ALL_TAC] THEN
            MP_TAC (ISPECL [`f3:(num,num)fmap`; `s3:(C,FFI)clos_state`; `t3:(C,FFI)bvl_state`; `ptr:num`;
              `clos_Thunk NotEvaluated (x0:clos_v)`; `rp:num`] state_rel_refs_lookup) THEN
            ASM_REWRITE_TAC[C2BP2AUX_ref_rel_inv] THEN
            DISCH_THEN(X_CHOOSE_THEN `z:bvl_v bvl_ref` (CONJUNCTS_THEN2 ASSUME_TAC
              (X_CHOOSE_THEN `w0:bvl_v` STRIP_ASSUME_TAC))) THEN RVEQ_TAC THEN
            MP_TAC (ISPECL [`f3:(num,num)fmap`; `s3:(C,FFI)clos_state`; `t3:(C,FFI)bvl_state`;
              `Evaluated`; `v:clos_v`; `w:bvl_v`] C2BP2AUX_bad_thunk_update) THEN
            ASM_REWRITE_TAC[clos_bad_thunk_update_def] THEN DISCH_TAC THEN
            REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
            CAKE_REWRITE_TAC[] THEN
          FS[] THEN EXISTS_TAC `f3:(num,num)fmap` THEN
            SUBGOAL_THEN `(rp:num) IN FRANGE (f3:(num,num)fmap)` ASSUME_TAC THENL
             [ASM_MESON_TAC[FRANGE_FLOOKUP]; ALL_TAC] THEN
            REWRITE_TAC[clos_state_INFO.ri_accfupds; bvl_state_INFO.ri_accfupds; K_THM] THEN
            ASM_SIMP_TAC[v_rel_UPDATE_REF; FDIFF_FUPDATE] THEN
            REPEAT CONJ_TAC THENL
             [MATCH_MP_TAC state_rel_UPDATE_REF THEN
              EXISTS_TAC `clos_Thunk NotEvaluated (x0:clos_v)` THEN
              ASM_REWRITE_TAC[clos_to_bvlProof_ref_rel_def; distinctness "bvl_ref"];
              ASM_MESON_TAC[SUBMAP_TRANS];
              ASM_MESON_TAC[SUBMAP_TRANS]];
          (* the application raises or aborts *)
          FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN RVEQ_TAC THEN
            CASES_ON `res2:(bvl_v list,bvl_v)result` THEN
            RULE_ASSUM_TAC(REWRITE_RULE[result_rel_def; distinctness "result"; injectivity "result"]) THEN
            TRY(FIRST_ASSUM CONTR_TAC) THEN CAKE_REWRITE_TAC[] THEN
            MAP_EVERY EXISTS_TAC [`Rerr a'':(bvl_v list,bvl_v)result`; `t3:(C,FFI)bvl_state`;
                                  `f3:(num,num)fmap`] THEN
            ASM_REWRITE_TAC[result_rel_def] THEN ASM_MESON_TAC[SUBMAP_TRANS]]];
    ALL_TAC] THEN
  FS[] THEN
  C2BP2AUX_IH_ON_TAC `xs:clos_exp list` [] THEN ANTS_TAC THENL [C2BP2AUX_SIDE_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
   (X_CHOOSE_THEN `t2:(C,FFI)bvl_state` (X_CHOOSE_THEN `f2:(num,num)fmap`
    STRIP_ASSUME_TAC)))) THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  CASES_ON `x:(clos_v list,clos_v)result` THEN FS[] THENL
   [EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    C2BP2AUX_CASES_ON `clos_do_app op (REVERSE a) (s':(C,FFI)clos_state)` THEN FS[] THENL
     [(* the operation succeeds *)
      C2BP2AUX_PAIR_CASES_TAC `a':clos_v#(C,FFI)clos_state` `v:clos_v` `s3:(C,FFI)clos_state` THEN
      FS[] THEN RVEQ_TAC THEN
      IMP_RES_TAC evaluate_const THEN C2BP2AUX_MAX_APP_TAC THEN
      MP_TAC (ISPECL [`op:clos_op`; `REVERSE (a:clos_v list)`; `s':(C,FFI)clos_state`;
        `v:clos_v`; `s2:(C,FFI)clos_state`; `f2:(num,num)fmap`; `t2:(C,FFI)bvl_state`;
        `REVERSE (v':bvl_v list)`] C2BP2AUX_do_app_Rval) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EVERY2_REVERSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:bvl_v` (X_CHOOSE_THEN `t3:(C,FFI)bvl_state`
        (X_CHOOSE_THEN `f3:(num,num)fmap` STRIP_ASSUME_TAC))) THEN
      ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`Rval [w]:(bvl_v list,bvl_v)result`; `t3:(C,FFI)bvl_state`;
                            `f3:(num,num)fmap`] THEN
      IMP_RES_TAC clos_do_app_const THEN IMP_RES_TAC bvl_do_app_const THEN FS[] THEN
      C2BP2AUX_MAX_APP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBMAP_TRANS];
      (* the operation fails *)
      RVEQ_TAC THEN IMP_RES_TAC evaluate_const THEN C2BP2AUX_MAX_APP_TAC THEN
      MP_TAC (ISPECL [`op:clos_op`; `REVERSE (a:clos_v list)`; `s2:(C,FFI)clos_state`;
        `a':(clos_v)error_result`; `f2:(num,num)fmap`; `t2:(C,FFI)bvl_state`;
        `REVERSE (v':bvl_v list)`] clos_to_bvlProof_do_app_err) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [DISCH_THEN SUBST_ALL_TAC THEN FS[];
          MATCH_MP_TAC EVERY2_REVERSE THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:(bvl_v)error_result` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`Rerr e:(bvl_v list,bvl_v)result`; `t2:(C,FFI)bvl_state`;
                            `f2:(num,num)fmap`] THEN
      FS[]];
    (* the arguments raise or abort *)
    RVEQ_TAC THEN EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`Rerr e':(bvl_v list,bvl_v)result`; `t2:(C,FFI)bvl_state`;
                          `f2:(num,num)fmap`] THEN FS[]]);;

(* HOL4 line 3433 (closSem's evaluate and evaluate_app on the left,          *)
(* bvlSem's evaluate and find_code on the right; HOL4 f1 SUBMAP f2 is the    *)
(* finite map order, FDIFF is FDIFF)                                         *)
let clos_to_bvlProof_compile_exps_correct = prove
 (CASE_TERM
  `(!tmp xs env (s1:(C,FFI)clos_state) aux1 (t1:(C,FFI)bvl_state) env' f1 res s2 ys aux2.
      tmp = (xs,env,s1) /\
      clos_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) /\
      clos_to_bvl_compile_exps (clos_state_max_app s1) xs aux1 = (ys,aux2) /\
      every_Fn_SOME xs /\ FEVERY (\p. every_Fn_SOME [SND (SND p)]) (clos_state_code s1) /\
      every_Fn_vs_SOME xs /\ FEVERY (\p. every_Fn_vs_SOME [SND (SND p)]) (clos_state_code s1) /\
      clos_to_bvlProof_code_installed aux2 (bvl_state_code t1) /\
      clos_to_bvlProof_env_rel (clos_state_max_app s1) f1 (bvl_state_refs t1)
        (bvl_state_code t1) env env' /\
      clos_to_bvlProof_state_rel f1 s1 t1
      ==> ?ck res' t2 f2.
            bvl_evaluate (ys,env',bvl_state_clock_fupd (combin_K (clos_state_clock s1 + ck)) t1) =
              (res',t2) /\
            result_rel (ALL2 (clos_to_bvlProof_v_rel (clos_state_max_app s1) f2
                                (bvl_state_refs t2) (bvl_state_code t2)))
              (clos_to_bvlProof_v_rel (clos_state_max_app s1) f2 (bvl_state_refs t2)
                 (bvl_state_code t2)) res res' /\
            clos_to_bvlProof_state_rel f2 s2 t2 /\
            f1 SUBMAP f2 /\
            FDIFF (bvl_state_refs t1) (FRANGE f1) SUBMAP FDIFF (bvl_state_refs t2) (FRANGE f2) /\
            FEVERY (\p. every_Fn_SOME [SND (SND p)]) (clos_state_code s2) /\
            FEVERY (\p. every_Fn_vs_SOME [SND (SND p)]) (clos_state_code s2) /\
            clos_state_clock s2 = bvl_state_clock t2) /\
   (!loc_opt func args (s1:(C,FFI)clos_state) res s2 env (t1:(C,FFI)bvl_state) args' func'
      f1.
      evaluate_app loc_opt func args s1 = (res,s2) /\
      ~(res = Rerr (Rabort Rtype_error)) /\
      FEVERY (\p. every_Fn_SOME [SND (SND p)]) (clos_state_code s1) /\
      FEVERY (\p. every_Fn_vs_SOME [SND (SND p)]) (clos_state_code s1) /\
      clos_to_bvlProof_v_rel (clos_state_max_app s1) f1 (bvl_state_refs t1)
        (bvl_state_code t1) func func' /\
      ALL2 (clos_to_bvlProof_v_rel (clos_state_max_app s1) f1 (bvl_state_refs t1)
              (bvl_state_code t1)) args args' /\
      clos_to_bvlProof_state_rel f1 s1 t1
      ==> ?ck res' t2 f2.
            (~(LENGTH args' = 0)
             ==> (match loc_opt with
                    NONE ->
                      bvl_evaluate
                        ([mk_cl_call (bvl_Var (LENGTH args'))
                            (list_of_seq bvl_Var (LENGTH args'))],
                         APPEND (APPEND args' [func']) env,
                         bvl_state_clock_fupd (combin_K (clos_state_clock s1 + ck)) t1) =
                      (res',t2)
                  | SOME loc ->
                      (match bvl_find_code (SOME (loc + num_stubs (clos_state_max_app s1)))
                               (APPEND args' [func']) (bvl_state_code t1) with
                         NONE -> (Rerr (Rabort Rtype_error),t2)
                       | SOME (args,exp) ->
                           if clos_state_clock s1 + ck < LENGTH args'
                           then (Rerr (Rabort Rtimeout_error),bvl_state_clock_fupd (combin_K 0) t1)
                           else bvl_evaluate
                                  ([exp],args,
                                   bvl_state_clock_fupd
                                     (combin_K ((clos_state_clock s1 + ck) - LENGTH args')) t1)) =
                      (res',t2))) /\
            result_rel (ALL2 (clos_to_bvlProof_v_rel (clos_state_max_app s1) f2
                                (bvl_state_refs t2) (bvl_state_code t2)))
              (clos_to_bvlProof_v_rel (clos_state_max_app s1) f2 (bvl_state_refs t2)
                 (bvl_state_code t2)) res res' /\
            clos_to_bvlProof_state_rel f2 s2 t2 /\
            f1 SUBMAP f2 /\
            FDIFF (bvl_state_refs t1) (FRANGE f1) SUBMAP FDIFF (bvl_state_refs t2) (FRANGE f2) /\
            FEVERY (\p. every_Fn_SOME [SND (SND p)]) (clos_state_code s2) /\
            FEVERY (\p. every_Fn_vs_SOME [SND (SND p)]) (clos_state_code s2) /\
            clos_state_clock s2 = bvl_state_clock t2)`,
  MATCH_MP_TAC clos_evaluate_ind THEN REPEAT CONJ_TAC THEN
  MAP_FIRST ACCEPT_TAC
    [C2BP2AUX_cer_NIL; C2BP2AUX_cer_CONS; C2BP2AUX_cer_Var; C2BP2AUX_cer_If; C2BP2AUX_cer_Let;
     C2BP2AUX_cer_Raise; C2BP2AUX_cer_Handle; C2BP2AUX_cer_Op; C2BP2AUX_cer_Fn;
     C2BP2AUX_cer_Letrec; C2BP2AUX_cer_App; C2BP2AUX_cer_Tick; C2BP2AUX_cer_Call;
     C2BP2AUX_cer_app_NIL; C2BP2AUX_cer_app_CONS]);;

(* HOL4 line 5667 (HOL4 composes $+ n with the doubling function) *)
let build_aux_thm = prove
 (`!c n aux n7 aux7.
     build_aux n c aux = (n7,APPEND aux7 aux)
     ==> MAP FST aux7 = REVERSE (list_of_seq ((\x. n + x) o (\x. 2 * x)) (LENGTH c))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[build_aux_def; PAIR_EQ; LENGTH; list_of_seq; REVERSE] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM `LENGTH:(num#num#bvl_exp)list->num` o CONJUNCT2) THEN
    REWRITE_TAC[LENGTH_APPEND; ARITH_RULE `a = b + a <=> b = 0`; LENGTH_EQ_NIL] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MAP];
    REPEAT GEN_TAC THEN REWRITE_TAC[build_aux_def] THEN
    ONCE_REWRITE_TAC[build_aux_MOVE] THEN
    DISCH_THEN(X_CHOOSE_THEN `aux2:(num#num#bvl_exp)list` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n + 2`; `[]:(num#num#bvl_exp)list`; `n7:num`;
                                  `aux2:(num#num#bvl_exp)list`]) THEN
    ASM_REWRITE_TAC[APPEND_NIL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `aux7 = APPEND aux2 [n:num,h:num#bvl_exp]` SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[GSYM (ISPECL [`aux7:(num#num#bvl_exp)list`;
                                      `APPEND aux2 [n:num,h:num#bvl_exp]`;
                                      `aux:(num#num#bvl_exp)list`] APPEND_RCANCEL)] THEN
      ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[MAP_APPEND; MAP; LENGTH; LIST_OF_SEQ; REVERSE] THEN
    REWRITE_TAC[o_THM; MULT_CLAUSES; ADD_CLAUSES; APPEND_RCANCEL] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ARITH_TAC]);;

(* HOL4 line 5682 *)
let MEM_build_aux_imp_SND_MEM = prove
 (`!n ls acc m aux x.
     build_aux n ls acc = (m,aux) /\ MEM x aux ==> MEM (SND x) ls \/ MEM x acc`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN REWRITE_TAC[build_aux_def; PAIR_EQ; MEM] THENL
   [MESON_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n + 2`; `CONS (n:num,h:num#bvl_exp) acc`; `m:num`;
                                  `aux:(num#num#bvl_exp)list`; `x:num#num#bvl_exp`]) THEN
    ASM_REWRITE_TAC[MEM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[SND]]);;

(* HOL4 line 5693 *)
let clos_to_bvlProof_lemma = prove
 (`!max_app xs aux c aux1.
     clos_to_bvl_compile_exps max_app xs aux = (c,aux1)
     ==> LENGTH c = LENGTH xs /\ ?ys. aux1 = APPEND ys aux`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`max_app:num`; `xs:clos_exp list`; `aux:(num#num#bvl_exp)list`]
               compile_exps_acc) THEN
  ASM_REWRITE_TAC[pair_CASE]);;

(* HOL4 line 5701 *)
let lemma2 = prove
 (`!n k aux a b. build_aux n k aux = (a,b) ==> ?z. b = APPEND z aux`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[build_aux_MOVE] THEN MESON_TAC[]);;

(* helpers for compile_exps_code_locs *)

let C2BP2AUX_MAP_REVERSE_GENLIST = prove
 (`!ns k l. MAP ((+) ns) (REVERSE (list_of_seq (\n. l + 2 * n) k)) =
            REVERSE (list_of_seq ((\x. (l + ns) + x) o (\x. 2 * x)) k)`,
  REWRITE_TAC[GSYM MAP_REVERSE; MAP_LIST_OF_SEQ] THEN REPEAT GEN_TAC THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ARITH_TAC);;

(* the witness of a goal ?a. X = APPEND a aux /\ ..., X a chain of APPEND and *)
(* CONS ending in aux                                                         *)
let C2BP2AUX_APPEND_WITNESS_TAC : tactic = fun (asl,w as g) ->
  let a,body = dest_exists w in
  let eq = fst(dest_conj body) in
  let x,r = dest_eq eq in
  let aux = rand r in
  let ety = hd(snd(dest_type(type_of a))) in
  let app = inst [ety,`:A`] `APPEND:A list->A list->A list` in
  let rec wit t =
    if t = aux then mk_const("NIL",[ety,`:A`]) else
    match strip_comb t with
      c,[h;y] when fst(dest_const c) = "APPEND" -> mk_binop app h (wit y)
    | c,[h;y] when fst(dest_const c) = "CONS" -> mk_cons h (wit y)
    | _ -> failwith "C2BP2AUX_APPEND_WITNESS_TAC" in
  (EXISTS_TAC (wit x) THEN REWRITE_TAC[APPEND; GSYM APPEND_ASSOC]) g;;

let C2BP2AUX_is_build_aux th =
  try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "build_aux" with Failure _ -> false;;

let C2BP2AUX_compile_exps_code_locs = prove
 (`!max_app xs aux ys aux1.
     clos_to_bvl_compile_exps max_app xs aux = (ys,aux1)
     ==> ?aux2. aux1 = APPEND aux2 aux /\
                MAP FST aux2 = MAP ((+) (num_stubs max_app)) (REVERSE (code_locs xs))`,
  let fin_tac =
    REPEAT PAIRARG_TAC THEN GVS[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    TRY(C2BP2AUX_APPEND_WITNESS_TAC THEN
        ASM_REWRITE_TAC[MAP_APPEND; REVERSE_APPEND; MAP; REVERSE; APPEND; APPEND_NIL;
                        GSYM APPEND_ASSOC] THEN
        REWRITE_TAC[CONS_11; ADD_SYM]) in
  let unfold_tac =
    ONCE_REWRITE_TAC[clos_to_bvl_compile_exps_def] THEN
    REWRITE_TAC[code_locs_def; LET_DEF; LET_END_DEF] in
  let letrec_tac =
    CASES_ON `fns:(num#clos_exp)list` THENL
     [unfold_tac THEN GVS[] THEN REWRITE_TAC[list_of_seq; APPEND; code_locs_def] THEN
      FIRST_ASSUM MATCH_ACCEPT_TAC;
      CASES_ON `a0:num#clos_exp` THEN CASES_ON `a1:(num#clos_exp)list` THEN
      unfold_tac THEN GVS[] THENL
       [REPEAT PAIRARG_TAC THEN GVS[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
        FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(fun eq ->
          CAKE_STRIP_ASSUME_TAC (MATCH_MP ih eq))) THEN
        RVEQ_TAC THEN C2BP2AUX_APPEND_WITNESS_TAC THEN
        ASM_REWRITE_TAC[MAP_APPEND; REVERSE_APPEND; MAP; REVERSE; APPEND; APPEND_NIL;
                        GSYM APPEND_ASSOC] THEN
        REWRITE_TAC[LISTAUX_list_of_seq_1; APPEND; MULT_CLAUSES; ADD_CLAUSES; REVERSE;
                    MAP; CONS_11; ADD_SYM];
        REPEAT PAIRARG_TAC THEN GVS[] THEN
        FIRST_ASSUM(CAKE_STRIP_ASSUME_TAC o MATCH_MP lemma2 o check C2BP2AUX_is_build_aux) THEN
        RVEQ_TAC THEN
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP build_aux_thm o check C2BP2AUX_is_build_aux) THEN
        GVS[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
        FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(fun eq -> FIRST_ASSUM(fun eq2 ->
          CAKE_STRIP_ASSUME_TAC (MATCH_MP (MATCH_MP ih eq) eq2)))) THEN
        RVEQ_TAC THEN C2BP2AUX_APPEND_WITNESS_TAC THEN
        ASM_REWRITE_TAC[MAP_APPEND; REVERSE_APPEND; MAP; REVERSE; APPEND; APPEND_NIL;
                        GSYM APPEND_ASSOC; C2BP2AUX_MAP_REVERSE_GENLIST]]] in
  MATCH_MP_TAC clos_to_bvl_compile_exps_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  (fun g -> if is_imp (snd g) && is_forall (rand (snd g)) then DISCH_THEN STRIP_ASSUME_TAC g
            else ALL_TAC g) THEN
  REPEAT GEN_TAC THEN
  (fun g -> if CLOS2AUX_CONST_IN "clos_Letrec" (snd g) then letrec_tac g
            else (unfold_tac THEN fin_tac) g));;

(* HOL4 line 5708 *)
let compile_exps_code_locs = prove
 (`!max_app xs aux ys aux2.
     clos_to_bvl_compile_exps max_app xs aux = (ys,APPEND aux2 aux)
     ==> MAP FST aux2 = MAP ((+) (num_stubs max_app)) (REVERSE (code_locs xs))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP C2BP2AUX_compile_exps_code_locs) THEN
  REWRITE_TAC[APPEND_RCANCEL] THEN MESON_TAC[]);;
let C2BP2AUX_init_code_LENGTH = prove
 (`!max_app.
     LENGTH (APPEND (list_of_seq (\n. n + 2,generate_generic_app max_app n) max_app)
              (FLAT (list_of_seq (\tot. list_of_seq
                       (\prev. tot - prev + 1,generate_partial_app_closure_fn tot prev) tot)
                     max_app))) =
     max_app + (max_app * (max_app - 1)) DIV 2`,
  GEN_TAC THEN REWRITE_TAC[LENGTH_APPEND; LENGTH_LIST_OF_SEQ] THEN
  MP_TAC(BETA_RULE(ISPECL [`max_app:num`;
     `\tot prev. tot - prev + 1:num,generate_partial_app_closure_fn tot prev`]
     triangle_table_size)) THEN
  SIMP_TAC[]);;

(* HOL4 line 5733 (clos_to_bvl's init_code) *)
let init_code_ok = prove
 (`!max_app.
     0 < max_app
     ==> (!n. n < max_app
              ==> lookup (generic_app_fn_location n) (clos_to_bvl_init_code max_app) =
                  SOME (n + 2,generate_generic_app max_app n)) /\
         (!tot n.
            tot < max_app /\ n < tot
            ==> lookup (partial_app_fn_location max_app tot n) (clos_to_bvl_init_code max_app) =
                SOME ((tot - n) + 1,generate_partial_app_closure_fn tot n))`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[clos_to_bvl_init_code_def; lookup_fromList; C2BP2AUX_init_code_LENGTH;
              generic_app_fn_location_def; partial_app_fn_location_def] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `n < m ==> n < m + k`; EL_APPEND1; LENGTH_LIST_OF_SEQ;
                 EL_LIST_OF_SEQ];
    MP_TAC(SPECL [`max_app:num`; `n:num`; `tot:num`] triangle_div_lemma) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `a + b < c ==> m + b + a < m + c`] THEN
    SIMP_TAC[EL_APPEND2; LENGTH_LIST_OF_SEQ; ARITH_RULE `m <= m + k:num`] THEN
    REWRITE_TAC[ARITH_RULE `(m + t + n) - m = n + t:num`] THEN
    MP_TAC(BETA_RULE(ISPECL [`n:num`; `tot:num`; `max_app:num`;
       `\tot prev. tot - prev + 1:num,generate_partial_app_closure_fn tot prev`]
       triangle_el_no_suff)) THEN
    ASM_SIMP_TAC[]]);;

(* HOL4 line 5760 *)
let domain_init_code_lt_num_stubs = prove
 (`!max_app x. x IN domain (clos_to_bvl_init_code max_app) ==> x < num_stubs max_app`,
  REWRITE_TAC[clos_to_bvl_init_code_def; domain_fromList; C2BP2AUX_init_code_LENGTH;
              IN_COUNT; num_stubs_def] THEN
  ARITH_TAC);;

(* HOL4 line 5769 *)
let domain_init_code = prove
 (`!max_app.
     0 < max_app
     ==> domain (clos_to_bvl_init_code max_app) =
         pred_set_count (max_app + (max_app * (max_app - 1)) DIV 2)`,
  REWRITE_TAC[clos_to_bvl_init_code_def; domain_fromList; C2BP2AUX_init_code_LENGTH]);;
let C2BP2AUX_MAP_FST_MAP2 = prove
 (`!(f:A->B->C#D) g l1 l2.
     (!x y. FST (f x y) = g x) ==> MAP FST (MAP2 f l1 l2) = MAP g l1`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP2_DEF; MAP]);;

(* HOL4 line 5779 *)
let compile_prog_code_locs = prove
 (`!ls max_app.
     MAP FST (clos_to_bvl_compile_prog max_app ls) =
     APPEND (MAP ((+) (num_stubs max_app) o FST) ls)
       (MAP ((+) (num_stubs max_app)) (REVERSE (code_locs (MAP (SND o SND) ls))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_to_bvl_compile_prog_def] THEN PAIRARG_TAC THEN
  REWRITE_TAC[MAP_APPEND] THEN BINOP_TAC THENL
   [MATCH_MP_TAC C2BP2AUX_MAP_FST_MAP2 THEN
    REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; FST; o_THM] THEN ARITH_TAC;
    MATCH_MP_TAC compile_exps_code_locs THEN
    EXISTS_TAC `[]:(num#num#bvl_exp)list` THEN EXISTS_TAC `new_exps:bvl_exp list` THEN
    ASM_REWRITE_TAC[APPEND_NIL]]);;
let C2BP2AUX_PERM_code_merge = prove
 (`!(xs:(num#A)list) ys. PERM (code_merge xs ys) (APPEND xs ys)`,
  MATCH_MP_TAC code_merge_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[code_merge_def] THEN
  CASES_ON `xs:(num#A)list` THEN CASES_ON `ys:(num#A)list` THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[APPEND; APPEND_NIL; PERM_REFL] THEN FS[] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[PERM_CONS_IFF];
    REWRITE_TAC[PERM_CONS_EQ_APPEND] THEN
    MAP_EVERY EXISTS_TAC [`CONS (a0:num#A) a1`; `a1':(num#A)list`] THEN
    ASM_SIMP_TAC[APPEND]]);;

(* HOL4 line 5795 *)
let IMP_PERM_code_merge = prove
 (`!(xs:(num#A)list) ys zs. PERM (APPEND xs ys) zs ==> PERM (code_merge xs ys) zs`,
  MESON_TAC[C2BP2AUX_PERM_code_merge; PERM_TRANS]);;

(* HOL4 line 5819 (HOL4 xs2 ++ xs3 ++ xs1 is left-associative) *)
let code_split_IMP_PERM = prove
 (`!(xs1:(num#A)list) xs2 xs3 ts1 ts2.
     code_split xs1 xs2 xs3 = (ts1,ts2)
     ==> PERM (APPEND ts1 ts2) (APPEND (APPEND xs2 xs3) xs1)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[code_split_def; PAIR_EQ] THENL
   [SIMP_TAC[APPEND_NIL; PERM_REFL]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
    [`CONS (h:num#A) xs3`; `xs2:(num#A)list`; `ts1:(num#A)list`; `ts2:(num#A)list`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MATCH_MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] PERM_TRANS) th)) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[PERM_CONS_EQ_APPEND] THEN
  MAP_EVERY EXISTS_TAC [`APPEND (xs2:(num#A)list) xs3`; `t:(num#A)list`] THEN
  REWRITE_TAC[APPEND_ASSOC; PERM_APPEND_IFF; PERM_APPEND]);;

(* HOL4 line 5831 *)
let PERM_code_sort = prove
 (`!(xs:(num#A)list). PERM (code_sort xs) xs`,
  MATCH_MP_TAC code_sort_ind THEN REWRITE_TAC[code_sort_def; PERM_REFL] THEN
  REPEAT STRIP_TAC THEN PAIRARG_TAC THEN
  MATCH_MP_TAC IMP_PERM_code_merge THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP code_split_IMP_PERM o check (is_eq o concl)) THEN
  MATCH_MP_TAC PERM_TRANS THEN
  EXISTS_TAC `APPEND (xs':(num#A)list) ys` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PERM_CONG THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> fst(dest_const(fst(strip_comb(concl th)))) = "PERM")) THEN
    REWRITE_TAC[APPEND]]);;

(* HOL4 line 5843 *)
let set_MAP_code_sort = prove
 (`!(f:num#A->B) x. set_of_list (MAP f (code_sort x)) = set_of_list (MAP f x)`,
  MESON_TAC[PERM_LIST_TO_SET; PERM_MAP; PERM_code_sort]);;

(* HOL4 line 5851 *)
let ALL_DISTINCT_code_sort = prove
 (`!(xs:(num#A)list). ALL_DISTINCT (MAP FST (code_sort xs)) <=> ALL_DISTINCT (MAP FST xs)`,
  MESON_TAC[ALL_DISTINCT_PERM; PERM_MAP; PERM_code_sort]);;

(* HOL4 line 5858 *)
let PERM_IMP_fromAList_EQ_fromAList = prove
 (`!(xs:(num#A)list) ys. PERM xs ys ==> ALL_DISTINCT (MAP FST xs) ==> fromAList xs = fromAList ys`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (ys:(num#A)list))` ASSUME_TAC THENL
   [ASM_MESON_TAC[ALL_DISTINCT_PERM; PERM_MAP]; ALL_TAC] THEN
  SIMP_TAC[spt_eq_thm; wf_fromAList; lookup_fromAList] THEN X_GEN_TAC `k:num` THEN
  CASES_ON `ALOOKUP (xs:(num#A)list) k` THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[ALOOKUP_NONE]) THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[ALOOKUP_NONE] THEN
    ASM_MESON_TAC[MEM_PERM; PERM_MAP];
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN
    ASM_MESON_TAC[ALOOKUP_MEM; MEM_PERM]]);;

(* HOL4 line 5872 *)
let fromAList_code_sort = prove
 (`!(xs:(num#A)list). ALL_DISTINCT (MAP FST xs) ==> fromAList (code_sort xs) = fromAList xs`,
  MESON_TAC[PERM_IMP_fromAList_EQ_fromAList; PERM_code_sort; ALL_DISTINCT_code_sort]);;

(* HOL4 line 5890: Overload code_loc' = \e. code_locs [e] (written out where *)
(* used)                                                                      *)

(* HOL4 line 5892 *)
let MAP_FST_chain_exps = prove
 (`!i ls. ~(ls = []) ==> MAP FST (chain_exps i ls) = MAP ((+) i) (COUNT_LIST (LENGTH ls))`,
  MATCH_MP_TAC chain_exps_ind THEN REWRITE_TAC[chain_exps_def; MAP; MAP_COUNT_LIST] THEN
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[LENGTH; ONE; LIST_OF_SEQ; ADD_CLAUSES];
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    REWRITE_TAC[NOT_CONS_NIL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[LENGTH] THEN GEN_REWRITE_TAC RAND_CONV [CONJUNCT2 LIST_OF_SEQ] THEN
    REWRITE_TAC[ADD_CLAUSES; CONS_11] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ARITH_TAC]);;

(* HOL4 line 5902 *)
let MAP_FST_chain_exps_any = prove
 (`!i ls. MAP FST (chain_exps i ls) = MAP ((+) i) (COUNT_LIST (MAX 1 (LENGTH ls)))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `ls:clos_exp list = []` THENL
   [ASM_REWRITE_TAC[chain_exps_def; MAP; LENGTH; MAP_COUNT_LIST] THEN
    REWRITE_TAC[ARITH_RULE `MAX 1 0 = SUC 0`; LIST_OF_SEQ; ADD_CLAUSES];
    ASM_SIMP_TAC[MAP_FST_chain_exps] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM LENGTH_EQ_NIL]) THEN ARITH_TAC]);;

(* HOL4 line 5920 *)
let chain_exps_code_locs = prove
 (`!n es. code_locs (MAP (SND o SND) (chain_exps n es)) = code_locs es`,
  MATCH_MP_TAC chain_exps_ind THEN REWRITE_TAC[chain_exps_def; MAP; o_THM] THEN
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[code_locs_def];
    ONCE_REWRITE_TAC[code_locs_cons] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[code_locs_def; LET_DEF; LET_END_DEF; APPEND_NIL] THEN
    GEN_REWRITE_TAC RAND_CONV [code_locs_cons] THEN REFL_TAC]);;

let _ = cake_add_simps [chain_exps_code_locs];;

(* HOL4 line 5929 *)
let chain_exps_ALL_DISTINCT = prove
 (`!i ls. ALL_DISTINCT (MAP FST (chain_exps i ls))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAP_FST_chain_exps_any] THEN
  MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN REWRITE_TAC[all_distinct_count_list] THEN
  ARITH_TAC);;

let _ = cake_add_simps [chain_exps_ALL_DISTINCT];;

(* HOL4 line 5939 *)
let chain_exps_LE = prove
 (`!n xs. ALL ((<=) n) (MAP FST (chain_exps n xs))`,
  REWRITE_TAC[MAP_FST_chain_exps_any] THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM] THEN ARITH_TAC);;

(* HOL4 line 5948 *)
let chain_exps_GT = prove
 (`!n xs. ~(xs = []) ==> ALL ((>) (n + LENGTH xs)) (MAP FST (chain_exps n xs))`,
  SIMP_TAC[MAP_FST_chain_exps] THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM; MEM_COUNT_LIST] THEN ARITH_TAC);;

(* HOL4 line 5957: val common_def = compile_common_def |> REWRITE_RULE      *)
(* [GSYM EVEN_MOD2, GSYM make_even_def] (a rewritten definition for the     *)
(* proofs; compile_common_def of clos_to_bvl.ml)                             *)

(* helpers for compile_common_distinct_locs *)

(* clos_annotate_compile keeps the names and does not add code locations *)
let C2BP2AUX_annotate_compile_code_locs = prove
 (`!prog. MAP FST (clos_annotate_compile prog) = MAP FST prog /\
          set_of_list (code_locs (MAP (SND o SND) (clos_annotate_compile prog))) SUBSET
          set_of_list (code_locs (MAP (SND o SND) prog)) /\
          (ALL_DISTINCT (code_locs (MAP (SND o SND) prog))
           ==> ALL_DISTINCT (code_locs (MAP (SND o SND) (clos_annotate_compile prog))))`,
  REWRITE_TAC[clos_annotate_compile_def] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; code_locs_def; SUBSET_REFL; ALL_DISTINCT] THEN
  SPEC_TAC(`h:num#num#clos_exp`,`h:num#num#clos_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`nm:num`; `ar:num`; `ex:clos_exp`] THEN
  CAKE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[code_locs_cons] THEN REWRITE_TAC[o_THM; FST; SND; HD_annotate_SING] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC (ISPECL [`ar:num`; `[ex:clos_exp]`] annotate_code_locs) THEN
  REWRITE_TAC[ALL_DISTINCT_APPEND; SET_OF_LIST_APPEND] THEN
  REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM SET_TAC[];
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[]]);;

(* the arithmetic of compile_common_distinct_locs: the chained names below  *)
(* hi, the code locations even and at least N >= hi, the names of the       *)
(* functions of clos_call the successors of code locations                  *)
let C2BP2AUX_distinct_core = prove
 (`!(A1:num list) A2 B hi N.
     ALL_DISTINCT A1 /\ ALL_DISTINCT A2 /\ ALL_DISTINCT B /\
     (!x. MEM x A1 ==> x < hi) /\ hi <= N /\
     (!x. MEM x B ==> EVEN x /\ N <= x) /\
     (!x. MEM x A2 ==> ?y. EVEN y /\ N <= y /\ x = SUC y)
     ==> ALL_DISTINCT (APPEND (APPEND A1 A2) B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. MEM x (A2:num list) ==> ~EVEN x /\ N < x` ASSUME_TAC THENL
   [X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (fun th ->
      is_exists (rand (snd (strip_forall (concl th)))))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[EVEN] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ALL_DISTINCT_APPEND; MEM_APPEND] THEN
  CONJ_TAC THEN X_GEN_TAC `e:num` THEN REPEAT STRIP_TAC THEN RES_TAC THEN
  FIRST [ASM_ARITH_TAC; ASM_MESON_TAC[]]);;

let C2BP2AUX_pair_case_id = prove
 (CASE_TERM `!p:A#B. (match p with (x,y) -> (x,y)) = p`,
  GEN_TAC THEN C2BP2AUX_PAIR_CASES_TAC `p:A#B` `a:A` `b:B` THEN CAKE_REWRITE_TAC[]);;

(* HOL4 line 5960 *)
let compile_common_distinct_locs = prove
 (`!c e c' p.
     compile_common c e = (c',p)
     ==> ALL_DISTINCT (APPEND (MAP FST p) (code_locs (MAP (SND o SND) p)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_common_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
  REPEAT PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN
  MP_TAC (ISPEC `APPEND (chain_exps (clos_to_bvl_config_next_loc c) es'') aux`
    C2BP2AUX_annotate_compile_code_locs) THEN
  REWRITE_TAC[ALL_DISTINCT_APPEND; GSYM IN_SET_OF_LIST] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ALL_DISTINCT (APPEND (MAP FST (APPEND (chain_exps (clos_to_bvl_config_next_loc c) es'') aux))
      (code_locs (MAP (SND o SND) (APPEND (chain_exps (clos_to_bvl_config_next_loc c) es'') aux))))`
    MP_TAC THENL [ALL_TAC;
    REWRITE_TAC[ALL_DISTINCT_APPEND; GSYM IN_SET_OF_LIST] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[]] THEN
  ABBREV_TAC `N = if (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH (e:clos_exp list))) MOD 2 = 0
                  then clos_to_bvl_config_next_loc c + MAX 1 (LENGTH e)
                  else (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH e)) + 1` THEN
  SUBGOAL_THEN `EVEN N /\ clos_to_bvl_config_next_loc c + MAX 1 (LENGTH (e:clos_exp list)) <= N`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN COND_CASES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM EVEN_MOD2]) THEN
    ASM_REWRITE_TAC[LE_REFL; EVEN_ADD; ARITH_RULE `n <= n + 1`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the lengths *)
  SUBGOAL_THEN `LENGTH (es'':clos_exp list) = LENGTH (e:clos_exp list)` ASSUME_TAC THENL
   [IMP_RES_TAC clos_call_compile_LENGTH THEN IMP_RES_TAC clos_knownProof_compile_LENGTH THEN
    IMP_RES_TAC renumber_code_locs_list_length THEN FS[];
    ALL_TAC] THEN
  (* clos_number *)
  MP_TAC (ISPECL [`N:num`; `clos_mti_compile (clos_to_bvl_config_do_mti c)
      (clos_to_bvl_config_max_app c) e`] (CONJUNCT1 renumber_code_locs_EVEN)) THEN
  MP_TAC (ISPECL [`N:num`; `clos_mti_compile (clos_to_bvl_config_do_mti c)
      (clos_to_bvl_config_max_app c) e`] renumber_code_locs_list_distinct) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  (* clos_known *)
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP compile_code_locs_bag) THEN
  SUBGOAL_THEN `set_of_list (code_locs es') SUBSET set_of_list (code_locs es) /\
                ALL_DISTINCT (code_locs es')` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_TO_BAG_SUBSET; LIST_TO_BAG_DISTINCT; BAG_ALL_DISTINCT_SUB_BAG];
    ALL_TAC] THEN
  REWRITE_TAC[MAP_APPEND; code_locs_append; chain_exps_code_locs] THEN
  MATCH_MP_TAC C2BP2AUX_distinct_core THEN
  MAP_EVERY EXISTS_TAC [`clos_to_bvl_config_next_loc c + MAX 1 (LENGTH (es'':clos_exp list))`;
                        `N:num`] THEN
  ASM_REWRITE_TAC[chain_exps_ALL_DISTINCT; MAP_FST_chain_exps_any] THEN
  REWRITE_TAC[MEM_MAP; MEM_COUNT_LIST] THEN
  CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL
    [MESON_TAC[LT_ADD_LCANCEL]; ALL_TAC]]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  CASES_ON `clos_to_bvl_config_do_call c` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_call_compile_def; LET_DEF; LET_END_DEF]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THENL
   [(* clos_call on: the names of the new functions are distinct *)
    RULE_ASSUM_TAC(REWRITE_RULE[C2BP2AUX_pair_case_id]) THEN
      MP_TAC (ISPECL [`es':clos_exp list`; `(LN:num_set,[]:(num#num#clos_exp)list)`;
        `es'':clos_exp list`; `(g:num_set,aux:(num#num#clos_exp)list)`] calls_ALL_DISTINCT) THEN
      ASM_REWRITE_TAC[MAP; ALL_DISTINCT; set_of_list; DISJOINT_EMPTY];
    (* clos_call off *)
    RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
      REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
      RVEQ_TAC THEN ASM_REWRITE_TAC[MAP; ALL_DISTINCT];
    (* clos_call on: the code locations are distinct *)
    RULE_ASSUM_TAC(REWRITE_RULE[C2BP2AUX_pair_case_id]) THEN
      MP_TAC (ISPECL [`es':clos_exp list`; `(LN:num_set,[]:(num#num#clos_exp)list)`;
        `es'':clos_exp list`; `(g:num_set,aux:(num#num#clos_exp)list)`]
        calls_code_locs_ALL_DISTINCT) THEN
      ASM_REWRITE_TAC[MAP; code_locs_def; APPEND_NIL];
    RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
      REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
      RVEQ_TAC THEN ASM_REWRITE_TAC[MAP; code_locs_def; APPEND_NIL];
    (* clos_call on: the code locations are even, the new names odd *)
    RULE_ASSUM_TAC(REWRITE_RULE[C2BP2AUX_pair_case_id]) THEN
      SUBGOAL_THEN `!x. MEM x (code_locs es') ==> EVEN x /\ N <= x` ASSUME_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_SET_OF_LIST]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC (ISPECL [`es':clos_exp list`; `(LN:num_set,[]:(num#num#clos_exp)list)`;
        `es'':clos_exp list`; `(g:num_set,aux:(num#num#clos_exp)list)`] calls_code_locs_MEM) THEN
      MP_TAC (ISPECL [`es':clos_exp list`; `(LN:num_set,[]:(num#num#clos_exp)list)`;
        `es'':clos_exp list`; `(g:num_set,aux:(num#num#clos_exp)list)`] calls_add_SUC_code_locs) THEN
      ASM_REWRITE_TAC[MAP; code_locs_def; set_of_list; UNION_EMPTY; MEM; MEM_APPEND] THEN
      REWRITE_TAC[SUBSET; IN_IMAGE; IN_SET_OF_LIST; MEM_MAP] THEN
      REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
      REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
      RVEQ_TAC THEN REWRITE_TAC[MAP; code_locs_def; APPEND_NIL; MEM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_SET_OF_LIST]) THEN ASM_MESON_TAC[]]);;

(* HOL4 line 6047 *)
let compile_all_distinct_locs = prove
 (`!c e c' p n. clos_to_bvl_compile c e = (c',p,n) ==> ALL_DISTINCT (MAP FST p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_to_bvl_compile_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
  REPEAT PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN
  REWRITE_TAC[ALL_DISTINCT_code_sort; MAP_APPEND; MAP; compile_prog_code_locs] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP compile_common_distinct_locs) THEN
  SUBGOAL_THEN `!x. MEM x (MAP FST (toAList (clos_to_bvl_init_code
                   (clos_to_bvl_config_max_app c'')))) ==>
                  x + 2 < num_stubs (clos_to_bvl_config_max_app c'')` ASSUME_TAC THENL
   [REWRITE_TAC[toAList_domain; clos_to_bvl_init_code_def; domain_fromList;
                C2BP2AUX_init_code_LENGTH; IN_COUNT; num_stubs_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (APPEND (MAP FST (prog:(num#num#clos_exp)list))
                  (REVERSE (code_locs (MAP (SND o SND) prog))))` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL_DISTINCT (APPEND (MAP FST (prog:(num#num#clos_exp)list))
                  (code_locs (MAP (SND o SND) prog)))` THEN
    REWRITE_TAC[ALL_DISTINCT_APPEND; ALL_DISTINCT_REVERSE; MEM_REVERSE];
    ALL_TAC] THEN
  SUBGOAL_THEN `MAP ((+) (num_stubs (clos_to_bvl_config_max_app c'')) o FST)
                  (prog:(num#num#clos_exp)list) =
                MAP ((+) (num_stubs (clos_to_bvl_config_max_app c''))) (MAP FST prog)`
    SUBST1_TAC THENL [REWRITE_TAC[MAP_o]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MAP_APPEND] THEN
  ABBREV_TAC `q = APPEND (MAP FST (prog:(num#num#clos_exp)list))
                   (REVERSE (code_locs (MAP (SND o SND) prog)))` THEN
  SUBGOAL_THEN `2 <= num_stubs (clos_to_bvl_config_max_app c'')` ASSUME_TAC THENL
   [REWRITE_TAC[num_stubs_def] THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `ns = num_stubs (clos_to_bvl_config_max_app c'')` THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP ((+) ns) (q:num list))` ASSUME_TAC THENL
   [MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN ASM_REWRITE_TAC[EQ_ADD_LCANCEL] THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[ALL_DISTINCT_APPEND; ALL_DISTINCT; MEM; MEM_APPEND; ALL_DISTINCT_MAP_FST_toAList] THEN
  REWRITE_TAC[MEM_MAP] THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[MEM_MAP; LEFT_IMP_EXISTS_THM] o check (fun th ->
    can (find_term ((=) `toAList:(num#bvl_exp)spt->(num#num#bvl_exp)list`)) (concl th))) THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_ARITH_TAC);;
