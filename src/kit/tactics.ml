(* ========================================================================= *)
(* CakeML kit: HOL4-style tactics (not a translator: the same proof ideas,   *)
(* written by hand, with tactics that behave like HOL4's).                   *)
(*                                                                           *)
(*   CASES_ON tm      Cases_on: split on tm by its type's cases theorem; a   *)
(*                    compound tm keeps its equation as an assumption.       *)
(*   TOP_CASE_TAC     split the outermost case/if in the goal conclusion.    *)
(*   CASE_TAC         split the innermost case/if in the goal conclusion.    *)
(*   EVERY_CASE_TAC   split every case/if in the goal and assumptions.       *)
(*   DRULE th         drule: MP_TAC th with its first antecedent matched     *)
(*                    against an assumption (conjunctions curried first).    *)
(*   DXRULE th        dxrule: the same, removing the assumption used.        *)
(*   DRULE_ALL th     drule_all: every antecedent matched.                   *)
(*   IRULE th         irule: backward chaining, antecedents as subgoals.     *)
(*   IMP_RES_TAC th   imp_res_tac: resolve th with all assumptions.          *)
(*   RES_TAC          res_tac: resolve implicational assumptions with the    *)
(*                    others.                                                *)
(*   PAIRARG_TAC      pairarg_tac: split a pair_CASE e f with e not a pair.  *)
(*   INDUCT_ON x      Induct_on: structural induction on the variable x.     *)
(*   ASM_EXISTS_TAC   asm_exists_tac: witnesses matched with assumptions.    *)
(*   IRULE_AT pos th  irule_at: th applied to a conjunct of an existential.  *)
(*   SUFF_TAC t       suff_tac; QEXISTS_TAC "t", QSUFF_TAC "t" (qexists_tac, *)
(*                    qsuff_tac) parse t in the goal context.                *)
(*   QPAT_X_ASSUM "pat" ttac, QPAT_ASSUM  qpat_x_assum, qpat_assum;          *)
(*   QSPEC_THEN "t" ttac th, QSPECL_THEN  qspec_then, qspecl_then.          *)
(*   QCASES_ON "t"    Cases_on with t parsed in the goal context.            *)
(*   LAST_ASSUM, LAST_X_ASSUM  last_assum, last_x_assum (oldest first).      *)
(*   RENAME1 "pat"    rename1; RENAME_TAC ["pat"; ...] rename;               *)
(*                    MATCH_ASMSUB_RENAME_TAC, MATCH_GOALSUB_RENAME_TAC.     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The rewrites used after a case split (HOL4's case_rws + bool_ss): case    *)
(* equations, distinctness, injectivity, with a cached net.                  *)
(* ------------------------------------------------------------------------- *)

let cake_case_net = ref (basic_net());;

(* the case infos and the basic net the net was made from *)
let cake_case_net_infos = ref (!the_case_infos);;
let cake_case_net_basic = ref (basic_net());;

let cake_rebuild_case_net () =
  cake_case_net :=
    itlist (net_of_thm true)
           (itlist (mk_rewrites false) (all_case_rewrites()) [])
           (basic_net());
  cake_case_net_infos := !the_case_infos;
  cake_case_net_basic := basic_net();;

cake_rebuild_case_net();;

(* after new datatypes only their theorems are added (a rebuild of the net  *)
(* takes half a minute in a session with all the semantics); everything is *)
(* rebuilt if a case info was replaced or the basic rewrites changed       *)
let cake_update_case_net () =
  let old = !cake_case_net_infos and cur = !the_case_infos in
  let known e l = exists (fun e' -> e' == e) l in
  if exists (fun e -> not (known e cur)) old ||
     not (basic_net() == !cake_case_net_basic)
  then cake_rebuild_case_net() else
  let news = filter (fun e -> not (known e old)) cur in
  let thms = itlist (fun (_,ci) l -> ci.ci_def :: ci.ci_distinct @
                                     ci.ci_inject @ l) news [] in
  cake_case_net := itlist (net_of_thm true)
                          (itlist (mk_rewrites false) thms [])
                          (!cake_case_net);
  cake_case_net_infos := cur;;

let cake_type s =
  let res = cake_type s in
  cake_update_case_net(); res;;

let CASE_REWRITE_CONV thl =
  GENERAL_REWRITE_CONV true TOP_DEPTH_CONV (!cake_case_net) thl;;

let CASE_REWRITE_TAC thl = CONV_TAC (CASE_REWRITE_CONV thl);;

let CASE_REWRITE_RULE thl = CONV_RULE (CASE_REWRITE_CONV thl);;

(* ------------------------------------------------------------------------- *)
(* Cases_on.                                                                 *)
(* ------------------------------------------------------------------------- *)

(* cases theorems for types that are not datatypes (e.g. llist, path):      *)
(* cake_register_cases "llist" LLIST_CASES  with a theorem                  *)
(* !x. x = C1 \/ (?a b. x = C2 a b) \/ ...  makes CASES_ON work on them      *)

let cake_extra_cases = ref ([] : (string * thm) list);;

let cake_register_cases tyname th =
  cake_extra_cases := (tyname,th) ::
                      filter (fun (n,_) -> n <> tyname) (!cake_extra_cases);;

let nchotomy_of_type ty =
  let n = fst(dest_type ty) in
  try assoc n (!cake_extra_cases) with Failure _ ->
  try (case_info_of_tyname n).ci_nchotomy
  with Failure _ ->
    let th = cases n in
    find (fun c -> fst(dest_type(type_of(fst(dest_forall(concl c))))) = n)
         (CONJUNCTS th);;

let CASES_ON (tm:term) : tactic =
  fun (asl,w as gl) ->
    let ty = type_of tm in
    if ty = bool_ty then
      (if is_var tm then BOOL_CASES_TAC tm gl
       else (ASM_CASES_TAC tm THEN
             (* rewrite the goal AND the other assumptions with the new fact, *)
             (* or a conditional in an assumption is split again and again   *)
             FIRST_ASSUM(fun cth ->
               RULE_ASSUM_TAC(fun th -> if th == cth then th
                                        else REWRITE_RULE[cth] th) THEN
               REWRITE_TAC[cth])) gl)
    else
      let nch = ISPEC tm (nchotomy_of_type ty) in
      if is_var tm then
        (MP_TAC nch THEN
         DISCH_THEN(REPEAT_TCL STRIP_THM_THEN
           (fun th -> CAKE_SUBST_ALL_TAC th ORELSE ASSUME_TAC th))) gl
      else
        (MP_TAC nch THEN
         DISCH_THEN(REPEAT_TCL STRIP_THM_THEN
           (fun th -> (CAKE_SUBST_ALL_TAC th THEN ASSUME_TAC th)
                      ORELSE ASSUME_TAC th))) gl;;

(* ------------------------------------------------------------------------- *)
(* Finding case expressions.                                                 *)
(* ------------------------------------------------------------------------- *)

(* the scrutinee of a case application or conditional *)

let scrutinee_of tm =
  if is_cond tm then lhand(rator tm)
  else let _,x,_ = dest_case_app tm in x;;

(* innermost-first search, as HOL4's case_find_subterm *)

let case_find_subterm p =
  let f = find_term p in
  let rec g t =
    if is_comb t then
      (try g (f (rator t)) with Failure _ ->
         try g (f (rand t)) with Failure _ -> t)
    else if is_abs t then
      (try g (f (body t)) with Failure _ -> t)
    else t in
  fun t -> g (f t);;

let scrutinized_and_free_in whole t =
  if (is_cond t || is_case_app t) then
    let x = scrutinee_of t in
    if free_in x whole && not (x = cake_true_tm) && not (x = cake_false_tm)
    then x else failwith "scrutinized_and_free_in"
  else failwith "scrutinized_and_free_in";;

(* can (scrutinized_and_free_in whole), without an exception per subterm *)
let is_scrutinized_and_free_in whole t =
  (is_cond t || is_case_app t) &&
  (let x = if is_cond t then lhand(rator t) else hd(snd(strip_comb t)) in
   free_in x whole && not (x = cake_true_tm) && not (x = cake_false_tm));;

let first_case_scrutinee whole tm =
  let t = find_term (is_scrutinized_and_free_in whole) tm in
  scrutinized_and_free_in whole t;;

let inner_case_scrutinee whole tm =
  let t = case_find_subterm (is_scrutinized_and_free_in whole) tm in
  scrutinized_and_free_in whole t;;

(* after a split: drop reflexive assumptions, rewrite with the new ones and *)
(* the case rewrites                                                         *)

(* (functions of the goal, so that the case net is read when they run, not  *)
(* when the kit is loaded)                                                   *)

let CASE_TIDY_TAC : tactic =
  fun gl ->
   (REPEAT (FIRST_X_ASSUM (fun th ->
      let c = concl th in
      if is_eq c && lhs c = rhs c then ALL_TAC else failwith "keep")) THEN
    ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[]) gl;;

let CASE_ASM_TIDY_TAC : tactic =
  fun gl ->
   (RULE_ASSUM_TAC (CASE_REWRITE_RULE[]) THEN
    REPEAT (FIRST_X_ASSUM (fun th ->
      let c = concl th in
      if c = cake_true_tm then ALL_TAC
      else if c = cake_false_tm then CONTR_TAC th
      else failwith "keep"))) gl;;

let TOP_CASE_TAC : tactic =
  fun (asl,w as gl) ->
    let x = first_case_scrutinee w w in
    (CASES_ON x THEN CASE_TIDY_TAC) gl;;

(* TOP_CASE_NOPAIR_TAC: TOP_CASE_TAC as HOL4's, which does not see paired   *)
(* lets (HOL4 writes them with UNCURRY): pair_CASE (let (a,b) = e in t, or  *)
(* a match on a pair) is skipped, and the tactic fails if that is all there *)
(* is (PAIRARG_TAC splits those).  The kit's TOP_CASE_TAC splits the first  *)
(* case expression of any kind, also pair_CASE; the full load of 2026-11-20 *)
(* showed that existing proofs rely on that (hol4/mc_multiword), so it is a *)
(* separate tactic.  Since 2026-11-20.                                       *)
let is_pair_case_app t =
  is_case_app t && (let c,_,_ = dest_case_app t in fst(dest_const c) = "pair_CASE");;

let TOP_CASE_NOPAIR_TAC : tactic =
  fun (asl,w as gl) ->
    let x = scrutinized_and_free_in w
              (find_term (fun t -> is_scrutinized_and_free_in w t &&
                                   not (is_pair_case_app t)) w) in
    (CASES_ON x THEN CASE_TIDY_TAC) gl;;

let CASE_TAC : tactic =
  fun (asl,w as gl) ->
    let x = inner_case_scrutinee w w in
    (CASES_ON x THEN CASE_TIDY_TAC) gl;;

let FULL_CASE_TAC : tactic =
  fun (asl,w as gl) ->
    let whole = list_mk_conj(w :: map (concl o snd) asl) in
    let x = inner_case_scrutinee whole whole in
    (CASES_ON x THEN CASE_ASM_TIDY_TAC THEN CASE_TIDY_TAC) gl;;

let EVERY_CASE_TAC : tactic = REPEAT FULL_CASE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Forward reasoning.                                                        *)
(* ------------------------------------------------------------------------- *)

(* the n theorems of |- t1 /\ ... /\ tn (right nested, as list_mk_conj) *)
let rec kit_conj_split_n n th =
  if n <= 1 then [th] else CONJUNCT1 th :: kit_conj_split_n (n-1) (CONJUNCT2 th);;

(* curry conjunctive antecedents: (a /\ b ==> c) becomes a ==> b ==> c,     *)
(* everywhere under the quantifiers; a non-implication is left alone        *)

let rec IMP_CURRY_RULE th =
  let c = concl th in
  if is_forall c then
    let v = fst(dest_forall c) in
    (* a binder named like a free variable of an antecedent already        *)
    (* discharged is renamed: SPEC would identify the two (and GEN fail)   *)
    let hv = freesl (hyp th) in
    let v' = if mem v hv then variant (hv @ frees c) v else v in
    GEN v' (IMP_CURRY_RULE (SPEC v' th))
  else if is_imp c then
    let a,b = dest_imp c in
    if is_conj a then
      IMP_CURRY_RULE
        (CONV_RULE (REWR_CONV (GSYM IMP_IMP)) th)
    else
      let th1 = IMP_CURRY_RULE (UNDISCH th) in
      DISCH a th1
  else th;;

let MATCH_MP_CURRIED th =
  let th' = IMP_CURRY_RULE (GEN_ALL th) in
  fun a -> MATCH_MP th' a;;

let DRULE th : tactic =
  let mp = MATCH_MP_CURRIED th in
  FIRST_ASSUM (fun a -> MP_TAC (mp a));;

let DXRULE th : tactic =
  let mp = MATCH_MP_CURRIED th in
  FIRST_X_ASSUM (fun a -> MP_TAC (mp a));;

(* drule_all: discharge every antecedent with assumptions *)

let rec drule_all_with asl th =
  let c = concl th in
  if is_imp(snd(strip_forall c)) then
    let mp = MATCH_MP_CURRIED th in
    tryfind (fun a -> drule_all_with asl (mp a)) asl
  else th;;

(* HOL4's drule_all fails on a theorem that is not an implication; the    *)
(* kit's gave the theorem back (FIRST_X_ASSUM DRULE_ALL took the newest     *)
(* assumption whatever it was).  Since 2026-11-20 it fails too (check mode: *)
(* KITDIFF and the old behaviour).                                          *)
let DRULE_ALL th : tactic =
  fun (asl,w as gl) ->
    let th' = IMP_CURRY_RULE (GEN_ALL th) in
    if not (is_imp (snd (strip_forall (concl th')))) then
      (if !kit_check then (kit_diff "DRULE_ALL on a non-implication"; MP_TAC th' gl)
       else failwith "DRULE_ALL: not an implication")
    else MP_TAC (drule_all_with (map snd asl) th') gl;;

(* theorem-tactic forms: use an assumption as the rule *)

let DRULE_THEN (ttac:thm_tactic) th : tactic =
  let mp = MATCH_MP_CURRIED th in
  FIRST_ASSUM (fun a -> ttac (mp a));;

(* irule.  A curried theorem !xs. a1 ==> !ys. a2 ==> c is used as           *)
(* !xs ys. a1 /\ a2 ==> c (HOL4's irule chains on the conclusion after all  *)
(* the antecedents) when MATCH_MP_TAC of it as it is (which matches a2 ==> c *)
(* with the goal) fails; since 2026-11-18                                    *)

let kit_irule_plain th : tactic =
  let th' = GEN_ALL th in
  let c = snd(strip_forall(concl th')) in
  if not (is_imp c) then MATCH_ACCEPT_TAC th' else
  MATCH_MP_TAC th' THEN
  (fun (asl,w as gl) ->
     if is_exists w then ALL_TAC gl else REPEAT CONJ_TAC gl);;

(* !xs. a1 ==> !ys. a2 ==> .. ==> c  as  !xs ys .. a1 /\ a2 /\ .. ==> c, *)
(* for at least two antecedents (else failure)                             *)
let kit_uncurry_rule th =
  let th1 = GEN_ALL th in
  let rec strip th avoid vs ants =
    let c = concl th in
    if is_forall c then
      let v = fst(dest_forall c) in
      let v' = if mem v avoid then variant avoid v else v in
      strip (SPEC v' th) (v'::avoid) (vs @ [v']) ants
    else if is_imp c then strip (UNDISCH th) avoid vs (ants @ [fst(dest_imp c)])
    else th,vs,ants in
  let thc,vs,ants = strip th1 (thm_frees th1) [] [] in
  if length ants < 2 then failwith "kit_uncurry_rule" else
  let ant = list_mk_conj ants in
  let parts = kit_conj_split_n (length ants) (ASSUME ant) in
  GENL vs (DISCH ant (itlist PROVE_HYP parts thc));;

let IRULE th : tactic = fun g ->
  try kit_irule_plain th g with Failure _ as e ->
  match (try Some (kit_uncurry_rule th) with Failure _ -> None) with
    None -> raise e
  | Some th' -> (try let r = kit_irule_plain th' g in kit_note "IRULE curried"; r
                 with Failure _ -> raise e);;

(* imp_res_tac: resolve the antecedents of th with every assumption, as far *)
(* as they go; add every result (stripped)                                   *)

let IMP_RES_THEN (ttac:thm_tactic) th : tactic =
  fun (asl,w as gl) ->
    let asms = map snd asl in
    let rec resolve th =
      if not (is_imp(snd(strip_forall(concl th)))) then [th] else
      let mp = MATCH_MP_CURRIED th in
      let rs = mapfilter mp asms in
      if rs = [] then [th] else flat (map resolve rs) in
    let th' = IMP_CURRY_RULE (GEN_ALL th) in
    let mp = MATCH_MP_CURRIED th' in
    let first = mapfilter mp asms in
    if first = [] then failwith "IMP_RES_THEN: no match" else
    let results = flat (map resolve first) in
    EVERY (map ttac results) gl;;

(* a conjunction of implications (under quantifiers) is resolved conjunct by *)
(* conjunct, as HOL4's imp_res_tac (RES_CANON) does; since 2026-11-18       *)

let IMP_RES_TAC th : tactic =
  fun gl -> try IMP_RES_THEN CAKE_ASSUME_TAC th gl
            with Failure _ ->
              let cs = try map GEN_ALL (CONJUNCTS (SPEC_ALL (GEN_ALL th)))
                       with Failure _ -> [] in
              if length cs < 2 then ALL_TAC gl else
              let ok = filter (fun c -> is_imp(snd(strip_forall(concl c)))) cs in
              let tacs = map (fun c g -> try IMP_RES_THEN CAKE_ASSUME_TAC c g
                                         with Failure _ -> ALL_TAC g) ok in
              let res = EVERY tacs gl in
              (match res with
                 (_,[g'],_) when g' = gl -> ()
               | _ -> kit_note "IMP_RES_TAC conjunction");
              res;;

(* res_tac: every implicational assumption against the others *)

let RES_TAC : tactic =
  fun (asl,w as gl) ->
    let imps = filter (fun th -> is_imp(snd(strip_forall(concl th))))
                      (map snd asl) in
    (EVERY (map IMP_RES_TAC imps)) gl;;

(* FULL_RES_TAC: RES_TAC (HOL4's res_tac, one round), then, while a round   *)
(* added a fact that is new (not an assumption already, up to alpha),       *)
(* another round that adds only new facts, at most kit_res_rounds rounds in *)
(* all: chains a ==> b, b ==> c need no second RES_TAC.  (RES_TAC itself is *)
(* unchanged: more facts change the witnesses ASM_EXISTS_TAC picks after    *)
(* it.)  Since 2026-11-18.                                                   *)

let kit_res_rounds = ref 3;;

let kit_res_with (ttac:thm_tactic) : tactic =
  fun (asl,w as gl) ->
    let imps = filter (fun th -> is_imp(snd(strip_forall(concl th))))
                      (map snd asl) in
    EVERY (map (fun th g -> try IMP_RES_THEN ttac th g with Failure _ -> ALL_TAC g)
               imps) gl;;

let kit_assume_new th : tactic = fun (asl,w as g) ->
  if exists (fun (_,a) -> aconv (concl a) (concl th)) asl then ALL_TAC g
  else CAKE_ASSUME_TAC th g;;

let kit_full_res_old : tactic =
  let rec rounds k old : tactic = fun (asl,w as gl) ->
    let is_new (_,th) = not (exists (fun (_,a) -> aconv (concl a) (concl th)) old) in
    if k <= 1 || not (exists is_new asl) then ALL_TAC gl
    else (kit_res_with kit_assume_new THEN rounds (k-1) asl) gl in
  fun (asl,w as gl) -> (RES_TAC THEN rounds !kit_res_rounds asl) gl;;

(* Since 2026-11-20 FULL_RES_TAC goes on to a fixpoint (at most            *)
(* kit_res_max_rounds rounds), every round adding only new facts, and the  *)
(* one-point rule is applied to each new fact first (!x. x = t ==> P x     *)
(* becomes P t, ?x. x = t /\ P x becomes P t), so that a resolvent such as *)
(* !v. v = f a ==> Q v is used at once (check mode: KITDIFF where the goals *)
(* differ from the old FULL_RES_TAC's, and those).                          *)

let kit_res_max_rounds = ref 10;;

let kit_one_point_rule (th:thm) : thm =
  try CONV_RULE (CHANGED_CONV (TOP_DEPTH_CONV
         (CHANGED_CONV FORALL_UNWIND_CONV ORELSEC CHANGED_CONV UNWIND_CONV))) th
  with Failure _ -> th;;

let kit_full_res_new : tactic =
  let rec rounds k old : tactic = fun (asl,w as gl) ->
    let is_new (_,th) = not (exists (fun (_,a) -> aconv (concl a) (concl th)) old) in
    if k <= 0 || not (exists is_new asl) then ALL_TAC gl
    else (kit_res_with (fun th -> kit_assume_new (kit_one_point_rule th)) THEN
          rounds (k-1) asl) gl in
  fun gl -> rounds !kit_res_max_rounds [] gl;;

let kit_same_goalstate ((_,gs1,_):goalstate) ((_,gs2,_):goalstate) =
  length gs1 = length gs2 &&
  forall2 (fun (a1,w1) (a2,w2) ->
             aconv w1 w2 && length a1 = length a2 &&
             forall2 (fun (_,x) (_,y) -> aconv (concl x) (concl y)) a1 a2) gs1 gs2;;

let FULL_RES_TAC : tactic = fun gl ->
  if !kit_check then
    kit_check_both "FULL_RES_TAC fixpoint" kit_same_goalstate
      (fun () -> kit_full_res_old gl) (fun () -> kit_full_res_new gl)
  else kit_full_res_new gl;;

(* ------------------------------------------------------------------------- *)
(* pairarg_tac: a pair_CASE e (\a b. ...) with e not a pair becomes          *)
(* e = (a,b) in the assumptions, the goal and assumptions rewritten.        *)
(* ------------------------------------------------------------------------- *)

let PAIRARG_TAC : tactic =
  fun (asl,w as gl) ->
    let whole = list_mk_conj(w :: map (concl o snd) asl) in
    let is_cand t =
      is_case_app t &&
      (let c,x,fs = dest_case_app t in
       fst(dest_const c) = "pair_CASE" && not (is_pair x) &&
       free_in x whole) in
    let t = find_term is_cand whole in
    let _,x,fs = dest_case_app t in
    let f = hd fs in
    let tya,tyb = match dest_type(type_of x) with
        "prod",[a;b] -> a,b | _ -> failwith "PAIRARG_TAC" in
    let n1,n2 =
      try let a,b = dest_abs f in let b1,_ = dest_abs b in
          fst(dest_var a),fst(dest_var b1)
      with Failure _ -> "p1","p2" in
    (* also the variables free only in the hypotheses of an assumption      *)
    (* theorem (a variable eliminated by SUBS stays there): CHOOSE fails     *)
    (* in the justification if one of them is chosen                         *)
    let avoid = itlist (union o thm_frees o snd) asl (frees whole) in
    let v1 = kit_fresh_var avoid (mk_var(n1,tya)) in
    let v2 = kit_fresh_var (v1::avoid) (mk_var(n2,tyb)) in
    let nch = ISPEC x (nchotomy_of_type (type_of x)) in
    (MP_TAC nch THEN
     DISCH_THEN(X_CHOOSE_THEN v1 (X_CHOOSE_THEN v2
       (fun th -> if is_var x then CAKE_SUBST_ALL_TAC th
                  else CAKE_SUBST_ALL_TAC th THEN ASSUME_TAC th))) THEN
     CASE_ASM_TIDY_TAC THEN CASE_REWRITE_TAC[]) gl;;

(* ------------------------------------------------------------------------- *)
(* Induct_on: structural induction on a free variable; assumptions about it  *)
(* are moved into the goal first.                                            *)
(* ------------------------------------------------------------------------- *)

let cake_induction_thms = ref ([] : (string * thm) list);;

let induction_thm_of_type ty =
  let n = fst(dest_type ty) in
  try assoc n (!cake_induction_thms) with Failure _ ->
  match n with
    "num" -> num_INDUCTION
  | "list" -> list_INDUCT
  | "option" -> option_INDUCT
  | "sum" -> sum_INDUCT
  | _ -> let _,ith,_ = assoc n (!inductive_type_store) in ith;;

let INDUCT_ON (x:term) : tactic =
  fun (asl,w as gl) ->
    (REPEAT (FIRST_X_ASSUM (fun th ->
       if free_in x (concl th) then MP_TAC th else failwith "keep")) THEN
     SPEC_TAC(x,x) THEN
     MATCH_MP_TAC (induction_thm_of_type (type_of x)) THEN
     REPEAT CONJ_TAC) gl;;

(* ------------------------------------------------------------------------- *)
(* HOL Light's Metis builds terms whose types it lets HOL invent (variables  *)
(* __x ...), which type_invention_error := true (set by the prelude) turns   *)
(* into errors: run it with the flag off.                                     *)
(* ------------------------------------------------------------------------- *)

let with_type_invention f x =
  let old = !type_invention_error in
  type_invention_error := false;
  try let r = f x in type_invention_error := old; r
  with e -> (type_invention_error := old; raise e);;

(* the same, also without the warning: for the patterns of the q-tactics, *)
(* whose type variables are found by matching (HOL4's q-tactics parse with  *)
(* its warnings off too); since 2026-11-20                                  *)
let with_quiet_type_invention f x =
  let old_e = !type_invention_error and old_w = !type_invention_warning in
  type_invention_error := false; type_invention_warning := false;
  let restore () = type_invention_error := old_e; type_invention_warning := old_w in
  try let r = f x in restore (); r with e -> (restore (); raise e);;

let METIS_TAC thl : tactic =
  fun g -> with_type_invention (fun g -> METIS_TAC thl g) g;;

let ASM_METIS_TAC thl : tactic =
  fun g -> with_type_invention (fun g -> ASM_METIS_TAC thl g) g;;

let METIS thl tm = with_type_invention (METIS thl) tm;;

(* HOL4's CCONTR_TAC: assume the negation of the goal, prove F *)

let CCONTR_TAC : tactic = REFUTE_THEN ASSUME_TAC;;

(* ------------------------------------------------------------------------- *)
(* Existential goals: witnesses from the assumptions (HOL4 asm_exists_tac)   *)
(* and from an implication (HOL4 irule_at); suffices (HOL4 suff_tac).        *)
(* ------------------------------------------------------------------------- *)

(* |- (?vs. b) <=> (?vs'. b), for vs' a permutation of the variables vs *)

let EXISTS_PERM_CONV (vs':term list) (tm:term) : thm =
  let vs,bod = strip_exists tm in
  if length vs' <> length vs || not (set_eq vs vs') then failwith "EXISTS_PERM_CONV" else
  let tm' = list_mk_exists(vs',bod) in
  let one a b =
    let thb = itlist (fun v th -> EXISTS (mk_exists(v,concl th),v) th)
                     (fst(strip_exists b)) (ASSUME bod) in
    let rec chooses a th =
      if is_exists a then
        let v,inner = dest_exists a in CHOOSE (v,ASSUME a) (chooses inner th)
      else th in
    DISCH a (chooses a thb) in
  IMP_ANTISYM_RULE (one tm tm') (one tm' tm);;

(* names of the variables vs, renamed apart from avoid (and each other) *)

let kit_variants (avoid:term list) (vs:term list) =
  rev (itlist (fun v acc -> variant (acc @ avoid) v :: acc) (rev vs) []);;

(* every free variable of a goal: conclusion, assumptions and their hypotheses *)

let kit_goal_frees ((asl,w):goal) =
  itlist (fun (_,th) acc -> union (freesl (concl th :: hyp th)) acc) asl (frees w);;

(* |- ?vs. b from |- b[vals/vs] (vals: one value per variable of vs, in order) *)

let kit_exists_build (w:term) (vals:term list) (th:thm) : thm =
  let vs,b = strip_exists w in
  let rec build vs vals sofar =
    match vs,vals with
      [],[] -> []
    | v::vs',t::vals' ->
        let pat = vsubst sofar (list_mk_exists(v::vs',b)) in
        pat :: build vs' vals' ((t,v)::sofar)
    | _ -> failwith "kit_exists_build" in
  let pats = build vs vals [] in
  let th' = itlist2 (fun pat t th -> EXISTS (pat,t) th) pats vals th in
  EQ_MP (ALPHA (concl th') w) th';;

(* instantiate some existential variables of the goal (theta: value,var  *)
(* pairs; the values must not contain the goal's existential variables);  *)
(* the others stay existential, in their order                            *)

let EXISTS_INST_TAC (theta:(term * term) list) : tactic = fun (asl,w as g) ->
  let vs,_ = strip_exists w in
  let ins = filter (fun v -> exists (fun (_,x) -> x = v) theta) vs in
  if ins = [] then ALL_TAC g else
  let rest = subtract vs ins in
  (CONV_TAC (EXISTS_PERM_CONV (ins @ rest)) THEN
   MAP_EVERY (fun v -> EXISTS_TAC (rev_assoc v theta)) ins) g;;

(* drop the conjuncts of ?vs. c1 /\ ... /\ cn that are assumptions (and do  *)
(* not mention vs); T if nothing is left                                     *)

let kit_drop_asm_conjuncts_conv (facts:thm list) =
  let and_t = GEN_REWRITE_CONV I [AND_CLAUSES] in
  let rec conjs bvs tm =
    if is_conj tm then
      let l,r = dest_conj tm in
      let th = MK_COMB(AP_TERM (rator(rator tm)) (conjs bvs l),conjs bvs r) in
      let r' = rand(concl th) in
      if lhand r' = cake_true_tm || rand r' = cake_true_tm
      then TRANS th (and_t r') else th
    else if exists (fun v -> vfree_in v tm) bvs then REFL tm
    else try let f = find (fun f -> aconv (concl f) tm) facts in
             EQT_INTRO (EQ_MP (ALPHA (concl f) tm) f)
         with Failure _ -> REFL tm in
  let rec under bvs tm =
    if is_exists tm then
      let v,_ = dest_exists tm in
      let th = BINDER_CONV (under (v::bvs)) tm in
      let r = rand(concl th) in
      if is_exists r && snd(dest_exists r) = cake_true_tm
      then TRANS th (GEN_REWRITE_CONV I [EXISTS_SIMP] r) else th
    else conjs bvs tm in
  under [];;

let KIT_DROP_ASM_CONJUNCTS_TAC : tactic = fun (asl,w as g) ->
  let facts = flat (map (CONJUNCTS o snd) asl) in
  (CONV_TAC (CHANGED_CONV (kit_drop_asm_conjuncts_conv facts)) ORELSE ALL_TAC) g;;

(* ASM_EXISTS_TAC: for a goal ?x1 .. xn. c1 /\ ... /\ ck, choose witnesses  *)
(* by matching conjuncts with assumptions (HOL4 asm_exists_tac matches the  *)
(* first conjunct only); the choice that makes the most conjuncts           *)
(* assumptions is taken (a search over the conjuncts in order, the newest   *)
(* assumption first, of at most kit_exists_budget steps); the conjuncts    *)
(* that are then assumptions are dropped, the other variables stay          *)
(* existential.  Fails if no conjunct matches.                              *)

let kit_exists_budget = ref 2000;;

let kit_asm_witnesses (asl:(string * thm) list) (w:term) =
  let vs0,bod0 = strip_exists w in
  if vs0 = [] then failwith "ASM_EXISTS_TAC: not an existential goal" else
  (* the bound variables renamed apart from everything else *)
  let avoid = kit_goal_frees (asl,w) in
  let vs = kit_variants avoid vs0 in
  let bod = vsubst (zip vs vs0) bod0 in
  let cjs = conjuncts bod in
  let facts = map concl (flat (map (CONJUNCTS o snd) asl)) in
  let head t = try fst(strip_comb t) with Failure _ -> t in
  let same_head p f =
    let hp = head p and hf = head f in
    is_var hp || hp = hf in
  let extend theta c' rem f =
    let lconsts = subtract (frees c') rem in
    let _,ti,tyi = term_match lconsts c' f in
    if exists (fun (ty,v) -> ty <> v) tyi || exists (fun (_,v) -> not (mem v rem)) ti
    then failwith "extend" else ti @ theta in
  let score theta =
    itlist (fun c n ->
      let c' = vsubst theta c in
      if exists (fun v -> vfree_in v c') vs then n
      else if exists (aconv c') facts then n + 1 else n) cjs 0 in
  let ncj = length cjs in
  let best = ref (-1,[]) and budget = ref (!kit_exists_budget) in
  let rec dfs theta cs =
    if !budget <= 0 || fst !best >= ncj then () else
    (decr budget;
     match cs with
       [] -> let s = score theta in if s > fst !best then best := (s,theta)
     | c::rest ->
         let c' = vsubst theta c in
         let rem = filter (fun v -> vfree_in v c') vs in
         if rem = [] then dfs theta rest else
         (do_list (fun f ->
            if same_head c' f then
              match (try Some (extend theta c' rem f) with Failure _ -> None) with
                Some theta' -> dfs theta' rest
              | None -> ()) facts;
          dfs theta rest)) in
  dfs [] cjs;
  let theta = snd !best in
  if theta = [] then failwith "ASM_EXISTS_TAC: no conjunct matches an assumption" else
  (* back to the goal's own bound variables *)
  map (fun (t,v) -> t, assoc v (zip vs vs0)) theta;;

let ASM_EXISTS_TAC : tactic = fun (asl,w as g) ->
  let theta = kit_asm_witnesses asl w in
  (EXISTS_INST_TAC theta THEN KIT_DROP_ASM_CONJUNCTS_TAC) g;;

(* ------------------------------------------------------------------------- *)
(* IRULE_AT pos th (HOL4 irule_at): for a goal ?vs. c1 /\ ... /\ cn, unify   *)
(* the conclusion of th (!xs. a1 ==> ... ==> c, conjunctions in the         *)
(* antecedents curried) with the conjunct selected by pos, and replace it   *)
(* by th's antecedents; variables of vs instantiated by the unification     *)
(* disappear, variables of xs that are left become existential.  Positions  *)
(* as in HOL4: Any (the whole goal, as IRULE, else the first conjunct that  *)
(* unifies), Pos hd, Pos last, Pos (el n) (a function choosing a conjunct   *)
(* from the list), Pat `pattern` (the first conjunct the pattern matches),  *)
(* Concl (the whole goal: IRULE th).                                         *)
(* ------------------------------------------------------------------------- *)

type match_position = Any | Pos of (term list -> term) | Pat of term | Concl;;

(* the type variables of th that may be instantiated (those not in its      *)
(* hypotheses, e.g. those of a library theorem), renamed apart from the      *)
(* goal's; the type variables of the hypotheses (of an assumption) are fixed *)
let kit_fresh_tyvars (g:goal) (th:thm) =
  let gtys = itlist (fun v acc -> union (type_vars_in_term v) acc) (kit_goal_frees g)
                    (type_vars_in_term (snd g)) in
  let htys = itlist (union o type_vars_in_term) (hyp th) [] in
  let tys = subtract (type_vars_in_term (concl th)) htys in
  let bad = intersect tys gtys in
  if bad = [] then th else
  INST_TYPE (map (fun ty -> mk_vartype("?kit_" ^ dest_vartype ty), ty) bad) th;;

(* the parts of th: its universally quantified variables (renamed apart    *)
(* from avoid), the theorem with them free and the antecedents undischarged *)
(* (hypotheses), the antecedents in order, the conclusion                   *)
let kit_rule_parts (avoid:term list) (th:thm) =
  let rec strip th xs ants =
    let c = concl th in
    if is_forall c then
      let v,_ = dest_forall c in
      let v' = variant (avoid @ xs @ freesl (concl th :: hyp th)) v in
      strip (SPEC v' th) (xs @ [v']) ants
    else if is_imp c then
      let a,_ = dest_imp c in
      if is_conj a then strip (CONV_RULE (REWR_CONV (GSYM IMP_IMP)) th) xs ants
      else strip (UNDISCH th) xs (ants @ [a])
    else th,xs,ants in
  strip th [] [];;

(* unification of the types and then the terms (variables vars instantiable) *)
let kit_unify (vars:term list) (fixed_tys:hol_type list) (t1:term) (t2:term) =
  let rec tyu t1 t2 tyi =
    match t1,t2 with
      Var(_,ty1),_ when mem t1 vars -> type_unify ty1 (type_of t2) tyi
    | _,Var(_,ty2) when mem t2 vars -> type_unify (type_of t1) ty2 tyi
    | Comb(f1,x1),Comb(f2,x2) -> tyu f1 f2 (tyu x1 x2 tyi)
    | Abs(v1,b1),Abs(v2,b2) -> tyu b1 b2 (type_unify (type_of v1) (type_of v2) tyi)
    | Const(n1,ty1),Const(n2,ty2) -> if n1 = n2 then type_unify ty1 ty2 tyi
                                     else failwith "kit_unify"
    | Var(n1,ty1),Var(n2,ty2) -> if n1 = n2 then type_unify ty1 ty2 tyi
                                 else failwith "kit_unify"
    | _ -> failwith "kit_unify" in
  let tyi = tyu t1 t2 [] in
  let tyi = map (fun (ty,v) -> type_subst tyi ty,v) tyi in
  if exists (fun (ty,v) -> mem v fixed_tys && ty <> v) tyi then failwith "kit_unify: type" else
  let vars' = map (inst tyi) vars in
  let t1' = inst tyi t1 and t2' = inst tyi t2 in
  let _,ti,_ = term_unify vars' t1' t2' in
  let s1 = vsubst ti t1' and s2 = vsubst ti t2' in
  if not (aconv s1 s2) then failwith "kit_unify: no unifier" else
  tyi,ti;;

let rec kit_conj_leaves tm =
  if is_conj tm then kit_conj_leaves (lhand tm) @ kit_conj_leaves (rand tm) else [tm];;

(* the n theorems of |- t1 /\ ... /\ tn (right nested, as list_mk_conj) *)
let rec kit_conj_split n th =
  if n <= 1 then [th] else CONJUNCT1 th :: kit_conj_split (n-1) (CONJUNCT2 th);;

(* rebuild a conjunction with the shape of tree from theorems for its leaves *)
let kit_rebuild_tree (tree:term) (ths:thm list) : thm =
  let rec go tm ths =
    if is_conj tm then
      let l,r = dest_conj tm in
      let lth,ths' = go l ths in
      let rth,ths'' = go r ths' in
      CONJ lth rth,ths''
    else match ths with th::rest -> th,rest | [] -> failwith "kit_rebuild_tree" in
  match go tree ths with th,[] -> th | _ -> failwith "kit_rebuild_tree";;

let rec kit_chooses (a:term) (th:thm) =
  if is_exists a then
    let v,inner = dest_exists a in CHOOSE (v,ASSUME a) (kit_chooses inner th)
  else th;;

let kit_irule_at (pos:match_position) (th0:thm) : tactic = fun (asl,w as g) ->
  let vs0,bod0 = strip_exists w in
  let avoid0 = kit_goal_frees g in
  let vs = kit_variants (avoid0 @ freesl (concl th0 :: hyp th0)) vs0 in
  let bod = vsubst (zip vs vs0) bod0 in
  let leaves = kit_conj_leaves bod in
  let n = length leaves in
  let th1 = kit_fresh_tyvars g th0 in
  let thf,xs,ants = kit_rule_parts (avoid0 @ vs) th1 in
  let c = concl thf in
  let fixed_tys = itlist (fun v acc -> union (type_vars_in_term v) acc) avoid0
                         (itlist (union o type_vars_in_term) (hyp th1)
                                 (type_vars_in_term w)) in
  let try_leaf i =
    let tyi,ti = kit_unify (vs @ xs) fixed_tys c (el i leaves) in i,tyi,ti in
  let i,tyi,ti =
    match pos with
      Any -> tryfind try_leaf (0--(n-1))
    | Pos f -> let l = f leaves in
               let i = try index l leaves with Failure _ -> failwith "IRULE_AT: Pos" in
               try_leaf i
    | Pat p -> let i = try index (find (fun l -> can (term_match [] p) l) leaves) leaves
                       with Failure _ -> failwith "IRULE_AT: Pat" in
               try_leaf i
    | Concl -> failwith "IRULE_AT: Concl" in
  (* the instantiated theorem: its hypotheses and the antecedents |- leaf i *)
  let thi = INST ti (INST_TYPE tyi thf) in
  let sub t = vsubst ti (inst tyi t) in
  let ants' = map sub ants and leaves' = map sub leaves in
  let xs' = map (inst tyi) xs in
  let bound v = exists (fun (_,x) -> x = v) ti in
  let before,rest = chop_list i leaves' in
  let after = tl rest in
  let new_leaves = before @ ants' @ after in
  let nb = if new_leaves = [] then cake_true_tm else list_mk_conj new_leaves in
  let ws = filter (fun v -> not (bound v) && vfree_in v nb) (vs @ xs') in
  let w' = list_mk_exists(ws,nb) in
  let vals = map (fun v -> try rev_assoc v ti with Failure _ -> v) vs in
  let wren = list_mk_exists(vs,bod) in
  let just thn =
    let lths = if new_leaves = [] then []
               else kit_conj_split (length new_leaves) (ASSUME nb) in
    let bths,rest = chop_list (length before) lths in
    let aths,aths' = chop_list (length ants') rest in
    let ci = itlist PROVE_HYP aths thi in
    let thbody = kit_rebuild_tree bod (bths @ [ci] @ aths') in
    let thw = kit_exists_build wren vals thbody in
    let thw' = PROVE_HYP thn (kit_chooses w' thw) in
    EQ_MP (ALPHA (concl thw') w) thw' in
  if nb = cake_true_tm then
    let thn = kit_exists_build w' ws TRUTH in
    (null_meta,[],fun _ _ -> just thn)
  else (null_meta,[asl,w'],fun _ thl -> just (hd thl));;

(* the free variables of th that are not free in its hypotheses can be     *)
(* instantiated too (GEN_ALL, as IRULE does), when the unification with     *)
(* them fixed fails (since 2026-11-18)                                       *)
let kit_irule_at_gen (pos:match_position) (th:thm) : tactic = fun g ->
  try kit_irule_at pos th g with Failure _ as e ->
  let th' = GEN_ALL th in
  if concl th' = concl th then raise e else
  try let r = kit_irule_at pos th' g in kit_note "IRULE_AT GEN_ALL"; r
  with Failure _ -> raise e;;

let IRULE_AT (pos:match_position) (th:thm) : tactic =
  match pos with
    Concl -> IRULE th
  | Any -> IRULE th ORELSE kit_irule_at_gen Any th
  | _ -> kit_irule_at_gen pos th;;

(* HOL4 drule_at pos th: as DRULE th, but the antecedent of th matched with *)
(* an assumption is chosen by pos: Any (the first antecedent, in order, that *)
(* matches an assumption, newest assumption first), Pos hd, Pos last,       *)
(* Pos (el n) (n from 0), Pat `p` (the first antecedent p matches) or Concl *)
(* (the first antecedent).  The other antecedents stay, in order (curried). *)
(* The antecedents are those of th with every quantifier and implication    *)
(* stripped and conjunctions curried, as for IRULE_AT.                       *)

let kit_drule_parts (th:thm) =
  let th1 = GEN_ALL th in
  kit_rule_parts (thm_frees th1) th1;;

(* !xs. a_i ==> a_1 ==> .. (without a_i) .. ==> c *)
let kit_ants_first (thf:thm) (xs:term list) (ants:term list) (i:int) =
  let ai = el i ants in
  let others = filter (fun a -> not (a == ai)) ants in
  let others = if length others = length ants - 1 then others
               else (let b,a = chop_list i ants in b @ tl a) in
  GENL xs (DISCH ai (itlist DISCH others thf));;

let DRULE_AT (pos:match_position) (th:thm) : tactic = fun (asl,w as g) ->
  let thf,xs,ants = kit_drule_parts th in
  let n = length ants in
  if n = 0 then failwith "DRULE_AT: not an implication" else
  let idxs =
    match pos with
      Any -> 0--(n-1)
    | Concl -> [0]
    | Pos f -> let a = f ants in
               (try [index a ants] with Failure _ -> failwith "DRULE_AT: Pos")
    | Pat p -> (try [index (find (fun a -> can (term_match [] p) a) ants) ants]
                with Failure _ -> failwith "DRULE_AT: Pat") in
  let rules = map (fun i -> MATCH_MP (kit_ants_first thf xs ants i)) idxs in
  let try_asm (_,a) = tryfind (fun mp -> mp a) rules in
  MP_TAC (tryfind try_asm asl) g;;

(* ------------------------------------------------------------------------- *)
(* HOL4 recInduct ind: induction with a theorem !P. hyps ==> !x1 .. xn.     *)
(* P x1 .. xn, or one whose predicate takes a tuple, !P. hyps ==>            *)
(* !x1 .. xn. P (x1,..,xn) (an induction theorem of a function of a tuple), *)
(* or !P. hyps ==> !x. P x with x of a product type.  The goal must be      *)
(* !x1 .. xn y1 .. ym. t, with x1 .. xn of the types of P's arguments (of   *)
(* the components of x); P is instantiated to \x1 .. xn. !y1 .. ym. t      *)
(* (paired for a tuple) and the theorem is used with MATCH_MP_TAC.           *)
(* ------------------------------------------------------------------------- *)

let REC_IND_TAC (ind:thm) : tactic = fun (asl,w as g) ->
  let p,body = dest_forall (concl ind) in
  let cvs,papp = strip_forall (snd (dest_imp body)) in
  let pargs = snd (strip_comb papp) in
  let rec comps ty = match ty with
      Tyapp("prod",[a;b]) -> a :: comps b
    | _ -> [ty] in
  let vs,b = strip_forall w in
  if vs = [] then failwith "REC_IND_TAC: the goal is not universally quantified" else
  (* tupled: P takes one tuple; k: the number of goal variables it takes; *)
  (* split: !x. P x with x of a product type, the goal having components *)
  let tupled,k,split =
    match cvs,pargs with
      [v],[a] when a = v && length (comps (type_of v)) > 1 &&
                   type_of (hd vs) <> type_of v ->
        true,length (comps (type_of v)),true
    | _,[a] when length cvs > 1 -> true,length cvs,false
    | _ -> false,length cvs,false in
  if length vs < k then failwith "REC_IND_TAC: too few quantifiers in the goal" else
  let xs,ys = chop_list k vs in
  let inner = list_mk_forall(ys,b) in
  let pinst = if tupled then mk_gabs(end_itlist (curry mk_pair) xs,inner)
              else list_mk_abs(xs,inner) in
  let ith = ISPEC pinst ind in
  let rec split_n n tm =
    if n <= 1 then REFL tm
    else (REWR_CONV FORALL_PAIR_THM THENC BINDER_CONV (split_n (n-1))) tm in
  let ith = if split then CONV_RULE (RAND_CONV (split_n k)) ith else ith in
  (MP_TAC ith THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
   DISCH_THEN MATCH_MP_TAC) g;;

(* ------------------------------------------------------------------------- *)
(* HOL4 PairCases_on `x`: a variable x of a product type A1 # .. # An is     *)
(* replaced everywhere by a tuple (x0,..,x(n-1)) of new variables.           *)
(* ------------------------------------------------------------------------- *)

let PAIR_CASES_ON (x:term) : tactic = fun (asl,w as g) ->
  if not (is_var x) then failwith "PAIR_CASES_ON: not a variable" else
  let n,ty = dest_var x in
  let rec comps ty = match ty with
      Tyapp("prod",[a;b]) -> a :: comps b
    | _ -> [ty] in
  let tys = comps ty in
  if length tys < 2 then failwith "PAIR_CASES_ON: not of a product type" else
  let avoid = itlist (union o thm_frees o snd) asl (frees w) in
  let rec fresh av l i =
    match l with
      [] -> []
    | t::rest -> let v = kit_fresh_var av (mk_var(n ^ string_of_int i,t)) in
                 v :: fresh (v::av) rest (i+1) in
  let vs = fresh avoid tys 0 in
  let tup = end_itlist (curry mk_pair) vs in
  let rec projs t l =
    match l with
      [_] -> [t]
    | _::rest -> mk_icomb(mk_const("FST",[]),t) ::
                 projs (mk_icomb(mk_const("SND",[]),t)) rest
    | [] -> [] in
  let eth = prove(list_mk_exists(vs,mk_eq(x,tup)),
                  MAP_EVERY EXISTS_TAC (projs x vs) THEN REWRITE_TAC[PAIR]) in
  (MP_TAC eth THEN
   MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC)) vs THEN
   DISCH_THEN(fun th -> CAKE_SUBST_ALL_TAC th)) g;;


(* HOL4 suff_tac t: show t ==> goal (first) and t (second) *)

let SUFF_TAC (t:term) : tactic = fun (asl,w) ->
  (null_meta,[asl,mk_imp(t,w); asl,t],
   fun i thl -> match thl with
                  [th1;th2] -> MP th1 th2
                | _ -> failwith "SUFF_TAC: justification");;

(* ------------------------------------------------------------------------- *)
(* Renaming by patterns (HOL4 rename1, rename, qmatch_asmsub_rename_tac,     *)
(* qmatch_goalsub_rename_tac).  The pattern is a string, parsed when the    *)
(* tactic runs, with the types of the goal's free variables (as HOL4 parses *)
(* its quotations in the goal's context); other types are found by matching. *)
(* Each _ is its own wildcard, and variables whose names start with _ are    *)
(* matched but not renamed.  A pattern variable that is matched to a goal    *)
(* variable renames it; matched to a bigger term, it replaces that term      *)
(* everywhere (generalising it, as in HOL4).                                 *)
(*   RENAME1 "pat"    HOL4 rename1: variables of pat that are free in the   *)
(*                    goal stand for themselves; the first match of pat in  *)
(*                    the goal, a whole assumption, a subterm of the goal,  *)
(*                    a subterm of an assumption (newest first) is used.    *)
(*   RENAME_TAC ["p1"; ...]  HOL4 rename: every variable of the patterns is *)
(*                    a new name (an old variable of that name is renamed   *)
(*                    apart); the patterns are matched in turn, with        *)
(*                    backtracking.                                         *)
(*   MATCH_ASMSUB_RENAME_TAC "pat", MATCH_GOALSUB_RENAME_TAC "pat"  as      *)
(*                    RENAME1, matching only subterms of the assumptions or *)
(*                    of the goal.                                          *)
(*   QEXISTS_TAC "t", QSUFF_TAC "t"  HOL4 qexists_tac, qsuff_tac: EXISTS_TAC *)
(*                    and SUFF_TAC with the term parsed in the goal context. *)
(* ------------------------------------------------------------------------- *)

(* parse s with the free variables vars typed (other types invented) *)
let kit_parse_in (vars:term list) (s:string) : term =
  let venv = map (fun v -> let n,ty = dest_var v in n,pretype_of_type ty) vars in
  let ptm,l = (parse_preterm o flat o map cake_wild_tokens o lex o explode) s in
  if l <> [] then failwith "RENAME: unparsed input in pattern" else
  with_quiet_type_invention (fun p -> cake_preterm_to_term s venv p) ptm;;

(* parse s with the free variables vars typed, as a term of type ty *)
let kit_parse_typed (vars:term list) (ty:hol_type) (s:string) : term =
  let venv = map (fun v -> let n,t = dest_var v in n,pretype_of_type t) vars in
  let ptm,l = (parse_preterm o flat o map cake_wild_tokens o lex o explode) s in
  if l <> [] then failwith "unparsed input" else
  cake_preterm_to_term s venv (Typing(ptm,pretype_of_type ty));;

(* HOL4 qexists_tac and qsuff_tac: the term is a string parsed in the goal's *)
(* context (its free variables have the goal's types, the witness the type  *)
(* of the existential variable), so it needs no type annotations            *)
let QEXISTS_TAC (s:string) : tactic = fun (asl,w as g) ->
  let v,_ = try dest_exists w with Failure _ -> failwith "QEXISTS_TAC: not an existential" in
  EXISTS_TAC (kit_parse_typed (kit_goal_frees g) (type_of v) s) g;;

let QSUFF_TAC (s:string) : tactic = fun g ->
  SUFF_TAC (kit_parse_typed (kit_goal_frees g) bool_ty s) g;;

(* HOL4 qpat_x_assum and qpat_assum: the first assumption (newest first)    *)
(* that the pattern matches is given to the theorem-tactic (QPAT_X_ASSUM    *)
(* removes it first); the pattern is a string parsed in the goal context,   *)
(* its variables that are free in the goal stand for themselves, the others *)
(* match anything, each _ is a wildcard, e.g. QPAT_X_ASSUM "f _ = _" MP_TAC. *)
(* HOL4 qspec_then and qspecl_then: SPEC with the terms parsed              *)
(* in the goal context, typed by the bound variables (ISPEC if their types  *)
(* have type variables): FIRST_X_ASSUM (QSPEC_THEN "ck" MP_TAC).            *)

let kit_qpat (s:string) (g:goal) =
  let fr = kit_goal_frees g in
  let pat = kit_parse_in fr s in
  pat, intersect (frees pat) fr;;

let kit_qpat_find (s:string) ((asl,w) as g:goal) =
  let pat,fixed = kit_qpat s g in
  let ok th = can (term_match fixed pat) (concl th) in
  let rec split acc l =
    match l with
      [] -> failwith ("QPAT: no assumption matches " ^ s)
    | (_,th as a)::rest -> if ok th then th,List.rev_append acc rest else split (a::acc) rest in
  split [] asl;;

let QPAT_X_ASSUM (s:string) (ttac:thm_tactic) : tactic = fun (asl,w as g) ->
  let th,asl' = kit_qpat_find s g in ttac th (asl',w);;

let QPAT_ASSUM (s:string) (ttac:thm_tactic) : tactic = fun g ->
  let th,_ = kit_qpat_find s g in ttac th g;;

(* for a bound variable with type variables, the term is parsed alone and  *)
(* ISPEC'd; if that invents type variables (QSPEC_THEN "[]" on !l:A list),  *)
(* it is parsed as a term of the variable's type first (since 2026-11-18)  *)
let kit_invented_tyvars (t:term) =
  exists (fun ty -> let n = dest_vartype ty in String.length n > 0 && n.[0] = '?')
         (type_vars_in_term t);;

let QSPEC_THEN (s:string) (ttac:thm_tactic) (th:thm) : tactic = fun g ->
  let v,_ = try dest_forall (concl th) with Failure _ -> failwith "QSPEC_THEN: not universal" in
  let fr = kit_goal_frees g in
  if type_vars_in_term v = [] then ttac (SPEC (kit_parse_typed fr (type_of v) s) th) g
  else
    let t = kit_parse_in fr s in
    if not (kit_invented_tyvars t) then ttac (ISPEC t th) g else
    match (try Some (kit_parse_typed fr (type_of v) s) with Failure _ -> None) with
      Some t' -> (try let r = ttac (SPEC t' th) g in kit_note "QSPEC_THEN typed"; r
                  with Failure _ -> ttac (ISPEC t th) g)
    | None -> ttac (ISPEC t th) g;;

let QSPECL_THEN (sl:string list) (ttac:thm_tactic) (th:thm) : tactic =
  itlist (fun s k th -> QSPEC_THEN s k th) sl ttac th;;

(* HOL4 Cases_on `t`: CASES_ON with t parsed in the goal context, so that it *)
(* needs no annotation (QCASES_ON "res"); a type that cannot be inferred is *)
(* an error, as for any term                                                 *)
let QCASES_ON (s:string) : tactic = fun g ->
  let fr = kit_goal_frees g in
  let venv = map (fun v -> let n,t = dest_var v in n,pretype_of_type t) fr in
  let ptm,l = (parse_preterm o flat o map cake_wild_tokens o lex o explode) s in
  if l <> [] then failwith "QCASES_ON: unparsed input" else
  CASES_ON (cake_preterm_to_term s venv ptm) g;;

(* HOL4 last_assum, last_x_assum: FIRST_ASSUM and FIRST_X_ASSUM from the    *)
(* oldest assumption (often an induction hypothesis) to the newest           *)
let LAST_ASSUM (ttac:thm_tactic) : tactic = fun (asl,w as g) ->
  tryfind (fun (_,th) -> ttac th g) (rev asl);;

let LAST_X_ASSUM (ttac:thm_tactic) : tactic = fun (asl,w) ->
  tryfind (fun i -> let before,rest = chop_list i asl in
                    ttac (snd (hd rest)) (before @ tl rest,w))
          (rev (0--(length asl - 1)));;

let kit_is_uscore v = let n = fst(dest_var v) in String.length n > 0 && n.[0] = '_';;

(* the subterms of tm (pre-order) with the variables bound above them *)
let kit_subterms_ctx (tm:term) : (term * term list) list =
  let acc = ref [] in
  let rec go bvs t =
    acc := (t,bvs) :: !acc;
    match t with
      Comb(f,x) -> go bvs f; go bvs x
    | Abs(v,b) -> go (v::bvs) b
    | _ -> () in
  go [] tm; rev !acc;;

(* match pat (variables fixed are constants) against tm: the bindings of the *)
(* pattern variables that are not wildcards, type-instantiated              *)
let kit_rename_match (fixed:term list) (pat:term) (bvs:term list) (tm:term) =
  let _,ti,tyi = term_match fixed pat tm in
  let ti = map (fun (t,v) -> t,inst tyi v) ti in
  if exists (fun (t,_) -> exists (fun b -> vfree_in b t) bvs) ti
  then failwith "kit_rename_match: bound variable" else
  filter (fun (t,v) -> not (kit_is_uscore v) && not (t = v)) ti;;

(* rename the free variable or replace the term r by the variable l, in the *)
(* goal and the assumptions (l must be new to the goal)                      *)
let kit_rename_one ((r:term),(l:term)) : tactic = fun g ->
  if r = l then ALL_TAC g else
  if mem l (kit_goal_frees g) then failwith "kit_rename_one: name in use" else
  let ex = EXISTS (mk_exists(l,mk_eq(r,l)),r) (REFL r) in
  X_CHOOSE_THEN l (fun th -> SUBST_ALL_TAC th) ex g;;

(* the renamings of a list of bindings (value r, name l): residues first to  *)
(* fresh variables (so that bindings cannot interfere), then other free     *)
(* variables with one of the names renamed apart, then to the names         *)
let kit_rename_bindings (binds:(term * term) list) : tactic = fun g ->
  let binds = filter (fun (r,l) -> not (r = l)) binds in
  if binds = [] then ALL_TAC g else
  let gs = map (fun (r,l) -> genvar (type_of l)) binds in
  let step1 = MAP_EVERY kit_rename_one (zip (map fst binds) gs) in
  let step2 = fun g ->
    let fr = kit_goal_frees g in
    let clash = filter (fun (_,l) -> mem l fr) binds in
    let avoid = ref (fr @ map snd binds) in
    MAP_EVERY (fun (_,l) ->
        let l' = variant !avoid l in avoid := l' :: !avoid; kit_rename_one (l,l'))
      clash g in
  let step3 = MAP_EVERY kit_rename_one (zip gs (map snd binds)) in
  (step1 THEN step2 THEN step3) g;;

(* the places to match, in HOL4's order: g (the goal), a (an assumption),   *)
(* sg and sa (their strict subterms), sg0 and sa0 (all their subterms)     *)
let kit_rename_places (sel:string list) ((asl,w):goal) =
  let asms = map (concl o snd) asl in
  let whole_g = if mem "g" sel then [w,[]] else []
  and whole_a = if mem "a" sel then map (fun a -> a,[]) asms else []
  and sub_g = if mem "sg" sel then tl (kit_subterms_ctx w)
              else if mem "sg0" sel then kit_subterms_ctx w else []
  and sub_a = if mem "sa" sel then flat (map (fun a -> tl (kit_subterms_ctx a)) asms)
              else if mem "sa0" sel then flat (map kit_subterms_ctx asms) else [] in
  whole_g @ whole_a @ sub_g @ sub_a;;

(* the first place where pat matches and k succeeds after the renaming *)
let kit_rename_with (sel:string list) (allbind:bool) (s:string) (k:tactic) : tactic =
  fun (asl,w as g) ->
    let fr = kit_goal_frees g in
    let pat = kit_parse_in (if allbind then [] else fr) s in
    let fixed = if allbind then [] else intersect (frees pat) fr in
    let rec try_places ps =
      match ps with
        [] -> failwith ("RENAME: no match for " ^ s)
      | (t,bvs)::rest ->
          (match (try Some (kit_rename_match fixed pat bvs t) with Failure _ -> None) with
             None -> try_places rest
           | Some binds ->
               (try (kit_rename_bindings binds THEN k) g
                with Failure _ -> try_places rest)) in
    try_places (kit_rename_places sel g);;

let RENAME1 (s:string) : tactic = kit_rename_with ["g";"a";"sg";"sa"] false s ALL_TAC;;

let MATCH_ASMSUB_RENAME_TAC (s:string) : tactic = kit_rename_with ["sa0"] false s ALL_TAC;;

let MATCH_GOALSUB_RENAME_TAC (s:string) : tactic = kit_rename_with ["sg0"] false s ALL_TAC;;

let RENAME_TAC (sl:string list) : tactic =
  itlist (fun s k -> kit_rename_with ["g";"a";"sg";"sa"] true s k) sl ALL_TAC;;

(* ========================================================================= *)
(* More HOL4 tactics (since 2026-11-20).                                     *)
(*                                                                           *)
(*   QREFINE_TAC "t"        qrefine: witness t with new existentials.        *)
(*   QREFINEL_TAC ["t";"_"] qrefinel: several witnesses, _ keeps one.        *)
(*   DEP_REWRITE_TAC thl    dep_rewrite: conditional rewrites, antecedents   *)
(*                          as new conjuncts; DEP_ONCE_REWRITE_TAC, and the  *)
(*                          PURE_ versions.                                  *)
(*   MATCH_GOALSUB_ABBREV_TAC "pat"  qmatch_goalsub_abbrev_tac;              *)
(*   MATCH_ASMSUB_ABBREV_TAC "pat"   qmatch_asmsub_abbrev_tac.               *)
(*   QBY "t" tac            `t` by tac; QSUFFICES_BY "t" tac (suffices_by);  *)
(*                          QSUBGOAL "t" (sg).                               *)
(*   NAMED_CASES_ON "t" ["a b";"c"]  namedCases_on.                          *)
(*   QINDUCT_ON "x"         Induct_on `x`, x free or bound in the goal.      *)
(* ========================================================================= *)

(* the free variables of tm, in the order of their first occurrence *)
let kit_frees_lr (tm:term) : term list =
  let rec go bvs t acc =
    match t with
      Var _ -> if mem t bvs || mem t acc then acc else t :: acc
    | Const _ -> acc
    | Comb(f,x) -> go bvs x (go bvs f acc)
    | Abs(v,b) -> go (v::bvs) b acc in
  rev (go [] tm []);;

(* ------------------------------------------------------------------------- *)
(* qrefine and qrefinel (HOL4 Q.REFINE_EXISTS_TAC, Q.LIST_REFINE_EXISTS_TAC) *)
(* ------------------------------------------------------------------------- *)

(* |- w from |- b[vals/vs], for w = ?v1 .. vk. b and vals of length k *)
let rec kit_exists_n (w:term) (vals:term list) (th:thm) : thm =
  match vals with
    [] -> EQ_MP (ALPHA (concl th) w) th
  | t::rest -> let v,b = dest_exists w in
               EXISTS (w,t) (kit_exists_n (vsubst [t,v] b) rest th);;

(* a |- c to (?v1 .. vn. a') |- c, for a = ?v1 .. vn. a' (the vi not free  *)
(* in c or other hypotheses)                                                *)
let rec kit_choose_list (vs:term list) (a:term) (th:thm) : thm =
  match vs with
    [] -> th
  | v::rest -> let v',inner = dest_exists a in
               let inner' = if v' = v then inner else vsubst [v,v'] inner in
               CHOOSE (v,ASSUME a) (kit_choose_list rest inner' th);;

(* the goal ?v1 .. vk. b with the values vals for v1 .. vk (a value may be   *)
(* the variable itself), as the goal ?ws. b[vals/vs]                       *)
let kit_refine (vals:term list) (ws:term list) : tactic = fun (asl,w) ->
  let rec strip n tm acc =
    if n = 0 then rev acc,tm else
    let v,b = try dest_exists tm with Failure _ -> failwith "QREFINE: too few existentials" in
    strip (n-1) b (v::acc) in
  let vs,b = strip (length vals) w [] in
  let b' = vsubst (zip vals vs) b in
  let w' = list_mk_exists(ws,b') in
  let th = kit_choose_list ws w' (kit_exists_n w vals (ASSUME b')) in
  (null_meta,[asl,w'],fun _ thl -> PROVE_HYP (hd thl) th);;

(* HOL4 qrefine `t`: for a goal ?x. P x, the witness t is parsed in the      *)
(* goal's context with the type of x; its free variables that are not free  *)
(* in the goal become existential: ?v1 .. vn. P t (vi in order of           *)
(* occurrence), e.g. QREFINE_TAC "ck + n" on ?ck. evaluate .. ck .. .        *)
let QREFINE_TAC (s:string) : tactic = fun (asl,w as g) ->
  let v,_ = try dest_exists w with Failure _ -> failwith "QREFINE_TAC: not an existential" in
  let fr = kit_goal_frees g in
  let t = kit_parse_typed fr (type_of v) s in
  let ws = filter (fun x -> not (mem x fr)) (kit_frees_lr t) in
  kit_refine [t] ws g;;

(* HOL4 qrefinel [`t1`, `_`, ..]: witnesses for the first existential       *)
(* variables, each parsed in the goal's context and that of the new         *)
(* variables of the witnesses before it; "_" keeps the variable existential *)
(* (renamed apart from the new variables); the goal is then ?ws vs'. b with *)
(* ws the new variables (in order) and vs' the kept ones.                   *)
let QREFINEL_TAC (sl:string list) : tactic = fun (asl,w as g) ->
  let fr = kit_goal_frees g in
  let rec strip n tm acc =
    if n = 0 then rev acc else
    let v,b = try dest_exists tm with Failure _ -> failwith "QREFINEL_TAC: too many witnesses" in
    strip (n-1) b (v::acc) in
  let vs = strip (length sl) w [] in
  let rec go pairs news vals =
    match pairs with
      [] -> rev news,rev vals
    | (s,v)::rest ->
        if String.trim s = "_" then go rest news ((None,v)::vals) else
        let t = kit_parse_typed (fr @ news) (type_of v) s in
        let nw = filter (fun x -> not (mem x fr) && not (mem x news)) (kit_frees_lr t) in
        go rest (rev nw @ news) ((Some t,v)::vals) in
  let news,vals = go (zip sl vs) [] [] in
  (* kept variables, renamed apart from the goal and the new variables *)
  let avoid = ref (fr @ news) in
  let vals' = map (fun (wo,v) ->
      match wo with
        Some t -> t,None
      | None -> let v' = kit_primed_var !avoid v in avoid := v' :: !avoid; v',Some v') vals in
  let kept = mapfilter (fun (_,k) -> match k with Some v -> v | None -> fail()) vals' in
  kit_refine (map fst vals') (news @ kept) g;;

(* ------------------------------------------------------------------------- *)
(* HOL4 dep_rewrite (Homeier): DEP_PURE_ONCE_REWRITE_TAC thl uses each       *)
(* theorem of thl (each conjunct) once, in order: !xs. a1 ==> .. ==> l = r   *)
(* (conjunctive antecedents curried; a conclusion ~p is p = F, other ones p *)
(* are p = T) is matched with the first subterm of the goal (top down, left *)
(* to right) that it matches with antecedents free of variables bound above *)
(* the subterm; the goal is rewritten once (PURE_ONCE_REWRITE_CONV) with    *)
(* the instance and its antecedents are collected; then the goal is         *)
(* a1' /\ .. /\ an' /\ goal' (the antecedents without duplicates and T).    *)
(* DEP_ONCE_REWRITE_TAC thl is that THEN REWRITE_TAC[].  DEP_PURE_REWRITE_TAC *)
(* and DEP_REWRITE_TAC rewrite with each instance to a fixpoint             *)
(* (PURE_REWRITE_CONV, REWRITE_CONV), use the theorems again until nothing   *)
(* changes, and then again on the new goal with its antecedent conjuncts     *)
(* (at most kit_dep_max_steps instances in all).                             *)
(* ------------------------------------------------------------------------- *)

let kit_dep_max_steps = ref 200;;

(* the rules of a theorem: (number of antecedents, a1 ==> .. ==> l = r with *)
(* the variables free, the variables that th quantifies, renamed apart from *)
(* avoid, the variables of the goal); th's own free variables are           *)
(* instantiated by matching too (as in HOL4)                                *)
let kit_dep_rules (avoid:term list) (thl:thm list) : (int * thm * term list) list =
  map (fun th ->
         let thf,xs,ants = kit_rule_parts (union avoid (thm_frees th)) th in
         let c = concl thf in
         let eqth = if is_eq c then thf else if is_neg c then EQF_INTRO thf
                    else EQT_INTRO thf in
         length ants,itlist DISCH ants eqth,xs)
      (flat (map CONJUNCTS thl));;

(* the first instance of a rule in tm: A |- l' = r' (A the antecedents).    *)
(* The variables that the theorem quantifies and that the match leaves in   *)
(* antecedents only become existential, as in HOL4 (DEP_FIND_matches): the  *)
(* antecedents with them are then one antecedent ?vs. ai' /\ .. /\ aj'       *)
let kit_dep_match ((n,rule,xs):int * thm * term list) (tm:term) : thm * term list =
  let partfn c = lhs (funpow n rand c) in
  let mfn = PART_MATCH partfn rule in
  let rec ants k c = if k = 0 then [] else lhand c :: ants (k-1) (rand c) in
  let at bvs t =
    let ith = mfn t in
    let al = ants n (concl ith) in
    let eqi = funpow n UNDISCH ith in
    let eqn = concl eqi in
    let evs = filter (fun x -> not (vfree_in x eqn) && exists (vfree_in x) al &&
                               not (exists (fun h -> vfree_in x h) (hyp rule))) xs in
    let eqi,al =
      if evs = [] then eqi,al else
      let eal,oal = partition (fun a -> exists (fun x -> vfree_in x a) evs) al in
      let a = list_mk_conj eal in
      let eqa = itlist PROVE_HYP (kit_conj_split (length eal) (ASSUME a)) eqi in
      let ex = list_mk_exists(evs,a) in
      kit_choose_list evs ex eqa,oal @ [ex] in
    if exists (fun a -> exists (fun b -> vfree_in b a) bvs) al
    then failwith "kit_dep_match: bound variable" else eqi,al in
  let rec search bvs t =
    try at bvs t with Failure _ ->
    match t with
      Comb(l,r) -> (try search bvs l with Failure _ -> search bvs r)
    | Abs(v,b) -> search (v::bvs) b
    | _ -> failwith "kit_dep_match" in
  search [] tm;;

(* rewrite tm with the rules (each once if once, else again and again):    *)
(* A |- tm = tm' and the antecedents A, or failure if nothing applies      *)
let kit_dep_conv (once:bool) (rw:thm list -> conv) (rules:(int * thm * term list) list)
                 (tm:term) : thm * term list =
  let steps = ref 0 in
  let rec round rules tm (th,acc) changed =
    match rules with
      [] -> (th,acc),changed
    | r::rest ->
        (match (try Some (kit_dep_match r tm) with Failure _ -> None) with
           None -> round rest tm (th,acc) changed
         | Some (eqi,al) ->
             incr steps;
             if !steps > !kit_dep_max_steps then failwith "DEP_REWRITE: too many steps" else
             let cth = rw [eqi] tm in
             let tm' = rand(concl cth) in
             if tm' = tm then round rest tm (th,acc) changed else
             round rest tm' (TRANS th cth,acc @ al) true) in
  let rec loop tm (th,acc) any =
    let (th',acc'),changed = round rules tm (th,acc) false in
    if changed && not once then loop (rand(concl th')) (th',acc') true
    else (th',acc'),(any || changed) in
  let (th,acc),changed = loop tm (REFL tm,[]) false in
  if not changed then failwith "DEP_REWRITE: no change" else th,acc;;

(* the goal from |- A /\ .. /\ tm' (A the antecedents) *)
let kit_dep_tac (once:bool) (rw:thm list -> conv) (thl:thm list) : tactic =
  fun (asl,w) ->
    let rules = kit_dep_rules (variables w) thl in
    let cth,al = kit_dep_conv once rw rules w in
    let w' = rand(concl cth) in
    let atoms = rev_itlist (fun a acc ->
        rev_itlist (fun c acc -> if c = cake_true_tm || exists (aconv c) acc then acc
                                 else acc @ [c])
                   (conjuncts a) acc) al [] in
    if atoms = [] then
      let cth' = itlist (fun a th -> PROVE_HYP (EQT_ELIM (REWRITE_CONV[] a)) th) al cth in
      (null_meta,[asl,w'],fun _ thl -> EQ_MP (SYM cth') (hd thl))
    else
      (* the goal A /\ goal', or just A when goal' is T (as HOL4's DEP_TAC) *)
      let triv = (w' = cake_true_tm) in
      let nw = if triv then list_mk_conj atoms else mk_conj(list_mk_conj atoms,w') in
      (null_meta,[asl,nw],fun _ thl ->
         let th = hd thl in
         let ath = if triv then th else CONJUNCT1 th in
         let aths = kit_conj_split (length atoms) ath in
         let rec build t =
           if t = cake_true_tm then TRUTH
           else if is_conj t then CONJ (build (lhand t)) (build (rand t))
           else let f = find (fun f -> aconv (concl f) t) aths in
                EQ_MP (ALPHA (concl f) t) f in
         let cth' = itlist (fun a th -> PROVE_HYP (build a) th) al cth in
         EQ_MP (SYM cth') (if triv then TRUTH else CONJUNCT2 th));;

let DEP_PURE_ONCE_REWRITE_TAC thl = kit_dep_tac true PURE_ONCE_REWRITE_CONV thl;;
let DEP_ONCE_REWRITE_TAC thl = DEP_PURE_ONCE_REWRITE_TAC thl THEN REWRITE_TAC[];;
let DEP_PURE_REWRITE_TAC thl =
  REPEAT (CHANGED_TAC (kit_dep_tac false PURE_REWRITE_CONV thl));;
let DEP_REWRITE_TAC thl =
  REPEAT (CHANGED_TAC (kit_dep_tac false REWRITE_CONV thl));;
let DEP_ASM_REWRITE_TAC thl = ASSUM_LIST (fun asl -> DEP_REWRITE_TAC (asl @ thl));;
let DEP_ONCE_ASM_REWRITE_TAC thl = ASSUM_LIST (fun asl -> DEP_ONCE_REWRITE_TAC (asl @ thl));;

(* ------------------------------------------------------------------------- *)
(* HOL4 qmatch_goalsub_abbrev_tac `pat` and qmatch_asmsub_abbrev_tac: the    *)
(* pattern (a string, parsed in the goal's context: its variables that are  *)
(* free in the goal stand for themselves) is matched with the subterms of   *)
(* the goal (of the assumptions), top down, newest assumption first; the    *)
(* other pattern variables (not those named _..) become abbreviations       *)
(* (ABBREV_TAC `v = t`: t is replaced by v in the goal and the assumptions  *)
(* and t = v is assumed); EXPAND_TAC "v" undoes one.                        *)
(* ------------------------------------------------------------------------- *)

let kit_match_abbrev (sel:string list) (s:string) : tactic = fun (asl,w as g) ->
  let fr = kit_goal_frees g in
  let pat = kit_parse_in fr s in
  let fixed = intersect (frees pat) fr in
  let binds = tryfind (fun (t,bvs) ->
                 let b = kit_rename_match fixed pat bvs t in
                 if b = [] then failwith "nothing to abbreviate" else b)
                (kit_rename_places sel g) in
  MAP_EVERY (fun (t,v) -> if is_var t then ALL_TAC else ABBREV_TAC (mk_eq(v,t))) binds g;;

let MATCH_GOALSUB_ABBREV_TAC (s:string) : tactic = kit_match_abbrev ["sg0"] s;;

let MATCH_ASMSUB_ABBREV_TAC (s:string) : tactic = kit_match_abbrev ["sa0"] s;;

(* ------------------------------------------------------------------------- *)
(* HOL4 `t` by tac, `t` suffices_by tac, sg `t`, with t a string parsed in   *)
(* the goal's context (no type annotations needed).                          *)
(*   QBY "t" tac          prove t by tac (which must solve it), then strip  *)
(*                        it into the assumptions (as HOL4's by).           *)
(*   QSUFFICES_BY "t" tac t ==> goal by tac; t is the new goal.             *)
(*   QSUBGOAL "t"         the goals t, then the goal with t assumed.        *)
(* ------------------------------------------------------------------------- *)

let QBY (s:string) (tac:tactic) : tactic = fun g ->
  let t = kit_parse_typed (kit_goal_frees g) bool_ty s in
  (SUBGOAL_THEN t CAKE_STRIP_ASSUME_TAC THENL [tac THEN NO_TAC; ALL_TAC]) g;;

let QSUFFICES_BY (s:string) (tac:tactic) : tactic = fun g ->
  let t = kit_parse_typed (kit_goal_frees g) bool_ty s in
  (SUFF_TAC t THENL [tac THEN NO_TAC; ALL_TAC]) g;;

let QSUBGOAL (s:string) : tactic = fun g ->
  let t = kit_parse_typed (kit_goal_frees g) bool_ty s in
  SUBGOAL_THEN t CAKE_STRIP_ASSUME_TAC g;;

(* ------------------------------------------------------------------------- *)
(* HOL4 namedCases_on `t` ["a b"; "c"]: CASES_ON with the names of the new   *)
(* variables of each case (the disjuncts of the type's cases theorem, in     *)
(* order; "_" or "" keeps the default names of a case); for a product type  *)
(* one string names all the components (HOL4's tupleCases): ["a b c"]      *)
(* gives t = (a,b,c).  t is parsed in the goal's context.                   *)
(* ------------------------------------------------------------------------- *)

let kit_named_nchotomy (names:string list) (ty:hol_type) : thm =
  let words s = filter (fun w -> w <> "") (String.split_on_char ' ' (String.trim s)) in
  let rec comps ty = match ty with Tyapp("prod",[a;b]) -> a :: comps b | _ -> [ty] in
  let tys = comps ty in
  if length tys > 1 && length names = 1 then
    let ns = words (hd names) in
    if length ns <> length tys then failwith "NAMED_CASES_ON: wrong number of names" else
    let vs = map2 (fun n t -> if n = "_" || n = "-" then genvar t else mk_var(n,t)) ns tys in
    let x = variant vs (mk_var("x",ty)) in
    let tup = end_itlist (curry mk_pair) vs in
    let rec projs t l =
      match l with
        [_] -> [t]
      | _::rest -> mk_icomb(mk_const("FST",[]),t) :: projs (mk_icomb(mk_const("SND",[]),t)) rest
      | [] -> [] in
    GEN x (prove(list_mk_exists(vs,mk_eq(x,tup)),
                 MAP_EVERY EXISTS_TAC (projs x vs) THEN REWRITE_TAC[PAIR]))
  else
    let nch = nchotomy_of_type ty in
    let nch = INST_TYPE (type_match (type_of (fst(dest_forall(concl nch)))) ty []) nch in
    let x,body = dest_forall (concl nch) in
    let ds = disjuncts body in
    let rename (s,d) =
      let bvs,m = strip_exists d in
      let ns = words s in
      if ns = [] || ns = ["_"] || ns = ["-"] || length ns <> length bvs then d else
      let vs' = map2 (fun n v -> if n = "_" || n = "-" then v else mk_var(n,type_of v)) ns bvs in
      list_mk_exists(vs',vsubst (zip vs' bvs) m) in
    let names' = if length names >= length ds then fst(chop_list (length ds) names)
                 else names @ replicate "_" (length ds - length names) in
    let tm' = mk_forall(x,list_mk_disj(map rename (zip names' ds))) in
    EQ_MP (ALPHA (concl nch) tm') nch;;

let NAMED_CASES_ON (s:string) (names:string list) : tactic = fun (asl,w as g) ->
  let fr = kit_goal_frees g in
  let venv = map (fun v -> let n,t = dest_var v in n,pretype_of_type t) fr in
  let ptm,l = (parse_preterm o flat o map cake_wild_tokens o lex o explode) s in
  if l <> [] then failwith "NAMED_CASES_ON: unparsed input" else
  let tm = cake_preterm_to_term s venv ptm in
  let nch = ISPEC tm (kit_named_nchotomy names (type_of tm)) in
  (* the new variables keep their names unless they are in use *)
  let avoid = itlist (union o thm_frees o snd) asl (frees w) in
  let rec ttac th : tactic =
    let c = concl th in
    if is_disj c then DISJ_CASES_THEN ttac th
    else if is_exists c then
      let v,_ = dest_exists c in
      X_CHOOSE_THEN (kit_primed_var (avoid @ thm_frees th) v) ttac th
    else if is_var tm then CAKE_SUBST_ALL_TAC th ORELSE ASSUME_TAC th
    else (CAKE_SUBST_ALL_TAC th THEN ASSUME_TAC th) ORELSE ASSUME_TAC th in
  (MP_TAC nch THEN DISCH_THEN ttac) g;;

(* ------------------------------------------------------------------------- *)
(* HOL4 Induct_on `x` for a variable x given by name: free in the goal (as  *)
(* INDUCT_ON), or bound by the goal's leading universal quantifiers: the    *)
(* quantifiers are stripped, x stays free and the others are quantified     *)
(* again (HOL4 FREEUP), then INDUCT_ON x; the induction hypothesis is then  *)
(* for all values of the other variables.                                   *)
(* ------------------------------------------------------------------------- *)

let kit_induct_bound (x:term) : tactic = fun (asl,w as g) ->
  let vs,_ = strip_forall w in
  let avoid = ref (filter (fun v -> not (v = x)) (kit_goal_frees g)) in
  let vs' = map (fun v -> if v = x then x else
                   let v' = kit_primed_var (x :: !avoid) v in avoid := v' :: !avoid; v') vs in
  let others = filter (fun v -> not (v = x)) vs' in
  (MAP_EVERY X_GEN_TAC vs' THEN MAP_EVERY (fun v -> SPEC_TAC(v,v)) (rev others) THEN
   INDUCT_ON x) g;;

let QINDUCT_ON (s:string) : tactic = fun (asl,w as g) ->
  let n = String.trim s in
  let fr = kit_goal_frees g in
  match filter (fun v -> fst(dest_var v) = n) fr with
    v::_ -> INDUCT_ON v g
  | [] ->
      let vs,_ = strip_forall w in
      match filter (fun v -> fst(dest_var v) = n) vs with
        v::_ -> kit_induct_bound v g
      | [] -> failwith ("QINDUCT_ON: no variable " ^ n ^
                        " free in the goal or bound by its quantifiers");;

(* INDUCT_ON x with x not free in the goal but bound by its leading          *)
(* universal quantifiers: as HOL4's Induct_on (FREEUP, above).  Before, the  *)
(* induction was on a vacuous quantifier !x around the goal.  Since          *)
(* 2026-11-20 (in check mode: a KITDIFF line, and the old behaviour).        *)
let INDUCT_ON (x:term) : tactic = fun (asl,w as g) ->
  if is_var x && not (free_in x w) &&
     not (exists (fun (_,th) -> free_in x (concl th)) asl) &&
     mem x (fst(strip_forall w))
  then (if !kit_check then (kit_diff "INDUCT_ON on a bound variable"; INDUCT_ON x g)
        else kit_induct_bound x g)
  else INDUCT_ON x g;;

(* PAIR_CASES_ON t for a term t of a product type that is not a variable:   *)
(* t = (p0,..,pn) is assumed, with new variables p0 .. pn, and t is         *)
(* replaced by the tuple everywhere (as CASES_ON a compound term; HOL4's    *)
(* PairCases_on takes only variables).  Before, it failed.  Since 2026-11-20. *)
let PAIR_CASES_ON (x:term) : tactic = fun (asl,w as g) ->
  if is_var x then PAIR_CASES_ON x g else
  let rec comps ty = match ty with
      Tyapp("prod",[a;b]) -> a :: comps b
    | _ -> [ty] in
  let tys = comps (type_of x) in
  if length tys < 2 then failwith "PAIR_CASES_ON: not of a product type" else
  let avoid = itlist (union o thm_frees o snd) asl (frees w) in
  let rec fresh av l i =
    match l with
      [] -> []
    | t::rest -> let v = kit_primed_var av (mk_var("p" ^ string_of_int i,t)) in
                 v :: fresh (v::av) rest (i+1) in
  let vs = fresh avoid tys 0 in
  let tup = end_itlist (curry mk_pair) vs in
  let rec projs t l =
    match l with
      [_] -> [t]
    | _::rest -> mk_icomb(mk_const("FST",[]),t) ::
                 projs (mk_icomb(mk_const("SND",[]),t)) rest
    | [] -> [] in
  let eth = prove(list_mk_exists(vs,mk_eq(x,tup)),
                  MAP_EVERY EXISTS_TAC (projs x vs) THEN REWRITE_TAC[PAIR]) in
  (MP_TAC eth THEN
   MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC)) vs THEN
   DISCH_THEN(fun th -> CAKE_SUBST_ALL_TAC th THEN ASSUME_TAC th)) g;;

(* ------------------------------------------------------------------------- *)
(* IGNASM "pat" (HOL4 IgnAsm `pat`) in the list of SIMP, FS, RFS, GVS,       *)
(* GVS_ASM or RW: the assumptions that the pattern matches (parsed in the   *)
(* goal's context, as for QPAT_X_ASSUM) are neither used nor simplified:     *)
(* they are set aside while the tactic runs and put back, as the oldest      *)
(* assumptions, in every goal it leaves; e.g. FS[IGNASM "!x. _"; def] keeps *)
(* the induction hypotheses out of FS.  IGNASM "pat" is a marker theorem    *)
(* (a fresh copy of T, with its pattern in a table).  Since 2026-11-20.     *)
(* ------------------------------------------------------------------------- *)

let kit_ignasm_tbl = ref ([] : (thm * string) list);;

let IGNASM (s:string) : thm =
  let th = CONJUNCT1 (CONJ TRUTH TRUTH) in
  kit_ignasm_tbl := (th,s) :: !kit_ignasm_tbl; th;;

let kit_with_ignasm (tac:thm list -> tactic) (thl:thm list) : tactic = fun (asl,w as g) ->
  let pats = mapfilter (fun th -> snd (find (fun (m,_) -> m == th) !kit_ignasm_tbl)) thl in
  if pats = [] then tac thl g else
  let thl' = filter (fun th -> not (exists (fun (m,_) -> m == th) !kit_ignasm_tbl)) thl in
  let pts = map (fun s -> kit_qpat s g) pats in
  let ign (_,th) = exists (fun (p,fixed) -> can (term_match fixed p) (concl th)) pts in
  let ignored = filter ign asl and kept = filter (fun a -> not (ign a)) asl in
  let (meta,gs,just) = tac thl' (kept,w) in
  (meta,map (fun (a,w') -> (a @ ignored,w')) gs,just);;

let SIMP thl = kit_with_ignasm SIMP thl;;
let FS thl = kit_with_ignasm FS thl;;
let RFS thl = kit_with_ignasm RFS thl;;
let GVS thl = kit_with_ignasm GVS thl;;
let GVS_ASM thl = kit_with_ignasm GVS_ASM thl;;
let RW thl = kit_with_ignasm RW thl;;
