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

let DRULE_ALL th : tactic =
  fun (asl,w as gl) ->
    MP_TAC (drule_all_with (map snd asl) (IMP_CURRY_RULE (GEN_ALL th))) gl;;

(* theorem-tactic forms: use an assumption as the rule *)

let DRULE_THEN (ttac:thm_tactic) th : tactic =
  let mp = MATCH_MP_CURRIED th in
  FIRST_ASSUM (fun a -> ttac (mp a));;

(* irule *)

let IRULE th : tactic =
  let th' = GEN_ALL th in
  let c = snd(strip_forall(concl th')) in
  if not (is_imp c) then MATCH_ACCEPT_TAC th' else
  MATCH_MP_TAC th' THEN
  (fun (asl,w as gl) ->
     if is_exists w then ALL_TAC gl else REPEAT CONJ_TAC gl);;

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

let IMP_RES_TAC th : tactic =
  fun gl -> try IMP_RES_THEN CAKE_ASSUME_TAC th gl
            with Failure _ -> ALL_TAC gl;;

(* res_tac: every implicational assumption against the others *)

let RES_TAC : tactic =
  fun (asl,w as gl) ->
    let imps = filter (fun th -> is_imp(snd(strip_forall(concl th))))
                      (map snd asl) in
    (EVERY (map IMP_RES_TAC imps)) gl;;

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
    let avoid = frees whole in
    let v1 = variant avoid (mk_var(n1,tya)) in
    let v2 = variant (v1::avoid) (mk_var(n2,tyb)) in
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

let METIS_TAC thl : tactic =
  fun g -> with_type_invention (fun g -> METIS_TAC thl g) g;;

let ASM_METIS_TAC thl : tactic =
  fun g -> with_type_invention (fun g -> ASM_METIS_TAC thl g) g;;

let METIS thl tm = with_type_invention (METIS thl) tm;;

(* HOL4's CCONTR_TAC: assume the negation of the goal, prove F *)

let CCONTR_TAC : tactic = REFUTE_THEN ASSUME_TAC;;
