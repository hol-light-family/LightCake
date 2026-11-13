(* ========================================================================= *)
(* CakeML kit: the definition package.                                       *)
(*                                                                           *)
(*   cake_def `clauses`              HOL4 Definition with automatic          *)
(*                                   termination (as HOL Light's define).    *)
(*   cake_def_wf `R` tac `clauses`   HOL4 Definition ... Termination         *)
(*                                   WF_REL_TAC `R` >> tac: R is the         *)
(*                                   relation on the tupled arguments (on    *)
(*                                   their sum, for mutual recursion); WF R  *)
(*                                   is proved automatically and tac must    *)
(*                                   prove each termination condition.       *)
(*   cake_ind "name"                 the induction theorem of a recursive    *)
(*                                   definition (HOL4's name_ind), with one  *)
(*                                   case per clause and one hypothesis per  *)
(*                                   recursive call.                         *)
(* Clauses may use case constants (see datatype.ml) on their right hand      *)
(* sides; the definitions come out with the case constants as written.       *)
(* Internally a case constant is turned into a match while the recursion     *)
(* theorem is built (so that HOL Light's machinery sees the contexts of the  *)
(* recursive calls), and back afterwards.  Nothing is ever assumed.          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* HOL4's combinators for termination relations.                             *)
(* ------------------------------------------------------------------------- *)

let inv_image = new_definition
  `inv_image (R:B->B->bool) (f:A->B) = \x y. R (f x) (f y)`;;

let inv_image_THM = prove
 (`!R (f:A->B) x y. inv_image R f x y <=> R (f x) (f y)`,
  REWRITE_TAC[inv_image]);;

let WF_inv_image = prove
 (`!R (f:A->B). WF R ==> WF (inv_image R f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inv_image] THEN
  MATCH_MP_TAC WF_MEASURE_GEN THEN ASM_REWRITE_TAC[]);;

parse_as_infix("LEX",(14,"right"));;

let LEX_DEF = new_definition
  `(R1:A->A->bool) LEX (R2:B->B->bool) =
     \p q. R1 (FST p) (FST q) \/ (FST p = FST q /\ R2 (SND p) (SND q))`;;

let LEX_THM = prove
 (`!R1 R2 (a:A) (b:B) c d.
     (R1 LEX R2) (a,b) (c,d) <=> R1 a c \/ (a = c /\ R2 b d)`,
  REWRITE_TAC[LEX_DEF]);;

let WF_LEX_HOL4 = prove
 (`!(R1:A->A->bool) (R2:B->B->bool). WF R1 /\ WF R2 ==> WF (R1 LEX R2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`R1:A->A->bool`; `R2:B->B->bool`] WF_LEX) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; LEX_DEF]);;

let measure = new_definition
  `measure (f:A->num) = inv_image (<) f`;;

let measure_THM = prove
 (`!(f:A->num) x y. measure f x y <=> f x < f y`,
  REWRITE_TAC[measure; inv_image]);;

let WF_measure = prove
 (`!f:A->num. WF (measure f)`,
  REWRITE_TAC[measure] THEN GEN_TAC THEN MATCH_MP_TAC WF_inv_image THEN
  REWRITE_TAC[WF_num]);;

let WF_LT_NUM = prove
 (`WF ((<):num->num->bool)`,
  REWRITE_TAC[WF_num]);;

(* the automatic proof of WF R, for R built from the combinators above *)

(* and of relations whose well-foundedness was proved by hand and          *)
(* registered with cake_register_wf (HOL4 termination relations that are   *)
(* not built from measure, inv_image and LEX)                               *)

let cake_extra_wf = ref ([] : thm list);;

let cake_register_wf th = cake_extra_wf := th :: !cake_extra_wf;;

let WF_TAC : tactic =
  REPEAT (MATCH_ACCEPT_TAC WF_LT_NUM ORELSE MATCH_ACCEPT_TAC WF_measure ORELSE
          MATCH_ACCEPT_TAC WF_MEASURE ORELSE MATCH_ACCEPT_TAC WF_FALSE ORELSE
          MATCH_MP_TAC WF_inv_image ORELSE MATCH_MP_TAC WF_LEX_HOL4 ORELSE
          MATCH_MP_TAC WF_MEASURE_GEN ORELSE CONJ_TAC ORELSE
          (fun g -> MAP_FIRST MATCH_ACCEPT_TAC (!cake_extra_wf) g));;

(* the rewrites that unfold the combinators in termination conditions *)

let WF_REL_THMS = [inv_image_THM; LEX_THM; measure_THM; MEASURE];;

(* ------------------------------------------------------------------------- *)
(* A termination tactic for size measures (HOL4: WF_REL_TAC `measure ..` >>  *)
(* fs[list_size ...] >> decide_tac): unfold the relation, the size           *)
(* functions and their aux forms; for every MEM x l assumption and every     *)
(* list_size f l of the goal add f x < list_size f l; then arithmetic.       *)
(* ------------------------------------------------------------------------- *)

let MEM_LIST_SIZE = prove
 (`!(f:A->num) l x. MEM x l ==> f x < list_size f l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; list_size] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[]) THEN
  ARITH_TAC);;

let MEM_SIZE_TAC : tactic =
  fun (asl,w as gl) ->
    let ls = find_terms (fun t -> try fst(dest_const(fst(strip_comb t))) =
                                      "list_size" && length(snd(strip_comb t)) = 2
                                  with Failure _ -> false) w in
    let mems = mapfilter (fun (_,th) -> let c = concl th in
                            if is_comb c && is_comb(rator c) &&
                               (try fst(dest_const(rator(rator c))) = "MEM"
                                with Failure _ -> false)
                            then th else failwith "") asl in
    let facts = flat (map (fun t ->
        let _,[f;l] = strip_comb t in
        mapfilter (fun th -> if rand(concl th) = l then
                                MATCH_MP (ISPECL [f;l] MEM_LIST_SIZE) th
                              else failwith "") mems) ls) in
    MAP_EVERY ASSUME_TAC facts gl;;

let TERM_TAC : tactic =
  REPEAT BOSS_STRIP_TAC THEN RVEQ_TAC THEN
  (fun g -> let ths = WF_REL_THMS @ [FST; SND; pair_size_THM; sum_CASE] @
                      !the_size_defs @ flat (map snd (!the_size_aux_eqs)) in
            (RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths) g) THEN
  MEM_SIZE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pair_size_THM]) THEN
  ASM_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Case constants to match terms and back.                                   *)
(* ------------------------------------------------------------------------- *)

(* HOL Light's recursion machinery collects the variables bound by the     *)
(* enclosing patterns into tuples, so every bound variable of the match    *)
(* terms must be distinct from every other variable of the clauses: the    *)
(* pattern variables get the names of the user's lambda variables, made    *)
(* fresh, and the arm variables fresh names.                                *)

let rename_match_arms (fresh:term->term) (fs:term list) (mtm:term) =
  let m,x_arms = dest_comb mtm in
  let x = rand m in
  let rec arms t =
    if is_comb t && is_comb(rator t) &&
       (try fst(dest_const(rator(rator t))) = "_SEQPATTERN"
        with Failure _ -> false)
    then rand(rator t) :: arms (rand t) else [t] in
  let al = arms x_arms in
  let prefs = map (fun f -> fst(strip_abs f)) fs in
  let rename_arm arm pref =
    let y,b1 = dest_abs arm in
    let z,b2 = dest_abs b1 in
    let vs,core = strip_exists b2 in
    let y' = fresh y and z' = fresh z in
    let vs' = map2 (fun v k ->
                      let base = if k < length pref then el k pref else v in
                      fresh (mk_var(fst(dest_var base),type_of v)))
                   vs (0--(length vs - 1)) in
    let core' = vsubst ((y',y)::(z',z)::zip vs' vs) core in
    mk_abs(y',mk_abs(z',list_mk_exists(vs',core'))) in
  let al' = map2 rename_arm al prefs in
  let rec rebuild t al' =
    match al' with
      [a] -> a
    | a::rest -> mk_comb(mk_comb(rator(rator t),a),rebuild (rand t) rest)
    | [] -> failwith "rename_match_arms" in
  mk_comb(m,rebuild x_arms al');;

(* case constants go to the recursion package as they are (it has a rule for *)
(* each, kit/recursion.ml); set this to true to turn them into match terms   *)
(* first, as the kit did before 2026-11-13                                    *)

let cake_case_to_match = ref false;;

let CASE_TO_MATCH_CONV : conv =
  fun tm0 ->
    let avoid = ref (variables tm0) in
    let fresh v = let v' = variant (!avoid) v in avoid := v' :: !avoid; v' in
    let one tm =
      if not (is_case_app tm) then failwith "CASE_TO_MATCH_CONV" else
      let c,_,fs = dest_case_app tm in
      (* pair_CASE stays: the recursion package has a cheap rule for it *)
      if fst(dest_const c) = "pair_CASE" then failwith "CASE_TO_MATCH_CONV" else
      let ci = case_info_of_const c in
      let th1 = REWR_CONV (case_match_thm ci) tm in
      let mtm = rand(concl th1) in
      let mtm' = rename_match_arms fresh fs mtm in
      let th2 = TRANS th1 (ALPHA mtm mtm') in
      CONV_RULE (RAND_CONV (DEPTH_CONV BETA_CONV)) th2 in
    TOP_DEPTH_CONV one tm0;;

(* ------------------------------------------------------------------------- *)
(* Clauses.                                                                  *)
(* ------------------------------------------------------------------------- *)

(* the clauses as a list of (vars, lhs function, args, rhs) *)

let dest_clauses tm =
  map (fun cl ->
         let vs,eq = strip_forall cl in
         let l,r = dest_eq eq in
         let f,args = strip_comb l in
         vs,f,args,r)
      (conjuncts tm);;

(* close each clause over its free variables, except the defined functions *)

(* in the order of their first occurrence, left to right, as HOL4 does *)

let frees_in_order tm =
  let rec go bound t acc =
    match t with
      Var _ -> if mem t bound || mem t acc then acc else t :: acc
    | Const _ -> acc
    | Comb(a,b) -> go bound b (go bound a acc)
    | Abs(v,b) -> go (v::bound) b acc in
  rev (go [] tm []);;

let close_clauses fns tm =
  list_mk_conj
    (map (fun cl -> let bod = snd(strip_forall cl) in
                    let vs = subtract (frees_in_order bod) fns in
                    list_mk_forall(vs,bod))
         (conjuncts tm));;

(* ------------------------------------------------------------------------- *)
(* Store of induction theorems.                                              *)
(* ------------------------------------------------------------------------- *)

let cake_ind_store = ref ([] : (string * thm) list);;

let cake_ind name = assoc name (!cake_ind_store);;

let cake_tc_store = ref ([] : (string * term) list);;

(* ------------------------------------------------------------------------- *)
(* Single recursive function.                                                *)
(* ------------------------------------------------------------------------- *)

(* the conjuncts of the termination condition, after instantiating <<      *)

let tcs_of_wf_hyp wfh r =
  let rel,bod = dest_exists wfh in
  let bod' = vsubst [r,rel] bod in
  let wf,tcs = dest_conj bod' in
  wf,conjuncts tcs;;

let cake_quiet = ref false;;

let print_tcs name tcs =
  if !cake_quiet then () else
   (Format.print_string ("cake_def "^name^": termination conditions:\n");
    do_list (fun t -> Format.print_string ("  "^string_of_term t^"\n")) tcs;
    Format.print_flush());;

(* prove the existence theorem's hypotheses: the well-definedness one       *)
(* automatically, the WF one with the relation r (WF r by WF_TAC) and the   *)
(* tactic tac for each termination condition.  Returns the theorem and, if  *)
(* a relation was used, (WF theorem, TC theorems).                          *)

let is_wf_hyp h =
  is_exists h &&
  (let bod = snd(dest_exists h) in
   try let w = if is_conj bod then fst(dest_conj bod) else bod in
       fst(dest_const(rator w)) = "WF"
   with Failure _ -> false);;

let discharge_hyps name rel_tac eth =
  let wfhs,others = partition is_wf_hyp (hyp eth) in
  let eth =
    itlist (fun h th ->
              let hth = try prove(h, REWRITE_TAC[] THEN
                                     TRY(REPEAT GEN_TAC THEN DISCH_TAC THEN
                                         ASM_MESON_TAC[]))
                        with Failure _ ->
                          failwith ("cake_def "^name^
                                    ": could not prove well-definedness: "^
                                    string_of_term h) in
              PROVE_HYP hth th) others eth in
  match wfhs,rel_tac with
    [],_ -> eth,None
  | [h],Some(r,tac) ->
      let rel,bod = dest_exists h in
      let r' = try inst (type_match (type_of r) (type_of rel) []) r
               with Failure _ -> r in
      if type_of r' <> type_of rel then
        failwith ("cake_def_wf "^name^": the relation has type "^
                  string_of_type(type_of r)^" but should have type "^
                  string_of_type(type_of rel)) else
      let bod' = vsubst [r',rel] bod in
      let wftm,tcs = if is_conj bod' then
                       let w,t = dest_conj bod' in w,conjuncts t
                     else bod',[] in
      cake_tc_store := (name,list_mk_conj (wftm::tcs)) :: !cake_tc_store;
      let wfth = try prove(wftm,WF_TAC)
                 with Failure _ -> failwith ("cake_def_wf "^name^
                                             ": could not prove "^
                                             string_of_term wftm) in
      let tc_thms =
        map (fun tc -> try prove(tc,tac)
                       with Failure msg ->
                         (print_tcs name [tc];
                          failwith ("cake_def_wf "^name^
                                    ": termination condition not proved ("^
                                    msg^")"))) tcs in
      let hth = EXISTS (h,r') (if tc_thms = [] then wfth
                               else CONJ wfth (end_itlist CONJ tc_thms)) in
      (* for the induction theorem every TC must be strict, R a p: a TC of a  *)
      (* tail call has the form !y. R y a ==> R y p; prove R a p as well       *)
      let strict tc th =
        let vs,bod = strip_forall tc in
        let ctx,c = if is_imp bod then dest_imp bod else `T`,bod in
        if is_forall c then
          let y,b = dest_forall c in
          let ra,rp = dest_imp b in
          let a = rand ra in
          let r0 = rator(rator ra) in
          let p = rand rp in
          let stm = list_mk_forall(vs,
                      if ctx = `T` then mk_comb(mk_comb(r0,a),p)
                      else mk_imp(ctx,mk_comb(mk_comb(r0,a),p))) in
          prove(stm,tac)
        else th in
      let strict_thms = try Some(map2 strict tcs tc_thms)
                        with Failure _ -> None in
      PROVE_HYP hth eth,
      (match strict_thms with Some st -> Some(wfth,st) | None -> None)
  | [h],None ->
      let rel,bod = dest_exists h in
      print_tcs name (conjuncts bod);
      failwith ("cake_def "^name^": termination not proved; use cake_def_wf")
  | _ -> failwith "discharge_hyps: several WF hypotheses";;

(* ------------------------------------------------------------------------- *)
(* Tuples.                                                                   *)
(* ------------------------------------------------------------------------- *)

let mk_tuple_term tms = end_itlist (curry mk_pair) tms;;

(* the selectors of a right-nested n-tuple t: FST t, FST(SND t), ..., SND^(n-1) t *)

let tuple_selectors n t =
  let rec sel k t =
    if k = 1 then [t]
    else mk_fst t :: sel (k - 1) (mk_snd t)
  and mk_fst t = mk_comb(mk_const("FST",[type_of(fst(dest_pair_ty t)),aty;
                                          snd(dest_pair_ty t),bty]),t)
  and mk_snd t = mk_comb(mk_const("SND",[type_of(fst(dest_pair_ty t)),aty;
                                          snd(dest_pair_ty t),bty]),t)
  and dest_pair_ty t =
    match dest_type(type_of t) with
      "prod",[a;b] -> mk_var("dummy",a),b
    | _ -> failwith "tuple_selectors" in
  sel n t;;

(* the curried form of WF induction on a relation r over n-tuples:          *)
(* WF r ==> !P. (!x1..xn. (!y1..yn. r (y1,..,yn) (x1,..,xn) ==> P y1..yn)  *)
(*                         ==> P x1..xn) ==> !x1..xn. P x1..xn             *)
(* proved once per n over type variables, then type-instantiated           *)

let wf_ind_curry_cache = ref ([] : (int * thm) list);;

let wf_ind_curry n =
  try assoc n (!wf_ind_curry_cache) with Failure _ ->
  let tys = map (fun i -> mk_vartype("A"^string_of_int i)) (1--n) in
  let xs = map2 (fun ty i -> mk_var("x"^string_of_int i,ty)) tys (1--n) in
  let ys = map2 (fun ty i -> mk_var("y"^string_of_int i,ty)) tys (1--n) in
  let xt = mk_tuple_term xs and yt = mk_tuple_term ys in
  let tty = type_of xt in
  let r = mk_var("r",mk_fun_ty tty (mk_fun_ty tty bool_ty)) in
  let p = mk_var("P",itlist mk_fun_ty tys bool_ty) in
  let pxs = list_mk_comb(p,xs) and pys = list_mk_comb(p,ys) in
  let hyp_tm = list_mk_forall(xs,
                 mk_imp(list_mk_forall(ys,mk_imp(list_mk_comb(r,[yt;xt]),pys)),
                        pxs)) in
  let wf_r = mk_comb(mk_const("WF",[tty,aty]),r) in
  let stmt = mk_imp(wf_r,mk_forall(p,mk_imp(hyp_tm,list_mk_forall(xs,pxs)))) in
  let t = mk_var("t_ind",tty) in
  let q = mk_abs(t,list_mk_comb(p,tuple_selectors n t)) in
  let th = prove(stmt,
    DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPEC q (MATCH_MP (fst(EQ_IMP_RULE(ISPEC r (GEN_ALL WF_IND))))
                             (ASSUME wf_r))) THEN
    REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]) in
  wf_ind_curry_cache := (n,th) :: !wf_ind_curry_cache; th;;

(* the instance for a given WF theorem, predicate variable and variables    *)

let curried_wf_ind wfth p xs =
  let n = length xs in
  let gen = wf_ind_curry n in
  let tys = map type_of xs in
  let tyi = map2 (fun ty i -> ty,mk_vartype("A"^string_of_int i)) tys (1--n) in
  let gen' = INST_TYPE tyi gen in
  let r = rand(concl wfth) in
  let th1 = MP (INST [r,mk_var("r",type_of r)] gen') wfth in
  let th2 = SPEC p th1 in
  (* rename the bound variables to xs *)
  th2;;

(* ------------------------------------------------------------------------- *)
(* Pattern splitting (exhaustiveness).                                       *)
(* ------------------------------------------------------------------------- *)

(* does term a (over split variables) match the pattern p? *)

let pattern_matches p a =
  try ignore(term_match [] p a); true with Failure _ -> false;;

(* compatibility of a pattern p with an argument a: they could be equal *)

let rec pat_compatible p a =
  if is_var p || is_var a then true
  else if is_numeral p && is_numeral a then dest_numeral p = dest_numeral a
  else
    let hp,ps = strip_comb p and ha,as_ = strip_comb a in
    is_const hp && is_const ha && fst(dest_const hp) = fst(dest_const ha) &&
    length ps = length as_ && forall2 pat_compatible ps as_;;

(* the first variable of a at which p has a non-variable *)

let rec split_var p a =
  if is_var a then (if is_var p then None else Some a)
  else if is_var p then None
  else
    let _,ps = strip_comb p and _,as_ = strip_comb a in
    let rec first l1 l2 = match l1,l2 with
        x::t,y::u -> (match split_var x y with Some v -> Some v
                                            | None -> first t u)
      | _ -> None in
    first ps as_;;

(* instances of a variable v by the patterns of its type, fresh names       *)

let split_instances avoid v =
  let nch = ISPEC v (nchotomy_of_type (type_of v)) in
  let ds = disjuncts(concl nch) in
  let avoid = ref avoid in
  map (fun d ->
         let vs,eq = strip_exists d in
         let vs' = map (fun x -> let x' = variant !avoid x in
                                 avoid := x' :: !avoid; x') vs in
         vsubst (zip vs' vs) (rand eq))
      ds;;

(* the leaves of the split tree of argument lists against clause patterns: *)
(* (args, Some i) for a clause leaf, (args, None) for a missing case       *)

let split_tree (pats : term list list) (args : term list) =
  let rec go args =
    let compat = filter (fun (i,ps) -> forall2 pat_compatible ps args)
                        (zip (0--(length pats - 1)) pats) in
    match compat with
      [] -> [args,None]
    | _ ->
      match find_opt (fun (i,ps) -> forall2 pattern_matches ps args) compat with
        Some (i,_) -> [args,Some i]
      | None ->
          let (_,ps) = hd compat in
          let rec first l1 l2 = match l1,l2 with
              x::t,y::u -> (match split_var x y with Some v -> Some v
                                                  | None -> first t u)
            | _ -> None in
          match first ps args with
            None -> failwith "split_tree: cannot split"
          | Some v ->
              let insts = split_instances (itlist (union o frees) args []) v in
              flat (map (fun inst -> go (map (vsubst [inst,v]) args)) insts)
  and find_opt p l = try Some (find p l) with Failure _ -> None in
  go args;;

(* the matching proof: split the goal P a1 .. an the same way              *)

let rec SPLIT_PATTERNS_TAC (pats : term list list) (leaf : int option -> tactic)
    : tactic =
  fun (asl,w as gl) ->
    let _,args = strip_comb w in
    let compat = filter (fun (i,ps) -> forall2 pat_compatible ps args)
                        (zip (0--(length pats - 1)) pats) in
    match compat with
      [] -> leaf None gl
    | _ ->
      let hit = try Some(fst(find (fun (i,ps) ->
                                       forall2 pattern_matches ps args) compat))
                with Failure _ -> None in
      match hit with
        Some i -> leaf (Some i) gl
      | None ->
        let (_,ps) = hd compat in
        let rec first l1 l2 = match l1,l2 with
            x::t,y::u -> (match split_var x y with Some v -> Some v
                                                | None -> first t u)
          | _ -> None in
        match first ps args with
          None -> failwith "SPLIT_PATTERNS_TAC"
        | Some v ->
            (CASES_ON v THEN SPLIT_PATTERNS_TAC pats leaf) gl;;

(* ------------------------------------------------------------------------- *)
(* The induction theorem of a single recursive function c (curried, n      *)
(* arguments) from its clauses and termination condition theorems.          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Tidying the context of an induction hypothesis: equations C x = t become  *)
(* t = C x, conjuncts implied by the others are dropped.  Returns the tidy   *)
(* context and |- tidy ==> ctx (or the context itself if anything fails).    *)
(* ------------------------------------------------------------------------- *)

let tidy_ctx ctx =
  if ctx = `T` then ctx,DISCH ctx (ASSUME ctx) else
  try
    let cs = conjuncts ctx in
    let orient c =
      if is_eq c && is_constructor_app (lhs c) && not (is_constructor_app (rhs c))
      then mk_eq(rhs c,lhs c) else c in
    let cs1 = map orient cs in
    (* the case rewrites come from the kit's prebuilt net (CASE_REWRITE_TAC): *)
    (* rebuilding a net of all of them for each conjunct costs about a second *)
    (* once a type with many constructors is defined                          *)
    let exists_meson ths = W(fun (_,w) -> if is_exists w then MESON_TAC ths
                                          else NO_TAC) in
    let implied others c =
      others <> [] &&
      can (fun () -> prove(mk_imp(list_mk_conj others,c),
                           DISCH_THEN(fun th -> CASE_REWRITE_TAC(CONJUNCTS th)) THEN
                           exists_meson []))
          () in
    let rec drop kept l = match l with
        [] -> rev kept
      | c::rest -> if implied (rev kept @ rest) c then drop kept rest
                   else drop (c::kept) rest in
    let cs2 = drop [] cs1 in
    let ctx' = list_mk_conj cs2 in
    let th = prove(mk_imp(ctx',ctx),
                   DISCH_THEN(fun th ->
                     let ths = CONJUNCTS th in
                     CASE_REWRITE_TAC ths THEN
                     REWRITE_TAC(map GSYM (filter (fun t -> is_eq(concl t)) ths)) THEN
                     CASE_REWRITE_TAC ths THEN
                     TRY(MESON_TAC ths))) in
    ctx',th
  with Failure _ -> ctx,DISCH ctx (ASSUME ctx);;

(* nicer names for the extra bound variables of an IH: drop primes when the  *)
(* unprimed name is free                                                    *)

let unprime_vars avoid vs =
  let rec base n = let k = String.length n in
    if k > 1 && n.[k-1] = '\'' then base (String.sub n 0 (k-1)) else n in
  let used = ref (map (fst o dest_var) avoid) in
  map (fun v -> let n,ty = dest_var v in
                let b = base n in
                let n' = if mem b !used then n else b in
                used := n' :: !used; mk_var(n',ty)) vs;;

let cake_ind_dbg = ref (None : (term * thm * (int option -> tactic) * term list list * (term * thm * bool) list list) option);;

let derive_induction (c:term) (clauses:(term list * term list) list)
                     (tc_thms:thm list) (wfth:thm) =
  let argtys,_ = splitlist dest_fun_ty (type_of c) in
  let n = length (snd(hd clauses)) in
  let argtys = fst(chop_list n argtys) in
  (* the predicate is P, or P' etc. if a clause has a variable called P *)
  let used = map (fst o dest_var)
               (itlist (fun (vs,args) acc -> union vs (union (freesl args) acc))
                       clauses []) in
  let rec pname n = if mem n used then pname (n ^ "'") else n in
  let p = mk_var(pname "P",itlist mk_fun_ty argtys bool_ty) in
  (* the tupled form of c, for the function variable of the TCs *)
  let tupled_c =
    if n = 1 then c else
    let t = mk_var("t_tc",itlist (fun a b -> mk_type("prod",[a;b]))
                                 (butlast argtys) (last argtys)) in
    mk_abs(t,list_mk_comb(c,tuple_selectors n t)) in
  let clean = CONV_RULE (DEPTH_CONV BETA_CONV THENC
                         PURE_REWRITE_CONV[FST; SND; AND_CLAUSES; IMP_CLAUSES]) in
  let inst_fn th =
    let c0 = concl th in
    if is_forall c0 &&
       (let v = fst(dest_forall c0) in type_of v = type_of tupled_c)
    then clean (ISPEC tupled_c th) else clean th in
  let tcs = map inst_fn tc_thms in
  let pats = map snd clauses in
  let untuple k t =
    let rec go k t = if k = 1 then [t]
                     else let x,y = dest_pair t in x :: go (k-1) y in
    go k t in
  (* each TC: !vs. ctx ==> r a p ; find its clause.  The TC's variables are *)
  (* first renamed apart from the pattern variables of every clause: the     *)
  (* TC of f t in the clause f s may call its variables s (for t) and s'    *)
  (* (for the argument), and renaming s' to the clause's s must not capture  *)
  let allpv = itlist (fun ps acc -> union (itlist (union o frees) ps []) acc)
                     pats [] in
  let apart th0 =
    let vs0 = fst(strip_forall(concl th0)) in
    let avoid = ref (allpv @ vs0 @ freesl(hyp th0)) in
    let vs' = map (fun v -> if mem (fst(dest_var v)) (map (fst o dest_var) allpv)
                            then pm_fresh avoid v else v) vs0 in
    if vs' = vs0 then th0 else GENL vs' (SPECL vs' th0) in
  let tc_info th =
    let th = apart th in
    let vs,bod = strip_forall(concl th) in
    let ctx,rc = if is_imp bod then dest_imp bod else `T`,bod in
    let ra,pt = dest_comb rc in
    let a = rand ra in
    let aargs = untuple n a in
    let i = index true (map (fun ps -> try let _,tmi,_ =
                                             term_match [] (mk_tuple_term ps)
                                                           pt in
                                           forall (fun (t,v) -> is_var t) tmi
                                       with Failure _ -> false) pats) in
    let _,ren,_ = term_match [] pt (mk_tuple_term (el i pats)) in
    let ctx1 = vsubst ren ctx in
    let aargs1 = map (vsubst ren) aargs in
    if ctx = `T` then i,ctx1,aargs1,th else
    (* th specialised to the clause's names *)
    let th1 = SPECL (map (fun v -> try rev_assoc v ren with Failure _ -> v) vs) th in
    (* eliminate equations y = t of variables that are not pattern variables *)
    let pv = itlist (union o frees) (el i pats) [] in
    let elim_one (ctx,args,th) =
      let c = find (fun c -> is_eq c &&
                     ((is_var(lhs c) && not (mem (lhs c) pv) &&
                       not (free_in (lhs c) (rhs c))) ||
                      (is_var(rhs c) && not (mem (rhs c) pv) &&
                       not (free_in (rhs c) (lhs c)))))
                   (conjuncts ctx) in
      let y,t = if is_var(lhs c) && not (mem (lhs c) pv) &&
                   not (free_in (lhs c) (rhs c))
                then lhs c,rhs c else rhs c,lhs c in
      vsubst [t,y] ctx,map (vsubst [t,y]) args,INST [t,y] th in
    let rec elim st = try elim (elim_one st) with Failure _ -> st in
    let ctx1',aargs1',th1' = elim (ctx1,aargs1,th1) in
    let ctx2,imp_th = tidy_ctx ctx1' in
    let th' = GEN_ALL (DISCH ctx2 (MP th1' (MP imp_th (ASSUME ctx2)))) in
    i,ctx2,aargs1',th' in
  let infos = map tc_info tcs in
  let ih_of (i,ctx,aargs,_) =
    let pv = itlist (union o frees) (el i pats) [] in
    let body = if ctx = `T` then list_mk_comb(p,aargs)
               else mk_imp(ctx,list_mk_comb(p,aargs)) in
    let evs = subtract (frees body) (p :: pv) in
    let evs' = unprime_vars (pv @ (subtract (frees body) evs)) evs in
    let body' = vsubst (zip evs' evs) body in
    list_mk_forall(evs',body') in
  (* per clause: the IHs, each with the TC theorem that proves it; drop     *)
  (* duplicates, keep the order                                             *)
  let clause_ihs i =
    let mine = filter (fun (j,_,_,_) -> j = i) infos in
    let rec dedup acc l = match l with
        [] -> rev acc
      | ((_,ctx,_,th) as inf)::t ->
          let ih = ih_of inf in
          if exists (fun (ih',_,_) -> aconv ih ih') acc then dedup acc t
          else dedup ((ih,th,ctx = `T`)::acc) t in
    dedup [] mine in
  let ihss = map clause_ihs (0--(length clauses - 1)) in
  let cases = map2 (fun (vs,ps) ihs ->
      let concl_ = list_mk_comb(p,ps) in
      let pv = itlist (union o frees) ps [] in
      list_mk_forall(pv,
        if ihs = [] then concl_
        else mk_imp(list_mk_conj (map (fun (ih,_,_) -> ih) ihs),concl_)))
    clauses ihss in
  (* missing patterns *)
  let xs = map2 (fun ty k -> mk_var("x"^string_of_int k,ty))
                argtys (1--n) in
  let leaves = split_tree pats xs in
  let missing = mapfilter (fun (args,opt) -> if opt = None then args
                                           else failwith "") leaves in
  let mcases = map (fun args ->
                      let pv = itlist (union o frees) args [] in
                      list_mk_forall(pv,list_mk_comb(p,args))) missing in
  let allcases = cases @ mcases in
  let stmt = mk_forall(p,mk_imp(list_mk_conj allcases,
                                list_mk_forall(xs,list_mk_comb(p,xs)))) in
  let cind = curried_wf_ind wfth p xs in
  let ncases = length cases in
  (* the proof of one IH, given its TC theorem *)
  let IH_TAC (_,tc,triv) =
    REPEAT GEN_TAC THEN
    (if triv then
       USE_THEN "wfh" MATCH_MP_TAC THEN MATCH_ACCEPT_TAC tc
     else
       DISCH_THEN(fun cth ->
         USE_THEN "wfh" MATCH_MP_TAC THEN MATCH_ACCEPT_TAC (MATCH_MP tc cth))) in
  let leaf opt =
    match opt with
      Some i ->
        let ihs = el i ihss in
        (match ihs with
           [] -> USE_THEN ("case"^string_of_int i) MATCH_ACCEPT_TAC
         | [ih] -> USE_THEN ("case"^string_of_int i) MATCH_MP_TAC THEN
                   IH_TAC ih
         | _ -> USE_THEN ("case"^string_of_int i) MATCH_MP_TAC THEN
                REPEAT CONJ_TAC THENL (map IH_TAC ihs))
    | None -> FIRST (map (fun k -> USE_THEN ("case"^string_of_int k)
                                     MATCH_ACCEPT_TAC)
                         (ncases--(length allcases - 1))) in
  cake_ind_dbg := Some(stmt,cind,leaf,pats,ihss);
  prove(stmt,
    GEN_TAC THEN DISCH_THEN(fun th ->
      MAP_EVERY (fun (k,c) -> LABEL_TAC ("case"^string_of_int k) c)
                (zip (0--(length allcases - 1)) (CONJUNCTS th))) THEN
    MATCH_MP_TAC cind THEN REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "wfh") THEN
    SPLIT_PATTERNS_TAC pats leaf);;

(* ------------------------------------------------------------------------- *)
(* The main entry points (single functions; mutual recursion below).         *)
(* ------------------------------------------------------------------------- *)

let cake_ind_debug = ref (None : (term * (term list * term list) list * thm list * thm) option);;

let cake_def_mutual_ref =
  ref (fun (_:(term * tactic) option) (_:term) ->
         (failwith "mutual recursion not loaded" : thm));;

(* a wildcard (a _ of the quotation) in a clause gives a named variable *)

let rename_wildcards tm =
  let fix cl =
    let bod = snd(strip_forall cl) in
    let ws = filter is_wildcard (frees bod) in
    if ws = [] then cl else
    let avoid = ref (frees bod) in
    let sub = map (fun w -> pm_fresh avoid (mk_var("x",type_of w)),w) ws in
    vsubst sub bod in
  list_mk_conj(map fix (conjuncts tm));;

(* measures to try for the induction theorem of a definition whose          *)
(* termination HOL Light proved by itself: the size of one argument, or of  *)
(* all of them                                                              *)

let measure_candidates ty =
  let rec comps ty = match dest_type ty with
      "prod",[a;b] -> a :: comps b
    | _ -> [ty] in
  let cs = comps ty in
  let n = length cs in
  let t = mk_var("t_ms",ty) in
  let sels = if n = 1 then [t] else tuple_selectors n t in
  let zero s = (try snd(dest_abs s) = `0` with Failure _ -> false) in
  let one k =
    let s = size_of_type [] (el k cs) in
    if zero s then failwith "" else
    let body = rhs(concl(TOP_DEPTH_CONV BETA_CONV (mk_comb(s,el k sels)))) in
    mk_comb(mk_const("measure",[ty,aty]),mk_abs(t,body)) in
  let whole = let s = size_of_type [] ty in
              if zero s then [] else [mk_comb(mk_const("measure",[ty,aty]),s)] in
  mapfilter one (0--(n-1)) @ whole;;

(* bare occurrences of the function f being defined (MAP f l, or f x for a  *)
(* function of two arguments) are eta-expanded, with bound variables named *)
(* eta%N, because the recursion package needs f applied to all its k       *)
(* arguments; ETA_MARKED_CONV undoes this in the definition theorem         *)

let eta_expand_bare k f tm =
  let n = ref 0 in
  let rec go t =
    let h,args = strip_comb t in
    if h = f then
      let args' = map go args in
      let m = length args' in
      if m >= k then list_mk_comb(h,args') else
      let tys = fst(chop_list (k - m)
                  (fst(splitlist dest_fun_ty (type_of(list_mk_comb(h,args')))))) in
      let vs = map (fun ty -> incr n; mk_var("eta%"^string_of_int !n,ty)) tys in
      list_mk_abs(vs,list_mk_comb(h,args' @ vs))
    else match t with
      Comb(a,b) -> mk_comb(go a,go b)
    | Abs(v,b) -> mk_abs(v,go b)
    | _ -> t in
  go tm;;

let ETA_MARKED_CONV tm =
  match tm with
    Abs(v,Comb(_,v')) when v' = v &&
      (let n = fst(dest_var v) in
       String.length n > 4 && String.sub n 0 4 = "eta%") -> ETA_CONV tm
  | _ -> failwith "ETA_MARKED_CONV";;

(* Overlapping clauses (HOL4 semantics: the first clause that matches      *)
(* wins) are completed as HOL4's TFL does: each clause is replaced by the   *)
(* instances of its patterns that no earlier clause matches, found by      *)
(* splitting variables into the constructors of their type; argument       *)
(* lists that no clause matches stay unspecified.  The instances of a      *)
(* clause keep its variable names.  Clauses with literal patterns (numerals *)
(* other than 0, T, F, strings) are not completed.                          *)

let complete_clauses (cls : (term list * term * term list * term) list) =
  let pats = map (fun (_,_,a,_) -> a) cls in
  let n = length pats in
  let idx = 0--(n-1) in
  let overlap =
    exists (fun i -> exists (fun j -> forall2 pat_compatible (el j pats) (el i pats))
                            (0--(i-1)))
           (1--(n-1)) in
  if not overlap then None else
  let rec has_literal p =
    if is_var p then false
    else if is_numeral p then dest_numeral p <> num_0
    else if is_constructor_app p then exists has_literal (snd(strip_comb p))
    else true in
  if exists (exists has_literal) pats then
    failwith "cake_def: overlapping clauses with literal patterns" else
  let avoid = ref (itlist (fun (_,_,a,r) acc -> union (frees r) (union (freesl a) acc))
                          cls []) in
  (* new variables are named v, v1, v2, ... as in HOL4's completed clauses *)
  let vcount = ref 0 in
  let rec fresh_v ty =
    let n = if !vcount = 0 then "v" else "v" ^ string_of_int !vcount in
    incr vcount;
    if mem n (map (fst o dest_var) !avoid) then fresh_v ty
    else let v = mk_var(n,ty) in (avoid := v :: !avoid; v) in
  let args0 = map (fun p -> fresh_v (type_of p)) (hd pats) in
  let split v =
    let nch = ISPEC v (nchotomy_of_type (type_of v)) in
    map (fun d -> let vs,eq = strip_exists d in
                  let vs' = map (fresh_v o type_of) vs in
                  vsubst (zip vs' vs) (rand eq))
        (disjuncts(concl nch)) in
  let rec first l1 l2 = match l1,l2 with
      x::t,y::u -> (match split_var x y with Some v -> Some v | None -> first t u)
    | _ -> None in
  let rec go args =
    match filter (fun i -> forall2 pat_compatible (el i pats) args) idx with
      [] -> []
    | i::_ ->
        let ps = el i pats in
        if forall2 pattern_matches ps args then [i,args] else
        match first ps args with
          None -> failwith "complete_clauses: cannot split"
        | Some v -> flat (map (fun inst -> go (map (vsubst [inst,v]) args)) (split v)) in
  let leaves = go args0 in
  let leaves = flat (map (fun i -> filter (fun (j,_) -> j = i) leaves) idx) in
  Some (map (fun (i,args) ->
      let (_,f,ps,r) = el i cls in
      let _,tmi,_ = term_match [] (list_mk_comb(f,ps)) (list_mk_comb(f,args)) in
      let ren = mapfilter (fun (t,x) -> if is_var t then (x,t) else fail()) tmi in
      let args' = map (vsubst ren) args in
      let tmi' = map (fun (t,x) -> vsubst ren t,x) tmi in
      mk_eq(list_mk_comb(f,args'),vsubst tmi' r)) leaves);;

(* the clauses of each defined function completed separately (functions in *)
(* the order of their first clause); tm itself if nothing overlaps          *)

let complete_all_clauses tm =
  let cls = dest_clauses tm in
  let rec order acc l = match l with
      [] -> rev acc
    | (_,f,_,_)::t -> if mem f acc then order acc t else order (f::acc) t in
  let fns = order [] cls in
  let groups = map (fun f -> filter (fun (_,g,_,_) -> g = f) cls) fns in
  let res = map (fun g ->
      match (try complete_clauses g with Failure _ -> None) with
        Some c -> c,true
      | None -> map (fun (vs,f,a,r) -> list_mk_forall(vs,mk_eq(list_mk_comb(f,a),r))) g,
                false) groups in
  if exists snd res then list_mk_conj (flat (map fst res)) else tm;;

let cake_def_gen (rel_tac : (term * tactic) option) (tm:term) : thm =
  let tm = rename_wildcards (cases_of_matches tm) in
  let tm = complete_all_clauses tm in
  let cls = dest_clauses tm in
  let fns = setify (map (fun (_,f,_,_) -> f) cls) in
  if length fns <> 1 then !cake_def_mutual_ref rel_tac tm else
  let f = hd fns in
  if not (is_var f) then failwith "cake_def: the defined function is a constant" else
  let name = fst(dest_var f) in
  let k = (match cls with (_,_,args,_)::_ -> length args | [] -> 0) in
  let tm = eta_expand_bare k f tm in
  let tm0 = close_clauses [f] tm in
  let cls0 = dest_clauses tm0 in
  let recursive = exists (fun (_,_,_,r) -> free_in f r) cls0 in
  let single_var_clause =
    match cls0 with
      [(_,_,args,_)] -> forall is_var args &&
                        length (setify args) = length args
    | _ -> false in
  if not recursive && single_var_clause then
    (* quantified in the order of the arguments, as HOL4 does *)
    let th = new_definition (snd(strip_forall tm0)) in
    let vs = frees_in_order (lhs(snd(strip_forall(concl th)))) in
    GENL vs (SPEC_ALL th)
  else
  let cth = if !cake_case_to_match then CASE_TO_MATCH_CONV tm0 else REFL tm0 in
  let tm_m = rand(concl cth) in
  let etm = mk_exists(f,tm_m) in
  let eth0 = if rel_tac = None then prove_general_recursive_function_exists etm
             else pure_prove_recursive_function_exists etm in
  let eth,wfinfo = discharge_hyps name rel_tac eth0 in
  if not (aconv (concl eth) etm) then
    failwith "cake_def: the existence theorem is not about the clauses" else
  let eth' = EQ_MP (SYM (MK_EXISTS f cth)) eth in
  let def = new_specification [name] eth' in
  (match wfinfo with
     Some(wfth,tc_thms) when recursive ->
       let c = mk_const(name,[]) in
       let c = inst (type_match (type_of c) (type_of f) []) c in
       let clauses = map (fun (vs,_,args,_) -> vs,args) cls0 in
       cake_ind_debug := Some(c,clauses,tc_thms,wfth);
       (try let ind = derive_induction c clauses tc_thms wfth in
            cake_ind_store := (name,ind) :: !cake_ind_store
        with Failure msg ->
          Format.print_string("Warning: cake_def "^name^
                              ": no induction theorem ("^msg^")\n"))
   | None when recursive && rel_tac = None ->
       (* termination was automatic: look for a size measure for the       *)
       (* induction theorem                                               *)
       (try
          let eth_p = pure_prove_recursive_function_exists etm in
          let h = find is_wf_hyp (hyp eth_p) in
          let rel,_ = dest_exists h in
          let ty = fst(dest_fun_ty(type_of rel)) in
          let c = mk_const(name,[]) in
          let c = inst (type_match (type_of c) (type_of f) []) c in
          let clauses = map (fun (vs,_,args,_) -> vs,args) cls0 in
          let saved = !cake_quiet in
          let rec go l = match l with
              [] -> ()
            | r::rest ->
                let ok =
                  try let _,info =
                        (cake_quiet := true;
                         let res = discharge_hyps name (Some(r,TERM_TAC)) eth_p in
                         cake_quiet := saved; res) in
                      (match info with
                         Some(wfth,tcs) ->
                           let ind = derive_induction c clauses tcs wfth in
                           cake_ind_store := (name,ind) :: !cake_ind_store; true
                       | None -> false)
                  with Failure _ -> (cake_quiet := saved; false) in
                if ok then () else go rest in
          go (measure_candidates ty)
        with Failure _ -> ())
   | None when recursive ->
       Format.print_string("Warning: cake_def "^name^": no induction theorem "^
         "(the strict form R a p of a tail-call termination condition was not "^
         "proved by the tactic)\n")
   | _ -> ());
  CONV_RULE (DEPTH_CONV ETA_MARKED_CONV) def;;

(* cake_def (with its size-measure fallback) is at the end of this file *)

let cake_def_wf r tac tm = cake_def_gen (Some(r,tac)) tm;;

(* clauses parsed one by one: in one quotation a variable name has one type, *)
(* while HOL4 types each clause separately (n : num in one clause and        *)
(* n : bool in another)                                                     *)

let cake_def_wf_clauses r tac tms = cake_def_wf r tac (list_mk_conj tms);;

(* ------------------------------------------------------------------------- *)
(* Mutual recursion: f1 .. fk are encoded as one function on the sum of     *)
(* their tupled argument types, returning the sum of their result types     *)
(* (the encoding of HOL4's Define; the relation of cake_def_wf is on that   *)
(* sum: INL (args of f1), INR (INL (args of f2)), ..., INR (.. (INR ..)).   *)
(* ------------------------------------------------------------------------- *)

let SUM_CASE_FORALL = prove
 (`!(f:A->bool) (g:B->bool).
     (!x. sum_CASE x f g) <=> (!a. f a) /\ (!b. g b)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `INL (a:A):A+B`) THEN REWRITE_TAC[sum_CASE];
    FIRST_X_ASSUM(MP_TAC o SPEC `INR (b:B):A+B`) THEN REWRITE_TAC[sum_CASE];
    STRUCT_CASES_TAC(ISPEC `x:A+B` sum_case_info.ci_nchotomy) THEN
    ASM_REWRITE_TAC[sum_CASE]]);;

let mk_sum_ty tys = end_itlist (fun a b -> mk_type("sum",[a;b])) tys;;

let mk_tuple_ty tys = end_itlist (fun a b -> mk_type("prod",[a;b])) tys;;

(* injection of t (of type el i tys) into the sum of tys *)

let rec mk_sum_inj tys i t =
  match tys with
    [_] -> t
  | ty::rest ->
      let sty = mk_sum_ty rest in
      let fty = mk_type("sum",[ty;sty]) in
      if i = 0 then mk_comb(mk_const("INL",[ty,aty; sty,bty]),t)
      else mk_comb(mk_const("INR",[ty,aty; sty,bty]),mk_sum_inj rest (i-1) t)
  | [] -> failwith "mk_sum_inj";;

(* projection of the i-th component out of the sum t *)

let rec mk_sum_proj tys i t =
  match tys with
    [_] -> t
  | ty::rest ->
      let sty = mk_sum_ty rest in
      if i = 0 then mk_comb(mk_const("OUTL",[ty,aty; sty,bty]),t)
      else mk_sum_proj rest (i-1) (mk_comb(mk_const("OUTR",[ty,aty; sty,bty]),t))
  | [] -> failwith "mk_sum_proj";;

(* (!t:A1#..#An. body) as !x1..xn. body[(x1,..,xn)/t], exactly n-1 levels  *)

let rec FORALL_TUPLE_CONV n tm =
  if n <= 1 then REFL tm else
  (GEN_REWRITE_CONV I [FORALL_PAIR_THM] THENC
   BINDER_CONV (FORALL_TUPLE_CONV (n - 1))) tm;;

let cake_def_mutual (rel_tac : (term * tactic) option) (tm:term) : thm =
  let fns0 = setify (map (fun (_,f,_,_) -> f) (dest_clauses tm)) in
  let tm = close_clauses fns0 tm in
  (* variables of the same name and different types in different clauses   *)
  (* (x3:pat in one function, x3:pat list in the other) are renamed apart:  *)
  (* the recursion package puts them into one tuple                         *)
  let tm =
    let seen = ref ([] : (string * hol_type) list) in
    list_mk_conj (map (fun cl ->
      let vs,bod = strip_forall cl in
      let ren = mapfilter (fun v ->
          let n,ty = dest_var v in
          if exists (fun (n',ty') -> n' = n && ty' <> ty) (!seen) then
            let names = map fst (!seen) @ map (fst o dest_var) (variables bod) in
            let rec go m = if mem m names then go (m ^ "'") else m in
            let v' = mk_var(go n,ty) in
            seen := (fst(dest_var v'),ty) :: !seen; (v',v)
          else (seen := (n,ty) :: !seen; fail())) vs in
      let vs' = map (fun v -> try rev_assoc v ren with Failure _ -> v) vs in
      list_mk_forall(vs',vsubst ren bod)) (conjuncts tm)) in
  let cls = dest_clauses tm in
  let fns = rev (itlist (fun (_,f,_,_) l -> if mem f l then l else f::l)
                        (rev cls) []) in
  let fns = rev fns in
  let fns = (* in order of first occurrence *)
    let rec order acc l = match l with
        [] -> rev acc
      | (_,f,_,_)::t -> if mem f acc then order acc t else order (f::acc) t in
    order [] cls in
  if exists (fun f -> not (is_var f)) fns then
    failwith "cake_def: a defined function is a constant" else
  let k = length fns in
  let arity f = let (_,_,args,_) = find (fun (_,g,_,_) -> g = f) cls in
                length args in
  let ns = map arity fns in
  let split_ty f n = let tys,r = splitlist dest_fun_ty (type_of f) in
                     let a,b = chop_list n tys in
                     a, itlist mk_fun_ty b r in
  let sigs = map2 split_ty fns ns in
  let argtups = map (fun (a,_) -> mk_tuple_ty a) sigs in
  let restys = map snd sigs in
  let sty = mk_sum_ty argtups and rty = mk_sum_ty restys in
  let names = map (fst o dest_var) fns in
  let fname = end_itlist (fun a b -> a^"_"^b) names ^ "_MUTREC" in
  let ff = mk_var(fname,mk_fun_ty sty rty) in
  (* f_j as a function of the combined function *)
  let encode i f =
    let n = el i ns and (atys,_) = el i sigs in
    let xs = map2 (fun ty j -> mk_var("x_mr"^string_of_int j,ty)) atys (1--n) in
    list_mk_abs(xs,mk_sum_proj restys i
                     (mk_comb(ff,mk_sum_inj argtups i (mk_tuple_term xs)))) in
  let substs = map2 (fun f i -> encode i f,f) fns (0--(k-1)) in
  let beta_new t = rhs(concl(TOP_DEPTH_CONV BETA_CONV t)) in
  let fclause (vs,f,args,r) =
    let i = index f fns in
    let lhs_ = mk_comb(ff,mk_sum_inj argtups i (mk_tuple_term args)) in
    let r' = mk_sum_inj restys i (beta_new (vsubst substs r)) in
    list_mk_forall(vs,mk_eq(lhs_,r')) in
  let ftm = list_mk_conj(map fclause cls) in
  let fdef = cake_def_gen rel_tac ftm in
  let fconst = mk_const(fname,[]) in
  let fconst = inst (type_match (type_of fconst) (type_of ff) []) fconst in
  (* the definitions of the f_i *)
  let fdefs = map2 (fun f i ->
      let n = el i ns and (atys,_) = el i sigs in
      let xs = map2 (fun ty j -> mk_var("x"^string_of_int j,ty)) atys (1--n) in
      let r = mk_sum_proj restys i
                (mk_comb(fconst,mk_sum_inj argtups i (mk_tuple_term xs))) in
      new_definition (mk_eq(list_mk_comb(f,xs),r)))
    fns (0--(k-1)) in
  let consts = map (fun f -> let c = mk_const(fst(dest_var f),[]) in
                             inst (type_match (type_of c) (type_of f) []) c)
                   fns in
  let csubst = zip consts fns in
  (* the clauses of the f_i *)
  let fold_conv = PURE_REWRITE_CONV (map GSYM fdefs) in
  let clause_thm (vs,f,args,r) =
    let i = index f fns in
    let tm = vsubst csubst (list_mk_forall(vs,mk_eq(list_mk_comb(f,args),r))) in
    prove(tm,
      REPEAT GEN_TAC THEN
      CONV_TAC(LAND_CONV(REWR_CONV (SPEC_ALL (el i fdefs)) THENC
                         RAND_CONV(PURE_ONCE_REWRITE_CONV[fdef]) THENC
                         PURE_REWRITE_CONV[OUTL; OUTR] THENC fold_conv)) THEN
      REFL_TAC) in
  let def = end_itlist CONJ (map clause_thm cls) in
  (* the induction theorem *)
  (try
     let find = cake_ind fname in
     let ps = map2 (fun f (atys,_) ->
                      mk_var("P"^fst(dest_var f),itlist mk_fun_ty atys bool_ty))
                   fns sigs in
     let pfun i =
       let n = el i ns in
       let t = mk_var("t_mr",el i argtups) in
       mk_abs(t,list_mk_comb(el i ps,if n = 1 then [t]
                                     else tuple_selectors n t)) in
     let rec qterm l i = match l with
         [_] -> pfun i
       | _::rest ->
           let s = mk_var("s_mr",mk_sum_ty l) in
           let a = pfun i and b = qterm rest (i+1) in
           mk_abs(s,list_mk_icomb "sum_CASE" [s;a;b])
       | [] -> failwith "qterm" in
     let q = qterm argtups 0 in
     let th1 = ISPEC q find in
     let th2 = CONV_RULE (TOP_DEPTH_CONV BETA_CONV THENC
                          PURE_REWRITE_CONV[sum_CASE; FST; SND] THENC
                          TOP_DEPTH_CONV BETA_CONV THENC
                          PURE_REWRITE_CONV[FST; SND] THENC fold_conv) th1 in
     let rec split_conv l = match l with
         [_] -> ALL_CONV
       | _::rest -> GEN_REWRITE_CONV I [SUM_CASE_FORALL] THENC
                    RAND_CONV (split_conv rest) in
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
     let th5 = GENL ps th4 in
     do_list (fun n -> cake_ind_store := (n,th5) :: !cake_ind_store) names
   with Failure msg ->
     Format.print_string("Warning: cake_def "^fname^
                         ": no mutual induction theorem ("^msg^")\n"));
  def;;

cake_def_mutual_ref := cake_def_mutual;;

(* cake_def: termination by HOL Light's own analysis, else (as HOL4's       *)
(* Define does) by a size measure: for one function the size of one       *)
(* argument or of all of them, for mutual recursion (on the sum of the     *)
(* argument tuples) the size of all the arguments or of the first one of   *)
(* each function                                                            *)

let sum_measure_candidates (tys:hol_type list) =
  let num = `:num` in
  let whole ty = size_of_type [] ty in
  let first ty = match dest_type ty with
      "prod",[a;b] -> let t = mk_var("t_ms",ty) in
                      mk_abs(t,mk_comb(size_of_type [] a,
                                       mk_comb(mk_const("FST",[a,aty; b,bty]),t)))
    | _ -> whole ty in
  let rec combine tys fs = match tys,fs with
      [_],[f] -> f
    | ty::tys',f::fs' ->
        let g = combine tys' fs' in
        let sty' = fst(dest_fun_ty(type_of g)) in
        let sty = mk_type("sum",[ty;sty']) in
        let s = mk_var("s_ms",sty) in
        let c0 = mk_const("sum_CASE",[]) in
        let cty = mk_fun_ty sty (mk_fun_ty (mk_fun_ty ty num)
                                   (mk_fun_ty (mk_fun_ty sty' num) num)) in
        let c = inst (type_match (type_of c0) cty []) c0 in
        mk_abs(s,list_mk_comb(c,[s;f;g]))
    | _ -> failwith "sum_measure_candidates" in
  let ms = [combine tys (map whole tys); combine tys (map first tys)] in
  map (fun m -> mk_comb(mk_const("measure",[fst(dest_fun_ty(type_of m)),aty]),m)) ms;;

let cake_has_substring s sub =
  let n = String.length s and m = String.length sub in
  let rec go i = i + m <= n && (String.sub s i m = sub || go (i + 1)) in
  go 0;;

let cake_def tm =
  let saved = !cake_quiet in
  try cake_quiet := true;
      let th = cake_def_gen None tm in
      cake_quiet := saved; th
  with Failure msg ->
    cake_quiet := saved;
    if not (cake_has_substring msg "termination not proved") then failwith msg else
    let cls = dest_clauses (rename_wildcards (cases_of_matches tm)) in
    let rec order acc l = match l with
        [] -> rev acc
      | (_,f,_,_)::t -> if mem f acc then order acc t else order (f::acc) t in
    let fns = order [] cls in
    let argty f =
      let k = match find (fun (_,g,_,_) -> g = f) cls with (_,_,args,_) -> length args in
      mk_tuple_ty (fst(chop_list k (fst(splitlist dest_fun_ty (type_of f))))) in
    let cands = try if length fns = 1 then measure_candidates (argty (hd fns))
                    else sum_measure_candidates (map argty fns)
                with Failure _ -> [] in
    let rec go l = match l with
        [] -> cake_def_gen None tm
      | r::rest ->
          (try cake_quiet := true;
               let th = cake_def_gen (Some(r,TERM_TAC)) tm in
               cake_quiet := saved; th
           with Failure _ -> (cake_quiet := saved; go rest)) in
    go cands;;

let cake_def_clauses tms = cake_def (list_mk_conj tms);;

(* ------------------------------------------------------------------------- *)
(* Inductive relations (HOL4 Inductive foo ... End): new_inductive_definition *)
(* on the match-compiled term; returns foo_rules, foo_ind, foo_cases and     *)
(* foo_strongind.                                                            *)
(* ------------------------------------------------------------------------- *)

let cake_inductive tm =
  let rules,ind,cases = new_inductive_definition (cases_of_matches tm) in
  if hyp rules <> [] then
    failwith ("cake_inductive: no monotonicity theorem for a premise; add one "^
              "to monotonicity_theorems first: "^
              string_of_term (hd(hyp rules))) else
  let strongind = try derive_strong_induction(rules,ind)
                  with Failure _ -> ind in
  rules,ind,cases,strongind;;
