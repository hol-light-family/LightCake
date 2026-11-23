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
(* HOL4 measure is HOL Light's MEASURE (wf.ml), with WF_MEASURE; the kit     *)
(* keeps measure_THM (HOL4 measure_thm) for it.                              *)
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

(* HOL4's measure is HOL Light's MEASURE (wf.ml: MEASURE m = \x y. m x < m y, *)
(* with WF_MEASURE); measure_THM is HOL4's measure_thm for it               *)

let measure_THM = prove
 (`!(f:A->num) x y. MEASURE f x y <=> f x < f y`,
  REWRITE_TAC[MEASURE]);;

let WF_LT_NUM = prove
 (`WF ((<):num->num->bool)`,
  REWRITE_TAC[WF_num]);;

(* the automatic proof of WF R, for R built from the combinators above *)

(* and of relations whose well-foundedness was proved by hand and          *)
(* registered with cake_register_wf (HOL4 termination relations that are   *)
(* not built from MEASURE, inv_image and LEX)                               *)

let cake_extra_wf = ref ([] : thm list);;

let cake_register_wf th = cake_extra_wf := th :: !cake_extra_wf;;

let WF_TAC : tactic =
  REPEAT (MATCH_ACCEPT_TAC WF_LT_NUM ORELSE MATCH_ACCEPT_TAC WF_MEASURE ORELSE
          MATCH_ACCEPT_TAC WF_FALSE ORELSE
          MATCH_MP_TAC WF_inv_image ORELSE MATCH_MP_TAC WF_LEX_HOL4 ORELSE
          MATCH_MP_TAC WF_MEASURE_GEN ORELSE CONJ_TAC ORELSE
          (fun g -> MAP_FIRST MATCH_ACCEPT_TAC (!cake_extra_wf) g));;

(* the rewrites that unfold the combinators in termination conditions *)

let WF_REL_THMS = [inv_image_THM; LEX_THM; measure_THM; MEASURE];;

(* terms used by the functions below, parsed once: parsing in a session with *)
(* thousands of constants takes milliseconds per quotation                   *)

let cake_true_tm = `T` and cake_zero_tm = `0:num` and cake_num_ty = `:num`;;

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

(* the rewriting of TERM_TAC with every size function, built once per state *)
(* of the size tables (and of the basic rewrites) instead of twice per goal *)

let cake_term_rw_cache =
  ref (None : (thm list * (string * thm list) list * gconv net * conv) option);;

let cake_term_rw_conv () =
  match !cake_term_rw_cache with
    Some(d,a,b,c) when d == !the_size_defs && a == !the_size_aux_eqs &&
                       b == basic_net() -> c
  | _ ->
      let ths = WF_REL_THMS @ [FST; SND; pair_size_THM; sum_CASE] @
                !the_size_defs @ flat (map snd (!the_size_aux_eqs)) in
      let c = REWRITE_CONV ths in
      cake_term_rw_cache := Some(!the_size_defs,!the_size_aux_eqs,basic_net(),c);
      c;;

let TERM_TAC : tactic =
  REPEAT BOSS_STRIP_TAC THEN RVEQ_TAC THEN
  (fun g -> let c = cake_term_rw_conv () in
            (RULE_ASSUM_TAC(CONV_RULE c) THEN CONV_TAC c) g) THEN
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
        let ctx,c = if is_imp bod then dest_imp bod else cake_true_tm,bod in
        if is_forall c then
          let y,b = dest_forall c in
          let ra,rp = dest_imp b in
          let a = rand ra in
          let r0 = rator(rator ra) in
          let p = rand rp in
          let stm = list_mk_forall(vs,
                      if ctx = cake_true_tm then mk_comb(mk_comb(r0,a),p)
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

(* an existential that no prover can prove because it is false for some     *)
(* value of a free variable: ?xs. .. /\ v = C .. /\ .. with v free, not in   *)
(* the C term, of a datatype with another constructor D (false for v := D zs) *)
(* MESON fails on it anyway, after its whole search (40 s for ?s'. y' =      *)
(* SX_CONS s' s'' in fromSexp)                                               *)

let cake_existential_refutable w =
  try
    let xs,bod = strip_exists w in
    let test v t =
      is_var v && not (mem v xs) && not (free_in v t) &&
      (let h = fst(strip_comb t) in
       is_const h &&
       let ci = case_info_of_tyname (fst(dest_type(type_of v))) in
       length ci.ci_pats >= 2 &&
       exists (fun (_,p) -> let h' = fst(strip_comb p) in
                            is_const h' && fst(dest_const h') = fst(dest_const h))
              ci.ci_pats) in
    exists (fun c -> is_eq c && (test (lhs c) (rhs c) || test (rhs c) (lhs c)))
           (conjuncts bod)
  with Failure _ -> false;;

let tidy_ctx ctx =
  if ctx = cake_true_tm then ctx,DISCH ctx (ASSUME ctx) else
  try
    let cs = conjuncts ctx in
    let orient c =
      if is_eq c && is_constructor_app (lhs c) && not (is_constructor_app (rhs c))
      then mk_eq(rhs c,lhs c) else c in
    let cs1 = map orient cs in
    (* the case rewrites come from the kit's prebuilt net (CASE_REWRITE_TAC): *)
    (* rebuilding a net of all of them for each conjunct costs about a second *)
    (* once a type with many constructors is defined                          *)
    let exists_meson ths = W(fun (_,w) -> if is_exists w &&
                                             not (cake_existential_refutable w)
                                          then MESON_TAC ths else NO_TAC) in
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
(* unprimed name is free, and is not another of the variables vs (with the  *)
(* same type: the two would become one variable, as y' and y did in the IH  *)
(* of a let (y,k) = (y + 1,n) in .. under match x with SOME y, which gave   *)
(* !y y k. x = SOME y /\ (y + 1,n) = (y,k) ==> ..; since 2026-11-18)        *)

let cake_ind_unprime_log = ref false and cake_ind_unprime_kept = ref false;;

let unprime_vars avoid vs =
  let rec base n = let k = String.length n in
    if k > 1 && n.[k-1] = '\'' then base (String.sub n 0 (k-1)) else n in
  let used = ref (map (fst o dest_var) avoid) in
  map (fun v -> let n,ty = dest_var v in
                let b = base n in
                let clash = b <> n && mem (mk_var(b,ty)) vs in
                (if clash && not (mem b !used) then cake_ind_unprime_kept := true);
                let n' = if mem b !used || clash then n else b in
                used := n' :: !used; mk_var(n',ty)) vs;;

let cake_ind_dbg = ref (None : (term * thm * (int option -> tactic) * term list list * (term * thm * bool) list list) option);;

(* the variables of the conclusion !x1 .. xn. P x1 .. xn of an induction     *)
(* theorem (of each conjunct, for mutual recursion) are named apart from     *)
(* the variables of the cases and from each other: before, ordav_ind had     *)
(* !x1 x2 x3. P x1 x2 x3 with x2 a variable of its cases too, and            *)
(* MATCH_MP_TAC (whose match renames the bound variables of the conclusion   *)
(* to the goal's) also renamed that one, so the cases got two variables      *)
(* named env.  HOL4's conclusions are !v v1 .. (TFL's vary).  An             *)
(* alpha-equivalent theorem.  Since 2026-11-22.                              *)
let kit_ind_concl_apart (th:thm) : thm =
  try
    let ps,body = strip_forall (concl th) in
    let ant,cn = dest_imp body in
    let used = ref (map (fst o dest_var) (variables ant @ ps @ variables cn)) in
    let fresh = ref (map (fst o dest_var) (variables ant @ ps)) in
    let changed = ref false in
    let fix c =
      let vs,b = strip_forall c in
      let vs' = map (fun v ->
          let n,ty = dest_var v in
          if mem n !fresh then
            let rec go m = if mem m !used then go (m ^ "'") else m in
            let n' = go n in
            changed := true; used := n' :: !used; fresh := n' :: !fresh; mk_var(n',ty)
          else (fresh := n :: !fresh; v)) vs in
      if vs' = vs then c else list_mk_forall(vs',vsubst (zip vs' vs) b) in
    let cn' = list_mk_conj (map fix (conjuncts cn)) in
    if not !changed then th else
    let th' = EQ_MP (ALPHA (concl th) (list_mk_forall(ps,mk_imp(ant,cn')))) th in
    kit_note "cake_ind: conclusion variables named apart"; th'
  with Failure _ -> th;;

let derive_induction (c:term) (clauses:(term list * term list) list)
                     (tc_thms:thm list) (wfth:thm) =
  cake_ind_unprime_kept := false;
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
    let ctx,rc = if is_imp bod then dest_imp bod else cake_true_tm,bod in
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
    if ctx = cake_true_tm then i,ctx1,aargs1,th else
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
    let body = if ctx = cake_true_tm then list_mk_comb(p,aargs)
               else mk_imp(ctx,list_mk_comb(p,aargs)) in
    let evs = subtract (frees body) (p :: pv) in
    let evs' = unprime_vars (pv @ (subtract (frees body) evs)) evs in
    (* a variable named like the defined function (the recursion package    *)
    (* sometimes names one so) gets a v-name                                *)
    let cname = try fst(dest_const c) with Failure _ ->
                try fst(dest_var c) with Failure _ -> "" in
    let evs' =
      let used = ref (map (fst o dest_var) (pv @ evs' @ frees body)) in
      map (fun v -> let n,ty = dest_var v in
                    if n <> cname then v else
                    let rec go k = let m = "v" ^ string_of_int k in
                                   if mem m !used then go (k+1) else m in
                    let m = go 1 in used := m :: !used; mk_var(m,ty)) evs' in
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
          else dedup ((ih,th,ctx = cake_true_tm)::acc) t in
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
  (if !cake_ind_unprime_log && !cake_ind_unprime_kept then
     Format.print_string ("INDFIX "^(try fst(dest_const c) with Failure _ ->
                                         try fst(dest_var c) with Failure _ -> "?")^"\n"));
  kit_ind_concl_apart (prove(stmt,
    GEN_TAC THEN DISCH_THEN(fun th ->
      MAP_EVERY (fun (k,c) -> LABEL_TAC ("case"^string_of_int k) c)
                (zip (0--(length allcases - 1)) (CONJUNCTS th))) THEN
    MATCH_MP_TAC cind THEN REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "wfh") THEN
    SPLIT_PATTERNS_TAC pats leaf));;

(* ------------------------------------------------------------------------- *)
(* cake_ind_tidy th (opt-in; since 2026-11-22): the induction theorem th     *)
(* without the induction hypotheses that another hypothesis of the same      *)
(* case implies (the same variables and conclusion, a subset of its          *)
(* conditions): after lets are unfolded a recursive call can occur several   *)
(* times, each with a stronger context (INST_CORE's call in a let, then in   *)
(* if IS_RESULT tres then .. RESULT tres else tres), and each gave its own   *)
(* hypothesis.  HOL4's TFL gives one per call.  The result is logically      *)
(* equivalent; cake_ind itself is unchanged (stored theorems of existing     *)
(* files stay as they are): write let f_ind = cake_ind_tidy (cake_ind "f").  *)
(* ------------------------------------------------------------------------- *)

let cake_ind_tidy (th:thm) : thm =
  let ps,body = strip_forall (concl th) in
  let ant,cn = dest_imp body in
  let cases = conjuncts ant in
  let parts h = let ws,b = strip_forall h in
                if is_imp b then ws,conjuncts (fst(dest_imp b)),snd(dest_imp b)
                else ws,[],b in
  let implies hi hj =
    let wi,ci,gi = parts hi and wj,cj,gj = parts hj in
    wi = wj && aconv gi gj && forall (fun c -> exists (aconv c) cj) ci in
  let tidy_case c =
    let vs,b = strip_forall c in
    if not (is_imp b) then c else
    let ihs,cc = dest_imp b in
    let hs = Array.of_list (conjuncts ihs) in
    let n = Array.length hs in
    let keep j = not (exists (fun i -> i <> j && implies hs.(i) hs.(j) &&
                                       (i < j || not (implies hs.(j) hs.(i))))
                            (0--(n-1))) in
    let hs' = map (fun j -> hs.(j)) (filter keep (0--(n-1))) in
    if length hs' = n then c else list_mk_forall(vs,mk_imp(list_mk_conj hs',cc)) in
  let cases' = map tidy_case cases in
  if cases' = cases then th else
  let ant' = list_mk_conj cases' in
  let cths = CONJUNCTS (ASSUME ant') in
  let old_case (c,c',cth) =
    if c = c' then cth else
    let vs,b = strip_forall c in
    let ihs,_ = dest_imp b in
    let hs' = conjuncts (fst(dest_imp(snd(strip_forall c')))) in
    let parts = CONJUNCTS (ASSUME ihs) in
    let pth = end_itlist CONJ (map (fun h -> find (fun t -> aconv (concl t) h) parts) hs') in
    GENL vs (DISCH ihs (MP (SPECL vs cth) pth)) in
  let cth = end_itlist CONJ (map2 (fun (c,c') t -> old_case (c,c',t)) (zip cases cases') cths) in
  GENL ps (DISCH ant' (MP (SPECL ps th) cth));;

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
  let zero s = (try snd(dest_abs s) = cake_zero_tm with Failure _ -> false) in
  let one k =
    let s = size_of_type [] (el k cs) in
    if zero s then failwith "" else
    let body = rhs(concl(TOP_DEPTH_CONV BETA_CONV (mk_comb(s,el k sels)))) in
    mk_comb(mk_const("MEASURE",[ty,aty]),mk_abs(t,body)) in
  let whole = let s = size_of_type [] ty in
              if zero s then [] else [mk_comb(mk_const("MEASURE",[ty,aty]),s)] in
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

(* ------------------------------------------------------------------------- *)
(* Non-recursive clauses by a case tree, as HOL4's TFL does: the clauses of  *)
(* f are compiled into one case tree on fresh argument variables (first      *)
(* match wins, ARB where no clause matches), each clause is proved from the  *)
(* equation f x1 .. xn = tree by rewriting with the case equations, and only *)
(* then f is defined by that equation.  The result is the theorem of the     *)
(* recursion package's route (the clauses as given), without its well-       *)
(* definedness condition for every pair of clauses over the variables of all *)
(* of them.  Fails (before anything is defined) if a clause is not proved,   *)
(* for example with literal patterns; cake_def then takes the other route.   *)
(* ------------------------------------------------------------------------- *)

let cake_tfl_nonrec = ref true;;

let cake_tfl_tree (avoid:term list ref) (f:term)
                  (cls:(term list * term * term list * term) list) =
  let n = match cls with (_,_,args,_)::_ -> length args
                       | [] -> failwith "cake_tfl_tree" in
  let tys,r = splitlist dest_fun_ty (type_of f) in
  let atys,btys = chop_list n tys in
  let rty = itlist mk_fun_ty btys r in
  let xs = map2 (fun ty j ->
      let base = match cls with
          (_,_,args,_)::_ when is_var (el j args) -> fst(dest_var (el j args))
        | _ -> "x"^string_of_int (j + 1) in
      pm_fresh avoid (mk_var(base,ty))) atys (0--(n-1)) in
  let counter = ref 0 in
  let rows = map (fun (_,_,args,r) ->
      let pvs = filter (fun v -> not (is_wildcard v)) (freesl args) in
      let ren = map (fun v -> incr counter;
                       mk_var(fst(dest_var v)^"%pm"^string_of_int !counter,
                              type_of v),v) pvs in
      {pm_pats = map (vsubst ren) args; pm_guard = None;
       pm_rhs = vsubst ren r}) cls in
  let avoid0 = !avoid @ flat (map (fun r -> freesl r.pm_pats) rows) in
  xs,compile_rows avoid0 xs rows (mk_const("ARB",[rty,aty]));;

let cake_tfl_define (f:term) (tm0:term) cls0 : thm =
  let name = fst(dest_var f) in
  let xs,body = cake_tfl_tree (ref (frees tm0)) f cls0 in
  let deq = mk_eq(list_mk_comb(f,xs),body) in
  let dtm = list_mk_forall(xs,deq) in
  let imps = map (fun cl ->
      prove(mk_imp(dtm,cl),
            DISCH_THEN(fun dth -> REPEAT GEN_TAC THEN
                         GEN_REWRITE_TAC LAND_CONV [dth] THEN
                         CASE_REWRITE_TAC[] THEN TRY REFL_TAC THEN NO_TAC)))
    (conjuncts tm0) in
  let def = new_definition deq in
  let c = mk_const(name,[]) in
  let c = inst (type_match (type_of c) (type_of f) []) c in
  (* new_definition may quantify the arguments in another order *)
  let def' = GENL xs (SPEC_ALL def) in
  end_itlist CONJ (map (fun th -> MP (INST [c,f] th) def') imps);;

(* ------------------------------------------------------------------------- *)
(* A recursive definition without a relation (cake_def): HOL Light's        *)
(* automatic termination proof first, then the induction theorem from the   *)
(* first size measure (measure_candidates) whose termination conditions     *)
(* TERM_TAC proves (with the strict forms) and for which derive_induction   *)
(* succeeds; if the automatic proof fails, cake_def defines the function    *)
(* with the first measure whose conditions TERM_TAC proves.  The measures   *)
(* are tried first here and the automatic proof (often seconds, and         *)
(* useless when a measure works) only when it decides the result: same     *)
(* definitions and induction theorems.  eth_p is the existence theorem of    *)
(* the recursion package with its WF hypothesis.                             *)
(* ------------------------------------------------------------------------- *)

let cake_candidates_first = ref true;;

let cake_def_auto name (f:term) (cth:thm) (etm:term) cls0 (eth_p:thm) : thm =
  let define_from eth =
    if not (aconv (concl eth) etm) then
      failwith "cake_def: the existence theorem is not about the clauses" else
    new_specification [name] (EQ_MP (SYM (MK_EXISTS f cth)) eth) in
  let the_const () = let c = mk_const(name,[]) in
                     inst (type_match (type_of c) (type_of f) []) c in
  let clauses = map (fun (vs,_,args,_) -> vs,args) cls0 in
  let finish def = CONV_RULE (DEPTH_CONV ETA_MARKED_CONV) def in
  let h = find is_wf_hyp (hyp eth_p) in
  let ty = fst(dest_fun_ty(type_of(fst(dest_exists h)))) in
  let cands = try measure_candidates ty with Failure _ -> [] in
  let saved = !cake_quiet in
  let attempt r =
    try cake_quiet := true;
        let res = discharge_hyps name (Some(r,TERM_TAC)) eth_p in
        cake_quiet := saved; Some res
    with Failure _ -> (cake_quiet := saved; None) in
  let rec first l = match l with
      [] -> None
    | r::rest -> (match attempt r with Some res -> Some(res,rest)
                                     | None -> first rest) in
  (* after the automatic proof: the first measure with an induction theorem *)
  let rec a_loop l = match l with
      [] -> ()
    | r::rest ->
        let ok = match attempt r with
            Some(_,Some(wfth,tcs)) ->
              (try let ind = derive_induction (the_const()) clauses tcs wfth in
                   cake_ind_store := (name,ind) :: !cake_ind_store; true
               with Failure _ -> false)
          | _ -> false in
        if ok then () else a_loop rest in
  match first cands with
    Some((eth1,info1),rest) ->
      let def = define_from eth1 in
      let auto_ok () = can cake_guess_wf_hyp eth_p in
      (match info1 with
         Some(wfth,tc_thms) ->
           let c = the_const() in
           cake_ind_debug := Some(c,clauses,tc_thms,wfth);
           let msg = ref "" in
           (match (try Some(derive_induction c clauses tc_thms wfth)
                   with Failure m -> (msg := m; None)) with
              Some ind -> cake_ind_store := (name,ind) :: !cake_ind_store
            | None ->
                if auto_ok () then a_loop rest else
                Format.print_string("Warning: cake_def "^name^
                                    ": no induction theorem ("^ !msg ^")\n"))
       | None ->
           if auto_ok () then a_loop rest else
           Format.print_string("Warning: cake_def "^name^": no induction theorem "^
             "(the strict form R a p of a tail-call termination condition was not "^
             "proved by the tactic)\n"));
      finish def
  | None ->
      let eth0 = try cake_guess_wf_hyp eth_p with Failure _ -> eth_p in
      let eth,_ = discharge_hyps name None eth0 in
      finish (define_from eth);;

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
  match (if recursive || not !cake_tfl_nonrec then None
         else try Some(cake_tfl_define f tm0 cls0)
              with Failure _ | Not_found | Invalid_argument _ -> None) with
    Some th -> th
  | None ->
  let cth = if !cake_case_to_match then CASE_TO_MATCH_CONV tm0 else REFL tm0 in
  let tm_m = rand(concl cth) in
  let etm = mk_exists(f,tm_m) in
  let auto_eth = if rel_tac = None && recursive && !cake_candidates_first
                 then try Some(pure_prove_recursive_function_exists etm)
                      with Failure _ -> None
                 else None in
  match (match auto_eth with
           Some eth_p when exists is_wf_hyp (hyp eth_p) -> Some eth_p
         | _ -> None) with
    Some eth_p -> cake_def_auto name f cth etm cls0 eth_p
  | None ->
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

(* Identical redefinitions (since 2026-11-20).  Each definition is stored   *)
(* with a digest of its clauses as cake_def_gen sees them (after            *)
(* cases_of_matches and rename_wildcards, up to alpha), its function        *)
(* variables replaced by the new constants.  The same clauses given again,  *)
(* in a session that holds the definition already (the functions then parse *)
(* as the constants: an image with the file, in which a changed copy of the *)
(* file or its dependents are to be checked), give the stored theorem back, *)
(* as HOL Light's define and new_definition do for a benign redefinition.   *)
(* Any other clauses for a defined constant still fail ("the defined        *)
(* function is a constant").  (Only digests are kept: the clause terms of   *)
(* every definition made the heap bigger and later loads slower.)            *)

let kit_term_digest (tm:term) : string =
  let buf = Buffer.create 4096 in
  let add = Buffer.add_string buf in
  let rec tyser ty =
    match ty with
      Tyvar n -> add "'"; add n
    | Tyapp(c,args) -> add c; add "("; do_list (fun a -> tyser a; add ",") args; add ")" in
  let rec go env t =
    match t with
      Var(n,ty) ->
        let rec idx i l =
          match l with [] -> -1 | v::r -> if v == t || v = t then i else idx (i+1) r in
        let i = idx 0 env in
        if i >= 0 then (add "B"; add (string_of_int i))
        else (add "V("; add n; add ":"; tyser ty; add ")")
    | Const(n,ty) -> add "C("; add n; add ":"; tyser ty; add ")"
    | Comb(f,x) -> add "A("; go env f; add " "; go env x; add ")"
    | Abs(v,b) -> add "L("; tyser (type_of v); add "."; go (v::env) b; add ")" in
  go [] tm; Digest.string (Buffer.contents buf);;

let cake_def_store = (Hashtbl.create 1000 : (string,(string * thm)) Hashtbl.t);;

let kit_def_store = ref true;;

let cake_def_gen =
  let cake_def_gen0 = cake_def_gen in
  fun (rel_tac : (term * tactic) option) (tm:term) ->
    if not !kit_def_store then cake_def_gen0 rel_tac tm else
    let ctm = rename_wildcards (cases_of_matches tm) in
    let head = try (match dest_clauses ctm with
                      (_,f,_,_)::_ -> if is_var f then fst(dest_var f)
                                      else fst(dest_const f)
                    | [] -> "")
               with Failure _ -> "" in
    let olds = Hashtbl.find_all cake_def_store head in
    let found =
      if olds = [] then None else
      let d = kit_term_digest ctm in
      try Some (snd (find (fun (k,_) -> k = d) olds)) with Failure _ -> None in
    match found with
      Some th -> (Format.print_string ("Warning: cake_def "^head^
                                       ": benign redefinition\n"); th)
    | None ->
        (* ctm is already compiled: cake_def_gen0's own cases_of_matches and   *)
        (* rename_wildcards leave it as it is (no second compilation)          *)
        let th = cake_def_gen0 rel_tac ctm in
        (try
           let fns = setify (filter is_var (map (fun (_,f,_,_) -> f) (dest_clauses ctm))) in
           let sub = map (fun f ->
               let c = mk_const(fst(dest_var f),[]) in
               inst (type_match (type_of c) (type_of f) []) c,f) fns in
           if sub <> [] && head <> "" then
             Hashtbl.add cake_def_store head (kit_term_digest (vsubst sub ctm),th)
         with Failure _ -> ());
        th;;

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
  (* the encoded function takes cake_def_gen's own route: cake_def's        *)
  (* fallback for mutual recursion has measures of its own                   *)
  let fdef = let saved = !cake_candidates_first in
             cake_candidates_first := false;
             try let th = cake_def_gen rel_tac ftm in
                 cake_candidates_first := saved; th
             with e -> (cake_candidates_first := saved; raise e) in
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
      (* a function that occurs bare (MAP f l) comes back as \x. f x *)
      (REFL_TAC ORELSE (CONV_TAC(TOP_DEPTH_CONV ETA_CONV) THEN REFL_TAC))) in
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
     (* with three or more functions a sum_CASE reduces to a beta-redex   *)
     (* whose reduct is a sum_CASE again: reduce until nothing changes     *)
     let step = PURE_REWRITE_CONV[sum_CASE; FST; SND] THENC
                TOP_DEPTH_CONV BETA_CONV in
     let th2 = CONV_RULE (TOP_DEPTH_CONV BETA_CONV THENC
                          REPEATC (CHANGED_CONV step) THENC
                          PURE_REWRITE_CONV[FST; SND] THENC fold_conv) th1 in
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
     let th5 = kit_ind_concl_apart (GENL ps th4) in
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
  let num = cake_num_ty in
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
  map (fun m -> mk_comb(mk_const("MEASURE",[fst(dest_fun_ty(type_of m)),aty]),m)) ms;;

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
