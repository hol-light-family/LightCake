(* ========================================================================= *)
(* CakeML kit: the project simpset and HOL4-style simplification tactics.   *)
(*                                                                           *)
(*   SIMP thl   HOL4 simp[thl]: simplify the goal with the project simpset,  *)
(*              the assumptions and thl.                                    *)
(*   FS thl     HOL4 fs[thl]: simplify each assumption (oldest first, with   *)
(*              the older ones), strip them back in, then simplify the goal. *)
(*   GVS thl    HOL4 gvs[thl]: like FS, but each assumption is simplified    *)
(*              with all the others, equations var = t are eliminated, and   *)
(*              this is repeated until nothing changes.                     *)
(*   RW thl     HOL4 rw[thl]: strip the goal, split its conditionals,        *)
(*              eliminate var equations, simplify.                           *)
(*   VAR_EQ_TAC HOL4 rveq: substitute away one assumption var = t / t = var. *)
(*   RFS thl    FS in the other order: newest first, with the newer ones    *)
(*              (this is the order of HOL4's fs; FS has the order of rfs).  *)
(*   DECIDE_TAC HOL4 decide_tac: ARITH_TAC with the arithmetic assumptions. *)
(*   ARITH_ss   a marker for the lists above: arithmetic (HOL4 ARITH_ss).   *)
(* The simplifier strategy is HOL Light's TOP_DEPTH_SQCONV without its      *)
(* redundant second pass (same results, faster); SIMP_TAC etc. use it too.  *)
(* The project simpset (HOL4's srw_ss) holds the case equations,             *)
(* distinctness and injectivity of every registered datatype, the record     *)
(* theorems, and whatever cake_add_simps registers.                         *)
(* ========================================================================= *)

(* KITNEW lines (kit_new_log := true): the places where a tactic extended *)
(* on 2026-11-18 behaves differently from before (for the full-load checks) *)

let kit_new_log = ref false;;
let kit_note (s:string) = if !kit_new_log then Format.print_string ("KITNEW "^s^"\n");;

(* KITDIFF lines (kit_check := true, for the full-load checks of changes    *)
(* made on 2026-11-20): where a changed tactic would give a different       *)
(* result, the old and the new result are both computed, a KITDIFF line is *)
(* printed when they differ, and the old one is used, so that a full load   *)
(* in check mode tells which proofs a change would affect                   *)

let kit_check = ref false;;
let kit_diff (s:string) = Format.print_string ("KITDIFF "^s^"\n");;

(* in check mode: run old () and new_ (), report a difference (by eq) and *)
(* return the old result (or raise its exception)                          *)
type 'a kit_result = Kit_ok of 'a | Kit_exn of exn;;

let kit_check_results (name:string) (eq:'a -> 'a -> bool) (r_old:'a kit_result)
                      (r_new:'a kit_result) : 'a =
  (match r_old,r_new with
     Kit_ok a,Kit_ok b -> if not (eq a b) then kit_diff (name ^ ": different results")
   | Kit_ok _,Kit_exn _ -> kit_diff (name ^ ": the new one fails")
   | Kit_exn _,Kit_ok _ -> kit_diff (name ^ ": the old one fails")
   | Kit_exn _,Kit_exn _ -> ());
  match r_old with Kit_ok a -> a | Kit_exn e -> raise e;;

let kit_check_both (name:string) (eq:'a -> 'a -> bool) (old:unit -> 'a) (new_:unit -> 'a) : 'a =
  let r_old = (try Kit_ok (old ()) with e -> Kit_exn e) in
  let r_new = (try Kit_ok (new_ ()) with e -> Kit_exn e) in
  kit_check_results name eq r_old r_new;;

(* The rewrite maker of the kit's simpsets: HOL Light's mk_rewrites, except *)
(* that no rewrite has a bare variable as its left side (one not free in    *)
(* the hypotheses, so a pattern that matches every term of its type), as in *)
(* HOL4's IMP_EQ_CANON (simp/src/Cond_rewr.sml): a conclusion b or ~b with *)
(* b such a variable (from an induction hypothesis !b. .. ==> b /\ ..) is  *)
(* not used, and an equation x = t with x such a variable (from INJ's       *)
(* !x y. .. /\ f x = f y ==> x = y) is used as (x = t) <=> T.  HOL Light's  *)
(* mk_rewrites makes b <=> T, b <=> F and x = t of them, which the          *)
(* simplifier tries at every subterm of the type, proving the condition    *)
(* each time (FS ran for minutes on such assumptions).  Since 2026-11-18.  *)

let kit_mk_rewrites =
  let mk = mk_rewrites true in
  let tf = [`T`; `F`] in
  let bad th =
    let c = concl th in
    let eqn = if is_imp c then rand c else c in
    is_eq eqn && is_var (lhs eqn) && not (mem (lhs eqn) (freesl (hyp th))) in
  let fix th =
    let c = concl th in
    let eqn = if is_imp c then rand c else c in
    if type_of (lhs eqn) = bool_ty && mem (rhs eqn) tf then []
    else if is_imp c then [DISCH (lhand c) (EQT_INTRO (UNDISCH th))]
    else [EQT_INTRO th] in
  fun th sofar ->
    let ths = mk th [] in
    if not (exists bad ths) then ths @ sofar
    else (kit_note "rewrite with a variable left side";
          flat (map (fun t -> if bad t then fix t else [t]) ths) @ sofar);;

(* HOL4's default simpsets have no SATISFY_ss: drop the satisfy_prover of HOL Light's basic_ss *)
let cake_basic_ss thl =
  let Simpset(n,p,_,_) = basic_ss thl in Simpset(n,p,[],kit_mk_rewrites);;

let K_DEF = new_definition `K = \(x:A) (y:B). x`;;

let K_THM = prove
 (`!(x:A) (y:B). K x y = x`,
  REWRITE_TAC[K_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Rewrite nets made once per theorem list.  A tactic that rewrites each      *)
(* assumption or each goal of a case split with the same long list of         *)
(* theorems (record accessor theorems, case equations, definitions) would     *)
(* canonicalize the list and build its net again at every call.  HOL Light's   *)
(* rewriting functions are redefined here with a small memo: the net of a     *)
(* list is reused for the same flag, base net and theorems (physical          *)
(* equality), so the nets and hence the results are the same; only nets that  *)
(* took some time to build are kept (the last cake_memo_keep of them).        *)
(* ------------------------------------------------------------------------- *)

let cake_memo_keep = 16 and cake_memo_min_time = 0.002;;

let cake_same_thms l1 l2 =
  let rec go a b =
    match a,b with
      [],[] -> true
    | x::a',y::b' -> x == y && go a' b'
    | _ -> false in
  go l1 l2;;

(* look up a memo (most recent first; a hit moves to the front), or make the *)
(* value and keep it if that took at least cake_memo_min_time               *)
let cake_memo (memo:('a * 'b) list ref) (key:'a -> bool) (k:'a) (make:unit -> 'b) =
  let rec split acc l =
    match l with
      [] -> None
    | (k',v as e)::t -> if key k' then Some(v, e :: List.rev_append acc t)
                        else split (e::acc) t in
  match split [] !memo with
    Some(v,l) -> memo := l; v
  | None ->
      let t0 = Sys.time() in
      let v = make() in
      (if Sys.time() -. t0 >= cake_memo_min_time then
         memo := (k,v) :: (if length !memo >= cake_memo_keep then butlast !memo
                           else !memo));
      v;;

let cake_rw_net_memo = ref ([] : ((bool * gconv net * thm list) * gconv net) list);;

let GENERAL_REWRITE_CONV rep (cnvl:conv->conv) (builtin_net:gconv net) thl =
  let final_net =
    cake_memo cake_rw_net_memo
      (fun (r,b,l) -> r = rep && b == builtin_net && cake_same_thms l thl)
      (rep,builtin_net,thl)
      (fun () -> let thl_canon = itlist (mk_rewrites false) thl [] in
                 itlist (net_of_thm rep) thl_canon builtin_net) in
  cnvl (REWRITES_CONV final_net);;

(* HOL Light's front ends, unchanged, so that they use the memo *)

let GEN_REWRITE_CONV (cnvl:conv->conv) thl =
  GENERAL_REWRITE_CONV false cnvl empty_net thl;;
let PURE_REWRITE_CONV thl =
  GENERAL_REWRITE_CONV true TOP_DEPTH_CONV empty_net thl;;
let REWRITE_CONV thl =
  GENERAL_REWRITE_CONV true TOP_DEPTH_CONV (basic_net()) thl;;
let PURE_ONCE_REWRITE_CONV thl =
  GENERAL_REWRITE_CONV false ONCE_DEPTH_CONV empty_net thl;;
let ONCE_REWRITE_CONV thl =
  GENERAL_REWRITE_CONV false ONCE_DEPTH_CONV (basic_net()) thl;;
let GEN_REWRITE_RULE cnvl thl = CONV_RULE(GEN_REWRITE_CONV cnvl thl);;
let PURE_REWRITE_RULE thl = CONV_RULE(PURE_REWRITE_CONV thl);;
let REWRITE_RULE thl = CONV_RULE(REWRITE_CONV thl);;
let PURE_ONCE_REWRITE_RULE thl = CONV_RULE(PURE_ONCE_REWRITE_CONV thl);;
let ONCE_REWRITE_RULE thl = CONV_RULE(ONCE_REWRITE_CONV thl);;
let PURE_ASM_REWRITE_RULE thl th =
    PURE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th;;
let ASM_REWRITE_RULE thl th =
    REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th;;
let PURE_ONCE_ASM_REWRITE_RULE thl th =
    PURE_ONCE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th;;
let ONCE_ASM_REWRITE_RULE thl th =
    ONCE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th;;
let GEN_REWRITE_TAC cnvl thl = CONV_TAC(GEN_REWRITE_CONV cnvl thl);;
let PURE_REWRITE_TAC thl = CONV_TAC(PURE_REWRITE_CONV thl);;
let REWRITE_TAC thl = CONV_TAC(REWRITE_CONV thl);;
let PURE_ONCE_REWRITE_TAC thl = CONV_TAC(PURE_ONCE_REWRITE_CONV thl);;
let ONCE_REWRITE_TAC thl = CONV_TAC(ONCE_REWRITE_CONV thl);;
let (PURE_ASM_REWRITE_TAC: thm list -> tactic) = ASM PURE_REWRITE_TAC;;
let (ASM_REWRITE_TAC: thm list -> tactic) = ASM REWRITE_TAC;;
let (PURE_ONCE_ASM_REWRITE_TAC: thm list -> tactic) = ASM PURE_ONCE_REWRITE_TAC;;
let (ONCE_ASM_REWRITE_TAC: thm list -> tactic) = ASM ONCE_REWRITE_TAC;;

(* ------------------------------------------------------------------------- *)
(* A faster simplifier.  HOL Light's TOP_DEPTH_SQCONV, after a pass over the *)
(* subterms of a term has changed some of them, simplifies the new term      *)
(* again from scratch, so every subterm is traversed once more (and again    *)
(* at every enclosing level: on a big induction hypothesis 550,000 calls for *)
(* a term of size 220).  That second pass cannot change anything: each       *)
(* subterm is then the result of a call of the strategy (which goes on until *)
(* it fails) or a subterm on which it failed.  KIT_TOP_DEPTH_SQCONV tries   *)
(* only the rewrites at the top of the new term instead, and so gives the    *)
(* same theorems.  The helper functions are HOL Light's (simp.ml), unchanged.*)
(* SIMPLIFY_CONV and HOL Light's SIMP_CONV, SIMP_RULE, SIMP_TAC,             *)
(* ASM_SIMP_TAC and their PURE_ versions are redefined with it (otherwise    *)
(* HOL Light's definitions), for the kit and every later file.               *)
(* ------------------------------------------------------------------------- *)

(* find_witnesses of HOL Light's simp.ml (commit 9cb19cc), copied so that   *)
(* the kit also loads on HOL Light versions without it (924faf0)            *)
let kit_find_witnesses provers vs tm : instantiation =
  let evs,bod = strip_exists tm in
  let avs = vs @ evs in
  let p = list_mk_conj(filter (fun c -> exists (C vfree_in c) avs)
                              (conjuncts bod)) in
  let q = list_mk_exists(avs,p) and lconsts = subtract (frees p) avs in
  let restrict l = filter (fun (_,v) -> mem v vs) l in
  tryfind (fun pr ->
    let bcs,insts,tyin = term_match lconsts p (concl(apply_prover pr q)) in
    if exists (fun (ty,v) -> ty <> v) tyin then fail()
    else restrict bcs,restrict insts,[])
  provers;;

(* The conditions of conditional rewrites are proved by the simplifier      *)
(* (the simpset's prover), at a depth lev; the same condition is often      *)
(* tried many times in one simplification, all failing (an induction        *)
(* hypothesis !x. P x ==> f x = T rewrites every f t, and its condition     *)
(* contains f again: 1230 attempts at 14 different conditions, 36 s, in     *)
(* simplifying one assumption of flat_patternProof's compile_exp_esgc_free). *)
(* The results (theorem or failure) are kept for each simpset (the same    *)
(* object, so the same context), depth and condition, during one call of    *)
(* SIMPLIFY_CONV; the prover is deterministic, so the results are the same. *)
(* Since 2026-11-18.                                                         *)

let kit_cond_cache = (Hashtbl.create 1000 : (term, (simpset * int * thm option)) Hashtbl.t);;

let kit_cond_prove prover strat (ss:simpset) (lev:int) (cnd:term) : thm =
  let hit = try Some (find (fun (s,l,_) -> s == ss && l = lev)
                           (Hashtbl.find_all kit_cond_cache cnd))
            with Failure _ -> None in
  match hit with
    Some (_,_,Some th) -> th
  | Some (_,_,None) -> failwith "kit_cond_prove: cached failure"
  | None ->
      let r = try Some (prover strat ss (lev-1) cnd) with Failure _ -> None in
      (if Hashtbl.length kit_cond_cache > 100000 then Hashtbl.reset kit_cond_cache);
      Hashtbl.add kit_cond_cache cnd (ss,lev,r);
      match r with Some th -> th | None -> failwith "kit_cond_prove";;

(* A bound variable named like a free variable of the context (HOL4 style  *)
(* statements and induction hypotheses reuse names under binders: ?l i cs. *)
(* beside free l i cs).  HOL Light simplifies the body of \v. b with v as  *)
(* it is and, if the result depends on a context fact about the free v (so *)
(* ABS fails), all again with a genvar for v: under n such binders the body *)
(* is simplified up to 2^n times (compile_thm of word_bignumProof: FS 25    *)
(* times slower than with primed bound names).  The kit does the same, but  *)
(* as soon as a rewrite uses a hypothesis of the context that mentions v    *)
(* (which would make ABS fail at the end), the attempt with v is abandoned  *)
(* (exception Kit_binder_abort) and the genvar route taken: the same        *)
(* theorems, without the work wasted (HOL4's Opening.sml EQ_CONGPROC        *)
(* renames such a binder up front).  Only rewrites that are used count: the *)
(* proofs of side conditions are not watched, their results are.  The      *)
(* context: the hypotheses of the theorems given to SIMPLIFY_CONV and the   *)
(* antecedents assumed under implications (kit_context_hyps, lazily, each   *)
(* once).  Since 2026-11-20 (kit_binder_shortcut := false restores the     *)
(* plain route).                                                            *)

let kit_binder_shortcut = ref true;;

let kit_context_hyps = ref (lazy ([]:term list));;
let kit_context_frees = ref (lazy ([]:term list));;

(* the hypotheses of thl, each once (the assumption theorems of FS and GVS  *)
(* carry the hypotheses of the ones they were simplified with)              *)
let kit_dedup_hyps (thl:thm list) : term list =
  let seen = ref [] in
  do_list (fun th -> do_list (fun h -> if not (List.memq h !seen) then seen := h :: !seen)
                             (hyp th)) thl;
  !seen;;

let kit_set_context (hs:term list Lazy.t) =
  kit_context_hyps := hs;
  kit_context_frees := lazy (itlist (fun h acc -> union (frees h) acc) (Lazy.force hs) []);;

let kit_with_context (cxto:term option) (f:unit -> 'a) : 'a =
  match cxto with
    None -> f ()
  | Some cxt ->
      let oh = !kit_context_hyps and ofr = !kit_context_frees in
      kit_context_hyps := lazy (cxt :: Lazy.force oh);
      kit_context_frees := lazy (union (frees cxt) (Lazy.force ofr));
      let restore () = kit_context_hyps := oh; kit_context_frees := ofr in
      (try let r = f () in restore (); r
       with e -> (restore (); raise e));;

(* the binders being simplified with their own variable that is free in the *)
(* context, innermost first, each with the context hypotheses mentioning it *)
exception Kit_binder_abort of term;;

let kit_active_binders = ref ([] : (term * term list) list);;

(* the flags of the ONCE rewrites of the latest kit simpset (set by          *)
(* CAKE_AUGMENTED_SS below).  While one is unused the shortcut is off: an   *)
(* abandoned attempt would not use up the ONCE rewrites that HOL Light's    *)
(* full attempt uses up, so the genvar route could differ.                  *)
let kit_current_once_flags = ref ([] : bool ref list);;

let kit_once_pending () = exists (fun r -> not !r) !kit_current_once_flags;;

(* a rewrite of the strategy produced th: if it uses a hypothesis about an   *)
(* active binder's variable, abandon the innermost such binder's attempt   *)
(* (where HOL Light's ABS fails first; its genvar route decides the outer  *)
(* ones)                                                                    *)
let kit_check_abort (th:thm) : unit =
  match !kit_active_binders with
    [] -> ()
  | act ->
      let hs = hyp th in
      if hs = [] then () else
      match (try Some (find (fun (_,vhs) -> exists (fun h -> List.memq h vhs) hs) act)
             with Failure _ -> None) with
        Some (v,_) -> raise (Kit_binder_abort v)
      | None -> ();;

let KIT_TOP_DEPTH_SQCONV =
  let nonlooping th =
    let l,r = dest_eq(rand(concl th)) in
    let matchable = can o term_match (freesl(hyp th)) in
    not(free_in l r) &&
    (not(matchable l r && matchable r l) || term_order l r) in
  let IMP_REWRITES_CONV strat (Simpset(net,prover,provers,rewmaker) as ss) lev
                        pconvs tm =
    tryfind (fun (n,cnv) ->
      if n >= 4 then fail() else
      let th = cnv tm in
      let etm = concl th in
      if is_eq etm then (kit_check_abort th; th) else
      if lev <= 0 then failwith "IMP_REWRITES_CONV: Too deep" else
      let cnd = lhand etm in
      let mvs = subtract (frees cnd) (union (frees tm) (freesl(hyp th))) in
      let th' =
        if mvs = [] then th else
        let th1 = try INSTANTIATE (kit_find_witnesses provers mvs cnd) th
                  with Failure _ -> th in
        if nonlooping th1 then th1
        else if th1 != th && nonlooping th then th
        else failwith "IMP_REWRITES_CONV: looping instance" in
      (* a side condition is proved without the binder checks: an attempt   *)
      (* that fails must not abandon a binder; a proof that succeeds is       *)
      (* checked through r, which carries its hypotheses                      *)
      let cth =
        match !kit_active_binders with
          [] -> kit_cond_prove prover strat ss lev (lhand(concl th'))
        | act ->
            kit_active_binders := [];
            (try let c = kit_cond_prove prover strat ss lev (lhand(concl th')) in
                 kit_active_binders := act; c
             with e -> (kit_active_binders := act; raise e)) in
      let r = MP th' cth in kit_check_abort r; r) pconvs in
  let rec RUN_SUB_CONV strat ss lev triv th =
    let tm = concl th in
    if is_imp tm then
      let subtm = lhand tm in
      let avs,bod = strip_forall subtm in
      let (t,t'),ss',mk_fun,cxto =
        try dest_eq bod,ss,I,None with Failure _ ->
        let cxt,deq = dest_imp bod in
        dest_eq deq,AUGMENT_SIMPSET (ASSUME cxt) ss,DISCH cxt,Some cxt in
      let eth,triv' = try kit_with_context cxto (fun () -> strat ss' lev t),false
                      with Failure _ -> REFL t,triv in
      let eth' = GENL avs (mk_fun eth) in
      let th' = if is_var t' then INST [rand(concl eth),t'] th
                else GEN_PART_MATCH lhand th (concl eth') in
      let th'' = MP th' eth' in
      RUN_SUB_CONV strat ss lev triv' th''
    else if triv then fail() else th in
  let GEN_SUB_CONV strat ss lev pconvs tm =
    try tryfind (fun (n,cnv) ->
          if n < 4 then fail() else
          let th = cnv tm in
          RUN_SUB_CONV strat ss lev true th) pconvs
    with Failure _ ->
        if is_comb tm then
          let l,r = dest_comb tm in
          try let th1 = strat ss lev l in
              try let th2 = strat ss lev r in MK_COMB(th1,th2)
              with Failure _ -> AP_THM th1 r
          with Failure _ -> AP_TERM l (strat ss lev r)
        else if is_abs tm then
          let v,bod = dest_abs tm in
          let via_genvar () =
            let gv = genvar(type_of v) in
            let gbod = vsubst[gv,v] bod in
            let gth = ABS gv (strat ss lev gbod) in
            let gtm = concl gth in
            let l,r = dest_eq gtm in
            let v' = variant (frees gtm) v in
            let l' = alpha v' l and r' = alpha v' r in
            EQ_MP (ALPHA gtm (mk_eq(l',r'))) gth in
          let direct () =
            let th = strat ss lev bod in
            try ABS v th with Failure _ -> via_genvar () in
          if not !kit_binder_shortcut || not (mem v (Lazy.force !kit_context_frees)) ||
             kit_once_pending ()
          then direct () else
          let watched () =
            let vhs = filter (vfree_in v) (Lazy.force !kit_context_hyps) in
            let old_act = !kit_active_binders in
            kit_active_binders := (v,vhs) :: old_act;
            match (try Kit_ok (strat ss lev bod) with e -> Kit_exn e) with
              Kit_ok th -> kit_active_binders := old_act;
                           (try ABS v th with Failure _ -> via_genvar ())
            | Kit_exn (Kit_binder_abort v') when v' == v ->
                kit_active_binders := old_act; via_genvar ()
            | Kit_exn e -> kit_active_binders := old_act; raise e in
          watched ()
        else failwith "GEN_SUB_CONV" in
  let rec TOP_DEPTH_SQCONV (Simpset(net,prover,provers,rewmaker) as ss) lev tm =
    let pconvs = lookup tm net in
    try let th1 = IMP_REWRITES_CONV TOP_DEPTH_SQCONV ss lev pconvs tm in
        (try TRANS th1 (TOP_DEPTH_SQCONV ss lev (rand(concl th1)))
         with Failure _ -> th1)
    with Failure _ ->
      let th1 = GEN_SUB_CONV TOP_DEPTH_SQCONV ss lev pconvs tm in
      let tm1 = rand(concl th1) in
      try let th2 = IMP_REWRITES_CONV TOP_DEPTH_SQCONV ss lev (lookup tm1 net) tm1 in
          TRANS th1 (try TRANS th2 (TOP_DEPTH_SQCONV ss lev (rand(concl th2)))
                     with Failure _ -> th2)
      with Failure _ -> th1 in
  TOP_DEPTH_SQCONV;;


let kit_simp_depth = ref 0;;

let kit_simplify_conv ss thl tm =
  (if !kit_simp_depth = 0 then Hashtbl.reset kit_cond_cache);
  incr kit_simp_depth;
  let old_hyps = !kit_context_hyps and old_frees = !kit_context_frees
  and old_act = !kit_active_binders in
  kit_set_context (lazy (kit_dedup_hyps thl));
  kit_active_binders := [];
  let leave () = kit_context_hyps := old_hyps; kit_context_frees := old_frees;
                 kit_active_binders := old_act;
                 decr kit_simp_depth;
                 if !kit_simp_depth = 0 then Hashtbl.reset kit_cond_cache in
  let r = try GEN_SIMPLIFY_CONV KIT_TOP_DEPTH_SQCONV ss 3 thl tm
          with e -> (leave (); raise e) in
  leave (); r;;

(* terms equal up to the names of genvars (_123) among the bound variables: *)
(* two runs of the same simplification can differ in those (the genvar     *)
(* counter), so the check below compares up to them                        *)
let kit_same_upto_genvars (t1:term) (t2:term) =
  let is_gv s = String.length s > 1 && s.[0] = '_' &&
                (try ignore (int_of_string (String.sub s 1 (String.length s - 1))); true
                 with Failure _ -> false) in
  let rec names t acc =
    match t with
      Abs(v,b) -> let n = fst (dest_var v) in names b ((if is_gv n then "_" else n) :: acc)
    | Comb(f,x) -> names x (names f acc)
    | _ -> acc in
  aconv t1 t2 && names t1 [] = names t2 [];;

(* in check mode, every outermost call also runs with the binder shortcut  *)
(* off (HOL Light's route, second, from the same ONCE flags, so that its    *)
(* state is the one kept) and a KITDIFF line reports a different theorem   *)
(* (up to genvar names)                                                     *)
let SIMPLIFY_CONV ss thl tm =
  if not (!kit_check && !kit_binder_shortcut && !kit_simp_depth = 0)
  then kit_simplify_conv ss thl tm else
  let plain () =
    kit_binder_shortcut := false;
    let r = (try kit_simplify_conv ss thl tm
             with e -> (kit_binder_shortcut := true; raise e)) in
    kit_binder_shortcut := true; r in
  let sub l1 l2 = forall (fun h -> exists (kit_same_upto_genvars h) l2) l1 in
  let same a b = kit_same_upto_genvars (concl a) (concl b) &&
                 sub (hyp a) (hyp b) && sub (hyp b) (hyp a) in
  let flags = !kit_current_once_flags in
  let saved = map (!) flags in
  let r_new = (try Kit_ok (kit_simplify_conv ss thl tm) with e -> Kit_exn e) in
  List.iter2 (fun r v -> r := v) flags saved;
  let r_old = (try Kit_ok (plain ()) with e -> Kit_exn e) in
  kit_check_results "simplifier binder" same r_old r_new;;
let SIMP_CONV thl = SIMPLIFY_CONV (basic_ss []) thl;;
let PURE_SIMP_CONV thl = SIMPLIFY_CONV empty_ss thl;;
let SIMP_RULE thl = CONV_RULE(SIMP_CONV thl);;
let PURE_SIMP_RULE thl = CONV_RULE(PURE_SIMP_CONV thl);;
let SIMP_TAC thl = CONV_TAC(SIMP_CONV thl);;
let PURE_SIMP_TAC thl = CONV_TAC(PURE_SIMP_CONV thl);;
let ASM_SIMP_TAC = ASM SIMP_TAC;;
let PURE_ASM_SIMP_TAC = ASM PURE_SIMP_TAC;;

(* a few arithmetic rewrites in the spirit of HOL4's ARITH_RWTS_ss *)

let cake_arith_rewrites =
  [ADD_CLAUSES; MULT_CLAUSES; SUB_0; SUB_REFL; ADD_SUB; ADD_SUB2;
   LE_REFL; LT_REFL; LE_0; LT_0; LE_SUC_LT; LT_SUC_LE; SUC_INJ; NOT_SUC;
   EQ_ADD_LCANCEL; EQ_ADD_RCANCEL; EQ_ADD_LCANCEL_0; EQ_ADD_RCANCEL_0;
   LE_ADD_LCANCEL; LE_ADD_RCANCEL; LT_ADD_LCANCEL; LT_ADD_RCANCEL;
   ADD_EQ_0; MULT_EQ_0; EXP; LT_SUC; LE_SUC; PRE;
   ARITH_RULE `!x. MIN 0 x = 0 /\ MIN x 0 = 0`;
   ARITH_RULE `!x. MAX 0 x = x /\ MAX x 0 = x`;
   ARITH_RULE `!x. x <= x + c <=> T`; ARITH_RULE `!x. x < x + c <=> 0 < c`;
   ARITH_RULE `!x. x <= c + x <=> T`; ARITH_RULE `!x. x < c + x <=> 0 < c`;
   ARITH_RULE `!x. x < SUC x`; ARITH_RULE `!x. x <= SUC x`;
   ARITH_RULE `!x. 0 < SUC x`; ARITH_RULE `!x. ~(SUC x <= 0)`;
   ARITH_RULE `!x. x >= x`; ARITH_RULE `!x. ~(x > x)`;
   ARITH_RULE `!x. x >= 0`; ARITH_RULE `!x. SUC x > 0`;
   ARITH_RULE `!x. (SUC x = 1 <=> x = 0) /\ (1 = SUC x <=> x = 0)`;
   ARITH_RULE `!x. (SUC x = 2 <=> x = 1) /\ (2 = SUC x <=> x = 1)`;
   LENGTH_EQ_NIL; MESON[LENGTH_EQ_NIL] `!l:A list. 0 = LENGTH l <=> l = []`];;

let cake_basic_rewrites =
  [K_THM; I_THM; o_THM; FST; SND; PAIR; LET_DEF; LET_END_DEF;
   HD; TL; LENGTH; APPEND; APPEND_NIL; MAP; NULL; REVERSE; MEM;
   ALL; EX; NOT_CONS_NIL; CONS_11; option_INJ; option_DISTINCT;
   PAIR_EQ; COND_ID; EXISTS_REFL; UNWIND_THM1; UNWIND_THM2;
   MESON[] `!a:A. ?x. a = x`;
   MESON[] `!a:A P. (!x. x = a ==> P x) <=> P a`;
   MESON[] `!a:A P. (!x. a = x ==> P x) <=> P a`] @
  cake_arith_rewrites;;

(* ------------------------------------------------------------------------- *)
(* The registry.                                                             *)
(*                                                                           *)
(* Global part: the kit's basic rewrites and the theorems of every datatype  *)
(* and record (they only mention their own constants).  File part: what a    *)
(* file registers with cake_add_simps (HOL4's [simp]) is used by the files   *)
(* that load it with needs (directly or not), as HOL4's srw_ss follows the   *)
(* ancestry of a theory; so a file's simpset does not depend on what other   *)
(* files happen to be loaded in the same session.  Outside the loading of a  *)
(* file (interactive work), the simpset is that of the file named by         *)
(* cake_begin "path.ml" (its needs closure), or else all registrations.      *)
(* ------------------------------------------------------------------------- *)

let cake_simp_thms = ref ([]:thm list);;          (* the global part *)

let cake_base_ss () =
  let numconvs =
    [`m + n:num`; `m * n:num`; `m - n:num`; `SUC n`; `m EXP n`;
     `m DIV n`; `m MOD n`; `m < n:num`; `m <= n:num`; `m > n:num`;
     `m >= n:num`; `m:num = n`; `PRE n`; `EVEN n`; `ODD n`] in
  (* conversions in a simpset must fail (not return x = x) when they do not *)
  (* apply, or the simplifier loops: hence CHANGED_CONV                     *)
  let ss0 = itlist (fun k ss -> ss_of_conv k (CHANGED_CONV NUM_RED_CONV) ss)
                   numconvs (cake_basic_ss []) in
  let ss0 = ss_of_conv `?x:A. P x` (CHANGED_CONV UNWIND_CONV) ss0 in
  ss_of_conv `!x:A. P x` (CHANGED_CONV FORALL_UNWIND_CONV) ss0;;

let cake_global_ss = ref (cake_basic_ss []);;

(* files being loaded (innermost first), their needs, their registrations *)

let cake_loading = ref ([] : string list);;
let cake_file_deps = ref ([] : (string * string list) list);;
let cake_simp_buckets = ref ([] : (string * thm list) list);;
let cake_context = ref (None : string option);;   (* set by cake_begin *)

(* simpsets per context ("*" = everything), built lazily, each with the    *)
(* registrations made since it was last used (newest first): a cached     *)
(* simpset is brought up to date only when it is used again, so a          *)
(* registration costs no ss_of_thms per cached simpset (each cached simpset *)
(* of a session with all the semantics got the theorems of every new type); *)
(* the additions are made in the same order as before, so the simpset is   *)
(* the same                                                                  *)
let cake_ss_cache = ref ([] : (string * simpset * thm list list) list);;

(* the files named by the needs lines of a file (on the load path); a needs  *)
(* line naming a file that is not on the load path is skipped with a         *)
(* warning (since 2026-11-22: before, file_on_path's Not_found escaped       *)
(* mapfilter and the whole list was empty, so cake_begin on a file whose     *)
(* prerequisites were partly unwritten gave only the global simps)           *)
let read_needs_lines file =
  try
    let ic = open_in file in
    let n = in_channel_length ic in
    let s = really_input_string ic n in
    close_in ic;
    let ls = String.split_on_char '\n' s in
    mapfilter (fun l ->
        let l = String.trim l in
        if String.length l > 7 && String.sub l 0 7 = "needs \"" then
          let k = try String.index_from l 7 '"' with Not_found -> failwith "" in
          let f = String.sub l 7 (k - 7) in
          try file_on_path (!load_path) f with Not_found ->
            (warn true (file ^ ": needs \"" ^ f ^ "\": no such file on the load path " ^
                        "(left out of its simpset closure)");
             failwith "")
        else failwith "") ls
  with _ -> [];;

let rec cake_file_closure f acc =
  if mem f acc then acc else
  let ds = try assoc f (!cake_file_deps) with Failure _ -> [] in
  itlist cake_file_closure ds (f::acc);;

let cake_context_key () =
  match !cake_loading with
    f::_ -> f
  | [] -> (match !cake_context with Some f -> f | None -> "*");;

let cake_ss_for key =
  match filter (fun (k,_,_) -> k = key) (!cake_ss_cache) with
    (_,ss,[])::_ -> ss
  | (_,ss,pend)::_ ->
      let ss' = itlist ss_of_thms pend ss in
      cake_ss_cache := map (fun (k,_,_ as e) -> if k = key then (k,ss',[]) else e)
                           (!cake_ss_cache);
      ss'
  | [] ->
  let thms =
    if key = "*" then flat (map snd (!cake_simp_buckets))
    else
      let cl = cake_file_closure key [] in
      flat (mapfilter (fun f -> assoc f (!cake_simp_buckets)) cl) in
  let ss = ss_of_thms thms (!cake_global_ss) in
  cake_ss_cache := (key,ss,[]) :: !cake_ss_cache; ss;;

(* the simpset of the current context *)
let cake_active_ss () = cake_ss_for (cake_context_key());;

(* kept for compatibility: the current simpset as a reference *)
let cake_ss = ref (cake_basic_ss []);;

let cake_rebuild_ss () =
  cake_global_ss := ss_of_thms (!cake_simp_thms) (cake_base_ss());
  cake_ss_cache := [];;

(* global registration (datatypes, records): every cached simpset grows    *)
(* (when it is next used)                                                   *)

let cake_add_global_simps thl =
  cake_simp_thms := thl @ !cake_simp_thms;
  cake_global_ss := ss_of_thms thl (!cake_global_ss);
  cake_ss_cache := map (fun (k,ss,p) -> k,ss,thl::p) (!cake_ss_cache);;

(* registration by a file (HOL4 [simp]) *)

let cake_add_simps thl =
  let f = match !cake_loading with f::_ -> f
          | [] -> (match !cake_context with Some f -> f | None -> "*") in
  let old = try assoc f (!cake_simp_buckets) with Failure _ -> [] in
  cake_simp_buckets := (f,thl @ old) ::
                       filter (fun (g,_) -> g <> f) (!cake_simp_buckets);
  (* the caches that see f: f itself, "*", and anything being loaded *)
  cake_ss_cache :=
    mapfilter (fun (k,ss,p) ->
                 if k = f || k = "*" then (k,ss,thl::p)
                 else if mem k (!cake_loading) then failwith ""
                 else if mem f (cake_file_closure k []) then failwith ""
                 else (k,ss,p)) (!cake_ss_cache);;

(* remove registered rewrites (by conclusion), everywhere *)
let cake_del_simps thl =
  let keep th = not (exists (equals_thm th) thl) in
  cake_simp_thms := filter keep (!cake_simp_thms);
  cake_simp_buckets := map (fun (f,l) -> f,filter keep l) (!cake_simp_buckets);
  cake_rebuild_ss();;

(* interactive work on a file: use the simpset of its needs closure *)

let cake_begin file =
  (* the file need not exist yet: then it is file in the src directory *)
  let f = try file_on_path (!load_path) file
          with Not_found -> Filename.concat cakeml_src_dir file in
  cake_file_deps := (f,read_needs_lines f) ::
                    filter (fun (g,_) -> g <> f) (!cake_file_deps);
  cake_context := Some f;
  cake_ss_cache := filter (fun (k,_,_) -> k <> f) (!cake_ss_cache);;

let cake_end () = cake_context := None;;

(* needs, recording which file is being loaded and its needs *)

let needs s =
  let s' = file_on_path (!load_path) s in
  let fileid = (Filename.basename s',Digest.file s') in
  if List.mem fileid (!loaded_files) then needs s else
  begin
    cake_file_deps := (s',read_needs_lines s') ::
                      filter (fun (g,_) -> g <> s') (!cake_file_deps);
    cake_loading := s' :: !cake_loading;
    (try needs s with e -> (cake_loading := tl (!cake_loading); raise e));
    cake_loading := tl (!cake_loading)
  end;;

(* the case theorems of every datatype known so far, and those of each new
   datatype as it is made *)

let cake_register_type_simps tyname =
  let ci = case_info_of_tyname tyname in
  cake_add_global_simps (ci.ci_def :: ci.ci_distinct @ ci.ci_inject);;

let () =
  cake_simp_thms := cake_basic_rewrites @ all_case_rewrites();
  cake_rebuild_ss();;

let cake_type s =
  let res = cake_type s in
  do_list cake_register_type_simps (!cake_last_types);
  res;;

(* ------------------------------------------------------------------------- *)
(* The bijections of an enumeration type with 0 .. k-1 (HOL4's Datatype      *)
(* makes them for every type whose constructors are all nullary;             *)
(* EnumType.sml).  cake_enum_bijections "ty" defines ty2num (ty2num C_i = i, *)
(* constructors in the order of the type's specification) and num2ty         *)
(* (num2ty n = C_n for n < k; ARB otherwise, unspecified as in HOL4), and    *)
(* returns HOL4's theorems by name: ty2num_thm, num2ty_thm, ty2num_11,       *)
(* num2ty_11, ty2num_ONTO, num2ty_ONTO, num2ty_ty2num, ty2num_num2ty,        *)
(* ty_EQ_ty, and num2ty_def; ty2num_thm and num2ty_thm are added to the      *)
(* simpset, as HOL4's TypeBase does.  Not automatic (opt-in): files that     *)
(* define such functions themselves (ag32) keep working.  Since 2026-11-22.  *)
(*   let funcT_enum = cake_enum_bijections "funcT";;                         *)
(*   let funcT2num_11 = assoc "funcT2num_11" funcT_enum;;                    *)
(* ------------------------------------------------------------------------- *)

(* r < k (k a numeral) as r = k-1 \/ .. \/ r = 0 \/ F                        *)
let kit_lt_numeral_cases_conv =
  let lt0,ltsuc = CONJ_PAIR LT in
  let step t =
    let l,r = dest_binop `(<):num->num->bool` t in
    if not (is_numeral r) then failwith "kit_lt_numeral_cases_conv" else
    if dest_numeral r =/ num_0 then REWR_CONV lt0 t
    else (RAND_CONV num_CONV THENC REWR_CONV ltsuc) t in
  REPEATC (CHANGED_CONV (ONCE_DEPTH_CONV step)) THENC REWRITE_CONV[];;

let cake_enum_bijections (tyname:string) : (string * thm) list =
  let ci = try case_info_of_tyname tyname
           with Failure _ -> failwith ("cake_enum_bijections: no datatype " ^ tyname) in
  let pats = ci.ci_pats in
  if pats = [] || exists (fun (vs,_) -> vs <> []) pats then
    failwith ("cake_enum_bijections: " ^ tyname ^ " is not an enumeration") else
  let cs = map snd pats in
  let ty = type_of (hd cs) in
  if tyvars ty <> [] then failwith ("cake_enum_bijections: " ^ tyname ^ " is polymorphic") else
  let k = length cs in
  let repn = tyname ^ "2num" and absn = "num2" ^ tyname in
  if can get_const_type repn || can get_const_type absn then
    failwith ("cake_enum_bijections: " ^ repn ^ " or " ^ absn ^ " is already a constant") else
  let numty = `:num` in
  let nums = map mk_small_numeral (0--(k-1)) in
  let _,_,rth = assoc tyname (!inductive_type_store) in
  let repv = mk_var(repn,mk_fun_ty ty numty) in
  let rep_thm = kit_new_recursive_definition rth
                  (list_mk_conj (map2 (fun c n -> mk_eq(mk_comb(repv,c),n)) cs nums)) in
  let rep = fst(strip_comb(lhs(hd(conjuncts(concl rep_thm))))) in
  let absv = mk_var(absn,mk_fun_ty numty ty) and n = mk_var("n",numty) in
  let chain = itlist2 (fun c i acc -> mk_cond(mk_eq(n,i),c,acc)) cs nums
                      (mk_const("ARB",[ty,aty])) in
  let abs_def = new_definition (mk_eq(mk_comb(absv,n),chain)) in
  let abs = fst(strip_comb(lhs(snd(strip_forall(concl abs_def))))) in
  let k_tm = mk_small_numeral k in
  let a = mk_var("a",ty) and a' = mk_var("a'",ty)
  and r = mk_var("r",numty) and r' = mk_var("r'",numty) in
  let rep_a = mk_comb(rep,a) and abs_r = mk_comb(abs,r) in
  let lt x = mk_binop `(<):num->num->bool` x k_tm in
  let cases_tac = GEN_TAC THEN
    STRUCT_CASES_TAC (SPEC a ci.ci_nchotomy) in
  let abs_thm = prove
   (list_mk_conj (map2 (fun c i -> mk_eq(mk_comb(abs,i),c)) cs nums),
    REWRITE_TAC[abs_def] THEN CONV_TAC(DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC[]) in
  let abs_rep = prove
   (mk_forall(a,mk_eq(mk_comb(abs,rep_a),a)),
    cases_tac THEN REWRITE_TAC[rep_thm; abs_thm]) in
  let rep_lt = prove
   (mk_forall(a,lt rep_a),
    cases_tac THEN REWRITE_TAC[rep_thm] THEN CONV_TAC NUM_REDUCE_CONV) in
  let rep_11 = prove
   (list_mk_forall([a;a'],mk_eq(mk_eq(rep_a,mk_comb(rep,a')),mk_eq(a,a'))),
    REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM abs) THEN REWRITE_TAC[abs_rep];
      DISCH_THEN SUBST1_TAC THEN REFL_TAC]) in
  let eq_ty = prove
   (list_mk_forall([a;a'],mk_eq(mk_eq(a,a'),mk_eq(rep_a,mk_comb(rep,a')))),
    REWRITE_TAC[rep_11]) in
  let rep_abs = prove
   (mk_forall(r,mk_eq(lt r,mk_eq(mk_comb(rep,abs_r),r))),
    GEN_TAC THEN EQ_TAC THENL
     [CONV_TAC(LAND_CONV kit_lt_numeral_cases_conv) THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
      REWRITE_TAC[abs_thm; rep_thm];
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[rep_lt]]) in
  let abs_11 = prove
   (list_mk_forall([r;r'],mk_imp(lt r,mk_imp(lt r',
      mk_eq(mk_eq(abs_r,mk_comb(abs,r')),mk_eq(r,r'))))),
    REPEAT GEN_TAC THEN REWRITE_TAC[rep_abs] THEN REPEAT DISCH_TAC THEN EQ_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM rep) THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN REFL_TAC]) in
  let rep_onto = prove
   (mk_forall(r,mk_eq(lt r,mk_exists(a,mk_eq(r,rep_a)))),
    GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC abs_r THEN ASM_MESON_TAC[rep_abs];
      STRIP_TAC THEN ASM_REWRITE_TAC[rep_lt]]) in
  let abs_onto = prove
   (mk_forall(a,mk_exists(r,mk_conj(mk_eq(a,abs_r),lt r))),
    GEN_TAC THEN EXISTS_TAC rep_a THEN REWRITE_TAC[abs_rep; rep_lt]) in
  cake_add_global_simps [rep_thm; abs_thm];
  [repn ^ "_thm",rep_thm; absn ^ "_thm",abs_thm; repn ^ "_11",rep_11; absn ^ "_11",abs_11;
   repn ^ "_ONTO",rep_onto; absn ^ "_ONTO",abs_onto; absn ^ "_" ^ repn,abs_rep;
   repn ^ "_" ^ absn,rep_abs; tyname ^ "_EQ_" ^ tyname,eq_ty; absn ^ "_def",abs_def];;

(* ------------------------------------------------------------------------- *)
(* Conversions and rules.                                                    *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* DECIDE_TAC (HOL4 decide_tac): ARITH_TAC with the arithmetic assumptions   *)
(* only (boolean combinations of num relations), first those that share an  *)
(* atom with the goal (transitively), then, if that fails, all of them.     *)
(* ------------------------------------------------------------------------- *)

let kit_num_rel tm =
  (is_eq tm || (try mem (fst(dest_const(rator(rator tm)))) ["<"; "<="; ">"; ">="]
                with Failure _ -> false)) &&
  (try type_of (lhand tm) = kit_num_ty with Failure _ -> false);;

let rec kit_is_arith tm =
  if is_neg tm then kit_is_arith (rand tm)
  else if is_conj tm || is_disj tm || is_imp tm then
    kit_is_arith (lhand tm) && kit_is_arith (rand tm)
  else if is_eq tm && type_of (lhand tm) = bool_ty then
    kit_is_arith (lhand tm) && kit_is_arith (rand tm)
  else kit_num_rel tm;;

(* the atoms of an arithmetic formula: its maximal subterms of type num that *)
(* are not sums, differences, products, SUC, PRE or numerals                 *)
let kit_arith_atoms =
  let ops = ["+"; "-"; "*"; "SUC"; "PRE"; "NUMERAL"; "BIT0"; "BIT1"; "_0"] in
  let rec num_atoms tm acc =
    if is_numeral tm then acc else
    let f,args = strip_comb tm in
    if is_const f && mem (fst(dest_const f)) ops then itlist num_atoms args acc
    else insert tm acc in
  let rec go tm acc =
    if is_neg tm then go (rand tm) acc
    else if is_conj tm || is_disj tm || is_imp tm || (is_eq tm && type_of (lhand tm) = bool_ty)
    then go (lhand tm) (go (rand tm) acc)
    else if is_comb tm && is_comb (rator tm) then num_atoms (lhand tm) (num_atoms (rand tm) acc)
    else acc in
  fun tm -> go tm [];;

(* the facts that share an atom with the goal, directly or through others *)
let kit_relevant_facts (goal:term) (facts:thm list) =
  let tagged = map (fun th -> th,kit_arith_atoms (concl th)) facts in
  let rec close atoms chosen rest =
    let new_,rest' = partition (fun (_,ats) -> exists (fun a -> mem a atoms) ats) rest in
    if new_ = [] then chosen else
    close (itlist (fun (_,ats) acc -> union ats acc) new_ atoms) (chosen @ new_) rest' in
  map fst (close (kit_arith_atoms goal) [] tagged);;

let DECIDE_TAC : tactic = fun (asl,w as g) ->
  let facts = filter (kit_is_arith o concl) (map snd asl) in
  let rel = kit_relevant_facts w facts in
  let with_facts fs = MAP_EVERY MP_TAC fs THEN ARITH_TAC in
  if length rel = length facts then with_facts facts g else
  (with_facts rel ORELSE with_facts facts) g;;

(* HOL Light's ASM_ARITH_TAC (every assumption that is not universally      *)
(* quantified, then ARITH_TAC), redefined: with at least                    *)
(* kit_asm_arith_min assumptions, first ARITH_TAC with only the arithmetic  *)
(* assumptions that share an atom with the goal (as DECIDE_TAC), and HOL    *)
(* Light's tactic only if that fails, so the same goals are proved (with    *)
(* the same theorems), faster in big contexts (the full load spent 195 s in *)
(* ASM_ARITH_TAC calls over 0.3 s with 10 or more assumptions).  HOL        *)
(* Light's tactic at once when the first try cannot succeed: an assumption  *)
(* F or ~T (which HOL Light's uses at once), or a goal without arithmetic   *)
(* atoms (such as F).  Since 2026-11-20.                                    *)
let kit_asm_arith_min = ref 10;;

let ASM_ARITH_TAC : tactic =
  let hol = ASM_ARITH_TAC in
  let f_tm = `F` and t_tm = `T` in
  let absurd tm = tm = f_tm || (is_neg tm && rand tm = t_tm) in
  fun (asl,w as g) ->
    if length asl < !kit_asm_arith_min || exists (fun (_,th) -> absurd (concl th)) asl ||
       kit_arith_atoms w = [] then hol g else
    let facts = filter (kit_is_arith o concl) (map snd asl) in
    let rel = kit_relevant_facts w facts in
    if length rel = length asl then hol g else
    try (MAP_EVERY MP_TAC rel THEN ARITH_TAC) g with Failure _ -> hol g;;

(* ------------------------------------------------------------------------- *)
(* ARITH_ss (HOL4 ARITH_ss, for the easy cases): a marker theorem; any kit   *)
(* simplification tactic given it in its list (SIMP[ARITH_ss], FS, RFS, GVS, *)
(* RW, CAKE_SIMP_CONV, ...) also                                             *)
(*  - decides relations of num (<, <=, =, >, >=) by linear arithmetic, with  *)
(*    the arithmetic facts of the context that share an atom with them       *)
(*    (assumptions and antecedents; at most kit_arith_max_facts of them);    *)
(*    the results, also failures, are cached;                                *)
(*  - cancels numerals in a subtraction: (m + n + 1) - 1 = m + n;            *)
(*  - rewrites m < n - p to m + p < n.                                       *)
(* Without the marker nothing changes.  The decision is made through the    *)
(* simplifier's conditional rewriting: m < n ==> (m < n <=> T) and           *)
(* ~(m < n) ==> (m < n <=> F), with the conditions guarded by ARITH_COND     *)
(* (the identity) and proved by an arithmetic prover that holds the context  *)
(* (never by simplification, which would apply the same rewrites again).    *)
(* ------------------------------------------------------------------------- *)

let ARITH_ss = CONJUNCT1 (CONJ TRUTH TRUTH);;

let ARITH_COND_DEF = new_definition `ARITH_COND (p:bool) <=> p`;;

let kit_arith_cond_tm = `ARITH_COND`;;

let kit_arith_max_facts = ref 10;;

let kit_arith_cache = (Hashtbl.create 1000 : (term,thm option) Hashtbl.t);;

(* |- p from facts (the context), by ARITH_RULE on the relevant facts *)
let kit_arith_decide (facts:thm list) (p:term) : thm =
  let rel = kit_relevant_facts p facts in
  let rel = if length rel > !kit_arith_max_facts
            then fst (chop_list (!kit_arith_max_facts) rel) else rel in
  let key = itlist (curry mk_imp o concl) rel p in
  let res =
    try Hashtbl.find kit_arith_cache key with Not_found ->
      let r = try Some (ARITH_RULE key) with Failure _ -> None in
      (if Hashtbl.length kit_arith_cache > 50000 then Hashtbl.reset kit_arith_cache);
      Hashtbl.add kit_arith_cache key r; r in
  match res with
    Some ith -> rev_itlist (fun f th -> MP th f) rel ith
  | None -> failwith "kit_arith_decide";;

let kit_arith_prover =
  let apply facts tm =
    if not (is_comb tm && rator tm = kit_arith_cond_tm) then failwith "kit_arith_prover" else
    EQ_MP (SYM (SPEC (rand tm) ARITH_COND_DEF)) (kit_arith_decide facts (rand tm))
  and augment facts thl =
    filter (kit_is_arith o concl) (flat (map CONJUNCTS thl)) @ facts in
  mk_prover apply augment [];;

(* the condition prover of an ARITH_ss simpset: ARITH_COND conditions go to *)
(* the arithmetic prover, all others to HOL Light's basic_prover as before   *)
let kit_arith_condition_prover strat (Simpset(_,_,provers,_) as ss) lev tm =
  if is_comb tm && rator tm = kit_arith_cond_tm
  then tryfind (fun pr -> apply_prover pr tm) provers
  else basic_prover strat ss lev tm;;

let kit_arith_ss_rewrites =
  let tac = REWRITE_TAC[ARITH_COND_DEF] in
  map (fun tm -> prove(tm,tac))
   [`!m n:num. ARITH_COND (m < n) ==> (m < n <=> T)`;
    `!m n:num. ARITH_COND (~(m < n)) ==> (m < n <=> F)`;
    `!m n:num. ARITH_COND (m <= n) ==> (m <= n <=> T)`;
    `!m n:num. ARITH_COND (~(m <= n)) ==> (m <= n <=> F)`;
    `!m n:num. ARITH_COND (m = n) ==> (m = n <=> T)`;
    `!m n:num. ARITH_COND (~(m = n)) ==> (m = n <=> F)`;
    `!m n:num. ARITH_COND (m > n) ==> (m > n <=> T)`;
    `!m n:num. ARITH_COND (~(m > n)) ==> (m > n <=> F)`;
    `!m n:num. ARITH_COND (m >= n) ==> (m >= n <=> T)`;
    `!m n:num. ARITH_COND (~(m >= n)) ==> (m >= n <=> F)`] @
  [ARITH_RULE `!m n p:num. m < n - p <=> m + p < n`];;

(* (... + k + ...) - j with numerals k >= j: the sum with k - j for k *)
let kit_sub_numeral_conv tm =
  let a,b = dest_binary "-" tm in
  if not (is_numeral b) || type_of b <> kit_num_ty then failwith "kit_sub_numeral_conv" else
  let summands = striplist (dest_binary "+") a in
  let nums,others = partition is_numeral summands in
  if nums = [] || others = [] then failwith "kit_sub_numeral_conv" else
  let c = itlist (fun t s -> dest_numeral t +/ s) nums (num 0) and k = dest_numeral b in
  if c </ k then failwith "kit_sub_numeral_conv" else
  let r = c -/ k in
  let target = if r =/ num 0 then list_mk_binop `(+):num->num->num` others
               else list_mk_binop `(+):num->num->num` (others @ [mk_numeral r]) in
  ARITH_RULE (mk_eq(tm,target));;

let kit_arith_ss (ss:simpset) : simpset =
  let ss1 = ss_of_conv `m - n:num` kit_sub_numeral_conv (ss_of_thms kit_arith_ss_rewrites ss) in
  ss_of_prover kit_arith_condition_prover (ss_of_provers [kit_arith_prover] ss1);;

(* ------------------------------------------------------------------------- *)
(* ARITH_LIN_ss: ARITH_ss and the normalisation of linear num terms of       *)
(* HOL4's ARITH_ss (numSimps CTXT_ARITH on terms of type num, with           *)
(* lin_of_term and term_of_lin): a sum or difference is put in the normal    *)
(* form (p1 + .. + pk + c) - (n1 + .. + nm), the atoms sorted, like atoms    *)
(* and numerals collected (x + x becomes 2 times x); with no subtraction     *)
(* among its summands always (an identity), with one only when the           *)
(* arithmetic facts of the context prove it (cut-off subtraction):           *)
(* n - 1 + 1 = n under ~(n = 0), a - n + n + m = a + m under n <= a, and     *)
(* k - 1 - (c - 1 - x) and k - (c - x) both (k + x) - c when the context     *)
(* allows.  The normal form of a normal form is itself, so it cannot loop;   *)
(* the proofs are cached (ARITH_RULE).  A separate marker: ARITH_ss is       *)
(* unchanged (the existing proofs use it).  Since 2026-11-20.                *)
(* ------------------------------------------------------------------------- *)

let ARITH_LIN_ss = CONJUNCT2 (CONJ TRUTH (CONJ TRUTH TRUTH));;

(* the linear form of a num term: (atom, coefficient) list sorted by atom, *)
(* and a constant; a subtraction gives negative coefficients (HOL4         *)
(* lin_of_term: +, -, numerals, numeral times t; anything else an atom)   *)
let kit_lin_of_term (tm:term) : (term * num) list * num =
  let add t c l =
    let rec ins l = match l with
        [] -> [t,c]
      | (u,d)::rest -> if u = t then (u,d +/ c)::rest else (u,d)::ins rest in
    ins l in
  let rec go tm sign (l,k) =
    match tm with
      Comb(Comb(Const("+",_),a),b) -> go b sign (go a sign (l,k))
    | Comb(Comb(Const("-",_),a),b) -> go b (minus_num sign) (go a sign (l,k))
    | Comb(Comb(Const("*",_),a),b) when is_numeral a ->
        add b (sign */ dest_numeral a) l,k
    | _ -> if is_numeral tm then l,k +/ (sign */ dest_numeral tm)
           else add tm sign l,k in
  let l,k = go tm (num 1) ([],num 0) in
  sort (fun (a,_) (b,_) -> compare a b < 0) (filter (fun (_,c) -> not (c =/ num 0)) l),k;;

let kit_num_add_tm = `(+):num->num->num` and kit_num_sub_tm = `(-):num->num->num`
and kit_num_mul_tm = `( * ):num->num->num`;;

(* HOL4 term_of_lin: (positive summands + constant) - (negative ones) *)
let kit_term_of_lin ((l,k):(term * num) list * num) : term =
  let mk (t,c) = if c =/ num 1 then t else mk_binop kit_num_mul_tm (mk_numeral c) t in
  let pos = map mk (filter (fun (_,c) -> c >/ num 0) l)
  and neg = map (fun (t,c) -> mk (t,minus_num c)) (filter (fun (_,c) -> c </ num 0) l) @
            (if k </ num 0 then [mk_numeral (minus_num k)] else []) in
  let sum l = end_itlist (mk_binop kit_num_add_tm) l in
  if k >/ num 0 then
    let kt = mk_numeral k in
    if pos = [] then (if neg = [] then kt else mk_binop kit_num_sub_tm kt (sum neg))
    else if neg = [] then sum (pos @ [kt])
    else mk_binop kit_num_sub_tm (sum (pos @ [kt])) (sum neg)
  else if pos = [] then (if neg = [] then kit_num_zero else failwith "kit_term_of_lin")
  else if neg = [] then sum pos
  else mk_binop kit_num_sub_tm (sum pos) (sum neg);;

let kit_lin_cache = (Hashtbl.create 1000 : (term,thm option) Hashtbl.t);;

(* tm = nf, or ARITH_COND (tm = nf) ==> tm = nf if a summand of tm (split *)
(* at +) is a subtraction (proved by the arithmetic prover with the       *)
(* context); fails on a normal form                                       *)
let kit_lin_norm_conv (tm:term) : thm =
  if not (type_of tm = kit_num_ty) then failwith "kit_lin_norm_conv" else
  let nf = kit_term_of_lin (kit_lin_of_term tm) in
  if nf = tm then failwith "kit_lin_norm_conv: normal form" else
  let eq = mk_eq(tm,nf) in
  let has_minus = exists (fun t -> is_comb t && is_comb (rator t) &&
                                   rator (rator t) = kit_num_sub_tm)
                         (striplist (dest_binary "+") tm) in
  if has_minus then
    let c = mk_comb(kit_arith_cond_tm,eq) in
    DISCH c (EQ_MP (SPEC eq ARITH_COND_DEF) (ASSUME c))
  else
    let r = try Hashtbl.find kit_lin_cache eq with Not_found ->
      let r = try Some (ARITH_RULE eq) with Failure _ -> None in
      (if Hashtbl.length kit_lin_cache > 50000 then Hashtbl.reset kit_lin_cache);
      Hashtbl.add kit_lin_cache eq r; r in
    match r with Some th -> th | None -> failwith "kit_lin_norm_conv";;

let kit_arith_lin_ss (ss:simpset) : simpset =
  ss_of_conv `m + n:num` kit_lin_norm_conv
    (ss_of_conv `m - n:num` kit_lin_norm_conv (kit_arith_ss ss));;

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* HOL4 ELIM_UNCURRY: a paired lambda \(x1,..,xn). t (HOL4 UNCURRY) becomes *)
(* \p. t with the xi replaced by FST p, FST (SND p), ..; ELIM_UNCURRY_CONV  *)
(* on such a lambda, or ELIM_UNCURRY in the list of a kit simplification     *)
(* tactic (a marker, like ARITH_ss; since 2026-11-18).                      *)
(* ------------------------------------------------------------------------- *)

let ELIM_UNCURRY_CONV : conv = fun tm ->
  if is_abs tm then failwith "ELIM_UNCURRY_CONV" else
  let vstr,bod = try dest_gabs tm with Failure _ -> failwith "ELIM_UNCURRY_CONV" in
  if not (is_pair vstr) then failwith "ELIM_UNCURRY_CONV" else
  let p = variant (frees tm) (mk_var("p",type_of vstr)) in
  let rec projs v t =
    if is_pair v then
      let l,r = dest_pair v in
      projs l (mk_icomb(mk_const("FST",[]),t)) @ projs r (mk_icomb(mk_const("SND",[]),t))
    else [t,v] in
  prove(mk_eq(tm,mk_abs(p,vsubst (projs vstr p) bod)),
        REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; FST; SND]);;

let ELIM_UNCURRY = CONJUNCT2 (CONJ TRUTH TRUTH);;

(* ------------------------------------------------------------------------- *)
(* ONCE th (HOL4 Once th) in the list of a kit simplification tactic: the   *)
(* rewrites of th (equations or iffs, unconditional) are used once in each  *)
(* call of the tactic, at the first subterm (top down) where one applies;  *)
(* e.g. SIMP[ONCE red_rel_cases].  ONCE th is |- CAKE_ONCE t for th |- t   *)
(* (a marker; since 2026-11-18).                                            *)
(* ------------------------------------------------------------------------- *)

let CAKE_ONCE_DEF = new_definition `CAKE_ONCE (p:bool) <=> p`;;

let kit_once_tm = `CAKE_ONCE`;;

let ONCE (th:thm) : thm = EQ_MP (SYM (SPEC (concl th) CAKE_ONCE_DEF)) th;;

let kit_is_once (th:thm) =
  let c = concl th in is_comb c && rator c = kit_once_tm;;

(* the rewrites of the theorem under a ONCE marker, as (key, conversion)   *)
(* pairs sharing a flag: once one of them has rewritten, they all fail     *)
let kit_once_convs (mth:thm) : bool ref * (term * conv) list =
  let th = EQ_MP (SPEC (rand (concl mth)) CAKE_ONCE_DEF) mth in
  let used = ref false in
  let rws = mk_rewrites false th [] in
  let mk rw =
    let cnv = REWR_CONV rw in
    lhs (concl rw),
    (fun tm -> if !used then failwith "ONCE: used" else
               let r = cnv tm in used := true; r) in
  used,map mk rws;;

(* ------------------------------------------------------------------------- *)
(* NOT_ss (HOL4 boolSimps.NOT_ss, a part of HOL4's bool_ss and so of its     *)
(* srw_ss, simp, fs, rw and gvs): a marker for the list of a kit             *)
(* simplification tactic.  Negations are moved inwards with NOT_IMP,        *)
(* DE_MORGAN_THM, NOT_FORALL_THM, NOT_EXISTS_THM and                        *)
(* (~p <=> ~q) <=> (p <=> q), so FS[NOT_ss] splits an assumption ~(a \/ b)  *)
(* into ~a and ~b; RW[NOT_ss] also breaks up such assumptions               *)
(* (~(a \/ b), ~(a ==> b), ~(?x. P x), ~(!x. P x)) as HOL4's rw does.      *)
(* Opt-in: the default simpset, that of HOL Light's basic rewrites, has    *)
(* none of these (they would change what the existing proofs see).  Since  *)
(* 2026-11-20.                                                               *)
(* ------------------------------------------------------------------------- *)

let NOT_ss = CONJUNCT1 (CONJ TRUTH (CONJ TRUTH TRUTH));;

let kit_not_ss_rewrites =
  [NOT_IMP; DE_MORGAN_THM; NOT_FORALL_THM; NOT_EXISTS_THM;
   TAUT `!p q. (~p <=> ~q) <=> (p <=> q)`];;

(* ------------------------------------------------------------------------- *)
(* RECORD_SELFID_ss (HOL4's rec_fupdselfid theorems of srw_ss): a marker for *)
(* the list of a kit simplification tactic; every record's rules           *)
(* rec_f_fupd (K (rec_f r)) r = r (HOL4 r with f := r.f = r) are added.     *)
(* Not in the default simpset: the full load of 2026-11-20 showed existing  *)
(* proofs that rely on their absence (word_bignumProof).  cake_record      *)
(* (record.ml) adds the rules of each new record to kit_record_selfids,    *)
(* proved when first used.                                                  *)
(* ------------------------------------------------------------------------- *)

let RECORD_SELFID_ss = CONJUNCT2 (CONJ TRUTH (CONJ TRUTH (CONJ TRUTH TRUTH)));;

let kit_record_selfids = ref ([] : thm Lazy.t list);;

(* ------------------------------------------------------------------------- *)
(* CONGR th (HOL4 Cong th) in the list of a kit simplification tactic: th is *)
(* used as a congruence rule (HOL Light's ss_of_congs), not as a rewrite.   *)
(* th is a1 ==> .. ==> (l = r) with each ai of the form !vs. t = t' or      *)
(* !vs. c ==> t = t' (the context c is assumed while t is simplified to t'), *)
(* e.g. HOL4's MAP_CONG; conjunctive antecedents are curried first, as HOL4 *)
(* does (normCong).  CONGR th is |- CAKE_CONG t for th |- t (a marker; since *)
(* 2026-11-20).                                                              *)
(* ------------------------------------------------------------------------- *)

let CAKE_CONG_DEF = new_definition `CAKE_CONG (p:bool) <=> p`;;

let kit_cong_tm = `CAKE_CONG`;;

let CONGR (th:thm) : thm = EQ_MP (SYM (SPEC (concl th) CAKE_CONG_DEF)) th;;

let kit_is_cong (th:thm) =
  let c = concl th in is_comb c && rator c = kit_cong_tm;;

let kit_cong_rule (mth:thm) : thm =
  let th = EQ_MP (SPEC (rand (concl mth)) CAKE_CONG_DEF) mth in
  SPEC_ALL (PURE_REWRITE_RULE[GSYM IMP_IMP] (SPEC_ALL th));;

(* the project simpset augmented with thl: SIMPLIFY_CONV (CAKE_AUGMENTED_SS *)
(* thl) l is SIMPLIFY_CONV (cake_active_ss()) (l @ thl) (AUGMENT_SIMPSET    *)
(* works from the right of the list).  Made when the tactic runs, once per  *)
(* call of a tactic that simplifies many assumptions, and kept in a memo    *)
(* like the rewrite nets above (same simpset, same theorems).  The markers  *)
(* ARITH_ss, ELIM_UNCURRY and ONCE th add their conversions; the flags of   *)
(* the ONCE rewrites are reset at each call.                                *)

let cake_ss_memo = ref ([] : ((simpset * thm list) * (simpset * bool ref list)) list);;

let kit_augment ss thl =
  let is_mark th = th == ARITH_ss || th == ELIM_UNCURRY || kit_is_once th ||
                   th == NOT_ss || kit_is_cong th || th == ARITH_LIN_ss ||
                   th == RECORD_SELFID_ss in
  if not (exists is_mark thl) then itlist AUGMENT_SIMPSET thl ss,[] else
  let plain = filter (fun th -> not (is_mark th)) thl in
  let ss = if exists (fun th -> th == NOT_ss) thl then ss_of_thms kit_not_ss_rewrites ss
           else ss in
  let ss = if exists (fun th -> th == RECORD_SELFID_ss) thl
           then ss_of_thms (flat (map (CONJUNCTS o Lazy.force) !kit_record_selfids)) ss
           else ss in
  let congs = filter kit_is_cong thl in
  let ss = if congs = [] then ss else ss_of_congs (map kit_cong_rule congs) ss in
  let ss1 = if exists (fun th -> th == ARITH_LIN_ss) thl then kit_arith_lin_ss ss
            else if exists (fun th -> th == ARITH_ss) thl then kit_arith_ss ss else ss in
  let ss2 = if exists (fun th -> th == ELIM_UNCURRY) thl
            then ss_of_conv `GABS (f:(A->B)->bool)` ELIM_UNCURRY_CONV ss1 else ss1 in
  let ss3,flags =
    itlist (fun mth (ss,fl) ->
              let r,cnvs = kit_once_convs mth in
              itlist (fun (k,c) ss -> ss_of_conv k c ss) cnvs ss, r::fl)
           (filter kit_is_once thl) (ss2,[]) in
  itlist AUGMENT_SIMPSET plain ss3,flags;;

let CAKE_AUGMENTED_SS thl =
  let ss = cake_active_ss() in
  let ss',flags =
    cake_memo cake_ss_memo (fun (s,l) -> s == ss && cake_same_thms l thl) (ss,thl)
      (fun () -> kit_augment ss thl) in
  do_list (fun r -> r := false) flags;
  kit_current_once_flags := flags;
  ss';;

(* simplify the goal with the assumptions and an augmented simpset *)
let SIMP_SS ss : tactic = ASM (fun l -> CONV_TAC (SIMPLIFY_CONV ss l)) [];;

let CAKE_SIMP_CONV thl tm = SIMPLIFY_CONV (CAKE_AUGMENTED_SS thl) [] tm;;

let CAKE_SIMP_RULE thl = CONV_RULE (CAKE_SIMP_CONV thl);;

(* HOL4 simp_tac (no assumptions) and simp (= asm_simp_tac) *)

let SIMP_NOASM thl = CONV_TAC (CAKE_SIMP_CONV thl);;

let SIMP thl : tactic = fun gl -> SIMP_SS (CAKE_AUGMENTED_SS thl) gl;;

(* ------------------------------------------------------------------------- *)
(* Putting a simplified assumption back: closes the goal if it is F (or the *)
(* goal itself), drops it if it is T, else strips it in (conjunctions,      *)
(* disjunctions = case splits, existentials).                               *)
(* ------------------------------------------------------------------------- *)

(* T and F, parsed once: a quotation in a function body is parsed at each  *)
(* call, which costs milliseconds in a session with thousands of constants *)

let cake_true_tm = `T` and cake_false_tm = `F`;;

(* stripping that never fails on name clashes: every existential gets a     *)
(* name that is fresh for the whole goal and the theorem (HOL Light's        *)
(* STRIP_ASSUME_TAC can fail with CHOOSE when an inner bound name is free    *)
(* in a later conjunct); the goal's variables include those free only in    *)
(* the hypotheses of an assumption theorem (a variable eliminated by SUBS   *)
(* stays there), and av those of assumptions not put back yet (FS, RFS)     *)

(* the name of a new variable: HOL Light's variant avoids only variables  *)
(* of the same name and type, so a case split can leave x:num beside       *)
(* x:state (the q-tactics and RENAME1 then cannot tell them apart).  As    *)
(* HOL4's variant and HOL Light's own CHOOSE_TAC (mk_primed_var), names in *)
(* use by any free variable can be avoided: in the files that call        *)
(* cake_distinct_names () (or everywhere, kit_distinct_names := true).     *)
(* Not the default: existing proofs use the old names (the full load of    *)
(* 2026-11-20 broke at flat_patternProof compile_pat_bindings_simulation).  *)
(* Check mode: KITDIFF where a name differs.  Since 2026-11-20.            *)
let kit_distinct_names = ref false;;

(* files that asked for distinct names with cake_distinct_names () (when    *)
(* kit_distinct_names is false): the file being loaded (or the one named by *)
(* cake_begin) is looked up when a name is chosen                           *)
let kit_distinct_files = ref ([] : string list);;

let kit_names_distinct () =
  !kit_distinct_names ||
  (!kit_distinct_files <> [] &&
   (match !cake_loading with
      f::_ -> mem f !kit_distinct_files
    | [] -> (match !cake_context with Some f -> mem f !kit_distinct_files | None -> false)));;

let cake_distinct_names () =
  match !cake_loading with
    f::_ -> kit_distinct_files := f :: !kit_distinct_files
  | [] -> (match !cake_context with
             Some f -> kit_distinct_files := f :: !kit_distinct_files
           | None -> kit_distinct_names := true);;

(* mk_primed_var with the kit's table of constants (parse.ml) instead of   *)
(* get_const_type, a search of the list of all constants for every name   *)
(* tried: the same variables                                               *)
let kit_primed_var (avoid:term list) (v:term) : term =
  cake_ptab_sync ();
  let names = mapfilter (fst o dest_var) avoid in
  let s,ty = dest_var v in
  let rec svariant s =
    if mem s names || (Hashtbl.mem cake_ptab_consts s && not (is_hidden s))
    then svariant (s^"'") else s in
  mk_var(svariant s,ty);;

let kit_fresh_var (avoid:term list) (v:term) : term =
  let old = variant avoid v in
  if !kit_check then
    (let nw = kit_primed_var avoid v in
     if not (nw = old) then kit_diff "names across types";
     old)
  else if kit_names_distinct () then kit_primed_var avoid v else old;;

let rec CAKE_STRIP_ASSUME_AV (av:term list) th : tactic =
  fun (asl,w as gl) ->
    let c = concl th in
    if c = cake_true_tm then ALL_TAC gl
    else if c = cake_false_tm then CONTR_TAC th gl
    else if is_conj c then
      let c1,c2 = dest_conj c in
      CONJUNCTS_THEN2 (CAKE_STRIP_ASSUME_AV (union av (frees c2)))
                      (CAKE_STRIP_ASSUME_AV av) th gl
    else if is_disj c then
      DISJ_CASES_THEN (CAKE_STRIP_ASSUME_AV av) th gl
    else if is_exists c then
      let v,_ = dest_exists c in
      let avoid = itlist (union o thm_frees o snd) asl
                    (union av (union (frees w)
                      (union (frees c) (freesl (hyp th))))) in
      let v' = kit_fresh_var avoid v in
      X_CHOOSE_THEN v' (CAKE_STRIP_ASSUME_AV (v'::av)) th gl
    else ASSUME_TAC th gl;;

let CAKE_STRIP_ASSUME_TAC th = CAKE_STRIP_ASSUME_AV [] th;;

let CAKE_ASSUME_TAC th =
  let c = concl th in
  if c = cake_true_tm then ALL_TAC
  else if c = cake_false_tm then CONTR_TAC th
  else CAKE_STRIP_ASSUME_TAC th;;

(* the same, also avoiding the variables av (of assumptions to come) *)
let CAKE_ASSUME_AV (av:term list) th =
  let c = concl th in
  if c = cake_true_tm then ALL_TAC
  else if c = cake_false_tm then CONTR_TAC th
  else CAKE_STRIP_ASSUME_AV av th;;

let CAKE_ASSUME_NOSTRIP_TAC th =
  let c = concl th in
  if c = cake_true_tm then ALL_TAC
  else if c = cake_false_tm then CONTR_TAC th
  else ASSUME_TAC th;;

(* t = C x or C x = t, with C a constructor: (t, C x) *)
let kit_cons_eq tm =
  if not (is_eq tm) then failwith "kit_cons_eq" else
  let l,r = dest_eq tm in
  if is_constructor_app r && not (is_numeral r) && not (is_constructor_app l) then l,r
  else if is_constructor_app l && not (is_numeral l) && not (is_constructor_app r)
  then r,l
  else failwith "kit_cons_eq";;

(* After the assumptions of FS or RFS are simplified: two equations of one   *)
(* term t with constructor applications, t = C x and t = D y in either      *)
(* orientation (C x = t), give C x = D y simplified (x = y, or F), unless   *)
(* that is already an assumption.  The simplification of the assumptions in *)
(* one order merges such a pair only when the older one has t on the left   *)
(* (FS) or the newer one (RFS); HOL4's fs has the order of RFS.  Since      *)
(* 2026-11-18.                                                              *)

let kit_fs_merge (newer_first:bool) ss : tactic = fun (asl,w as g) ->
  let eqs = mapfilter (fun (_,th) -> let t,r = kit_cons_eq (concl th) in t,r,th) asl in
  let rec pairs l = match l with [] -> [] | x::rest -> map (fun y -> x,y) rest @ pairs rest in
  let cands = filter (fun ((t1,r1,_),(t2,r2,_)) -> aconv t1 t2 && not (aconv r1 r2))
                     (pairs eqs) in
  if cands = [] then ALL_TAC g else
  let orient th t = if aconv (lhs(concl th)) t then th else SYM th in
  (* a1 is newer than a2; the result is oriented as the simplification of  *)
  (* the newer (FS) or of the older (RFS) one would give it                 *)
  let facts = mapfilter (fun ((t1,_,a1),(t2,_,a2)) ->
      let eqth = if newer_first then TRANS (SYM (orient a1 t1)) (orient a2 t2)
                 else TRANS (SYM (orient a2 t2)) (orient a1 t1) in
      let fth = CONV_RULE (SIMPLIFY_CONV ss []) eqth in
      if concl fth = cake_true_tm ||
         exists (fun (_,a) -> aconv (concl a) (concl fth)) asl
      then fail() else fth) cands in
  if facts = [] then ALL_TAC g else
  (kit_note "FS merge"; MAP_EVERY CAKE_ASSUME_TAC facts g);;

(* ------------------------------------------------------------------------- *)
(* FS: HOL4 full_simp_tac (srw_ss()) thl.                                    *)
(* ------------------------------------------------------------------------- *)

let FS thl : tactic =
  fun gl ->
   let ss = CAKE_AUGMENTED_SS thl in
   (POP_ASSUM_LIST (fun asms ->
      let simped =
        rev_itlist (fun th acc -> CONV_RULE (SIMPLIFY_CONV ss acc) th :: acc)
                   (rev asms) [] in
      let av = itlist (union o thm_frees) simped [] in
      MAP_EVERY (CAKE_ASSUME_AV av) (rev simped)) THEN
    kit_fs_merge false ss THEN SIMP_SS ss) gl;;

(* ------------------------------------------------------------------------- *)
(* RFS: FS in the other order: each assumption, newest first, is simplified *)
(* with the newer ones (already simplified), so that old assumptions such   *)
(* as induction hypotheses are instantiated by the facts found after them;  *)
(* then the goal.  Note on HOL4: its full_simp_tac (fs) takes the NEWEST     *)
(* assumption first, like RFS, and rev_full_simp_tac (rfs) the oldest       *)
(* first, like FS (HOL4 simpLib GEN_FULL_SIMP_TAC; its help: each          *)
(* assumption is used to rewrite lower-numbered ones, 0 the oldest).        *)
(* ------------------------------------------------------------------------- *)

let RFS thl : tactic =
  fun gl ->
   let ss = CAKE_AUGMENTED_SS thl in
   (POP_ASSUM_LIST (fun asms ->
      let simped =
        rev_itlist (fun th acc -> CONV_RULE (SIMPLIFY_CONV ss acc) th :: acc)
                   asms [] in
      let av = itlist (union o thm_frees) simped [] in
      MAP_EVERY (CAKE_ASSUME_AV av) simped) THEN
    kit_fs_merge true ss THEN SIMP_SS ss) gl;;

(* ------------------------------------------------------------------------- *)
(* Variable elimination.  An assumption v = t or t = v with v a variable not *)
(* free in t is used to substitute t for v everywhere and is then dropped.   *)
(* ------------------------------------------------------------------------- *)

let is_eliminable tm =
  is_eq tm &&
  let l,r = dest_eq tm in
  (is_var l && not (free_in l r)) || (is_var r && not (free_in r l));;

(* SUBST_ALL_TAC rth, but SUBS only the assumptions in which the left side  *)
(* of rth occurs free: SUBS leaves the others as they are anyway (and costs  *)
(* a substitution and two beta reductions per assumption)                   *)
let CAKE_SUBST_ALL_TAC rth : tactic =
  fun gl ->
    let l = lhand(concl rth) in
    (SUBST1_TAC rth THEN
     RULE_ASSUM_TAC (fun th -> if free_in l (concl th) then SUBS [rth] th else th)) gl;;

let VSUBST_ASM_TAC th =
  let l,r = dest_eq(concl th) in
  let th' = if is_var l && not (free_in l r) then th else SYM th in
  (* th' : v = t; replace v by t *)
  let v = lhs(concl th') in
  if not (is_var v) then failwith "VSUBST_ASM_TAC" else
  CAKE_SUBST_ALL_TAC th' THEN
  (* drop the trivial assumption t = t that remains *)
  REPEAT (FIRST_X_ASSUM (fun a -> if is_eq(concl a) &&
                                     lhs(concl a) = rhs(concl a)
                                  then ALL_TAC else failwith "keep"));;

let VAR_EQ_TAC : tactic =
  FIRST_X_ASSUM (fun th ->
    if is_eliminable (concl th) then VSUBST_ASM_TAC th
    else failwith "VAR_EQ_TAC");;

let RVEQ_TAC = REPEAT VAR_EQ_TAC;;

(* ------------------------------------------------------------------------- *)
(* GVS: HOL4 gvs[thl] = global_simp_tac {droptrues, elimvars, oldestfirst,   *)
(* strip}: repeatedly pop the oldest assumption, simplify it with all the    *)
(* others, eliminate it if it is a var equation, else strip it back in at    *)
(* the end; until nothing changes; then simplify the goal.                   *)
(* ------------------------------------------------------------------------- *)

(* pop the OLDEST assumption (the last of HOL Light's list) *)

let POP_LAST_ASSUM (ttac:thm_tactic) : tactic =
  fun (asl,w) ->
    match rev asl with
      [] -> failwith "POP_LAST_ASSUM"
    | (_,th)::rest -> ttac th (rev rest,w);;

(* the steps with the simpset already augmented with thl *)

(* putting a simplified assumption back in GVS: as CAKE_ASSUME_TAC, but a  *)
(* branch of its case splits is closed at once when it assumes t = C x      *)
(* while an assumption says t = D y, with C and D different constructors    *)
(* (GVS would close it later anyway, after many more steps: the nested case *)
(* equations of an evaluate assumption split into 1395 goals of which a     *)
(* handful survive)                                                         *)

(* |- F from th : t = C x and an assumption t = D y *)
let kit_clash ss (asl:(string * thm) list) (th:thm) : thm =
  let t,r = kit_cons_eq (concl th) in
  let h = fst(strip_comb r) in
  let _,a = find (fun (_,a) ->
              try let t',r' = kit_cons_eq (concl a) in
                  aconv t' t && not (fst(strip_comb r') = h)
              with Failure _ -> false) asl in
  let orient th = if aconv (lhs(concl th)) t then th else SYM th in
  let eqth = TRANS (SYM (orient a)) (orient th) in
  let fth = EQ_MP (SIMPLIFY_CONV ss [] (concl eqth)) eqth in
  if concl fth = cake_false_tm then fth else failwith "kit_clash";;

let rec KIT_GVS_STRIP_AV ss (av:term list) th : tactic =
  fun (asl,w as gl) ->
    let c = concl th in
    if c = cake_true_tm then ALL_TAC gl
    else if c = cake_false_tm then CONTR_TAC th gl
    else if is_conj c then
      let c1,c2 = dest_conj c in
      CONJUNCTS_THEN2 (KIT_GVS_STRIP_AV ss (union av (frees c2)))
                      (KIT_GVS_STRIP_AV ss av) th gl
    else if is_disj c then
      DISJ_CASES_THEN (KIT_GVS_STRIP_AV ss av) th gl
    else if is_exists c then
      let v,_ = dest_exists c in
      let avoid = itlist (union o thm_frees o snd) asl
                    (union av (union (frees w)
                      (union (frees c) (freesl (hyp th))))) in
      let v' = kit_fresh_var avoid v in
      X_CHOOSE_THEN v' (KIT_GVS_STRIP_AV ss (v'::av)) th gl
    else (try CONTR_TAC (kit_clash ss asl th) gl
          with Failure _ -> ASSUME_TAC th gl);;

let KIT_GVS_ASSUME_TAC ss th =
  let c = concl th in
  if c = cake_true_tm then ALL_TAC
  else if c = cake_false_tm then CONTR_TAC th
  else KIT_GVS_STRIP_AV ss [] th;;

let GVS_STEP_SS ss : tactic =
  POP_LAST_ASSUM (fun th ->
    ASSUM_LIST (fun asms ->
      let th' = CONV_RULE (SIMPLIFY_CONV ss asms) th in
      if is_eliminable (concl th') then VSUBST_ASM_TAC th'
      else KIT_GVS_ASSUME_TAC ss th'));;

let GVS_ONE_PASS_SS ss : tactic =
  fun (asl,w as gl) -> EVERY (replicate (GVS_STEP_SS ss) (length asl)) gl;;

let GVS_STEP thl : tactic =
  fun gl -> GVS_STEP_SS (CAKE_AUGMENTED_SS thl) gl;;

let GVS_ONE_PASS thl : tactic =
  fun gl -> GVS_ONE_PASS_SS (CAKE_AUGMENTED_SS thl) gl;;

let GVS thl : tactic =
  fun gl ->
   let ss = CAKE_AUGMENTED_SS thl in
   (REPEAT (CHANGED_TAC (GVS_ONE_PASS_SS ss)) THEN SIMP_SS ss THEN
    RVEQ_TAC) gl;;

(* GVS_ASM thl: GVS on the assumptions only: the goal is not simplified    *)
(* (it gets only the substitutions of the eliminated variables), so case    *)
(* expressions of the goal are not expanded when only an assumption (an    *)
(* evaluation) needs splitting (no HOL4 counterpart; gvs splits both).      *)
(* Since 2026-11-20.                                                         *)

let GVS_ASM thl : tactic =
  fun gl ->
   let ss = CAKE_AUGMENTED_SS thl in
   (REPEAT (CHANGED_TAC (GVS_ONE_PASS_SS ss)) THEN RVEQ_TAC) gl;;

(* ------------------------------------------------------------------------- *)
(* RW: HOL4 rw[thl] (srw_tac): strip the goal, eliminate var equations,      *)
(* simplify, split the goal's conditionals, strip again, simplify the        *)
(* assumptions that can be broken up or that equate constructors.            *)
(* ------------------------------------------------------------------------- *)

let BOSS_STRIP_TAC : tactic =
  GEN_TAC ORELSE CONJ_TAC ORELSE DISCH_THEN CAKE_ASSUME_TAC;;

let rw_breakable tm =
  is_exists tm || is_conj tm || is_disj tm || tm = cake_true_tm || tm = cake_false_tm ||
  (is_neg tm && is_neg(rand tm)) ||
  can (find_term (fun t -> is_eq t && is_constructor_app (lhs t) &&
                           is_constructor_app (rhs t))) tm;;

(* with NOT_ss also the negations that it moves inwards (since 2026-11-20) *)
let rw_not_breakable tm =
  is_neg tm && (let t = rand tm in is_disj t || is_imp t || is_exists t || is_forall t);;

let RW thl : tactic =
  fun gl ->
   let ss = CAKE_AUGMENTED_SS thl in
   let breakable =
     if exists (fun th -> th == NOT_ss) thl
     then (fun tm -> rw_breakable tm || rw_not_breakable tm) else rw_breakable in
   (REPEAT (GEN_TAC ORELSE CONJ_TAC) THEN
    RVEQ_TAC THEN
    SIMP_SS ss THEN
    TRY (COND_CASES_TAC THEN REPEAT COND_CASES_TAC THEN SIMP_SS ss) THEN
    REPEAT BOSS_STRIP_TAC THEN
    REPEAT (CHANGED_TAC
      (VAR_EQ_TAC ORELSE
       FIRST_X_ASSUM (fun th ->
         if breakable (concl th) then
           CAKE_ASSUME_TAC (CONV_RULE (SIMPLIFY_CONV ss []) th)
         else failwith "RW") ORELSE
       SIMP_SS ss))) gl;;
