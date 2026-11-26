(* ========================================================================= *)
(* CakeML kit: HOL Light's recursion machinery with conditionals in the      *)
(* contexts of recursive calls.                                              *)
(*                                                                           *)
(* This is the block of HOL Light's define.ml (John Harrison) that proves     *)
(* the existence of recursive functions (instantiate_casewise_recursion,     *)
(* pure_prove_recursive_function_exists, prove_general_recursive_function_  *)
(* exists; here cake_instantiate_casewise_recursion,                         *)
(* cake_pure_prove_recursive_function_exists and                             *)
(* cake_prove_general_recursive_function_exists, which leave HOL Light's     *)
(* functions of those names as they are, since 2026-11-25), copied with one  *)
(* change: the admissibility analysis also uses                              *)
(* ADMISSIBLE_COND for a conditional that is not in tail position (for       *)
(* example inside the arm of a match), so the condition becomes part of the  *)
(* context of the recursive calls under it.  Without that, a definition like *)
(*   f (CONS h t) = match t with [] -> 0 | CONS y z -> if y = 0 then 0       *)
(*                                                    else f (CONS (y-1) z) *)
(* gets the termination condition CONS (y-1) z << CONS h t with no y <> 0.   *)
(* A second addition: the table cake_admissible_rules of admissibility rules *)
(* for further constants, the analogue of HOL4's [defncong] congruence rules *)
(* (a recursive call under ALL, EX, IMAGE, ITLIST, ==> ... gets the context  *)
(* HOL4's congruence rule gives it); cake_register_admissible adds one.      *)
(* ========================================================================= *)

let cake_admissible_rules = ref ([] : (string * thm) list);;

(* lets in recursive definitions: unfolded (false, the default) or kept with *)
(* HOL4's LET_CONG context x = e (true; changes the termination conditions)  *)

let cake_let_cong = ref false;;

let cake_register_admissible c th =
  cake_admissible_rules :=
    (c,th) :: filter (fun (c',_) -> c' <> c) (!cake_admissible_rules);;

(* a rule's bound pattern variables (e.g. the a b of ADMISSIBLE_pair_CASE)  *)
(* renamed to the user's names, so that the termination conditions and the *)
(* induction theorem use them; set below                                    *)

let cake_rename_proforma =
  ref (fun (_:string list) (_:string list) (th:thm) -> th);;

(* the rule for a case constant and the arms of the goal; set below *)

let cake_case_rule_ref =
  ref (fun (_:term) (_:term list) -> (failwith "case rule" : thm));;

(* the same rule unrenamed, and the function that renames its arm variables *)
(* in it or in the version HACK_PROFORMA makes of it; set below              *)

let cake_case_rule_parts_ref =
  ref (fun (_:term) (_:term list) ->
         (failwith "case rule" : thm * (thm -> thm)));;

(* the same for cake_rename_proforma: a version of the rule whose renamed   *)
(* bound variables have names of their own, and the renaming; set below      *)

let cake_proforma_parts_ref =
  ref (fun (_:string list) (_:string list) (_:thm) ->
         (failwith "proforma parts" : thm * (thm -> thm)));;

(* compare the two ways of making the rule for a case constant (debugging) *)

let cake_check_case_hack = ref false;;

(* HOL Light's ADMISSIBLE_LAMBDA with a body of any type, not only bool: a  *)
(* recursive call in a lambda (a monadic continuation, a function-valued    *)
(* result) is then admissible with the lambda's variable in its context    *)

let CAKE_ADMISSIBLE_LAMBDA = prove
 (`!(<<) p (s:P->A) (t:(A->B)->C->P->D).
     admissible(<<) (\f (u,x). p f x) (\(u,x). s x) (\f (u,x). t f u x)
     ==> admissible(<<) p s (\f x. \u. t f u x)`,
  REWRITE_TAC[admissible; FUN_EQ_THM; FORALL_PAIR_THM] THEN MESON_TAC[]);;

(* GEN_BETA_CONV for a paired lambda whose pattern is a right-nested tuple    *)
(* of distinct variables (the paired lambdas of the recursion package over   *)
(* the variables of all the clauses): the same right side as GEN_BETA_CONV    *)
(* (the body with the components substituted by vsubst, so the same bound    *)
(* names), with the redex itself as left side.  GEN_BETA_CONV takes time      *)
(* cubic in the size of the tuple (seconds for 50 variables); this is about   *)
(* quadratic in it and linear in the body.  Other redexes: GEN_BETA_CONV.     *)

(* SPEC_ALL computes the free variables of the theorem again for every       *)
(* quantifier, which is quadratic in their number: the same theorem by SPECL *)
(* when the quantified variables are distinct and not free in the theorem    *)
(* (then SPEC_ALL keeps their names), else SPEC_ALL                          *)

let CAKE_SPEC_ALL th =
  let vs = fst(strip_forall(concl th)) in
  if vs = [] then th else
  let fvs = thm_frees th in
  if exists (fun v -> mem v fvs) vs || length (setify vs) <> length vs
  then SPEC_ALL th else SPECL vs th;;

let CAKE_GEN_BETA_CONV : conv =
  let cache = Hashtbl.create 16 in
  let rec rtuple vs t =
    match vs with
      [v] -> t = v
    | v::rest -> (try let a,b = dest_pair t in a = v && rtuple rest b
                  with Failure _ -> false)
    | [] -> false in
  (* |- ?w. !x1 .. xk. GEQ (w (x1,..,xk)) (b x1 .. xk) over A1 .. Ak, B,  *)
  (* with the witness \p. pair_CASE p (\z1 r1. pair_CASE r1 (\z2 r2. ..   *)
  (* (\z(k-1) zk. b z1 .. zk))) reduced level by level                    *)
  let lemma k =
    try Hashtbl.find cache k with Not_found ->
    let tys = map (fun i -> mk_vartype("A"^string_of_int i)) (1--k) in
    let bty = mk_vartype "B" in
    let xs = map2 (fun ty i -> mk_var("x"^string_of_int i,ty)) tys (1--k) in
    let zs = map2 (fun ty i -> mk_var("z%cgb"^string_of_int i,ty)) tys (1--k) in
    let b = mk_var("b%cgb",itlist mk_fun_ty tys bty) in
    let tup = end_itlist (curry mk_pair) xs in
    let w = mk_var("w%cgb",mk_fun_ty (type_of tup) bty) in
    let p = mk_var("p",type_of tup) in
    let pc e f = list_mk_icomb "pair_CASE" [e;f] in
    let rec fn i =
      if i = k - 1 then list_mk_abs([el (k-2) zs; el (k-1) zs],list_mk_comb(b,zs))
      else let r = mk_var("r%cgb"^string_of_int i,
                          type_of(end_itlist (curry mk_pair) (snd(chop_list i xs)))) in
           list_mk_abs([el (i-1) zs; r],pc r (fn (i + 1))) in
    let wit = mk_abs(p,pc p (fn 1)) in
    let rec red tm =
      let th1 = REWR_CONV pair_CASE tm in
      let th2 = TRANS th1 (BETAS_CONV (rand(concl th1))) in
      let r2 = rand(concl th2) in
      if is_comb r2 && is_comb(rator r2) && is_const(rator(rator r2)) &&
         fst(dest_const(rator(rator r2))) = "pair_CASE"
      then TRANS th2 (red r2) else th2 in
    let th0 = BETA_CONV (mk_comb(wit,tup)) in
    let th1 = TRANS th0 (red (rand(concl th0))) in
    let th2 = EQ_MP (SYM (ISPECL [mk_comb(wit,tup); list_mk_comb(b,xs)] GEQ_DEF)) th1 in
    let geq = mk_icomb(mk_const("GEQ",[]),mk_comb(w,tup)) in
    let stmt = mk_exists(w,list_mk_forall(xs,mk_comb(geq,list_mk_comb(b,xs)))) in
    let th = EXISTS (stmt,wit) (GENL xs th2) in
    Hashtbl.add cache k th; th in
  (* the instance for given types, kept: the clauses of one definition give *)
  (* thousands of redexes over the same tuple                              *)
  let icache = Hashtbl.create 16 in
  let ilemma k tyi =
    let key = (k,map fst tyi) in
    try Hashtbl.find icache key with Not_found ->
    let th = INST_TYPE tyi (lemma k) in
    if Hashtbl.length icache > 2000 then Hashtbl.reset icache;
    Hashtbl.add icache key th; th in
  let geq0 = mk_const("GEQ",[]) in
  let degeq = REWR_CONV GEQ_DEF in
  fun tm ->
    try BETA_CONV tm with Failure _ ->
    match tm with
      Comb(Comb(Const("GABS",_),(Abs(_,fb) as pp)) as l,r) ->
        let avs,gq = strip_forall fb in
        let k = length avs in
        let ok,vstr,bod =
          try let g1,bod = dest_comb gq in
              let gc,fv = dest_comb g1 in
              let f,vstr = dest_comb fv in
              (k >= 2 && is_const gc && fst(dest_const gc) = "GEQ" &&
               f = bndvar pp && rtuple avs vstr &&
               length (setify avs) = k),vstr,bod
          with Failure _ -> false,tm,tm in
        if not ok then GEN_BETA_CONV tm else
        let instn = term_match [] vstr r in
        let tys = map type_of avs and bty = type_of bod in
        let tyi = (bty,mk_vartype "B") ::
                  map2 (fun ty i -> ty,mk_vartype("A"^string_of_int i)) tys (1--k) in
        let th0 = ilemma k tyi in
        let w,_ = dest_exists(concl th0) in
        let b = mk_var("b%cgb",itlist mk_fun_ty tys bty) in
        let geq = inst [bty,aty] geq0 in
        let target = mk_exists(w,list_mk_forall(avs,
                       mk_comb(mk_comb(geq,mk_comb(w,vstr)),list_mk_comb(b,avs)))) in
        let th1 = EQ_MP (ALPHA (concl th0) target) th0 in
        let th2 = INST [list_mk_abs(avs,bod),b] th1 in
        let th3 = CONV_RULE (BINDER_CONV (funpow k BINDER_CONV
                                            (RAND_CONV BETAS_CONV))) th2 in
        let th4 = CONV_RULE degeq (CAKE_SPEC_ALL (SELECT_RULE th3)) in
        let th5 = AP_THM (ISPEC pp GABS_DEF) vstr in
        INSTANTIATE instn (TRANS th5 th4)
    | _ -> GEN_BETA_CONV tm;;

(* the copied code relies on HOL Light's type invention *)
let cake_tie_saved = !type_invention_error;;
type_invention_error := false;;

let cake_instantiate_casewise_recursion,
    cake_pure_prove_recursive_function_exists,
    cake_prove_general_recursive_function_exists,
    cake_guess_wf_hyp =

(* ------------------------------------------------------------------------- *)
(* Make some basic simplification of conjunction of welldefinedness clauses. *)
(* ------------------------------------------------------------------------- *)

  let SIMPLIFY_WELLDEFINEDNESS_CONV =
    let LSYM =
      GEN_ALL o CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) o SPEC_ALL
    and evensimps = prove
     (`((2 * m + 2 = 2 * n + 1) <=> F) /\
       ((2 * m + 1 = 2 * n + 2) <=> F) /\
       ((2 * m = 2 * n + 1) <=> F) /\
       ((2 * m + 1 = 2 * n) <=> F) /\
       ((2 * m = SUC(2 * n)) <=> F) /\
       ((SUC(2 * m) = 2 * n) <=> F)`,
      REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
      REWRITE_TAC[EVEN_MULT; EVEN_ADD; ARITH; EVEN]) in
    let allsimps = itlist (mk_rewrites false)
     [EQ_ADD_RCANCEL; EQ_ADD_LCANCEL;
      EQ_ADD_RCANCEL_0; EQ_ADD_LCANCEL_0;
      LSYM EQ_ADD_RCANCEL_0; LSYM EQ_ADD_LCANCEL_0;
      EQ_MULT_RCANCEL; EQ_MULT_LCANCEL;
      EQT_INTRO(SPEC_ALL EQ_REFL);
      ADD_EQ_0; LSYM ADD_EQ_0;
      MULT_EQ_0; LSYM MULT_EQ_0;
      MULT_EQ_1; LSYM MULT_EQ_1;
      ARITH_RULE `(m + n = 1) <=> (m = 1) /\ (n = 0) \/ (m = 0) /\ (n = 1)`;
      ARITH_RULE `(1 = m + n) <=> (m = 1) /\ (n = 0) \/ (m = 0) /\ (n = 1)`;
      evensimps; ARITH_EQ] []
    and [simp1; simp2; simp3] = map MATCH_MP (CONJUNCTS
      (TAUT
       `((a <=> F) /\ (b <=> b) ==> ((a ==> b) <=> T)) /\
        ((a <=> a') /\ (a' ==> (b <=> T)) ==> ((a ==> b) <=> T)) /\
        ((a <=> a') /\ (a' ==> (b <=> b')) ==> ((a ==> b) <=> (a' ==> b')))`))
    and false_tm = `F` and and_tm = `(/\)`
    and eq_refl = EQT_INTRO(SPEC_ALL EQ_REFL) in
    fun tm ->
      let net = itlist (net_of_thm false) allsimps (!basic_rectype_net) in
      let RECTYPE_ARITH_EQ_CONV =
        TOP_SWEEP_CONV(REWRITES_CONV net) THENC
        GEN_REWRITE_CONV DEPTH_CONV [AND_CLAUSES; OR_CLAUSES] in
      let SIMPLIFY_CASE_DISTINCTNESS_CLAUSE tm =
        let avs,bod = strip_forall tm in
        let ant,cons = dest_imp bod in
        let ath = RECTYPE_ARITH_EQ_CONV ant in
        let atm = rand(concl ath) in
        let bth = CONJ ath
          (if atm = false_tm then REFL cons
                    else DISCH atm
                          (PURE_REWRITE_CONV[eq_refl; ASSUME atm] cons)) in
        let cth = try simp1 bth with Failure _ -> try simp2 bth
                  with Failure _ -> simp3 bth in
        itlist MK_FORALL avs cth in
      (DEPTH_BINOP_CONV and_tm SIMPLIFY_CASE_DISTINCTNESS_CLAUSE THENC
       GEN_REWRITE_CONV DEPTH_CONV [FORALL_SIMP; AND_CLAUSES]) tm in

(* ------------------------------------------------------------------------- *)
(* Simplify an existential question about a pattern.                         *)
(* ------------------------------------------------------------------------- *)

  let EXISTS_PAT_CONV =
    let pth = prove
     (`((?y. _UNGUARDED_PATTERN (GEQ s t) (GEQ z y)) <=> s = t) /\
       ((?y. _GUARDED_PATTERN (GEQ s t) g (GEQ z y)) <=> g /\ s = t)`,
      REWRITE_TAC[_UNGUARDED_PATTERN; _GUARDED_PATTERN; GEQ_DEF] THEN
      MESON_TAC[]) in
    let basecnv = GEN_REWRITE_CONV I [pth]
    and pushcnv = GEN_REWRITE_CONV I [SWAP_EXISTS_THM] in
    let rec EXISTS_PAT_CONV tm =
     ((pushcnv THENC BINDER_CONV EXISTS_PAT_CONV) ORELSEC
      basecnv) tm in
    fun tm -> if is_exists tm then EXISTS_PAT_CONV tm
              else failwith "EXISTS_PAT_CONV" in

(* ------------------------------------------------------------------------- *)
(* Hack a proforma to introduce new pairing or pattern variables.            *)
(* ------------------------------------------------------------------------- *)

  let p_ty = `:P` and q_ty = `:Q` in
  let HACK_PROFORMA,EACK_PROFORMA =
    let elemma0 = prove
     (`((!z. GEQ (f z) (g z)) <=> (!x y. GEQ (f(x,y)) (g(x,y)))) /\
       ((\p. P p) = (\(x,y). P(x,y)))`,
      REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM])
    and elemma1 = prove
     (`(!P. (!t:A->B->C#D->E. P t) <=> (!t. P (\a b (c,d). t a b d c))) /\
       (!P. (!t:B->C#D->E. P t) <=> (!t. P (\b (c,d). t b d c))) /\
       (!P. (!t:C#D->E. P t) <=> (!t. P (\(c,d). t d c)))`,
      REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `\a b d c. (t:A->B->C#D->E) a b (c,d)`);
        FIRST_X_ASSUM(MP_TAC o SPEC `\b d c. (t:B->C#D->E) b (c,d)`);
        FIRST_X_ASSUM(MP_TAC o SPEC `\d c. (t:C#D->E) (c,d)`)] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]) in
    (* HOL Light's version instantiates P with the n-tuple type at once and  *)
    (* rewrites to a fixpoint: about cubic in n (minutes per definition for  *)
    (* the clause sets of closSem, bviSem, evaluate).  Here the version for  *)
    (* m+1 variables is made from the one for m by splitting only the last   *)
    (* component (_Pm, or P when m = 1, becomes _Pm # _P(m+1)), which gives  *)
    (* the same theorem; and every version is cached per rule.              *)
    let HACK_PROFORMA =
      let mkname i = "_P"^string_of_int i in
      let conv i =
        let name = "x"^string_of_int i in
        let cnv = ALPHA_CONV (mk_var(name,mk_vartype(mkname i))) in
        fun tm -> if is_abs tm && name_of(bndvar tm) <> name
                  then cnv tm else failwith "conv" in
      let step m hm =
        let old = if m = 1 then p_ty else mk_vartype(mkname m) in
        let nw = mk_type("prod",[mk_vartype(mkname m);
                                 mk_vartype(mkname (m+1))]) in
        let th1 = INST_TYPE [nw,old] hm in
        let th2 = REWRITE_RULE[FORALL_PAIR_THM] th1 in
        let th3 = REWRITE_RULE[elemma0; elemma1] th2 in
        CONV_RULE(REDEPTH_CONV (FIRST_CONV [conv m; conv (m+1)])) th3 in
      let cache = Hashtbl.create 64 in
      fun n th ->
        if n <= 1 then th else
        let key = (hyp th,concl th) in
        let known = try Hashtbl.find cache key with Not_found -> [] in
        try assoc n known with Failure _ ->
        let m,hm = itlist (fun (k,h) (k0,h0) ->
                             if k < n && k > k0 then (k,h) else (k0,h0))
                          known (1,th) in
        let rec go k hk acc =
          if k = n then hk,acc else
          let hk' = step k hk in go (k+1) hk' ((k+1,hk')::acc) in
        let res,acc = go m hm [] in
        Hashtbl.replace cache key (acc @ known);
        res
    and EACK_PROFORMA n th =
      if n <= 1 then th else
      let mkname i = "_Q"^string_of_int i in
      let ty = end_itlist (fun s t -> mk_type("prod",[s;t]))
                          (map (mk_vartype o mkname) (1--n)) in
      let conv i =
        let name = "t"^string_of_int i in
        let cnv = ALPHA_CONV (mk_var(name,mk_vartype(mkname i))) in
        fun tm -> if is_abs tm && name_of(bndvar tm) <> name
                  then cnv tm else failwith "conv" in
      let convs = FIRST_CONV (map conv (1--n)) in
      let th1 = INST_TYPE [ty,q_ty] th in
      let th2 = REWRITE_RULE[EXISTS_PAIR_THM] th1 in
      let th3 = REWRITE_RULE[elemma1] th2 in
      let th4 = REWRITE_RULE[FORALL_PAIR_THM] th3 in
      CONV_RULE(REDEPTH_CONV convs) th4 in
    HACK_PROFORMA,EACK_PROFORMA in

(* ------------------------------------------------------------------------- *)
(* Hack and apply.                                                           *)
(* ------------------------------------------------------------------------- *)

  let APPLY_PROFORMA_TAC th (asl,w as gl) =
    let vs = fst(dest_gabs(body(rand w))) in
    let n = 1 + length(fst(splitlist dest_pair vs)) in
    (MATCH_MP_TAC(HACK_PROFORMA n th) THEN BETA_TAC) gl in

  (* the rule of a case constant has its arm variables renamed to the names *)
  (* of the goal's arms, so each use was a new theorem for HACK_PROFORMA's   *)
  (* cache, which then rebuilt it for n variables from scratch (most of the  *)
  (* admissibility analysis of a definition over a big datatype): the rule  *)
  (* is hacked unrenamed (cached) and its arm variables, whose names y<i>_<j> *)
  (* and types no step of the hack touches, renamed afterwards               *)
  let CASE_PROFORMA_TAC hop args (asl,w as gl) =
    let vs = fst(dest_gabs(body(rand w))) in
    let n = 1 + length(fst(splitlist dest_pair vs)) in
    let old () = HACK_PROFORMA n (!cake_case_rule_ref hop args) in
    let th = try let base,ren = !cake_case_rule_parts_ref hop args in
                 ren (HACK_PROFORMA n base)
             with Failure _ -> old () in
    let th = if not !cake_check_case_hack then th else
             let th' = old () in
             if concl th' = concl th && hyp th' = hyp th then th else
             (Format.print_string ("CASE_PROFORMA_TAC: differs for "^
                                   fst(dest_const hop)^"\n");
              th') in
    (MATCH_MP_TAC th THEN BETA_TAC) gl in

  (* the same for the rules of pair_CASE and LET, whose pattern variables  *)
  (* cake_rename_proforma renames to the names of the goal's binders       *)
  let RENAMED_PROFORMA_TAC olds news th0 (asl,w as gl) =
    let vs = fst(dest_gabs(body(rand w))) in
    let n = 1 + length(fst(splitlist dest_pair vs)) in
    let old () = HACK_PROFORMA n (!cake_rename_proforma olds news th0) in
    let th = try let base,ren = !cake_proforma_parts_ref olds news th0 in
                 ren (HACK_PROFORMA n base)
             with Failure _ -> old () in
    let th = if not !cake_check_case_hack then th else
             let th' = old () in
             if concl th' = concl th && hyp th' = hyp th then th else
             (Format.print_string "RENAMED_PROFORMA_TAC: differs\n"; th') in
    (MATCH_MP_TAC th THEN BETA_TAC) gl in

  let is_pattern p n tm =
    try let f,args = strip_comb(snd(strip_exists (body(body tm)))) in
        is_const f && name_of f = p && length args = n
    with Failure _ -> false in

  let SIMPLIFY_MATCH_WELLDEFINED_TAC =
    let pth0 = MESON[]
     `(a /\ x = k ==> x = y ==> d) ==> (a /\ x = k /\ y = k ==> d)`
    and pth1 = MESON[]
     `(a /\ b /\ c /\ x = k ==> x = y ==> d)
      ==> (a /\ x = k /\ b /\ y = k /\ c ==> d)` in
    REPEAT GEN_TAC THEN
    (MATCH_MP_TAC pth1 ORELSE MATCH_MP_TAC pth0) THEN
    CONV_TAC(RAND_CONV SIMPLIFY_WELLDEFINEDNESS_CONV) THEN
    PURE_REWRITE_TAC
      [AND_CLAUSES; IMP_CLAUSES; OR_CLAUSES; EQ_CLAUSES; NOT_CLAUSES] in

  let rec headonly f tm =
    match tm with
      Comb(s,t) -> headonly f s && headonly f t && not(t = f)
    | Abs(x,t) -> headonly f t
    | _ -> true in

  let MAIN_ADMISS_TAC (asl,w as gl) =
    let had,args = strip_comb w in
    if not(is_const had) then failwith "ADMISS_TAC" else
    let f,fbod = dest_abs(last args) in
    let xtup,bod = dest_gabs fbod in
    let hop,args = strip_comb bod in
    match (name_of had,name_of hop) with
      "superadmissible","COND"
          -> APPLY_PROFORMA_TAC SUPERADMISSIBLE_COND gl
    | "superadmissible","_MATCH" when
          name_of(repeat rator (last args)) = "_SEQPATTERN"
          -> (APPLY_PROFORMA_TAC SUPERADMISSIBLE_MATCH_SEQPATTERN THEN
              CONV_TAC(ONCE_DEPTH_CONV EXISTS_PAT_CONV)) gl
    | "superadmissible","_MATCH" when
         is_pattern "_UNGUARDED_PATTERN" 2 (last args)
          -> let n = length(fst(strip_exists(body(body(last args))))) in
             let th = EACK_PROFORMA n SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN in
             (APPLY_PROFORMA_TAC th THEN CONJ_TAC THENL
               [SIMPLIFY_MATCH_WELLDEFINED_TAC; ALL_TAC]) gl
    | "superadmissible","_MATCH" when
         is_pattern "_GUARDED_PATTERN" 3 (last args)
          -> let n = length(fst(strip_exists(body(body(last args))))) in
             let th = EACK_PROFORMA n SUPERADMISSIBLE_MATCH_GUARDED_PATTERN in
             (APPLY_PROFORMA_TAC th THEN CONJ_TAC THENL
               [SIMPLIFY_MATCH_WELLDEFINED_TAC; ALL_TAC]) gl
    | "superadmissible",_ when is_comb bod && rator bod = f
          -> APPLY_PROFORMA_TAC SUPERADMISSIBLE_TAIL gl
    | "admissible","sum"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_SUM gl
    | "admissible","nsum"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_NSUM gl
    | "admissible","MAP"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_MAP gl
    | "admissible","_MATCH" when
          name_of(repeat rator (last args)) = "_SEQPATTERN"
          -> (APPLY_PROFORMA_TAC ADMISSIBLE_MATCH_SEQPATTERN THEN
              CONV_TAC(ONCE_DEPTH_CONV EXISTS_PAT_CONV)) gl
    | "admissible","_MATCH"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_MATCH gl
    | "admissible","_UNGUARDED_PATTERN"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_UNGUARDED_PATTERN gl
    | "admissible","_GUARDED_PATTERN"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_GUARDED_PATTERN gl
    | "admissible","COND"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_COND gl
    | "admissible",_ when is_case_const hop &&
                          length args = 1 + length (case_info_of_const hop).ci_pats &&
                          not (can (assoc (name_of hop)) (!cake_admissible_rules))
          -> CASE_PROFORMA_TAC hop (tl args) gl
    | "admissible","LET" when can (assoc "LET") (!cake_admissible_rules)
          -> let th = assoc "LET" (!cake_admissible_rules) in
             let names = try let v1,_ = dest_abs (hd(snd(strip_comb bod))) in
                             [fst(dest_var v1)]
                         with Failure _ -> [] in
             RENAMED_PROFORMA_TAC ["y"] names th gl
    | "admissible","pair_CASE" when can (assoc "pair_CASE") (!cake_admissible_rules)
          -> let th = assoc "pair_CASE" (!cake_admissible_rules) in
             let names = try let v1,b1 = dest_abs (last(snd(strip_comb bod))) in
                             let v2,_ = dest_abs b1 in
                             [fst(dest_var v1); fst(dest_var v2)]
                         with Failure _ -> [] in
             RENAMED_PROFORMA_TAC ["a";"b"] names th gl
    | "admissible",c when can (assoc c) (!cake_admissible_rules)
          -> APPLY_PROFORMA_TAC (assoc c (!cake_admissible_rules)) gl
    | "admissible",_ when is_abs bod
          -> APPLY_PROFORMA_TAC CAKE_ADMISSIBLE_LAMBDA gl
    | "admissible",_ when is_comb bod && rator bod = f
          -> if free_in f (rand bod) then
               APPLY_PROFORMA_TAC ADMISSIBLE_NEST gl
             else
               APPLY_PROFORMA_TAC ADMISSIBLE_BASE gl
    | "admissible",_ when is_comb bod && headonly f bod
          -> APPLY_PROFORMA_TAC ADMISSIBLE_COMB gl
    | _ -> failwith "MAIN_ADMISS_TAC" in

  (* a binder in the body named like a variable of the tuple of all clause  *)
  (* variables (\f (x,ty,..). ?x. .. f (s,tm) ..): the shadowing defeats the *)
  (* matching of the rules (CAKE_ADMISSIBLE_LAMBDA), and the condition was   *)
  (* left as a termination condition that cannot be proved; such binders    *)
  (* are renamed apart (HOL4's TFL handles these calls).  Only where no     *)
  (* other step applies, so other definitions are as before.  Since          *)
  (* 2026-11-22.                                                             *)
  let UNCLASH_TAC (asl,w as gl) =
    let had,args = strip_comb w in
    if not(is_const had) then failwith "UNCLASH_TAC" else
    let f,fbod = dest_abs(last args) in
    let xtup,bod = dest_gabs fbod in
    let tvs = f :: frees xtup in
    let avoid = ref (tvs @ variables bod) in
    let rec ren t =
      match t with
        Abs(v,b) -> let b' = ren b in
                    if mem v tvs then
                      let v' = variant !avoid v in
                      avoid := v' :: !avoid; mk_abs(v',vsubst [v',v] b')
                    else mk_abs(v,b')
      | Comb(a,b) -> mk_comb(ren a,ren b)
      | _ -> t in
    let bod' = ren bod in
    if bod' = bod then failwith "UNCLASH_TAC" else
    let w' = list_mk_comb(had,butlast args @ [mk_abs(f,mk_gabs(xtup,bod'))]) in
    kit_note "recursion: binders renamed apart from the clause variables";
    CONV_TAC (fun tm -> ALPHA tm w') gl in

  let ADMISS_TAC =
    CONJ_TAC ORELSE
    MATCH_ACCEPT_TAC ADMISSIBLE_CONST ORELSE
    MATCH_ACCEPT_TAC SUPERADMISSIBLE_CONST ORELSE
    MAIN_ADMISS_TAC ORELSE
    MATCH_MP_TAC ADMISSIBLE_IMP_SUPERADMISSIBLE ORELSE
    (UNCLASH_TAC THEN MAIN_ADMISS_TAC) in

(* ------------------------------------------------------------------------- *)
(* Instantiate the casewise recursion theorem for existential claim.         *)
(* Also make a first attempt to simplify the distinctness clause. This may   *)
(* yield a theorem with just the wellfoundedness "?(<<)" assumption, or it   *)
(* may be that and an additional distinctness one.                           *)
(* ------------------------------------------------------------------------- *)

  let instantiate_casewise_recursion =
    let EXPAND_PAIRED_ALL_CONV =
      let pth0,pth1 = (CONJ_PAIR o prove)
       (`(ALL (\(s,t). P s t) [a,b] <=> P a b) /\
         (ALL (\(s,t). P s t) (CONS (a,b) l) <=>
          P a b /\ ALL (\(s,t). P s t) l)`,
        REWRITE_TAC[ALL]) in
      let conv0 = REWR_CONV pth0 and conv1 = REWR_CONV pth1 in
      let rec conv tm =
        try conv0 tm with Failure _ ->
        let th = conv1 tm in CONV_RULE (funpow 2 RAND_CONV conv) th in
      conv
    and LAMBDA_PAIR_CONV =
      let rewr1 =  GEN_REWRITE_RULE I [GSYM FORALL_PAIR_THM]
      and rewr2 = GEN_REWRITE_CONV I [FUN_EQ_THM] in
      fun parms tm ->
        let parm = end_itlist (curry mk_pair) parms in
        let x,bod = dest_abs tm in
        let tm' = mk_gabs(parm,vsubst[parm,x] bod) in
        let th1 = BETA_CONV(mk_comb(tm,parm))
        and th2 = CAKE_GEN_BETA_CONV (mk_comb(tm',parm)) in
        let th3 = TRANS th1 (SYM th2) in
        let th4 = itlist (fun v th -> rewr1 (GEN v th))
                         (butlast parms) (GEN (last parms) th3) in
        EQ_MP (SYM(rewr2(mk_eq(tm,tm')))) th4
    and FORALL_PAIR_CONV =
      let rule = GEN_REWRITE_RULE RAND_CONV [GSYM FORALL_PAIR_THM] in
      let rec depair l t =
        match l with
          [v] -> REFL t
        | v::vs -> rule(BINDER_CONV (depair vs) t) in
      fun parm parms ->
        let p = mk_var("P",mk_fun_ty (type_of parm) bool_ty) in
        let tm = list_mk_forall(parms,mk_comb(p,parm)) in
        GEN p (SYM(depair parms tm)) in
    let ELIM_LISTOPS_CONV =
      PURE_REWRITE_CONV[PAIRWISE; ALL; GSYM CONJ_ASSOC; AND_CLAUSES] THENC
      TOP_DEPTH_CONV CAKE_GEN_BETA_CONV in
    let tuple_function_existence tm =
      let f,def = dest_exists tm in
      let domtys0,ranty0 = splitlist dest_fun_ty (type_of f) in
      let nargs =
        itlist
         (max o length o snd o strip_comb o lhs o snd o strip_forall)
         (conjuncts(snd(strip_forall def))) 0 in
      let domtys,midtys = chop_list nargs domtys0 in
      let ranty = itlist mk_fun_ty midtys ranty0 in
      if length domtys <= 1 then ASSUME tm else
      let dty = end_itlist (fun ty1 ty2 -> mk_type("prod",[ty1;ty2])) domtys in
      let f' = variant (frees tm)
                       (mk_var(fst(dest_var f),mk_fun_ty dty ranty)) in
      let gvs = map genvar domtys in
      let f'' = list_mk_abs(gvs,mk_comb(f',end_itlist (curry mk_pair) gvs)) in
      let def' = subst [f'',f] def in
      let th1 = EXISTS (tm,f'') (ASSUME def')
      and bth = BETAS_CONV (list_mk_comb(f'',gvs)) in
      let th2 = GEN_REWRITE_CONV TOP_DEPTH_CONV [bth] (hd(hyp th1)) in
      SIMPLE_CHOOSE f' (PROVE_HYP (UNDISCH(snd(EQ_IMP_RULE th2))) th1) in
    let pinstantiate_casewise_recursion def =
      try PART_MATCH I EXISTS_REFL def with Failure _ ->
      let f,bod = dest_exists def in
      let cjs = conjuncts bod in
      let eqs = map (snd o strip_forall) cjs in
      let lefts,rights = unzip(map dest_eq eqs) in
      let arglists = map (snd o strip_comb) lefts in
      let parms0 = freesl(unions arglists) in
      let parms = if parms0 <> [] then parms0 else [genvar aty] in
      let parm = end_itlist (curry mk_pair) parms in
      let ss = map (fun a -> mk_gabs(parm,end_itlist (curry mk_pair) a))
                   arglists
      and ts = map (fun a -> mk_abs(f,mk_gabs(parm,a))) rights in
      let clauses = mk_flist(map2 (curry mk_pair) ss ts) in
      let pth = ISPEC clauses RECURSION_SUPERADMISSIBLE in
      let FIDDLE_CONV =
        (LAND_CONV o LAND_CONV o BINDER_CONV o RAND_CONV o LAND_CONV o
         GABS_CONV o RATOR_CONV o LAND_CONV o ABS_CONV) in
      let th0 = UNDISCH(CONV_RULE(FIDDLE_CONV(LAMBDA_PAIR_CONV parms)) pth) in
      let th1 = EQ_MP (GEN_ALPHA_CONV f (concl th0)) th0 in
      let rewr_forall_th = REWR_CONV(FORALL_PAIR_CONV parm parms) in
      (* the inner quantifier y of each well-definedness condition !f x y. ..  *)
      (* is split into variables named apart from parms: with the names of    *)
      (* parms, splitting x renames every one of them, and the kernel's vsubst *)
      (* takes time exponential in the number of nested binders it renames    *)
      (* (minutes for 20 variables).  The conditions are only alpha-converted  *)
      let rewr_forall_th' =
        let avoid = ref parms in
        let parms' = map (fun v -> let v' = variant (!avoid) v in
                                   avoid := v' :: !avoid; v') parms in
        REWR_CONV(FORALL_PAIR_CONV (end_itlist (curry mk_pair) parms') parms') in
      let th2 = CONV_RULE (BINDER_CONV
                    (LAND_CONV(GABS_CONV rewr_forall_th) THENC
                     EXPAND_PAIRED_ALL_CONV)) th1 in
      let f2,bod2 = dest_exists(concl th2) in
      let ths3 = map
       (CONV_RULE (COMB2_CONV (funpow 2 RAND_CONV CAKE_GEN_BETA_CONV)
                  (RATOR_CONV BETA_CONV THENC CAKE_GEN_BETA_CONV)) o CAKE_SPEC_ALL)
       (CONJUNCTS(ASSUME bod2)) in
      let ths4 = map2
       (fun th t -> let avs,tbod = strip_forall t in
                    itlist GEN avs (PART_MATCH I th tbod)) ths3 cjs in
      let th5 = SIMPLE_EXISTS f (end_itlist CONJ ths4) in
      let th6 = PROVE_HYP th2 (SIMPLE_CHOOSE f th5) in
      let th7 =
       (RAND_CONV(COMB2_CONV
            (RAND_CONV (LAND_CONV (GABS_CONV(BINDER_CONV
                     (BINDER_CONV(rewr_forall_th') THENC rewr_forall_th)))))
            (LAND_CONV (funpow 2 GABS_CONV(BINDER_CONV
                     (BINDER_CONV(rewr_forall_th') THENC
                      rewr_forall_th))))) THENC
        ELIM_LISTOPS_CONV) (hd(hyp th6)) in
      let th8 = PROVE_HYP (UNDISCH(snd(EQ_IMP_RULE th7))) th6 in
      let wfasm,cdasm = dest_conj(hd(hyp th8)) in
      let th9 = PROVE_HYP (CONJ (ASSUME wfasm) (ASSUME cdasm)) th8 in
      let th10 = SIMPLIFY_WELLDEFINEDNESS_CONV cdasm in
      let th11 = PROVE_HYP (UNDISCH(snd(EQ_IMP_RULE th10))) th9 in
      PROVE_HYP TRUTH th11 in
    fun etm ->
      let eth = tuple_function_existence etm in
      let dtm = hd(hyp eth) in
      let dth = pinstantiate_casewise_recursion dtm in
      PROVE_HYP dth eth in

(* ------------------------------------------------------------------------- *)
(* Justify existence assertion and try to simplify/remove side-conditions.   *)
(* ------------------------------------------------------------------------- *)

  let pure_prove_recursive_function_exists =
    let break_down_admissibility th1 =
      if hyp th1 = [] then th1 else
      let def = concl th1 in
      let f,bod = dest_exists def in
      let cjs = conjuncts bod in
      let eqs = map (snd o strip_forall) cjs in
      let lefts,rights = unzip(map dest_eq eqs) in
      let arglists = map (snd o strip_comb) lefts in
      let parms0 = freesl(unions arglists) in
      let parms = if parms0 <> [] then parms0 else [genvar aty] in
      let wfasm = find is_exists (hyp th1) in
      let ord,bod = dest_exists wfasm in
      let SIMP_ADMISS_TAC =
        (* with cake_let_cong set, LET stays (rule ADMISSIBLE_LET, HOL4's    *)
        (* LET_CONG: a call in the bound expression is analysed once); by    *)
        (* default lets are unfolded, as HOL Light does                      *)
        (fun g -> REWRITE_TAC(if !cake_let_cong then [LET_END_DEF]
                              else [LET_DEF; LET_END_DEF]) g) THEN
        REPEAT ADMISS_TAC THEN
        TRY(W(fun (asl,w) -> let v = fst(dest_forall w) in
                X_GEN_TAC v THEN
                MAP_EVERY
                  (fun v -> TRY(GEN_REWRITE_TAC I [FORALL_PAIR_THM]) THEN
                            X_GEN_TAC v)
                  parms THEN
                CONV_TAC(TOP_DEPTH_CONV CAKE_GEN_BETA_CONV) THEN
                MAP_EVERY (fun v -> SPEC_TAC(v,v)) (rev parms @ [v]))) THEN
        PURE_REWRITE_TAC[FORALL_SIMP] THEN
        W(fun (asl,w) -> MAP_EVERY (fun t -> SPEC_TAC(t,t))
                                   (subtract (frees w) [ord])) THEN
        W(fun (asl,w) -> ACCEPT_TAC(ASSUME w)) in
      let th2 = TAC_PROOF(([],bod),SIMP_ADMISS_TAC) in
      let th3 = SIMPLE_EXISTS ord th2 in
      let allasms = hyp th3 and wfasm = lhand(concl th2) in
      let th4 = ASSUME(list_mk_conj(wfasm::subtract allasms [wfasm])) in
      let th5 = SIMPLE_CHOOSE ord (itlist PROVE_HYP (CONJUNCTS th4) th3) in
      PROVE_HYP th5 th1 in
    (* the last result is kept: cake_def asks for the same claim again after *)
    (* the automatic termination proof (for the induction theorem) and for   *)
    (* each size measure it tries; the key includes the tables the analysis *)
    (* reads                                                                  *)
    let cache = ref [] in
    fun dtm ->
      let l0 = !cake_let_cong and a0 = !cake_admissible_rules
      and c0 = !the_case_infos and n0 = !basic_rectype_net
      and r0 = !cake_rename_proforma and q0 = !cake_case_rule_ref
      and u0 = !cake_case_rule_parts_ref and v0 = !cake_proforma_parts_ref in
      let hit (d,l,a,c,n,r,q,u,v,_) =
        l = l0 && a == a0 && c == c0 && n == n0 && r == r0 && q == q0 &&
        u == u0 && v == v0 && d = dtm in
      try let (_,_,_,_,_,_,_,_,_,th) = find hit (!cache) in th with Failure _ ->
      let th =  break_down_admissibility(instantiate_casewise_recursion dtm) in
      if concl th = dtm then (cache := [dtm,l0,a0,c0,n0,r0,q0,u0,v0,th]; th)
      else failwith "prove_general_recursive_function_exists: sanity" in

(* ------------------------------------------------------------------------- *)
(* Same, but attempt to prove the wellfoundedness hyp by good guesses.       *)
(* ------------------------------------------------------------------------- *)

  let prove_general_recursive_function_exists =
    let plus_tm = `(+):num->num->num` and succ_tm = `\n:num. n + 1` in
    let prove_depth_measure_exists =
      let num_ty = `:num` in
      fun tyname ->
        let _,_,sth = assoc tyname (!inductive_type_store) in
        let ty,zty = dest_fun_ty
         (type_of(fst(dest_exists(snd(strip_forall(concl sth)))))) in
        let rth = INST_TYPE [num_ty,zty] sth in
        let avs,bod = strip_forall(concl rth) in
        let ev,cbod = dest_exists bod in
        let process_clause k t =
          let avs,eq = strip_forall t in
          let l,r = dest_eq eq in
          let fn,cargs = dest_comb l in
          let con,args = strip_comb cargs in
          let bargs = filter (fun t -> type_of t = ty) args in
          let r' = list_mk_binop plus_tm
                    (mk_small_numeral k :: map (curry mk_comb fn) bargs) in
          list_mk_forall(avs,mk_eq(l,r')) in
        let cjs = conjuncts cbod in
        let def = map2 process_clause (1--length cjs) cjs in
        prove_recursive_functions_exist sth (list_mk_conj def) in
    let INDUCTIVE_MEASURE_THEN tac (asl,w) =
      let ev,bod = dest_exists w in
      let ty = fst(dest_type(fst(dest_fun_ty(type_of ev)))) in
      let th = prove_depth_measure_exists ty in
      let ev',bod' = dest_exists(concl th) in
      let th' = INST_TYPE(type_match (type_of ev') (type_of ev) []) th in
      (MP_TAC th' THEN MATCH_MP_TAC MONO_EXISTS THEN
       GEN_TAC THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN tac) (asl,w) in
    let CONSTANT_MEASURE_THEN =
      let one_tm = `1` in
      fun tac (asl,w) ->
        let ev,bod = dest_exists w in
        let ty = fst(dest_fun_ty(type_of ev)) in
        (EXISTS_TAC(mk_abs(genvar ty,one_tm)) THEN tac) (asl,w) in
    let GUESS_MEASURE_THEN tac =
      (EXISTS_TAC succ_tm THEN tac) ORELSE
      (INDUCTIVE_MEASURE_THEN tac) ORELSE
      CONSTANT_MEASURE_THEN tac in
    let pth_lexleft = prove
     (`(?r. WF(r) /\
            ?s. WF(s) /\
                P(\(x1,y1) (x2,y2). r x1 x2 \/ (x1 = x2) /\ s y1 y2))
       ==> ?t:A#B->A#B->bool. WF(t) /\ P t`,
      REPEAT STRIP_TAC THEN EXISTS_TAC
       `\(x1:A,y1:B) (x2:A,y2:B). r x1 x2 \/ (x1 = x2) /\ s y1 y2` THEN
      ASM_SIMP_TAC[WF_LEX]) in
    let pth_lexright = prove
     (`(?r. WF(r) /\
            ?s. WF(s) /\
                P(\(x1,y1) (x2,y2). r y1 y2 \/ (y1 = y2) /\ s x1 x2))
       ==> ?t:A#B->A#B->bool. WF(t) /\ P t`,
      REPEAT STRIP_TAC THEN
      EXISTS_TAC `\u:A#B v:A#B.
                    (\(x1:B,y1:A) (x2:B,y2:A). r x1 x2 \/ (x1 = x2) /\ s y1 y2)
                     ((\(a,b). b,a) u) ((\(a,b). b,a) v)` THEN
      ASM_SIMP_TAC[WF_LEX; ETA_AX;
       ISPECL [`R:A#B->A#B->bool`; `\(b:B,a:A). a,b`] WF_MEASURE_GEN] THEN
      FIRST_X_ASSUM(fun th -> MP_TAC th THEN
                              MATCH_MP_TAC EQ_IMP THEN
                              AP_TERM_TAC) THEN
      REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]) in
    let pth_measure = prove
     (`(?m:A->num. P(MEASURE m)) ==> ?r:A->A->bool. WF(r) /\ P r`,
      MESON_TAC[WF_MEASURE]) in
    let rec GUESS_WF_THEN tac (asl,w) =
     ((MATCH_MP_TAC pth_lexleft THEN GUESS_WF_THEN (GUESS_WF_THEN tac)) ORELSE
      (MATCH_MP_TAC pth_lexright THEN GUESS_WF_THEN (GUESS_WF_THEN tac)) ORELSE
      (MATCH_MP_TAC pth_measure THEN
       REWRITE_TAC[MEASURE; MEASURE_LE] THEN
       REWRITE_TAC[FORALL_PAIR_THM] THEN
       GUESS_MEASURE_THEN tac)) (asl,w) in
    let PRE_GUESS_TAC =
      CONV_TAC(BINDER_CONV(DEPTH_BINOP_CONV `(/\)`
       (TRY_CONV SIMPLIFY_WELLDEFINEDNESS_CONV THENC
        TRY_CONV FORALL_UNWIND_CONV))) in
    let GUESS_ORDERING_TAC =
      let false_tm = `\x:A y:A. F` in
      W(fun (asl,w) ->
            let ty = fst(dest_fun_ty(type_of(fst(dest_exists w)))) in
            EXISTS_TAC(inst [ty,aty] false_tm) THEN
            REWRITE_TAC[WF_FALSE] THEN NO_TAC) ORELSE
      GUESS_WF_THEN
       (REWRITE_TAC[FORALL_PAIR_THM] THEN ARITH_TAC) in
    (* the automatic proof of the WF hypothesis of an existence theorem   *)
    (* (fails if the guess fails); cake_def uses it on its own as well      *)
    let guess_wf_hyp th =
      let wtm = find is_exists (hyp th) in
      let wth = prove(wtm,PRE_GUESS_TAC THEN GUESS_ORDERING_TAC) in
      PROVE_HYP wth th in
    (fun etm ->
       let th = pure_prove_recursive_function_exists etm in
       try guess_wf_hyp th with Failure _ -> th),
    guess_wf_hyp in

  instantiate_casewise_recursion,
  pure_prove_recursive_function_exists,
  fst prove_general_recursive_function_exists,
  snd prove_general_recursive_function_exists;;

type_invention_error := cake_tie_saved;;

(* ------------------------------------------------------------------------- *)
(* Admissibility rules with the contexts of HOL4's congruence rules         *)
(* (IMP_CONG, EVERY_CONG, EXISTS_CONG, IMAGE_CONG, FOLDR_CONG).              *)
(* ------------------------------------------------------------------------- *)

let ADMISSIBLE_IMP = prove
 (`!(<<) (p:(A->B)->P->bool) (s:P->A) P Q.
        admissible(<<) p s P /\
        admissible(<<) (\f x. p f x /\ P f x) s Q
        ==> admissible(<<) p s (\f x. P f x ==> Q f x)`,
  REWRITE_TAC[admissible] THEN MESON_TAC[]);;

let ADMISSIBLE_ALL = prove
 (`!(<<) (p:(A->B)->P->bool) (s:P->A) (h:(A->B)->P->C->bool) l.
        admissible(<<) p s l /\
        admissible (<<) (\f (y,x). p f x /\ MEM y (l f x))
                        (\(y,x). s x) (\f (y,x). h f x y)
        ==> admissible (<<) p s (\f x. ALL (h f x) (l f x))`,
  REWRITE_TAC[admissible; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[] `(x:C list) = y /\ (ALL f x <=> ALL g x) ==> (ALL f x <=> ALL g y)`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[]);;

let ADMISSIBLE_EX = prove
 (`!(<<) (p:(A->B)->P->bool) (s:P->A) (h:(A->B)->P->C->bool) l.
        admissible(<<) p s l /\
        admissible (<<) (\f (y,x). p f x /\ MEM y (l f x))
                        (\(y,x). s x) (\f (y,x). h f x y)
        ==> admissible (<<) p s (\f x. EX (h f x) (l f x))`,
  REWRITE_TAC[admissible; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[] `(x:C list) = y /\ (EX f x <=> EX g x) ==> (EX f x <=> EX g y)`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM EX_MEM] THEN ASM_MESON_TAC[]);;

let ADMISSIBLE_IMAGE = prove
 (`!(<<) (p:(A->B)->P->bool) (s:P->A) (h:(A->B)->P->C->D) l.
        admissible(<<) p s l /\
        admissible (<<) (\f (y,x). p f x /\ y IN l f x)
                        (\(y,x). s x) (\f (y,x). h f x y)
        ==> admissible (<<) p s (\f x. IMAGE (h f x) (l f x))`,
  REWRITE_TAC[admissible; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[] `(x:C->bool) = y /\ IMAGE (f:C->D) x = IMAGE g x ==> IMAGE f x = IMAGE g y`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]);;

let ADMISSIBLE_ITLIST = prove
 (`!(<<) (p:(A->B)->P->bool) (s:P->A) (h:(A->B)->P->C->D->D) l b.
        admissible(<<) p s l /\ admissible(<<) p s b /\
        admissible (<<) (\f (y,c,x). p f x /\ MEM y (l f x))
                        (\(y,c,x). s x) (\f (y,c,x). h f x y c)
        ==> admissible (<<) p s (\f x. ITLIST (h f x) (l f x) (b f x))`,
  REWRITE_TAC[admissible; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(l:(A->B)->P->C list) g a = l f a /\ (b:(A->B)->P->D) g a = b f a`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y c. MEM y ((l:(A->B)->P->C list) f a)
                      ==> (h:(A->B)->P->C->D->D) f a y c = h g a y c`
  MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`(l:(A->B)->P->C list) f a`,`ll:C list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; MEM] THEN ASM_MESON_TAC[]);;

(* pair_CASE e (\a b. t), the kit's let (a,b) = e in t: the context        *)
(* e = (a,b) (HOL4's LET_CONG with the pair); much cheaper for the recursion *)
(* package than the match it used to be turned into                         *)

let ADMISSIBLE_pair_CASE = prove
 (`!(<<) (p:(A->B)->P->bool) (s:P->A) (e:(A->B)->P->C#D) (h:(A->B)->P->C->D->E).
        admissible(<<) p s e /\
        admissible (<<) (\f (a,b,x). p f x /\ e f x = (a,b))
                        (\(a,b,x). s x) (\f (a,b,x). h f x a b)
        ==> admissible (<<) p s (\f x. pair_CASE (e f x) (h f x))`,
  REWRITE_TAC[admissible; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(e:(A->B)->P->C#D) g a = e f a` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `(e:(A->B)->P->C#D) f a` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:C` (X_CHOOSE_THEN `v:D` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN ASM_MESON_TAC[]);;

let rec cake_rename_bound (ren:(string*string) list) tm =
  match tm with
    Abs(v,b) -> let b' = cake_rename_bound ren b in
                let n,ty = dest_var v in
                (try let v' = mk_var(assoc n ren,ty) in mk_abs(v',vsubst [v',v] b')
                 with Failure _ -> mk_abs(v,b'))
  | Comb(f,x) -> mk_comb(cake_rename_bound ren f,cake_rename_bound ren x)
  | _ -> tm;;

cake_rename_proforma :=
  (fun olds news th ->
     if length news <> length olds then th else
     let used = ref (map (fst o dest_var) (variables (concl th))) in
     let fresh n = let rec go n = if mem n !used then go (n ^ "'") else n in
                   let n' = go n in used := n' :: !used; n' in
     let ren = map2 (fun od nw -> od, fresh nw) olds news in
     try let c' = cake_rename_bound ren (concl th) in
         EQ_MP (ALPHA (concl th) c') th
     with Failure _ -> th);;

(* the renaming of cake_rename_proforma split in two: the rule with the old   *)
(* names marked (made once per rule, so that HACK_PROFORMA's cache knows it) *)
(* and the renaming of the marked names to the new ones, chosen as before    *)

let cake_marked_rules = ref ([] : ((string list * term) * thm) list);;

let cake_proforma_parts olds news th =
  if length news <> length olds then failwith "cake_proforma_parts" else
  let used = ref (map (fst o dest_var) (variables (concl th))) in
  let fresh n = let rec go n = if mem n !used then go (n ^ "'") else n in
                let n' = go n in used := n' :: !used; n' in
  let ren = map2 (fun od nw -> od^"%arm", fresh nw) olds news in
  let key = (olds,concl th) in
  let base =
    try assoc key (!cake_marked_rules) with Failure _ ->
    let c' = cake_rename_bound (map (fun od -> od,od^"%arm") olds) (concl th) in
    let b = EQ_MP (ALPHA (concl th) c') th in
    cake_marked_rules := (key,b) :: !cake_marked_rules; b in
  base,(fun hth -> let c' = cake_rename_bound ren (concl hth) in
                   EQ_MP (ALPHA (concl hth) c') hth);;

cake_proforma_parts_ref := cake_proforma_parts;;

(* ------------------------------------------------------------------------- *)
(* Admissibility rules for case constants (HOL4's case congruence rules):     *)
(*   admissible R p s e /\                                                   *)
(*   (for each constructor Ci y1 .. ym)                                      *)
(*   admissible R (\f (y1,..,ym,x). p f x /\ e f x = Ci y1 .. ym)             *)
(*                (\(y1,..,ym,x). s x) (\f (y1,..,ym,x). hi f x y1 .. ym)     *)
(*   ==> admissible R p s (\f x. ty_CASE (e f x) (h1 f x) .. (hk f x))       *)
(* (for a constructor without arguments the context is e f x = Ci).  Made    *)
(* for each case constant when a recursive definition first needs it; a call *)
(* in an arm gets the context scrutinee = pattern, as with HOL4's TFL.       *)
(* ------------------------------------------------------------------------- *)

let cake_case_admissible_cache = ref ([] : (string * thm) list);;

let case_admissible_thm (ci:case_info) =
  let cname = fst(dest_const ci.ci_case) in
  try assoc cname (!cake_case_admissible_cache) with Failure _ ->
  let c = ci.ci_case in
  let tyc = type_of c in
  let tty = hd(snd(dest_type tyc)) in
  let n = length ci.ci_pats in
  let rty = funpow (n + 1) (fun t -> hd(tl(snd(dest_type t)))) tyc in
  let used = map dest_vartype (tyvars tyc) in
  let pick l = mk_vartype (find (fun s -> not (mem s used)) l) in
  let aty' = pick ["A";"A1";"A2";"A3";"A4"]
  and bty' = pick ["B";"B1";"B2";"B3";"B4"]
  and pty' = pick ["P";"P1";"P2";"P3";"P4"] in
  let fty = mk_fun_ty aty' bty' in
  let lt = mk_var("<<",mk_fun_ty aty' (mk_fun_ty aty' bool_ty)) in
  let p = mk_var("p",mk_fun_ty fty (mk_fun_ty pty' bool_ty)) in
  let s = mk_var("s",mk_fun_ty pty' aty') in
  let e = mk_var("e",mk_fun_ty fty (mk_fun_ty pty' tty)) in
  let f = mk_var("f",fty) and x = mk_var("x",pty') in
  let adm0 = mk_const("admissible",[]) in
  let mk_adm r pp ss t =
    let ty = itlist mk_fun_ty (map type_of [r;pp;ss;t]) bool_ty in
    list_mk_comb(inst (type_match (type_of adm0) ty []) adm0,[r;pp;ss;t]) in
  let arms = map2 (fun (vs,pat) i ->
      let ys = map2 (fun v j -> mk_var("y"^string_of_int i^"_"^string_of_int j,
                                       type_of v)) vs (1--length vs) in
      let pat' = vsubst (zip ys vs) pat in
      let h = mk_var("h"^string_of_int i,
                     mk_fun_ty fty (mk_fun_ty pty' (itlist mk_fun_ty (map type_of vs) rty))) in
      ys,pat',h) ci.ci_pats (1--n) in
  let pfx = mk_comb(mk_comb(p,f),x) and efx = mk_comb(mk_comb(e,f),x) in
  let ant (ys,pat',h) =
    if ys = [] then
      mk_adm lt (mk_abs(f,mk_abs(x,mk_conj(pfx,mk_eq(efx,pat'))))) s
                (mk_abs(f,mk_abs(x,list_mk_comb(h,[f;x]))))
    else
      let tup = end_itlist (curry mk_pair) (ys @ [x]) in
      mk_adm lt (mk_abs(f,mk_gabs(tup,mk_conj(pfx,mk_eq(efx,pat')))))
                (mk_gabs(tup,mk_comb(s,x)))
                (mk_abs(f,mk_gabs(tup,list_mk_comb(h,[f;x] @ ys)))) in
  let c' = inst (type_match tyc (itlist mk_fun_ty
                   (tty :: map (fun (ys,_,_) -> itlist mk_fun_ty (map type_of ys) rty) arms)
                   rty) []) c in
  let body = list_mk_comb(c',efx :: map (fun (_,_,h) -> list_mk_comb(h,[f;x])) arms) in
  let concl_ = mk_adm lt p s (mk_abs(f,mk_abs(x,body))) in
  let tm = list_mk_forall(lt :: p :: s :: e :: map (fun (_,_,h) -> h) arms,
             mk_imp(list_mk_conj(mk_adm lt p s e :: map ant arms),concl_)) in
  let nch = ci.ci_nchotomy and cdef = ci.ci_def in
  (* the arm antecedents are used by instantiating their tuple variable    *)
  (* with (y1,..,ym,a) and reducing the paired lambdas: FORALL_PAIR_THM     *)
  (* would also split a constructor argument of product type               *)
  let arm_tac (asl,w as gl) =
    let hl,hr = dest_eq w in
    let _,largs = strip_comb hl and _,rargs = strip_comb hr in
    let f0 = hd largs and g0 = hd rargs and a0 = hd(tl largs) in
    let ys = tl(tl largs) in
    let tup = if ys = [] then a0 else end_itlist (curry mk_pair) (ys @ [a0]) in
    let red = CONV_RULE (TOP_DEPTH_CONV GEN_BETA_CONV) in
    (FIRST_ASSUM(fun th -> MATCH_MP_TAC (red (SPECL [f0;g0;tup] th))) THEN
     ASM_REWRITE_TAC[]) gl in
  let tac (asl,w as gl) =
    let l,r = dest_eq w in
    let sl = hd(snd(strip_comb l)) and sr = hd(snd(strip_comb r)) in
    (* e f a = e g a from the first antecedent, without MESON (a type with *)
    (* tens of constructors gives as many assumptions: MESON goes too deep) *)
    (SUBGOAL_THEN (mk_eq(sl,sr)) (ASSUME_TAC o SYM) THENL
      [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
       ASM_REWRITE_TAC[] THEN
       MP_TAC(ISPEC sl nch) THEN
       DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN
                    (REPEAT_TCL CHOOSE_THEN ASSUME_TAC)) THEN
       ASM_REWRITE_TAC[cdef] THEN arm_tac]) gl in
  let th = prove(tm,
    REPEAT GEN_TAC THEN REWRITE_TAC[admissible] THEN
    STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN tac) in
  cake_case_admissible_cache := (cname,th) :: !cake_case_admissible_cache;
  th;;

(* the arm variables y<i>_<j> of a case rule renamed to the binder names of  *)
(* the arms of the goal (each arm apart from the others)                     *)

let cake_case_rule_ren (th:thm) (news:string list list) =
  let is_armvar n =
    String.length n > 1 && String.sub n 0 1 = "y" && String.contains n '_' in
  let base = filter (fun n -> not (is_armvar n))
               (map (fst o dest_var) (variables (concl th))) in
  flat (map2 (fun nl i ->
      let used = ref base in
      let fresh n = let rec go n = if mem n !used then go (n ^ "'") else n in
                    let n' = go n in used := n' :: !used; n' in
      map2 (fun nw j -> "y"^string_of_int i^"_"^string_of_int j, fresh nw)
           nl (1--length nl)) news (1--length news));;

let cake_rename_case_rule (th:thm) (news:string list list) =
  let ren = cake_case_rule_ren th news in
  try let c' = cake_rename_bound ren (concl th) in EQ_MP (ALPHA (concl th) c') th
  with Failure _ -> th;;

let cake_case_rule_for (hop:term) (arms:term list) =
  let ci = case_info_of_const hop in
  let th = case_admissible_thm ci in
  let news = map2 (fun (vs,_) a ->
      let rec binders k t = if k = 0 then [] else
        let v,b = dest_abs t in fst(dest_var v) :: binders (k-1) b in
      try binders (length vs) a with Failure _ -> map (fst o dest_var) vs)
    ci.ci_pats arms in
  cake_rename_case_rule th news;;

cake_case_rule_ref := cake_case_rule_for;;

let cake_case_rule_parts (hop:term) (arms:term list) =
  let ci = case_info_of_const hop in
  (* a constructor argument of product type is split by HACK_PROFORMA *)
  if exists (fun (vs,_) -> exists (fun v -> is_type (type_of v) &&
                                            fst(dest_type(type_of v)) = "prod") vs)
            ci.ci_pats then failwith "cake_case_rule_parts" else
  let th = case_admissible_thm ci in
  let news = map2 (fun (vs,_) a ->
      let rec binders k t = if k = 0 then [] else
        let v,b = dest_abs t in fst(dest_var v) :: binders (k-1) b in
      try binders (length vs) a with Failure _ -> map (fst o dest_var) vs)
    ci.ci_pats arms in
  let ren = cake_case_rule_ren th news in
  th,(fun hth -> let c' = cake_rename_bound ren (concl hth) in
                 EQ_MP (ALPHA (concl hth) c') hth);;

cake_case_rule_parts_ref := cake_case_rule_parts;;

(* LET h e, the kit's let x = e in t: the context e = x (HOL4's LET_CONG) *)

let ADMISSIBLE_LET = prove
 (`!(<<) (p:(A->B)->P->bool) (s:P->A) (e:(A->B)->P->C) (h:(A->B)->P->C->D).
        admissible(<<) p s e /\
        admissible (<<) (\f (y,x). p f x /\ e f x = y)
                        (\(y,x). s x) (\f (y,x). h f x y)
        ==> admissible (<<) p s (\f x. LET (h f x) (e f x))`,
  REWRITE_TAC[admissible; FORALL_PAIR_THM; LET_DEF] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(e:(A->B)->P->C) g a = e f a` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

do_list (uncurry cake_register_admissible)
  ["==>",ADMISSIBLE_IMP; "ALL",ADMISSIBLE_ALL; "EX",ADMISSIBLE_EX;
   "IMAGE",ADMISSIBLE_IMAGE; "ITLIST",ADMISSIBLE_ITLIST;
   "pair_CASE",ADMISSIBLE_pair_CASE; "LET",ADMISSIBLE_LET];;
