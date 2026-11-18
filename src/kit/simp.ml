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
(* The project simpset (HOL4's srw_ss) holds the case equations,             *)
(* distinctness and injectivity of every registered datatype, the record     *)
(* theorems, and whatever cake_add_simps registers.                         *)
(* ========================================================================= *)

(* HOL4's default simpsets have no SATISFY_ss: drop the satisfy_prover of HOL Light's basic_ss *)
let cake_basic_ss thl = let Simpset(n,p,_,r) = basic_ss thl in Simpset(n,p,[],r);;

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
          let k = String.index_from l 7 '"' in
          let f = String.sub l 7 (k - 7) in
          file_on_path (!load_path) f
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
(* Conversions and rules.                                                    *)
(* ------------------------------------------------------------------------- *)

(* the project simpset augmented with thl: SIMPLIFY_CONV (CAKE_AUGMENTED_SS *)
(* thl) l is SIMPLIFY_CONV (cake_active_ss()) (l @ thl) (AUGMENT_SIMPSET    *)
(* works from the right of the list).  Made when the tactic runs, once per  *)
(* call of a tactic that simplifies many assumptions, and kept in a memo    *)
(* like the rewrite nets above (same simpset, same theorems)                *)

let cake_ss_memo = ref ([] : ((simpset * thm list) * simpset) list);;

let CAKE_AUGMENTED_SS thl =
  let ss = cake_active_ss() in
  cake_memo cake_ss_memo (fun (s,l) -> s == ss && cake_same_thms l thl) (ss,thl)
    (fun () -> itlist AUGMENT_SIMPSET thl ss);;

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
(* in a later conjunct)                                                     *)

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
      let avoid = itlist (union o frees o concl o snd) asl
                    (union av (union (frees w)
                      (union (frees c) (freesl (hyp th))))) in
      let v' = variant avoid v in
      X_CHOOSE_THEN v' (CAKE_STRIP_ASSUME_AV (v'::av)) th gl
    else ASSUME_TAC th gl;;

let CAKE_STRIP_ASSUME_TAC th = CAKE_STRIP_ASSUME_AV [] th;;

let CAKE_ASSUME_TAC th =
  let c = concl th in
  if c = cake_true_tm then ALL_TAC
  else if c = cake_false_tm then CONTR_TAC th
  else CAKE_STRIP_ASSUME_TAC th;;

let CAKE_ASSUME_NOSTRIP_TAC th =
  let c = concl th in
  if c = cake_true_tm then ALL_TAC
  else if c = cake_false_tm then CONTR_TAC th
  else ASSUME_TAC th;;

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
      MAP_EVERY CAKE_ASSUME_TAC (rev simped)) THEN
    SIMP thl) gl;;

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

let GVS_STEP_SS ss : tactic =
  POP_LAST_ASSUM (fun th ->
    ASSUM_LIST (fun asms ->
      let th' = CONV_RULE (SIMPLIFY_CONV ss asms) th in
      if is_eliminable (concl th') then VSUBST_ASM_TAC th'
      else CAKE_ASSUME_TAC th'));;

let GVS_ONE_PASS_SS ss : tactic =
  fun (asl,w as gl) -> EVERY (replicate (GVS_STEP_SS ss) (length asl)) gl;;

let GVS_STEP thl : tactic =
  fun gl -> GVS_STEP_SS (CAKE_AUGMENTED_SS thl) gl;;

let GVS_ONE_PASS thl : tactic =
  fun gl -> GVS_ONE_PASS_SS (CAKE_AUGMENTED_SS thl) gl;;

let GVS thl : tactic =
  fun gl ->
   let ss = CAKE_AUGMENTED_SS thl in
   (REPEAT (CHANGED_TAC (GVS_ONE_PASS_SS ss)) THEN SIMP thl THEN
    RVEQ_TAC) gl;;

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

let RW thl : tactic =
  fun gl ->
   let ss = CAKE_AUGMENTED_SS thl in
   (REPEAT (GEN_TAC ORELSE CONJ_TAC) THEN
    RVEQ_TAC THEN
    SIMP_SS ss THEN
    TRY (COND_CASES_TAC THEN REPEAT COND_CASES_TAC THEN SIMP_SS ss) THEN
    REPEAT BOSS_STRIP_TAC THEN
    REPEAT (CHANGED_TAC
      (VAR_EQ_TAC ORELSE
       FIRST_X_ASSUM (fun th ->
         if rw_breakable (concl th) then
           CAKE_ASSUME_TAC (CONV_RULE (SIMPLIFY_CONV ss []) th)
         else failwith "RW") ORELSE
       SIMP_SS ss))) gl;;
