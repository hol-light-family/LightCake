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

let K_DEF = new_definition `K = \(x:A) (y:B). x`;;

let K_THM = prove
 (`!(x:A) (y:B). K x y = x`,
  REWRITE_TAC[K_DEF]);;

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
                   numconvs (basic_ss []) in
  let ss0 = ss_of_conv `?x:A. P x` (CHANGED_CONV UNWIND_CONV) ss0 in
  ss_of_conv `!x:A. P x` (CHANGED_CONV FORALL_UNWIND_CONV) ss0;;

let cake_global_ss = ref (basic_ss []);;

(* files being loaded (innermost first), their needs, their registrations *)

let cake_loading = ref ([] : string list);;
let cake_file_deps = ref ([] : (string * string list) list);;
let cake_simp_buckets = ref ([] : (string * thm list) list);;
let cake_context = ref (None : string option);;   (* set by cake_begin *)

(* simpsets per context ("*" = everything), built lazily *)
let cake_ss_cache = ref ([] : (string * simpset) list);;

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
  try assoc key (!cake_ss_cache) with Failure _ ->
  let thms =
    if key = "*" then flat (map snd (!cake_simp_buckets))
    else
      let cl = cake_file_closure key [] in
      flat (mapfilter (fun f -> assoc f (!cake_simp_buckets)) cl) in
  let ss = ss_of_thms thms (!cake_global_ss) in
  cake_ss_cache := (key,ss) :: !cake_ss_cache; ss;;

(* the simpset of the current context *)
let cake_active_ss () = cake_ss_for (cake_context_key());;

(* kept for compatibility: the current simpset as a reference *)
let cake_ss = ref (basic_ss []);;

let cake_rebuild_ss () =
  cake_global_ss := ss_of_thms (!cake_simp_thms) (cake_base_ss());
  cake_ss_cache := [];;

(* global registration (datatypes, records): every cached simpset grows *)

let cake_add_global_simps thl =
  cake_simp_thms := thl @ !cake_simp_thms;
  cake_global_ss := ss_of_thms thl (!cake_global_ss);
  cake_ss_cache := map (fun (k,ss) -> k,ss_of_thms thl ss) (!cake_ss_cache);;

(* registration by a file (HOL4 [simp]) *)

let cake_add_simps thl =
  let f = match !cake_loading with f::_ -> f
          | [] -> (match !cake_context with Some f -> f | None -> "*") in
  let old = try assoc f (!cake_simp_buckets) with Failure _ -> [] in
  cake_simp_buckets := (f,thl @ old) ::
                       filter (fun (g,_) -> g <> f) (!cake_simp_buckets);
  (* the caches that see f: f itself, "*", and anything being loaded *)
  cake_ss_cache :=
    mapfilter (fun (k,ss) ->
                 if k = f || k = "*" then (k,ss_of_thms thl ss)
                 else if mem k (!cake_loading) then failwith ""
                 else if mem f (cake_file_closure k []) then failwith ""
                 else (k,ss)) (!cake_ss_cache);;

(* remove registered rewrites (by conclusion), everywhere *)
let cake_del_simps thl =
  let keep th = not (exists (equals_thm th) thl) in
  cake_simp_thms := filter keep (!cake_simp_thms);
  cake_simp_buckets := map (fun (f,l) -> f,filter keep l) (!cake_simp_buckets);
  cake_rebuild_ss();;

(* interactive work on a file: use the simpset of its needs closure *)

let cake_begin file =
  let f = file_on_path (!load_path) file in
  cake_file_deps := (f,read_needs_lines f) ::
                    filter (fun (g,_) -> g <> f) (!cake_file_deps);
  cake_context := Some f;
  cake_ss_cache := filter (fun (k,_) -> k <> f) (!cake_ss_cache);;

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

let CAKE_SIMP_CONV thl tm = SIMPLIFY_CONV (cake_active_ss()) thl tm;;

let CAKE_SIMP_RULE thl = CONV_RULE (CAKE_SIMP_CONV thl);;

(* HOL4 simp_tac (no assumptions) and simp (= asm_simp_tac) *)

let SIMP_NOASM thl = CONV_TAC (CAKE_SIMP_CONV thl);;

let SIMP thl = ASM (fun l -> CONV_TAC (CAKE_SIMP_CONV l)) thl;;

(* ------------------------------------------------------------------------- *)
(* Putting a simplified assumption back: closes the goal if it is F (or the *)
(* goal itself), drops it if it is T, else strips it in (conjunctions,      *)
(* disjunctions = case splits, existentials).                               *)
(* ------------------------------------------------------------------------- *)

(* stripping that never fails on name clashes: every existential gets a     *)
(* name that is fresh for the whole goal and the theorem (HOL Light's        *)
(* STRIP_ASSUME_TAC can fail with CHOOSE when an inner bound name is free    *)
(* in a later conjunct)                                                     *)

let rec CAKE_STRIP_ASSUME_AV (av:term list) th : tactic =
  fun (asl,w as gl) ->
    let c = concl th in
    if c = `T` then ALL_TAC gl
    else if c = `F` then CONTR_TAC th gl
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
  if c = `T` then ALL_TAC
  else if c = `F` then CONTR_TAC th
  else CAKE_STRIP_ASSUME_TAC th;;

let CAKE_ASSUME_NOSTRIP_TAC th =
  let c = concl th in
  if c = `T` then ALL_TAC
  else if c = `F` then CONTR_TAC th
  else ASSUME_TAC th;;

(* ------------------------------------------------------------------------- *)
(* FS: HOL4 full_simp_tac (srw_ss()) thl.                                    *)
(* ------------------------------------------------------------------------- *)

let FS thl : tactic =
  POP_ASSUM_LIST (fun asms ->
    let simped =
      rev_itlist (fun th acc -> CAKE_SIMP_RULE (acc @ thl) th :: acc)
                 (rev asms) [] in
    MAP_EVERY CAKE_ASSUME_TAC (rev simped)) THEN
  SIMP thl;;

(* ------------------------------------------------------------------------- *)
(* Variable elimination.  An assumption v = t or t = v with v a variable not *)
(* free in t is used to substitute t for v everywhere and is then dropped.   *)
(* ------------------------------------------------------------------------- *)

let is_eliminable tm =
  is_eq tm &&
  let l,r = dest_eq tm in
  (is_var l && not (free_in l r)) || (is_var r && not (free_in r l));;

let VSUBST_ASM_TAC th =
  let l,r = dest_eq(concl th) in
  let th' = if is_var l && not (free_in l r) then th else SYM th in
  (* th' : v = t; replace v by t *)
  let v = lhs(concl th') in
  if not (is_var v) then failwith "VSUBST_ASM_TAC" else
  SUBST_ALL_TAC th' THEN
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

let GVS_STEP thl : tactic =
  POP_LAST_ASSUM (fun th ->
    ASSUM_LIST (fun asms ->
      let th' = CAKE_SIMP_RULE (asms @ thl) th in
      if is_eliminable (concl th') then VSUBST_ASM_TAC th'
      else CAKE_ASSUME_TAC th'));;

let GVS_ONE_PASS thl : tactic =
  fun (asl,w as gl) -> EVERY (replicate (GVS_STEP thl) (length asl)) gl;;

let GVS thl : tactic =
  REPEAT (CHANGED_TAC (GVS_ONE_PASS thl)) THEN SIMP thl THEN
  RVEQ_TAC;;

(* ------------------------------------------------------------------------- *)
(* RW: HOL4 rw[thl] (srw_tac): strip the goal, eliminate var equations,      *)
(* simplify, split the goal's conditionals, strip again, simplify the        *)
(* assumptions that can be broken up or that equate constructors.            *)
(* ------------------------------------------------------------------------- *)

let BOSS_STRIP_TAC : tactic =
  GEN_TAC ORELSE CONJ_TAC ORELSE DISCH_THEN CAKE_ASSUME_TAC;;

let rw_breakable tm =
  is_exists tm || is_conj tm || is_disj tm || tm = `T` || tm = `F` ||
  (is_neg tm && is_neg(rand tm)) ||
  can (find_term (fun t -> is_eq t && is_constructor_app (lhs t) &&
                           is_constructor_app (rhs t))) tm;;

let RW thl : tactic =
  REPEAT (GEN_TAC ORELSE CONJ_TAC) THEN
  RVEQ_TAC THEN
  SIMP thl THEN
  TRY (COND_CASES_TAC THEN REPEAT COND_CASES_TAC THEN SIMP thl) THEN
  REPEAT BOSS_STRIP_TAC THEN
  REPEAT (CHANGED_TAC
    (VAR_EQ_TAC ORELSE
     FIRST_X_ASSUM (fun th ->
       if rw_breakable (concl th) then
         CAKE_ASSUME_TAC (CAKE_SIMP_RULE thl th)
       else failwith "RW") ORELSE
     SIMP thl));;
