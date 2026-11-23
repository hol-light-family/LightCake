(* ========================================================================= *)
(* data_to_word_gcProof_p2: part 2 of 3 (HOL4 lines 3001-5933) of the port   *)
(* of HOL4 compiler/backend/proofs/data_to_word_gcProofScript.sml (CakeML    *)
(* v3479).  Part of the correctness proof for data_to_word.                  *)
(* The parts _p1, _p2, _p3 are loaded one after the other (each needs the    *)
(* previous one); data_to_word_gcProof.ml needs the last.                    *)
(* GCP2AUX_ names are local helpers of this part.                            *)
(* Rendering: HOL4 'a ml_heap is written out as                              *)
(*   ((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list *)
(* and HOL4 Type state (wordSem state) is (A,C,FFI)wl_state; wordSem is a    *)
(* qualified ancestor in HOL4, so its constants are the wl_ ones.            *)
(* ========================================================================= *)

needs "compiler/backend/proofs/data_to_word_gcProof_p1.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 2: HOL4 lines 3001-5933 ===== *)

(* ------------------------------------------------------------------------- *)
(* Helpers of this part (GCP2AUX_ theorems, gcp2aux_ functions).             *)
(* ------------------------------------------------------------------------- *)

(* does the term contain a constant of this name *)
let gcp2aux_has_const n tm =
  can (find_term (fun t -> is_const t && fst(dest_const t) = n)) tm;;

(* GCP2AUX: the domain of adjust_set consists of the adjust_var of the     *)
(* domain                                                                   *)
let GCP2AUX_IN_domain_adjust_set = prove
 (`!(s:A spt) k. k IN domain (adjust_set s) <=> ?n. k = adjust_var n /\ n IN domain s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[adjust_set_def; domain_fromAList; IN_SET_OF_LIST; MEM_MAP; EXISTS_PROD; FST;
              PAIR_EQ] THEN
  REWRITE_TAC[domain_lookup; GSYM MEM_toAList] THEN MESON_TAC[]);;

(* GCP2AUX: what a successful cut of the data locals is *)
let GCP2AUX_data_cut_env = prove
 (`!r (ls:A spt) x.
     data_cut_env r ls = SOME x ==> x = mk_wf (sptree_inter ls r) /\ domain r SUBSET domain ls`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_env_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

(* GCP2AUX: what a successful cut of the word locals is *)
let GCP2AUX_cut_envs_adjust_sets = prove
 (`!(r:B spt) (lt:A spt) y.
     cut_envs (adjust_sets r) lt = SOME y ==>
     FST y = sptree_inter lt (LS one) /\ SND y = sptree_inter lt (adjust_set r) /\
     domain (adjust_set r) SUBSET domain lt /\ 0 IN domain lt`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_envs_def; adjust_sets_def; cut_names_def; FST; SND] THEN
  REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[domain_def; SING_SUBSET]) THEN ASM_REWRITE_TAC[FST; SND]);;

let gcp2aux_is_star tm =
  try let f,_ = dest_comb tm in
      let s,_ = dest_comb f in
      is_const s && fst(dest_const s) = "STAR"
  with Failure _ -> false;;

let rec gcp2aux_star_leaves tm =
  if gcp2aux_is_star tm
  then gcp2aux_star_leaves (rand(rator tm)) @ gcp2aux_star_leaves (rand tm)
  else [tm];;

(* |- p = q for STAR trees p, q equal up to AC *)
let gcp2aux_STAR_AC_EQ p q =
  if aconv p q then REFL p else AC LSORTAUX_STAR_AC (mk_eq(p,q));;

(* closes a goal  q s  with an assumption  p s  (p, q equal up to AC) *)
let gcp2aux_sep_ac_tac : tactic = fun (asl,w as g) ->
  let q,s = dest_comb w in
  let ql = gcp2aux_star_leaves q in
  let try_one (_,th) =
    let c = concl th in
    if is_comb c && aconv (rand c) s &&
       length (gcp2aux_star_leaves (rator c)) = length ql
    then let p = rator c in
         ACCEPT_TAC (EQ_MP (AP_THM (gcp2aux_STAR_AC_EQ p q) s) th) g
    else failwith "" in
  tryfind try_one asl;;

(* GCP2AUX: tuples of length 7 *)
let GCP2AUX_TUPLE7 = prove
 (`!p:A#B#C#D#E#F#G. ?a b c d e f g. p = (a,b,c,d,e,f,g)`,
  GEN_TAC THEN MAP_EVERY EXISTS_TAC [`FST(p:A#B#C#D#E#F#G)`; `FST(SND(p:A#B#C#D#E#F#G))`;
    `FST(SND(SND(p:A#B#C#D#E#F#G)))`; `FST(SND(SND(SND(p:A#B#C#D#E#F#G))))`;
    `FST(SND(SND(SND(SND(p:A#B#C#D#E#F#G)))))`;
    `FST(SND(SND(SND(SND(SND(p:A#B#C#D#E#F#G))))))`;
    `SND(SND(SND(SND(SND(SND(p:A#B#C#D#E#F#G))))))`] THEN
  REWRITE_TAC[PAIR]);;

let gcp2aux_mk_star p q =
  let x = fst(dest_fun_ty(fst(dest_fun_ty(type_of p)))) in
  mk_comb(mk_comb(mk_const("STAR",[x,`:A`]),p),q);;

let gcp2aux_list_mk_star l =
  match l with
    [] -> failwith "gcp2aux_list_mk_star"
  | h::t -> rev_itlist (fun x acc -> gcp2aux_mk_star acc x) t h;;

(* th : |- p s, leaf a leaf of the STAR tree p: |- (leaf STAR rest) s *)
let gcp2aux_sep_focus leaf th =
  let p,s = dest_comb(concl th) in
  let leaves = gcp2aux_star_leaves p in
  let rec remove l = match l with
      [] -> failwith "gcp2aux_sep_focus"
    | h::t -> if aconv h leaf then t else h :: remove t in
  let rest = remove leaves in
  let q = if rest = [] then leaf else gcp2aux_mk_star leaf (gcp2aux_list_mk_star rest) in
  EQ_MP (AP_THM (gcp2aux_STAR_AC_EQ p q) s) th;;

(* the leaf of a STAR tree that is set_sep_one at address a *)
let gcp2aux_one_leaf a p =
  find (fun l -> try let f,arg = dest_comb l in
                     fst(dest_const f) = "set_sep_one" && aconv (fst(dest_pair arg)) a
                 with Failure _ -> false) (gcp2aux_star_leaves p);;

(* reading: th : |- p (fun2set (m,dm)) with a leaf set_sep_one (a,x):     *)
(* |- m a = x /\ a IN dm                                                   *)
let gcp2aux_sep_read a th =
  let leaf = gcp2aux_one_leaf a (rator(concl th)) in
  MATCH_MP read_fun2set (gcp2aux_sep_focus leaf th);;

(* writing: th : |- p (fun2set (m,dm)) with a leaf set_sep_one (a,x):     *)
(* |- (rest STAR set_sep_one (a,y)) (fun2set ((a =+ y) m,dm))              *)
let gcp2aux_sep_write a y th =
  let leaf = gcp2aux_one_leaf a (rator(concl th)) in
  SPEC y (MATCH_MP write_fun2set (gcp2aux_sep_focus leaf th));;

(* the first application of the constant name in tm with no bound variable *)
let gcp2aux_find_app name tm =
  let rec find bvs tm =
    let here () =
      let f,args = strip_comb tm in
      if is_const f && fst(dest_const f) = name && args <> [] &&
         not (exists (fun v -> vfree_in v tm) bvs) then tm else failwith "" in
    try here () with Failure _ ->
    match tm with
      Comb(f,x) -> (try find bvs f with Failure _ -> find bvs x)
    | Abs(v,b) -> find (v::bvs) b
    | _ -> failwith "gcp2aux_find_app" in
  find [] tm;;

(* the conclusion  l = r  of th, with l an application of the constant name *)
let gcp2aux_is_app_eq name th =
  let c = concl th in
  is_eq c && (try fst(dest_const(fst(strip_comb(lhs c)))) = name with Failure _ -> false);;

(* moves such an equation from the assumptions to the goal *)
let gcp2aux_undisch_app name : tactic =
  FIRST_X_ASSUM(fun th -> if gcp2aux_is_app_eq name th then MP_TAC th else NO_TAC);;

(* rewrites the goal and the other assumptions with the assumption  l = r *)
let gcp2aux_rw_asm_tac (l:term) : tactic =
  FIRST_ASSUM(fun th -> if is_eq(concl th) && aconv (lhs(concl th)) l
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN ASSUME_TAC th
    else NO_TAC);;

(* goal  gc_state_ok_fupd (K F) s = s1 ==> w  with  gc_state_ok s1  assumed *)
let gcp2aux_ok_F_tac : tactic =
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `F`)) THEN REWRITE_TAC[];;

(* abbreviates the argument X of the antecedent  f c X = y  of the goal *)
let gcp2aux_abbrev_arg_tac (v:string) : tactic = fun (asl,w as g) ->
  let tm = rand(lhand(lhand w)) in
  ABBREV_TAC (mk_eq(mk_var(v,type_of tm),tm)) g;;

(* names the components of the first closed tuple-valued application of   *)
(* the constant name in the goal, else in the assumptions, by fresh        *)
(* variables (new assumption  app = (v1,...,vn))                            *)
let gcp2aux_tuple_tac name names : tactic = fun (asl,w as g) ->
  let tm = try gcp2aux_find_app name w with Failure _ ->
           tryfind (fun (_,th) -> gcp2aux_find_app name (concl th)) asl in
  let th0 = match length names with
      2 -> PAIR_SURJECTIVE | 3 -> BASICAUX_TUPLE3 | 4 -> BASICAUX_TUPLE4
    | 5 -> BASICAUX_TUPLE5 | 6 -> GC1AUX_PAIR6 | 7 -> GCP2AUX_TUPLE7
    | _ -> failwith "gcp2aux_tuple_tac: arity" in
  let th = ISPEC tm th0 in
  let rec split ty n =
    if n <= 1 then [ty] else
    match dest_type ty with
      ("prod",[a;b]) -> a :: split b (n-1)
    | _ -> failwith "gcp2aux_tuple_tac: not a tuple" in
  let tys = split (type_of tm) (length names) in
  let vs = map2 (fun n ty -> mk_var(n,ty)) names tys in
  (itlist (fun v k -> X_CHOOSE_THEN v k) vs ASSUME_TAC) th g;;

(* th : |- p s with a leaf set_sep_cond c of the STAR tree p: |- c /\ rest s *)
let gcp2aux_sep_cond th =
  let leaf = find (fun l -> try fst(dest_const(rator l)) = "set_sep_cond" with Failure _ -> false)
                  (gcp2aux_star_leaves (rator(concl th))) in
  CONV_RULE (REWR_CONV (CONJUNCT1 (SPEC_ALL cond_STAR))) (gcp2aux_sep_focus leaf th);;

let rec gcp2aux_strip_pair tm =
  try let a,b = dest_pair tm in a :: gcp2aux_strip_pair b with Failure _ -> [tm];;

(* a leaf of a STAR tree with an address argument: name, address, the     *)
(* other arguments, and the congruence  a1 = a2 |- leaf a1 = leaf a2       *)
let gcp2aux_leaf_split l =
  let f,args = strip_comb l in
  let name = try fst(dest_const f) with Failure _ -> "" in
  if name = "set_sep_one" && length args = 1 then
    let pr = hd args in
    let a,v = dest_pair pr in
    (name, a, [v], fun th -> AP_TERM f (AP_THM (AP_TERM (rator(rator pr)) th) v))
  else if mem name ["word_heap"; "misc_word_list"; "word_list_exists"] && args <> [] then
    (name, hd args, tl args,
     fun th -> rev_itlist (fun x th' -> AP_THM th' x) (tl args) (AP_TERM f th))
  else failwith "gcp2aux_leaf_split";;

(* closes a goal  q s  with an assumption  p s  whose leaves agree with    *)
(* those of q up to AC and up to the addresses of the leaves; the address  *)
(* equations are proved by addr_tac (with the assumptions of the goal)     *)
let gcp2aux_sep_addr_tac (addr_tac:tactic) : tactic = fun (asl,w as g) ->
  let q,s = dest_comb w in
  let ql = gcp2aux_star_leaves q in
  let rec remove x l = match l with
      [] -> failwith "remove"
    | h::t -> if aconv h x then t else h :: remove x t in
  let try_one (_,th) =
    let c = concl th in
    if not (is_comb c && aconv (rand c) s) then failwith "" else
    let pl = gcp2aux_star_leaves (rator c) in
    if length pl <> length ql then failwith "" else
    let qrest,prest = itlist (fun lq (qr,pr) ->
        try (qr, remove lq pr) with Failure _ -> (lq::qr, pr)) ql ([],pl) in
    let rec pair qr pr = match qr with
        [] -> if pr = [] then [] else failwith "pair"
      | lq::qt ->
          let (nq,aq,rq,cong) = gcp2aux_leaf_split lq in
          let lp = find (fun lp -> try let (np,_,rp,_) = gcp2aux_leaf_split lp in
                           np = nq && length rp = length rq && forall2 aconv rp rq
                         with Failure _ -> false) pr in
          let (_,ap,_,_) = gcp2aux_leaf_split lp in
          let eq = TAC_PROOF((asl, mk_eq(aq,ap)), addr_tac) in
          cong eq :: pair qt (remove lp pr) in
    let eqs = pair qrest prest in
    let th1 = if eqs = [] then REFL q else SUBS_CONV eqs q in
    let q' = rand(concl th1) in
    let th2 = EQ_MP (AP_THM (gcp2aux_STAR_AC_EQ (rator c) q') s) th in
    ACCEPT_TAC (EQ_MP (SYM (AP_THM th1 s)) th2) g in
  tryfind try_one asl;;

let gcp2aux_hl_rw = [heap_length_APPEND; heap_length_CONS; heap_length_NIL; el_length_def;
                     ADD_CLAUSES];;

(* heap addresses  word_add p (word_mul bytes_in_word (word n))  *)
let gcp2aux_addr_tac : tactic =
  REWRITE_TAC gcp2aux_hl_rw THEN REWRITE_TAC[GSYM word_add_n2w] THEN CONV_TAC WORD_RULE;;

(* goal  f X = r  with an assumption  f Y = r: reduce to the component equations *)
let gcp2aux_same_app_tac name : tactic =
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq name th
    then GEN_REWRITE_TAC RAND_CONV [SYM th] else NO_TAC) THEN
  AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ];;

(* linear arithmetic over the num (in)equations among the assumptions *)
let gcp2aux_arith_tac : tactic = fun (asl,w as g) ->
  let is_num_rel tm =
    try let f,args = strip_comb tm in
        let n = fst(dest_const f) in
        length args = 2 && type_of (hd args) = `:num` && mem n ["="; "<"; "<="]
    with Failure _ -> false in
  let ths = map snd (filter (fun (_,th) -> is_num_rel (concl th)) asl) in
  let simple th = not (gcp2aux_has_const "DIV" (concl th)) &&
                  not (gcp2aux_has_const "EXP" (concl th)) in
  let tac l = MAP_EVERY MP_TAC l THEN REWRITE_TAC (LENGTH :: LENGTH_APPEND :: gcp2aux_hl_rw) THEN
              ARITH_TAC in
  (tac (filter simple ths) ORELSE tac ths) g;;

(* GCP2AUX: distinct heap offsets give distinct addresses *)
let GCP2AUX_word_offset_ne = prove
 (`!(p:A word) a b.
     a < b /\ b * (dimindex(:A) DIV 8) < dimword(:A) /\ good_dimindex(:A) ==>
     ~(word_add p (word_mul bytes_in_word (word a)) =
       word_add p (word_mul bytes_in_word (word b)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_ADD_LCANCEL; bytes_in_word_def; word_mul_n2w] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `0 < dimindex(:A) DIV 8` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[good_dimindex_def]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `dimindex(:A) DIV 8 * a < dimindex(:A) DIV 8 * b` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LT_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `dimindex(:A) DIV 8 * b < dimword(:A)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:A word->num`) THEN
  REWRITE_TAC[VAL_WORD; GSYM dimword_def] THEN
  SUBGOAL_THEN `dimindex(:A) DIV 8 * a < dimword(:A)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC);;

(* GCP2AUX: a heap length bound below dimword *)
let GCP2AUX_LT_DIMWORD = prove
 (`!n. n * (dimindex(:A) DIV 8) < dimword(:A) /\ good_dimindex(:A) ==> n < dimword(:A)`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  POP_ASSUM SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

(* GCP2AUX: a nonempty heap segment does not end where it starts *)
let GCP2AUX_word_offset_ne0 = prove
 (`!(p:A word) b.
     0 < b /\ b * (dimindex(:A) DIV 8) < dimword(:A) /\ good_dimindex(:A) ==>
     ~(p = word_add p (word_mul bytes_in_word (word b)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A word`; `0`; `b:num`] GCP2AUX_word_offset_ne) THEN
  ASM_REWRITE_TAC[WORD_MUL_0; WORD_ADD_0]);;

(* GCP2AUX: shifting a heap offset in bytes back to words *)
let GCP2AUX_ushr_bytes = prove
 (`!n. good_dimindex(:A) /\ n * (dimindex(:A) DIV 8) < dimword(:A) ==>
       word_ushr (word_mul bytes_in_word (word n):A word) (backend_common_word_shift (:A)) =
       word n`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[bytes_in_word_mul_eq_shift] THEN
  MATCH_MP_TAC lsl_lsr THEN
  SUBGOAL_THEN `n < dimword(:A)` ASSUME_TAC THENL
   [MATCH_MP_TAC GCP2AUX_LT_DIMWORD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD; GSYM dimword_def; MOD_LT] THEN
  UNDISCH_TAC `n * dimindex(:A) DIV 8 < dimword(:A)` THEN
  UNDISCH_TAC `good_dimindex(:A)` THEN
  REWRITE_TAC[good_dimindex_def; backend_common_word_shift_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* rewriting with the record accessors of gc states *)
let gcp2aux_st_rw = [gc_state_FIELDS.ri_accfupds; gc_state_FIELDS.ri_accessors; K_THM;
                     empty_state_def];;

(* substitutes the variables with the given names by their equations *)
let gcp2aux_subst_vars_tac (names:string list) : tactic =
  let isv tm = is_var tm && mem (fst(dest_var tm)) names in
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && isv (lhs c) && not (vfree_in (lhs c) (rhs c)) then SUBST_ALL_TAC th
    else if is_eq c && isv (rhs c) && not (vfree_in (rhs c) (lhs c)) then SUBST_ALL_TAC (SYM th)
    else NO_TAC));;

(* addresses, using the heap length equations among the assumptions *)
let gcp2aux_addr_hl_tac : tactic = fun (asl,w as g) ->
  let ths = map snd (filter (fun (_,th) -> gcp2aux_is_app_eq "heap_length" th &&
                                 not (gcp2aux_has_const "-" (concl th))) asl) in
  (REWRITE_TAC ths THEN REWRITE_TAC gcp2aux_hl_rw THEN REWRITE_TAC ths THEN
   gcp2aux_addr_tac) g;;

(* the assumptions  f x = y  with f one of the given constants *)
let gcp2aux_eqs_of names (asl:(string*thm)list) =
  map snd (filter (fun (_,th) -> exists (fun n -> gcp2aux_is_app_eq n th) names) asl);;

(* addresses, using the heap length and list length equations among the assumptions *)
let gcp2aux_addr_len_tac : tactic = fun (asl,w as g) ->
  let ths = map snd (filter (fun (_,th) ->
      (gcp2aux_is_app_eq "heap_length" th || gcp2aux_is_app_eq "LENGTH" th) &&
      not (gcp2aux_has_const "-" (concl th))) asl) in
  (REWRITE_TAC ths THEN REWRITE_TAC gcp2aux_hl_rw THEN REWRITE_TAC ths THEN
   gcp2aux_addr_tac) g;;

(* goal  q s  with a leaf set_sep_cond c of q: reduces it to  c /\ rest s *)
let gcp2aux_goal_cond_tac : tactic = fun (asl,w as g) ->
  let q,s = dest_comb w in
  let leaves = gcp2aux_star_leaves q in
  let leaf = find (fun l -> try fst(dest_const(rator l)) = "set_sep_cond" with Failure _ -> false)
                  leaves in
  let rec remove l = match l with
      [] -> failwith "gcp2aux_goal_cond_tac"
    | h::t -> if aconv h leaf then t else h :: remove t in
  let rest = remove leaves in
  let q' = if rest = [] then leaf else gcp2aux_mk_star leaf (gcp2aux_list_mk_star rest) in
  let th = AP_THM (gcp2aux_STAR_AC_EQ q q') s in
  (CONV_TAC(K th) THEN CONV_TAC(REWR_CONV (CONJUNCT1 (SPEC_ALL cond_STAR)))) g;;

(* GCP2AUX: a lookup that succeeds *)
let GCP2AUX_FLOOKUP_SOME = prove
 (`!(f:(A,B)fmap) k v. FLOOKUP f k = SOME v <=> k IN FDOM f /\ FAPPLY f k = v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_INJ; distinctness "option"]);;

(* GCP2AUX: moving a word root gives a word *)
let GCP2AUX_word_gc_move_Word = prove
 (`!c (w:A word) i pa old m dm.
     isWord (FST (word_gc_move c (wl_Word w,i,pa,old,m,dm)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_gc_move_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[isWord_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN COND_CASES_TAC THEN REWRITE_TAC[isWord_def] THEN
  gcp2aux_tuple_tac "memcpy" ["pa1";"m1";"c1"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[isWord_def]);;

(* GCP2AUX: a full collection whose first root is a word gives a word first root *)
let GCP2AUX_word_full_gc_HD = prove
 (`!c (w:A word) ws new old m dm rs i pa m1 c1.
     word_full_gc c (CONS (wl_Word w) ws,new,old,m,dm) = (rs,i,pa,m1,c1) ==>
     isWord (HD rs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_full_gc_def; word_gc_move_roots_def] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `w:A word`; `word 0:A word`; `new:A word`;
    `old:A word`; `m:A word->A word_loc`; `dm:A word->bool`] GCP2AUX_word_gc_move_Word) THEN
  gcp2aux_tuple_tac "word_gc_move" ["w1";"i1";"pa1";"m2";"c2"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  gcp2aux_tuple_tac "word_gc_move_roots" ["ws2";"i2";"pa2";"m3";"c3"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  gcp2aux_tuple_tac "word_gc_move_loop" ["i4";"pa4";"m4";"c4"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `rs:(A word_loc)list`)) THEN
  ASM_REWRITE_TAC[HD]);;

(* HOL4 line 3001 *)
let word_gen_gc_partial_move_roots_thm = prove
 (`!x xs x1 w s1 s pa1 pa m1 m i1 frame dm curr c1 old current refs gen_conf conf.
     (gen_gc_partial_gc_move_list gen_conf s x = (x1,s1)) /\ gc_state_ok s1 /\
     gc_state_h2 s = [] /\ gc_state_r4 s = [] /\
     gen_gc_partial_conf_limit gen_conf = heap_length (gc_state_heap s) /\
     heap_length (gc_state_heap s) <= dimword (:A) DIV 2 EXP shift_length conf /\
     gen_gc_partial_conf_gen_start gen_conf <= gen_gc_partial_conf_refs_start gen_conf /\
     gen_gc_partial_conf_refs_start gen_conf <= heap_length (gc_state_heap s) /\
     (heap_segment (gen_gc_partial_conf_gen_start gen_conf,
                    gen_gc_partial_conf_refs_start gen_conf) (gc_state_heap s) =
        SOME (old,current,refs)) /\
     (!t r. (gen_gc_partial_conf_isRef gen_conf (t,r) <=> isMutTag t)) /\
     heap_length (gc_state_heap s) * (dimindex (:A) DIV 8) < dimword (:A) /\
     (word_heap (word_add curr (word_mul bytes_in_word (word (heap_length old))))
        current conf STAR misc_word_list pa xs STAR frame) (fun2set (m,dm)) /\
     (word_gen_gc_partial_move_roots conf
        (MAP (word_addr conf) x,word (gc_state_a s),pa,curr:A word,m,dm,
         word_mul bytes_in_word (word (gen_gc_partial_conf_gen_start gen_conf)),
         word_mul bytes_in_word (word (gen_gc_partial_conf_refs_start gen_conf))) =
       (w:(A word_loc)list,i1,pa1,m1,c1)) /\
     LENGTH xs = gc_state_n s /\ good_dimindex (:A) ==>
     ?xs1 current1.
       (word_heap (word_add curr (word_mul bytes_in_word (word (heap_length old))))
          current1 conf STAR
        word_heap pa (gc_state_h2 s1) conf STAR
        misc_word_list pa1 xs1 STAR frame) (fun2set (m1,dm)) /\
       (w = MAP (word_addr conf) x1) /\
       heap_length (gc_state_heap s1) = heap_length (gc_state_heap s) /\
       (heap_segment (gen_gc_partial_conf_gen_start gen_conf,
                      gen_gc_partial_conf_refs_start gen_conf) (gc_state_heap s1) =
          SOME (old,current1,refs)) /\
       c1 /\ (i1 = word (gc_state_a s1)) /\ gc_state_n s1 = LENGTH xs1 /\
       gc_state_n s =
         heap_length (gc_state_h2 s1) + gc_state_n s1 + heap_length (gc_state_r4 s1) /\
       pa1 = word_add pa (word_mul bytes_in_word (word (heap_length (gc_state_h2 s1))))`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[gen_gc_partial_gc_move_list_def; MAP; word_gen_gc_partial_move_roots_def;
                PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`xs:(A word_loc)list`; `current:((A word_loc,
       data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
    ASM_REWRITE_TAC[word_heap_def; SEP_CLAUSES; heap_length_NIL; ADD_CLAUSES; MAP;
                    WORD_MUL_0; WORD_ADD_0];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[gen_gc_partial_gc_move_list_def; MAP] THEN
  REWRITE_TAC[word_gen_gc_partial_move_roots_def] THEN
  MP_TAC(ISPEC `gen_gc_partial_gc_move
     (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf)
     (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) h`
     PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:(A word_loc)heap_address` (X_CHOOSE_THEN
    `s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `gen_gc_partial_gc_move_list
     (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf)
     (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) t`
     PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:((A word_loc)heap_address)list` (X_CHOOSE_THEN
    `s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `word_gen_gc_partial_move conf (word_addr conf h,
     word (gc_state_a (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)),
     pa,curr:A word,m,dm,
     word_mul bytes_in_word (word (gen_gc_partial_conf_gen_start
       (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf))),
     word_mul bytes_in_word (word (gen_gc_partial_conf_refs_start gen_conf)))`
    BASICAUX_TUPLE5) THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:A word_loc` (X_CHOOSE_THEN `i2:A word` (X_CHOOSE_THEN
    `pa2:A word` (X_CHOOSE_THEN `m2:A word->A word_loc` (X_CHOOSE_THEN `c2:bool`
    ASSUME_TAC))))) THEN
  MP_TAC(ISPEC `word_gen_gc_partial_move_roots conf (MAP (word_addr conf) t,i2,pa2,
     curr:A word,m2,dm,
     word_mul bytes_in_word (word (gen_gc_partial_conf_gen_start
       (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf))),
     word_mul bytes_in_word (word (gen_gc_partial_conf_refs_start gen_conf)))`
    BASICAUX_TUPLE5) THEN
  DISCH_THEN(X_CHOOSE_THEN `ws3:(A word_loc)list` (X_CHOOSE_THEN `i3:A word` (X_CHOOSE_THEN
    `pa3:A word` (X_CHOOSE_THEN `m3:A word->A word_loc` (X_CHOOSE_THEN `c3:bool`
    ASSUME_TAC))))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `gc_state_ok (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                  gc_state)` ASSUME_TAC THENL
   [ASM_MESON_TAC[gc_partial_move_list_ok_before]; ALL_TAC] THEN
  MP_TAC(ISPECL [`gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf`;
    `s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `h:(A word_loc)heap_address`; `h1:(A word_loc)heap_address`;
    `s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `conf:data_to_word_config`; `curr:A word`;
    `old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `current:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `pa:A word`; `xs:(A word_loc)list`; `frame:(A word#A word_loc->bool)->bool`;
    `m:A word->A word_loc`; `dm:A word->bool`; `w2:A word_loc`; `i2:A word`;
    `pa2:A word`; `m2:A word->A word_loc`; `c2:bool`] word_gen_gc_partial_move_thm) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs2:(A word_loc)list` (X_CHOOSE_THEN
    `current2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:((A word_loc)heap_address)list`;
    `s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `t1:((A word_loc)heap_address)list`;
    `s1:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf`]
    gc_partial_move_list_with_NIL) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `gen_gc_partial_gc_move_list
     (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf)
     (gc_state_h2_fupd (K []) (gc_state_r4_fupd (K [])
        (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))) t`
     PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t4:((A word_loc)heap_address)list` (X_CHOOSE_THEN
    `s4:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`xs2:(A word_loc)list`; `t1:((A word_loc)heap_address)list`;
    `ws3:(A word_loc)list`;
    `s4:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `gc_state_h2_fupd (K []) (gc_state_r4_fupd (K [])
       (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))`;
    `pa1:A word`;
    `word_add pa (word_mul bytes_in_word (word (heap_length (gc_state_h2
       (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))))):A word`;
    `m1:A word->A word_loc`; `m2:A word->A word_loc`; `i1:A word`;
    `word_heap pa (gc_state_h2
       (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) conf STAR
     (frame:(A word#A word_loc->bool)->bool)`;
    `dm:A word->bool`; `curr:A word`; `c3:bool`;
    `old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `current2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf`;
    `conf:data_to_word_config`]) THEN
  ASM_REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  ANTS_TAC THENL [gcp2aux_sep_ac_tac; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs3:(A word_loc)list` (X_CHOOSE_THEN
    `current3:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`xs3:(A word_loc)list`; `current3:((A word_loc,
     data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
  ASM_REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM; MAP; heap_length_APPEND] THEN
  REWRITE_TAC[word_heap_APPEND] THEN
  REPEAT CONJ_TAC THENL
   [gcp2aux_sep_ac_tac;
    ARITH_TAC;
    REWRITE_TAC[GSYM word_add_n2w] THEN CONV_TAC WORD_RULE]);;

(* HOL4 line 3069 *)
let word_gen_gc_partial_move_list_thm = prove
 (`!x xs x1 s1 s pa1 pa m1 m i1 frame dm curr c1 k old current refs gen_conf conf k1.
     (gen_gc_partial_gc_move_list gen_conf s x = (x1,s1)) /\ gc_state_ok s1 /\
     gc_state_h2 s = [] /\ gc_state_r4 s = [] /\
     gen_gc_partial_conf_limit gen_conf = heap_length (gc_state_heap s) /\
     heap_length (gc_state_heap s) <= dimword (:A) DIV 2 EXP shift_length conf /\
     gen_gc_partial_conf_gen_start gen_conf <= gen_gc_partial_conf_refs_start gen_conf /\
     gen_gc_partial_conf_refs_start gen_conf <= heap_length (gc_state_heap s) /\
     (heap_segment (gen_gc_partial_conf_gen_start gen_conf,
                    gen_gc_partial_conf_refs_start gen_conf) (gc_state_heap s) =
        SOME (old,current,refs)) /\
     (!t r. (gen_gc_partial_conf_isRef gen_conf (t,r) <=> isMutTag t)) /\
     heap_length (gc_state_heap s) * (dimindex (:A) DIV 8) < dimword (:A) /\
     (word_heap (word_add curr (word_mul bytes_in_word (word (heap_length old))))
        current conf STAR misc_word_list pa xs STAR
      misc_word_list k (MAP (word_addr conf) x) STAR frame) (fun2set (m,dm)) /\
     (word_gen_gc_partial_move_list conf
        (k,word (LENGTH x),word (gc_state_a s),pa,curr:A word,m,dm,
         word_mul bytes_in_word (word (gen_gc_partial_conf_gen_start gen_conf)),
         word_mul bytes_in_word (word (gen_gc_partial_conf_refs_start gen_conf))) =
       (k1,i1,pa1,m1,c1)) /\
     LENGTH xs = gc_state_n s /\ good_dimindex (:A) /\ LENGTH x < dimword (:A) ==>
     ?xs1 current1.
       (word_heap (word_add curr (word_mul bytes_in_word (word (heap_length old))))
          current1 conf STAR
        word_heap pa (gc_state_h2 s1) conf STAR
        misc_word_list pa1 xs1 STAR
        misc_word_list k (MAP (word_addr conf) x1) STAR
        frame) (fun2set (m1,dm)) /\
       heap_length (gc_state_heap s1) = heap_length (gc_state_heap s) /\
       (heap_segment (gen_gc_partial_conf_gen_start gen_conf,
                      gen_gc_partial_conf_refs_start gen_conf) (gc_state_heap s1) =
          SOME (old,current1,refs)) /\
       c1 /\ (i1 = word (gc_state_a s1)) /\ gc_state_n s1 = LENGTH xs1 /\
       gc_state_n s =
         heap_length (gc_state_h2 s1) + gc_state_n s1 + heap_length (gc_state_r4 s1) /\
       k1 = word_add k (word_mul (word (LENGTH x)) bytes_in_word) /\
       pa1 = word_add pa (word_mul bytes_in_word (word (heap_length (gc_state_h2 s1))))`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[gen_gc_partial_gc_move_list_def; MAP; LENGTH; PAIR_EQ] THEN
    ONCE_REWRITE_TAC[word_gen_gc_partial_move_list_def] THEN REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`xs:(A word_loc)list`; `current:((A word_loc,
       data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
    ASM_REWRITE_TAC[word_heap_def; SEP_CLAUSES; heap_length_NIL; ADD_CLAUSES; MAP;
                    misc_word_list_def; WORD_MUL_0; WORD_ADD_0] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[misc_word_list_def; SEP_CLAUSES]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `SUC (LENGTH (t:((A word_loc)heap_address)list)) < dimword(:A)` THENL
   [ALL_TAC; ASM_REWRITE_TAC[LENGTH]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LBIGAUX_WORD_SUC_NZ) THEN
  ASM_REWRITE_TAC[gen_gc_partial_gc_move_list_def; MAP; LENGTH; misc_word_list_def;
                  word_gen_gc_partial_move_list_suc] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  gcp2aux_tuple_tac "gen_gc_partial_gc_move" ["h1";"s2"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  gcp2aux_tuple_tac "gen_gc_partial_gc_move_list" ["t1";"s3"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  gcp2aux_tuple_tac "word_gen_gc_partial_move" ["w2";"i2";"pa2";"m2";"c2"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  gcp2aux_tuple_tac "word_gen_gc_partial_move_list" ["k3";"i3";"pa3";"m3";"c3"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(fun th -> let th1 = gcp2aux_sep_read `k:A word` th in
    ASSUME_TAC (CONJUNCT2 th1) THEN RULE_ASSUM_TAC(REWRITE_RULE[CONJUNCT1 th1])) THEN
  SUBGOAL_THEN `gc_state_ok (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                  gc_state)` ASSUME_TAC THENL
   [ASM_MESON_TAC[gc_partial_move_list_ok_before]; ALL_TAC] THEN
  MP_TAC(ISPECL [`gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf`;
    `s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `h:(A word_loc)heap_address`; `h1:(A word_loc)heap_address`;
    `s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `conf:data_to_word_config`; `curr:A word`;
    `old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `current:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `pa:A word`; `xs:(A word_loc)list`;
    `set_sep_one (k:A word,word_addr conf (h:(A word_loc)heap_address)) STAR
     misc_word_list (word_add k bytes_in_word) (MAP (word_addr conf) t) STAR
     (frame:(A word#A word_loc->bool)->bool)`;
    `m:A word->A word_loc`; `dm:A word->bool`; `w2:A word_loc`; `i2:A word`;
    `pa2:A word`; `m2:A word->A word_loc`; `c2:bool`] word_gen_gc_partial_move_thm) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [gcp2aux_sep_ac_tac; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs2:(A word_loc)list` (X_CHOOSE_THEN
    `current2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_comb(concl th) &&
     rand(concl th) = `fun2set (m2:A word->A word_loc,dm)`
   then ASSUME_TAC(gcp2aux_sep_write `k:A word`
          `word_addr conf (h1:(A word_loc)heap_address)` th) else failwith "") THEN
  MP_TAC(ISPECL [`t:((A word_loc)heap_address)list`;
    `s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `t1:((A word_loc)heap_address)list`;
    `s1:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf`]
    gc_partial_move_list_with_NIL) THEN
  ASM_REWRITE_TAC[] THEN
  gcp2aux_tuple_tac "gen_gc_partial_gc_move_list" ["t4";"s4"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`xs2:(A word_loc)list`; `t1:((A word_loc)heap_address)list`;
    `s4:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `gc_state_h2_fupd (K []) (gc_state_r4_fupd (K [])
       (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))`;
    `pa1:A word`;
    `word_add pa (word_mul bytes_in_word (word (heap_length (gc_state_h2
       (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))))):A word`;
    `m1:A word->A word_loc`;
    `((k:A word) =+ word_addr conf (h1:(A word_loc)heap_address)) (m2:A word->A word_loc)`;
    `i1:A word`;
    `word_heap pa (gc_state_h2
       (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) conf STAR
     set_sep_one (k:A word,word_addr conf (h1:(A word_loc)heap_address)) STAR
     (frame:(A word#A word_loc->bool)->bool)`;
    `dm:A word->bool`; `curr:A word`; `c3:bool`; `word_add (k:A word) bytes_in_word`;
    `old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `current2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf`;
    `conf:data_to_word_config`; `k1:A word`]) THEN
  ASM_REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [gcp2aux_sep_ac_tac;
      UNDISCH_TAC `SUC (LENGTH (t:((A word_loc)heap_address)list)) < dimword(:A)` THEN
      ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs3:(A word_loc)list` (X_CHOOSE_THEN
    `current3:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`xs3:(A word_loc)list`; `current3:((A word_loc,
     data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
  ASM_REWRITE_TAC[MAP; misc_word_list_def; heap_length_APPEND] THEN
  REWRITE_TAC[word_heap_APPEND] THEN
  REPEAT CONJ_TAC THENL
   [gcp2aux_sep_ac_tac;
    ARITH_TAC;
    REWRITE_TAC[ADD1; GSYM word_add_n2w] THEN CONV_TAC WORD_RULE;
    REWRITE_TAC[GSYM word_add_n2w] THEN CONV_TAC WORD_RULE]);;

(* HOL4 line 3140 *)
let gc_partial_move_heap_lengths = prove
 (`!gen_conf (s:(A,B)gc_state) x x1 s1.
     gen_gc_partial_gc_move gen_conf s x = (x1,s1) /\ gc_state_ok s1 ==>
     gc_state_n s + heap_length (gc_state_h2 s) =
     gc_state_n s1 + heap_length (gc_state_h2 s1)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN CASES_ON `x:A heap_address` THEN
  REWRITE_TAC[gen_gc_partial_gc_move_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THENL
   [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[gc_state_FIELDS.ri_accfupds];
    ALL_TAC] THEN
  CASES_ON `heap_lookup a0 (gc_state_heap (s:(A,B)gc_state))` THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
    FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`));
    ALL_TAC] THEN
  CASES_ON `a:(A,B)heap_element` THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
    FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`));
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  SUBGOAL_THEN `a1' + 1 <= gc_state_n (s:(A,B)gc_state)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP gc_shared_gc_forward_ptr_ok) THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; heap_length_NIL; el_length_def] THEN
  ASM_ARITH_TAC);;

(* HOL4 line 3163 *)
let gc_partial_move_list_heap_lengths = prove
 (`!x gen_conf (s:(A,B)gc_state) x1 s1.
     gen_gc_partial_gc_move_list gen_conf s x = (x1,s1) /\ gc_state_ok s1 ==>
     gc_state_n s + heap_length (gc_state_h2 s) =
     gc_state_n s1 + heap_length (gc_state_h2 s1)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[gen_gc_partial_gc_move_list_def] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  PAIRARG_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `gc_state_ok (state':(A,B)gc_state)` ASSUME_TAC THENL
   [ASM_MESON_TAC[gc_partial_move_list_ok_before]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `gc_state_n (state':(A,B)gc_state) + heap_length (gc_state_h2 state')` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[gc_partial_move_heap_lengths]; ASM_MESON_TAC[]]);;

(* HOL4 line 3174 *)
let partial_len_inv_def = cake_def
  `partial_len_inv (s:(A,B)gc_state) <=>
     heap_length (gc_state_heap s) =
     heap_length (APPEND (gc_state_h1 s) (gc_state_h2 s)) + gc_state_n s +
     heap_length (APPEND (APPEND (APPEND (APPEND (gc_state_r4 s) (gc_state_r3 s))
                                         (gc_state_r2 s)) (gc_state_r1 s))
                         (gc_state_old s))`;;

let gcp2aux_hl5_tac : tactic =
  REWRITE_TAC[GSYM(ASSUME `heap_length (gc_state_heap (s:(A word_loc,
    data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) =
    heap_length (gc_state_heap (s5:(A word_loc,
    data_to_word_memoryProof_tag#(A word_loc)list)gc_state))`)] THEN ASM_REWRITE_TAC[];;

(* HOL4 line 3180 *)
let word_gen_gc_partial_move_data_thm = prove
 (`!k s m dm curr xs s1 pa1 m1 i1 frame c1 old current refs gen_conf conf p.
     (gen_gc_partial_gc_move_data gen_conf s = s1) /\ gc_state_ok s1 /\
     gen_gc_partial_conf_limit gen_conf = heap_length (gc_state_heap s) /\
     heap_length (gc_state_heap s) <= dimword (:A) DIV 2 EXP shift_length conf /\
     heap_length (gc_state_heap s) * (dimindex (:A) DIV 8) < dimword (:A) /\
     gen_gc_partial_conf_gen_start gen_conf <= gen_gc_partial_conf_refs_start gen_conf /\
     gen_gc_partial_conf_refs_start gen_conf <= heap_length (gc_state_heap s) /\
     (heap_segment (gen_gc_partial_conf_gen_start gen_conf,
                    gen_gc_partial_conf_refs_start gen_conf) (gc_state_heap s) =
        SOME (old,current,refs)) /\
     data_to_word_config_len_size conf + 2 < dimindex (:A) /\
     (!t r. (gen_gc_partial_conf_isRef gen_conf (t,r) <=> isMutTag t)) /\
     (word_gen_gc_partial_move_data conf k
        (word_add p (word_mul bytes_in_word (word (heap_length (gc_state_h1 s)))),
         word (gc_state_a s),
         word_add p (word_mul bytes_in_word
           (word (heap_length (APPEND (gc_state_h1 s) (gc_state_h2 s))))),
         curr:A word,m,dm,
         word_mul bytes_in_word (word (gen_gc_partial_conf_gen_start gen_conf)),
         word_mul bytes_in_word (word (gen_gc_partial_conf_refs_start gen_conf))) =
       (i1,pa1,m1,c1)) /\
     heap_length (gc_state_h2 s) + gc_state_n s <= k /\ partial_len_inv s /\
     (word_heap (word_add curr (word_mul bytes_in_word (word (heap_length old))))
        current conf STAR
      word_heap p (APPEND (gc_state_h1 s) (gc_state_h2 s)) conf STAR
      misc_word_list (word_add p (word_mul bytes_in_word
        (word (heap_length (APPEND (gc_state_h1 s) (gc_state_h2 s)))))) xs STAR
      frame) (fun2set (m,dm)) /\
     ALL (is_Ref (gen_gc_partial_conf_isRef gen_conf))
       (APPEND (APPEND (APPEND (gc_state_r4 s) (gc_state_r3 s)) (gc_state_r2 s))
          (gc_state_r1 s)) /\
     LENGTH xs = gc_state_n s /\ good_dimindex (:A) ==>
     ?xs1 current1.
       (word_heap (word_add curr (word_mul bytes_in_word (word (heap_length old))))
          current1 conf STAR
        word_heap p (APPEND (gc_state_h1 s1) (gc_state_h2 s1)) conf STAR
        misc_word_list (word_add p (word_mul bytes_in_word
          (word (heap_length (APPEND (gc_state_h1 s1) (gc_state_h2 s1)))))) xs1 STAR
        frame) (fun2set (m1,dm)) /\ gc_state_h2 s1 = [] /\
       heap_length (gc_state_heap s1) = heap_length (gc_state_heap s) /\
       (heap_segment (gen_gc_partial_conf_gen_start gen_conf,
                      gen_gc_partial_conf_refs_start gen_conf) (gc_state_heap s1) =
          SOME (old,current1,refs)) /\
       c1 /\ (i1 = word (gc_state_a s1)) /\
       gc_state_n s1 = LENGTH xs1 /\ partial_len_inv s1 /\
       heap_length (APPEND (APPEND (gc_state_h1 s1) (gc_state_h2 s1)) (gc_state_r4 s1)) +
         gc_state_n s1 =
       heap_length (APPEND (APPEND (gc_state_h1 s) (gc_state_h2 s)) (gc_state_r4 s)) +
         gc_state_n s /\
       pa1 = word_add p (word_mul bytes_in_word
               (word (heap_length (APPEND (gc_state_h1 s1) (gc_state_h2 s1))))) /\
       ALL (is_Ref (gen_gc_partial_conf_isRef gen_conf))
         (APPEND (APPEND (APPEND (gc_state_r4 s1) (gc_state_r3 s1)) (gc_state_r2 s1))
            (gc_state_r1 s1))`,
  INDUCT_TAC THEN (REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `gc_state_h2 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                   gc_state) = []` THENL
   [gcp2aux_undisch_app "gen_gc_partial_gc_move_data" THEN
    ONCE_REWRITE_TAC[gen_gc_partial_gc_move_data_def] THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `gc_state_h2 (s:(A word_loc,
        data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`
      then RULE_ASSUM_TAC(REWRITE_RULE[th; APPEND_NIL]) THEN REWRITE_TAC[th; APPEND_NIL] THEN
           ASSUME_TAC th else NO_TAC) THEN
    CASE_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    gcp2aux_undisch_app "word_gen_gc_partial_move_data" THEN
    ONCE_REWRITE_TAC[word_gen_gc_partial_move_data_def] THEN
    ASM_REWRITE_TAC[APPEND_NIL; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`xs:(A word_loc)list`; `current:((A word_loc,
       data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
    ASM_REWRITE_TAC[APPEND_NIL];
    ALL_TAC] THEN
  MP_TAC(ISPEC `gc_state_h2 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                  gc_state)` list_CASES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
    heap_element` (X_CHOOSE_THEN `t:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
    heap_element)list` ASSUME_TAC))) THENL
   [(* k = 0: the gray heap is not empty *)
    UNDISCH_TAC `heap_length (gc_state_h2 (s:(A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) + gc_state_n s <= 0` THEN
    ASM_REWRITE_TAC[heap_length_CONS] THEN
    MP_TAC(ISPEC `h:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element`
      el_length_GT_0) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(heap_length (gc_state_heap (s:(A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)gc_state)) <
      heap_length (APPEND (gc_state_h1 s) (gc_state_h2 s)))` ASSUME_TAC THENL
   [UNDISCH_TAC `partial_len_inv (s:(A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)gc_state)` THEN
    ASM_REWRITE_TAC[partial_len_inv_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  gcp2aux_undisch_app "gen_gc_partial_gc_move_data" THEN
  ONCE_REWRITE_TAC[gen_gc_partial_gc_move_data_def] THEN
  gcp2aux_rw_asm_tac `gc_state_h2 (s:(A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)gc_state)` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `h:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element` THEN
  CASE_REWRITE_TAC[] THENL [gcp2aux_ok_F_tac; gcp2aux_ok_F_tac; ALL_TAC] THEN
  (* a data element: the gc side *)
  MP_TAC(ISPEC `a2:data_to_word_memoryProof_tag#(A word_loc)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tag:data_to_word_memoryProof_tag` (X_CHOOSE_THEN
    `qs:(A word_loc)list` SUBST_ALL_TAC)) THEN
  gcp2aux_tuple_tac "gen_gc_partial_gc_move_list" ["ys1";"s3"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  gcp2aux_abbrev_arg_tac "s4" THEN DISCH_TAC THEN
  SUBGOAL_THEN `gc_state_ok (s4:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                 gc_state)` MP_TAC THENL
   [MATCH_MP_TAC gc_partial_move_data_ok_before THEN
    MAP_EVERY EXISTS_TAC [`gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)
      gen_gc_partial_conf`; `s1:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      gc_state`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "s4" THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a0:((A word_loc)heap_address)list`;
    `s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `ys1:((A word_loc)heap_address)list`;
    `s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf`]
    gc_partial_move_list_with_NIL) THEN
  ASM_REWRITE_TAC[] THEN
  gcp2aux_tuple_tac "gen_gc_partial_gc_move_list" ["ys5";"s5"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "gen_gc_partial_gc_move_list" th &&
      gcp2aux_has_const "gc_state_h2_fupd" (lhs(concl th)) then
    MP_TAC(MATCH_MP gen_gc_partial_gc_move_list_IMP th) THEN
    MP_TAC(MATCH_MP gen_gc_partial_gc_move_list_heap_length th) else NO_TAC) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN REPEAT STRIP_TAC THEN
  (* the word side: the scan pointer is not at the end *)
  gcp2aux_undisch_app "word_gen_gc_partial_move_data" THEN
  ONCE_REWRITE_TAC[word_gen_gc_partial_move_data_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN
  SUBGOAL_THEN `heap_length (APPEND (gc_state_h1 (s:(A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)gc_state)) (CONS (DataElement a0 a1 (tag,qs)) t)) <=
      heap_length (gc_state_heap s)` ASSUME_TAC THENL
   [UNDISCH_TAC `partial_len_inv (s:(A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)gc_state)` THEN
    ASM_REWRITE_TAC[partial_len_inv_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(word_add p (word_mul bytes_in_word (word (heap_length (gc_state_h1
      (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))))) =
     word_add (p:A word) (word_mul bytes_in_word (word (heap_length (APPEND (gc_state_h1 s)
       (CONS (DataElement a0 a1 (tag,qs)) t))))))` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC GCP2AUX_word_offset_ne THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[heap_length_APPEND; heap_length_CONS; el_length_def] THEN ARITH_TAC;
      MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `heap_length (gc_state_heap (s:(A word_loc,data_to_word_memoryProof_tag#
        (A word_loc)list)gc_state)) * dimindex(:A) DIV 8` THEN
      ASM_REWRITE_TAC[LE_MULT_RCANCEL]];
    ALL_TAC] THEN
  (* the header of the element in memory *)
  FIRST_ASSUM(fun th -> if is_comb(concl th) &&
      rand(concl th) = `fun2set (m:A word->A word_loc,dm)` &&
      gcp2aux_has_const "APPEND" (concl th)
    then ASSUME_TAC(REWRITE_RULE[word_heap_APPEND; word_heap_def; word_el_def] th)
    else NO_TAC) THEN
  gcp2aux_tuple_tac "word_payload" ["hd";"ts";"cc"] THEN
  gcp2aux_rw_asm_tac `word_payload a0 a1 tag qs conf:A word#(A word_loc)list#bool` THEN
  RULE_ASSUM_TAC(CONV_RULE(CASE_REWRITE_CONV[])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[misc_word_list_def]) THEN
  FIRST_X_ASSUM(fun th -> STRIP_ASSUME_TAC(gcp2aux_sep_cond th)) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  FIRST_ASSUM(fun th -> let th1 = gcp2aux_sep_read `word_add p (word_mul bytes_in_word
      (word (heap_length (gc_state_h1 (s:(A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)gc_state))))):A word` th in
    REWRITE_TAC[th1; isWord_def; theWord_def] THEN ASSUME_TAC th1) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && gcp2aux_is_app_eq "decode_length" th
    then REWRITE_TAC[th] else NO_TAC) THEN
  MP_TAC(ISPECL [`a0:((A word_loc)heap_address)list`; `a1:num`;
    `tag:data_to_word_memoryProof_tag`; `qs:(A word_loc)list`; `conf:data_to_word_config`;
    `hd:A word`; `ts:(A word_loc)list`] word_payload_T_IMP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `bit 2 (hd:A word)` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THENL
   [(* no pointers in the element: skip it *)
    RVEQ_TAC THEN
    FIRST_X_ASSUM(fun th -> if gcp2aux_is_app_eq "gen_gc_partial_gc_move_list" th &&
        gcp2aux_has_const "gc_state_h2_fupd" (lhs(concl th)) then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[gen_gc_partial_gc_move_list_def; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    gcp2aux_tuple_tac "word_gen_gc_partial_move_data" ["i2";"pa2";"m2";"c2"] THEN
    FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "word_gen_gc_partial_move_data" th
      then REWRITE_TAC[th] else NO_TAC) THEN
    CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
    REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
    REWRITE_TAC[APPEND_NIL; APPEND; TL; HD; NOT_CONS_NIL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL; APPEND; TL; HD; NOT_CONS_NIL]) THEN
    (fun (asl,w as g) ->
      let tm = gcp2aux_find_app "gen_gc_partial_gc_move_data" w in
      FIRST_X_ASSUM(MP_TAC o ISPECL [rand tm; `m:A word->A word_loc`; `dm:A word->bool`;
        `curr:A word`; `xs:(A word_loc)list`; tm; `pa1:A word`; `m1:A word->A word_loc`;
        `i1:A word`; `frame:(A word#A word_loc->bool)->bool`; `c1:bool`;
        `old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `current:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf`;
        `conf:data_to_word_config`; `p:A word`]) g) THEN
    REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [gcp2aux_same_app_tac "word_gen_gc_partial_move_data" THEN
        REWRITE_TAC gcp2aux_hl_rw THEN REWRITE_TAC[GSYM word_add_n2w; ADD_ASSOC] THEN
        CONV_TAC WORD_RULE;
        FIRST_X_ASSUM(MP_TAC o check (fun th -> gcp2aux_has_const "SUC" (concl th))) THEN
        REWRITE_TAC gcp2aux_hl_rw THEN ARITH_TAC;
        UNDISCH_TAC `partial_len_inv (s:(A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)gc_state)` THEN
        ASM_REWRITE_TAC([partial_len_inv_def; gc_state_FIELDS.ri_accfupds; K_THM] @
                        gcp2aux_hl_rw) THEN ARITH_TAC;
        REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN gcp2aux_sep_ac_tac];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `xs1:(A word_loc)list` (X_CHOOSE_THEN
      `current1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`xs1:(A word_loc)list`; `current1:((A word_loc,
       data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC gcp2aux_hl_rw THEN ARITH_TAC;
    ALL_TAC] THEN
  (* pointers in the element: move them, then the rest *)
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN REWRITE_TAC[LENGTH_MAP] THEN
  gcp2aux_tuple_tac "word_gen_gc_partial_move_list" ["h2a3";"i3";"pa3";"m3";"c3"] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "word_gen_gc_partial_move_list" th
    then REWRITE_TAC[th] else NO_TAC) THEN
  CASE_REWRITE_TAC[] THEN
  gcp2aux_tuple_tac "word_gen_gc_partial_move_data" ["i4";"pa4";"m4";"c4"] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "word_gen_gc_partial_move_data" th
    then REWRITE_TAC[th] else NO_TAC) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `heap_length (gc_state_heap (s:(A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)gc_state)) < dimword(:A)` ASSUME_TAC THENL
   [MATCH_MP_TAC GCP2AUX_LT_DIMWORD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (a0:((A word_loc)heap_address)list) < dimword(:A)` ASSUME_TAC THENL
   [UNDISCH_TAC `heap_length (gc_state_heap (s:(A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)gc_state)) < dimword(:A)` THEN
    UNDISCH_TAC `heap_length (APPEND (gc_state_h1 (s:(A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)gc_state))
      (CONS (DataElement a0 (LENGTH (a0:((A word_loc)heap_address)list)) (tag,qs)) t)) <=
      heap_length (gc_state_heap s)` THEN
    REWRITE_TAC gcp2aux_hl_rw THEN ARITH_TAC;
    ALL_TAC] THEN
  (fun (asl,w as g) ->
    let th = snd(find (fun (_,th) -> gcp2aux_is_app_eq "word_gen_gc_partial_move_list" th)
                      asl) in
    let comps = gcp2aux_strip_pair (rand(lhs(concl th))) in
    let k0 = el 0 comps and pa0 = el 3 comps in
    let h2a = lhand k0 in
    let frame' = vsubst [h2a, `h2a:A word`]
     `word_heap p (gc_state_h1 (s:(A word_loc,data_to_word_memoryProof_tag#
        (A word_loc)list)gc_state)) conf STAR
      set_sep_one (h2a:A word, wl_Word (hd:A word)) STAR
      word_heap (word_add h2a (word_mul bytes_in_word (word (el_length
        (DataElement (a0:((A word_loc)heap_address)list) (LENGTH a0)
          (tag:data_to_word_memoryProof_tag,qs:(A word_loc)list))))))
        (t:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
        conf STAR
      (frame:(A word#A word_loc->bool)->bool)` in
    MP_TAC(ISPECL [`a0:((A word_loc)heap_address)list`; `xs:(A word_loc)list`;
      `ys1:((A word_loc)heap_address)list`;
      `s5:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
      `gc_state_h2_fupd (K []) (gc_state_r4_fupd (K [])
         (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))`;
      `pa3:A word`; pa0; `m3:A word->A word_loc`; `m:A word->A word_loc`; `i3:A word`;
      frame'; `dm:A word->bool`; `curr:A word`; `c3:bool`; k0;
      `old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `current:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf`;
      `conf:data_to_word_config`; `h2a3:A word`] word_gen_gc_partial_move_list_thm) g) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
  gcp2aux_rw_asm_tac `LENGTH (a0:((A word_loc)heap_address)list)` THEN
  ANTS_TAC THENL [gcp2aux_sep_ac_tac; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs2:(A word_loc)list` (X_CHOOSE_THEN
    `current2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  MP_TAC(ISPECL [`a0:((A word_loc)heap_address)list`; `tag:data_to_word_memoryProof_tag`;
    `qs:(A word_loc)list`; `conf:data_to_word_config`; `hd:A word`;
    `ys1:((A word_loc)heap_address)list`] word_payload_swap) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  REWRITE_TAC[APPEND; TL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[APPEND; TL; HD; NOT_CONS_NIL; heap_length_NIL; ADD_CLAUSES]) THEN
  gcp2aux_rw_asm_tac `gc_state_h1 (s5:(A word_loc,data_to_word_memoryProof_tag#
     (A word_loc)list)gc_state)` THEN
  gcp2aux_rw_asm_tac `gc_state_r4 (s5:(A word_loc,data_to_word_memoryProof_tag#
     (A word_loc)list)gc_state)` THEN
  FIRST_ASSUM(fun th -> if concl th = `gc_state_ok (s5:(A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN ASSUME_TAC th
    else NO_TAC) THEN
  REWRITE_TAC[APPEND] THEN
  (fun (asl,w as g) ->
    let tm = gcp2aux_find_app "gen_gc_partial_gc_move_data" w in
    FIRST_X_ASSUM(MP_TAC o ISPECL [rand tm; `m3:A word->A word_loc`; `dm:A word->bool`;
      `curr:A word`; `xs2:(A word_loc)list`; tm; `pa1:A word`; `m1:A word->A word_loc`;
      `i1:A word`; `frame:(A word#A word_loc->bool)->bool`; `c4:bool`;
      `old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `current2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf`;
      `conf:data_to_word_config`; `p:A word`]) g) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[APPEND]) THEN ASM_REWRITE_TAC[];
      gcp2aux_hl5_tac;
      gcp2aux_hl5_tac;
      gcp2aux_hl5_tac;
      gcp2aux_same_app_tac "word_gen_gc_partial_move_data" THEN CONJ_TAC THEN
      gcp2aux_addr_tac;
      gcp2aux_arith_tac;
      REWRITE_TAC[partial_len_inv_def; gc_state_FIELDS.ri_accfupds; K_THM] THEN
      UNDISCH_TAC `partial_len_inv (s:(A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)gc_state)` THEN
      ASM_REWRITE_TAC[partial_len_inv_def] THEN gcp2aux_hl5_tac THEN gcp2aux_arith_tac;
      gcp2aux_rw_asm_tac `LENGTH (a0:((A word_loc)heap_address)list)` THEN
      REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; word_heap_APPEND; word_heap_def;
                  word_el_def] THEN
      (fun (asl,w as g) -> REWRITE_TAC (map snd (filter (fun (_,th) ->
         gcp2aux_is_app_eq "word_payload" th) asl)) g) THEN
      CASE_REWRITE_TAC[] THEN REWRITE_TAC[misc_word_list_def; LENGTH_MAP] THEN
      (fun (asl,w as g) -> REWRITE_TAC (map snd (filter (fun (_,th) ->
         gcp2aux_is_app_eq "decode_length" th ||
         (is_comb (concl th) && gcp2aux_has_const "EXP" (concl th) &&
          gcp2aux_has_const "LENGTH" (concl th))) asl)) g) THEN
      REWRITE_TAC[SEP_CLAUSES] THEN
      gcp2aux_sep_addr_tac gcp2aux_addr_tac];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs1:(A word_loc)list` (X_CHOOSE_THEN
    `current1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`xs1:(A word_loc)list`; `current1:((A word_loc,
     data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC gcp2aux_hl_rw THEN ARITH_TAC);;

(* HOL4 line 3394 *)
let word_gen_gc_partial_move_ref_list_thm = prove
 (`!x ck xs x1 s1 s pa1 pa m1 m i1 frame dm curr c1 k old current refs gen_conf conf.
     (gc_move_ref_list gen_conf s x = (x1,s1)) /\ gc_state_ok s1 /\
     gc_state_h2 s = [] /\ gc_state_r4 s = [] /\
     heap_length x <= ck /\
     gen_gc_partial_conf_limit gen_conf = heap_length (gc_state_heap s) /\
     heap_length (gc_state_heap s) <= dimword (:A) DIV 2 EXP shift_length conf /\
     gen_gc_partial_conf_gen_start gen_conf <= gen_gc_partial_conf_refs_start gen_conf /\
     gen_gc_partial_conf_refs_start gen_conf <= heap_length (gc_state_heap s) /\
     heap_segment (gen_gc_partial_conf_gen_start gen_conf,
                   gen_gc_partial_conf_refs_start gen_conf) (gc_state_heap s) =
       SOME (old,current,refs) /\
     heap_length x <= heap_length (gc_state_heap s) /\
     ALL isRef x /\
     (!t r. (gen_gc_partial_conf_isRef gen_conf (t,r) <=> isMutTag t)) /\
     heap_length (gc_state_heap s) * (dimindex (:A) DIV 8) < dimword (:A) /\
     (word_heap (word_add curr (word_mul bytes_in_word (word (heap_length old))))
        current conf STAR misc_word_list pa xs STAR
      word_heap k x conf STAR frame) (fun2set (m,dm)) /\
     (word_gen_gc_partial_move_ref_list ck conf
        (k,word (gc_state_a s),pa,curr:A word,m,dm,T,
         word_mul bytes_in_word (word (gen_gc_partial_conf_gen_start gen_conf)),
         word_mul bytes_in_word (word (gen_gc_partial_conf_refs_start gen_conf)),
         word_add k (word_mul bytes_in_word (word (heap_length x)))) =
       (i1,pa1,m1,c1)) /\
     LENGTH xs = gc_state_n s /\ good_dimindex (:A) /\ LENGTH x < dimword (:A) ==>
     ?xs1 current1.
       (word_heap (word_add curr (word_mul bytes_in_word (word (heap_length old))))
          current1 conf STAR
        word_heap pa (gc_state_h2 s1) conf STAR
        misc_word_list pa1 xs1 STAR
        word_heap k x1 conf STAR
        frame) (fun2set (m1,dm)) /\
       heap_segment (gen_gc_partial_conf_gen_start gen_conf,
                     gen_gc_partial_conf_refs_start gen_conf) (gc_state_heap s1) =
         SOME (old,current1,refs) /\
       heap_length (gc_state_heap s1) = heap_length (gc_state_heap s) /\
       c1 /\ (i1 = word (gc_state_a s1)) /\ gc_state_n s1 = LENGTH xs1 /\
       ALL isRef x1 /\
       gc_state_n s =
         heap_length (gc_state_h2 s1) + gc_state_n s1 + heap_length (gc_state_r4 s1) /\
       pa1 = word_add pa (word_mul bytes_in_word (word (heap_length (gc_state_h2 s1))))`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THEN
    ONCE_REWRITE_TAC[word_gen_gc_partial_move_ref_list_def] THEN
    REWRITE_TAC[heap_length_NIL; WORD_MUL_0; WORD_ADD_0; PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`xs:(A word_loc)list`; `current:((A word_loc,
       data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[word_heap_def; SEP_CLAUSES]) THEN
    ASM_REWRITE_TAC[word_heap_def; SEP_CLAUSES; heap_length_NIL; ADD_CLAUSES; ALL;
                    WORD_MUL_0; WORD_ADD_0];
    ALL_TAC] THEN
  CASES_ON `h:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element` THEN
  REWRITE_TAC[ALL; isRef_def] THEN
  MP_TAC(ISPEC `a2:data_to_word_memoryProof_tag#(A word_loc)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tag:data_to_word_memoryProof_tag` (X_CHOOSE_THEN
    `qs:(A word_loc)list` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[isRef_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[gc_move_ref_list_def] THEN
  gcp2aux_tuple_tac "gen_gc_partial_gc_move_list" ["ptrs1";"s2"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  gcp2aux_tuple_tac "gc_move_ref_list" ["t1";"s3"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  (* the word side: not at the end of the list, enough fuel *)
  SUBGOAL_THEN `~((k:A word) = word_add k (word_mul bytes_in_word (word (heap_length
     (CONS (DataElement (a0:((A word_loc)heap_address)list) a1 (tag,qs:(A word_loc)list))
       (t:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))))))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC GCP2AUX_word_offset_ne0 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC gcp2aux_hl_rw THEN ARITH_TAC;
      MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `heap_length (gc_state_heap (s:(A word_loc,data_to_word_memoryProof_tag#
        (A word_loc)list)gc_state)) * dimindex(:A) DIV 8` THEN
      ASM_REWRITE_TAC[LE_MULT_RCANCEL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(ck = 0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
      (try rand(concl th) = `ck:num` with Failure _ -> false))) THEN
    REWRITE_TAC gcp2aux_hl_rw THEN ARITH_TAC;
    ALL_TAC] THEN
  gcp2aux_undisch_app "word_gen_gc_partial_move_ref_list" THEN
  ONCE_REWRITE_TAC[word_gen_gc_partial_move_ref_list_def] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  (* the header of the reference in memory *)
  FIRST_ASSUM(fun th -> if is_comb(concl th) &&
      rand(concl th) = `fun2set (m:A word->A word_loc,dm)` &&
      gcp2aux_has_const "DataElement" (concl th)
    then ASSUME_TAC(REWRITE_RULE[word_heap_def; word_el_def] th)
    else NO_TAC) THEN
  gcp2aux_tuple_tac "word_payload" ["hd";"ts";"cc"] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "word_payload" th then
    MP_TAC(MATCH_MP isMutTag_word_payload_IMP (CONJ th
      (ASSUME `isMutTag (tag:data_to_word_memoryProof_tag)`))) else NO_TAC) THEN
  STRIP_TAC THEN
  gcp2aux_rw_asm_tac `word_payload a0 a1 tag qs conf:A word#(A word_loc)list#bool` THEN
  RULE_ASSUM_TAC(CONV_RULE(CASE_REWRITE_CONV[])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[misc_word_list_def]) THEN
  FIRST_X_ASSUM(fun th -> STRIP_ASSUME_TAC(gcp2aux_sep_cond th)) THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(fun th -> let th1 = gcp2aux_sep_read `k:A word` th in
    REWRITE_TAC[th1; isWord_def; theWord_def] THEN ASSUME_TAC th1) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && gcp2aux_is_app_eq "decode_length" th
    then REWRITE_TAC[th] else NO_TAC) THEN
  REWRITE_TAC[LENGTH_MAP] THEN
  FIRST_X_ASSUM(fun th -> if is_conj(concl th) && gcp2aux_has_const "RefTag" (concl th) &&
      not (gcp2aux_has_const "word_payload" (concl th)) then STRIP_ASSUME_TAC th
    else NO_TAC) THEN
  RVEQ_TAC THEN
  gcp2aux_tuple_tac "word_gen_gc_partial_move_list" ["pb2";"i2";"pa2";"m2";"c2"] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "word_gen_gc_partial_move_list" th
    then REWRITE_TAC[th] else NO_TAC) THEN
  CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the pointers of the reference *)
  FIRST_ASSUM(fun th1 -> if gcp2aux_is_app_eq "gc_move_ref_list" th1 then
     FIRST_ASSUM(fun th2 ->
       ASSUME_TAC(MATCH_MP gc_partial_move_ref_list_ok_before (CONJ th1 th2)))
   else NO_TAC) THEN
  SUBGOAL_THEN `heap_length (gc_state_heap (s:(A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)gc_state)) < dimword(:A)` ASSUME_TAC THENL
   [MATCH_MP_TAC GCP2AUX_LT_DIMWORD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (a0:((A word_loc)heap_address)list) < dimword(:A)` ASSUME_TAC THENL
   [gcp2aux_arith_tac; ALL_TAC] THEN
  MP_TAC(ISPECL [`a0:((A word_loc)heap_address)list`; `xs:(A word_loc)list`;
      `ptrs1:((A word_loc)heap_address)list`;
      `s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
      `s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
      `pa2:A word`; `pa:A word`; `m2:A word->A word_loc`; `m:A word->A word_loc`;
      `i2:A word`;
      `set_sep_one (k:A word,wl_Word (make_header conf
         (muttag_header (tag:data_to_word_memoryProof_tag))
         (LENGTH (a0:((A word_loc)heap_address)list)))) STAR
       word_heap (word_add k (word_mul bytes_in_word (word (el_length
         (DataElement a0 (LENGTH a0) (tag,[]:(A word_loc)list))))))
         (t:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
         conf STAR
       (frame:(A word#A word_loc->bool)->bool)`;
      `dm:A word->bool`; `curr:A word`; `c2:bool`; `word_add (k:A word) bytes_in_word`;
      `old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `current:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf`;
      `conf:data_to_word_config`; `pb2:A word`] word_gen_gc_partial_move_list_thm) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [gcp2aux_sep_ac_tac; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs2:(A word_loc)list` (X_CHOOSE_THEN
    `current2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(fun th -> if concl th = `c2:bool` then
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th else NO_TAC) THEN
  (* the rest of the references *)
  MP_TAC(ISPECL [`t:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      heap_element)list`;
    `s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `t1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `s1:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf`]
    gc_partial_move_ref_list_with_NIL) THEN
  ASM_REWRITE_TAC[] THEN
  gcp2aux_tuple_tac "gc_move_ref_list" ["t4";"s4"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
  (fun (asl,w as g) ->
    let th = snd(find (fun (_,th) -> gcp2aux_is_app_eq "word_gen_gc_partial_move_ref_list" th)
                      asl) in
    let comps = gcp2aux_strip_pair (rand(lhs(concl th))) in
    let k0 = el 0 comps and pa0 = el 2 comps in
    FIRST_X_ASSUM(MP_TAC o ISPECL [`ck - 1`; `xs2:(A word_loc)list`;
      `t1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `s4:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
      `gc_state_h2_fupd (K []) (gc_state_r4_fupd (K [])
         (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))`;
      `pa1:A word`; pa0; `m1:A word->A word_loc`; `m2:A word->A word_loc`; `i1:A word`;
      `word_heap pa (gc_state_h2 (s2:(A word_loc,data_to_word_memoryProof_tag#
         (A word_loc)list)gc_state)) conf STAR
       set_sep_one (k:A word,wl_Word (make_header conf
         (muttag_header (tag:data_to_word_memoryProof_tag))
         (LENGTH (a0:((A word_loc)heap_address)list)))) STAR
       misc_word_list (word_add k bytes_in_word)
         (MAP (word_addr conf) (ptrs1:((A word_loc)heap_address)list)) STAR
       (frame:(A word#A word_loc->bool)->bool)`;
      `dm:A word->bool`; `curr:A word`; `c1:bool`; k0;
      `old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `current2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf`;
      `conf:data_to_word_config`]) g) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [gcp2aux_arith_tac;
      gcp2aux_arith_tac;
      gcp2aux_sep_addr_tac gcp2aux_addr_tac;
      gcp2aux_same_app_tac "word_gen_gc_partial_move_ref_list" THEN gcp2aux_addr_tac;
      gcp2aux_arith_tac];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs3:(A word_loc)list` (X_CHOOSE_THEN
    `current3:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`xs3:(A word_loc)list`; `current3:((A word_loc,
     data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[ALL; isRef_def] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "gen_gc_partial_gc_move_list" th then
      ASSUME_TAC(CONJUNCT1(MATCH_MP gen_gc_partial_gc_move_list_IMP th)) else NO_TAC) THEN
    REWRITE_TAC[word_heap_APPEND; word_heap_def; word_el_def] THEN
    gcp2aux_tuple_tac "word_payload" ["hd1";"ts1";"cc1"] THEN
    FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "word_payload" th then
      MP_TAC(MATCH_MP isMutTag_word_payload_IMP (CONJ th
        (ASSUME `isMutTag (tag:data_to_word_memoryProof_tag)`))) else NO_TAC) THEN
    STRIP_TAC THEN
    FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "word_payload" th then
      REWRITE_TAC[th] else NO_TAC) THEN
    RVEQ_TAC THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[misc_word_list_def; LENGTH_MAP] THEN
    FIRST_ASSUM(fun th -> if concl th = `LENGTH (a0:((A word_loc)heap_address)list) =
      LENGTH (ptrs1:((A word_loc)heap_address)list)` then REWRITE_TAC[GSYM th]
      else NO_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN ASM_REWRITE_TAC[SEP_CLAUSES] THEN
    FIRST_ASSUM(fun th -> if concl th = `LENGTH (a0:((A word_loc)heap_address)list) =
      LENGTH (ptrs1:((A word_loc)heap_address)list)` then REWRITE_TAC[GSYM th]
      else NO_TAC) THEN
    gcp2aux_sep_addr_tac gcp2aux_addr_tac;
    REWRITE_TAC gcp2aux_hl_rw THEN ARITH_TAC;
    gcp2aux_addr_tac]);;

(* HOL4 line 3496 (local) *)
let data_to_word_gcProof_gc_move_ref_list_IMP = prove
 (`!conf (state:(A,B)gc_state) (refs:((A,C)heap_element)list) state1 refs1.
     (gc_move_ref_list conf state refs = (refs1,state1)) ==>
     (gc_state_old state1 = gc_state_old state) /\
     (gc_state_h1 state1 = gc_state_h1 state) /\
     (gc_state_r1 state1 = gc_state_r1 state) /\
     (gc_state_r2 state1 = gc_state_r2 state) /\
     (gc_state_r3 state1 = gc_state_r3 state) /\
     (gc_state_r4 state1 = gc_state_r4 state) /\
     (heap_length refs = heap_length refs1) /\
     (!ptr.
        isSomeDataElement (heap_lookup ptr refs) ==>
        isSomeDataElement (heap_lookup ptr refs1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP gen_gc_partial_gc_move_ref_list_IMP) THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST(MP_TAC o last) THEN
  SPEC_TAC(`refs1:((A,C)heap_element)list`,`refs1:((A,C)heap_element)list`) THEN
  SPEC_TAC(`state1:(A,B)gc_state`,`state1:(A,B)gc_state`) THEN
  SPEC_TAC(`refs:((A,C)heap_element)list`,`refs:((A,C)heap_element)list`) THEN
  SPEC_TAC(`state:(A,B)gc_state`,`state:(A,B)gc_state`) THEN
  SPEC_TAC(`conf:B gen_gc_partial_conf`,`conf:B gen_gc_partial_conf`) THEN
  MATCH_MP_TAC gc_move_ref_list_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC;
    REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[gc_state_FIELDS.ri_accfupds];
    REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[gc_state_FIELDS.ri_accfupds]] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[gc_move_ref_list_def] THEN PAIRARG_TAC THEN PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP gen_gc_partial_gc_move_list_IMP) THEN
  USE_THEN "IH" (MP_TAC o SPECL [`ptrs':(A heap_address)list`; `state':(A,B)gc_state`]) THEN
  REWRITE_TAC[] THEN DISCH_THEN(fun ih2 -> FIRST_ASSUM(MP_TAC o MATCH_MP ih2)) THEN
  SIMP_TAC[]);;

(* HOL4 line 3529 *)
let heap_length_LENGTH = prove
 (`!x:((A,B)heap_element)list. LENGTH x <= heap_length x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; heap_length_NIL; LE_REFL] THEN
  REWRITE_TAC[GC1AUX_heap_length_CONS] THEN
  MP_TAC(ISPEC `h:(A,B)heap_element` el_length_GT_0) THEN ASM_ARITH_TAC);;

(* HOL4 line 3536 *)
let partial_gc_move_ref_list_isRef = prove
 (`!refs (s:(A,B)gc_state) (refs':((A,B)heap_element)list) state' gen_conf.
     gc_move_ref_list gen_conf s refs = (refs',state') ==>
     ALL (is_Ref (gen_gc_partial_conf_isRef gen_conf)) refs' =
     ALL (is_Ref (gen_gc_partial_conf_isRef gen_conf)) refs`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `h:(A,B)heap_element` THEN REWRITE_TAC[gc_move_ref_list_def] THENL
   [REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  PAIRARG_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[ALL; is_Ref_def] THEN AP_TERM_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 3550 *)
let EVERY_is_Ref_isRef = prove
 (`!f (refs:((A,data_to_word_memoryProof_tag#B)heap_element)list).
     (!t r. f (t,r) <=> isMutTag t) ==> ALL (is_Ref f) refs = ALL isRef refs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> FIRST_ASSUM(SUBST1_TAC o MATCH_MP th)) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  CASES_ON `h:(A,data_to_word_memoryProof_tag#B)heap_element` THEN
  REWRITE_TAC[is_Ref_def; isRef_def] THEN
  SPEC_TAC(`a2:data_to_word_memoryProof_tag#B`,`p:data_to_word_memoryProof_tag#B`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; isRef_def] THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 3558 *)
let ends_with_refs_def = cake_def
  `ends_with_refs rs (heap:((A,data_to_word_memoryProof_tag#B)heap_element)list) <=>
     ?h1 h2. heap_split rs heap = SOME (h1,h2) /\ ALL isRef h2`;;

(* GCP2AUX: heap_segment_IMP_split, needed before its place in the script *)
let GCP2AUX_heap_segment_split = prove
 (`!m n (heap:((A,B)heap_element)list) x1 x2 x3.
     heap_segment (m,n) heap = SOME (x1,x2,x3) ==>
     heap_split m heap = SOME (x1,APPEND x2 x3) /\
     heap_split n heap = SOME (APPEND x1 x2,x3)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP heap_segment_IMP) THEN
  DISCH_THEN(fun th -> let ths = CONJUNCTS th in
     SUBST1_TAC(SYM(el 0 ths)) THEN SUBST1_TAC(SYM(el 1 ths)) THEN
     SUBST1_TAC(SYM(el 2 ths))) THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM APPEND_ASSOC]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[heap_split_APPEND_if] THEN
  REWRITE_TAC[LT_REFL; SUB_REFL; heap_split_0] THEN CASE_REWRITE_TAC[APPEND_NIL]);;

let gcp2aux_st3_rw = map (fun t -> ASSUME t)
  [`gc_state_h1 (st3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = []`;
   `gc_state_r4 (st3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = []`;
   `gc_state_r3 (st3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = []`;
   `gc_state_old (st3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) =
    old`];;

(* HOL4 line 3563 *)
let word_gen_gc_partial_thm = prove
 (`!m dm curr s1 pa1 m1 i1 frame c1 roots heap roots1 roots1' new gen_conf conf.
     (partial_gc gen_conf (roots,heap) = (roots1,s1)) /\ gc_state_ok s1 /\
     heap_length heap <= dimword (:A) DIV 2 EXP shift_length conf /\
     heap_length heap * (dimindex (:A) DIV 8) < dimword (:A) /\
     gen_gc_partial_conf_limit gen_conf = heap_length heap /\
     gen_gc_partial_conf_gen_start gen_conf <= gen_gc_partial_conf_refs_start gen_conf /\
     gen_gc_partial_conf_refs_start gen_conf <= heap_length heap /\
     ends_with_refs (gen_gc_partial_conf_refs_start gen_conf) heap /\
     heap_length heap * (dimindex (:A) DIV 8) < dimword (:A) /\
     data_to_word_config_len_size conf + 2 < dimindex (:A) /\
     (!t r. (gen_gc_partial_conf_isRef gen_conf (t,r) <=> isMutTag t)) /\
     (word_gen_gc_partial conf
        (MAP (word_addr conf) roots,curr,new,
         word_mul bytes_in_word (word (heap_length heap)),m,dm,
         word_mul bytes_in_word (word (gen_gc_partial_conf_gen_start gen_conf)),
         word_mul bytes_in_word (word (gen_gc_partial_conf_refs_start gen_conf))) =
        (roots1',i1,pa1:A word,m1,c1)) /\
     (word_heap curr heap conf STAR
      word_list_exists new (gen_gc_partial_conf_refs_start gen_conf -
                            gen_gc_partial_conf_gen_start gen_conf) STAR
      frame) (fun2set (m,dm)) /\ good_dimindex (:A) ==>
     ?xs1 current1 refs1.
       (word_heap curr (APPEND (APPEND (gc_state_old s1) current1) (gc_state_r1 s1))
          conf STAR
        word_heap new (gc_state_h1 s1) conf STAR
        misc_word_list (word_add new (word_mul bytes_in_word
          (word (heap_length (gc_state_h1 s1))))) xs1 STAR
        frame) (fun2set (m1,dm)) /\
       gc_state_h2 s1 = [] /\ gc_state_r4 s1 = [] /\ gc_state_r3 s1 = [] /\
       gc_state_r2 s1 = [] /\
       roots1' = MAP (word_addr conf) roots1 /\
       heap_length (gc_state_heap s1) = heap_length heap /\
       heap_segment (gen_gc_partial_conf_gen_start gen_conf,
                     gen_gc_partial_conf_refs_start gen_conf) (gc_state_heap s1) =
         SOME (gc_state_old s1,current1,refs1) /\
       c1 /\ (i1 = word (gc_state_a s1)) /\
       pa1 = word_add new (word_mul bytes_in_word (word (heap_length (gc_state_h1 s1)))) /\
       gc_state_n s1 = LENGTH xs1 /\ partial_len_inv s1 /\
       heap_length (gc_state_h1 s1) <= heap_length current1 /\
       heap_length (gc_state_h1 s1) + LENGTH xs1 + gen_gc_partial_conf_gen_start gen_conf =
         gen_gc_partial_conf_refs_start gen_conf /\
       ALL (is_Ref (gen_gc_partial_conf_isRef gen_conf)) (gc_state_r1 s1)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[partial_gc_def] THEN
  DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ocr:((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list#((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list#((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list` ASSUME_TAC)
   (ISPEC `heap_segment (gen_gc_partial_conf_gen_start (gen_conf:(data_to_word_memoryProof_tag#
      (A word_loc)list)gen_gc_partial_conf), gen_gc_partial_conf_refs_start gen_conf)
      (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`
      (cases "option")) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `F`)) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `ocr:((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list#((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list#((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list` BASICAUX_TUPLE3) THEN
  DISCH_THEN(X_CHOOSE_THEN `old:((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list` (X_CHOOSE_THEN `current:((A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` (X_CHOOSE_THEN
      `refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
      SUBST_ALL_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  gcp2aux_tuple_tac "gen_gc_partial_gc_move_list" ["roots2";"st1"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  gcp2aux_tuple_tac "gc_move_ref_list" ["rf1";"st2"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "heap_segment" th then
    STRIP_ASSUME_TAC(MATCH_MP heap_segment_IMP th) THEN
    STRIP_ASSUME_TAC(MATCH_MP GCP2AUX_heap_segment_split th) else NO_TAC) THEN
  (* the memory: old, current and refs parts of the heap, and the free space *)
  FIRST_X_ASSUM(fun th -> if is_comb(concl th) &&
      rand(concl th) = `fun2set (m:A word->A word_loc,dm)` then
    MP_TAC(REWRITE_RULE[word_heap_APPEND; word_list_exists_def; SEP_CLAUSES;
                        SEP_EXISTS_THM]
      (SUBS[SYM(ASSUME `APPEND (APPEND old current) refs:((A word_loc,
         data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list = heap`)] th))
    else NO_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:(A word_loc)list` (fun th ->
    STRIP_ASSUME_TAC(gcp2aux_sep_cond th))) THEN
  (* the states are ok *)
  FIRST_ASSUM(fun th -> if (try fst(dest_const(rator(concl th))) = "gc_state_ok" &&
      gcp2aux_has_const "gen_gc_partial_gc_move_data" (concl th) with Failure _ -> false)
    then let md = rand(concl th) in
         ASSUME_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]
           (MATCH_MP gc_partial_move_data_ok_before (CONJ (REFL md) th)))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th1 -> if gcp2aux_is_app_eq "gc_move_ref_list" th1 then
     FIRST_ASSUM(fun th2 ->
       ASSUME_TAC(MATCH_MP gc_partial_move_ref_list_ok_before (CONJ th1 th2)))
   else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "gen_gc_partial_gc_move_list" th then
    MP_TAC(MATCH_MP gen_gc_partial_gc_move_list_IMP th) else NO_TAC) THEN
  REWRITE_TAC gcp2aux_st_rw THEN STRIP_TAC THEN
  (* the word side *)
  gcp2aux_undisch_app "word_gen_gc_partial" THEN
  REWRITE_TAC[word_gen_gc_partial_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `word_ushr (word_mul bytes_in_word (word (gen_gc_partial_conf_gen_start
      (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf))):A word)
      (backend_common_word_shift (:A)) = word (gen_gc_partial_conf_gen_start gen_conf)`
    (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC GCP2AUX_ushr_bytes THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list) * dimindex(:A) DIV 8` THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN gcp2aux_arith_tac;
    ALL_TAC] THEN
  gcp2aux_tuple_tac "word_gen_gc_partial_move_roots" ["roots3";"i3";"pa3";"m3";"c13"] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "word_gen_gc_partial_move_roots" th
    then REWRITE_TAC[th] else NO_TAC) THEN
  CASE_REWRITE_TAC[] THEN
  gcp2aux_tuple_tac "word_gen_gc_partial_move_ref_list" ["i4";"pa4";"m4";"c24"] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "word_gen_gc_partial_move_ref_list" th
    then REWRITE_TAC[th] else NO_TAC) THEN
  CASE_REWRITE_TAC[] THEN
  gcp2aux_tuple_tac "word_gen_gc_partial_move_data" ["i5";"pa5";"m5";"c35"] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "word_gen_gc_partial_move_data" th
    then REWRITE_TAC[th] else NO_TAC) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  gcp2aux_subst_vars_tac ["roots3";"i5";"pa5";"m5";"c1"] THEN
  (* the roots *)
  SUBGOAL_THEN `LENGTH (xs:(A word_loc)list) = heap_length (current:((A word_loc,
     data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)` ASSUME_TAC THENL
   [gcp2aux_arith_tac; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[empty_state_def]) THEN
  (fun (asl,w as g) ->
    let th = snd(find (fun (_,th) -> gcp2aux_is_app_eq "gen_gc_partial_gc_move_list" th) asl) in
    let st0 = rand(rator(lhs(concl th))) in
    MP_TAC(ISPECL [`roots:((A word_loc)heap_address)list`; `xs:(A word_loc)list`;
      `roots1:((A word_loc)heap_address)list`; `roots1':(A word_loc)list`;
      `st1:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; st0;
      `pa3:A word`; `new:A word`; `m3:A word->A word_loc`; `m:A word->A word_loc`;
      `i3:A word`;
      `word_heap curr (old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
         heap_element)list) conf STAR
       word_heap (word_add curr (word_mul bytes_in_word (word (heap_length
         (APPEND old (current:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list)))))) (refs:((A word_loc,data_to_word_memoryProof_tag#
         (A word_loc)list)heap_element)list) conf STAR
       (frame:(A word#A word_loc->bool)->bool)`;
      `dm:A word->bool`; `curr:A word`; `c13:bool`; `old:((A word_loc,
        data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `current:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf`;
      `conf:data_to_word_config`] word_gen_gc_partial_move_roots_thm) g) THEN
  REWRITE_TAC gcp2aux_st_rw THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [gcp2aux_sep_addr_tac gcp2aux_addr_hl_tac; gcp2aux_arith_tac];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs2:(A word_loc)list` (X_CHOOSE_THEN
    `current2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    STRIP_ASSUME_TAC)) THEN
  gcp2aux_subst_vars_tac ["roots1'";"i3";"pa3"] THEN
  (* the references *)
  FIRST_ASSUM(fun th -> if concl th = `c13:bool` then
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th else NO_TAC) THEN
  MP_TAC(ISPECL [`refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      heap_element)list`;
    `st1:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `rf1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `st2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf`]
    gc_partial_move_ref_list_with_NIL) THEN
  ASM_REWRITE_TAC[] THEN
  gcp2aux_tuple_tac "gc_move_ref_list" ["rf3";"st3"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  gcp2aux_subst_vars_tac ["rf3";"st2"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "gc_move_ref_list" th &&
      gcp2aux_has_const "gc_state_h2_fupd" (lhs(concl th)) then
    MP_TAC(MATCH_MP data_to_word_gcProof_gc_move_ref_list_IMP th) else NO_TAC) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALL isRef (refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      heap_element)list)` ASSUME_TAC THENL
   [UNDISCH_TAC `ends_with_refs (gen_gc_partial_conf_refs_start (gen_conf:
      (data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf))
      (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)` THEN
    ASM_REWRITE_TAC[ends_with_refs_def; option_INJ; PAIR_EQ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      heap_element)list) = gen_gc_partial_conf_refs_start (gen_conf:
      (data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf) +
      heap_length (refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      heap_element)list)` ASSUME_TAC THENL
   [gcp2aux_arith_tac; ALL_TAC] THEN
  SUBGOAL_THEN `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list) < dimword(:A)` ASSUME_TAC THENL
   [MATCH_MP_TAC GCP2AUX_LT_DIMWORD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      heap_element)list` heap_length_LENGTH) THEN DISCH_TAC THEN
  (fun (asl,w as g) ->
    let th = snd(find (fun (_,th) -> gcp2aux_is_app_eq "word_gen_gc_partial_move_ref_list" th)
                      asl) in
    let comps = gcp2aux_strip_pair (rand(lhs(concl th))) in
    let k0 = el 0 comps and pa0 = el 2 comps in
    MP_TAC(ISPECL [`refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
        heap_element)list`; `dimword(:A)`; `xs2:(A word_loc)list`;
      `rf1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `st3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
      `gc_state_h2_fupd (K []) (gc_state_r4_fupd (K [])
         (st1:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))`;
      `pa4:A word`; pa0; `m4:A word->A word_loc`; `m3:A word->A word_loc`; `i4:A word`;
      `word_heap new (gc_state_h2 (st1:(A word_loc,data_to_word_memoryProof_tag#
         (A word_loc)list)gc_state)) conf STAR
       word_heap curr (old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
         heap_element)list) conf STAR
       (frame:(A word#A word_loc->bool)->bool)`;
      `dm:A word->bool`; `curr:A word`; `c24:bool`; k0;
      `old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `current2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf`;
      `conf:data_to_word_config`] word_gen_gc_partial_move_ref_list_thm) g) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [gcp2aux_arith_tac; gcp2aux_arith_tac; gcp2aux_arith_tac; gcp2aux_arith_tac;
      SUBGOAL_THEN `gen_gc_partial_conf_refs_start (gen_conf:(data_to_word_memoryProof_tag#
          (A word_loc)list)gen_gc_partial_conf) + heap_length (rf1:((A word_loc,
          data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) =
          heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
          heap_element)list)` SUBST1_TAC THENL
       [gcp2aux_arith_tac; ASM_REWRITE_TAC[]];
      gcp2aux_sep_addr_tac gcp2aux_addr_hl_tac;
      SUBGOAL_THEN `heap_length (rf1:((A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)heap_element)list) = heap_length (refs:((A word_loc,
          data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)` ASSUME_TAC THENL
       [gcp2aux_arith_tac;
        gcp2aux_same_app_tac "word_gen_gc_partial_move_ref_list" THEN gcp2aux_addr_hl_tac];
      gcp2aux_arith_tac];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs3:(A word_loc)list` (X_CHOOSE_THEN
    `current3:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    STRIP_ASSUME_TAC)) THEN
  gcp2aux_subst_vars_tac ["i4";"pa4"] THEN
  SUBGOAL_THEN `heap_length (rf1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      heap_element)list) = heap_length (refs:((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list)` ASSUME_TAC THENL
   [gcp2aux_arith_tac; ALL_TAC] THEN
  (* the data *)
  FIRST_ASSUM(fun th -> if (try fst(dest_const(rator(concl th))) = "gc_state_ok" &&
      gcp2aux_has_const "gen_gc_partial_gc_move_data" (concl th) with Failure _ -> false)
    then let md = rand(concl th) in
    MP_TAC(ISPECL [`dimword(:A)`; rand md; `m4:A word->A word_loc`; `dm:A word->bool`;
      `curr:A word`; `xs3:(A word_loc)list`; md; `pa1:A word`; `m1:A word->A word_loc`;
      `i1:A word`;
      `word_heap curr (old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
         heap_element)list) conf STAR
       word_heap (word_add curr (word_mul bytes_in_word (word (gen_gc_partial_conf_refs_start
         (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf)))))
         (rf1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
         conf STAR
       (frame:(A word#A word_loc->bool)->bool)`;
      `c35:bool`; `old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
        heap_element)list`;
      `current3:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf`;
      `conf:data_to_word_config`; `new:A word`] word_gen_gc_partial_move_data_thm)
    else NO_TAC) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM; APPEND] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      gcp2aux_arith_tac;
      gcp2aux_arith_tac;
      SUBGOAL_THEN `heap_length (gc_state_heap (st3:(A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)gc_state)) = heap_length (heap:((A word_loc,
          data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)` SUBST1_TAC THENL
       [gcp2aux_arith_tac; FIRST_ASSUM ACCEPT_TAC];
      FIRST_ASSUM ACCEPT_TAC;
      gcp2aux_arith_tac;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      gcp2aux_same_app_tac "word_gen_gc_partial_move_data" THEN
      REWRITE_TAC(APPEND :: gcp2aux_st3_rw) THEN CONJ_TAC THEN gcp2aux_addr_hl_tac;
      gcp2aux_arith_tac;
      REWRITE_TAC[partial_len_inv_def; gc_state_FIELDS.ri_accfupds; K_THM] THEN
      REWRITE_TAC(APPEND :: APPEND_NIL :: gcp2aux_st3_rw) THEN gcp2aux_arith_tac;
      REWRITE_TAC(APPEND :: word_heap_APPEND :: gcp2aux_st3_rw) THEN
      REWRITE_TAC[word_heap_def; SEP_CLAUSES] THEN
      gcp2aux_sep_addr_tac gcp2aux_addr_hl_tac;
      REWRITE_TAC(APPEND :: APPEND_NIL :: gcp2aux_st3_rw) THEN
      ASM_SIMP_TAC[EVERY_is_Ref_isRef];
      gcp2aux_arith_tac;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs4:(A word_loc)list` (X_CHOOSE_THEN
    `current4:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    STRIP_ASSUME_TAC)) THEN
  gcp2aux_subst_vars_tac ["i1";"pa1";"c1"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE(APPEND_NIL :: gcp2aux_st3_rw)) THEN
  REWRITE_TAC(APPEND_NIL :: gcp2aux_st3_rw) THEN
  (fun (asl,w as g) ->
    let md = gcp2aux_find_app "gen_gc_partial_gc_move_data" w in
    MP_TAC(MATCH_MP gc_move_data_IMP (REFL md)) g) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM; APPEND_NIL] THEN
  REWRITE_TAC gcp2aux_st3_rw THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "heap_segment" th &&
      vfree_in `current4:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
        heap_element)list` (concl th) then
    STRIP_ASSUME_TAC(MATCH_MP heap_segment_IMP th) else NO_TAC) THEN
  MAP_EVERY EXISTS_TAC [`xs4:(A word_loc)list`; `current4:((A word_loc,
     data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
     `refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
  REPEAT CONJ_TAC THENL
   [(fun (asl,w as g) -> REWRITE_TAC (gcp2aux_eqs_of
      ["gc_state_old";"gc_state_r1";"gc_state_h2"] asl) g) THEN
    REWRITE_TAC[word_heap_APPEND; APPEND_NIL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL]) THEN
    (fun (asl,w as g) -> RULE_ASSUM_TAC(REWRITE_RULE (gcp2aux_eqs_of ["gc_state_h2"] asl)) g) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL]) THEN
    gcp2aux_sep_addr_tac gcp2aux_addr_hl_tac;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    gcp2aux_arith_tac;
    (fun (asl,w as g) -> REWRITE_TAC (gcp2aux_eqs_of ["gc_state_old"] asl) g) THEN
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    (fun (asl,w as g) -> REWRITE_TAC (gcp2aux_eqs_of ["gc_state_h2"] asl) g) THEN
    REWRITE_TAC[APPEND_NIL];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    (fun (asl,w as g) -> RULE_ASSUM_TAC(REWRITE_RULE(gcp2aux_eqs_of
       ["gc_state_h2";"gc_state_r4"] asl)) g) THEN gcp2aux_arith_tac;
    (fun (asl,w as g) -> RULE_ASSUM_TAC(REWRITE_RULE(gcp2aux_eqs_of
       ["gc_state_h2";"gc_state_r4"] asl)) g) THEN gcp2aux_arith_tac;
    (fun (asl,w as g) -> RULE_ASSUM_TAC(REWRITE_RULE(APPEND :: gcp2aux_eqs_of
       ["gc_state_r4";"gc_state_r3";"gc_state_r2"] asl)) g) THEN FIRST_ASSUM ACCEPT_TAC]);;

(* HOL4 line 3703 *)
let word_gen_gc_partial_full_thm = prove
 (`!m dm curr s1 pa1 m1 i1 frame c1 roots heap roots1 roots1' new gen_conf conf.
     (partial_gc gen_conf (roots,heap) = (roots1,s1)) /\ gc_state_ok s1 /\
     heap_length heap <= dimword (:A) DIV 2 EXP shift_length conf /\
     heap_length heap * (dimindex (:A) DIV 8) < dimword (:A) /\
     ends_with_refs (gen_gc_partial_conf_refs_start gen_conf) heap /\
     gen_gc_partial_conf_limit gen_conf = heap_length heap /\
     gen_gc_partial_conf_gen_start gen_conf <= gen_gc_partial_conf_refs_start gen_conf /\
     gen_gc_partial_conf_refs_start gen_conf <= heap_length heap /\
     heap_length heap * (dimindex (:A) DIV 8) < dimword (:A) /\
     data_to_word_config_len_size conf + 2 < dimindex (:A) /\
     (!t r. (gen_gc_partial_conf_isRef gen_conf (t,r) <=> isMutTag t)) /\
     (word_gen_gc_partial_full conf
        (MAP (word_addr conf) roots,curr,new,
         word_mul bytes_in_word (word (heap_length heap)),m,dm,
         word_mul bytes_in_word (word (gen_gc_partial_conf_gen_start gen_conf)),
         word_mul bytes_in_word (word (gen_gc_partial_conf_refs_start gen_conf))) =
        (roots1',i1,pa1:A word,m1,c1)) /\
     (word_heap curr heap conf STAR
      word_list_exists new (heap_length heap) STAR
      frame) (fun2set (m,dm)) /\ good_dimindex (:A) ==>
     ?current1 refs1.
       (word_heap curr (gc_state_old s1) conf STAR
        word_heap (word_add curr (word_mul bytes_in_word
          (word (heap_length (gc_state_old s1))))) (gc_state_h1 s1) conf STAR
        word_list_exists pa1 (gc_state_n s1) STAR
        word_heap (word_add pa1 (word_mul bytes_in_word (word (gc_state_n s1))))
          (gc_state_r1 s1) conf STAR
        word_list_exists new (heap_length heap) STAR
        frame) (fun2set (m1,dm)) /\
       gc_state_h2 s1 = [] /\ gc_state_r4 s1 = [] /\ gc_state_r3 s1 = [] /\
       gc_state_r2 s1 = [] /\
       roots1' = MAP (word_addr conf) roots1 /\
       heap_length (gc_state_heap s1) = heap_length heap /\
       heap_segment (gen_gc_partial_conf_gen_start gen_conf,
                     gen_gc_partial_conf_refs_start gen_conf) (gc_state_heap s1) =
         SOME (gc_state_old s1,current1,refs1) /\
       c1 /\ (i1 = word (gc_state_a s1)) /\
       pa1 = word_add curr (word_mul bytes_in_word
               (word (heap_length (APPEND (gc_state_old s1) (gc_state_h1 s1))))) /\
       partial_len_inv s1 /\
       ALL (is_Ref (gen_gc_partial_conf_isRef gen_conf)) (gc_state_r1 s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  gcp2aux_undisch_app "word_gen_gc_partial_full" THEN
  REWRITE_TAC[word_gen_gc_partial_full_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  gcp2aux_tuple_tac "word_gen_gc_partial" ["roots3";"i3";"pa3";"m3";"c13"] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "word_gen_gc_partial" th
    then REWRITE_TAC[th] else NO_TAC) THEN
  CASE_REWRITE_TAC[] THEN
  gcp2aux_tuple_tac "memcpy" ["b1";"m4";"c24"] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "memcpy" th
    then REWRITE_TAC[th] else NO_TAC) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  gcp2aux_subst_vars_tac ["roots3";"i3";"b1";"m4";"c1"] THEN
  (* the partial collection, with the free space split *)
  SUBGOAL_THEN `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      heap_element)list) =
    (gen_gc_partial_conf_refs_start (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)
      gen_gc_partial_conf) - gen_gc_partial_conf_gen_start gen_conf) +
    (heap_length heap - (gen_gc_partial_conf_refs_start gen_conf -
                         gen_gc_partial_conf_gen_start gen_conf))` ASSUME_TAC THENL
   [gcp2aux_arith_tac; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_comb(concl th) &&
      rand(concl th) = `fun2set (m:A word->A word_loc,dm)` then
    FIRST_ASSUM(fun eq -> if is_eq(concl eq) && gcp2aux_is_app_eq "heap_length" eq &&
        gcp2aux_has_const "-" (concl eq) then
      ASSUME_TAC(REWRITE_RULE[data_to_word_memoryProof_word_list_exists_ADD]
        (ONCE_REWRITE_RULE[eq] th)) else NO_TAC)
    else NO_TAC) THEN
  MP_TAC(ISPECL [`m:A word->A word_loc`; `dm:A word->bool`; `curr:A word`;
    `s1:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `pa3:A word`; `m3:A word->A word_loc`; `i1:A word`;
    `word_list_exists (word_add new (word_mul bytes_in_word (word
       (gen_gc_partial_conf_refs_start (gen_conf:(data_to_word_memoryProof_tag#
         (A word_loc)list)gen_gc_partial_conf) - gen_gc_partial_conf_gen_start gen_conf))))
       (heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
         heap_element)list) - (gen_gc_partial_conf_refs_start gen_conf -
         gen_gc_partial_conf_gen_start gen_conf)) STAR
     (frame:(A word#A word_loc->bool)->bool)`;
    `c13:bool`; `roots:((A word_loc)heap_address)list`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `roots1:((A word_loc)heap_address)list`; `roots1':(A word_loc)list`; `new:A word`;
    `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf`;
    `conf:data_to_word_config`] word_gen_gc_partial_thm) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [gcp2aux_sep_ac_tac; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs1:(A word_loc)list` (X_CHOOSE_THEN
    `current1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    (X_CHOOSE_THEN `refs1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      heap_element)list` STRIP_ASSUME_TAC))) THEN
  gcp2aux_subst_vars_tac ["roots1'";"i1";"pa3"] THEN
  (* the current part and the copied part as word lists *)
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "heap_segment" th then
    STRIP_ASSUME_TAC(MATCH_MP heap_segment_IMP th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if is_comb(concl th) &&
      rand(concl th) = `fun2set (m3:A word->A word_loc,dm)` then
    ASSUME_TAC(REWRITE_RULE[word_heap_APPEND] th) else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if is_comb(concl th) &&
      rand(concl th) = `fun2set (m3:A word->A word_loc,dm)` then
    let leaf = find (fun l -> try let f,args = strip_comb l in
        fst(dest_const f) = "word_heap" &&
        el 1 args = `current1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
          heap_element)list` with Failure _ -> false)
      (gcp2aux_star_leaves (rator(concl th))) in
    MP_TAC(MATCH_MP word_heap_eq_word_list (gcp2aux_sep_focus leaf th)) else NO_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `ys:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> if is_comb(concl th) &&
      rand(concl th) = `fun2set (m3:A word->A word_loc,dm)` &&
      gcp2aux_has_const "misc_word_list" (concl th) then
    let leaf = find (fun l -> try let f,args = strip_comb l in
        fst(dest_const f) = "word_heap" && el 0 args = `new:A word` with Failure _ -> false)
      (gcp2aux_star_leaves (rator(concl th))) in
    MP_TAC(MATCH_MP word_heap_eq_word_list_strong (gcp2aux_sep_focus leaf th)) else NO_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `xh:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`heap_length (gc_state_h1 (s1:(A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)gc_state))`; `ys:(A word_loc)list`] LESS_EQ_IMP_APPEND) THEN
  ANTS_TAC THENL [gcp2aux_arith_tac; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ys1:(A word_loc)list` (X_CHOOSE_THEN `ys2:(A word_loc)list`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(fun th -> if concl th = `ys:(A word_loc)list = APPEND ys1 ys2` then
    SUBST_ALL_TAC th else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_to_word_memoryProof_word_list_APPEND]) THEN
  (* the copy *)
  SUBGOAL_THEN `word_ushr (word_sub (word_add (new:A word) (word_mul bytes_in_word (word
      (heap_length (gc_state_h1 (s1:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      gc_state)))))) new) (backend_common_word_shift (:A)) =
      (word (LENGTH (xh:(A word_loc)list)):A word)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[WORD_RULE `word_sub (word_add (a:A word) b) a = b`] THEN
    FIRST_ASSUM(fun th -> if concl th = `heap_length (gc_state_h1 (s1:(A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) = LENGTH (xh:(A word_loc)list)`
      then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    MATCH_MP_TAC GCP2AUX_ushr_bytes THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list) * dimindex(:A) DIV 8` THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN gcp2aux_arith_tac;
    ALL_TAC] THEN
  (fun (asl,w as g) ->
    let th = snd(find (fun (_,th) -> let c = concl th in is_comb c &&
       rand c = `fun2set (m3:A word->A word_loc,dm)` &&
       mem `misc_word_list (new:A word) (xh:(A word_loc)list)` (gcp2aux_star_leaves (rator c)) &&
       exists (fun l -> vfree_in `ys1:(A word_loc)list` l) (gcp2aux_star_leaves (rator c)))
       asl) in
    let leaves = gcp2aux_star_leaves (rator(concl th)) in
    let is_ys1 l = try rand l = `ys1:(A word_loc)list` with Failure _ -> false in
    let rest = filter (fun l -> not (l = `misc_word_list (new:A word) (xh:(A word_loc)list)`) &&
                                not (is_ys1 l)) leaves in
    let frame' = gcp2aux_list_mk_star rest in
    MP_TAC(ISPECL [`xh:(A word_loc)list`; `new:A word`; `c24:bool`;
      `word_add curr (word_mul bytes_in_word (word (gen_gc_partial_conf_gen_start
         (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf)))):A word`;
      `m3:A word->A word_loc`; `m1:A word->A word_loc`; `dm:A word->bool`; `pa1:A word`;
      `ys1:(A word_loc)list`; frame'] memcpy_thm) g) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#
        (A word_loc)list)heap_element)list)` THEN CONJ_TAC THENL
       [gcp2aux_arith_tac; MATCH_MP_TAC GCP2AUX_LT_DIMWORD THEN ASM_REWRITE_TAC[]];
      gcp2aux_sep_addr_tac gcp2aux_addr_len_tac];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_comb(concl th) &&
      rand(concl th) = `fun2set (m1:A word->A word_loc,dm)` then
    let leaf = `misc_word_list (word_add (curr:A word) (word_mul bytes_in_word (word
      (gen_gc_partial_conf_gen_start (gen_conf:(data_to_word_memoryProof_tag#
       (A word_loc)list)gen_gc_partial_conf))))) (xh:(A word_loc)list)` in
    let th1 = gcp2aux_sep_focus leaf th in
    FIRST_ASSUM(fun imp -> if is_forall(concl imp) &&
        gcp2aux_has_const "misc_word_list" (concl imp) && gcp2aux_has_const "word_heap" (concl imp)
      then ASSUME_TAC(MATCH_MP imp th1) else NO_TAC)
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if is_comb(concl th) &&
      rand(concl th) = `fun2set (m1:A word->A word_loc,dm)` then
    MP_TAC(REWRITE_RULE[word_list_exists_def; SEP_CLAUSES; SEP_EXISTS_THM] th) else NO_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `zs:(A word_loc)list` (fun th ->
    STRIP_ASSUME_TAC(gcp2aux_sep_cond th))) THEN
  MAP_EVERY EXISTS_TAC [`current1:((A word_loc,data_to_word_memoryProof_tag#
     (A word_loc)list)heap_element)list`; `refs1:((A word_loc,data_to_word_memoryProof_tag#
     (A word_loc)list)heap_element)list`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[word_list_exists_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
    MAP_EVERY EXISTS_TAC [`ys2:(A word_loc)list`;
      `APPEND (xh:(A word_loc)list) (APPEND xs1 zs)`] THEN
    gcp2aux_goal_cond_tac THEN CONJ_TAC THENL [gcp2aux_arith_tac; ALL_TAC] THEN
    gcp2aux_goal_cond_tac THEN CONJ_TAC THENL [gcp2aux_arith_tac; ALL_TAC] THEN
    REWRITE_TAC[data_to_word_memoryProof_word_list_APPEND] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `pa1:A word`)) THEN
    SUBGOAL_THEN `gen_gc_partial_conf_refs_start (gen_conf:(data_to_word_memoryProof_tag#
        (A word_loc)list)gen_gc_partial_conf) - gen_gc_partial_conf_gen_start gen_conf =
        LENGTH (xh:(A word_loc)list) + LENGTH (xs1:(A word_loc)list) /\
      gen_gc_partial_conf_refs_start gen_conf =
        gen_gc_partial_conf_gen_start gen_conf + LENGTH xh + LENGTH xs1`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN gcp2aux_arith_tac; ALL_TAC] THEN
    gcp2aux_sep_addr_tac (FIRST_ASSUM(fun th -> if concl th = `gen_gc_partial_conf_refs_start
        (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf) -
        gen_gc_partial_conf_gen_start gen_conf =
        LENGTH (xh:(A word_loc)list) + LENGTH (xs1:(A word_loc)list)` then
        REWRITE_TAC[th] else NO_TAC) THEN
      FIRST_ASSUM(fun th -> if concl th = `gen_gc_partial_conf_refs_start
        (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf) =
        gen_gc_partial_conf_gen_start gen_conf + LENGTH (xh:(A word_loc)list) +
        LENGTH (xs1:(A word_loc)list)` then REWRITE_TAC[th] else NO_TAC) THEN
      gcp2aux_addr_len_tac);
    REFL_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `pa1:A word` then
      REWRITE_TAC[th] else NO_TAC) THEN gcp2aux_addr_len_tac]);;

(* HOL4 line 3804 *)
let gen_starts_in_store_IMP_SOME_Word = prove
 (`!c gens x. gen_starts_in_store c gens x ==> ?w:A word. x = SOME (wl_Word w)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  CASES_ON `gens:gen_state` THEN
  CASES_ON `x:(A word_loc)option` THEN REWRITE_TAC[gen_starts_in_store_def] THEN
  CASES_ON `a:A word_loc` THEN REWRITE_TAC[gen_starts_in_store_def] THEN MESON_TAC[]);;

(* HOL4 line 3811 *)
let glob_real_inv = prove
 (`!c (other:A word) w.
     glob_real_inv c other (SOME w) (SOME (glob_real c other w)) <=> isWord w`,
  REPEAT GEN_TAC THEN CASES_ON `w:A word_loc` THEN
  REWRITE_TAC[isWord_def; glob_real_def; glob_real_inv_def; option_INJ;
              injectivity "word_loc"; distinctness "word_loc"] THEN MESON_TAC[]);;

(* HOL4 line 3819 (HOL4: Q.prove ... |> GEN_ALL |> SIMP_RULE (srw_ss())      *)
(* [LET_DEF,PULL_EXISTS,GSYM CONJ_ASSOC] |> SPEC_ALL: the let is expanded,    *)
(* the unused existential a1 dropped; conjunctions as in the HOL4 source)   *)
let word_gc_fun_lemma_Simple = prove
 (`!c v stack refs hs heap be a sp sp1 gens limit ts s (m:A word->A word_loc) dm
    roots2 heap2.
     abs_ml_inv c (CONS v (MAP FST stack)) refs (hs,heap,be,a,sp,sp1,gens) limit ts /\
     good_dimindex (:A) /\
     heap_in_memory_store heap a sp sp1 gens c s m dm limit /\
     ALL2 (\v w. word_addr c v = w) hs (CONS (FAPPLY s Globals) (MAP SND stack)) /\
     full_gc (hs,heap,limit) = (roots2,heap2,heap_length heap2,T) /\
     data_to_word_config_gc_kind c = data_to_word_Simple ==>
     ?stack1 m1 s1.
       word_gc_fun c (MAP SND stack,m,dm,s) = SOME (stack1,m1,s1) /\
       heap_in_memory_store (APPEND heap2 (heap_expand (limit - heap_length heap2)))
         (heap_length heap2) (limit - heap_length heap2) 0 gens c s1 m1 dm limit /\
       ALL2 (\v w. word_addr c v = (w:A word_loc)) roots2
         (CONS (FAPPLY s1 Globals) (MAP SND (ZIP (MAP FST stack) stack1))) /\
       LENGTH stack1 = LENGTH stack`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "heap_in_memory_store" o concl)) THEN
  REWRITE_TAC[heap_in_memory_store_def; GCP2AUX_FLOOKUP_SOME] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "ALL2" o concl)) THEN
  REWRITE_TAC[LIST_REL_EQ_MAP] THEN DISCH_TAC THEN
  REWRITE_TAC[word_gc_fun_def] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[theWord_def] THEN
  CASE_REWRITE_TAC[])
  THEN
(REWRITE_TAC[ETA_AX] THEN
  gcp2aux_tuple_tac "word_full_gc" ["rs1";"i1";"pa1";"m1";"c2"] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "word_full_gc" th
    then REWRITE_TAC[th] else NO_TAC) THEN
  CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "full_gc" th then
    STRIP_ASSUME_TAC(MATCH_MP full_gc_IMP th) THEN
    ASSUME_TAC(MATCH_MP full_gc_IMP_LENGTH th) else NO_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `limit:num`)) THEN
  MP_TAC(ISPECL [`hs:((A word_loc)heap_address)list`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
       heap_element)list)`; `roots2:((A word_loc)heap_address)list`;
    `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `heap_length (heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
       heap_element)list)`;
    `c:data_to_word_config`; `curr:A word`; `other:A word`;
    `set_sep_emp:(A word#A word_loc->bool)->bool`; `m:A word->A word_loc`; `dm:A word->bool`;
    `rs1:(A word_loc)list`; `i1:A word`; `pa1:A word`; `m1:A word->A word_loc`;
    `c2:bool`] word_full_gc_thm) THEN
  ASM_REWRITE_TAC[SEP_CLAUSES] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `(heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#
        (A word_loc)list)heap_element)list) + 3) * dimindex(:A) DIV 8` THEN
      ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ARITH_TAC;
      gcp2aux_arith_tac];
    ALL_TAC] THEN
  STRIP_TAC THEN gcp2aux_subst_vars_tac ["rs1";"i1";"pa1"])
  THEN
(FIRST_ASSUM(fun th -> if gcp2aux_has_const "gen_starts_in_store" (concl th) then
    MP_TAC(MATCH_MP gen_starts_in_store_IMP_SOME_Word th) else NO_TAC) THEN
  REWRITE_TAC[GCP2AUX_FLOOKUP_SOME] THEN
  DISCH_THEN(X_CHOOSE_THEN `wg:A word` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> if gcp2aux_has_const "glob_real_inv" (concl th) then
    MP_TAC(REWRITE_RULE[glob_real_inv_def] th) else NO_TAC) THEN
  REWRITE_TAC[GCP2AUX_FLOOKUP_SOME] THEN
  DISCH_THEN(X_CHOOSE_THEN `wglob:A word` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `word_gc_fun_assum c (s:(store_name,A word_loc)fmap)` ASSUME_TAC THENL
   [REWRITE_TAC[word_gc_fun_assum_def; INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_REWRITE_TAC[isWord_def] THEN gcp2aux_arith_tac;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[])
  THEN
(MAP_EVERY EXISTS_TAC [`TL (MAP (word_addr c) (roots2:((A word_loc)heap_address)list))`;
    `m1:A word->A word_loc`] THEN
  REWRITE_TAC[option_INJ; PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  REWRITE_TAC[FUPDATE_LIST_THM; FDOM_FUPDATE; FAPPLY_FUPDATE_THM; FLOOKUP_UPDATE; IN_INSERT;
              distinctness "store_name"] THEN
  REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand] THEN
  SUBGOAL_THEN `heap_length (heap2:((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list) + heap_length (heap:((A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) -
      heap_length heap2 = heap_length heap` SUBST1_TAC THENL
   [gcp2aux_arith_tac; ALL_TAC] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES])
  THEN
(SUBGOAL_THEN `LENGTH (roots2:((A word_loc)heap_address)list) =
      SUC (LENGTH (stack:(data_v#A word_loc)list))` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && gcp2aux_has_const "Globals" (concl th) &&
        gcp2aux_has_const "MAP" (concl th) then
      MP_TAC(AP_TERM `LENGTH:(A word_loc)list->num` th) else NO_TAC) THEN
    REWRITE_TAC[LENGTH; LENGTH_MAP] THEN gcp2aux_arith_tac;
    ALL_TAC])
  THEN
(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `r0:(A word_loc)heap_address`
    (X_CHOOSE_THEN `rt:((A word_loc)heap_address)list` SUBST_ALL_TAC))
    (ISPEC `roots2:((A word_loc)heap_address)list` list_CASES) THENL
   [gcp2aux_arith_tac; ALL_TAC] THEN
  REWRITE_TAC[MAP; HD; TL] THEN
  SUBGOAL_THEN `LENGTH (rt:((A word_loc)heap_address)list) =
      LENGTH (stack:(data_v#A word_loc)list)` ASSUME_TAC THENL
   [gcp2aux_arith_tac; ALL_TAC] THEN
  ASM_SIMP_TAC[MAP_ZIP; LENGTH_MAP])
  THEN
(EXISTS_TAC `other:A word` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `curr:A word` THEN ASM_REWRITE_TAC[glob_real_inv] THEN
  SUBGOAL_THEN `heap_length (heap2:((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list) + heap_length (heap:((A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) -
      heap_length heap2 = heap_length heap` SUBST1_TAC THENL
   [gcp2aux_arith_tac; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  FIRST_ASSUM(fun eq -> if is_eq(concl eq) && gcp2aux_has_const "Globals" (concl eq) &&
      gcp2aux_has_const "MAP" (concl eq) then
    FIRST_ASSUM(fun gw -> if is_eq(concl gw) && is_comb(lhs(concl gw)) &&
        gcp2aux_has_const "Globals" (lhs(concl gw)) && not (gcp2aux_has_const "MAP" (concl gw))
      then FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "word_full_gc" th then
        MP_TAC(MATCH_MP GCP2AUX_word_full_gc_HD (REWRITE_RULE[gw]
          (REWRITE_RULE[GSYM(REWRITE_RULE[ETA_AX] eq)] th)))
        else NO_TAC) else NO_TAC) else NO_TAC) THEN
  REWRITE_TAC[MAP; HD]));;

(* HOL4 line 3875 *)
let do_partial_def = cake_def
  `do_partial (c:data_to_word_config) (s:(store_name,A word_loc)fmap) =
     match data_to_word_config_gc_kind c with
       Generational l -> word_gen_gc_can_do_partial l s
     | _ -> F`;;

(* HOL4 line 3882 *)
let heap_segment_IMP_split = prove
 (`!m n (heap:((A,B)heap_element)list) x1 x2 x3.
     heap_segment (m,n) heap = SOME (x1,x2,x3) ==>
     heap_split m heap = SOME (x1,APPEND x2 x3) /\
     heap_split n heap = SOME (APPEND x1 x2,x3)`,
  MATCH_ACCEPT_TAC GCP2AUX_heap_segment_split);;

(* HOL4 line 3896 *)
let heap_split_IMP_heap_length = prove
 (`!(heap:((A,B)heap_element)list) n h1 h2.
     heap_split n heap = SOME (h1,h2) ==> heap_length h1 = n`,
  MESON_TAC[heap_split_heap_length]);;

(* HOL4 line 3906 *)
let heap_split_APPEND_EQ = prove
 (`!(h1:((A,B)heap_element)list) h2 a.
     heap_split a (APPEND h1 h2) = SOME (h1,h2) <=> a = heap_length h1`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[heap_split_heap_length];
    DISCH_THEN SUBST1_TAC THEN
    SIMP[heap_split_APPEND_if; LT_REFL; SUB_REFL; heap_split_0; APPEND_NIL]]);;

(* HOL4 line 3916 *)
let heap_split_IMP_APPEND = prove
 (`!(heap:((A,B)heap_element)list) n h1 h2.
     heap_split n heap = SOME (h1,h2) ==> heap = APPEND h1 h2`,
  MESON_TAC[heap_split_heap_length]);;

(* HOL4 line 3923 *)
let heap_length_nil = prove
 (`!m:((A,B)heap_element)list. heap_length m = 0 <=> m = []`,
  GEN_TAC THEN CASES_ON `m:((A,B)heap_element)list` THEN
  REWRITE_TAC[heap_length_NIL; GC1AUX_heap_length_CONS; NOT_CONS_NIL] THEN
  MP_TAC(ISPEC `a0:(A,B)heap_element` el_length_GT_0) THEN ARITH_TAC);;

(* HOL4 line 3929 *)
let abs_ml_inv_GenState_IMP_heap_length_FILTER = prove
 (`!c stack refs xs (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
     heap_element)list) be a sp sp1 n t ts tss y ys h1 h2.
     abs_ml_inv c stack refs
       (xs,heap,be,a,sp,sp1,GenState n (CONS t ts))
       (heap_length heap) tss /\
     data_to_word_config_gc_kind c = Generational (CONS y ys) /\
     heap_split (a + sp + sp1) heap = SOME (h1,h2) ==>
     ALL isDataElement h2 /\
     heap_length (FILTER isDataElement heap) = a + heap_length h2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def; unused_space_inv_def; gc_kind_inv_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "gen_state_ok" o concl)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq (concl th) && is_var (lhs(concl th)) && is_var (rhs(concl th))))) THEN
  SUBGOAL_THEN `ALL isDataElement (h2:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list)` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL isRef (h2:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list)` THEN
    MATCH_MP_TAC MONO_ALL THEN GEN_TAC THEN
    CASES_ON `x:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element` THEN
    REWRITE_TAC[isRef_def; isDataElement_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `data_up_to a (heap:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list)` THEN
  REWRITE_TAC[data_up_to_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list` (X_CHOOSE_THEN `p2:((A word_loc,
       data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
     heap_element)list`; `a:num`; `a + sp + sp1`; `p1:((A word_loc,
       data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
     `p2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
     `h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
     `h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`]
     heap_split_heap_split) THEN
  ASM_REWRITE_TAC[LE_ADD] THEN
  DISCH_THEN(X_CHOOSE_THEN `mm:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `heap_length (p1:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list) = a /\
                heap_length (mm:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) = sp + sp1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[heap_split_IMP_heap_length]; ALL_TAC] THEN
    MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
       heap_element)list`; `a + sp + sp1`; `h1:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list`; `h2:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list`] heap_split_IMP_heap_length) THEN
    ASM_REWRITE_TAC[heap_length_APPEND] THEN
    MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
       heap_element)list`; `a:num`; `p1:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list`; `p2:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list`] heap_split_IMP_heap_length) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `FILTER isDataElement (mm:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list) = []` ASSUME_TAC THENL
   [ASM_CASES_TAC `sp + sp1 = 0` THENL
     [SUBGOAL_THEN `mm:((A word_loc,data_to_word_memoryProof_tag#
         (A word_loc)list)heap_element)list = []` SUBST1_TAC THENL
       [ASM_MESON_TAC[heap_length_nil]; REWRITE_TAC[FILTER]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      gcp2aux_has_const "heap_lookup" (concl th))) THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    MP_TAC(ISPECL [`p1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
       heap_element)list`; `a:num`; `APPEND mm (h2:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list)`] heap_lookup_APPEND1) THEN
    ASM_REWRITE_TAC[LE_REFL; SUB_REFL] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `heap_length (mm:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list) = sp + sp1` THEN
    CASES_ON `mm:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    THENL [ASM_REWRITE_TAC[heap_length_NIL]; ALL_TAC] THEN
    REWRITE_TAC[APPEND; heap_lookup_def; option_INJ; GC1AUX_heap_length_CONS] THEN
    REPEAT DISCH_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `a1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list = []` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM heap_length_nil] THEN
      UNDISCH_TAC `el_length (Unused ((sp + sp1) - 1):((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)) +
                   heap_length (a1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) = sp + sp1` THEN
      REWRITE_TAC[el_length_def] THEN UNDISCH_TAC `~(sp + sp1 = 0)` THEN ARITH_TAC;
      REWRITE_TAC[FILTER; isDataElement_def; distinctness "heap_element"]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[FILTER_APPEND; APPEND] THEN
  SUBGOAL_THEN `FILTER isDataElement (p1:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list) = p1 /\ FILTER isDataElement (h2:((A word_loc,
       data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) = h2`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[FILTER_EQ_ID]; ALL_TAC] THEN
  ASM_REWRITE_TAC[heap_length_APPEND; APPEND_NIL; heap_length_NIL; ADD_CLAUSES]);;

(* HOL4 line 3970 (local) *)
let new_trig_ok = prove
 (`!a n x. word_ule a (word_mul bytes_in_word (word n)) /\ good_dimindex (:A) ==>
           word_ule a (new_trig (word_mul bytes_in_word (word n):A word) a x)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `h = word_mul bytes_in_word (word n):A word` THEN
  REWRITE_TAC[new_trig_def; LET_DEF; LET_END_DEF; WORD_ULE] THEN STRIP_TAC THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[WORD_VAL; LE_REFL] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `h:A word` VAL_BOUND) THEN REWRITE_TAC[VAL_WORD] THEN DISCH_TAC THEN
  SUBGOAL_THEN `MIN (val (h:A word)) (val (get_gen_size x:A word)) < 2 EXP dimindex(:A)`
    (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [UNDISCH_TAC `val (h:A word) < 2 EXP dimindex(:A)` THEN ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `val (a:A word) <= val (h:A word)` THEN
  UNDISCH_TAC `val (a:A word) <= val (get_gen_size x:A word)` THEN ARITH_TAC);;

(* GCP2AUX: replace dimindex(:A) by its value from an assumption and       *)
(* evaluate the numerals                                                    *)
let gcp2aux_dimindex_tac : tactic =
  FIRST_ASSUM(fun th ->
    if is_eq (concl th) && is_comb (lhs(concl th)) &&
       (try fst(dest_const(rator(lhs(concl th)))) = "dimindex" with Failure _ -> false) &&
       is_numeral (rhs(concl th))
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN ASSUME_TAC th
    else NO_TAC) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV(NUM_DIV_CONV ORELSEC LOG2_CONV ORELSEC NUM_EXP_CONV
    ORELSEC NUM_MULT_CONV))) THEN
  CONV_TAC(DEPTH_CONV(NUM_DIV_CONV ORELSEC LOG2_CONV ORELSEC NUM_EXP_CONV ORELSEC
    NUM_MULT_CONV));;

(* HOL4 line 3979 *)
let byte_aligned_IMP_bytes_in_word = prove
 (`!w:A word. byte_aligned w /\ good_dimindex (:A) ==> ?v. w = word_mul bytes_in_word v`,
  GEN_TAC THEN REWRITE_TAC[byte_aligned_def; aligned_def; align_w2n; good_dimindex_def;
    bytes_in_word_def] THEN STRIP_TAC THEN gcp2aux_dimindex_tac THENL
   [EXISTS_TAC `word (val (w:A word) DIV 4):A word`;
    EXISTS_TAC `word (val (w:A word) DIV 8):A word`] THEN
  REWRITE_TAC[word_mul_n2w] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
  REWRITE_TAC[MULT_SYM]);;

(* GCP2AUX: the arithmetic of MULT_bytes_in_word_LESS_EQ_IMP for a word   *)
(* size 2 EXP dimindex = M times d                                         *)
let GCP2AUX_mul_bytes_le = prove
 (`!(k:A word) n d M.
     2 EXP dimindex(:A) = M * d /\ 0 < d /\ 1 < M /\
     val (word_mul k (word d):A word) <= val (word_mul (word d) (word n):A word) ==>
     ?l. word_mul k (word d) = word_mul (word l) (word d):A word /\ l <= n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `d < M * d` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1 * d < M * d ==> d < M * d`) THEN
    REWRITE_TAC[LT_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val (word d:A word) = d` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD] THEN ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. (x * d) MOD (M * d) = x MOD M * d` ASSUME_TAC THENL
   [GEN_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MULT2] THEN
    REWRITE_TAC[MULT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `val (word_mul k (word d):A word) = val k MOD M * d` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `val (k:A word) MOD M < M` ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `val (k:A word) MOD M` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD_MUL; VAL_WORD] THEN
    SUBGOAL_THEN `val (k:A word) MOD M < M * d` (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th])
    THENL
     [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `M:num` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ARITH_RULE `M * 1 <= M * d ==> M <= M * d`) THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[MOD_MOD_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `val (word_mul (word d) (word n):A word) <= d * n` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_MUL; VAL_WORD] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `d * n MOD (M * d)` THEN
    REWRITE_TAC[MOD_LE; LE_MULT_LCANCEL] THEN DISJ2_TAC THEN REWRITE_TAC[MOD_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `val (k:A word) MOD M * d <= n * d` MP_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `val (word_mul k (word d):A word) <= val (word_mul (word d) (word n):A word)` THEN
    UNDISCH_TAC `val (word_mul (word d) (word n):A word) <= d * n` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC);;

(* HOL4 line 3990 *)
let MULT_bytes_in_word_LESS_EQ_IMP = prove
 (`!k n. val (word_mul k bytes_in_word:A word) <=
         val (word_mul bytes_in_word (word n):A word) /\
         good_dimindex (:A) ==>
         ?l. word_mul k bytes_in_word = word_mul (word l) bytes_in_word /\ l <= n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def; bytes_in_word_def] THEN
  STRIP_TAC THEN gcp2aux_dimindex_tac THEN
  MATCH_MP_TAC GCP2AUX_mul_bytes_le THENL
   [EXISTS_TAC `1073741824`; EXISTS_TAC `2305843009213693952`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* GCP2AUX: get_gen_size is a multiple of bytes_in_word *)
let GCP2AUX_get_gen_size_mul = prove
 (`!gs. ?k. get_gen_size gs = word_mul bytes_in_word k:A word`,
  GEN_TAC THEN CASES_ON `gs:num list` THEN REWRITE_TAC[get_gen_size_def] THENL
   [MESON_TAC[]; COND_CASES_TAC THEN MESON_TAC[]]);;

(* HOL4 line 4018 (local) *)
let new_trig_LESS_EQ = prove
 (`!n a22 a33. good_dimindex (:A) ==>
     ?k. new_trig (word_mul bytes_in_word (word n):A word) a22 a33 =
         word_mul bytes_in_word (word k) /\ k <= n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `h = word_mul bytes_in_word (word n):A word` THEN
  REWRITE_TAC[new_trig_def; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `?k. h = word_mul bytes_in_word (word k):A word /\ k <= n` ASSUME_TAC THENL
   [EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_VAL] THENL
   [REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_VAL] THEN
    MP_TAC(ISPEC `a33:num list` (INST_TYPE [`:A`,`:A`] GCP2AUX_get_gen_size_mul)) THEN
    DISCH_THEN(X_CHOOSE_TAC `k:A word`) THEN ASM_REWRITE_TAC[WORD_VAL] THEN
    MP_TAC(ISPECL [`k:A word`; `n:num`] MULT_bytes_in_word_LESS_EQ_IMP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [WORD_MUL_SYM] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `l:num` THEN ONCE_REWRITE_TAC[WORD_MUL_SYM] THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `a22:A word` byte_aligned_IMP_bytes_in_word) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:A word` SUBST_ALL_TAC) THEN
    MP_TAC(ISPECL [`v:A word`; `n:num`] MULT_bytes_in_word_LESS_EQ_IMP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [WORD_MUL_SYM] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
        gcp2aux_has_const "<" (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `l:num` THEN ONCE_REWRITE_TAC[WORD_MUL_SYM] THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 4039 *)
let alloc_size_def = cake_def
  `alloc_size k =
     (if k * (dimindex (:A) DIV 8) < dimword (:A)
      then word (k * (dimindex (:A) DIV 8))
      else word_neg (word 1)):A word`;;

(* GCP2AUX: the store of a heap in memory satisfies the gc assumption *)
let GCP2AUX_heap_in_memory_store_assum = prove
 (`!heap a sp sp1 gens c s (m:A word->A word_loc) dm limit.
     heap_in_memory_store heap a sp sp1 gens c s m dm limit /\ good_dimindex (:A) ==>
     word_gc_fun_assum c s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_in_memory_store_def; GCP2AUX_FLOOKUP_SOME] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if gcp2aux_has_const "gen_starts_in_store" (concl th) then
    MP_TAC(MATCH_MP gen_starts_in_store_IMP_SOME_Word th) else NO_TAC) THEN
  REWRITE_TAC[GCP2AUX_FLOOKUP_SOME] THEN
  DISCH_THEN(X_CHOOSE_THEN `wg:A word` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> if gcp2aux_has_const "glob_real_inv" (concl th) then
    MP_TAC(REWRITE_RULE[glob_real_inv_def] th) else NO_TAC) THEN
  REWRITE_TAC[GCP2AUX_FLOOKUP_SOME] THEN
  DISCH_THEN(X_CHOOSE_THEN `wglob:A word` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[word_gc_fun_assum_def; INSERT_SUBSET; EMPTY_SUBSET] THEN
  ASM_REWRITE_TAC[isWord_def] THEN gcp2aux_arith_tac);;



(* GCP2AUX: the copying collector returns the length of the new heap *)
let GCP2AUX_full_gc_a = prove
 (`!(roots:(A heap_address)list) (heap:((A,B)heap_element)list) limit roots1 heap1 a1.
     full_gc (roots,heap,limit) = (roots1,heap1,a1,T) ==> a1 = heap_length heap1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[full_gc_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  gcp2aux_tuple_tac "copying_gc_gc_move_list" ["r1";"h2";"a2";"n2";"heap2";"c2"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  gcp2aux_tuple_tac "copying_gc_gc_move_loop" ["heap3";"a3";"n3";"t3";"c3"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* instantiates the quantified variables of th by the free variables of the  *)
(* goal with the same names, or by the given terms                           *)
let gcp2aux_ispecl_names (pairs:(string*term)list) th : tactic = fun (asl,w as g) ->
  let vs = fst(strip_forall(concl th)) in
  let fvs = frees w @ itlist (fun (_,t) l -> frees (concl t) @ l) asl [] in
  let pick v = let n = fst(dest_var v) in
    try assoc n pairs with Failure _ -> find (fun u -> fst(dest_var u) = n) fvs in
  MP_TAC(ISPECL (map pick vs) th) g;;

(* the statement of word_gc_fun_lemma, for its case lemmas *)
let gcp2aux_gc_fun_stmt = `!c v stack refs hs heap be a sp sp1 gens limit ts s (m:A word->A word_loc) dm
    roots2 heap2 a2 n2 gens2 k.
     abs_ml_inv c (CONS v (MAP FST stack)) refs (hs,heap,be,a,sp,sp1,gens) limit ts /\
     good_dimindex (:A) /\
     heap_in_memory_store heap a sp sp1 gens c s m dm limit /\
     ALL2 (\v w. word_addr c v = w) hs (CONS (FAPPLY s Globals) (MAP SND stack)) /\
     gc_combined (make_gc_conf limit) (data_to_word_config_gc_kind c)
       (hs,heap,gens,a + sp + sp1,do_partial c s) =
       (roots2,heap2,a2,n2,gens2,T) ==>
     ?stack1 m1 s1 k2 k3.
       word_gc_fun c (MAP SND stack,m,dm,s) = SOME (stack1,m1,s1) /\
       heap_in_memory_store heap2 a2 k2 k3 gens2 c s1 m1 dm limit /\ k2 + k3 = n2 /\
       (!l. FLOOKUP s AllocSize = SOME (wl_Word (alloc_size k)) /\
            data_to_word_config_gc_kind c = Generational l /\
            word_gen_gc_can_do_partial l s ==>
            wl_has_space (wl_Word (alloc_size k:A word))
              (wl_state_store_fupd (K s1) (ARB:(A,C,FFI)wl_state)) = SOME T) /\
       (data_to_word_config_gc_kind c = data_to_word_None \/
        data_to_word_config_gc_kind c = data_to_word_Simple ==> k3 = 0) /\
       (!l k. FLOOKUP s AllocSize = SOME (wl_Word (alloc_size k)) /\
              data_to_word_config_gc_kind c = Generational l /\
              ~word_gen_gc_can_do_partial l s /\
              k <= n2 ==> k <= k2) /\
       ALL2 (\v w. word_addr c v = (w:A word_loc)) roots2
         (CONS (FAPPLY s1 Globals) (MAP SND (ZIP (MAP FST stack) stack1))) /\
       LENGTH stack1 = LENGTH stack`
;;

(* the statement of word_gc_fun_lemma with an extra hypothesis *)
let gcp2aux_gc_fun_case extra =
  let vs,body = strip_forall gcp2aux_gc_fun_stmt in
  let h,cl = dest_imp body in
  list_mk_forall(vs, mk_imp(mk_conj(extra,h),cl));;

(* GCP2AUX: word_gc_fun_lemma without a collector *)
let GCP2AUX_word_gc_fun_None = prove
 (gcp2aux_gc_fun_case `data_to_word_config_gc_kind c = data_to_word_None`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GCP2AUX_heap_in_memory_store_assum o
    CONJ (ASSUME `heap_in_memory_store heap a sp sp1 gens c s (m:A word->A word_loc) dm limit`) o
    K (ASSUME `good_dimindex(:A)`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "gc_combined" o concl)) THEN
  ASM_REWRITE_TAC[gc_combined_def; PAIR_EQ] THEN STRIP_TAC THEN
  gcp2aux_subst_vars_tac ["roots2";"heap2";"a2";"n2";"gens2"] THEN
  REWRITE_TAC[word_gc_fun_def] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "heap_in_memory_store" o concl)) THEN
  REWRITE_TAC[heap_in_memory_store_def; GCP2AUX_FLOOKUP_SOME] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`MAP SND (stack:(data_v#A word_loc)list)`; `m:A word->A word_loc`;
    `(s:(store_name,A word_loc)fmap) |++
        [NextFree,wl_Word (theWord (FAPPLY s CurrHeap));
         TriggerGC,wl_Word (theWord (FAPPLY s CurrHeap));
         EndOfHeap,wl_Word (theWord (FAPPLY s CurrHeap))]`; `0`; `0`] THEN
  REWRITE_TAC[heap_in_memory_store_def; GCP2AUX_FLOOKUP_SOME] THEN
  REWRITE_TAC[FUPDATE_LIST_THM; FDOM_FUPDATE; FAPPLY_FUPDATE_THM; FLOOKUP_UPDATE; IN_INSERT;
              distinctness "store_name"] THEN
  ASM_REWRITE_TAC[theWord_def; ADD_CLAUSES; WORD_MUL_0; WORD_ADD_0] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`curr:A word`; `other:A word`] THEN ASM_REWRITE_TAC[];
    SIMP_TAC[MAP_ZIP; LENGTH_MAP] THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[LENGTH_MAP]]);;

(* GCP2AUX: word_gc_fun_lemma with the copying collector *)
let GCP2AUX_word_gc_fun_Simple = prove
 (gcp2aux_gc_fun_case `data_to_word_config_gc_kind c = data_to_word_Simple`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "gc_combined" o concl)) THEN
  ASM_REWRITE_TAC[gc_combined_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[make_gc_conf_def; gen_gc_conf_FIELDS.ri_accessors] THEN
  gcp2aux_tuple_tac "full_gc" ["r2";"h2";"a3";"c3"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  gcp2aux_subst_vars_tac ["roots2";"heap2";"a2";"n2";"gens2"] THEN
  FIRST_ASSUM(fun th -> if concl th = `c3:bool` then
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "full_gc" th then
    ASSUME_TAC(MATCH_MP GCP2AUX_full_gc_a th) else NO_TAC) THEN
  gcp2aux_subst_vars_tac ["a3"] THEN
  gcp2aux_ispecl_names [("roots2",`r2:((A word_loc)heap_address)list`);
    ("heap2",`h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      heap_element)list`)] word_gc_fun_lemma_Simple THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `stack1:(A word_loc)list` (X_CHOOSE_THEN
    `m1:A word->A word_loc` (X_CHOOSE_THEN `s1:(store_name,A word_loc)fmap`
    STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`stack1:(A word_loc)list`; `m1:A word->A word_loc`;
    `s1:(store_name,A word_loc)fmap`; `limit - heap_length (h2:((A word_loc,
    data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`; `0`] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES]);;

(* GCP2AUX: a bound in bytes carries over to a larger number of words *)
let GCP2AUX_word_ule_bytes = prove
 (`!(w:A word) a b.
     word_ule w (word_mul bytes_in_word (word a)) /\ a <= b /\
     b * (dimindex(:A) DIV 8) < dimword(:A) ==>
     word_ule w (word_mul bytes_in_word (word b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ULE; bytes_in_word_def; word_mul_n2w] THEN
  REWRITE_TAC[VAL_WORD; GSYM dimword_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `dimindex(:A) DIV 8 * a <= dimindex(:A) DIV 8 * b /\
                dimindex(:A) DIV 8 * b < dimword(:A)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dimindex(:A) DIV 8 * a < dimword(:A)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD; GSYM dimword_def]) THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  UNDISCH_TAC `val (w:A word) <= (dimindex(:A) DIV 8 * a) MOD dimword(:A)` THEN
  ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC);;

(* GCP2AUX: a partial move of a word root gives a word *)
let GCP2AUX_word_gen_gc_partial_move_Word = prove
 (`!c (w:A word) i pa old m dm gs rs.
     isWord (FST (word_gen_gc_partial_move c (wl_Word w,i,pa,old,m,dm,gs,rs)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_gen_gc_partial_move_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[isWord_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN COND_CASES_TAC THEN REWRITE_TAC[isWord_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[isWord_def] THEN
  gcp2aux_tuple_tac "memcpy" ["pa1";"m1";"c1"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[isWord_def]);;

(* GCP2AUX: a partial collection whose first root is a word gives a word first root *)
let GCP2AUX_word_gen_gc_partial_full_HD = prove
 (`!c (w:A word) ws curr new len m dm gs rs rs1 i pa m1 c1.
     word_gen_gc_partial_full c (CONS (wl_Word w) ws,curr,new,len,m,dm,gs,rs) =
       (rs1,i,pa,m1,c1) ==>
     isWord (HD rs1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_gen_gc_partial_full_def; word_gen_gc_partial_def;
              word_gen_gc_partial_move_roots_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `w:A word`;
    `word_ushr (gs:A word) (backend_common_word_shift (:A))`; `new:A word`;
    `curr:A word`; `m:A word->A word_loc`; `dm:A word->bool`; `gs:A word`; `rs:A word`]
    GCP2AUX_word_gen_gc_partial_move_Word) THEN
  gcp2aux_tuple_tac "word_gen_gc_partial_move" ["w1";"i1";"pa1";"m2";"c2"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  gcp2aux_tuple_tac "word_gen_gc_partial_move_roots" ["ws2";"i2";"pa2";"m3";"c3"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  gcp2aux_tuple_tac "word_gen_gc_partial_move_ref_list" ["i4";"pa4";"m4";"c4"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  gcp2aux_tuple_tac "word_gen_gc_partial_move_data" ["i5";"pa5";"m5";"c5"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  gcp2aux_tuple_tac "memcpy" ["b6";"m6";"c6"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `rs1:(A word_loc)list`)) THEN
  ASM_REWRITE_TAC[HD]);;

let gcp2aux_hl3_tac : tactic =
  MATCH_MP_TAC LET_TRANS THEN
  EXISTS_TAC `(heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#
    (A word_loc)list)heap_element)list) + 3) * dimindex(:A) DIV 8` THEN
  ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ARITH_TAC;;

(* the statement of word_gc_fun_lemma with an extra hypothesis and variables *)
let gcp2aux_gc_fun_case2 extra (evs:term list) =
  let vs,body = strip_forall gcp2aux_gc_fun_stmt in
  let h,cl = dest_imp body in
  list_mk_forall(vs @ evs, mk_imp(mk_conj(extra,h),cl));;

(* GCP2AUX: word_gc_fun_lemma with the generational collector, partial collection *)
let GCP2AUX_word_gc_fun_partial = prove
 (gcp2aux_gc_fun_case2 `data_to_word_config_gc_kind c = Generational (l:num list) /\
     word_gen_gc_can_do_partial l (s:(store_name,A word_loc)fmap)` [`l:num list`],
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GCP2AUX_heap_in_memory_store_assum o
    CONJ (ASSUME `heap_in_memory_store heap a sp sp1 gens c s (m:A word->A word_loc) dm limit`) o
    K (ASSUME `good_dimindex(:A)`)) THEN
  SUBGOAL_THEN `do_partial c (s:(store_name,A word_loc)fmap)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[do_partial_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_has_const "abs_ml_inv" (concl th) then
    STRIP_ASSUME_TAC(REWRITE_RULE[abs_ml_inv_def; unused_space_inv_def; heap_ok_def;
      gc_kind_inv_def] th) else NO_TAC) THEN
  RULE_ASSUM_TAC(CONV_RULE(CASE_REWRITE_CONV[])) THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "heap_in_memory_store" o concl)) THEN
  REWRITE_TAC[heap_in_memory_store_def; GCP2AUX_FLOOKUP_SOME] THEN STRIP_TAC THEN
  (* the generations *)
  gcp2aux_rw_asm_tac `data_to_word_config_gc_kind c` THEN
  RULE_ASSUM_TAC(CONV_RULE(CASE_REWRITE_CONV[])) THEN
  gcp2aux_subst_vars_tac ["limit"] THEN
  MP_TAC(ISPEC `gens:gen_state` (cases "gen_state")) THEN
  DISCH_THEN(X_CHOOSE_THEN `gn:num` (X_CHOOSE_THEN `gstarts:num list` SUBST_ALL_TAC)) THEN
  FIRST_ASSUM(fun th -> if gcp2aux_has_const "gen_starts_in_store" (concl th) then
    MP_TAC(MATCH_MP gen_starts_in_store_IMP_SOME_Word th) else NO_TAC) THEN
  DISCH_THEN(X_CHOOSE_TAC `wg:A word`) THEN
  FIRST_X_ASSUM(fun th -> if gcp2aux_has_const "gen_starts_in_store" (concl th) then
    MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[gen_starts_in_store_def; injectivity "gc_kind"] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; UNWIND_THM2; FORALL_UNWIND_THM2] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GCP2AUX_FLOOKUP_SOME] o check (fun th ->
    gcp2aux_is_app_eq "FLOOKUP" th)) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l:num list` o check (fun th -> is_forall(concl th) &&
    (try fst(dest_var(fst(dest_forall(concl th)))) = "gen_sizes" with Failure _ -> false))) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[word_gen_gc_can_do_partial_def] o check (fun th ->
    gcp2aux_has_const "word_gen_gc_can_do_partial" (concl th) &&
    not (gcp2aux_has_const "do_partial" (concl th)))) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[theWord_def] THEN STRIP_TAC THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `g0:num` (X_CHOOSE_THEN `gs1:num list`
    SUBST_ALL_TAC)) (ISPEC `gstarts:num list` list_CASES) THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
      `LENGTH ([]:num list) = LENGTH (l:num list)`)) THEN
    REWRITE_TAC[LENGTH] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[LENGTH_EQ_NIL] THEN
    REWRITE_TAC[ASSUME `~(l:num list = [])`];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`g0:num`; `gs1:num list`] o check (fun th ->
    is_forall(concl th) && gcp2aux_has_const "CONS" (concl th) &&
    gcp2aux_has_const "bytes_in_word" (concl th))) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN gcp2aux_subst_vars_tac ["wg"] THEN
  (* the abstract partial collection *)
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "gc_combined" o concl)) THEN
  ASM_REWRITE_TAC[gc_combined_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[make_partial_conf_def; make_gc_conf_def; gen_gc_conf_FIELDS.ri_accessors; HD] THEN
  gcp2aux_tuple_tac "partial_gc" ["rt";"st"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  gcp2aux_subst_vars_tac ["roots2";"heap2";"a2";"n2";"gens2"] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "partial_gc" th then
    MP_TAC(MATCH_MP partial_gc_IMP (CONJ th (ASSUME `gc_state_ok (st:(A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`))) else NO_TAC) THEN
  REWRITE_TAC[gen_gc_partial_conf_FIELDS.ri_accessors] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `cur0:((A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` (X_CHOOSE_THEN
      `refs0:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
      STRIP_ASSUME_TAC)))))))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the allocation pointer does not grow *)
  FIRST_X_ASSUM(fun th -> if gcp2aux_has_const "gen_state_ok" (concl th) then
    STRIP_ASSUME_TAC(REWRITE_RULE[gen_state_ok_def; ALL] th) else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "heap_segment" th &&
      vfree_in `cur0:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
        (concl th) then
    STRIP_ASSUME_TAC(MATCH_MP heap_segment_IMP_split th) else NO_TAC) THEN
  SUBGOAL_THEN `ALL isDataElement (gc_state_old (st:(A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)gc_state))` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if gcp2aux_has_const "data_up_to" (concl th) then
      MP_TAC(REWRITE_RULE[data_up_to_def] th) else NO_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `hd1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      heap_element)list` (X_CHOOSE_THEN `hd2:((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      heap_element)list`; `g0:num`; `a:num`;
      `gc_state_old (st:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`;
      `APPEND (cur0:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
         refs0`; `hd1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      heap_element)list`; `hd2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      heap_element)list`] heap_split_heap_split) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> gcp2aux_has_const "isDataElement" (concl th) &&
      vfree_in `hd1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      heap_element)list` (concl th))) THEN
    ASM_REWRITE_TAC[ALL_APPEND] THEN STRIP_TAC;
    ALL_TAC] THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN
      FIRST_ASSUM(MP_TAC o check (fun th' -> concl th' = `~(l:num list = [])`)) THEN
      REWRITE_TAC[th])
    (X_CHOOSE_THEN `l0:num` (X_CHOOSE_THEN `ls:num list` SUBST_ALL_TAC))
    (ISPEC `l:num list` list_CASES) THEN
  FIRST_ASSUM(fun th -> if gcp2aux_has_const "abs_ml_inv" (concl th) then
    MP_TAC(MATCH_MP abs_ml_inv_GenState_IMP_heap_length_FILTER (CONJ th
      (CONJ (ASSUME `data_to_word_config_gc_kind c = Generational (CONS l0 ls)`)
        (ASSUME `heap_split (a + sp + sp1) heap =
          SOME (APPEND (gc_state_old (st:(A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)gc_state)) cur0,refs0)`)))) else NO_TAC) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if gcp2aux_has_const "similar_data" (concl th) then
    STRIP_ASSUME_TAC(MATCH_MP LIST_REL_similar_data_IMP th) else NO_TAC) THEN
  SUBGOAL_THEN `heap_length (gc_state_old (st:(A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)gc_state)) + heap_length (gc_state_h1 st) <= a` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> gcp2aux_has_const "FILTER" (concl th) &&
      gcp2aux_has_const "gc_state_r1" (concl th) && is_binary "<=" (concl th))) THEN
    ASM_REWRITE_TAC[FILTER_APPEND; heap_length_APPEND] THEN
    SUBGOAL_THEN `FILTER isDataElement (gc_state_old (st:(A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) = gc_state_old st /\
      FILTER isDataElement (gc_state_h1 st) = gc_state_h1 st /\
      FILTER isDataElement (refs0:((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list) = refs0` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[FILTER_EQ_ID]; ALL_TAC] THEN
    (fun (asl,w as g) -> REWRITE_TAC (gcp2aux_eqs_of ["FILTER"] asl) g) THEN
    (fun (asl,w as g) -> RULE_ASSUM_TAC(REWRITE_RULE (gcp2aux_eqs_of ["FILTER"] asl)) g) THEN
    gcp2aux_arith_tac;
    ALL_TAC] THEN
  (* the word side *)
  REWRITE_TAC[word_gc_fun_def] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[theWord_def] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add (a:A word) b) a = b`] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> gcp2aux_has_const "ALL2" (concl th) &&
    gcp2aux_has_const "word_addr" (concl th))) THEN
  REWRITE_TAC[LIST_REL_EQ_MAP; ETA_AX] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && gcp2aux_has_const "Globals" (concl th) &&
      gcp2aux_has_const "MAP" (concl th) then REWRITE_TAC[th] else NO_TAC) THEN
  gcp2aux_tuple_tac "word_gen_gc_partial_full" ["rw";"i1";"pa1";"m1";"c2"] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "word_gen_gc_partial_full" th
    then REWRITE_TAC[th] else NO_TAC) THEN
  CASE_REWRITE_TAC[] THEN
  gcp2aux_ispecl_names [("s1",`st:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      gc_state`); ("frame",`set_sep_emp:(A word#A word_loc->bool)->bool`);
    ("c1",`c2:bool`); ("roots",`hs:((A word_loc)heap_address)list`);
    ("roots1",`rt:((A word_loc)heap_address)list`); ("roots1'",`rw:(A word_loc)list`);
    ("new",`other:A word`);
    ("gen_conf",`(gen_gc_partial_conf_REC (heap_length (heap:((A word_loc,
       data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))
       (isMutTag o FST) g0 (a + sp + sp1)):(data_to_word_memoryProof_tag#
       (A word_loc)list)gen_gc_partial_conf`); ("conf",`c:data_to_word_config`)]
    word_gen_gc_partial_full_thm THEN
  REWRITE_TAC[gen_gc_partial_conf_FIELDS.ri_accessors; SEP_CLAUSES; o_THM] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [gcp2aux_hl3_tac;
      REWRITE_TAC[ends_with_refs_def] THEN
      MAP_EVERY EXISTS_TAC [`h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
        heap_element)list`; `h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
        heap_element)list`] THEN ASM_REWRITE_TAC[];
      gcp2aux_arith_tac;
      gcp2aux_hl3_tac;
      gcp2aux_arith_tac;
      FIRST_ASSUM(fun th -> if is_comb(concl th) &&
          rand(concl th) = `fun2set (m:A word->A word_loc,dm)` then
        ACCEPT_TAC(REWRITE_RULE[word_heap_heap_expand] th) else NO_TAC)];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `current1:((A word_loc,data_to_word_memoryProof_tag#
    (A word_loc)list)heap_element)list` (X_CHOOSE_THEN `refs1:((A word_loc,
    data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` STRIP_ASSUME_TAC)) THEN
  gcp2aux_subst_vars_tac ["rw";"i1";"pa1"] THEN
  (* the space checks *)
  SUBGOAL_THEN `heap_length (APPEND (gc_state_old (st:(A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) (gc_state_h1 st)) +
      gc_state_n st = a + sp + sp1` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if gcp2aux_has_const "heap_expand" (concl th) &&
        gcp2aux_is_app_eq "heap_length" th then
      MP_TAC(REWRITE_RULE[heap_length_APPEND; gc_shared_heap_length_heap_expand] th)
      else NO_TAC) THEN
    REWRITE_TAC[heap_length_APPEND] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word_add curr (word_mul bytes_in_word (word (a + sp + sp1))))
      (word_add curr (word_mul bytes_in_word (word (heap_length (APPEND (gc_state_old
      (st:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))
      (gc_state_h1 st)))))) = word_mul bytes_in_word (word (gc_state_n st)):A word`
    (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && rhs(concl th) = `a + sp + sp1` then
      REWRITE_TAC[GSYM th] else NO_TAC) THEN
    REWRITE_TAC[GSYM word_add_n2w] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_ule (theWord (FAPPLY (s:(store_name,A word_loc)fmap) AllocSize))
      (word_mul bytes_in_word (word (gc_state_n (st:(A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)gc_state))))` ASSUME_TAC THENL
   [MATCH_MP_TAC GCP2AUX_word_ule_bytes THEN EXISTS_TAC `sp1:num` THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> gcp2aux_has_const "word_ule" (concl th) &&
        gcp2aux_has_const "AllocSize" (concl th))) THEN
      MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM word_add_n2w; ADD_ASSOC] THEN CONV_TAC WORD_RULE;
      gcp2aux_arith_tac;
      MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#
        (A word_loc)list)heap_element)list) * dimindex(:A) DIV 8` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN gcp2aux_arith_tac;
        gcp2aux_hl3_tac]];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_has_const "word_ule" (concl th) &&
      gcp2aux_has_const "gc_state_n" (concl th) then
    ASSUME_TAC(MATCH_MP new_trig_ok (CONJ th (ASSUME `good_dimindex(:A)`))) else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  (* the new store *)
  MP_TAC(ISPECL [`gc_state_n (st:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      gc_state)`; `theWord (FAPPLY (s:(store_name,A word_loc)fmap) AllocSize)`;
    `CONS (l0:num) ls`] new_trig_LESS_EQ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k9:num` STRIP_ASSUME_TAC) THEN
  gcp2aux_rw_asm_tac `new_trig (word_mul bytes_in_word (word (gc_state_n (st:(A word_loc,
    data_to_word_memoryProof_tag#(A word_loc)list)gc_state))):A word)
    (theWord (FAPPLY (s:(store_name,A word_loc)fmap) AllocSize)) (CONS (l0:num) ls)` THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add (a:A word) b) a = b`] THEN
  (fun (asl,w as g) -> let tm = rand(lhs(fst(dest_conj(snd(strip_exists w))))) in
    (EXISTS_TAC (el 0 (gcp2aux_strip_pair tm)) THEN EXISTS_TAC (el 1 (gcp2aux_strip_pair tm)) THEN
     EXISTS_TAC (el 2 (gcp2aux_strip_pair tm))) g) THEN
  MAP_EVERY EXISTS_TAC [`k9:num`; `gc_state_n (st:(A word_loc,data_to_word_memoryProof_tag#
    (A word_loc)list)gc_state) - k9`] THEN
  REWRITE_TAC[heap_in_memory_store_def; GCP2AUX_FLOOKUP_SOME] THEN
  REWRITE_TAC[FUPDATE_LIST_THM; FDOM_FUPDATE; FAPPLY_FUPDATE_THM; FLOOKUP_UPDATE; IN_INSERT;
              distinctness "store_name"; injectivity "store_name"] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `heap_length (APPEND (APPEND (APPEND (gc_state_old (st:(A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) (gc_state_h1 st))
      (heap_expand (gc_state_n st))) (gc_state_r1 st)) =
      heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      heap_element)list)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "heap_split" th &&
        vfree_in `refs0:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
          heap_element)list` (concl th) &&
        gcp2aux_has_const "APPEND" (concl th) then
      MP_TAC(MATCH_MP heap_split_heap_length th) else NO_TAC) THEN
    REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand] THEN
    STRIP_TAC THEN gcp2aux_arith_tac;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_has_const "glob_real_inv" (concl th) then
    MP_TAC(REWRITE_RULE[glob_real_inv_def] th) else NO_TAC) THEN
  REWRITE_TAC[GCP2AUX_FLOOKUP_SOME] THEN
  DISCH_THEN(X_CHOOSE_THEN `wglob:A word` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `isWord (HD (MAP (word_addr c) (rt:((A word_loc)heap_address)list)))`
    ASSUME_TAC THENL
   [FIRST_ASSUM(fun eq -> if is_eq(concl eq) && gcp2aux_has_const "Globals" (concl eq) &&
        gcp2aux_has_const "MAP" (concl eq) then
      FIRST_ASSUM(fun gw -> if is_eq(concl gw) && is_comb(lhs(concl gw)) &&
          gcp2aux_has_const "Globals" (lhs(concl gw)) && not (gcp2aux_has_const "MAP" (concl gw))
          && not (gcp2aux_has_const "glob_real" (concl gw))
        then FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "word_gen_gc_partial_full" th then
          ACCEPT_TAC(MATCH_MP GCP2AUX_word_gen_gc_partial_full_HD (REWRITE_RULE[gw]
            (REWRITE_RULE[GSYM eq] th)))
          else NO_TAC) else NO_TAC) else NO_TAC);
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && gcp2aux_has_const "heap_expand" (concl th) &&
      gcp2aux_has_const "gc_state_r1" (concl th) && gcp2aux_is_app_eq "heap_length" th then
    REWRITE_TAC[th] else NO_TAC) THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY EXISTS_TAC [`curr:A word`; `other:A word`] THEN
    ASM_REWRITE_TAC[injectivity "word_loc"; glob_real_inv] THEN REPEAT CONJ_TAC THENL
     [gcp2aux_addr_hl_tac;
      gcp2aux_addr_hl_tac;
      SUBGOAL_THEN `(g0 + heap_length (gc_state_h1 (st:(A word_loc,data_to_word_memoryProof_tag#
         (A word_loc)list)gc_state))) + k9 + gc_state_n st - k9 = a + sp + sp1` SUBST1_TAC THENL
       [gcp2aux_arith_tac; REFL_TAC];
      REWRITE_TAC[gen_starts_in_store_def] THEN GEN_TAC THEN
      REWRITE_TAC[ASSUME `data_to_word_config_gc_kind c = Generational (CONS l0 ls)`;
                  injectivity "gc_kind"] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[LENGTH_MAP; MAP; K_THM; CONS_11] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        is_var(rhs(concl th)) && fst(dest_var(rhs(concl th))) = "x")) THEN
      gcp2aux_addr_hl_tac;
      REWRITE_TAC[word_heap_APPEND; word_heap_heap_expand] THEN
      gcp2aux_sep_addr_tac (REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand;
        ASSUME `heap_length (gc_state_old (st:(A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)gc_state)) = g0`] THEN gcp2aux_addr_tac)];
    gcp2aux_arith_tac;
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[wl_has_space_def; wl_get_store_def; wl_state_INFO.ri_accfupds; K_THM;
      FLOOKUP_UPDATE; distinctness "store_name"; injectivity "store_name"] THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_RULE `word_sub (word_add (a:A word) b) a = b`; option_INJ] THEN
    FIRST_ASSUM(MP_TAC o SPEC `CONS (l0:num) ls` o check (fun th -> is_forall(concl th) &&
      gcp2aux_has_const "word_ule" (concl th))) THEN
    (fun (asl,w as g) -> REWRITE_TAC (gcp2aux_eqs_of ["new_trig"] asl) g) THEN
    ASM_REWRITE_TAC[theWord_def; WORD_ULE];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
      is_var(rhs(concl th)) && fst(dest_var(rhs(concl th))) = "l'")) THEN
    ASM_MESON_TAC[];
    SUBGOAL_THEN `LENGTH (rt:((A word_loc)heap_address)list) =
        SUC (LENGTH (stack:(data_v#A word_loc)list))` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_eq(concl th) && gcp2aux_has_const "Globals" (concl th) &&
          gcp2aux_has_const "MAP" (concl th) then
        MP_TAC(AP_TERM `LENGTH:(A word_loc)list->num` th) else NO_TAC) THEN
      REWRITE_TAC[LENGTH; LENGTH_MAP] THEN gcp2aux_arith_tac;
      ALL_TAC] THEN
    DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `r0:(A word_loc)heap_address`
      (X_CHOOSE_THEN `rts:((A word_loc)heap_address)list` SUBST_ALL_TAC))
      (ISPEC `rt:((A word_loc)heap_address)list` list_CASES) THENL
     [gcp2aux_arith_tac; ALL_TAC] THEN
    REWRITE_TAC[MAP; HD; TL] THEN
    SUBGOAL_THEN `LENGTH (rts:((A word_loc)heap_address)list) =
        LENGTH (stack:(data_v#A word_loc)list)` ASSUME_TAC THENL
     [gcp2aux_arith_tac; ALL_TAC] THEN
    ASM_SIMP_TAC[MAP_ZIP; LENGTH_MAP];
    SUBGOAL_THEN `LENGTH (rt:((A word_loc)heap_address)list) =
        SUC (LENGTH (stack:(data_v#A word_loc)list))` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_eq(concl th) && gcp2aux_has_const "Globals" (concl th) &&
          gcp2aux_has_const "MAP" (concl th) then
        MP_TAC(AP_TERM `LENGTH:(A word_loc)list->num` th) else NO_TAC) THEN
      REWRITE_TAC[LENGTH; LENGTH_MAP] THEN gcp2aux_arith_tac;
      ALL_TAC] THEN
    DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `r0:(A word_loc)heap_address`
      (X_CHOOSE_THEN `rts:((A word_loc)heap_address)list` SUBST_ALL_TAC))
      (ISPEC `rt:((A word_loc)heap_address)list` list_CASES) THEN
    REWRITE_TAC[MAP; TL; LENGTH_MAP] THEN gcp2aux_arith_tac]);;

(* GCP2AUX: the allocation request fits below a large enough free space *)
let GCP2AUX_alloc_size_ule = prove
 (`!k n. k <= n /\ n * (dimindex(:A) DIV 8) < dimword(:A) ==>
         word_ule (alloc_size k:A word) (word_mul bytes_in_word (word n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `k * dimindex(:A) DIV 8 <= n * dimindex(:A) DIV 8` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ALL_TAC] THEN
  SUBGOAL_THEN `k * dimindex(:A) DIV 8 < dimword(:A)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[alloc_size_def; bytes_in_word_def; word_mul_n2w; WORD_ULE] THEN
  REWRITE_TAC[VAL_WORD; GSYM dimword_def] THEN
  SUBGOAL_THEN `dimindex(:A) DIV 8 * n < dimword(:A)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN ASM_REWRITE_TAC[]);;

(* GCP2AUX: alloc_size_LEQ_IMP, needed before its place in the script *)
let GCP2AUX_alloc_size_LEQ = prove
 (`!k sp1. word_ule (alloc_size k) (word_mul bytes_in_word (word sp1):A word) /\
           sp1 * (dimindex (:A) DIV 8) < dimword (:A) /\
           good_dimindex (:A) ==> k <= sp1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[alloc_size_def; bytes_in_word_def; word_mul_n2w; WORD_ULE] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `0 < dimindex(:A) DIV 8` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `val (word (dimindex(:A) DIV 8 * sp1):A word) = sp1 * dimindex(:A) DIV 8`
    ASSUME_TAC THENL
   [SUBGOAL_THEN `dimindex(:A) DIV 8 * sp1 = sp1 * dimindex(:A) DIV 8` SUBST1_TAC THENL
     [REWRITE_TAC[MULT_SYM]; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD; GSYM dimword_def] THEN ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> gcp2aux_has_const "val" (concl th) &&
                                          is_comb (concl th) &&
                                          gcp2aux_has_const "COND" (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[VAL_WORD_NEG_1] THENL
   [REWRITE_TAC[VAL_WORD; GSYM dimword_def] THEN ASM_SIMP_TAC[MOD_LT] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    REWRITE_TAC[GSYM dimword_def] THEN DISCH_TAC THEN
    SUBGOAL_THEN `sp1 * dimindex(:A) DIV 8 = dimword(:A) - 1` MP_TAC THENL
     [UNDISCH_TAC `sp1 * dimindex (:A) DIV 8 < dimword (:A)` THEN
      UNDISCH_TAC `dimword (:A) - 1 <= sp1 * dimindex (:A) DIV 8` THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
    UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[EVEN_MULT] THEN CONV_TAC NUM_REDUCE_CONV]);;

(* GCP2AUX: the new trigger leaves room for the allocation request *)
let GCP2AUX_new_trig_alloc = prove
 (`!n k (l:num list) k9.
     new_trig (word_mul bytes_in_word (word n):A word) (alloc_size k) l =
       word_mul bytes_in_word (word k9) /\
     k <= n /\ n * (dimindex(:A) DIV 8) < dimword(:A) /\ k9 <= n /\ good_dimindex(:A) ==>
     k <= k9`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC GCP2AUX_alloc_size_LEQ THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> gcp2aux_has_const "new_trig" (concl th)))
    THEN MATCH_MP_TAC new_trig_ok THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GCP2AUX_alloc_size_ule THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `n * dimindex(:A) DIV 8` THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL]]);;



(* GCP2AUX: a generational move of a word root gives a word *)
let GCP2AUX_word_gen_gc_move_Word = prove
 (`!c (w:A word) i pa ib pb old m dm.
     isWord (FST (word_gen_gc_move c (wl_Word w,i,pa,ib,pb,old,m,dm)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_gen_gc_move_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[isWord_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN COND_CASES_TAC THEN REWRITE_TAC[isWord_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[isWord_def] THEN
  gcp2aux_tuple_tac "memcpy" ["pa1";"m1";"c1"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[isWord_def]);;

(* GCP2AUX: a generational collection whose first root is a word gives a word first root *)
let GCP2AUX_word_gen_gc_HD = prove
 (`!c (w:A word) ws curr new len m dm rs i pa ib pb m1 c1.
     word_gen_gc c (CONS (wl_Word w) ws,curr,new,len,m,dm) = (rs,i,pa,ib,pb,m1,c1) ==>
     isWord (HD rs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_gen_gc_def; word_gen_gc_move_roots_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `w:A word`; `word 0:A word`; `new:A word`;
    `word_ushr (len:A word) (backend_common_word_shift (:A))`; `word_add (new:A word) len`;
    `curr:A word`; `m:A word->A word_loc`; `dm:A word->bool`] GCP2AUX_word_gen_gc_move_Word) THEN
  gcp2aux_tuple_tac "word_gen_gc_move" ["w1";"i1";"pa1";"ib1";"pb1";"m2";"c2"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  gcp2aux_tuple_tac "word_gen_gc_move_roots" ["ws2";"i2";"pa2";"ib2";"pb2";"m3";"c3"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  gcp2aux_tuple_tac "word_gen_gc_move_loop" ["i4";"pa4";"ib4";"pb4";"m4";"c4"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `rs:(A word_loc)list`)) THEN
  ASM_REWRITE_TAC[HD]);;

(* GCP2AUX: word_gc_fun_lemma with the generational collector, full collection *)
let GCP2AUX_word_gc_fun_gen = prove
 (gcp2aux_gc_fun_case2 `data_to_word_config_gc_kind c = Generational (l:num list) /\
     ~word_gen_gc_can_do_partial l (s:(store_name,A word_loc)fmap)` [`l:num list`],
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GCP2AUX_heap_in_memory_store_assum o
    CONJ (ASSUME `heap_in_memory_store heap a sp sp1 gens c s (m:A word->A word_loc) dm limit`) o
    K (ASSUME `good_dimindex(:A)`)) THEN
  SUBGOAL_THEN `~do_partial c (s:(store_name,A word_loc)fmap)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[do_partial_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_has_const "abs_ml_inv" (concl th) then
    STRIP_ASSUME_TAC(REWRITE_RULE[abs_ml_inv_def; unused_space_inv_def; heap_ok_def;
      gc_kind_inv_def] th) else NO_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "heap_in_memory_store" o concl)) THEN
  REWRITE_TAC[heap_in_memory_store_def; GCP2AUX_FLOOKUP_SOME] THEN STRIP_TAC THEN
  gcp2aux_rw_asm_tac `data_to_word_config_gc_kind c` THEN
  RULE_ASSUM_TAC(CONV_RULE(CASE_REWRITE_CONV[])) THEN
  gcp2aux_subst_vars_tac ["limit"] THEN
  (* the abstract generational collection *)
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "gc_combined" o concl)) THEN
  ASM_REWRITE_TAC[gc_combined_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  gcp2aux_tuple_tac "gen_gc" ["rt";"st"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  gcp2aux_subst_vars_tac ["roots2";"heap2";"a2";"n2";"gens2"] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "gen_gc" th then
    ASSUME_TAC(MATCH_MP gen_gc_LENGTH th) else NO_TAC) THEN
  SUBGOAL_THEN `gc_state_a (st:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      gc_state) = heap_length (gc_state_h1 st)` ASSUME_TAC THENL
   [MATCH_MP_TAC gen_gc_a THEN
    MAP_EVERY EXISTS_TAC [`make_gc_conf (heap_length (heap:((A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)):
      (data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`;
      `hs:((A word_loc)heap_address)list`; `heap:((A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `rt:((A word_loc)heap_address)list`] THEN
    ASM_REWRITE_TAC[make_gc_conf_def; gen_gc_conf_FIELDS.ri_accessors; heap_ok_def] THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> gcp2aux_is_app_eq "gen_gc" th)) THEN
    REWRITE_TAC[make_gc_conf_def];
    ALL_TAC] THEN
  (* the word side *)
  REWRITE_TAC[word_gc_fun_def] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[theWord_def] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> gcp2aux_has_const "ALL2" (concl th) &&
    gcp2aux_has_const "word_addr" (concl th))) THEN
  REWRITE_TAC[LIST_REL_EQ_MAP; ETA_AX] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && gcp2aux_has_const "Globals" (concl th) &&
      gcp2aux_has_const "MAP" (concl th) then REWRITE_TAC[th] else NO_TAC) THEN
  gcp2aux_tuple_tac "word_gen_gc" ["rw";"i1";"pa1";"ib1";"pb1";"m1";"c2"] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "word_gen_gc" th
    then REWRITE_TAC[th] else NO_TAC) THEN
  CASE_REWRITE_TAC[] THEN
  gcp2aux_ispecl_names [("s1",`st:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      gc_state`); ("frame",`set_sep_emp:(A word#A word_loc->bool)->bool`);
    ("c1",`c2:bool`); ("roots",`hs:((A word_loc)heap_address)list`);
    ("roots1",`rt:((A word_loc)heap_address)list`); ("roots1'",`rw:(A word_loc)list`);
    ("new",`other:A word`);
    ("gen_conf",`(make_gc_conf (heap_length (heap:((A word_loc,
       data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))):
       (data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`);
    ("conf",`c:data_to_word_config`)] word_gen_gc_thm THEN
  REWRITE_TAC[make_gc_conf_def; gen_gc_conf_FIELDS.ri_accessors; SEP_CLAUSES; o_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[make_gc_conf_def]) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [gcp2aux_hl3_tac; gcp2aux_arith_tac; gcp2aux_arith_tac;
      FIRST_ASSUM(fun th -> if is_comb(concl th) &&
          rand(concl th) = `fun2set (m:A word->A word_loc,dm)` then
        ACCEPT_TAC(REWRITE_RULE[word_heap_heap_expand] th) else NO_TAC)];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs1:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  gcp2aux_subst_vars_tac ["rw";"i1";"ib1";"pa1";"pb1"] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add (a:A word) b) a = b`] THEN
  FIRST_ASSUM(fun th -> if concl th = `c2:bool` then REWRITE_TAC[th] else NO_TAC) THEN
  SUBGOAL_THEN `word_sub (word_add other (word_mul bytes_in_word (word (heap_length
      (gc_state_h1 (st:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) +
      gc_state_n st)))) (word_add other (word_mul bytes_in_word (word (heap_length
      (gc_state_h1 st))))) = word_mul bytes_in_word (word (gc_state_n st)):A word`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM word_add_n2w] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  MP_TAC(ISPECL [`gc_state_n (st:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      gc_state)`; `theWord (FAPPLY (s:(store_name,A word_loc)fmap) AllocSize)`;
    `l:num list`] new_trig_LESS_EQ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k9:num` STRIP_ASSUME_TAC) THEN
  gcp2aux_rw_asm_tac `new_trig (word_mul bytes_in_word (word (LENGTH (xs1:(A word_loc)list))):A word)
    (theWord (FAPPLY (s:(store_name,A word_loc)fmap) AllocSize)) (l:num list)` THEN
  (fun (asl,w as g) -> let tm = rand(lhs(fst(dest_conj(snd(strip_exists w))))) in
    (EXISTS_TAC (el 0 (gcp2aux_strip_pair tm)) THEN EXISTS_TAC (el 1 (gcp2aux_strip_pair tm)) THEN
     EXISTS_TAC (el 2 (gcp2aux_strip_pair tm))) g) THEN
  MAP_EVERY EXISTS_TAC [`k9:num`; `LENGTH (xs1:(A word_loc)list) - k9`] THEN
  REWRITE_TAC[heap_in_memory_store_def; GCP2AUX_FLOOKUP_SOME] THEN
  REWRITE_TAC[FUPDATE_LIST_THM; FDOM_FUPDATE; FAPPLY_FUPDATE_THM; FLOOKUP_UPDATE; IN_INSERT;
              distinctness "store_name"; injectivity "store_name"] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `heap_length (APPEND (APPEND (gc_state_h1 (st:(A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)gc_state))
      (heap_expand (LENGTH (xs1:(A word_loc)list)))) (gc_state_r1 st)) =
      heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      heap_element)list)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[len_inv_def] o check (fun th ->
      gcp2aux_has_const "len_inv" (concl th))) THEN
    ASM_REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand; APPEND;
                    heap_length_NIL] THEN
    gcp2aux_arith_tac;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if gcp2aux_has_const "glob_real_inv" (concl th) then
    MP_TAC(REWRITE_RULE[glob_real_inv_def] th) else NO_TAC) THEN
  REWRITE_TAC[GCP2AUX_FLOOKUP_SOME] THEN
  DISCH_THEN(X_CHOOSE_THEN `wglob:A word` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `isWord (HD (MAP (word_addr c) (rt:((A word_loc)heap_address)list)))`
    ASSUME_TAC THENL
   [FIRST_ASSUM(fun eq -> if is_eq(concl eq) && gcp2aux_has_const "Globals" (concl eq) &&
        gcp2aux_has_const "MAP" (concl eq) then
      FIRST_ASSUM(fun gw -> if is_eq(concl gw) && is_comb(lhs(concl gw)) &&
          gcp2aux_has_const "Globals" (lhs(concl gw)) && not (gcp2aux_has_const "MAP" (concl gw))
          && not (gcp2aux_has_const "glob_real" (concl gw))
        then FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "word_gen_gc" th then
          ACCEPT_TAC(MATCH_MP GCP2AUX_word_gen_gc_HD (REWRITE_RULE[gw]
            (REWRITE_RULE[GSYM eq] th)))
          else NO_TAC) else NO_TAC) else NO_TAC);
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && gcp2aux_has_const "heap_expand" (concl th) &&
      gcp2aux_has_const "gc_state_r1" (concl th) && gcp2aux_is_app_eq "heap_length" th then
    REWRITE_TAC[th] else NO_TAC) THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY EXISTS_TAC [`other:A word`; `curr:A word`] THEN
    ASM_REWRITE_TAC[injectivity "word_loc"; glob_real_inv] THEN REPEAT CONJ_TAC THENL
     [gcp2aux_addr_tac;
      SUBGOAL_THEN `heap_length (gc_state_h1 (st:(A word_loc,data_to_word_memoryProof_tag#
         (A word_loc)list)gc_state)) + k9 + LENGTH (xs1:(A word_loc)list) - k9 =
         heap_length (gc_state_h1 st) + LENGTH xs1` SUBST1_TAC THENL
       [gcp2aux_arith_tac; REFL_TAC];
      REWRITE_TAC[gen_starts_in_store_def] THEN GEN_TAC THEN
      REWRITE_TAC[ASSUME `data_to_word_config_gc_kind c = Generational (l:num list)`;
                  injectivity "gc_kind"] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[LENGTH_MAP] THEN REPEAT STRIP_TAC THEN
      POP_ASSUM MP_TAC THEN
      DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `l0:num` (X_CHOOSE_THEN `ls:num list`
        SUBST1_TAC)) (ISPEC `l:num list` list_CASES) THEN
      REWRITE_TAC[MAP; K_THM; CONS_11; distinctness "list"] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(fun th -> if is_comb(concl th) &&
          rand(concl th) = `fun2set (m1:A word->A word_loc,dm)` then
        MP_TAC(MATCH_MP word_heap_eq_word_list th) else NO_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `ys:(A word_loc)list` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(fun th -> if is_comb(concl th) &&
          rand(concl th) = `fun2set (m1:A word->A word_loc,dm)` then
        (fun (asl,w as g) -> ASSUME_TAC(REWRITE_RULE (word_heap_parts_def :: APPEND_NIL ::
           APPEND :: gcp2aux_eqs_of ["gc_state_h2";"gc_state_r4";"gc_state_r3";"gc_state_r2"]
           asl) th) g)
        else NO_TAC) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL; APPEND]) THEN
      REWRITE_TAC[word_heap_APPEND; word_heap_heap_expand; word_list_exists_def; SEP_CLAUSES;
                  SEP_EXISTS_THM] THEN
      MAP_EVERY EXISTS_TAC [`xs1:(A word_loc)list`; `ys:(A word_loc)list`] THEN
      gcp2aux_goal_cond_tac THEN CONJ_TAC THENL [gcp2aux_arith_tac; ALL_TAC] THEN
      gcp2aux_goal_cond_tac THEN CONJ_TAC THENL [gcp2aux_arith_tac; ALL_TAC] THEN
      gcp2aux_sep_addr_tac (REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand]
        THEN gcp2aux_addr_tac)];
    gcp2aux_arith_tac;
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
      is_var(rhs(concl th)) && fst(dest_var(rhs(concl th))) = "l'")) THEN
    ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC GCP2AUX_new_trig_alloc THEN
    MAP_EVERY EXISTS_TAC [`LENGTH (xs1:(A word_loc)list)`; `l:num list`] THEN
    FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "new_trig" th then
      ASSUME_TAC(REWRITE_RULE[ASSUME `FAPPLY (s:(store_name,A word_loc)fmap) AllocSize =
        wl_Word (alloc_size k)`; theWord_def] th) else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list) * dimindex(:A) DIV 8` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
      FIRST_ASSUM(fun th -> if is_eq(concl th) && gcp2aux_has_const "heap_expand" (concl th) &&
          gcp2aux_has_const "gc_state_r1" (concl th) && gcp2aux_is_app_eq "heap_length" th then
        MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand] THEN ARITH_TAC;
      gcp2aux_hl3_tac];
    SUBGOAL_THEN `LENGTH (rt:((A word_loc)heap_address)list) =
        SUC (LENGTH (stack:(data_v#A word_loc)list))` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_eq(concl th) && gcp2aux_has_const "Globals" (concl th) &&
          gcp2aux_has_const "MAP" (concl th) then
        MP_TAC(AP_TERM `LENGTH:(A word_loc)list->num` th) else NO_TAC) THEN
      REWRITE_TAC[LENGTH; LENGTH_MAP] THEN gcp2aux_arith_tac;
      ALL_TAC] THEN
    DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `r0:(A word_loc)heap_address`
      (X_CHOOSE_THEN `rts:((A word_loc)heap_address)list` SUBST_ALL_TAC))
      (ISPEC `rt:((A word_loc)heap_address)list` list_CASES) THENL
     [gcp2aux_arith_tac; ALL_TAC] THEN
    REWRITE_TAC[MAP; HD; TL] THEN
    SUBGOAL_THEN `LENGTH (rts:((A word_loc)heap_address)list) =
        LENGTH (stack:(data_v#A word_loc)list)` ASSUME_TAC THENL
     [gcp2aux_arith_tac; ALL_TAC] THEN
    ASM_SIMP_TAC[MAP_ZIP; LENGTH_MAP];
    SUBGOAL_THEN `LENGTH (rt:((A word_loc)heap_address)list) =
        SUC (LENGTH (stack:(data_v#A word_loc)list))` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_eq(concl th) && gcp2aux_has_const "Globals" (concl th) &&
          gcp2aux_has_const "MAP" (concl th) then
        MP_TAC(AP_TERM `LENGTH:(A word_loc)list->num` th) else NO_TAC) THEN
      REWRITE_TAC[LENGTH; LENGTH_MAP] THEN gcp2aux_arith_tac;
      ALL_TAC] THEN
    DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `r0:(A word_loc)heap_address`
      (X_CHOOSE_THEN `rts:((A word_loc)heap_address)list` SUBST_ALL_TAC))
      (ISPEC `rt:((A word_loc)heap_address)list` list_CASES) THEN
    REWRITE_TAC[MAP; TL; LENGTH_MAP] THEN gcp2aux_arith_tac]);;

(* HOL4 line 4045 (HOL4: Q.prove ... |> GEN_ALL |> SIMP_RULE (srw_ss())      *)
(* [LET_DEF,PULL_EXISTS,GSYM CONJ_ASSOC] |> SPEC_ALL: the unused existential *)
(* a1 dropped; HOL4 <| store := s1 |> is wl_state_store_fupd (K s1) ARB)     *)
let word_gc_fun_lemma = prove
 (`!c v stack refs hs heap be a sp sp1 gens limit ts s (m:A word->A word_loc) dm
    roots2 heap2 a2 n2 gens2 k.
     abs_ml_inv c (CONS v (MAP FST stack)) refs (hs,heap,be,a,sp,sp1,gens) limit ts /\
     good_dimindex (:A) /\
     heap_in_memory_store heap a sp sp1 gens c s m dm limit /\
     ALL2 (\v w. word_addr c v = w) hs (CONS (FAPPLY s Globals) (MAP SND stack)) /\
     gc_combined (make_gc_conf limit) (data_to_word_config_gc_kind c)
       (hs,heap,gens,a + sp + sp1,do_partial c s) =
       (roots2,heap2,a2,n2,gens2,T) ==>
     ?stack1 m1 s1 k2 k3.
       word_gc_fun c (MAP SND stack,m,dm,s) = SOME (stack1,m1,s1) /\
       heap_in_memory_store heap2 a2 k2 k3 gens2 c s1 m1 dm limit /\ k2 + k3 = n2 /\
       (!l. FLOOKUP s AllocSize = SOME (wl_Word (alloc_size k)) /\
            data_to_word_config_gc_kind c = Generational l /\
            word_gen_gc_can_do_partial l s ==>
            wl_has_space (wl_Word (alloc_size k:A word))
              (wl_state_store_fupd (K s1) (ARB:(A,C,FFI)wl_state)) = SOME T) /\
       (data_to_word_config_gc_kind c = data_to_word_None \/
        data_to_word_config_gc_kind c = data_to_word_Simple ==> k3 = 0) /\
       (!l k. FLOOKUP s AllocSize = SOME (wl_Word (alloc_size k)) /\
              data_to_word_config_gc_kind c = Generational l /\
              ~word_gen_gc_can_do_partial l s /\
              k <= n2 ==> k <= k2) /\
       ALL2 (\v w. word_addr c v = (w:A word_loc)) roots2
         (CONS (FAPPLY s1 Globals) (MAP SND (ZIP (MAP FST stack) stack1))) /\
       LENGTH stack1 = LENGTH stack`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `l:num list` ASSUME_TAC))
    (ISPEC `data_to_word_config_gc_kind c` (cases "gc_kind")) THENL
   [MATCH_MP_TAC(SPEC_ALL GCP2AUX_word_gc_fun_None) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(SPEC_ALL GCP2AUX_word_gc_fun_Simple) THEN ASM_REWRITE_TAC[];
    ASM_CASES_TAC `word_gen_gc_can_do_partial (l:num list) (s:(store_name,A word_loc)fmap)`
    THENL
     [MATCH_MP_TAC(SPEC_ALL GCP2AUX_word_gc_fun_partial) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SPEC_ALL GCP2AUX_word_gc_fun_gen) THEN ASM_REWRITE_TAC[]]]);;

(* HOL4 line 4321 (local) *)
let abs_ml_inv_ADD = prove
 (`!c xs refs ys
    (heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
    be a2 k2 k3 gens2 limit ts l.
     abs_ml_inv c xs refs (ys,heap2,be,a2,k2 + k3,0,gens2) limit ts /\
     data_to_word_config_gc_kind c = Generational l ==>
     abs_ml_inv c xs refs (ys,heap2,be,a2,k2,k3,gens2) limit ts`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def; gc_kind_inv_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[ADD_CLAUSES; ADD_ASSOC] THEN SIMP_TAC[]);;

(* HOL4 line 4330 *)
let alloc_size_check = prove
 (`!k2 k. val (word_mul bytes_in_word (word k2):A word) < val (alloc_size k:A word) ==>
          k2 * (dimindex (:A) DIV 8) < dimword (:A) /\ good_dimindex (:A) ==>
          k2 < k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[alloc_size_def; bytes_in_word_def; word_mul_n2w] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  SUBGOAL_THEN `0 < dimindex(:A) DIV 8` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD; GSYM dimword_def] THEN
  MP_TAC(SPECL [`dimindex (:A) DIV 8 * k2`; `dimword(:A)`] MOD_LT) THEN
  ANTS_TAC THENL [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[VAL_WORD; GSYM dimword_def] THEN ASM_SIMP_TAC[MOD_LT] THEN
    REWRITE_TAC[ARITH_RULE `d * k2 < k * d <=> k2 * d < k * d`; LT_MULT_RCANCEL] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `k2 * dimindex(:A) DIV 8 < k * dimindex(:A) DIV 8` MP_TAC THENL
   [UNDISCH_TAC `~(k * dimindex (:A) DIV 8 < dimword (:A))` THEN
    UNDISCH_TAC `k2 * dimindex (:A) DIV 8 < dimword (:A)` THEN ARITH_TAC;
    REWRITE_TAC[LT_MULT_RCANCEL] THEN SIMP_TAC[]]);;

(* HOL4 line 4344 *)
let alloc_size_LEQ_IMP = prove
 (`!k sp1. word_ule (alloc_size k) (word_mul bytes_in_word (word sp1):A word) /\
           sp1 * (dimindex (:A) DIV 8) < dimword (:A) /\
           good_dimindex (:A) ==> k <= sp1`,
  MATCH_ACCEPT_TAC GCP2AUX_alloc_size_LEQ);;

(* GCP2AUX: a failing space check after a collection bounds the free space *)
let GCP2AUX_has_space_F = prove
 (`!heap a sp sp1 gens c s1 (m:A word->A word_loc) dm limit k (t:(A,C,FFI)wl_state).
     heap_in_memory_store heap a sp sp1 gens c s1 m dm limit /\
     wl_has_space (wl_Word (alloc_size k:A word)) (wl_state_store_fupd (K s1) t) = SOME F /\
     sp <= heap_length heap /\ good_dimindex(:A) ==>
     sp < k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_in_memory_store_def] THEN STRIP_TAC THEN
  UNDISCH_TAC `wl_has_space (wl_Word (alloc_size k:A word))
    (wl_state_store_fupd (K s1) (t:(A,C,FFI)wl_state)) = SOME F` THEN
  ASM_REWRITE_TAC[wl_has_space_def; wl_get_store_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ] THEN
  SUBGOAL_THEN `word_sub (word_add curr (word_mul bytes_in_word (word (a + sp))))
      (word_add curr (word_mul bytes_in_word (word a))) =
      word_mul bytes_in_word (word sp):A word` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM word_add_n2w] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[NOT_LE] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] alloc_size_check) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LET_TRANS THEN
  EXISTS_TAC `(heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#
    (A word_loc)list)heap_element)list) + 3) * dimindex(:A) DIV 8` THEN
  ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC);;

(* GCP2AUX: has_space only looks at the store *)
let GCP2AUX_has_space_store = prove
 (`!(w:A word_loc) s1 (t:(A,C,FFI)wl_state) (u:(A,C,FFI)wl_state).
     wl_has_space w (wl_state_store_fupd (K s1) t) =
     wl_has_space w (wl_state_store_fupd (K s1) u)`,
  REWRITE_TAC[wl_has_space_def; wl_get_store_def; wl_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 line 4356 *)
let word_gc_fun_correct = prove
 (`!heap a sp sp1 gens c s (m:A word->A word_loc) dm limit be ts refs v stack k
    (t:(A,C,FFI)wl_state).
     good_dimindex (:A) /\
     heap_in_memory_store heap a sp sp1 gens c s m dm limit /\
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (CONS (v,FAPPLY s Globals) stack) ==>
     ?stack1 m1 s1 heap1 a1 sp1 sp2 gens2 v1 xs.
       word_gc_fun c (MAP SND stack,m,dm,s) = SOME (stack1,m1,s1) /\
       heap_in_memory_store heap1 a1 sp1 sp2 gens2 c s1 m1 dm limit /\
       abs_ml_inv c (CONS v (MAP FST (ZIP (MAP FST stack) stack1))) refs
         (CONS v1 xs,heap1,be,a1,sp1,sp2,gens2) limit ts /\
       word_addr c v1 = FAPPLY s1 Globals /\
       ALL2 (\v w. word_addr c v = w) xs (MAP SND (ZIP (MAP FST stack) stack1)) /\
       (FLOOKUP s AllocSize = SOME (wl_Word (alloc_size k)) /\
        wl_has_space (wl_Word ((alloc_size k):A word)) (wl_state_store_fupd (K s1) t) =
          SOME F /\
        ~(data_to_word_config_gc_kind c = data_to_word_None) ==>
        sp1 + sp2 < k /\
        all_reachable_from_roots (CONS v1 xs) heap1 /\
        heap_length heap1 = data_length heap1 + sp1 + sp2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_ml_inv_def; MAP] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `CONS (v:data_v) (MAP FST (stack:(data_v#A word_loc)list))`;
    `refs:((data_v)bvl_ref)spt`; `hs:((A word_loc)heap_address)list`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `be:bool`; `a:num`; `sp:num`; `sp1:num`; `gens:gen_state`; `limit:num`; `ts:num`;
    `do_partial c (s:(store_name,A word_loc)fmap)`] gc_combined_thm) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[do_partial_def] THEN CASE_REWRITE_TAC[] THEN
    DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th]) (DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th])
      (X_CHOOSE_THEN `l:num list` (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)))
      (ISPEC `data_to_word_config_gc_kind c` (cases "gc_kind")) THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[word_gen_gc_can_do_partial_def] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[heap_in_memory_store_def] o check (fun th ->
      gcp2aux_has_const "heap_in_memory_store" (concl th))) THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th -> if gcp2aux_has_const "gen_starts_in_store" (concl th) then
      MP_TAC(MATCH_MP gen_starts_in_store_IMP_SOME_Word th) else NO_TAC) THEN
    DISCH_THEN(X_CHOOSE_TAC `wg:A word`) THEN
    FIRST_X_ASSUM(fun th -> if gcp2aux_has_const "gen_starts_in_store" (concl th) then
      MP_TAC th else NO_TAC) THEN
    MP_TAC(ISPEC `gens:gen_state` (cases "gen_state")) THEN
    DISCH_THEN(X_CHOOSE_THEN `gn:num` (X_CHOOSE_THEN `gstarts:num list` SUBST_ALL_TAC)) THEN
    ASM_REWRITE_TAC[gen_starts_in_store_def; has_gen_def] THEN
    DISCH_THEN(MP_TAC o SPEC `l:num list`) THEN REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `g0:num` (X_CHOOSE_THEN `gs1:num list`
      SUBST1_TAC)) (ISPEC `gstarts:num list` list_CASES) THEN
    REWRITE_TAC[LENGTH; NOT_CONS_NIL] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    REWRITE_TAC[LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `roots2:((A word_loc)heap_address)list` (X_CHOOSE_THEN
    `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    (X_CHOOSE_THEN `gens2:gen_state` (X_CHOOSE_THEN `n2:num` (X_CHOOSE_THEN `a2:num`
    STRIP_ASSUME_TAC))))) THEN
  gcp2aux_ispecl_names [] word_gc_fun_lemma THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `stack1:(A word_loc)list` (X_CHOOSE_THEN `m1:A word->A word_loc`
    (X_CHOOSE_THEN `s1:(store_name,A word_loc)fmap` (X_CHOOSE_THEN `k2:num`
    (X_CHOOSE_THEN `k3:num` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> gcp2aux_has_const "ALL2" (concl th) &&
    gcp2aux_has_const "s1" (concl th) || (gcp2aux_has_const "ALL2" (concl th) &&
    vfree_in `s1:(store_name,A word_loc)fmap` (concl th)))) THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `v1:(A word_loc)heap_address`
    (X_CHOOSE_THEN `xs:((A word_loc)heap_address)list` SUBST_ALL_TAC))
    (ISPEC `roots2:((A word_loc)heap_address)list` list_CASES) THEN
  REWRITE_TAC[ALL2] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`stack1:(A word_loc)list`; `m1:A word->A word_loc`;
    `s1:(store_name,A word_loc)fmap`;
    `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `a2:num`; `k2:num`; `k3:num`; `gens2:gen_state`; `v1:(A word_loc)heap_address`;
    `xs:((A word_loc)heap_address)list`] THEN
  ASM_SIMP_TAC[MAP_ZIP; LENGTH_MAP] THEN
  SUBGOAL_THEN `k2 <= heap_length (heap2:((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[abs_ml_inv_def; unused_space_inv_def] o check (fun th ->
      gcp2aux_has_const "abs_ml_inv" (concl th) && vfree_in `n2:num` (concl th))) THEN
    STRIP_TAC THEN gcp2aux_arith_tac;
    ALL_TAC] THEN
  DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `l:num list` ASSUME_TAC))
    (ISPEC `data_to_word_config_gc_kind c` (cases "gc_kind")) THEN
  gcp2aux_rw_asm_tac `data_to_word_config_gc_kind c` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "gc_kind"; injectivity "gc_kind"]) THEN
  REWRITE_TAC[distinctness "gc_kind"; injectivity "gc_kind"] THENL
   [FIRST_ASSUM(fun th -> if concl th = `k3 = 0` then SUBST_ALL_TAC th else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if concl th = `k2 + 0 = n2` then
      SUBST_ALL_TAC(SYM(REWRITE_RULE[ADD_CLAUSES] th)) else NO_TAC) THEN
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM(fun th -> if concl th = `k3 = 0` then SUBST_ALL_TAC th else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if concl th = `k2 + 0 = n2` then
      SUBST_ALL_TAC(SYM(REWRITE_RULE[ADD_CLAUSES] th)) else NO_TAC) THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GCP2AUX_has_space_F THEN
    MAP_EVERY EXISTS_TAC [`heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
        heap_element)list`; `a2:num`; `0`; `gens2:gen_state`; `c:data_to_word_config`;
      `s1:(store_name,A word_loc)fmap`; `m1:A word->A word_loc`; `dm:A word->bool`;
      `limit:num`; `t:(A,C,FFI)wl_state`] THEN
    ASM_REWRITE_TAC[];
    CONJ_TAC THENL
     [MATCH_MP_TAC abs_ml_inv_ADD THEN EXISTS_TAC `l:num list` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `k2 < k` ASSUME_TAC THENL
     [MATCH_MP_TAC GCP2AUX_has_space_F THEN
      MAP_EVERY EXISTS_TAC [`heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
          heap_element)list`; `a2:num`; `k3:num`; `gens2:gen_state`; `c:data_to_word_config`;
        `s1:(store_name,A word_loc)fmap`; `m1:A word->A word_loc`; `dm:A word->bool`;
        `limit:num`; `t:(A,C,FFI)wl_state`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `word_gen_gc_can_do_partial (l:num list) (s:(store_name,A word_loc)fmap)`
    THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `l:num list` o check (fun th -> is_forall(concl th) &&
        gcp2aux_has_const "wl_has_space" (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(fun th -> if gcp2aux_is_app_eq "wl_has_space" th then
        REWRITE_TAC[ONCE_REWRITE_RULE[GCP2AUX_has_space_store] th] else NO_TAC) THEN
      REWRITE_TAC[option_INJ];
      SUBGOAL_THEN `~do_partial c (s:(store_name,A word_loc)fmap)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[do_partial_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_ASSUM(fun th -> if is_imp(concl th) && gcp2aux_has_const "all_reachable_from_roots"
          (concl th) then
        MP_TAC(MP th (ASSUME `~do_partial c (s:(store_name,A word_loc)fmap)`)) else NO_TAC) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`l:num list`; `k:num`] o check (fun th ->
        is_forall(concl th) && vfree_in `k2:num` (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

(* HOL4 line 4431 *)
let data_to_word_gcProof_code_rel_def = cake_def
  `data_to_word_gcProof_code_rel c (s_code:(num#data_prog)spt)
     (t_code:(num#(A)wl_prog)spt) <=>
     domain t_code =
       domain s_code UNION set_of_list (MAP FST (data_to_word_stubs (:A) c)) /\
     ALL (\(n,x). lookup n t_code = SOME x) (data_to_word_stubs (:A) c) /\
     !n arg_count prog.
       (lookup n s_code = SOME (arg_count:num,prog)) ==>
       (lookup n t_code = SOME (arg_count + 1,FST (data_to_word_comp c n 2 prog)))`;;

(* HOL4 line 4440 *)
let data_to_word_gcProof_stack_rel_def = cake_def
  `(data_to_word_gcProof_stack_rel (data_Env s1 env)
      (StackFrame s2 ws (vs:(num#(A)word_loc)list) NONE) <=>
      ALL (\(x1,x2). ~(x1 = 0) /\ EVEN x1) vs /\ s1 = s2 /\
      ALL (\(x1,x2). x1 = 0) ws /\
      ALL_DISTINCT (MAP FST vs) /\
      !n. IS_SOME (lookup n env) <=>
          IS_SOME (lookup (adjust_var n) (fromAList vs))) /\
   (data_to_word_gcProof_stack_rel (Exc s1 env n)
      (StackFrame s2 ws vs (SOME (x1,x2,x3))) <=>
      data_to_word_gcProof_stack_rel (data_Env s1 env) (StackFrame s2 ws vs NONE) /\
      (x1 = n)) /\
   (data_to_word_gcProof_stack_rel _ _ <=> F)`;;

(* HOL4 line 4452 *)
let the_global_def = cake_def
  `the_global g = misc_the (data_Number (&0)) (OPTION_MAP (data_RefPtr T) g)`;;

(* HOL4 line 4456 *)
let contains_loc_def = cake_def
  `contains_loc (StackFrame _ vs _ _:(A)stack_frame) (l1,l2) <=>
     (ALOOKUP vs 0 = SOME (wl_Loc l1 l2))`;;

(* HOL4 line 4460 *)
let code_oracle_rel_def = cake_def
  `code_oracle_rel (c:data_to_word_config)
     (s_compile:C -> (num#num#data_prog)list -> (byte list#int64 list#C)option)
     (s_compile_oracle:num -> C#(num#num#data_prog)list)
     (t_store:(store_name,A word_loc)fmap)
     (t_compile:C -> (num#num#(A)wl_prog)list -> (byte list#(A word)list#C)option)
     (t_compile_oracle:num -> C#(num#num#(A)wl_prog)list)
     (t_code_buffer:(A,8)buffer) (t_data_buffer:(A,A)buffer) <=>
     buffer_buffer t_code_buffer = [] /\
     buffer_buffer t_data_buffer = [] /\
     FLOOKUP t_store CodeBuffer = SOME (wl_Word (buffer_position t_code_buffer)) /\
     FLOOKUP t_store CodeBufferEnd =
       SOME (wl_Word (word_add (buffer_position t_code_buffer)
                               (word (buffer_space_left t_code_buffer)))) /\
     FLOOKUP t_store BitmapBuffer = SOME (wl_Word (buffer_position t_data_buffer)) /\
     FLOOKUP t_store BitmapBufferEnd =
       SOME (wl_Word (word_add (buffer_position t_data_buffer)
                       (word_mul bytes_in_word (word (buffer_space_left t_data_buffer))))) /\
     s_compile = (\cfg. OPTION_MAP (I ## MAP upper_w2w ## I) o t_compile cfg o
                        MAP (data_to_word_compile_part c)) /\
     t_compile_oracle = (I ## MAP (data_to_word_compile_part c)) o s_compile_oracle /\
     (!n. ALL (\(n,_). data_num_stubs <= n) (SND (s_compile_oracle n)))`;;

(* HOL4 line 4483 *)
let code_oracle_rel_NextFree = prove
 (`!c (scc:C->(num#num#data_prog)list->(byte list#int64 list#C)option) sco
    (ts:(store_name,A word_loc)fmap) x tcc tco cb db.
     code_oracle_rel c scc sco (ts |+ (NextFree,x)) tcc tco cb db <=>
     code_oracle_rel c scc sco ts tcc tco cb db`,
  REWRITE_TAC[code_oracle_rel_def; FLOOKUP_UPDATE; distinctness "store_name"]);;

let _ = cake_add_simps [code_oracle_rel_NextFree];;

(* HOL4 line 4490 *)
let limits_inv_def = cake_def
  `limits_inv (lims:limits) heaplength t_stack_limit c_len_size c_has_fp_ops
     c_has_fp_tern <=>
     limits_stack_limit lims = t_stack_limit /\
     limits_length_limit lims = c_len_size /\
     limits_arch_64_bit lims = (dimindex (:A) = 64) /\
     heaplength = SOME (wl_Word (word_mul bytes_in_word (word (limits_heap_limit lims))
                                   :A word)) /\
     limits_heap_limit lims * val (bytes_in_word:A word) < dimword (:A) /\
     limits_has_fp_ops lims = c_has_fp_ops /\
     limits_has_fp_tops lims = c_has_fp_tern`;;

(* HOL4 line 4501: val s = (s:('c,'ffi) dataSem$state) *)

(* HOL4 line 4503 (Definition state_rel_thm: the constant state_rel) *)
let data_to_word_gcProof_state_rel_thm = cake_def
  `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
     (t:(A,C,FFI)wl_state) v1 locs <=>
     (wl_state_ffi t = data_state_ffi s) /\
     (wl_state_clock t = data_state_clock s) /\
     (wl_state_handler t = data_state_handler s) /\
     (wl_state_gc_fun t = word_gc_fun c) /\
     data_to_word_gcProof_code_rel c (data_state_code s) (wl_state_code t) /\
     code_oracle_rel c (data_state_compile s) (data_state_compile_oracle s)
       (wl_state_store t) (wl_state_compile t) (wl_state_compile_oracle t)
       (wl_state_code_buffer t) (wl_state_data_buffer t) /\
     good_dimindex (:A) /\
     shift_length c < dimindex (:A) /\
     IS_SOME (data_state_tstamps s) /\
     ALL (\n. n IN FDOM (wl_state_store t)) [Globals] /\
     (v1 = NONE ==> lookup 0 (wl_state_locals t) = SOME (wl_Loc l1 l2)) /\
     (!n. IS_SOME (lookup n (data_state_locals s)) ==>
          IS_SOME (lookup (adjust_var n) (wl_state_locals t))) /\
     ALL2 data_to_word_gcProof_stack_rel (data_state_stack s) (wl_state_stack t) /\
     ALL2 contains_loc (wl_state_stack t) locs /\
     option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
                                (wl_state_locals_size t)) (wl_state_stack_max t) /\
     option_le (wl_state_stack_max t) (data_state_stack_max s) /\
     wl_state_stack_size t = data_state_stack_frame_sizes s /\
     wl_state_locals_size t = data_state_locals_size s /\
     limits_inv (data_state_limits s) (FLOOKUP (wl_state_store t) HeapLength)
       (wl_state_stack_limit t) (data_to_word_config_len_size c)
       (data_to_word_config_has_fp_ops c) (data_to_word_config_has_fp_tern c) /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s)
       (data_state_space s) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (APPEND (APPEND (APPEND (match v1 with NONE -> [] | SOME vs -> vs)
          (join_env (data_state_locals s)
             (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s))))))
          [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)])
          (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t)))`;;

(* HOL4 line 4538: Theorem state_rel_thm[allow_rebind] = state_rel_thm (the  *)
(* same theorem)                                                            *)

(* HOL4 line 4541 (HOL4: state_rel_thm |> REWRITE_RULE [memory_rel_def])    *)
let data_to_word_gcProof_state_rel_def =
  REWRITE_RULE [memory_rel_def] data_to_word_gcProof_state_rel_thm;;

(* HOL4 line 4544 *)
let data_to_word_gcProof_state_rel_with_clock = prove
 (`!a b c (s1:(C,FFI)data_state) (s2:(A,C,FFI)wl_state) d e k.
     data_to_word_gcProof_state_rel a b c s1 s2 d e ==>
     data_to_word_gcProof_state_rel a b c (data_state_clock_fupd (K k) s1)
       (wl_state_clock_fupd (K k) s2) d e`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_state_INFO.ri_accfupds;
              wl_state_INFO.ri_accfupds; K_THM] THEN MESON_TAC[]);;

(* HOL4 line 4552 (the relation places no constraint on the FP registers) *)
let state_rel_with_fp_regs = prove
 (`!a b c (s1:(C,FFI)data_state) (s2:(A,C,FFI)wl_state) d e f.
     data_to_word_gcProof_state_rel a b c s1 s2 d e ==>
     data_to_word_gcProof_state_rel a b c s1 (wl_state_fp_regs_fupd (K f) s2) d e`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; wl_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 line 4563 *)
let flat_NIL = prove
 (`!xs:((A)stack_frame)list. data_to_word_gcProof_flat [] xs = []`,
  GEN_TAC THEN CASES_ON `xs:((A)stack_frame)list` THEN REWRITE_TAC[flat_def]);;

(* HOL4 line 4569 (the variables code_buffer and data_buffer of HOL4 are    *)
(* cbuf and dbuf: export.ml defines a constant code_buffer)                 *)
let init_store_ok_def = cake_def
  `init_store_ok c (store:(store_name,A word_loc)fmap) (m:A word->B) (dm:A word->bool)
     (cbuf:(A,8)buffer) (dbuf:(A,A)buffer) <=>
     ?limit curr.
       limit <= max_heap_limit (:A) c /\
       FLOOKUP store Globals = SOME (wl_Word (word 0)) /\
       FLOOKUP store GlobReal = SOME (wl_Word curr) /\
       FLOOKUP store GenStart = SOME (wl_Word (word 0)) /\
       FLOOKUP store CurrHeap = SOME (wl_Word curr) /\
       FLOOKUP store OtherHeap = FLOOKUP store EndOfHeap /\
       FLOOKUP store NextFree = SOME (wl_Word curr) /\
       FLOOKUP store EndOfHeap =
         SOME (wl_Word (word_add curr (word_mul bytes_in_word (word limit)))) /\
       FLOOKUP store TriggerGC =
         SOME (wl_Word (match data_to_word_config_gc_kind c with
                          Generational _ -> curr
                        | _ -> word_add curr (word_mul bytes_in_word (word limit)))) /\
       FLOOKUP store HeapLength =
         SOME (wl_Word (word_mul bytes_in_word (word limit))) /\
       FLOOKUP store CodeBuffer = SOME (wl_Word (buffer_position cbuf)) /\
       FLOOKUP store CodeBufferEnd =
         SOME (wl_Word (word_add (buffer_position cbuf)
                                 (word (buffer_space_left cbuf)))) /\
       FLOOKUP store BitmapBuffer = SOME (wl_Word (buffer_position dbuf)) /\
       FLOOKUP store BitmapBufferEnd =
         SOME (wl_Word (word_add (buffer_position dbuf)
                 (word_mul bytes_in_word (word (buffer_space_left dbuf))))) /\
       buffer_buffer cbuf = [] /\
       buffer_buffer dbuf = [] /\
       (word_list_exists curr (limit + limit)) (fun2set (m,dm)) /\
       byte_aligned curr`;;

(* HOL4 line 4600 (local) *)
let blocks_unique_empty = prove
 (`!v. blocks_unique v (all_vs (LN:(data_v bvl_ref)spt) [])`,
  GEN_TAC THEN
  SUBGOAL_THEN `all_vs (LN:(data_v bvl_ref)spt) [] = {}` SUBST1_TAC THENL
   [REWRITE_TAC[all_vs_def; v_all_vs_def; lookup_rwts; option_DISTINCT; MEM] THEN
    SET_TAC[];
    REWRITE_TAC[blocks_unique_def; NOT_IN_EMPTY]]);;

(* GCP2AUX: the abstract invariant of the initial (empty) heap *)
let GCP2AUX_abs_ml_inv_init = prove
 (CASE_TERM `!c (be:bool) limit.
     data_to_word_config_be c = be ==>
     abs_ml_inv c [] (LN:(data_v bvl_ref)spt)
       ([]:((A word_loc)heap_address)list,
        heap_expand limit:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                           heap_element)list,
        be,0,
        (match data_to_word_config_gc_kind c with Generational l -> 0 | _ -> limit),
        (match data_to_word_config_gc_kind c with Generational l -> limit | _ -> 0),
        GenState 0 (match data_to_word_config_gc_kind c with
                      Generational l -> MAP (K 0) l | _ -> [])) limit 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[abs_ml_inv_def; roots_ok_def; heap_ok_def; gc_shared_heap_length_heap_expand;
              unused_space_inv_def; bc_stack_ref_inv_def; MEM] THEN
  SUBGOAL_THEN
   `FILTER isForwardPointer (heap_expand limit:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list) = [] /\
    (!xs l d. ~MEM (DataElement xs l d) (heap_expand limit:((A word_loc,
       data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)) /\
    (~(limit = 0) ==> heap_lookup 0 (heap_expand limit:((A word_loc,
       data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) =
       SOME (Unused (limit - 1))) /\
    ALL (\x. ~isRef x) (heap_expand limit:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list)`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[heap_expand_def] THEN COND_CASES_TAC THEN
    REWRITE_TAC[FILTER; MEM; ALL; isForwardPointer_def; heap_lookup_def; isRef_def;
                distinctness "heap_element"];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?f tf:(num,num)fmap.
      INJ (FAPPLY f) (FDOM f)
        {a | isSomeDataElement (heap_lookup a (heap_expand limit:((A word_loc,
          data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))} /\
      FDOM f SUBSET domain (LN:(data_v bvl_ref)spt) /\
      INJ (FAPPLY tf) (FDOM tf)
        {a | isSomeDataElement (heap_lookup a (heap_expand limit:((A word_loc,
          data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))} /\
      FDOM tf SUBSET all_ts (LN:(data_v bvl_ref)spt) [] /\
      FDOM tf SUBSET {n | n < 0} /\
      be_ok be be /\
      blocks_unique 0 (all_vs (LN:(data_v bvl_ref)spt) []) /\
      ALL2 (\v x. v_inv c v (LN:(data_v bvl_ref)spt)
                  (x,f,tf,heap_expand limit:((A word_loc,data_to_word_memoryProof_tag#
                     (A word_loc)list)heap_element)list))
        ([]:data_v list) ([]:((A word_loc)heap_address)list) /\
      (!n. reachable_refs ([]:data_v list) (LN:(data_v bvl_ref)spt) n /\ n IN FDOM f
           ==> bc_ref_inv c n (LN:(data_v bvl_ref)spt)
                 (f,tf,heap_expand limit:((A word_loc,data_to_word_memoryProof_tag#
                     (A word_loc)list)heap_element)list,be))`
    ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`FEMPTY:(num,num)fmap`; `FEMPTY:(num,num)fmap`] THEN
    REWRITE_TAC[FDOM_FEMPTY; INJ; NOT_IN_EMPTY; EMPTY_SUBSET; be_ok_def;
                blocks_unique_empty; ALL2; reachable_refs_def; MEM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `data_up_to 0 (heap_expand limit:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list)` ASSUME_TAC THENL
   [REWRITE_TAC[data_up_to_def; heap_split_0] THEN MESON_TAC[ALL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `data_to_word_config_gc_kind c` THEN
  ASM_REWRITE_TAC[gc_kind_inv_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES; LE_REFL] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[gen_state_ok_def; ALL_MAP; o_DEF; K_THM; LE_REFL; GSYM ALL_MEM] THEN
  REWRITE_TAC[gen_start_ok_def; heap_split_0; MEM] THEN
  MP_TAC(ISPECL [`heap_expand limit:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list`; `[]:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list`; `limit:num`] heap_split_APPEND_EQ) THEN
  REWRITE_TAC[APPEND_NIL; gc_shared_heap_length_heap_expand] THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`[]:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `heap_expand limit:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
    REWRITE_TAC[MEM];
    MAP_EVERY EXISTS_TAC [`heap_expand limit:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `[]:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN ASM_REWRITE_TAC[MEM] THEN
    UNDISCH_TAC `ALL (\x. ~isRef x) (heap_expand limit:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)` THEN
    REWRITE_TAC[GSYM ALL_MEM]]);;

(* HOL4 line 4608 *)
let state_rel_init = prove
 (`!(t:(A,C,FFI)wl_state) ffi c code cc co l1 l2 lim.
     wl_state_ffi t = ffi /\ wl_state_handler t = 0 /\
     wl_state_gc_fun t = word_gc_fun c /\
     data_to_word_gcProof_code_rel c code (wl_state_code t) /\
     code_oracle_rel c cc co (wl_state_store t)
       (wl_state_compile t) (wl_state_compile_oracle t) (wl_state_code_buffer t)
       (wl_state_data_buffer t) /\
     good_dimindex (:A) /\
     lookup 0 (wl_state_locals t) = SOME (wl_Loc l1 l2) /\
     wl_state_stack t = [] /\
     wl_state_stack_max t = SOME 1 /\
     wl_state_locals_size t = SOME 0 /\
     wl_state_stack_limit t = limits_stack_limit lim /\
     data_to_word_config_len_size c = limits_length_limit lim /\
     data_to_word_config_be c = wl_state_be t /\
     (limits_arch_64_bit lim <=> dimindex (:A) = 64) /\
     limits_heap_limit lim * val (bytes_in_word:A word) < dimword (:A) /\
     FAPPLY (wl_state_store t) HeapLength =
       wl_Word (word_mul bytes_in_word (word (limits_heap_limit lim))) /\
     limits_has_fp_ops lim = data_to_word_config_has_fp_ops c /\
     limits_has_fp_tops lim = data_to_word_config_has_fp_tern c /\
     conf_ok (:A) c /\
     init_store_ok c (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (wl_state_code_buffer t) (wl_state_data_buffer t) ==>
     data_to_word_gcProof_state_rel c l1 l2
       (data_initial_state ffi code co cc T lim (wl_state_stack_size t)
          (wl_state_clock t))
       t NONE []`,
  REPEAT GEN_TAC THEN REWRITE_TAC[conf_ok_def; init_store_ok_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `Globals IN FDOM (wl_state_store (t:(A,C,FFI)wl_state)) /\
                FAPPLY (wl_state_store t) Globals = wl_Word (word 0)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) Globals =
                   SOME (wl_Word (word 0))` THEN
    REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT];
    ALL_TAC] THEN
  SUBGOAL_THEN `limits_inv lim (FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) HeapLength)
                  (wl_state_stack_limit t) (data_to_word_config_len_size c)
                  (data_to_word_config_has_fp_ops c) (data_to_word_config_has_fp_tern c)`
    ASSUME_TAC THENL
   [REWRITE_TAC[limits_inv_def] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) HeapLength =
                   SOME (wl_Word (word_mul bytes_in_word (word limit)))` THEN
    ASM_REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; injectivity "word_loc"] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_def; data_initial_state_def;
              data_state_INFO.ri_accessors] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[APPEND] THEN
  ASM_REWRITE_TAC[ALL; IS_SOME_DEF; lookup_rwts; ALL2; stack_size_eq2; OPTION_MAP2_THM;
                  option_le_def; ADD_CLAUSES; LE_REFL; THE_DEF] THEN
  REWRITE_TAC[adjust_set_LN; inter_LN; toAList_LN; join_env_def; FILTER; MAP; APPEND;
              flat_NIL; the_global_def; OPTION_MAP_DEF; misc_the_def; APPEND_NIL] THEN
  SUBGOAL_THEN `wl_Word (word 0:A word) = wl_Word (Smallnum (&0))` SUBST1_TAC THENL
   [REWRITE_TAC[data_to_word_Smallnum_def; INT_LT_REFL; INT_MUL_RZERO; NUM_OF_INT_OF_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM memory_rel_def] THEN MATCH_MP_TAC IMP_memory_rel_Number THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[small_int_def] THEN UNDISCH_TAC `good_dimindex(:A)` THEN
    REWRITE_TAC[good_dimindex_def; dimword_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[memory_rel_def] THEN
  SUBGOAL_THEN `limit <= dimword(:A) DIV 2 EXP shift_length c /\
                (limit + 3) * dimindex (:A) DIV 8 + 1 < dimword (:A)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `limit <= max_heap_limit (:A) c` THEN
    REWRITE_TAC[max_heap_limit_def; backend_common_word_shift_def;
                ARITH_RULE `x <= MIN a b <=> x <= a /\ x <= b`] THEN
    UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `byte_aligned (word_add curr (word_mul bytes_in_word (word limit)):A word)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `byte_aligned (curr:A word)` THEN
    REWRITE_TAC[byte_aligned_def; bytes_in_word_def; word_mul_n2w] THEN
    UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_DIV_CONV) THEN
    CONV_TAC(DEPTH_CONV LOG2_CONV) THENL
     [SUBGOAL_THEN `4 * limit = limit * 2 EXP 2` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC];
      SUBGOAL_THEN `8 * limit = limit * 2 EXP 3` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC]] THEN
    REWRITE_TAC[aligned_add_pow];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`; `limit:num`]
    (INST_TYPE [`:A`,`:A`] GCP2AUX_abs_ml_inv_init)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "TriggerGC" o concl)) THEN
  CASES_ON `data_to_word_config_gc_kind c` THEN CASE_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  EXISTS_TAC `heap_expand limit:((A word_loc,data_to_word_memoryProof_tag#
                (A word_loc)list)heap_element)list` THEN
  EXISTS_TAC `limit:num` THEN EXISTS_TAC `0` THENL
   [MAP_EVERY EXISTS_TAC [`limit:num`; `0`; `GenState 0 []`];
    MAP_EVERY EXISTS_TAC [`limit:num`; `0`; `GenState 0 []`];
    MAP_EVERY EXISTS_TAC [`0`; `limit:num`; `GenState 0 (MAP (K 0) (a:num list))`]] THEN
  REWRITE_TAC[heap_in_memory_store_def; gc_shared_heap_length_heap_expand; word_ml_inv_def;
              MAP; ALL2; word_heap_heap_expand; ADD_CLAUSES; LE_0] THEN
  ASM_REWRITE_TAC[] THEN
  (REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(limit + 3) * dimindex (:A) DIV 8 + 1 < dimword (:A)` THEN ARITH_TAC;
    MAP_EVERY EXISTS_TAC [`curr:A word`;
      `word_add curr (word_mul bytes_in_word (word limit)):A word`] THEN
    ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"; WORD_MUL_0; WORD_ADD_0] THEN
    REWRITE_TAC[glob_real_inv_def; option_INJ; injectivity "word_loc"; UNWIND_THM1;
                WORD_USHR_0; WORD_SHL_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[gen_starts_in_store_def; distinctness "gc_kind"; injectivity "gc_kind"] THEN
    ASM_REWRITE_TAC[GSYM data_to_word_memoryProof_word_list_exists_ADD] THEN
    GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LENGTH_MAP] THEN
    CASES_ON `a:num list` THEN REWRITE_TAC[MAP; NOT_CONS_NIL; injectivity "list"; K_THM] THEN
    REPEAT STRIP_TAC THEN UNDISCH_TAC `0 = x` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[WORD_MUL_0];
    EXISTS_TAC `[]:((A word_loc)heap_address)list` THEN ASM_REWRITE_TAC[ALL2]]));;

(* HOL4 line 4688 *)
let adjust_var_NOT_0 = prove
 (`!n. ~(adjust_var n = 0)`,
  REWRITE_TAC[adjust_var_def] THEN ARITH_TAC);;

let _ = cake_add_simps [adjust_var_NOT_0];;

(* HOL4 line 4694 *)
let state_rel_get_var_IMP = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v1 locs n x.
     data_to_word_gcProof_state_rel c l1 l2 s t v1 locs ==>
     (data_get_var n (data_state_locals s) = SOME x) ==>
     ?w. wl_get_var (adjust_var n) t = SOME w`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_get_var_def; wl_get_var_def] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[IS_SOME_DEF] THEN
  CASES_ON `lookup (adjust_var n) (wl_state_locals (t:(A,C,FFI)wl_state))` THEN
  REWRITE_TAC[IS_SOME_DEF; option_INJ] THEN MESON_TAC[]);;

(* HOL4 line 4705 *)
let state_rel_get_vars_IMP = prove
 (`!n xs c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs ==>
     (data_get_vars n (data_state_locals s) = SOME xs) ==>
     ?ws. wl_get_vars (MAP adjust_var n) t = SOME ws /\ (LENGTH xs = LENGTH ws)`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[data_get_vars_def; wl_get_vars_def; MAP; option_INJ] THEN
    MESON_TAC[LENGTH];
    ALL_TAC] THEN
  X_GEN_TAC `h:num` THEN X_GEN_TAC `tl:num list` THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[data_get_vars_def; wl_get_vars_def; MAP] THEN
  CASES_ON `data_get_var h (data_state_locals (s:(C,FFI)data_state))` THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `data_get_vars tl (data_state_locals (s:(C,FFI)data_state))` THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `?w. wl_get_var (adjust_var h) (t:(A,C,FFI)wl_state) = SOME w`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[state_rel_get_var_IMP]; ALL_TAC] THEN
  SUBGOAL_THEN `?ws. wl_get_vars (MAP adjust_var tl) (t:(A,C,FFI)wl_state) = SOME ws /\
                     LENGTH (a':data_v list) = LENGTH ws` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[UNWIND_THM1] THEN ASM_REWRITE_TAC[LENGTH]);;

(* HOL4 line 4718 *)
let state_rel_0_get_vars_IMP = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs n xs.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs ==>
     (data_get_vars n (data_state_locals s) = SOME xs) ==>
     ?ws. wl_get_vars (CONS 0 (MAP adjust_var n)) t = SOME (CONS (wl_Loc l1 l2) ws) /\
          (LENGTH xs = LENGTH ws)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num list`; `xs:data_v list`; `c:data_to_word_config`; `l1:num`;
                `l2:num`; `s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`;
                `locs:(num#num)list`] state_rel_get_vars_IMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lookup 0 (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME (wl_Loc l1 l2)`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
  ASM_REWRITE_TAC[wl_get_vars_def; wl_get_var_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ; injectivity "list"] THEN ASM_MESON_TAC[]);;

(* GCP2AUX: the head of a word_ml_inv list *)
let GCP2AUX_word_ml_inv_head = prove
 (`!heap be a sp sp1 gens limit ts c refs (v:data_v) (w:A word_loc) xs.
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs (CONS (v,w) xs) ==>
     ?h f tf. v_inv c v refs (h,f,tf,heap) /\ word_addr c h = w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_ml_inv_def; abs_ml_inv_def; bc_stack_ref_inv_def; MAP; FST; SND] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `ALL2 (\v w. word_addr c v = w) (hs:((A word_loc)heap_address)list)
                 (CONS (w:A word_loc) (MAP SND (xs:(data_v#A word_loc)list)))` THEN
  UNDISCH_TAC `ALL2 (\v x. v_inv c v refs (x,f,tf,heap))
                 (CONS (v:data_v) (MAP FST (xs:(data_v#A word_loc)list)))
                 (hs:((A word_loc)heap_address)list)` THEN
  CASES_ON `hs:((A word_loc)heap_address)list` THEN REWRITE_TAC[ALL2] THEN
  REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC
   [`a0:(A word_loc)heap_address`; `f:(num,num)fmap`; `tf:(num,num)fmap`] THEN
  ASM_REWRITE_TAC[]);;

(* GCP2AUX: clearing bit 0 of an even word *)
let GCP2AUX_word_and_not1_EVEN = prove
 (`!n. EVEN n ==> word_and (word n) (word_not (word 1)) = (word n:A word)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_NOT; BIT_WORD_1] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[BIT_WORD; EXP; DIV_1] THEN
  ASM_MESON_TAC[NOT_ODD]);;

(* GCP2AUX: every member of a word_ml_inv list is represented *)
let GCP2AUX_word_ml_inv_MEM = prove
 (`!heap be a sp sp1 gens limit ts c refs (xs:(data_v#A word_loc)list) v w.
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs xs /\ MEM (v,w) xs ==>
     ?h f tf. v_inv c v refs (h,f,tf,heap) /\ word_addr c h = w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC GCP2AUX_word_ml_inv_head THEN
  MAP_EVERY EXISTS_TAC [`be:bool`; `a:num`; `sp:num`; `sp1:num`; `gens:gen_state`;
    `limit:num`; `ts:num`; `[]:(data_v#A word_loc)list`] THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "word_ml_inv" o concl)) THEN
  MATCH_MP_TAC word_ml_inv_rearrange THEN REWRITE_TAC[MEM] THEN
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

(* GCP2AUX: a variable and its word are in the join_env of the locals *)

(* GCP2AUX: the word representation of the value of a variable *)
let GCP2AUX_state_rel_get_var_v_inv = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v1 locs n x w.
     data_to_word_gcProof_state_rel c l1 l2 s t v1 locs /\
     data_get_var n (data_state_locals s) = SOME x /\
     wl_get_var (adjust_var n) t = SOME w ==>
     ?h f tf heap. v_inv c x (data_state_refs s) (h,f,tf,heap) /\ word_addr c h = w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_def;
    data_get_var_def; wl_get_var_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "word_ml_inv" o concl)) THEN
  DISCH_THEN(MP_TAC o SPECL [`x:data_v`; `w:A word_loc`] o
    MATCH_MP (REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM] GCP2AUX_word_ml_inv_MEM)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MEM_APPEND] THEN DISJ1_TAC THEN DISJ1_TAC THEN DISJ2_TAC THEN
    MATCH_MP_TAC GCP1AUX_MEM_join_env THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
    MESON_TAC[]]);;

(* GCP2AUX: the representations of the booleans *)
let GCP2AUX_word_addr_Boolv = prove
 (`!c b h f tf (refs:(data_v bvl_ref)spt)
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list).
     v_inv c (data_Boolv b) refs (h,f,tf,heap) ==>
     word_addr c h = wl_Word (if b then word 18 else word 2):A word_loc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_Boolv_def; v_inv_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[word_addr_def; injectivity "word_loc"; BlockNil_def] THEN
  REWRITE_TAC[bool_to_tag_def; true_tag_def; false_tag_def] THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[WORD_SHL_WORD; word_add_n2w] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC GCP2AUX_word_and_not1_EVEN THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 4730 *)
let get_var_T_OR_F = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs n x w.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_var n (data_state_locals s) = SOME x /\
     wl_get_var (adjust_var n) t = SOME w ==>
     ~(18 MOD dimword (:A) = 2 MOD dimword (:A)) /\
     ((x = data_Boolv T) ==> (w = wl_Word (word 18))) /\
     ((x = data_Boolv F) ==> (w = wl_Word (word 2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `good_dimindex(:A)` MP_TAC THENL
     [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
    REWRITE_TAC[good_dimindex_def; dimword_def] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GCP2AUX_state_rel_get_var_v_inv o
    (fun th -> CONJ th (CONJ (ASSUME `data_get_var n (data_state_locals (s:(C,FFI)data_state)) = SOME x`)
      (ASSUME `wl_get_var (adjust_var n) (t:(A,C,FFI)wl_state) = SOME w`))) o
    check (gcp2aux_has_const "data_to_word_gcProof_state_rel" o concl)) THEN
  STRIP_TAC THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP GCP2AUX_word_addr_Boolv) THEN ASM_REWRITE_TAC[]);;

(* GCP2AUX: a represented value that is a boolean is a Boolv *)
let GCP2AUX_isBool_v_inv = prove
 (`!b x c (refs:(data_v bvl_ref)spt) h f tf
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list).
     isBool b x /\ v_inv c x refs (h,f,tf,heap) ==> x = data_Boolv b`,
  REPEAT GEN_TAC THEN CASES_ON `x:data_v` THEN REWRITE_TAC[isBool_def] THEN
  CASES_ON `a2:data_v list` THEN REWRITE_TAC[isBool_def] THEN
  REWRITE_TAC[v_inv_def; data_Boolv_def; injectivity "data_v"] THEN MESON_TAC[]);;

(* HOL4 line 4753 *)
let get_var_isT_OR_isF = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs n x w.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_var n (data_state_locals s) = SOME x /\
     wl_get_var (adjust_var n) t = SOME w ==>
     ~(18 MOD dimword (:A) = 2 MOD dimword (:A)) /\
     ((isBool T x) ==> (w = wl_Word (word 18))) /\
     ((isBool F x) ==> (w = wl_Word (word 2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL get_var_T_OR_F) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GCP2AUX_state_rel_get_var_v_inv o
    (fun th -> CONJ th (CONJ (ASSUME `data_get_var n (data_state_locals (s:(C,FFI)data_state)) = SOME x`)
      (ASSUME `wl_get_var (adjust_var n) (t:(A,C,FFI)wl_state) = SOME w`))) o
    check (gcp2aux_has_const "data_to_word_gcProof_state_rel" o concl)) THEN
  STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC GCP2AUX_isBool_v_inv THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 4781 (HOL4 infers ('a # num # num) option -> 'b word_loc) *)
let mk_loc_def = cake_def
  `mk_loc (SOME (t1:B,d1,d2)) = wl_Loc d1 d2:A word_loc`;;

(* HOL4 line 4785 *)
let cut_env_IMP_cut_env = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs r x.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_cut_env r (data_state_locals s) = SOME x ==>
     ?y. wl_cut_env (adjust_sets r) (wl_state_locals t) = SOME y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GCP2AUX_data_cut_env) THEN
  SUBGOAL_THEN `lookup 0 (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME (wl_Loc l1 l2) /\
                (!n. IS_SOME (lookup n (data_state_locals (s:(C,FFI)data_state))) ==>
                     IS_SOME (lookup (adjust_var n) (wl_state_locals t)))`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
  REWRITE_TAC[wl_cut_env_def; cut_envs_def; adjust_sets_def; cut_names_def; FST; SND] THEN
  SUBGOAL_THEN `domain (LS one) SUBSET domain (wl_state_locals (t:(A,C,FFI)wl_state)) /\
                domain (adjust_set (r:num_set)) SUBSET domain (wl_state_locals t)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[domain_def; SING_SUBSET; SUBSET; GCP2AUX_IN_domain_adjust_set] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_SING] THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[domain_lookup] THEN EXISTS_TAC `wl_Loc l1 l2:A word_loc` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IS_SOME (lookup j (data_state_locals (s:(C,FFI)data_state)))` MP_TAC THENL
     [UNDISCH_TAC `domain (r:num_set) SUBSET domain (data_state_locals (s:(C,FFI)data_state))` THEN
      REWRITE_TAC[SUBSET; domain_lookup; IS_SOME_EXISTS] THEN DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC `j IN domain (r:num_set)` THEN REWRITE_TAC[domain_lookup];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    REWRITE_TAC[IS_SOME_EXISTS; domain_lookup];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4 line 4806 *)
let cut_env_IMP_cut_envs = prove
 (`!t (l:A spt) y.
     wl_cut_env t l = SOME y ==>
     ?y1 y2. cut_envs t l = SOME (y1,y2) /\ y = sptree_union y2 y1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_cut_env_def] THEN
  CASES_ON `cut_envs t (l:A spt)` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  SPEC_TAC(`a:A spt#A spt`,`p:A spt#A spt`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CASE_REWRITE_TAC[option_INJ; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 4813 *)
let data_to_word_gcProof_set_vars_sing = prove
 (`!q (w:A word_loc) (s:(A,C,FFI)wl_state). wl_set_vars [q] [w] s = wl_set_var q w s`,
  REWRITE_TAC[wl_set_vars_def; wl_set_var_def; alist_insert_def]);;

(* HOL4 line 4820 *)
let jump_exc_call_env = prove
 (`!x y (s:(A,C,FFI)wl_state).
     wl_jump_exc (wl_call_env x y s) =
     wl_jump_exc (wl_state_stack_max_fupd
       (K (OPTION_MAP2 MAX (wl_state_stack_max s)
             (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s)) y))) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_jump_exc_def; wl_call_env_def; wl_state_INFO.ri_accfupds] THEN
  REWRITE_TAC[wl_state_INFO.ri_fupdfupds; wl_state_INFO.ri_fupdcanon; K_o_THM]);;

(* HOL4 line 4829 *)
let jump_exc_dec_clock = prove
 (`!s:(A,C,FFI)wl_state.
     (mk_loc (wl_jump_exc (wl_dec_clock s)):B word_loc) = mk_loc (wl_jump_exc s)`,
  GEN_TAC THEN REWRITE_TAC[wl_jump_exc_def; wl_dec_clock_def; wl_state_INFO.ri_accfupds] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN EVERY_CASE_TAC THEN REWRITE_TAC[mk_loc_def]);;

(* HOL4 line 4836 (HOL4: LASTN_LENGTH_ID |> Q.SPEC x::xs |>               *)
(* SIMP_RULE (srw_ss()) [ADD1])                                             *)
let LASTN_ADD1 = prove
 (`!(x:A) xs. LASTN (LENGTH xs + 1) (CONS x xs) = CONS x xs`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `CONS (x:A) xs` LASTN_LENGTH_ID) THEN
  REWRITE_TAC[LENGTH; ADD1]);;

(* GCP2AUX: mk_loc of jump_exc is unchanged by pushing a frame without a  *)
(* handler                                                                 *)
let GCP2AUX_mk_loc_jump_exc_push_NONE = prove
 (`!(s':(A,C,FFI)wl_state) (s:(A,C,FFI)wl_state) n e0 e.
     wl_state_handler s' = wl_state_handler s /\
     wl_state_stack s' = CONS (StackFrame n e0 e NONE) (wl_state_stack s) ==>
     (mk_loc (wl_jump_exc s'):B word_loc) = mk_loc (wl_jump_exc s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wl_jump_exc_def] THEN
  ASM_REWRITE_TAC[LENGTH] THEN
  ABBREV_TAC `h = wl_state_handler (s:(A,C,FFI)wl_state)` THEN
  ABBREV_TAC `st = wl_state_stack (s:(A,C,FFI)wl_state)` THEN
  ASM_CASES_TAC `h < LENGTH (st:((A)stack_frame)list)` THENL
   [ASM_SIMP_TAC[ARITH_RULE `h < l ==> h < SUC l`; LASTN_TL] THEN
    EVERY_CASE_TAC THEN REWRITE_TAC[mk_loc_def];
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `h = LENGTH (st:((A)stack_frame)list)` THENL
     [ASM_REWRITE_TAC[ARITH_RULE `l < SUC l`; LASTN_ADD1] THEN CASE_REWRITE_TAC[];
      SUBGOAL_THEN `~(h < SUC (LENGTH (st:((A)stack_frame)list)))`
        (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC]]);;

(* HOL4 line 4840 *)
let jump_exc_push_env_NONE = prove
 (`!(s:(A,C,FFI)wl_state) y m.
     (mk_loc (wl_jump_exc (wl_dec_clock s)):B word_loc) = mk_loc (wl_jump_exc s) /\
     (mk_loc (wl_jump_exc (wl_push_env y NONE s)):B word_loc) =
       mk_loc (wl_jump_exc s) /\
     (mk_loc (wl_jump_exc (wl_state_stack_max_fupd (K m) (wl_push_env y NONE s)))
        :B word_loc) =
       mk_loc (wl_jump_exc s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[jump_exc_dec_clock] THEN CONJ_TAC THEN
  MATCH_MP_TAC GCP2AUX_mk_loc_jump_exc_push_NONE THEN
  REWRITE_TAC[wl_push_env_def; LET_DEF; LET_END_DEF] THEN
  PAIRARG_TAC THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[injectivity "list"; injectivity "stack_frame"] THEN MESON_TAC[]);;

(* HOL4 line 4860 *)
let option_le_stack_size_cons = prove
 (`!(y:(A)stack_frame) ys. option_le (wl_stack_size ys) (wl_stack_size (CONS y ys))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_size_eq2] THEN
  CASES_ON `stack_size_frame (y:(A)stack_frame)` THEN
  CASES_ON `wl_stack_size (ys:((A)stack_frame)list)` THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_le_def] THEN ARITH_TAC);;

(* HOL4 line 4868 *)
let option_le_stack_size_append = prove
 (`!xs (ys:((A)stack_frame)list).
     option_le (wl_stack_size ys) (wl_stack_size (APPEND xs ys))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; option_le_refl] THEN GEN_TAC THEN
  MATCH_MP_TAC option_le_trans THEN
  EXISTS_TAC `wl_stack_size (APPEND t (ys:((A)stack_frame)list))` THEN
  ASM_REWRITE_TAC[option_le_stack_size_cons]);;

(* HOL4 line 4878: val s1 = mk_var("s1",type_of s) (a dataSem state) *)

(* HOL4 line 4880 (local) *)
let is_some_lookup_union = prove
 (`!n (t1:A spt) t2.
     IS_SOME (lookup n (sptree_union t1 t2)) <=>
     IS_SOME (lookup n t1) \/ IS_SOME (lookup n t2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_union] THEN
  CASES_ON `lookup n (t1:A spt)` THEN CASE_REWRITE_TAC[IS_SOME_DEF]);;

(* HOL4 line 4888 (s and t are num options here) *)
let option_le_tl = prove
 (`!opt ws (vs:(num#(A)word_loc)list) x ys s t.
     option_le (OPTION_MAP2 (+) (wl_stack_size (CONS (StackFrame opt ws vs x) ys)) s) t
     ==> option_le (OPTION_MAP2 (+) (wl_stack_size ys) opt) t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_size_eq2] THEN
  CASES_ON `x:(num#num#num)option` THEN REWRITE_TAC[stack_size_frame_def] THEN
  CASES_ON `opt:num option` THEN
  CASES_ON `wl_stack_size (ys:((A)stack_frame)list)` THEN
  CASES_ON `s:num option` THEN CASES_ON `t:num option` THEN
  REWRITE_TAC[OPTION_MAP2_THM; OPTION_MAP_DEF; option_le_def] THEN ARITH_TAC);;

(* HOL4 line 4900 *)
let inter_union_lemma = prove
 (`!(ws:(num#A)list) t (s:B spt).
     ALL (\(x1,x2). x1 = 0) ws ==>
     sptree_inter (sptree_union t (fromAList ws)) (adjust_set s) = sptree_inter t (adjust_set s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[inter_eq; lookup_inter_alt] THEN
  X_GEN_TAC `k:num` THEN COND_CASES_TAC THEN REWRITE_TAC[lookup_union] THEN
  CASES_ON `lookup k (t:A spt)` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[lookup_fromAList; ALOOKUP_NONE] THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `k IN domain (adjust_set (s:B spt))` THEN
    REWRITE_TAC[adjust_set_def; domain_fromAList; MEM_MAP; EXISTS_PROD; adjust_var_def] THEN
    REWRITE_TAC[IN_SET_OF_LIST; MEM_MAP; EXISTS_PROD; FST; PAIR_EQ] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_SET_OF_LIST; MEM_MAP; EXISTS_PROD; FST] THEN
  STRIP_TAC THEN UNDISCH_TAC `ALL (\(x1,x2). x1 = 0) (ws:(num#A)list)` THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `(p1,p2):num#A`) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* GCP2AUX: instantiate the existential of the memory part of state_rel   *)
(* with the variables of the heap_in_memory_store assumption               *)
let gcp2aux_mem_exists_tac : tactic = fun (asl,w as g) ->
  let th = snd(find (fun (_,th) ->
               let c = concl th in
               is_comb c && (let f,_ = strip_comb c in
                             is_const f && fst(dest_const f) = "heap_in_memory_store"))
             asl) in
  let _,args = strip_comb(concl th) in
  (* heap a sp sp1 gens c store m dm limit *)
  let heap = el 0 args and a = el 1 args and sp = el 2 args and sp1 = el 3 args
  and gens = el 4 args and limit = el 9 args in
  MAP_EVERY EXISTS_TAC [heap; limit; a; sp; sp1; gens] g;;

(* GCP2AUX: the variables restored from a stack frame *)
let GCP2AUX_MEM_join_env_fromAList = prove
 (`!(env:data_v spt) (vs:(num#A word_loc)list) e.
     MEM e (join_env env (toAList (sptree_inter (fromAList vs) (adjust_set env)))) ==>
     MEM e (join_env env vs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[join_env_def; MEM_MAP; MEM_FILTER; EXISTS_PROD] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `v:A word_loc` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `v:A word_loc`] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `MEM (k,v:A word_loc) (toAList (sptree_inter (fromAList (vs:(num#A word_loc)list))
                 (adjust_set (env:data_v spt))))` THEN
  REWRITE_TAC[MEM_toAList; lookup_inter_alt; lookup_fromAList] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; ALOOKUP_MEM]);;

(* GCP2AUX: the shapes of data stack frames and word stack frames *)
let GCP2AUX_stack_cases = prove
 (`!fr:stack. (?ss env. fr = data_Env ss env) \/ (?ss env n. fr = Exc ss env n)`,
  MESON_TAC[cases "stack"]);;

let GCP2AUX_stack_frame_cases = prove
 (`!fr:(A)stack_frame. ?m e0 e h. fr = StackFrame m e0 e h`,
  MESON_TAC[cases "stack_frame"]);;

(* GCP2AUX: a stack frame binds no variable 0 *)
let GCP2AUX_ALOOKUP_0_NONE = prove
 (`!(e:(num#A)list). ALL (\(x1,x2). ~(x1 = 0) /\ EVEN x1) e ==> ALOOKUP e 0 = NONE`,
  GEN_TAC THEN REWRITE_TAC[ALOOKUP_NONE; GSYM ALL_MEM; MEM_MAP; EXISTS_PROD; FST] THEN
  DISCH_TAC THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `v:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(k,v):num#A`) THEN ASM_REWRITE_TAC[]);;

(* GCP2AUX: the conjuncts of the stack_rel assumption of a popped frame *)
let gcp2aux_frame_conj k : thm_tactic -> tactic = fun ttac ->
  FIRST_ASSUM(fun th ->
    if is_conj(concl th) && gcp2aux_has_const "ALL_DISTINCT" (concl th)
    then ttac (el k (CONJUNCTS th)) else NO_TAC);;

(* GCP2AUX: the tail of the proofs of the pop_env lemmas *)
let gcp2aux_pop_tail_tac : tactic =
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[lookup_union; lookup_fromAList] THEN
    gcp2aux_frame_conj 0 (SUBST1_TAC o MATCH_MP GCP2AUX_ALOOKUP_0_NONE) THEN
    CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> gcp2aux_has_const "contains_loc" (concl th) &&
                                            not(gcp2aux_has_const "ALL2" (concl th)))) THEN
    REWRITE_TAC[contains_loc_def];
    REWRITE_TAC[is_some_lookup_union] THEN MESON_TAC[];
    FIRST_X_ASSUM(ACCEPT_TAC o MATCH_MP option_le_tl o
      check (fun th -> gcp2aux_has_const "option_le" (concl th) &&
                       gcp2aux_has_const "wl_stack_size" (concl th)));
    ALL_TAC] THEN
  gcp2aux_mem_exists_tac THEN ASM_REWRITE_TAC[] THEN
  gcp2aux_frame_conj 2 (fun th -> REWRITE_TAC[MATCH_MP inter_union_lemma th]) THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "word_ml_inv" o concl)) THEN
  MATCH_MP_TAC word_ml_inv_rearrange THEN
  REWRITE_TAC[MEM_APPEND] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ2_TAC THEN DISJ1_TAC THEN
  MATCH_MP_TAC GCP2AUX_MEM_join_env_fromAList THEN ASM_REWRITE_TAC[];;

(* GCP2AUX: the case analysis that starts the proofs of the pop_env lemmas *)
let gcp2aux_pop_prefix_tac : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALL2 data_to_word_gcProof_stack_rel (data_state_stack (s1:(C,FFI)data_state))
                  (wl_state_stack (t1:(A,C,FFI)wl_state)) /\
                ALL2 contains_loc (wl_state_stack t1) locs` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
  UNDISCH_TAC `data_pop_env (s1:(C,FFI)data_state) = SOME s2` THEN
  REWRITE_TAC[data_pop_env_def; wl_pop_env_def] THEN
  MP_TAC(ISPEC `data_state_stack (s1:(C,FFI)data_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[option_DISTINCT])
    (X_CHOOSE_THEN `fr:stack` (X_CHOOSE_THEN `st:stack list` ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  UNDISCH_TAC `ALL2 data_to_word_gcProof_stack_rel (data_state_stack (s1:(C,FFI)data_state))
                  (wl_state_stack (t1:(A,C,FFI)wl_state))` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `wl_state_stack (t1:(A,C,FFI)wl_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th; ALL2])
    (X_CHOOSE_THEN `wfr:(A)stack_frame` (X_CHOOSE_THEN `wst:((A)stack_frame)list`
       ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[ALL2] THEN STRIP_TAC THEN
  UNDISCH_TAC `ALL2 contains_loc (wl_state_stack (t1:(A,C,FFI)wl_state)) locs` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `locs:(num#num)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th; ALL2])
    (X_CHOOSE_THEN `lc:num#num` (X_CHOOSE_THEN `ll:(num#num)list` SUBST1_TAC))) THEN
  REWRITE_TAC[ALL2] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `lc:num#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l8:num` (X_CHOOSE_THEN `l9:num` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `wfr:(A)stack_frame` GCP2AUX_stack_frame_cases) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num option` (X_CHOOSE_THEN `e0:(num#A word_loc)list`
    (X_CHOOSE_THEN `e:(num#A word_loc)list` (X_CHOOSE_THEN `h:(num#num#num)option`
       SUBST_ALL_TAC)))) THEN
  CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `fr:stack` GCP2AUX_stack_cases) THEN
  DISCH_THEN(DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)) THEN
  (MP_TAC(ISPEC `h:(num#num#num)option` (cases "option")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
     (X_CHOOSE_THEN `hh:num#num#num` SUBST_ALL_TAC))) THEN
  TRY(MP_TAC(ISPEC `hh:num#num#num` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `x1:num` (X_CHOOSE_THEN `x23:num#num` SUBST_ALL_TAC)) THEN
      MP_TAC(ISPEC `x23:num#num` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `x2:num` (X_CHOOSE_THEN `x3:num` SUBST_ALL_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_to_word_gcProof_stack_rel_def]) THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  CASE_REWRITE_TAC[option_INJ];;

(* HOL4 line 4918 *)
let state_rel_pop_env_IMP = prove
 (`!c q l (s1:(C,FFI)data_state) (t1:(A,C,FFI)wl_state) xs locs s2.
     data_to_word_gcProof_state_rel c q l s1 t1 xs locs /\
     data_pop_env s1 = SOME s2 ==>
     ?t2 l8 l9 ll.
       wl_pop_env t1 = SOME t2 /\ locs = CONS (l8,l9) ll /\
       data_to_word_gcProof_state_rel c l8 l9 s2 t2 xs ll`,
  gcp2aux_pop_prefix_tac THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`wl_state_locals_fupd (K (sptree_union (fromAList e) (fromAList e0)))
      (wl_state_stack_fupd (K wst) (wl_state_locals_size_fupd (K m)
        (t1:(A,C,FFI)wl_state)))`;
      `l8:num`; `l9:num`; `ll:(num#num)list`] THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `data_to_word_gcProof_state_rel c q l s1 (t1:(A,C,FFI)wl_state) xs locs` THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_def; data_state_INFO.ri_accfupds;
                wl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[ALL2; flat_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    gcp2aux_pop_tail_tac;
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`wl_state_locals_fupd (K (sptree_union (fromAList e) (fromAList e0)))
      (wl_state_stack_fupd (K wst) (wl_state_locals_size_fupd (K m)
        (wl_state_handler_fupd (K x1) (t1:(A,C,FFI)wl_state))))`;
      `l8:num`; `l9:num`; `ll:(num#num)list`] THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `data_to_word_gcProof_state_rel c q l s1 (t1:(A,C,FFI)wl_state) xs locs` THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_def; data_state_INFO.ri_accfupds;
                wl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[ALL2; flat_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    gcp2aux_pop_tail_tac]);;

(* HOL4 line 4954 *)
let inter_insert_union = prove
 (`!n (x:A) t1 t2 (s:B spt).
     sptree_inter (insert n x (sptree_union t1 t2)) s = sptree_inter (sptree_union (insert n x t1) t2) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[inter_eq; lookup_inter_alt] THEN
  REWRITE_TAC[lookup_insert; lookup_union] THEN GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN CASE_REWRITE_TAC[]);;

(* GCP2AUX: the tail of the proof of state_rel_pop_env_set_var_IMP *)
let gcp2aux_pop_set_var_tail_tac : tactic =
  SUBGOAL_THEN `~(0 = adjust_var q1)` ASSUME_TAC THENL
   [REWRITE_TAC[adjust_var_def] THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[lookup_insert; lookup_union; lookup_fromAList] THEN
    gcp2aux_frame_conj 0 (SUBST1_TAC o MATCH_MP GCP2AUX_ALOOKUP_0_NONE) THEN
    CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> gcp2aux_has_const "contains_loc" (concl th) &&
                                            not(gcp2aux_has_const "ALL2" (concl th)))) THEN
    REWRITE_TAC[contains_loc_def];
    GEN_TAC THEN REWRITE_TAC[lookup_insert; adjust_var_11] THEN
    COND_CASES_TAC THEN REWRITE_TAC[IS_SOME_DEF; is_some_lookup_union] THEN
    gcp2aux_frame_conj 4 (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[];
    FIRST_X_ASSUM(ACCEPT_TAC o MATCH_MP option_le_tl o
      check (fun th -> gcp2aux_has_const "option_le" (concl th) &&
                       gcp2aux_has_const "wl_stack_size" (concl th)));
    ALL_TAC] THEN
  gcp2aux_mem_exists_tac THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[APPEND; inter_insert_union] THEN
  gcp2aux_frame_conj 2 (fun th -> REWRITE_TAC[MATCH_MP inter_union_lemma th]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  MATCH_MP_TAC (REWRITE_RULE[APPEND] word_ml_inv_insert) THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "word_ml_inv" o concl)) THEN
  MATCH_MP_TAC word_ml_inv_rearrange THEN
  REWRITE_TAC[MEM_APPEND; MEM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ2_TAC THEN DISJ1_TAC THEN
  MATCH_MP_TAC GCP2AUX_MEM_join_env_fromAList THEN ASM_REWRITE_TAC[];;

(* HOL4 line 4961 *)
let state_rel_pop_env_set_var_IMP = prove
 (`!c q l (s1:(C,FFI)data_state) (t1:(A,C,FFI)wl_state) a w locs s2 q1.
     data_to_word_gcProof_state_rel c q l s1 t1 (SOME [(a,w)]) locs /\
     data_pop_env s1 = SOME s2 ==>
     ?t2 l8 l9 ll.
       wl_pop_env t1 = SOME t2 /\ locs = CONS (l8,l9) ll /\
       data_to_word_gcProof_state_rel c l8 l9 (data_set_var q1 a s2)
         (wl_set_var (adjust_var q1) w t2) NONE ll`,
  gcp2aux_pop_prefix_tac THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`wl_state_locals_fupd (K (sptree_union (fromAList e) (fromAList e0)))
      (wl_state_stack_fupd (K wst) (wl_state_locals_size_fupd (K m)
        (t1:(A,C,FFI)wl_state)))`;
      `l8:num`; `l9:num`; `ll:(num#num)list`] THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `data_to_word_gcProof_state_rel c q l s1 (t1:(A,C,FFI)wl_state)
                   (SOME [(a,w)]) locs` THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_def; data_state_INFO.ri_accfupds;
                wl_state_INFO.ri_accfupds; K_THM; data_set_var_def; wl_set_var_def] THEN
    ASM_REWRITE_TAC[ALL2; flat_def] THEN CASE_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN gcp2aux_pop_set_var_tail_tac;
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`wl_state_locals_fupd (K (sptree_union (fromAList e) (fromAList e0)))
      (wl_state_stack_fupd (K wst) (wl_state_locals_size_fupd (K m)
        (wl_state_handler_fupd (K x1) (t1:(A,C,FFI)wl_state))))`;
      `l8:num`; `l9:num`; `ll:(num#num)list`] THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `data_to_word_gcProof_state_rel c q l s1 (t1:(A,C,FFI)wl_state)
                   (SOME [(a,w)]) locs` THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_def; data_state_INFO.ri_accfupds;
                wl_state_INFO.ri_accfupds; K_THM; data_set_var_def; wl_set_var_def] THEN
    ASM_REWRITE_TAC[ALL2; flat_def] THEN CASE_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN gcp2aux_pop_set_var_tail_tac]);;

(* HOL4 line 5006 *)
let BUTLASTN_APPEND_LASTN = prove
 (`!n (l:A list). APPEND (BUTLASTN n l) (LASTN n l) = l`,
  REWRITE_TAC[BUTLASTN_DEF; LASTN_DEF; GSYM REVERSE_APPEND; TAKE_DROP; REVERSE_REVERSE]);;

(* HOL4 line 5014 *)
let state_rel_jump_exc = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs n x w s1.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_var n (data_state_locals s) = SOME x /\
     wl_get_var (adjust_var n) t = SOME w /\
     data_jump_exc s = SOME s1 ==>
     ?t1 d1 d2 l5 l6 ll.
       wl_jump_exc t = SOME (t1,d1,d2) /\
       LASTN (LENGTH (data_state_stack s1) + 1) locs = CONS (l5,l6) ll /\
       !i. data_to_word_gcProof_state_rel c l5 l6 (data_set_var i x s1)
             (wl_set_var (adjust_var i) w t1) NONE ll`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALL2 data_to_word_gcProof_stack_rel (data_state_stack (s:(C,FFI)data_state))
                  (wl_state_stack (t:(A,C,FFI)wl_state)) /\
                ALL2 contains_loc (wl_state_stack t) locs /\
                wl_state_handler t = data_state_handler s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
  UNDISCH_TAC `data_jump_exc (s:(C,FFI)data_state) = SOME s1` THEN
  REWRITE_TAC[data_jump_exc_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  ABBREV_TAC `h = data_state_handler (s:(C,FFI)data_state)` THEN
  MP_TAC(ISPEC `LASTN (h + 1) (data_state_stack (s:(C,FFI)data_state))` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[option_DISTINCT])
    (X_CHOOSE_THEN `fr:stack` (X_CHOOSE_THEN `xs:stack list` ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `fr:stack` GCP2AUX_stack_cases) THEN
  DISCH_THEN(DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  MP_TAC(ISPECL [`data_state_stack (s:(C,FFI)data_state)`; `wl_state_stack (t:(A,C,FFI)wl_state)`;
                 `xs:stack list`; `h + 1`; `Exc ss env n'`;
                 `data_to_word_gcProof_stack_rel:stack->(A)stack_frame->bool`]
     LASTN_LIST_REL_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(A)stack_frame` (X_CHOOSE_THEN `ys:((A)stack_frame)list`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`wl_state_stack (t:(A,C,FFI)wl_state)`; `locs:(num#num)list`;
                 `ys:((A)stack_frame)list`; `h + 1`; `y:(A)stack_frame`;
                 `contains_loc:(A)stack_frame->num#num->bool`] LASTN_LIST_REL_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:num#num` (X_CHOOSE_THEN `zs:(num#num)list`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `z:num#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l5:num` (X_CHOOSE_THEN `l6:num` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `y:(A)stack_frame` GCP2AUX_stack_frame_cases) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num option` (X_CHOOSE_THEN `e0:(num#A word_loc)list`
    (X_CHOOSE_THEN `e:(num#A word_loc)list` (X_CHOOSE_THEN `hh:(num#num#num)option`
       SUBST_ALL_TAC)))) THEN
  (MP_TAC(ISPEC `hh:(num#num#num)option` (cases "option")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
     (X_CHOOSE_THEN `hx:num#num#num` SUBST_ALL_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_to_word_gcProof_stack_rel_def]) THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  MP_TAC(ISPEC `hx:num#num#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:num` (X_CHOOSE_THEN `x23:num#num` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `x23:num#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `x2:num` (X_CHOOSE_THEN `x3:num` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_to_word_gcProof_stack_rel_def]) THEN
  SUBGOAL_THEN `LENGTH (xs:stack list) = h` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`data_state_stack (s:(C,FFI)data_state)`; `h + 1`; `Exc ss env n'`;
                   `xs:stack list`] LASTN_CONS_IMP_LENGTH) THEN
    ASM_REWRITE_TAC[LENGTH] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (wl_state_stack (t:(A,C,FFI)wl_state)) =
                LENGTH (data_state_stack (s:(C,FFI)data_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[EVERY2_LENGTH]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`wl_state_handler_fupd (K x1)
     (wl_state_locals_fupd (K (sptree_union (fromAList e) (fromAList e0)))
       (wl_state_stack_fupd (K ys) (wl_state_locals_size_fupd (K m) (t:(A,C,FFI)wl_state))))`;
     `x2:num`; `x3:num`; `l5:num`; `l6:num`; `zs:(num#num)list`] THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[wl_jump_exc_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `h + 1 <= LENGTH (data_state_stack (s:(C,FFI)data_state)) /\
                h + 1 <= LENGTH (wl_state_stack (t:(A,C,FFI)wl_state))` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `h < LENGTH (data_state_stack (s:(C,FFI)data_state))` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. MEM y (data_to_word_gcProof_flat xs ys) \/ MEM y (join_env env e) ==>
                    MEM y (data_to_word_gcProof_flat (data_state_stack (s:(C,FFI)data_state))
                             (wl_state_stack (t:(A,C,FFI)wl_state)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`data_state_stack (s:(C,FFI)data_state)`; `h + 1`;
                   `CONS (Exc m env n') (xs:stack list)`] LASTN_IMP_APPEND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `zs1:stack list` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`wl_state_stack (t:(A,C,FFI)wl_state)`; `h + 1`;
                   `CONS (StackFrame m (e0:(num#A word_loc)list) e (SOME (n',x2,x3)))
                      (ys:((A)stack_frame)list)`] LASTN_IMP_APPEND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `zs2:((A)stack_frame)list` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `LENGTH (zs1:stack list) = LENGTH (zs2:((A)stack_frame)list)` ASSUME_TAC THENL
     [UNDISCH_TAC `LENGTH (wl_state_stack (t:(A,C,FFI)wl_state)) =
                   LENGTH (data_state_stack (s:(C,FFI)data_state))` THEN
      ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[flat_APPEND; flat_def; MEM_APPEND] THEN MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN
  UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 s (t:(A,C,FFI)wl_state) NONE locs` THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_def; data_set_var_def; wl_set_var_def;
              data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds; K_THM] THEN
  CASE_REWRITE_TAC[APPEND] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(0 = adjust_var i)` ASSUME_TAC THENL
   [REWRITE_TAC[adjust_var_def] THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[lookup_insert; lookup_union; lookup_fromAList] THEN
    gcp2aux_frame_conj 0 (SUBST1_TAC o MATCH_MP GCP2AUX_ALOOKUP_0_NONE) THEN
    CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> gcp2aux_has_const "contains_loc" (concl th) &&
                                            not(gcp2aux_has_const "ALL2" (concl th)))) THEN
    REWRITE_TAC[contains_loc_def];
    GEN_TAC THEN REWRITE_TAC[lookup_insert; adjust_var_11] THEN
    COND_CASES_TAC THEN REWRITE_TAC[IS_SOME_DEF; is_some_lookup_union] THEN
    gcp2aux_frame_conj 4 (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[];
    MATCH_MP_TAC option_le_trans THEN
    EXISTS_TAC `OPTION_MAP2 (+) (wl_stack_size (wl_state_stack (t:(A,C,FFI)wl_state)))
                  (wl_state_locals_size t)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC option_le_trans THEN
    EXISTS_TAC `wl_stack_size (wl_state_stack (t:(A,C,FFI)wl_state))` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[option_le_add]] THEN
    MATCH_MP_TAC option_le_trans THEN
    EXISTS_TAC `wl_stack_size (LASTN (h + 1) (wl_state_stack (t:(A,C,FFI)wl_state)))` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[stack_size_eq2; stack_size_frame_def] THEN
      CASES_ON `m:num option` THEN
      CASES_ON `wl_stack_size (ys:((A)stack_frame)list)` THEN
      REWRITE_TAC[OPTION_MAP2_THM; OPTION_MAP_DEF; option_le_def] THEN ARITH_TAC;
      MP_TAC(ISPECL [`h + 1`; `wl_state_stack (t:(A,C,FFI)wl_state)`] BUTLASTN_APPEND_LASTN) THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[option_le_stack_size_append]];
    ALL_TAC] THEN
  gcp2aux_mem_exists_tac THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[inter_insert_union] THEN
  gcp2aux_frame_conj 2 (fun th -> REWRITE_TAC[MATCH_MP inter_union_lemma th]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  MATCH_MP_TAC (REWRITE_RULE[APPEND] word_ml_inv_insert) THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "word_ml_inv" o concl)) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP word_ml_inv_get_var_IMP
    (CONJ th (CONJ (ASSUME `data_get_var n (data_state_locals (s:(C,FFI)data_state)) = SOME x`)
                   (ASSUME `wl_get_var (adjust_var n) (t:(A,C,FFI)wl_state) = SOME w`))))) THEN
  MATCH_MP_TAC word_ml_inv_rearrange THEN
  REWRITE_TAC[MEM_APPEND; MEM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ2_TAC THEN MATCH_MP_TAC GCP2AUX_MEM_join_env_fromAList THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 5106 *)
let data_to_word_gcProof_get_vars_IMP_LENGTH = prove
 (`!x t (s:A spt). data_get_vars x s = SOME t ==> LENGTH x = LENGTH t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[data_get_vars_def] THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[option_INJ] THEN MESON_TAC[LENGTH]; ALL_TAC] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 5113 *)
let get_vars_IMP_LENGTH_word = prove
 (`!x t (s:(A,C,FFI)wl_state). wl_get_vars x s = SOME t ==> LENGTH x = LENGTH t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wl_get_vars_def] THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[option_INJ] THEN MESON_TAC[LENGTH]; ALL_TAC] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 5120 *)
let lookup_adjust_var_fromList2 = prove
 (`!n (w:A) ws. lookup (adjust_var n) (fromList2 (CONS w ws)) = lookup n (fromList ws)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_fromList2; adjust_var_def] THEN
  SUBGOAL_THEN `2 * n + 2 = 2 * SUC n` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[EVEN_DOUBLE; DIV_MULT; ARITH_EQ; lookup_fromList; LENGTH; LT_SUC; EL; TL]);;

(* HOL4 line 5127 *)
let stack_rel_IMP_size_of_stack = prove
 (`!xs (ys:((A)stack_frame)list).
     ALL2 data_to_word_gcProof_stack_rel xs ys ==> wl_stack_size ys = size_of_stack xs`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN CASES_ON `ys:((A)stack_frame)list` THEN
  REWRITE_TAC[ALL2; stack_size_eq2; size_of_stack_def; ITLIST] THEN
  STRIP_TAC THEN REWRITE_TAC[o_THM; GSYM size_of_stack_def] THEN
  FIRST_X_ASSUM(fun th -> FIRST_ASSUM(SUBST1_TAC o MATCH_MP th)) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `data_to_word_gcProof_stack_rel h (a0:(A)stack_frame)` THEN
  CASES_ON `h:stack` THEN CASES_ON `a0:(A)stack_frame` THEN
  CASES_ON `a3:(num#num#num)option` THEN
  REWRITE_TAC[data_to_word_gcProof_stack_rel_def; size_of_stack_frame_def;
              stack_size_frame_def] THEN
  TRY(SPEC_TAC(`a:num#num#num`,`p:num#num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
      REWRITE_TAC[data_to_word_gcProof_stack_rel_def]) THEN
  MESON_TAC[]);;

(* GCP2AUX: the variables of a call environment are the arguments          *)
let GCP2AUX_MEM_join_env_call_env = prove
 (`!(q:B list) (ws:C list) (w0:C) x.
     LENGTH ws = LENGTH q /\
     MEM x (join_env (fromList q)
              (toAList (sptree_inter (fromList2 (CONS w0 ws)) (adjust_set (fromList q))))) ==>
     MEM x (ZIP q ws)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[join_env_def; MEM_MAP; MEM_FILTER; EXISTS_PROD] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `v:C` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `MEM (k,v:C) (toAList (sptree_inter (fromList2 (CONS (w0:C) ws))
                                          (adjust_set (fromList (q:B list)))))` THEN
  REWRITE_TAC[MEM_toAList; lookup_inter_alt] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GCP2AUX_IN_domain_adjust_set]) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[domain_fromList; IN_COUNT]) THEN
  ASM_REWRITE_TAC[lookup_adjust_var_fromList2; lookup_fromList; adjust_var_DIV_2] THEN
  REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ASM_SIMP_TAC[THE_DEF; MEM_ZIP] THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 5142 *)
let state_rel_call_env = prove
 (`!args (s:(C,FFI)data_state) q (t:(A,C,FFI)wl_state) ws c l5 l6 locs l1 l2 ss.
     data_get_vars args (data_state_locals s) = SOME q /\
     wl_get_vars (MAP adjust_var args) t = SOME ws /\
     data_to_word_gcProof_state_rel c l5 l6 s t NONE locs ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_call_env q ss (data_dec_clock s))
       (wl_call_env (CONS (wl_Loc l1 l2) ws) ss (wl_dec_clock t)) NONE locs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (ws:(A word_loc)list) = LENGTH (q:data_v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[data_to_word_gcProof_get_vars_IMP_LENGTH; get_vars_IMP_LENGTH_word;
                  LENGTH_MAP];
    ALL_TAC] THEN
  UNDISCH_TAC `data_to_word_gcProof_state_rel c l5 l6 s (t:(A,C,FFI)wl_state) NONE locs` THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_def; data_call_env_def; wl_call_env_def;
              data_dec_clock_def; wl_dec_clock_def; LET_DEF; LET_END_DEF;
              data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds; K_THM] THEN
  CASE_REWRITE_TAC[APPEND] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `wl_stack_size (wl_state_stack (t:(A,C,FFI)wl_state)) =
                size_of_stack (data_state_stack (s:(C,FFI)data_state))` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC(MATCH_MP stack_rel_IMP_size_of_stack th));
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[lookup_fromList2; EVEN] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[lookup_fromList; LENGTH; LT_0; EL; HD];
    REWRITE_TAC[lookup_adjust_var_fromList2; lookup_fromList] THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[IS_SOME_DEF];
    REWRITE_TAC[option_le_max_right; option_le_refl];
    REWRITE_TAC[option_le_max] THEN CONJ_TAC THEN
    REWRITE_TAC[option_le_max_right; option_le_refl] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp:num`; `sp1:num`; `gens:gen_state`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "word_ml_inv" o concl)) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP word_ml_inv_get_vars_IMP
    (CONJ th (CONJ (ASSUME `data_get_vars args (data_state_locals (s:(C,FFI)data_state)) =
                              SOME q`)
                   (ASSUME `wl_get_vars (MAP adjust_var args) (t:(A,C,FFI)wl_state) =
                              SOME ws`))))) THEN
  MATCH_MP_TAC word_ml_inv_rearrange THEN
  REWRITE_TAC[MEM_APPEND] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ1_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC GCP2AUX_MEM_join_env_call_env THEN
  EXISTS_TAC `wl_Loc l1 l2:A word_loc` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 5188 (HOL4: Q.prove ... |> SPEC_ALL; line 5196 rebinds the name *)
(* to the same theorem)                                                      *)
let data_get_vars_SNOC_IMP = prove
 (`!x1 x2 (s:A spt) x.
     data_get_vars (SNOC x1 x2) s = SOME x ==>
     ?y1 y2. x = SNOC y1 y2 /\
             data_get_var x1 s = SOME y1 /\
             data_get_vars x2 s = SOME y2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[SNOC; data_get_vars_def] THENL
   [CASES_ON `data_get_var x1 (s:A spt)` THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MAP_EVERY EXISTS_TAC [`a:A`; `[]:A list`] THEN
    REWRITE_TAC[SNOC];
    CASES_ON `data_get_var h (s:A spt)` THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    CASES_ON `data_get_vars (SNOC x1 t) (s:A spt)` THEN
    CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:A spt`; `a':A list`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`y1:A`; `CONS (a:A) y2`] THEN
    ASM_REWRITE_TAC[SNOC] THEN CASE_REWRITE_TAC[]]);;

(* HOL4 line 5199 (HOL4: Q.prove ... |> SPEC_ALL; line 5207 rebinds the name *)
(* to the same theorem)                                                      *)
let word_get_vars_SNOC_IMP = prove
 (`!x1 x2 (s:(A,C,FFI)wl_state) x.
     wl_get_vars (SNOC x1 x2) s = SOME x ==>
     ?y1 y2. x = SNOC y1 y2 /\
             wl_get_var x1 s = SOME y1 /\
             wl_get_vars x2 s = SOME y2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[SNOC; wl_get_vars_def] THENL
   [CASES_ON `wl_get_var x1 (s:(A,C,FFI)wl_state)` THEN
    CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MAP_EVERY EXISTS_TAC [`a:(A)word_loc`; `[]:((A)word_loc)list`] THEN
    REWRITE_TAC[SNOC];
    CASES_ON `wl_get_var h (s:(A,C,FFI)wl_state)` THEN
    CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    CASES_ON `wl_get_vars (SNOC x1 t) (s:(A,C,FFI)wl_state)` THEN
    CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:(A,C,FFI)wl_state`; `a':((A)word_loc)list`]) THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`y1:(A)word_loc`; `CONS (a:(A)word_loc) y2`] THEN
    ASM_REWRITE_TAC[SNOC] THEN CASE_REWRITE_TAC[]]);;

(* HOL4 line 5210 *)
let word_ml_inv_CodePtr = prove
 (`!heap be a sp sp1 gens limit ts c (s:(C,FFI)data_state) n (v:A word_loc) xs.
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c (data_state_refs s)
       (CONS (data_CodePtr n,v) xs) ==>
     (v = wl_Loc n 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_ml_inv_def; abs_ml_inv_def; bc_stack_ref_inv_def; MAP; FST; SND] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `ALL2 (\v w. word_addr c v = w) (hs:((A word_loc)heap_address)list)
                 (CONS (v:A word_loc) (MAP SND (xs:(data_v#A word_loc)list)))` THEN
  UNDISCH_TAC `ALL2 (\v x. v_inv c v (data_state_refs (s:(C,FFI)data_state)) (x,f,tf,heap))
                 (CONS (data_CodePtr n) (MAP FST (xs:(data_v#A word_loc)list)))
                 (hs:((A word_loc)heap_address)list)` THEN
  CASES_ON `hs:((A word_loc)heap_address)list` THEN REWRITE_TAC[ALL2] THEN
  REWRITE_TAC[v_inv_def] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[word_addr_def]);;

(* HOL4 line 5219 *)
let state_rel_CodePtr = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs args x y n.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_vars args (data_state_locals s) = SOME x /\
     wl_get_vars (MAP adjust_var args) t = SOME y /\
     LAST x = data_CodePtr n /\ ~(x = []) ==>
     ~(y = []) /\ LAST y = wl_Loc n 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (x:data_v list) = LENGTH (args:num list) /\
                LENGTH (y:(A word_loc)list) = LENGTH args` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[data_to_word_gcProof_get_vars_IMP_LENGTH];
      ASM_MESON_TAC[get_vars_IMP_LENGTH_word; LENGTH_MAP]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(args:num list = [])` ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
  MP_TAC(ISPEC `args:num list` SNOC_CASES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:num` (X_CHOOSE_THEN `x2:num list` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP data_get_vars_SNOC_IMP o
    check (fun th -> is_eq(concl th) && gcp2aux_has_const "data_get_vars" (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:data_v` (X_CHOOSE_THEN `y2:data_v list` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `wl_get_vars (MAP adjust_var (SNOC x1 x2)) (t:(A,C,FFI)wl_state) = SOME y` THEN
  REWRITE_TAC[MAP_SNOC] THEN DISCH_THEN(MP_TAC o MATCH_MP word_get_vars_SNOC_IMP) THEN
  DISCH_THEN(X_CHOOSE_THEN `z1:A word_loc` (X_CHOOSE_THEN `z2:(A word_loc)list`
    STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LAST_SNOC]) THEN REWRITE_TAC[LAST_SNOC] THEN
  RVEQ_TAC THEN
  UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 s (t:(A,C,FFI)wl_state) NONE locs` THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_def] THEN CASE_REWRITE_TAC[APPEND] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "word_ml_inv" o concl)) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP word_ml_inv_get_var_IMP
    (CONJ th (CONJ (ASSUME `data_get_var x1 (data_state_locals (s:(C,FFI)data_state)) =
                              SOME (data_CodePtr n)`)
                   (ASSUME `wl_get_var (adjust_var x1) (t:(A,C,FFI)wl_state) = SOME z1`))))) THEN
  REWRITE_TAC[APPEND] THEN DISCH_THEN(ACCEPT_TAC o MATCH_MP word_ml_inv_CodePtr));;

(* GCP2AUX: get_vars of all but the last variable *)
let GCP2AUX_data_get_vars_BUTLAST = prove
 (`!args (s:A spt) x.
     data_get_vars args s = SOME x /\ ~(args = []) ==>
     data_get_vars (BUTLAST args) s = SOME (BUTLAST x)`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `args:num list` SNOC_CASES) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP data_get_vars_SNOC_IMP) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FRONT_SNOC]);;

let GCP2AUX_wl_get_vars_BUTLAST = prove
 (`!args (s:(A,C,FFI)wl_state) x.
     wl_get_vars (MAP adjust_var args) s = SOME x /\ ~(args = []) ==>
     wl_get_vars (MAP adjust_var (BUTLAST args)) s = SOME (BUTLAST x)`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `args:num list` SNOC_CASES) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[MAP_SNOC] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP word_get_vars_SNOC_IMP) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FRONT_SNOC]);;

(* HOL4 line 5242 (HOL4: Q.prove ... |> SPEC_ALL; line 5277 rebinds the name *)
(* to the same theorem)                                                      *)
let data_to_word_gcProof_find_code_thm = prove
 (`!(s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) c l1 l2 locs args x ws dest fs q r ss.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_vars args (data_state_locals s) = SOME x /\
     wl_get_vars (CONS 0 (MAP adjust_var args)) t = SOME (CONS (wl_Loc l1 l2) ws) /\
     data_find_code dest x (data_state_code s) fs = SOME (q,r,ss) ==>
     ?args1 n1 n2.
       wl_find_code dest (CONS (wl_Loc l1 l2) ws) (wl_state_code t) fs =
         SOME (args1,FST (data_to_word_comp c n1 n2 r),ss) /\
       data_to_word_gcProof_state_rel c l1 l2 (data_call_env q ss (data_dec_clock s))
         (wl_call_env args1 ss (wl_dec_clock t)) NONE locs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wl_get_vars (MAP adjust_var args) (t:(A,C,FFI)wl_state) = SOME ws`
    ASSUME_TAC THENL
   [UNDISCH_TAC `wl_get_vars (CONS 0 (MAP adjust_var args)) (t:(A,C,FFI)wl_state) =
                   SOME (CONS (wl_Loc l1 l2) ws)` THEN
    REWRITE_TAC[wl_get_vars_def] THEN EVERY_CASE_TAC THEN
    REWRITE_TAC[option_INJ; option_DISTINCT; injectivity "list"] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (ws:(A word_loc)list) = LENGTH (x:data_v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[data_to_word_gcProof_get_vars_IMP_LENGTH; get_vars_IMP_LENGTH_word;
                  LENGTH_MAP];
    ALL_TAC] THEN
  SUBGOAL_THEN `data_to_word_gcProof_code_rel c (data_state_code (s:(C,FFI)data_state))
                  (wl_state_code (t:(A,C,FFI)wl_state))` MP_TAC THENL
   [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
  REWRITE_TAC[data_to_word_gcProof_code_rel_def] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
  CASES_ON `dest:num option` THENL
   [FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "data_find_code" o concl)) THEN
    REWRITE_TAC[data_find_code_def] THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT] THEN TOP_CASE_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    SUBGOAL_THEN `~(args:num list = [])` ASSUME_TAC THENL
     [ASM_MESON_TAC[data_to_word_gcProof_get_vars_IMP_LENGTH; LENGTH_EQ_NIL]; ALL_TAC] THEN
    MP_TAC(SPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                  `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `args:num list`;
                  `x:data_v list`; `ws:(A word_loc)list`; `a:num`] state_rel_CodePtr) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`CONS (wl_Loc l1 l2:A word_loc) (BUTLAST ws)`; `a:num`; `2`] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `lookup a (wl_state_code (t:(A,C,FFI)wl_state)) =
                    SOME (x' + 1,FST (data_to_word_comp c a 2 r))` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[wl_find_code_def; NOT_CONS_NIL; LAST; BUTLAST] THEN
      CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[LENGTH; ADD1] THEN CASE_REWRITE_TAC[];
      MATCH_MP_TAC state_rel_call_env THEN
      MAP_EVERY EXISTS_TAC [`BUTLAST (args:num list)`; `l1:num`; `l2:num`] THEN
      ASM_SIMP_TAC[GCP2AUX_data_get_vars_BUTLAST] THEN
      MATCH_MP_TAC GCP2AUX_wl_get_vars_BUTLAST THEN ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "data_find_code" o concl)) THEN
    REWRITE_TAC[data_find_code_def] THEN
    TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT] THEN TOP_CASE_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    SUBGOAL_THEN `lookup a (wl_state_code (t:(A,C,FFI)wl_state)) =
                  SOME (LENGTH (q:data_v list) + 1,FST (data_to_word_comp c a 2 r))`
      ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`CONS (wl_Loc l1 l2:A word_loc) ws`; `a:num`; `2`] THEN
    ASM_REWRITE_TAC[wl_find_code_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[LENGTH; ADD1] THEN
    MATCH_MP_TAC state_rel_call_env THEN
    MAP_EVERY EXISTS_TAC [`args:num list`; `l1:num`; `l2:num`] THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 5280 *)
let cut_env_adjust_set_lookup_0 = prove
 (`!(r:B spt) (t:(A,C,FFI)wl_state) y.
     cut_envs (adjust_sets r) (wl_state_locals t) = SOME y ==>
     lookup 0 (FST y) = lookup 0 (wl_state_locals t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_envs_def; adjust_sets_def; cut_names_def; FST; SND] THEN
  REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[FST; lookup_inter_alt; domain_def; IN_SING]);;

(* HOL4 line 5289 *)
let cut_env_IMP_MEM = prove
 (`!s (r:A spt) x n.
     data_cut_env s r = SOME x ==> (IS_SOME (lookup n x) <=> IS_SOME (lookup n s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_env_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[lookup_mk_wf; lookup_inter_alt] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[SUBSET; domain_lookup; IS_SOME_EXISTS] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[option_DISTINCT]);;

(* HOL4 line 5298 *)
let cut_env_IMP_lookup = prove
 (`!s (r:A spt) x n q.
     wl_cut_env s r = SOME x /\ lookup n x = SOME q ==> lookup n r = SOME q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_cut_env_def; cut_envs_def; cut_names_def] THEN
  REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th) THEN SUBST1_TAC(SYM(CONJUNCT1 th))) THEN
  REWRITE_TAC[lookup_union; lookup_inter_alt] THEN
  CASES_ON `lookup n (r:A spt)` THEN REPEAT COND_CASES_TAC THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ]);;

(* HOL4 line 5309 *)
let cut_env_IMP_lookup_EQ = prove
 (`!r (y:A spt) x n.
     data_cut_env r y = SOME x /\ n IN domain r ==> lookup n x = lookup n y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_env_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[lookup_mk_wf; lookup_inter_alt]);;

(* HOL4 line 5317 *)
let cut_env_res_IS_SOME_IMP = prove
 (`!r (x:A spt) y k.
     cut_envs r x = SOME y /\ IS_SOME (lookup k (SND y)) ==>
     IS_SOME (lookup k x) /\ IS_SOME (lookup k (SND r))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_envs_def; cut_names_def] THEN
  REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th) THEN SUBST1_TAC(SYM(CONJUNCT1 th))) THEN
  REWRITE_TAC[SND; lookup_inter_alt] THEN
  COND_CASES_TAC THEN REWRITE_TAC[IS_SOME_DEF] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
  ASM_MESON_TAC[IS_SOME_EXISTS; domain_lookup]);;

(* HOL4 line 5326 *)
let adjust_var_cut_env_IMP_MEM = prove
 (`!(s:B spt) (r:A spt) x n.
     cut_envs (adjust_sets s) r = SOME x ==>
     domain (SND x) SUBSET EVEN /\
     (IS_SOME (lookup (adjust_var n) (SND x)) <=> IS_SOME (lookup n s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_envs_def; adjust_sets_def; cut_names_def; FST; SND] THEN
  REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[SND] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; domain_inter; IN_INTER; GCP2AUX_IN_domain_adjust_set] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[IN; EVEN_adjust_var];
    ALL_TAC] THEN
  REWRITE_TAC[lookup_inter_alt; GCP2AUX_IN_domain_adjust_set; adjust_var_11] THEN
  REWRITE_TAC[UNWIND_THM1] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF] THENL
   [UNDISCH_TAC `domain (adjust_set (s:B spt)) SUBSET domain (r:A spt)` THEN
    REWRITE_TAC[SUBSET; GCP2AUX_IN_domain_adjust_set] THEN
    DISCH_THEN(MP_TAC o SPEC `adjust_var n`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[domain_lookup] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN
    UNDISCH_TAC `n IN domain (s:B spt)` THEN REWRITE_TAC[domain_lookup] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF];
    UNDISCH_TAC `~(n IN domain (s:B spt))` THEN REWRITE_TAC[domain_lookup] THEN
    CASES_ON `lookup n (s:B spt)` THEN REWRITE_TAC[IS_SOME_DEF] THEN MESON_TAC[]]);;

(* HOL4 line 5353 *)
let NOT_0_domain = prove
 (`!names:A spt. ~(0 IN domain (adjust_set names))`,
  GEN_TAC THEN
  REWRITE_TAC[adjust_set_def; domain_fromAList; IN_SET_OF_LIST; MEM_MAP; EXISTS_PROD; FST;
              PAIR_EQ; adjust_var_def] THEN
  STRIP_TAC THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* HOL4 line 5360 *)
let cut_envs_SND_nonzero = prove
 (`!(r:B spt) (l:A spt) y.
     cut_envs (adjust_sets r) l = SOME y ==> lookup 0 (SND y) = NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_envs_def; adjust_sets_def; cut_names_def; FST; SND] THEN
  REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[SND; lookup_inter_alt; NOT_0_domain]);;

(* HOL4 line 5368 *)
let lookup_adjust_var_after_cut = prove
 (`!p_1 y (z1:A) x l z2.
     lookup (adjust_var p_1) (SND y) = SOME z1 /\
     cut_envs x l = SOME y /\
     lookup (adjust_var p_1) l = SOME z2 ==> z1 = z2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_envs_def; cut_names_def] THEN
  REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) MP_TAC)) THEN
  REWRITE_TAC[SND; lookup_inter_alt] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT] THEN MESON_TAC[option_INJ]);;

(* HOL4 line 5377: val _ = temp_delsimps ["fromAList_def"] *)

(* GCP2AUX: the frame pushed by a call is related to the data environment  *)
let GCP2AUX_push_frame_stack_rel = prove
 (`!r (ls:data_v spt) x (lt:(A word_loc)spt) y perm l' p' lsz.
     data_cut_env r ls = SOME x /\ cut_envs (adjust_sets r) lt = SOME y /\
     env_to_list (SND y) perm = (l',p') ==>
     data_to_word_gcProof_stack_rel (data_Env lsz x)
       (StackFrame lsz (toAList (FST y)) l' NONE)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP env_to_list_lookup_equiv) THEN
  REWRITE_TAC[data_to_word_gcProof_stack_rel_def] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `v:A word_loc`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `v:A word_loc`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`r:num_set`; `lt:(A word_loc)spt`; `y:(A word_loc)spt#(A word_loc)spt`]
        cut_envs_SND_nonzero) THEN ASM_REWRITE_TAC[option_DISTINCT];
      MP_TAC(ISPECL [`r:num_set`; `lt:(A word_loc)spt`; `y:(A word_loc)spt#(A word_loc)spt`;
                     `0`] adjust_var_cut_env_IMP_MEM) THEN
      ASM_REWRITE_TAC[SUBSET; IN; domain_lookup] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_MESON_TAC[]];
    REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; MEM_toAList] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `v:A word_loc`] THEN
    UNDISCH_TAC `cut_envs (adjust_sets (r:num_set)) (lt:(A word_loc)spt) = SOME y` THEN
    REWRITE_TAC[cut_envs_def; adjust_sets_def; cut_names_def; FST; SND] THEN
    REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[FST; lookup_inter_alt; domain_def; IN_SING] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT];
    ASM_MESON_TAC[env_to_list_ALL_DISTINCT];
    GEN_TAC THEN ASM_REWRITE_TAC[lookup_fromAList] THEN
    MP_TAC(ISPECL [`r:num_set`; `lt:(A word_loc)spt`; `y:(A word_loc)spt#(A word_loc)spt`;
                   `n:num`] adjust_var_cut_env_IMP_MEM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    ASM_MESON_TAC[cut_env_IMP_MEM]]);;

(* GCP2AUX: the variables saved by a call are variables of the caller     *)
let GCP2AUX_MEM_join_env_cut = prove
 (`!r (ls:data_v spt) x (lt:(A word_loc)spt) y perm l' p' e.
     data_cut_env r ls = SOME x /\ cut_envs (adjust_sets r) lt = SOME y /\
     env_to_list (SND y) perm = (l',p') /\
     MEM e (join_env x l') ==>
     MEM e (join_env ls (toAList (sptree_inter lt (adjust_set ls))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP env_to_list_lookup_equiv) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GCP2AUX_cut_envs_adjust_sets) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GCP2AUX_data_cut_env) THEN
  UNDISCH_TAC `MEM (e:data_v#A word_loc) (join_env x l')` THEN
  REWRITE_TAC[join_env_def; MEM_MAP; MEM_FILTER; EXISTS_PROD] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `v:A word_loc` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `v:A word_loc`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `v:A word_loc`] o
    check (fun th -> is_forall(concl th) &&
                     is_imp(snd(strip_forall(concl th))))) THEN
  ASM_REWRITE_TAC[lookup_inter_alt] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[GCP2AUX_IN_domain_adjust_set] o
    check (fun th -> concl th = `k IN domain (adjust_set (r:num_set))`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `j IN domain (ls:data_v spt)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MEM_toAList; lookup_inter_alt; adjust_var_DIV_2; lookup_mk_wf] THEN
  REWRITE_TAC[GCP2AUX_IN_domain_adjust_set] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* GCP2AUX: the tactics shared by the two cases of                          *)
(* state_rel_call_env_push_opt                                              *)
let gcp2aux_push_prefix_tac : tactic =
  REWRITE_TAC[wl_push_env_def; wl_dec_clock_def; wl_state_INFO.ri_accfupds;
              LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPEC `env_to_list (SND (y:(A word_loc)spt#(A word_loc)spt))
                  (wl_state_permute (t:(A,C,FFI)wl_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `lv:(num#A word_loc)list`
    (X_CHOOSE_THEN `pv:num->num->num` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `data_to_word_gcProof_stack_rel
                  (data_Env (data_state_locals_size (s:(C,FFI)data_state)) x)
                  (StackFrame (data_state_locals_size s)
                     (toAList (FST (y:(A word_loc)spt#(A word_loc)spt))) lv NONE)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC GCP2AUX_push_frame_stack_rel THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 s (t:(A,C,FFI)wl_state)
                 (SOME (ZIP xs ws)) locs` THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_def; data_call_env_def; wl_call_env_def;
              data_push_env_def; data_dec_clock_def; LET_DEF; LET_END_DEF;
              data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds; K_THM] THEN
  CASE_REWRITE_TAC[APPEND] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ALL2];;

let gcp2aux_push_tail_tac : tactic =
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[lookup_fromList2; EVEN] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[lookup_fromList; LENGTH; LT_0; EL; HD];
    REWRITE_TAC[lookup_adjust_var_fromList2; lookup_fromList] THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[IS_SOME_DEF];
    REWRITE_TAC[contains_loc_def; ALOOKUP_toAList] THEN
    MP_TAC(ISPECL [`r:num_set`; `t:(A,C,FFI)wl_state`; `y:(A word_loc)spt#(A word_loc)spt`]
      cut_env_adjust_set_lookup_0) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[option_le_max_right; option_le_refl];
    REWRITE_TAC[option_le_max] THEN REPEAT CONJ_TAC THEN
    REWRITE_TAC[option_le_max_right; option_le_refl] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp:num`; `sp1:num`; `gens:gen_state`] THEN
  ASM_REWRITE_TAC[flat_def] THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "word_ml_inv" o concl)) THEN
  MATCH_MP_TAC word_ml_inv_rearrange THEN
  REWRITE_TAC[MEM_APPEND] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISJ1_TAC THEN DISJ1_TAC THEN DISJ1_TAC THEN
    MATCH_MP_TAC GCP2AUX_MEM_join_env_call_env THEN
    EXISTS_TAC `wl_Loc q l:A word_loc` THEN ASM_REWRITE_TAC[];
    DISJ1_TAC THEN DISJ1_TAC THEN DISJ2_TAC THEN MATCH_MP_TAC GCP2AUX_MEM_join_env_cut THEN
    MAP_EVERY EXISTS_TAC [`r:num_set`; `x:data_v spt`;
      `y:(A word_loc)spt#(A word_loc)spt`; `wl_state_permute (t:(A,C,FFI)wl_state)`;
      `lv:(num#A word_loc)list`; `pv:num->num->num`] THEN ASM_REWRITE_TAC[]];;

(* HOL4 line 5379 *)
let state_rel_call_env_push_opt = prove
 (`!(opt:(num#(A)wl_prog#num#num)option) c l1 l2 (s:(C,FFI)data_state)
    (t:(A,C,FFI)wl_state) xs ws locs r x y q l ss.
     data_to_word_gcProof_state_rel c l1 l2 s t (SOME (ZIP xs ws)) locs /\
     lookup 0 (wl_state_locals t) = SOME (wl_Loc l1 l2) /\
     LENGTH xs = LENGTH ws /\
     data_cut_env r (data_state_locals s) = SOME x /\
     cut_envs (adjust_sets r) (wl_state_locals t) = SOME y ==>
     data_to_word_gcProof_state_rel c q l
       (data_call_env xs ss (data_push_env x (IS_SOME opt) (data_dec_clock s)))
       (wl_call_env (CONS (wl_Loc q l) ws) ss (wl_push_env y opt (wl_dec_clock t)))
       NONE (CONS (l1,l2) locs)`,
  GEN_TAC THEN CASES_ON `opt:(num#(A)wl_prog#num#num)option` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[IS_SOME_DEF] THENL
   [gcp2aux_push_prefix_tac THEN
    SUBGOAL_THEN `wl_stack_size (CONS (StackFrame
                       (data_state_locals_size (s:(C,FFI)data_state))
                       (toAList (FST (y:(A word_loc)spt#(A word_loc)spt))) lv NONE)
                       (wl_state_stack (t:(A,C,FFI)wl_state))) =
                  size_of_stack (CONS (data_Env (data_state_locals_size s) x)
                                   (data_state_stack s))` SUBST1_TAC THENL
     [MATCH_MP_TAC stack_rel_IMP_size_of_stack THEN ASM_REWRITE_TAC[ALL2]; ALL_TAC] THEN
    gcp2aux_push_tail_tac;
    SPEC_TAC(`a:num#(A)wl_prog#num#num`,`a:num#(A)wl_prog#num#num`) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`a1:num`; `a2:(A)wl_prog`; `a3:num`; `a4:num`] THEN
    gcp2aux_push_prefix_tac THEN
    SUBGOAL_THEN `data_to_word_gcProof_stack_rel
                    (Exc (data_state_locals_size (s:(C,FFI)data_state)) x
                       (data_state_handler s))
                    (StackFrame (data_state_locals_size s)
                       (toAList (FST (y:(A word_loc)spt#(A word_loc)spt))) lv
                       (SOME (data_state_handler s,a3,a4)))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[data_to_word_gcProof_stack_rel_def]; ALL_TAC] THEN
    SUBGOAL_THEN `wl_stack_size (CONS (StackFrame
                       (data_state_locals_size (s:(C,FFI)data_state))
                       (toAList (FST (y:(A word_loc)spt#(A word_loc)spt))) lv
                       (SOME (data_state_handler s,a3,a4)))
                       (wl_state_stack (t:(A,C,FFI)wl_state))) =
                  size_of_stack (CONS (Exc (data_state_locals_size s) x
                                         (data_state_handler s))
                                   (data_state_stack s))` SUBST1_TAC THENL
     [MATCH_MP_TAC stack_rel_IMP_size_of_stack THEN ASM_REWRITE_TAC[ALL2]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[EVERY2_LENGTH]; ALL_TAC] THEN
    gcp2aux_push_tail_tac]);;

(* HOL4 line 5475 *)
let state_rel_call_env_push = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) xs ws locs r x y q l ss.
     data_to_word_gcProof_state_rel c l1 l2 s t (SOME (ZIP xs ws)) locs /\
     LENGTH xs = LENGTH ws /\
     lookup 0 (wl_state_locals t) = SOME (wl_Loc l1 l2) /\
     data_cut_env r (data_state_locals s) = SOME x /\
     cut_envs (adjust_sets r) (wl_state_locals t) = SOME y ==>
     data_to_word_gcProof_state_rel c q l
       (data_call_env xs ss (data_push_env x F (data_dec_clock s)))
       (wl_call_env (CONS (wl_Loc q l) ws) ss (wl_push_env y NONE (wl_dec_clock t)))
       NONE (CONS (l1,l2) locs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `NONE:(num#(A)wl_prog#num#num)option` state_rel_call_env_push_opt) THEN
  REWRITE_TAC[IS_SOME_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
  EXISTS_TAC `r:num_set` THEN ASM_REWRITE_TAC[]);;

(* GCP2AUX: the values of a get_vars can be added in front of the state     *)
(* relation's variable list                                                 *)
let GCP2AUX_state_rel_get_vars_SOME = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs args xs ws.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_vars args (data_state_locals s) = SOME xs /\
     wl_get_vars (MAP adjust_var args) t = SOME ws ==>
     data_to_word_gcProof_state_rel c l1 l2 s t (SOME (ZIP xs ws)) locs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_def] THEN CASE_REWRITE_TAC[APPEND] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  MAP_EVERY EXISTS_TAC
   [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp:num`; `sp1:num`; `gens:gen_state`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "word_ml_inv" o concl)) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP word_ml_inv_get_vars_IMP
    (CONJ th (CONJ (ASSUME `data_get_vars args (data_state_locals (s:(C,FFI)data_state)) =
                              SOME xs`)
                   (ASSUME `wl_get_vars (MAP adjust_var args) (t:(A,C,FFI)wl_state) =
                              SOME ws`))))) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC]);;

(* HOL4 line 5491 *)
let state_rel_call_env_push_env = prove
 (`!(opt:(num#(A)wl_prog#num#num)option) c l1 l2 (s:(C,FFI)data_state)
    (t:(A,C,FFI)wl_state) locs args xs ws r x y q l ss.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_vars args (data_state_locals s) = SOME xs /\
     wl_get_vars (MAP adjust_var args) t = SOME ws /\
     data_cut_env r (data_state_locals s) = SOME x /\
     cut_envs (adjust_sets r) (wl_state_locals t) = SOME y ==>
     data_to_word_gcProof_state_rel c q l
       (data_call_env xs ss (data_push_env x (IS_SOME opt) (data_dec_clock s)))
       (wl_call_env (CONS (wl_Loc q l) ws) ss (wl_push_env y opt (wl_dec_clock t)))
       NONE (CONS (l1,l2) locs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC state_rel_call_env_push_opt THEN
  EXISTS_TAC `r:num_set` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC GCP2AUX_state_rel_get_vars_SOME THEN
    EXISTS_TAC `args:num list` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm];
    ASM_MESON_TAC[data_to_word_gcProof_get_vars_IMP_LENGTH; get_vars_IMP_LENGTH_word;
                  LENGTH_MAP]]);;

(* GCP2AUX: find_code_thm_ret and find_code_thm_handler for any handler    *)
let GCP2AUX_find_code_push = prove
 (`!(opt:(num#(A)wl_prog#num#num)option) c l1 l2 (s:(C,FFI)data_state)
    (t:(A,C,FFI)wl_state) locs args xs ws dest fs ys prog ss r x y q l.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_vars args (data_state_locals s) = SOME xs /\
     wl_get_vars (MAP adjust_var args) t = SOME ws /\
     data_find_code dest xs (data_state_code s) fs = SOME (ys,prog,ss) /\
     data_cut_env r (data_state_locals s) = SOME x /\
     cut_envs (adjust_sets r) (wl_state_locals t) = SOME y ==>
     ?args1 n1 n2.
       wl_find_code dest (CONS (wl_Loc q l) ws) (wl_state_code t) fs =
         SOME (args1,FST (data_to_word_comp c n1 n2 prog),ss) /\
       data_to_word_gcProof_state_rel c q l
         (data_call_env ys ss (data_push_env x (IS_SOME opt) (data_dec_clock s)))
         (wl_call_env args1 ss (wl_push_env y opt (wl_dec_clock t)))
         NONE (CONS (l1,l2) locs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (ws:(A word_loc)list) = LENGTH (xs:data_v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[data_to_word_gcProof_get_vars_IMP_LENGTH; get_vars_IMP_LENGTH_word;
                  LENGTH_MAP];
    ALL_TAC] THEN
  SUBGOAL_THEN `data_to_word_gcProof_code_rel c (data_state_code (s:(C,FFI)data_state))
                  (wl_state_code (t:(A,C,FFI)wl_state))` MP_TAC THENL
   [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
  REWRITE_TAC[data_to_word_gcProof_code_rel_def] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
  CASES_ON `dest:num option` THENL
   [FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "data_find_code" o concl)) THEN
    REWRITE_TAC[data_find_code_def] THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT] THEN TOP_CASE_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    SUBGOAL_THEN `~(args:num list = [])` ASSUME_TAC THENL
     [ASM_MESON_TAC[data_to_word_gcProof_get_vars_IMP_LENGTH; LENGTH_EQ_NIL]; ALL_TAC] THEN
    MP_TAC(SPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                  `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `args:num list`;
                  `xs:data_v list`; `ws:(A word_loc)list`; `a:num`] state_rel_CodePtr) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`CONS (wl_Loc q l:A word_loc) (BUTLAST ws)`; `a:num`; `2`] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `lookup a (wl_state_code (t:(A,C,FFI)wl_state)) =
                    SOME (x' + 1,FST (data_to_word_comp c a 2 prog))` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[wl_find_code_def; NOT_CONS_NIL; LAST; BUTLAST] THEN
      CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[LENGTH; ADD1] THEN CASE_REWRITE_TAC[];
      MATCH_MP_TAC state_rel_call_env_push_env THEN
      MAP_EVERY EXISTS_TAC [`BUTLAST (args:num list)`; `r:num_set`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC GCP2AUX_data_get_vars_BUTLAST THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC GCP2AUX_wl_get_vars_BUTLAST THEN ASM_REWRITE_TAC[]]];
    FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "data_find_code" o concl)) THEN
    REWRITE_TAC[data_find_code_def] THEN
    TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT] THEN TOP_CASE_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    SUBGOAL_THEN `lookup a (wl_state_code (t:(A,C,FFI)wl_state)) =
                  SOME (LENGTH (ys:data_v list) + 1,FST (data_to_word_comp c a 2 prog))`
      ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`CONS (wl_Loc q l:A word_loc) ws`; `a:num`; `2`] THEN
    ASM_REWRITE_TAC[wl_find_code_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[LENGTH; ADD1] THEN
    MATCH_MP_TAC state_rel_call_env_push_env THEN
    MAP_EVERY EXISTS_TAC [`args:num list`; `r:num_set`] THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 5514 *)
let find_code_thm_ret = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs args xs ws dest fs ys
    prog ss r x y q l.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_vars args (data_state_locals s) = SOME xs /\
     wl_get_vars (MAP adjust_var args) t = SOME ws /\
     data_find_code dest xs (data_state_code s) fs = SOME (ys,prog,ss) /\
     data_cut_env r (data_state_locals s) = SOME x /\
     cut_envs (adjust_sets r) (wl_state_locals t) = SOME y ==>
     ?args1 n1 n2.
       wl_find_code dest (CONS (wl_Loc q l) ws) (wl_state_code t) fs =
         SOME (args1,FST (data_to_word_comp c n1 n2 prog),ss) /\
       data_to_word_gcProof_state_rel c q l
         (data_call_env ys ss (data_push_env x F (data_dec_clock s)))
         (wl_call_env args1 ss (wl_push_env y NONE (wl_dec_clock t)))
         NONE (CONS (l1,l2) locs)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `NONE:(num#(A)wl_prog#num#num)option` GCP2AUX_find_code_push) THEN
  REWRITE_TAC[IS_SOME_DEF] THEN DISCH_THEN MATCH_ACCEPT_TAC);;

(* HOL4 line 5553 *)
let find_code_thm_handler = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs args xs ws dest fs ys
    prog ss r x y q l x0 prog1 nn.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_vars args (data_state_locals s) = SOME xs /\
     wl_get_vars (MAP adjust_var args) t = SOME ws /\
     data_find_code dest xs (data_state_code s) fs = SOME (ys,prog,ss) /\
     data_cut_env r (data_state_locals s) = SOME x /\
     cut_envs (adjust_sets r) (wl_state_locals t) = SOME y ==>
     ?args1 n1 n2.
       wl_find_code dest (CONS (wl_Loc q l) ws) (wl_state_code t) fs =
         SOME (args1,FST (data_to_word_comp c n1 n2 prog),ss) /\
       data_to_word_gcProof_state_rel c q l
         (data_call_env ys ss (data_push_env x T (data_dec_clock s)))
         (wl_call_env args1 ss
            (wl_push_env y (SOME (adjust_var x0,(prog1:(A)wl_prog),nn,l + 1))
               (wl_dec_clock t)))
         NONE (CONS (l1,l2) locs)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `SOME (adjust_var x0,(prog1:(A)wl_prog),nn:num,l + 1)` GCP2AUX_find_code_push) THEN
  REWRITE_TAC[IS_SOME_DEF] THEN DISCH_THEN MATCH_ACCEPT_TAC);;

(* HOL4 line 5592 *)
let data_find_code = prove
 (`!dest xs (code:(num#A)spt) (fs:B spt) ys prog ss.
     data_find_code dest xs code fs = SOME (ys,prog,ss) ==> ~bad_dest_args dest xs`,
  GEN_TAC THEN CASES_ON `dest:num option` THEN
  REWRITE_TAC[data_find_code_def; bad_dest_args_def; option_DISTINCT] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]);;

(* HOL4 line 5599 *)
let s_key_eq_LENGTH = prove
 (`!xs (ys:((A)stack_frame)list). s_key_eq xs ys ==> (LENGTH xs = LENGTH ys)`,
  REWRITE_TAC[s_key_eq_def2] THEN MESON_TAC[EVERY2_LENGTH]);;

(* HOL4 line 5605 *)
let data_to_word_gcProof_s_key_eq_LASTN = prove
 (`!xs (ys:((A)stack_frame)list) n.
     s_key_eq xs ys ==> s_key_eq (LASTN n xs) (LASTN n ys)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  CASES_ON `ys:((A)stack_frame)list` THEN REWRITE_TAC[s_key_eq_def; LASTN_ALT] THEN
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (t:((A)stack_frame)list) = LENGTH (a1:((A)stack_frame)list)`
    ASSUME_TAC THENL [ASM_MESON_TAC[s_key_eq_LENGTH]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[s_key_eq_def]);;

(* GCP2AUX: mk_loc of jump_exc only depends on the keys of the stack and   *)
(* the handler                                                              *)
let GCP2AUX_s_key_eq_mk_loc = prove
 (`!(t:(A,C,FFI)wl_state) (t1:(A,C,FFI)wl_state).
     s_key_eq (wl_state_stack t) (wl_state_stack t1) /\
     wl_state_handler t = wl_state_handler t1 ==>
     (mk_loc (wl_jump_exc t1):B word_loc) = mk_loc (wl_jump_exc t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wl_jump_exc_def] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP s_key_eq_LENGTH) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `wl_state_handler (t1:(A,C,FFI)wl_state) + 1` o
    MATCH_MP data_to_word_gcProof_s_key_eq_LASTN) THEN
  SPEC_TAC(`LASTN (wl_state_handler (t1:(A,C,FFI)wl_state) + 1)
              (wl_state_stack (t:(A,C,FFI)wl_state))`,`l1:((A)stack_frame)list`) THEN
  SPEC_TAC(`LASTN (wl_state_handler (t1:(A,C,FFI)wl_state) + 1)
              (wl_state_stack (t1:(A,C,FFI)wl_state))`,`l2:((A)stack_frame)list`) THEN
  REPEAT GEN_TAC THEN CASES_ON `l1:((A)stack_frame)list` THEN
  CASES_ON `l2:((A)stack_frame)list` THEN
  REWRITE_TAC[s_key_eq_def] THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  CASES_ON `a0:(A)stack_frame` THEN CASES_ON `a0':(A)stack_frame` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[s_frame_key_eq_def2]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a3':(num#num#num)option` THEN CASE_REWRITE_TAC[] THEN
  SPEC_TAC(`a:num#num#num`,`p:num#num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CASE_REWRITE_TAC[mk_loc_def]);;

(* GCP2AUX: the stack and handler after a call with a handler frame *)
let GCP2AUX_call_push_SOME = prove
 (`!args1 ss y x1 x2 x3 x4 (t:(A,C,FFI)wl_state).
     wl_state_handler
       (wl_call_env args1 ss (wl_push_env y (SOME (x1,x2,x3,x4)) (wl_dec_clock t))) =
       LENGTH (wl_state_stack t) /\
     wl_state_stack
       (wl_call_env args1 ss (wl_push_env y (SOME (x1,x2,x3,x4)) (wl_dec_clock t))) =
       CONS (StackFrame (wl_state_locals_size t) (toAList (FST y))
               (FST (env_to_list (SND y) (wl_state_permute t)))
               (SOME (wl_state_handler t,x3,x4))) (wl_state_stack t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_push_env_def; wl_call_env_def; wl_dec_clock_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
  MP_TAC(ISPEC `env_to_list (SND (y:(A word_loc)spt#(A word_loc)spt))
                  (wl_state_permute (t:(A,C,FFI)wl_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `lv:(num#A word_loc)list`
    (X_CHOOSE_THEN `pv:num->num->num` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM]);;

(* GCP2AUX: HOL4 eval_push_env_SOME_exc_IMP_s_key_eq (line 5900), which is *)
(* needed before its place in the script                                  *)
let GCP2AUX_push_SOME_exc_s_key_eq = prove
 (`!p args1 ss y x1 x2 x3 x4 (t:(A,C,FFI)wl_state) l w t1.
     wl_evaluate (p,wl_call_env args1 ss
                      (wl_push_env y (SOME (x1,x2,x3,x4)) (wl_dec_clock t))) =
       (SOME (wl_Exception l w),t1) ==>
     s_key_eq (wl_state_stack t1) (wl_state_stack t) /\
     wl_state_handler t = wl_state_handler t1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:(A)wl_prog`; `wl_call_env args1 ss
    (wl_push_env y (SOME (x1,x2,x3,x4)) (wl_dec_clock (t:(A,C,FFI)wl_state)))`]
    wl_evaluate_stack_swap) THEN
  ASM_REWRITE_TAC[GCP2AUX_call_push_SOME] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `n < SUC n`; LASTN_ADD1; injectivity "list";
              injectivity "stack_frame"] THEN
  STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_state_handler"
     with Failure _ -> false))) THEN
  CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

(* GCP2AUX: the stack after a call (any handler) *)
let GCP2AUX_call_push_stack = prove
 (`!args1 ss y (opt:(num#(A)wl_prog#num#num)option) (t:(A,C,FFI)wl_state).
     ?h. wl_state_stack (wl_call_env args1 ss (wl_push_env y opt (wl_dec_clock t))) =
         CONS (StackFrame (wl_state_locals_size t) (toAList (FST y))
                 (FST (env_to_list (SND y) (wl_state_permute t))) h) (wl_state_stack t)`,
  REPEAT GEN_TAC THEN CASES_ON `opt:(num#(A)wl_prog#num#num)option` THENL
   [REWRITE_TAC[wl_push_env_def; wl_call_env_def; wl_dec_clock_def; LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
    MP_TAC(ISPEC `env_to_list (SND (y:(A word_loc)spt#(A word_loc)spt))
                    (wl_state_permute (t:(A,C,FFI)wl_state))` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `lv:(num#A word_loc)list`
      (X_CHOOSE_THEN `pv:num->num->num` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
    MESON_TAC[];
    SPEC_TAC(`a:num#(A)wl_prog#num#num`,`a:num#(A)wl_prog#num#num`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; GCP2AUX_call_push_SOME] THEN MESON_TAC[]]);;

(* HOL4 line 5613 *)
let evaluate_mk_loc_EQ = prove
 (`!q (t:(A,B,C)wl_state) t1.
     wl_evaluate (q,t) = (NONE,t1) ==>
     mk_loc (wl_jump_exc t1) = ((mk_loc (wl_jump_exc t)):A word_loc)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`q:(A)wl_prog`; `t:(A,B,C)wl_state`] wl_evaluate_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC GCP2AUX_s_key_eq_mk_loc THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 5625 *)
let mk_loc_eq_push_env_exc_Exception = prove
 (`!c args1 ss y x0 prog1 x1 l (t:(A,B,C)wl_state) xx w t1.
     wl_evaluate
       (c:(A)wl_prog,
        wl_call_env args1 ss
          (wl_push_env y (SOME (x0,prog1:(A)wl_prog,x1,l)) (wl_dec_clock t))) =
       (SOME (wl_Exception xx w),(t1:(A,B,C)wl_state)) ==>
     mk_loc (wl_jump_exc t1) = (mk_loc (wl_jump_exc t):A word_loc)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP GCP2AUX_push_SOME_exc_s_key_eq) THEN
  STRIP_TAC THEN MATCH_MP_TAC GCP2AUX_s_key_eq_mk_loc THEN
  ASM_MESON_TAC[s_key_eq_sym]);;

(* HOL4 line 5646 *)
let evaluate_IMP_domain_EQ = prove
 (`!c args1 ss y opt (t:(A,B,C)wl_state) ll w t1 t2.
     wl_evaluate
       (c,wl_call_env (args1:(A word_loc)list) ss
            (wl_push_env y (opt:(num#((A)wl_prog)#num#num)option) (wl_dec_clock t))) =
       (SOME (wl_Result ll w),t1) /\ wl_pop_env t1 = SOME t2 ==>
     domain (wl_state_locals t2) = domain (FST y) UNION domain (SND y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(A)wl_prog`; `wl_call_env (args1:(A word_loc)list) ss
    (wl_push_env y (opt:(num#((A)wl_prog)#num#num)option) (wl_dec_clock (t:(A,B,C)wl_state)))`]
    wl_evaluate_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`args1:(A word_loc)list`; `ss:num option`; `y:(A word_loc)spt#(A word_loc)spt`;
    `opt:(num#((A)wl_prog)#num#num)option`; `t:(A,B,C)wl_state`] GCP2AUX_call_push_stack) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:(num#num#num)option` SUBST1_TAC) THEN
  UNDISCH_TAC `wl_pop_env (t1:(A,B,C)wl_state) = SOME t2` THEN
  REWRITE_TAC[wl_pop_env_def] THEN
  MP_TAC(ISPEC `wl_state_stack (t1:(A,B,C)wl_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th; s_key_eq_def])
    (X_CHOOSE_THEN `f1:(A)stack_frame` (X_CHOOSE_THEN `st1:((A)stack_frame)list`
       SUBST1_TAC))) THEN
  MP_TAC(ISPEC `f1:(A)stack_frame` GCP2AUX_stack_frame_cases) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num option` (X_CHOOSE_THEN `e0:(num#A word_loc)list`
    (X_CHOOSE_THEN `e:(num#A word_loc)list` (X_CHOOSE_THEN `h1:(num#num#num)option`
       SUBST1_TAC)))) THEN
  REWRITE_TAC[s_key_eq_def; s_frame_key_eq_def2] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `h1:(num#num#num)option` THEN CASE_REWRITE_TAC[] THEN
  TRY(SPEC_TAC(`a:num#num#num`,`a:num#num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
      CASE_REWRITE_TAC[] THEN REPEAT GEN_TAC) THEN
  REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; domain_union; domain_fromAList] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    gcp2aux_has_const "MAP" (concl th) && not(gcp2aux_has_const "toAList" (concl th)))) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    gcp2aux_has_const "toAList" (concl th))) THEN
  REWRITE_TAC[IL2AUX_env_to_list_domain; set_MAP_FST_toAList_domain; UNION_COMM]);;

(* HOL4 line 5666 *)
let evaluate_IMP_domain_EQ_Exc = prove
 (`!c args1 ss y x0 prog1 x1 l (t:(A,B,C)wl_state) ll w t1.
     wl_evaluate
       (c,wl_call_env args1 ss
            (wl_push_env y (SOME (x0,prog1:(A)wl_prog,x1,l)) (wl_dec_clock t))) =
       (SOME (wl_Exception ll w),t1) ==>
     domain (wl_state_locals t1) = domain (FST y) UNION domain (SND y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(A)wl_prog`; `wl_call_env args1 ss
    (wl_push_env y (SOME (x0,prog1:(A)wl_prog,x1,l)) (wl_dec_clock (t:(A,B,C)wl_state)))`]
    wl_evaluate_stack_swap) THEN
  ASM_REWRITE_TAC[GCP2AUX_call_push_SOME] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `n < SUC n`; LASTN_ADD1; injectivity "list";
              injectivity "stack_frame"] THEN
  STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[domain_union; domain_fromAList] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    gcp2aux_has_const "MAP" (concl th))) THEN
  REWRITE_TAC[IL2AUX_env_to_list_domain; set_MAP_FST_toAList_domain; UNION_COMM]);;

(* HOL4 line 5688 *)
let mk_loc_jump_exc = prove
 (`!args1 ss y n (prog1:(A)wl_prog) x0 l (t:(A,C,FFI)wl_state).
     mk_loc
       (wl_jump_exc
          (wl_call_env args1 ss
             (wl_push_env y (SOME (adjust_var n,prog1,x0,l))
                (wl_dec_clock t)))) = (wl_Loc x0 l:B word_loc)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_push_env_def; LET_DEF; LET_END_DEF] THEN
  PAIRARG_TAC THEN
  REWRITE_TAC[wl_jump_exc_def; wl_call_env_def; wl_dec_clock_def;
              wl_state_INFO.ri_accfupds; K_THM; LENGTH;
              ARITH_RULE `n < SUC n`; LASTN_ADD1] THEN
  CASE_REWRITE_TAC[mk_loc_def]);;

(* HOL4 line 5700 *)
let data_to_word_gcProof_inc_clock_def = cake_def
  `data_to_word_gcProof_inc_clock n (t:(A,C,FFI)wl_state) =
     wl_state_clock_fupd (K (wl_state_clock t + n)) t`;;

(* HOL4 line 5704 *)
let data_to_word_gcProof_inc_clock_0 = prove
 (`!t:(A,C,FFI)wl_state. data_to_word_gcProof_inc_clock 0 t = t`,
  REWRITE_TAC[data_to_word_gcProof_inc_clock_def; ADD_CLAUSES] THEN
  REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM]);;

let _ = cake_add_simps [data_to_word_gcProof_inc_clock_0];;

(* HOL4 line 5710 *)
let data_to_word_gcProof_inc_clock_inc_clock = prove
 (`!t:(A,C,FFI)wl_state n m.
     data_to_word_gcProof_inc_clock n (data_to_word_gcProof_inc_clock m t) =
     data_to_word_gcProof_inc_clock (n + m) t`,
  REWRITE_TAC[data_to_word_gcProof_inc_clock_def; wl_state_INFO.ri_accfupds;
              wl_state_INFO.ri_fupdfupds; K_o_THM; K_THM] THEN
  REWRITE_TAC[ADD_AC]);;

let _ = cake_add_simps [data_to_word_gcProof_inc_clock_inc_clock];;

(* HOL4 line 5716 *)
let mk_loc_jmup_exc_inc_clock = prove
 (`!ck (t:(A,C,FFI)wl_state).
     (mk_loc (wl_jump_exc (data_to_word_gcProof_inc_clock ck t)):B word_loc) =
     mk_loc (wl_jump_exc t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_jump_exc_def; data_to_word_gcProof_inc_clock_def; wl_state_INFO.ri_accfupds] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN EVERY_CASE_TAC THEN REWRITE_TAC[mk_loc_def]);;

let _ = cake_add_simps [mk_loc_jmup_exc_inc_clock];;

(* HOL4 line 5723 *)
let jump_exc_inc_clock_EQ_NONE = prove
 (`!n (s:(A,C,FFI)wl_state).
     wl_jump_exc (data_to_word_gcProof_inc_clock n s) = NONE <=> wl_jump_exc s = NONE`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_jump_exc_def; data_to_word_gcProof_inc_clock_def; wl_state_INFO.ri_accfupds] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT]);;

(* HOL4 line 5730 *)
let state_rel_lookup_globals = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v1 locs g.
     data_to_word_gcProof_state_rel c l1 l2 s t v1 locs /\ data_state_global s = SOME g ==>
     ?x u. FLOOKUP (wl_state_store t) Globals = SOME (wl_Word (get_addr c x u))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "word_ml_inv" o concl)) THEN
  DISCH_THEN(MP_TAC o SPECL [`data_RefPtr T g`;
                              `FAPPLY (wl_state_store (t:(A,C,FFI)wl_state)) Globals`] o
    MATCH_MP (REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM] GCP2AUX_word_ml_inv_MEM)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEM_APPEND; MEM; the_global_def; OPTION_MAP_DEF; misc_the_def]; ALL_TAC] THEN
  REWRITE_TAC[v_inv_RefPtr_T] THEN STRIP_TAC THEN
  UNDISCH_TAC `ALL (\n. n IN FDOM (wl_state_store (t:(A,C,FFI)wl_state))) [Globals]` THEN
  REWRITE_TAC[ALL; FLOOKUP_DEF] THEN DISCH_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
    gcp2aux_has_const "word_addr" (concl th))) THEN
  ASM_REWRITE_TAC[word_addr_def] THEN MESON_TAC[]);;

(* GCP2AUX: the variables of a cut environment are variables of the        *)
(* environment                                                               *)
let GCP2AUX_MEM_join_env_mk_wf = prove
 (`!(ls:data_v spt) (names:num_set) (lt:(A word_loc)spt) e.
     MEM e (join_env (mk_wf (sptree_inter ls names))
              (toAList (sptree_inter lt (adjust_set (mk_wf (sptree_inter ls names)))))) ==>
     MEM e (join_env ls (toAList (sptree_inter lt (adjust_set ls))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[join_env_def; MEM_MAP; MEM_FILTER; EXISTS_PROD] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `v:A word_loc` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `v:A word_loc`] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `MEM (k,v:A word_loc) (toAList (sptree_inter (lt:(A word_loc)spt)
                 (adjust_set (mk_wf (sptree_inter (ls:data_v spt) (names:num_set))))))` THEN
  REWRITE_TAC[MEM_toAList; lookup_inter_alt; GCP2AUX_IN_domain_adjust_set; domain_mk_wf;
              domain_inter; IN_INTER] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[adjust_var_DIV_2; lookup_mk_wf; lookup_inter_alt] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 5761 *)
let state_rel_cut_env = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names x.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_cut_env names (data_state_locals s) = SOME x ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_state_locals_fupd (K x) s) t NONE locs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GCP2AUX_data_cut_env) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 s (t:(A,C,FFI)wl_state) NONE locs` THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM] THEN
  CASE_REWRITE_TAC[APPEND] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[lookup_mk_wf; lookup_inter_alt] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[IS_SOME_DEF];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp:num`; `sp1:num`; `gens:gen_state`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp2aux_has_const "word_ml_inv" o concl)) THEN
  MATCH_MP_TAC word_ml_inv_rearrange THEN
  REWRITE_TAC[MEM_APPEND] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ1_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC GCP2AUX_MEM_join_env_mk_wf THEN
  EXISTS_TAC `names:num_set` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 5790 *)
let state_rel_get_var_Block = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v1 locs n ts tag vs.
     data_to_word_gcProof_state_rel c l1 l2 s t v1 locs /\
     data_get_var n (data_state_locals s) = SOME (data_Block ts tag vs) ==>
     ?w. wl_get_var (adjust_var n) t = SOME (wl_Word w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP state_rel_get_var_IMP) THEN
  DISCH_THEN(MP_TAC o SPECL [`n:num`; `data_Block ts tag vs`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word_loc` ASSUME_TAC) THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `v1:((data_v#A word_loc)list)option`; `locs:(num#num)list`;
    `n:num`; `data_Block ts tag vs`; `w:A word_loc`] GCP2AUX_state_rel_get_var_v_inv) THEN
  ASM_REWRITE_TAC[v_inv_def] THEN STRIP_TAC THEN
  POP_ASSUM(SUBST_ALL_TAC o SYM) THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[word_addr_def; injectivity "word_loc"] THEN MESON_TAC[]);;

(* HOL4 line 5826: val s' = mk_var("s'",type_of s) (a dataSem state) *)

(* HOL4 line 5828 *)
let state_rel_cut_state_opt_get_var = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names_opt x v w.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_cut_state_opt names_opt s = SOME x /\
     data_get_var v (data_state_locals x) = SOME w ==>
     ?s':(C,FFI)data_state.
       data_to_word_gcProof_state_rel c l1 l2 s' t NONE locs /\
       data_get_var v (data_state_locals s') = SOME w`,
  REPEAT GEN_TAC THEN CASES_ON `names_opt:num_set option` THEN
  REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def] THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[option_INJ] THEN STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CASES_ON `data_cut_env a (data_state_locals (s:(C,FFI)data_state))` THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  EXISTS_TAC `data_state_locals_fupd (K a') (s:(C,FFI)data_state)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC state_rel_cut_env THEN
  EXISTS_TAC `a:num_set` THEN ASM_REWRITE_TAC[]);;

(* GCP2AUX: whether jump_exc fails is unchanged by pushing a frame without *)
(* a handler                                                                *)
let GCP2AUX_jump_exc_push_NONE_EQ_NONE = prove
 (`!(s':(A,C,FFI)wl_state) (s:(A,C,FFI)wl_state) n e0 e.
     wl_state_handler s' = wl_state_handler s /\
     wl_state_stack s' = CONS (StackFrame n e0 e NONE) (wl_state_stack s) ==>
     (wl_jump_exc s' = NONE <=> wl_jump_exc s = NONE)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wl_jump_exc_def] THEN
  ASM_REWRITE_TAC[LENGTH] THEN
  ABBREV_TAC `h = wl_state_handler (s:(A,C,FFI)wl_state)` THEN
  ABBREV_TAC `st = wl_state_stack (s:(A,C,FFI)wl_state)` THEN
  ASM_CASES_TAC `h < LENGTH (st:((A)stack_frame)list)` THENL
   [ASM_SIMP_TAC[ARITH_RULE `h < l ==> h < SUC l`; LASTN_TL] THEN
    EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT];
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `h = LENGTH (st:((A)stack_frame)list)` THENL
     [ASM_REWRITE_TAC[ARITH_RULE `l < SUC l`; LASTN_ADD1] THEN CASE_REWRITE_TAC[];
      SUBGOAL_THEN `~(h < SUC (LENGTH (st:((A)stack_frame)list)))`
        (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC]]);;

(* HOL4 line 5843 (allow_rebind) *)
let jump_exc_push_env_NONE_simp = prove
 (`!(t:(A,C,FFI)wl_state) y b.
     (wl_jump_exc (wl_dec_clock t) = NONE <=> wl_jump_exc t = NONE) /\
     (wl_jump_exc (wl_push_env y NONE t) = NONE <=> wl_jump_exc t = NONE) /\
     (wl_jump_exc (wl_state_stack_max_fupd (K b) t) = NONE <=> wl_jump_exc t = NONE)`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[wl_jump_exc_def; wl_dec_clock_def; wl_state_INFO.ri_accfupds] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT];
    MATCH_MP_TAC GCP2AUX_jump_exc_push_NONE_EQ_NONE THEN
    REWRITE_TAC[wl_push_env_def; LET_DEF; LET_END_DEF] THEN
    PAIRARG_TAC THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
    REWRITE_TAC[injectivity "list"; injectivity "stack_frame"] THEN MESON_TAC[];
    REWRITE_TAC[wl_jump_exc_def; wl_state_INFO.ri_accfupds] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT]]);;

(* HOL4 line 5861 *)
let s_key_eq_handler_eq_IMP = prove
 (`!(t:(A,C,FFI)wl_state) (t1:(A,C,FFI)wl_state).
     s_key_eq (wl_state_stack t) (wl_state_stack t1) /\
     wl_state_handler t = wl_state_handler t1 ==>
     (~(wl_jump_exc t1 = NONE) <=> ~(wl_jump_exc t = NONE))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wl_jump_exc_def] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP s_key_eq_LENGTH) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `wl_state_handler (t1:(A,C,FFI)wl_state) + 1` o
    MATCH_MP data_to_word_gcProof_s_key_eq_LASTN) THEN
  SPEC_TAC(`LASTN (wl_state_handler (t1:(A,C,FFI)wl_state) + 1)
              (wl_state_stack (t:(A,C,FFI)wl_state))`,`l1:((A)stack_frame)list`) THEN
  SPEC_TAC(`LASTN (wl_state_handler (t1:(A,C,FFI)wl_state) + 1)
              (wl_state_stack (t1:(A,C,FFI)wl_state))`,`l2:((A)stack_frame)list`) THEN
  REPEAT GEN_TAC THEN CASES_ON `l1:((A)stack_frame)list` THEN
  CASES_ON `l2:((A)stack_frame)list` THEN
  REWRITE_TAC[s_key_eq_def] THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  CASES_ON `a0:(A)stack_frame` THEN CASES_ON `a0':(A)stack_frame` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[s_frame_key_eq_def2]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a3':(num#num#num)option` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  SPEC_TAC(`a:num#num#num`,`p:num#num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CASE_REWRITE_TAC[option_DISTINCT]);;

(* HOL4 line 5873 *)
let eval_NONE_IMP_jump_exc_NONE_EQ = prove
 (`!q (t:(A,C,FFI)wl_state) t1.
     wl_evaluate (q,t) = (NONE,t1) ==> (wl_jump_exc t1 = NONE <=> wl_jump_exc t = NONE)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`q:(A)wl_prog`; `t:(A,C,FFI)wl_state`] wl_evaluate_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(A,C,FFI)wl_state`; `t1:(A,C,FFI)wl_state`] s_key_eq_handler_eq_IMP) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4 line 5880 *)
let jump_exc_push_env_SOME = prove
 (`!y x prog1 l1 l2 (t:(A,C,FFI)wl_state).
     ~(wl_jump_exc (wl_push_env y (SOME (x,prog1,l1,l2)) t) = NONE)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_push_env_def; LET_DEF; LET_END_DEF] THEN
  PAIRARG_TAC THEN
  REWRITE_TAC[wl_jump_exc_def; wl_state_INFO.ri_accfupds; K_THM; LENGTH;
              ARITH_RULE `n < SUC n`; LASTN_ADD1] THEN
  CASE_REWRITE_TAC[option_DISTINCT]);;

(* GCP2AUX: raising out of a call with a handler frame restores the stack  *)
let GCP2AUX_data_jump_exc_push_T = prove
 (`!ys ss x (s:(C,FFI)data_state) s2.
     data_jump_exc (data_call_env ys ss (data_push_env x T (data_dec_clock s))) = SOME s2
     ==> data_state_stack s2 = data_state_stack s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_jump_exc_def; data_call_env_def; data_push_env_def; data_dec_clock_def;
              LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM; LENGTH;
              ARITH_RULE `n < SUC n`; LASTN_ADD1] THEN
  CASE_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

(* GCP2AUX: raising out of a call without a handler frame shortens the     *)
(* stack                                                                     *)
let GCP2AUX_data_jump_exc_push_F = prove
 (`!ys ss x (s:(C,FFI)data_state) s2.
     data_jump_exc (data_call_env ys ss (data_push_env x F (data_dec_clock s))) = SOME s2
     ==> LENGTH (data_state_stack s2) < LENGTH (data_state_stack s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_jump_exc_def; data_call_env_def; data_push_env_def; data_dec_clock_def;
              LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM; LENGTH] THEN
  ABBREV_TAC `h = data_state_handler (s:(C,FFI)data_state)` THEN
  ABBREV_TAC `st = data_state_stack (s:(C,FFI)data_state)` THEN
  ASM_CASES_TAC `h < LENGTH (st:stack list)` THENL
   [ASM_SIMP_TAC[ARITH_RULE `h < l ==> h < SUC l`; LASTN_TL] THEN
    MP_TAC(ISPECL [`st:stack list`; `h + 1`] LENGTH_LASTN_LESS) THEN
    SPEC_TAC(`LASTN (h + 1) (st:stack list)`,`l:stack list`) THEN
    GEN_TAC THEN CASES_ON `l:stack list` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
    CASES_ON `a0:stack` THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `h = LENGTH (st:stack list)` THENL
     [ASM_REWRITE_TAC[ARITH_RULE `l < SUC l`; LASTN_ADD1] THEN
      CASE_REWRITE_TAC[option_DISTINCT];
      SUBGOAL_THEN `~(h < SUC (LENGTH (st:stack list)))`
        (fun th -> REWRITE_TAC[th; option_DISTINCT]) THEN ASM_ARITH_TAC]]);;

(* HOL4 line 5888 *)
let eval_push_env_T_Raise_IMP_stack_length = prove
 (`!p ys ss x (s:(C,FFI)data_state) a r'.
     data_evaluate (p,data_call_env ys ss (data_push_env x T (data_dec_clock s))) =
       (SOME (Rerr (Rraise a)),r') ==>
     LENGTH (data_state_stack r') = LENGTH (data_state_stack s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:data_prog`;
     `data_call_env ys ss (data_push_env x T (data_dec_clock (s:(C,FFI)data_state)))`]
     data_evaluate_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "data_state_stack"
    with Failure _ -> false)) THEN
  ASM_MESON_TAC[GCP2AUX_data_jump_exc_push_T]);;

(* HOL4 line 5900 *)
let eval_push_env_SOME_exc_IMP_s_key_eq = prove
 (`!p args1 ss y x1 x2 x3 x4 (t:(A,C,FFI)wl_state) l w t1.
     wl_evaluate (p,wl_call_env args1 ss
                      (wl_push_env y (SOME (x1,x2,x3,x4)) (wl_dec_clock t))) =
       (SOME (wl_Exception l w),t1) ==>
     s_key_eq (wl_state_stack t1) (wl_state_stack t) /\
     wl_state_handler t = wl_state_handler t1`,
  MATCH_ACCEPT_TAC GCP2AUX_push_SOME_exc_s_key_eq);;

(* HOL4 line 5915 *)
let eval_exc_stack_shorter = prove
 (`!c ys ss x (s:(C,FFI)data_state) a r'.
     data_evaluate (c,data_call_env ys ss (data_push_env x F (data_dec_clock s))) =
       (SOME (Rerr (Rraise a)),r') ==>
     LENGTH (data_state_stack r') < LENGTH (data_state_stack s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:data_prog`;
     `data_call_env ys ss (data_push_env x F (data_dec_clock (s:(C,FFI)data_state)))`]
     data_evaluate_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "data_state_stack"
    with Failure _ -> false)) THEN
  ASM_MESON_TAC[GCP2AUX_data_jump_exc_push_F]);;
