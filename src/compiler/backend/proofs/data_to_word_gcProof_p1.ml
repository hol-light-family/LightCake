(* ========================================================================= *)
(* data_to_word_gcProof_p1: part 1 of 3 (HOL4 lines 1-3000) of the port of   *)
(* HOL4 compiler/backend/proofs/data_to_word_gcProofScript.sml (CakeML       *)
(* v3479).  Part of the correctness proof for data_to_word.                  *)
(* The parts _p1, _p2, _p3 are loaded one after the other (each needs the    *)
(* previous one); data_to_word_gcProof.ml needs the last.                    *)
(* GCP1AUX_ names are local helpers of this part.                            *)
(* Rendering: HOL4 'a ml_heap is written out as                              *)
(*   ((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list *)
(* and HOL4 Type state (wordSem state) is (A,C,FFI)wl_state; wordSem is a    *)
(* qualified ancestor in HOL4, so its constants are the wl_ ones.            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/sptree.ml";;
needs "hol4/int_bitwise.ml";;
needs "hol4/set_sep.ml";;
needs "hol4/multiword.ml";;
needs "basis/pure/mllist.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/gc/gen_gc_partial.ml";;
needs "compiler/backend/gc/gc_combined.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/proofs/word_simpProof.ml";;
needs "compiler/backend/proofs/word_gcFunctions.ml";;
needs "compiler/backend/proofs/word_bignumProof.ml";;
needs "compiler/backend/proofs/data_to_word_memoryProof.ml";;
(* HOL4 ancestors not needed by the definitions and statements:             *)
(* semanticsProps, While (alignment is in hol4/words4.ml)                   *)

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Helpers (GCP1AUX_ names, gcp1_ functions; after the helpers of memoryProof *)
(* part 4).  Separation logic: the work of HOL4 helperLib's SEP_R_TAC,      *)
(* SEP_W_TAC, SEP_F_TAC and of fs [AC STAR_ASSOC STAR_COMM].  An assertion  *)
(* is a left-associated STAR tree; its leaves are compared up to            *)
(* alpha-conversion.                                                         *)
(* ------------------------------------------------------------------------- *)

let GCP1AUX_STAR_AC = prove
 (`(!p q:(A->bool)->bool. p STAR q = q STAR p) /\
   (!p q r:(A->bool)->bool. (p STAR q) STAR r = p STAR (q STAR r)) /\
   (!p q r:(A->bool)->bool. p STAR (q STAR r) = q STAR (p STAR r))`,
  MESON_TAC[STAR_COMM; STAR_ASSOC]);;

let GCP1AUX_write_fun2set_one = prove
 (`!(y:A) (a:B) x f d.
     set_sep_one (a,x) (fun2set (f,d))
     ==> set_sep_one (a,y) (fun2set ((a =+ y) f,d))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!(p:(B#A->bool)->bool) s. p s <=> (p STAR emp) s`
    (fun th -> ONCE_REWRITE_TAC[th]) THENL [REWRITE_TAC[SEP_CLAUSES]; ALL_TAC] THEN
  REWRITE_TAC[one_fun2set; APPLY_UPDATE_THM; emp_def; fun2set_EMPTY] THEN
  SIMP_TAC[]);;

let gcp1_is_star tm =
  try let f,_ = dest_comb tm in
      let s,_ = dest_comb f in
      is_const s && fst(dest_const s) = "STAR"
  with Failure _ -> false;;

let rec gcp1_star_leaves tm =
  if gcp1_is_star tm then gcp1_star_leaves (rand(rator tm)) @ gcp1_star_leaves (rand tm)
  else [tm];;

let gcp1_mk_star p q =
  let x = fst(dest_fun_ty(fst(dest_fun_ty(type_of p)))) in
  mk_comb(mk_comb(mk_const("STAR",[x,`:A`]),p),q);;

let gcp1_list_mk_star l =
  match l with
    [] -> failwith "gcp1_list_mk_star"
  | h::t -> rev_itlist (fun x acc -> gcp1_mk_star acc x) t h;;

let gcp1_is_app name tm =
  try let f,_ = strip_comb tm in is_const f && fst(dest_const f) = name
  with Failure _ -> false;;

let gcp1_is_one tm =
  try let f,_ = dest_comb tm in is_const f && fst(dest_const f) = "set_sep_one"
  with Failure _ -> false;;

let rec gcp1_remove_first p l =
  match l with
    [] -> failwith "gcp1_remove_first"
  | h::t -> if p h then t else h :: gcp1_remove_first p t;;

(* |- p = q for STAR trees p, q equal up to AC *)
let GCP1AUX_STAR_AC_EQ p q =
  if aconv p q then REFL p else AC GCP1AUX_STAR_AC (mk_eq(p,q));;

(* th : |- p s  ->  |- q s  (p, q equal up to AC) *)
let GCP1AUX_STAR_AC_RULE q th =
  let p,s = dest_comb(concl th) in
  EQ_MP (AP_THM (GCP1AUX_STAR_AC_EQ p q) s) th;;

(* th : |- p s; puts the first leaf satisfying pr in front:                 *)
(*   |- (leaf STAR rest) s   (rest a left-associated STAR of the others)     *)
let GCP1AUX_STAR_FOCUS pr th =
  let p,s = dest_comb(concl th) in
  let leaves = gcp1_star_leaves p in
  let leaf = find pr leaves in
  let rest = gcp1_remove_first (fun l -> l == leaf) leaves in
  GCP1AUX_STAR_AC_RULE (gcp1_mk_star leaf (gcp1_list_mk_star rest)) th;;

(* reading: th : |- p (fun2set (m,dm)) gives |- m a = x /\ a IN dm for     *)
(* every leaf set_sep_one (a,x) of p                                        *)
let GCP1AUX_SEP_READS th =
  let p,s = dest_comb(concl th) in
  let leaves = gcp1_star_leaves p in
  let ones = filter gcp1_is_one leaves in
  if length leaves = 1 then
    (if ones = [] then [] else [MATCH_MP one_fun2set_IMP th])
  else
    map (fun leaf ->
           let rest = gcp1_remove_first (fun l -> l == leaf) leaves in
           let th1 = GCP1AUX_STAR_AC_RULE
                       (gcp1_mk_star leaf (gcp1_list_mk_star rest)) th in
           MATCH_MP read_fun2set th1) ones;;

let gcp1_is_fun2set_asm tm =
  try let _,s = dest_comb tm in
      let f,_ = dest_comb s in
      is_const f && fst(dest_const f) = "fun2set"
  with Failure _ -> false;;

(* HOL4 SEP_R_TAC: the reads of every fun2set assumption as assumptions   *)
let GCP1AUX_SEP_R_TAC : tactic = fun (asl,w as g) ->
  let ths = flat (map (fun (_,th) ->
                   if gcp1_is_fun2set_asm (concl th)
                   then (try GCP1AUX_SEP_READS th with Failure _ -> [])
                   else []) asl) in
  let ths = flat (map CONJUNCTS ths) in
  let ths = filter (fun th -> not (exists (fun (_,a) -> aconv (concl a) (concl th)) asl))
                   ths in
  MAP_EVERY ASSUME_TAC ths g;;

(* writing: th : |- p (fun2set (m,dm)) with a leaf set_sep_one (a,x) gives *)
(* |- p' (fun2set ((a =+ y) m,dm)), p' = p with that leaf set_sep_one (a,y) *)
let GCP1AUX_SEP_WRITE a y th =
  let p,s = dest_comb(concl th) in
  let leaves = gcp1_star_leaves p in
  let leaf = find (fun l -> gcp1_is_one l && aconv (fst(dest_pair(rand l))) a) leaves in
  let newleaf = mk_comb(rator leaf,mk_pair(a,y)) in
  let leaves' = map (fun l -> if l == leaf then newleaf else l) leaves in
  if length leaves = 1 then
    SPEC y (MATCH_MP GCP1AUX_write_fun2set_one th)
  else
    let rest = gcp1_remove_first (fun l -> l == leaf) leaves in
    let th1 = GCP1AUX_STAR_AC_RULE (gcp1_mk_star leaf (gcp1_list_mk_star rest)) th in
    let th2 = SPEC y (MATCH_MP write_fun2set th1) in
    GCP1AUX_STAR_AC_RULE (gcp1_list_mk_star leaves') th2;;

(* the updates of an update chain (a1 =+ y1) ((a2 =+ y2) ... m), outermost *)
(* first, and m                                                              *)
let rec gcp1_dest_updates tm =
  try let f,m = dest_comb tm in
      let g,y = dest_comb f in
      let u,a = dest_comb g in
      if is_const u && fst(dest_const u) = "=+" then
        let l,m0 = gcp1_dest_updates m in (a,y)::l,m0
      else [],tm
  with Failure _ -> [],tm;;

(* th : |- p (fun2set (m,dm)); upd an update chain over m: the assertion    *)
(* with the written leaves, on fun2set (upd,dm)                             *)
let GCP1AUX_SEP_WRITES upd th =
  let ups,_ = gcp1_dest_updates upd in
  rev_itlist (fun (a,y) th -> GCP1AUX_SEP_WRITE a y th) (rev ups) th;;

(* HOL4 SEP_W_TAC: for a fun2set assumption over m and the biggest update  *)
(* chain over m in the goal, the written assertion as a new assumption     *)
let GCP1AUX_SEP_W_TAC : tactic = fun (asl,w as g) ->
  let cands = filter (fun (_,th) -> gcp1_is_fun2set_asm (concl th)) asl in
  let try_one (_,th) =
    let _,s = dest_comb(concl th) in
    let m = lhand(rand s) in
    let ups = find_terms (fun t -> let l,m0 = gcp1_dest_updates t in
                                   l <> [] && aconv m0 m) w in
    let ups = sort (fun x y -> length(fst(gcp1_dest_updates x)) >
                               length(fst(gcp1_dest_updates y))) ups in
    let up = hd ups in
    GCP1AUX_SEP_WRITES up th in
  ASSUME_TAC (tryfind try_one cands) g;;

(* closes a goal  q s  with an assumption  p s,  p and q equal up to AC    *)
let GCP1AUX_SEP_AC_TAC : tactic = fun (asl,w as g) ->
  let q,s = dest_comb w in
  let ql = gcp1_star_leaves q in
  let ok (_,th) =
    let c = concl th in
    is_comb c && aconv (rand c) s &&
    let pl = gcp1_star_leaves (rator c) in
    length pl = length ql in
  tryfind (fun (_,th as a) ->
             if ok a then ACCEPT_TAC (GCP1AUX_STAR_AC_RULE q th) g
             else failwith "") asl;;

(* ------------------------------------------------------------------------- *)
(* Bit-level reasoning about words built from numerals (any word size).     *)
(* ------------------------------------------------------------------------- *)

let GCP1AUX_DIV_2EXP_0 = prove
 (`!n k i. n < 2 EXP k /\ k <= i ==> n DIV 2 EXP i = 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_LT THEN MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `2 EXP k` THEN ASM_REWRITE_TAC[LE_EXP; ARITH_EQ]);;

let gcp1_num_bits n =
  let rec f k p = if n </ p then k else f (k + 1) (p */ Num.num_of_int 2) in
  f 0 (Num.num_of_int 1);;

(* rewrites every  n DIV 2 EXP e  (n a numeral, e not) with 0 when the      *)
(* assumptions give  k <= e  for the bit length k of n                       *)
let GCP1AUX_DIV_2EXP_0_TAC : tactic = fun (asl,w as g) ->
  let is_target t =
    is_binary "DIV" t && is_numeral (lhand t) &&
    (let r = rand t in is_binary "EXP" r && is_numeral (lhand r) &&
                       dest_numeral (lhand r) =/ Num.num_of_int 2 &&
                       not (is_numeral (rand r))) in
  let tms = setify (find_terms is_target w) in
  let tac tm =
    let n = dest_numeral (lhand tm) in
    let k = gcp1_num_bits n in
    let e = rand(rand tm) in
    let th = SPECL [lhand tm; mk_small_numeral k; e] GCP1AUX_DIV_2EXP_0 in
    TRY(SUBGOAL_THEN (mk_eq(tm,`0`)) SUBST1_TAC THENL
         [MATCH_MP_TAC th THEN CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
          REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC]) in
  MAP_EVERY tac tms g;;

let GCP1AUX_BIT_REWRS =
  [BIT_WORD_OR; BIT_WORD_AND; BIT_WORD_SHL; BIT_WORD_USHR; BIT_WORD_NOT;
   BIT_WORD_XOR; BIT_WORD; BIT_WORD_0];;

(* goal  !i. i < dimindex(:N) ==> P i  over bits of numeral words: split    *)
(* i < k (enumerated) and k <= i (numerals of at most k bits vanish)         *)
let GCP1AUX_BITS_CASES_TAC k =
  let i = `i:num` in
  let lt = mk_binary "<" (i,mk_small_numeral k) in
  let enum = ARITH_RULE (mk_imp(lt, list_mk_disj
               (map (fun j -> mk_eq(i,mk_small_numeral j)) (0--(k-1))))) in
  X_GEN_TAC i THEN DISCH_TAC THEN
  ASM_CASES_TAC lt THENL
   [FIRST_ASSUM(fun th -> if concl th = lt then
                            REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC (MATCH_MP enum th)
                          else NO_TAC) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    GCP1AUX_DIV_2EXP_0_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC];;

(* equations of words built with numerals, or, and, not, shifts *)
let GCP1AUX_WORD_BITS_TAC k =
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN REWRITE_TAC GCP1AUX_BIT_REWRS THEN
  GCP1AUX_BITS_CASES_TAC k;;

(* split the cond leaves of a STAR assertion: |- P s gives the conditions  *)
(* and the assertion without them (as a list of theorems)                  *)
let rec GCP1AUX_SEP_COND_RULE th =
  let p,s = dest_comb (concl th) in
  let leaves = gcp1_star_leaves p in
  match filter (gcp1_is_app "cond") leaves with
    [] -> [th]
  | cd::_ ->
      if length leaves = 1 then [CONJUNCT2 (REWRITE_RULE[cond_def] th)]
      else
        let th1 = GCP1AUX_STAR_FOCUS (fun l -> l == cd) th in
        let th2 = CONV_RULE (REWR_CONV (CONJUNCT1 (SPEC_ALL cond_STAR))) th1 in
        CONJUNCT1 th2 :: GCP1AUX_SEP_COND_RULE (CONJUNCT2 th2);;

let GCP1AUX_SEP_COND_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if gcp1_is_fun2set_asm c &&
       exists (gcp1_is_app "cond") (gcp1_star_leaves (rator c))
    then MAP_EVERY STRIP_ASSUME_TAC (GCP1AUX_SEP_COND_RULE th)
    else failwith "GCP1AUX_SEP_COND_TAC"));;

let gcp1_is_sep_exists tm =
  try let f,b = dest_comb tm in
      is_const f && fst(dest_const f) = "SEP_EXISTS" && is_abs b
  with Failure _ -> false;;

(* |- P s with a leaf SEP_EXISTS v. p v: |- ?v. (p v STAR rest) s          *)
let GCP1AUX_SEP_EXISTS_RULE th =
  let p,s = dest_comb (concl th) in
  let leaves = gcp1_star_leaves p in
  let ex = find gcp1_is_sep_exists leaves in
  if length leaves = 1 then REWRITE_RULE[SEP_EXISTS_THM] th else
  let th1 = GCP1AUX_STAR_FOCUS (fun l -> l == ex) th in
  let th2 = CONV_RULE (RATOR_CONV (REWR_CONV (CONJUNCT1 (SPEC_ALL SEP_CLAUSES)))) th1 in
  CONV_RULE (REWR_CONV SEP_EXISTS_THM) th2;;

(* strip all SEP_EXISTS leaves of the fun2set assumptions *)
let GCP1AUX_SEP_EXISTS_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if gcp1_is_fun2set_asm c &&
       exists gcp1_is_sep_exists (gcp1_star_leaves (rator c))
    then CAKE_STRIP_ASSUME_TAC (GCP1AUX_SEP_EXISTS_RULE th)
    else failwith "GCP1AUX_SEP_EXISTS_TAC"));;

(* the assertion with the given leaves in front, in this order, then the   *)
(* rest (as one STAR term)                                                   *)
let GCP1AUX_STAR_FRONT leaves th =
  let p,s = dest_comb(concl th) in
  let all = gcp1_star_leaves p in
  let rec remove l acc =
    match l with
      [] -> acc
    | x::t -> remove t (gcp1_remove_first (fun y -> aconv x y) acc) in
  let rest = remove leaves all in
  let front = gcp1_list_mk_star leaves in
  let q = if rest = [] then front else gcp1_mk_star front (gcp1_list_mk_star rest) in
  GCP1AUX_STAR_AC_RULE q th;;

(* the frame of an assertion after taking out the given leaves *)
let gcp1_frame_of p leaves =
  let all = gcp1_star_leaves p in
  let rec remove l acc =
    match l with
      [] -> acc
    | x::t -> remove t (gcp1_remove_first (fun y -> aconv x y) acc) in
  gcp1_list_mk_star (remove leaves all);;

(* HOL4 SEP_F_TAC: the goal  (!frame. A1 /\ ... /\ (frame STAR L1 ... Lk)  *)
(* (fun2set (m,dm)) /\ ... ==> C) ==> G  with an assumption  P (fun2set    *)
(* (m,dm)) whose leaves contain L1 ... Lk: frame is instantiated with the  *)
(* other leaves of P and the assertion conjunct is proved from the          *)
(* assumption (AC); the goal becomes  (A1 /\ ... ==> C) ==> G.             *)
let GCP1AUX_SEP_FRAME_TAC : tactic = fun (asl,w as g) ->
  let ant,_ = dest_imp w in
  let fv,body = dest_forall ant in
  let hyp,_ = dest_imp body in
  let cj = conjuncts hyp in
  let sepc = find (fun c -> gcp1_is_fun2set_asm c && free_in fv c) cj in
  let p,s = dest_comb sepc in
  let pleaves = filter (fun l -> not (l = fv)) (gcp1_star_leaves p) in
  let _,asm = find (fun (_,th) -> gcp1_is_fun2set_asm (concl th) &&
                                  aconv (rand (concl th)) s &&
                                  (let ql = gcp1_star_leaves (rator (concl th)) in
                                   forall (fun l -> exists (aconv l) ql) pleaves)) asl in
  let q = rator (concl asm) in
  let frame = gcp1_frame_of q pleaves in
  let sepc' = vsubst [frame,fv] sepc in
  let septh = GCP1AUX_STAR_AC_RULE (rator sepc') asm in
  (DISCH_THEN(MP_TAC o SPEC frame) THEN REWRITE_TAC[septh]) g;;

(* case splits on the bit atoms (bit i w with i or w not numerals) of the  *)
(* goal, each followed by ASM_REWRITE_TAC[]                                 *)
let GCP1AUX_BIT_SPLIT_TAC : tactic =
  let one : tactic = fun (asl,w as g) ->
    let t = find_term (fun t -> gcp1_is_app "bit" t && type_of t = bool_ty &&
                                not (is_const (rand t) || is_numeral (rand t))) w in
    (ASM_CASES_TAC t THEN ASM_REWRITE_TAC[]) g in
  REPEAT one;;

(* move the first assumption  f ... = t  (f the constant name) into the goal *)
let GCP1AUX_UNDISCH_EQ name : tactic =
  FIRST_X_ASSUM(fun th -> let c = concl th in
    if is_eq c && gcp1_is_app name (lhs c) then MP_TAC th
    else failwith "GCP1AUX_UNDISCH_EQ");;

(* the goal  p s  with the first leaf satisfying pr put in front:          *)
(*   (leaf STAR rest) s                                                      *)
let GCP1AUX_SEP_FOCUS_GOAL_TAC pr : tactic = fun (asl,w as g) ->
  let p,s = dest_comb w in
  let leaves = gcp1_star_leaves p in
  let leaf = find pr leaves in
  let rest = gcp1_remove_first (fun l -> l == leaf) leaves in
  if rest = [] then ALL_TAC g else
  let q = gcp1_mk_star leaf (gcp1_list_mk_star rest) in
  CONV_TAC(RATOR_CONV(fun t -> GCP1AUX_STAR_AC_EQ t q)) g;;

(* substitute the assumptions  e = v  for the variables named in vs *)
let GCP1AUX_SUBST_VARS_TAC (vs:string list) : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_var (rhs c) && mem (fst(dest_var(rhs c))) vs &&
       not (free_in (rhs c) (lhs c))
    then SUBST_ALL_TAC (SYM th) else failwith "GCP1AUX_SUBST_VARS_TAC"));;

(* split a tuple-valued term tm into new variables with the given names:   *)
(* the assumption  tm = (v1,...,vk)  is added and the goal rewritten with  *)
(* it (case constants of the tuple reduced)                                 *)
let GCP1AUX_TUPLE_TAC (tm:term) (names:string list) : tactic = fun (asl,w as g) ->
  let k = length names in
  let rec comps ty k =
    if k = 1 then [ty] else
    match dest_type ty with
      "prod",[a;b] -> a :: comps b (k-1)
    | _ -> failwith "GCP1AUX_TUPLE_TAC" in
  let tys = comps (type_of tm) k in
  let avoid = itlist (union o thm_frees o snd) asl (frees w) in
  let vs = itlist (fun (n,ty) acc -> variant (acc @ avoid) (mk_var(n,ty)) :: acc)
                  (rev (zip names tys)) [] in
  let vs = rev vs in
  let rec projs t k =
    if k = 1 then [t] else
    let a,b = match dest_type (type_of t) with
        "prod",[a;b] -> a,b | _ -> failwith "GCP1AUX_TUPLE_TAC" in
    mk_comb(mk_const("FST",[a,`:A`; b,`:B`]),t) ::
    projs (mk_comb(mk_const("SND",[a,`:A`; b,`:B`]),t)) (k-1) in
  let ps = projs tm k in
  let tup = end_itlist (curry mk_pair) vs in
  let ex = list_mk_exists(vs, mk_eq(tm,tup)) in
  let exth = prove(ex, MAP_EVERY EXISTS_TAC ps THEN REWRITE_TAC[PAIR]) in
  (MP_TAC exth THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC vs THEN
   DISCH_THEN(fun th -> ASSUME_TAC th THEN REWRITE_TAC[th] THEN CASE_REWRITE_TAC[])) g;;

(* substitute the assumptions  v = e  for the variables named in vs *)
let GCP1AUX_SUBST_LVARS_TAC (vs:string list) : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_var (lhs c) && mem (fst(dest_var(lhs c))) vs &&
       not (free_in (lhs c) (rhs c))
    then SUBST_ALL_TAC th else failwith "GCP1AUX_SUBST_LVARS_TAC"));;

(* decide the arithmetic atoms (relations on num) of the goal that follow  *)
(* (or whose negation follows) from the arithmetic assumptions             *)
let gcp1_is_num_rel t =
  (is_binary "<" t || is_binary "<=" t || is_binary ">" t || is_binary ">=" t ||
   is_eq t) && (try type_of (lhand t) = `:num` with Failure _ -> false);;

let rec gcp1_is_arith t =
  if is_neg t then gcp1_is_arith (rand t)
  else if is_conj t || is_disj t || is_imp t then
    gcp1_is_arith (lhand t) && gcp1_is_arith (rand t)
  else gcp1_is_num_rel t;;

let GCP1AUX_DECIDE_TAC : tactic = fun (asl,w as g) ->
  let hyps = filter (fun (_,th) -> gcp1_is_arith (concl th)) asl in
  let hth = if hyps = [] then TRUTH else end_itlist CONJ (map snd hyps) in
  let atoms = setify (find_terms gcp1_is_num_rel w) in
  let try_atom t =
    try [EQT_INTRO (MP (ARITH_RULE (mk_imp(concl hth, t))) hth)]
    with Failure _ ->
    try [EQF_INTRO (MP (ARITH_RULE (mk_imp(concl hth, mk_neg t))) hth)]
    with Failure _ -> [] in
  let ths = flat (map try_atom atoms) in
  (if ths = [] then ALL_TAC else REWRITE_TAC ths) g;;

(* th : |- A1 /\ ... /\ An ==> C  with every Ai an assumption (up to alpha):  *)
(* C is added to the goal as an antecedent (avoids the collapse trap of      *)
(* MP_TAC followed by ASM_REWRITE_TAC)                                        *)
let GCP1AUX_ASM_MP (th:thm) : tactic = fun (asl,w as g) ->
  let ants,c = dest_imp (concl th) in
  let prove_cj t =
    try snd (find (fun (_,a) -> aconv (concl a) t) asl)
    with Failure _ -> failwith "GCP1AUX_ASM_MP" in
  let cth = end_itlist CONJ (map prove_cj (conjuncts ants)) in
  MP_TAC (MP th cth) g;;

(* for every assumption A ==> B whose antecedent is an assumption: B *)
let GCP1AUX_MP_ASM_TAC : tactic = fun (asl,w as g) ->
  let ths = mapfilter (fun (_,th) -> let c = concl th in
     if is_imp c then
       let a = lhand c in
       let _,ath = find (fun (_,t) -> aconv (concl t) a) asl in MP th ath
     else failwith "") asl in
  MAP_EVERY STRIP_ASSUME_TAC ths g;;

(* ARITH_TAC with the arithmetic assumptions only *)
let GCP1AUX_ARITH_TAC : tactic = fun (asl,w as g) ->
  let ths = filter (fun th -> gcp1_is_arith (concl th)) (map snd asl) in
  (MAP_EVERY MP_TAC ths THEN ARITH_TAC) g;;

(* split the first (pair-valued) application of the constant name in the   *)
(* goal into two new variables                                               *)
let GCP1AUX_SPLIT_APP_TAC name : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> gcp1_is_app name t &&
                              (try fst(dest_type(type_of t)) = "prod" with Failure _ -> false) &&
                              not (exists (fun v -> free_in v t) (fst(strip_forall w)))) w in
  GCP1AUX_TUPLE_TAC t ["p1";"p2"] g;;

(* split the first tuple-valued application of the constant name in the   *)
(* goal into new variables with the given names                            *)
let GCP1AUX_SPLITN_TAC name names : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> gcp1_is_app name t &&
                              (try fst(dest_type(type_of t)) = "prod" with Failure _ -> false) &&
                              not (exists (fun v -> free_in v t) (fst(strip_forall w)))) w in
  GCP1AUX_TUPLE_TAC t names g;;

(* ===== PART 1: HOL4 lines 1-3000 ===== *)

(* HOL4 line 38 *)
let LESS_EQ_IMP_APPEND_ALT = prove
 (`!n (xs:A list). n <= LENGTH xs ==> ?ys zs. xs = APPEND ys zs /\ LENGTH zs = n`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`TAKE (LENGTH (xs:A list) - n) xs`;
                        `DROP (LENGTH (xs:A list) - n) xs`] THEN
  REWRITE_TAC[TAKE_DROP; LENGTH_DROP] THEN ASM_ARITH_TAC);;

(* HOL4 line 49 *)
let word_asr_dimindex = prove
 (`!(w:A word) n. dimindex (:A) <= n ==>
                  (word_ishr w n = word_ishr w (dimindex (:A) - 1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ISHR] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `(:A)` DIMINDEX_GE_1) THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(i + n < dimindex(:A))` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 56 *)
let WORD_MUL_BIT0 = prove
 (`!a b:A word. bit 0 (word_mul a b) <=> bit 0 a /\ bit 0 b`,
  REWRITE_TAC[BIT_LSB; VAL_WORD_MUL; ODD_MOD_POW2; DIMINDEX_NONZERO; ODD_MULT]);;

(* HOL4 line 63 *)
let word_lsl_index = prove
 (`!i (w:A word) n.
     i < dimindex(:A) ==> (bit i (word_shl w n) <=> n <= i /\ bit (i - n) w)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[BIT_WORD_SHL]);;

(* HOL4 line 70 *)
let word_lsr_index = prove
 (`!i (w:A word) n.
     i < dimindex(:A) ==>
     (bit i (word_ushr w n) <=> i + n < dimindex(:A) /\ bit (i + n) w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BIT_WORD_USHR] THEN
  GEN_REWRITE_TAC LAND_CONV [BIT_GUARD] THEN REWRITE_TAC[]);;

(* HOL4 line 77 *)
let lsr_lsl = prove
 (`!(w:A word) n. alignment_aligned n w ==> word_shl (word_ushr w n) n = w`,
  REWRITE_TAC[aligned_def; align_shift]);;

(* HOL4 line 83 *)
let word_index_test = prove
 (`!n (w:A word).
     n < dimindex (:A) ==> (bit n w <=> ~(word_and w (word (2 EXP n)) = word 0))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_POW2; BIT_WORD_0] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN ASM_MESON_TAC[]);;

(* HOL4 line 89 (same in stack_alloc) *)
let data_to_word_gcProof_word_and_one_eq_0_iff = prove
 (`!w:A word. (word_and w (word 1) = word 0) <=> ~(bit 0 w)`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_1; BIT_WORD_0] THEN
  MESON_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> 0 < n`]);;

(* HOL4 line 95 *)
let word_index_0 = prove
 (`!w:A word. bit 0 w <=> ~(word_and (word 1) w = word 0)`,
  MESON_TAC[data_to_word_gcProof_word_and_one_eq_0_iff; WORD_AND_SYM]);;

(* HOL4 line 101 *)
let ABS_w2n = prove
 (`!w:A word. abs (&(val w):int) = &(val w)`,
  REWRITE_TAC[INT_ABS_NUM]);;

let _ = cake_add_simps [ABS_w2n];;

(* HOL4 line 107 *)
let n2mw_w2n = prove
 (`!w:A word. n2mw (val w) = if w = word 0 then [] else [w]`,
  GEN_TAC THEN ONCE_REWRITE_TAC[n2mw_def] THEN REWRITE_TAC[VAL_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[w2n_lt; MOD_LT; DIV_LT; WORD_VAL] THEN
  ONCE_REWRITE_TAC[n2mw_def] THEN REWRITE_TAC[]);;

(* HOL4 line 116 (wordSem get_var and set_var, as in the HOL4 proof) *)
let data_to_word_gcProof_get_var_set_var = prove
 (`!n (w:A word_loc) (s:(A,C,FFI)wl_state). wl_get_var n (wl_set_var n w s) = SOME w`,
  SIMP[wl_get_var_def; wl_set_var_def; lookup_insert]);;

let _ = cake_add_simps [data_to_word_gcProof_get_var_set_var];;

(* HOL4 line 122 *)
let data_to_word_gcProof_set_var_set_var = prove
 (`!n (v:A word_loc) w (s:(A,C,FFI)wl_state).
     wl_set_var n v (wl_set_var n w s) = wl_set_var n v s`,
  SIMP[wl_set_var_def; insert_shadow]);;

let _ = cake_add_simps [data_to_word_gcProof_set_var_set_var];;

(* HOL4 line 129 *)
let toAList_LN = prove
 (`toAList (LN:A spt) = []`,
  REWRITE_TAC[toAList_def; foldi_def]);;

let _ = cake_add_simps [toAList_LN];;

(* HOL4 line 135 *)
let adjust_set_LN = prove
 (`adjust_set (LN:A spt) = LN`,
  REWRITE_TAC[adjust_set_def; toAList_LN; MAP; fromAList_def]);;

let _ = cake_add_simps [adjust_set_LN];;

(* HOL4 line 141 *)
let push_env_termdep = prove
 (`!y opt (t:(A,C,FFI)wl_state).
     wl_state_termdep (wl_push_env y opt t) = wl_state_termdep t`,
  GEN_TAC THEN REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT STRIP_TAC THEN PAIRARG_TAC THEN SIMP[]);;

(* HOL4 line 149 *)
let ALOOKUP_SKIP_LEMMA = prove
 (`!n (xs:(A#B)list) d e ys.
     ~MEM n (MAP FST xs) /\ d = e ==>
     ALOOKUP (APPEND (APPEND xs [(n,d)]) ys) n = SOME e`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; ALOOKUP_def; MAP; MEM] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; ALOOKUP_def; FST; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [ASM_MESON_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 156 *)
let LAST_EQ = prove
 (`!(x:A) xs. (LAST (CONS x xs) = if xs = [] then x else LAST xs) /\
              (BUTLAST (CONS x xs) = if xs = [] then [] else CONS x (BUTLAST xs))`,
  REWRITE_TAC[LAST; BUTLAST]);;

(* HOL4 line 163 (the unused bound variables y ys are left out) *)
let LASTN_LIST_REL_LEMMA = prove
 (`!xs1 (ys1:B list) (xs:A list) n x P.
     LASTN n xs1 = CONS x xs /\ ALL2 P xs1 ys1 ==>
     ?y ys. LASTN n ys1 = CONS y ys /\ P x y /\ ALL2 P xs ys`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ALL2 (P:A->B->bool) (LASTN n xs1) (LASTN n ys1)` MP_TAC THENL
   [REWRITE_TAC[LASTN_DROP_UNCOND] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP EVERY2_LENGTH) THEN
    MATCH_MP_TAC EVERY2_DROP THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`LASTN n (ys1:B list)`,`l:B list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; NOT_CONS_NIL; CONS_11] THEN
    MESON_TAC[]]);;

(* HOL4 line 176 *)
let LASTN_CONS_IMP_LENGTH = prove
 (`!(xs:A list) n y ys.
     n <= LENGTH xs ==> (LASTN n xs = CONS y ys) ==> LENGTH (CONS y ys) = n`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[LENGTH_LASTN]);;

(* HOL4 line 185 *)
let LASTN_IMP_APPEND = prove
 (`!(xs:A list) n ys.
     n <= LENGTH xs /\ (LASTN n xs = ys) ==> ?zs. xs = APPEND zs ys /\ LENGTH ys = n`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  EXISTS_TAC `BUTLASTN n (xs:A list)` THEN
  ASM_SIMP_TAC[APPEND_BUTLASTN_LASTN; LENGTH_LASTN]);;

(* HOL4 line 195 *)
let NOT_NIL_IMP_LAST = prove
 (`!(xs:A list) x. ~(xs = []) ==> LAST (CONS x xs) = LAST xs`,
  SIMP_TAC[LAST]);;

(* HOL4 line 201 *)
let IS_SOME_IF = prove
 (`!b (x:A option) y. IS_SOME (if b then x else y) = if b then IS_SOME x else IS_SOME y`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* HOL4 line 207 *)
let IS_SOME_ALOOKUP_EQ = prove
 (`!(l:(A#B)list) x. IS_SOME (ALOOKUP l x) = MEM x (MAP FST l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_def; MAP; MEM; IS_SOME_DEF] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; ALOOKUP_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 214 *)
let MEM_IMP_IS_SOME_ALOOKUP = prove
 (`!(l:(A#B)list) x y. MEM (x,y) l ==> IS_SOME (ALOOKUP l x)`,
  REWRITE_TAC[IS_SOME_ALOOKUP_EQ; MEM_MAP; EXISTS_PAIR_THM] THEN MESON_TAC[]);;

(* HOL4 line 220 *)
let SUBSET_INSERT_EQ_SUBSET = prove
 (`!(x:A) s t. ~(x IN s) ==> (s SUBSET (x INSERT t) <=> s SUBSET t)`,
  SET_TAC[]);;

(* HOL4 line 226 *)
let data_to_word_gcProof_EVERY2_IMP_EL = prove
 (`!(xs:A list) (ys:B list) P n. ALL2 P xs ys /\ n < LENGTH ys ==> P (EL n xs) (EL n ys)`,
  REWRITE_TAC[LIST_REL_EL_EQN] THEN MESON_TAC[]);;

(* HOL4 line 233 *)
let FST_PAIR_EQ = prove
 (`!(x:A#B) v. (FST x,v) = x <=> v = SND x`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 239 *)
let EVERY2_APPEND_IMP = prove
 (`!(xs1:A list) xs2 (zs:B list) P.
     ALL2 P (APPEND xs1 xs2) zs ==>
     ?zs1 zs2. zs = APPEND zs1 zs2 /\ ALL2 P xs1 zs1 /\ ALL2 P xs2 zs2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND] THENL
   [MESON_TAC[APPEND; ALL2]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `zs:B list` list_CASES) THEN
  REWRITE_TAC[ALL2] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
  MAP_EVERY EXISTS_TAC [`CONS (h':B) zs1`; `zs2:B list`] THEN
  ASM_REWRITE_TAC[APPEND; ALL2]);;

(* HOL4 line 249 *)
let ZIP_ID = prove
 (`!xs:(A#B)list. ZIP (MAP FST xs) (MAP SND xs) = xs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ZIP]);;

(* HOL4 line 255 *)
let FOLDL_LENGTH_LEMMA = prove
 (`!(xs:A list) k l d q r.
     FOLDL (\(i,t) a. (i + d,insert i a t)) (k,l) xs = (q,r) ==>
     q = LENGTH xs * d + k`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL; LENGTH; PAIR_EQ] THENL
   [ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC);;

(* HOL4 line 263 *)
let fromList_SNOC = prove
 (`!(xs:A list) y. fromList (SNOC y xs) = insert (LENGTH xs) y (fromList xs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fromList_def; SNOC_APPEND; FOLDL_APPEND; FOLDL] THEN
  MP_TAC(ISPECL [`xs:A list`; `0`; `LN:A spt`; `1`] FOLDL_LENGTH_LEMMA) THEN
  SPEC_TAC(`FOLDL (\(i,t) (a:A). (i + 1,insert i a t)) (0,LN) xs`,`p:num#A spt`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[SND] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPECL [`p1:num`; `p2:A spt`]) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

(* HOL4 line 271 *)
let fromList2_SNOC = prove
 (`!(xs:A list) y. fromList2 (SNOC y xs) = insert (2 * LENGTH xs) y (fromList2 xs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fromList2_def; SNOC_APPEND; FOLDL_APPEND; FOLDL] THEN
  MP_TAC(ISPECL [`xs:A list`; `0`; `LN:A spt`; `2`] FOLDL_LENGTH_LEMMA) THEN
  SPEC_TAC(`FOLDL (\(i,t) (a:A). (i + 2,insert i a t)) (0,LN) xs`,`p:num#A spt`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[SND] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPECL [`p1:num`; `p2:A spt`]) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MULT_SYM]);;

(* HOL4 line 285 *)
let join_env_def = cake_def
  `join_env (env:A spt) (vs:(num#B)list) =
     MAP (\(n,v). (THE (lookup ((n - 2) DIV 2) env),v))
       (FILTER (\(n,v). ~(n = 0) /\ EVEN n) vs)`;;

(* HOL4 line 291 *)
let flat_def = cake_def
  `(data_to_word_gcProof_flat (CONS (data_Env _ env) xs)
         (CONS (StackFrame _ _ (vs:(num#(A)word_loc)list) _) ys) =
      APPEND (join_env env vs) (data_to_word_gcProof_flat xs ys)) /\
   (data_to_word_gcProof_flat (CONS (Exc _ env _) xs) (CONS (StackFrame _ _ vs _) ys) =
      APPEND (join_env env vs) (data_to_word_gcProof_flat xs ys)) /\
   (data_to_word_gcProof_flat _ _ = [])`;;

(* HOL4 flat_ind (made by Definition) *)
let flat_ind = cake_ind "data_to_word_gcProof_flat";;

(* HOL4 line 299 *)
let flat_APPEND = prove
 (`!xs (ys:((A)stack_frame)list) xs1 ys1.
     LENGTH xs = LENGTH ys ==>
     data_to_word_gcProof_flat (APPEND xs xs1) (APPEND ys ys1) = APPEND (data_to_word_gcProof_flat xs ys) (data_to_word_gcProof_flat xs1 ys1)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; APPEND; flat_def] THEN
  REPEAT STRIP_TAC THEN
  CASES_ON `h:stack` THEN CASES_ON `h':(A)stack_frame` THEN
  SIMP[flat_def; APPEND_ASSOC]);;

(* HOL4 line 309 *)
let adjust_var_DIV_2 = prove
 (`!n. (adjust_var n - 2) DIV 2 = n`,
  SIMP_TAC[adjust_var_def; ADD_SUB; DIV_MULT; ARITH_EQ]);;

(* HOL4 line 315 *)
let adjust_var_DIV_2_ANY = prove
 (`!n. (adjust_var n) DIV 2 = n + 1`,
  GEN_TAC THEN REWRITE_TAC[adjust_var_def; ARITH_RULE `2 * n + 2 = 2 * (n + 1)`] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

(* HOL4 line 321 *)
let EVEN_adjust_var = prove
 (`!n. EVEN (adjust_var n)`,
  REWRITE_TAC[adjust_var_def; EVEN_ADD; EVEN_MULT; ARITH]);;

(* HOL4 line 328 *)
let adjust_var_eq_numeral = prove
 (`!n k. adjust_var n = NUMERAL k <=>
         EVEN (NUMERAL k) /\ ~(NUMERAL k = 0) /\ n = (NUMERAL k - 2) DIV 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[adjust_var_def] THEN
  SPEC_TAC(`NUMERAL k`,`kk:num`) THEN GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH; ADD_SUB] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ] THEN ARITH_TAC;
    REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN
    UNDISCH_TAC `~(kk = 0)` THEN UNDISCH_TAC `n = (kk - 2) DIV 2` THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `(2 * m - 2) DIV 2 = m - 1`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [SUBGOAL_THEN `2 * m - 2 = 2 * (m - 1)` SUBST1_TAC THENL
       [ARITH_TAC; SIMP_TAC[DIV_MULT; ARITH_EQ]];
      ASM_ARITH_TAC]]);;

let _ = cake_add_simps [adjust_var_eq_numeral];;

(* HOL4 line 342 *)
let adjust_var_NEQ_0 = prove
 (`!n. ~(adjust_var n = 0)`,
  REWRITE_TAC[adjust_var_def] THEN ARITH_TAC);;

let _ = cake_add_simps [adjust_var_NEQ_0];;

(* HOL4 line 348 *)
let adjust_var_NEQ_1 = prove
 (`!n. ~(adjust_var n = 1)`,
  REWRITE_TAC[adjust_var_eq_numeral] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 354 *)
let adjust_var_NEQ = prove
 (`!n. ~(adjust_var n = 0) /\
       ~(adjust_var n = 1) /\
       ~(adjust_var n = 3) /\
       ~(adjust_var n = 5) /\
       ~(adjust_var n = 7) /\
       ~(adjust_var n = 9) /\
       ~(adjust_var n = 11) /\
       ~(adjust_var n = 13)`,
  REWRITE_TAC[adjust_var_eq_numeral] THEN CONV_TAC NUM_REDUCE_CONV);;

let _ = cake_add_simps [adjust_var_NEQ];;

(* HOL4 line 367 *)
let unit_opt_eq = prove
 (`!x y:1 option. (x = y) <=> (IS_SOME x <=> IS_SOME y)`,
  REWRITE_TAC[FORALL_OPTION_THM; IS_SOME_DEF; option_DISTINCT; option_INJ] THEN
  MESON_TAC[one]);;

(* HOL4 line 373 *)
let adjust_var_11 = prove
 (`!n m. (adjust_var n = adjust_var m) <=> n = m`,
  REWRITE_TAC[adjust_var_def] THEN ARITH_TAC);;

(* HOL4 line 379 *)
let lookup_adjust_var_adjust_set = prove
 (`!n s:num_set. lookup (adjust_var n) (adjust_set s) = lookup n s`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[unit_opt_eq] THEN
  REWRITE_TAC[adjust_set_def; lookup_fromAList; IS_SOME_ALOOKUP_EQ] THEN
  REWRITE_TAC[MAP_MAP_o; o_DEF; MEM_MAP; EXISTS_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[FST; MEM_toAList; PAIR_EQ] THEN
  CASES_ON `lookup n (s:num_set)` THEN REWRITE_TAC[IS_SOME_DEF] THEN
  ASM_MESON_TAC[adjust_var_11; option_DISTINCT]);;

(* HOL4 line 388 *)
let adjust_var_IN_adjust_set = prove
 (`!n s:num_set. adjust_var n IN domain (adjust_set s) <=> n IN domain s`,
  REWRITE_TAC[domain_lookup; lookup_adjust_var_adjust_set]);;

(* HOL4 line 394 *)
let none_opt_eq = prove
 (`!(x:A option) (y:B option). ((x = NONE) <=> (y = NONE)) <=> (IS_SOME x <=> IS_SOME y)`,
  REWRITE_TAC[FORALL_OPTION_THM; IS_SOME_DEF; option_DISTINCT]);;

(* HOL4 line 400 *)
let lookup_adjust_var_adjust_set_NONE = prove
 (`!n s:A spt. lookup (adjust_var n) (adjust_set s) = NONE <=> lookup n s = NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[none_opt_eq] THEN
  REWRITE_TAC[adjust_set_def; lookup_fromAList; IS_SOME_ALOOKUP_EQ] THEN
  REWRITE_TAC[MAP_MAP_o; o_DEF; MEM_MAP; EXISTS_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[FST; MEM_toAList; PAIR_EQ] THEN
  CASES_ON `lookup n (s:A spt)` THEN REWRITE_TAC[IS_SOME_DEF] THEN
  ASM_MESON_TAC[adjust_var_11; option_DISTINCT]);;

(* HOL4 line 409 *)
let lookup_adjust_var_adjust_set_SOME_UNIT = prove
 (`!n s:A spt. lookup (adjust_var n) (adjust_set s) = SOME one <=> IS_SOME (lookup n s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `s:A spt`] lookup_adjust_var_adjust_set_NONE) THEN
  CASES_ON `lookup (adjust_var n) (adjust_set (s:A spt))` THEN
  CASES_ON `lookup n (s:A spt)` THEN
  REWRITE_TAC[IS_SOME_DEF; option_DISTINCT; option_INJ] THEN MESON_TAC[one]);;

let GCP1AUX_ML_INV_REARR_TAC : tactic =
  FIRST_X_ASSUM(fun th -> if gcp1_is_app "word_ml_inv" (concl th)
                          then MP_TAC th else failwith "GCP1AUX_ML_INV_REARR_TAC") THEN
  MATCH_MP_TAC word_ml_inv_rearrange THEN REWRITE_TAC[MEM_APPEND; MEM] THEN
  ASM_MESON_TAC[];;

let GCP1AUX_MEM_join_env = prove
 (`!(l1:A spt) (l2:(B)spt) n x w.
     lookup n l1 = SOME x /\ lookup (adjust_var n) l2 = SOME w ==>
     MEM (x,w) (join_env l1 (toAList (inter l2 (adjust_set l1))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[join_env_def; MEM_MAP; MEM_FILTER; EXISTS_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  MAP_EVERY EXISTS_TAC [`adjust_var n`; `w:B`] THEN
  ASM_REWRITE_TAC[adjust_var_DIV_2; EVEN_adjust_var; adjust_var_NEQ_0; MEM_toAList;
                  lookup_inter; PAIR_EQ] THEN
  MP_TAC(SPECL [`n:num`; `l1:A spt`] lookup_adjust_var_adjust_set_NONE) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `lookup (adjust_var n) (adjust_set (l1:A spt))` THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  ASM_REWRITE_TAC[THE_DEF]);;

(* HOL4 line 419 *)
let word_ml_inv_lookup = prove
 (`!heap be a sp sp1 gens limit ts c refs ys (l1:data_v spt) l2 xs n x (w:A word_loc).
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (APPEND (APPEND ys (join_env l1 (toAList (inter l2 (adjust_set l1))))) xs) /\
     lookup n l1 = SOME x /\
     lookup (adjust_var n) l2 = SOME w ==>
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (APPEND (APPEND (APPEND ys [(x,w)])
          (join_env l1 (toAList (inter l2 (adjust_set l1))))) xs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`l1:data_v spt`; `l2:(A word_loc)spt`; `n:num`; `x:data_v`;
                `w:A word_loc`] GCP1AUX_MEM_join_env) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN GCP1AUX_ML_INV_REARR_TAC);;

(* HOL4 line 439 *)
let word_ml_inv_get_var_IMP_lemma = prove
 (`!heap be a sp sp1 gens limit ts c refs ll (t:(A,C,FFI)wl_state) envs n x w.
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (APPEND (join_env ll (toAList (inter (wl_state_locals t) (adjust_set ll))))
          envs) /\
     data_get_var n ll = SOME x /\
     wl_get_var (adjust_var n) t = SOME w ==>
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (APPEND (APPEND [(x,w)]
          (join_env ll (toAList (inter (wl_state_locals t) (adjust_set ll)))))
          envs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_get_var_def; wl_get_var_def] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ll:data_v spt`; `wl_state_locals (t:(A,C,FFI)wl_state)`; `n:num`;
                `x:data_v`; `w:A word_loc`] GCP1AUX_MEM_join_env) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN GCP1AUX_ML_INV_REARR_TAC);;

(* HOL4 line 453 *)
let word_ml_inv_get_var_IMP = prove
 (`!heap be a sp sp1 gens limit ts c refs (s:(C,FFI)data_state)
    (t:(A,C,FFI)wl_state) envs n x w.
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (APPEND (join_env (data_state_locals s)
          (toAList (inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
          envs) /\
     data_get_var n (data_state_locals s) = SOME x /\
     wl_get_var (adjust_var n) t = SOME w ==>
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (APPEND (APPEND [(x,w)]
          (join_env (data_state_locals s)
             (toAList (inter (wl_state_locals t) (adjust_set (data_state_locals s))))))
          envs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_get_var_def; wl_get_var_def] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`data_state_locals (s:(C,FFI)data_state)`;
                `wl_state_locals (t:(A,C,FFI)wl_state)`; `n:num`;
                `x:data_v`; `w:A word_loc`] GCP1AUX_MEM_join_env) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN GCP1AUX_ML_INV_REARR_TAC);;

let GCP1AUX_ml_inv_cons = prove
 (`!heap be a sp sp1 gens limit ts c refs ll (t:(A,C,FFI)wl_state) envs n x w.
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (APPEND (join_env ll (toAList (inter (wl_state_locals t) (adjust_set ll))))
          envs) /\
     data_get_var n ll = SOME x /\
     wl_get_var (adjust_var n) t = SOME w ==>
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (APPEND (join_env ll (toAList (inter (wl_state_locals t) (adjust_set ll))))
          (CONS (x,w) envs))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP word_ml_inv_get_var_IMP_lemma) THEN
  MATCH_MP_TAC word_ml_inv_rearrange THEN REWRITE_TAC[MEM_APPEND; MEM] THEN
  MESON_TAC[]);;

(* HOL4 line 467 (HOL4: Q.prove ... |> SPEC_ALL) *)
let word_ml_inv_get_vars_IMP_lemma = prove
 (`!heap be a sp sp1 gens limit ts c refs ll (t:(A,C,FFI)wl_state) n x w envs.
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (APPEND (join_env ll (toAList (inter (wl_state_locals t) (adjust_set ll))))
          envs) /\
     data_get_vars n ll = SOME x /\
     wl_get_vars (MAP adjust_var n) t = SOME w ==>
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (APPEND (APPEND (ZIP x w)
          (join_env ll (toAList (inter (wl_state_locals t) (adjust_set ll)))))
          envs)`,
  REPLICATE_TAC 12 GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[data_get_vars_def; wl_get_vars_def; MAP] THENL
   [REWRITE_TAC[option_INJ] THEN REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
    ASM_REWRITE_TAC[ZIP; APPEND];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  CASES_ON `data_get_var h (ll:data_v spt)` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `data_get_vars t' (ll:data_v spt)` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `wl_get_var (adjust_var h) (t:(A,C,FFI)wl_state)` THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `wl_get_vars (MAP adjust_var t') (t:(A,C,FFI)wl_state)` THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  REWRITE_TAC[ZIP] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a'':data_v list`; `a'''':(A word_loc)list`;
    `CONS (a':data_v,a''':A word_loc) envs`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC GCP1AUX_ml_inv_cons THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `h:num` THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN GCP1AUX_ML_INV_REARR_TAC]);;

(* HOL4 line 492 (HOL4: Q.prove ... |> SPEC_ALL) *)
let word_ml_inv_get_vars_IMP = prove
 (`!heap be a sp sp1 gens limit ts c refs (s:(C,FFI)data_state)
    (t:(A,C,FFI)wl_state) n x w envs.
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (APPEND (join_env (data_state_locals s)
          (toAList (inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
          envs) /\
     data_get_vars n (data_state_locals s) = SOME x /\
     wl_get_vars (MAP adjust_var n) t = SOME w ==>
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (APPEND (APPEND (ZIP x w)
          (join_env (data_state_locals s)
             (toAList (inter (wl_state_locals t) (adjust_set (data_state_locals s))))))
          envs)`,
  REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC word_ml_inv_get_vars_IMP_lemma);;

(* HOL4 line 504 *)
let IMP_adjust_var = prove
 (`!n. ~(n = 0) /\ EVEN n ==> adjust_var ((n - 2) DIV 2) = n`,
  GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[adjust_var_def] THEN
  SUBGOAL_THEN `2 * m - 2 = 2 * (m - 1)` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN ASM_ARITH_TAC);;

(* HOL4 line 512 *)
let unit_some_eq_IS_SOME = prove
 (`!x:1 option. (x = SOME one) <=> IS_SOME x`,
  REWRITE_TAC[FORALL_OPTION_THM; IS_SOME_DEF; option_DISTINCT; option_INJ] THEN
  MESON_TAC[one]);;

(* HOL4 line 518 *)
let IS_SOME_lookup_domain = prove
 (`!k m:A spt. IS_SOME (lookup k m) <=> k IN domain m`,
  REWRITE_TAC[domain_lookup] THEN REPEAT GEN_TAC THEN
  CASES_ON `lookup k (m:A spt)` THEN
  REWRITE_TAC[IS_SOME_DEF; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let GCP1AUX_adjust_var_IN_adjust_set = prove
 (`!n s:A spt. adjust_var n IN domain (adjust_set s) <=> n IN domain s`,
  REWRITE_TAC[GSYM IS_SOME_lookup_domain] THEN REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `s:A spt`] lookup_adjust_var_adjust_set_NONE) THEN
  CASES_ON `lookup (adjust_var n) (adjust_set (s:A spt))` THEN
  CASES_ON `lookup n (s:A spt)` THEN
  REWRITE_TAC[IS_SOME_DEF; option_DISTINCT]);;

(* HOL4 line 525 *)
let word_ml_inv_insert = prove
 (`!heap be a sp sp1 gens limit ts c refs x (w:A word_loc) d l xs dest.
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (APPEND (APPEND [(x,w)] (join_env d (toAList (inter l (adjust_set d))))) xs) ==>
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (APPEND (join_env (insert dest x d)
          (toAList (inter (insert (adjust_var dest) w l)
                          (adjust_set (insert dest x d))))) xs)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC word_ml_inv_rearrange THEN
  REWRITE_TAC[MEM_APPEND; MEM] THEN GEN_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> q \/ r) ==> (p \/ s ==> (q \/ r) \/ s)`) THEN
  REWRITE_TAC[join_env_def; MEM_MAP; MEM_FILTER; EXISTS_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[MEM_toAList; lookup_inter_alt] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `v:A word_loc` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `q = (p - 2) DIV 2` THEN
  SUBGOAL_THEN `p = adjust_var q` SUBST_ALL_TAC THENL
   [EXPAND_TAC "q" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC IMP_adjust_var THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[adjust_var_DIV_2]) THEN ASM_REWRITE_TAC[adjust_var_DIV_2] THEN
  ASM_CASES_TAC `q:num = dest` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[lookup_insert; GCP1AUX_adjust_var_IN_adjust_set;
                                domain_insert; IN_INSERT; option_INJ]) THEN
    DISJ1_TAC THEN ASM_REWRITE_TAC[lookup_insert; THE_DEF];
    RULE_ASSUM_TAC(REWRITE_RULE[lookup_insert; GCP1AUX_adjust_var_IN_adjust_set;
                                domain_insert; IN_INSERT; adjust_var_11]) THEN
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`adjust_var q`; `v:A word_loc`] THEN
    ASM_REWRITE_TAC[lookup_insert; adjust_var_DIV_2; adjust_var_NEQ_0; EVEN_adjust_var;
                    GCP1AUX_adjust_var_IN_adjust_set] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]]);;

(* HOL4 line 556 *)
let one_and_or_1 = prove
 (`!w:A word. word_and (word 1) (word_or w (word 1)) = word 1`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_OR] THEN
  MESON_TAC[]);;

(* HOL4 line 562 *)
let one_and_or_3 = prove
 (`!w:A word. word_and (word 3) (word_or w (word 3)) = word 3`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_OR] THEN
  MESON_TAC[]);;

(* HOL4 line 568 *)
let ODD_not_zero = prove
 (`!n. ODD n ==> ~(word n = word 0:A word)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD; BIT_WORD_0; NOT_FORALL_THM; NOT_IMP] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN
  ASM_REWRITE_TAC[EXP; DIV_1; DIMINDEX_GT_0]);;

(* HOL4 line 577 *)
let three_not_0 = prove
 (`~(word 3 = word 0:A word)`,
  MATCH_MP_TAC ODD_not_zero THEN CONV_TAC NUM_REDUCE_CONV);;

let _ = cake_add_simps [three_not_0];;

(* HOL4 line 583 (val DISJ_EQ_IMP; prefixed: hol4/basic.ml binds DISJ_EQ_IMP *)
(* with another statement)                                                 *)
let data_to_word_gcProof_DISJ_EQ_IMP = prove
 (`!b c. (~b \/ c) <=> (b ==> c)`,
  REPEAT GEN_TAC THEN CONV_TAC TAUT);;

(* HOL4 line 585 *)
let three_and_shift_2 = prove
 (`!w:A word. word_and (word 3) (word_shl w 2) = word 0`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_SHL; BIT_WORD; BIT_WORD_0] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `2 <= i` THEN
  ASM_REWRITE_TAC[] THEN GCP1AUX_DIV_2EXP_0_TAC THEN REWRITE_TAC[ODD]);;

(* HOL4 line 591 *)
let shift_to_zero = prove
 (`word_ushr (word 3:A word) 2 = word 0`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD; BIT_WORD_0] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN GCP1AUX_DIV_2EXP_0_TAC THEN
  REWRITE_TAC[ODD]);;

(* HOL4 line 597 *)
let shift_around_under_big_shift = prove
 (`!(w:A word) n k. n <= k ==> word_shl (word_ushr (word_shl w n) n) k = word_shl w k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SHL; BIT_WORD_USHR] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `k <= i` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n <= (i - k) + n /\ (i - k) + n < dimindex(:A) /\ ((i - k) + n) - n = i - k`
    (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

(* HOL4 line 603 *)
let select_shift_out = prove
 (`!n m (w:A word) v.
     ~(n = 0) /\ n <= m ==>
     word_bits (n - 1) 0 (word_or w (word_shl v m)) = word_bits (n - 1) 0 w`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_BITS; BIT_WORD_OR; BIT_WORD_SHL; ADD_CLAUSES] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i <= n - 1` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(m <= i)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

(* HOL4 line 609 *)
let shift_length_NOT_ZERO = prove
 (`!conf. ~(shift_length conf = 0)`,
  REWRITE_TAC[shift_length_def] THEN ARITH_TAC);;

let _ = cake_add_simps [shift_length_NOT_ZERO];;

(* HOL4 line 615 *)
let get_addr_and_1_not_0 = prove
 (`!conf k a. ~(word_and (word 1) (get_addr conf k a) = word 0:A word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; NOT_FORALL_THM; NOT_IMP] THEN
  EXISTS_TAC `0` THEN
  REWRITE_TAC[BIT_WORD_AND; BIT_WORD_1; BIT_WORD_0; DIMINDEX_GT_0; get_addr_def;
              BIT_WORD_OR] THEN
  CASES_ON `a:A word_loc` THEN
  REWRITE_TAC[get_lowerbits_def; BIT_WORD_OR; BIT_WORD_1; DIMINDEX_GT_0]);;

(* HOL4 line 622 *)
let one_lsr_shift_length = prove
 (`!conf. word_ushr (word 1:A word) (shift_length conf) = word 0`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_1; BIT_WORD_0] THEN
  MP_TAC(SPEC `conf:data_to_word_config` shift_length_NOT_ZERO) THEN ARITH_TAC);;

(* HOL4 line 629 *)
let ptr_to_addr_get_addr = prove
 (`!k conf curr a.
     k * 2 EXP shift_length conf < dimword (:A) ==>
     ptr_to_addr conf curr (get_addr conf k a) =
     word_add curr (word_mul (word k) bytes_in_word):A word`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ptr_to_addr_def; get_addr_def] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_USHR_OR; get_lowerbits_LSL_shift_length; WORD_OR_0] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD_SHL; VAL_WORD] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[dimword_def]) THEN
  SUBGOAL_THEN `k < 2 EXP dimindex(:A)` ASSUME_TAC THENL
   [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `k * 2 EXP shift_length conf` THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `k = k * 1`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL; ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_LT] THEN
  SIMP_TAC[arithmetic_MULT_DIV; LT_NZ; EXP_EQ_0; ARITH_EQ]);;

(* HOL4 line 646 *)
let is_fws_ptr_OR_3 = prove
 (`!w:A word. is_fwd_ptr (wl_Word (word_shl w 2)) /\
              ~is_fwd_ptr (wl_Word (word_or w (word 3)))`,
  GEN_TAC THEN REWRITE_TAC[is_fwd_ptr_def] THEN ONCE_REWRITE_TAC[WORD_AND_SYM] THEN
  REWRITE_TAC[three_and_shift_2; one_and_or_3; three_not_0]);;

let GCP1AUX_bit0_not_fwd = prove
 (`!h:A word. bit 0 h ==> ~is_fwd_ptr (wl_Word h)`,
  GEN_TAC THEN REWRITE_TAC[is_fwd_ptr_def; WORD_EQ_BITS_ALT; NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_TAC THEN EXISTS_TAC `0` THEN
  ASM_REWRITE_TAC[BIT_WORD_AND; BIT_WORD; BIT_WORD_0; DIMINDEX_GT_0] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let GCP1AUX_bit0_or_odd = prove
 (`!(w:A word) n. ODD n ==> bit 0 (word_or w (word n))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[BIT_WORD_OR; BIT_WORD; DIMINDEX_GT_0; EXP; DIV_1]);;

(* HOL4 line 653 *)
let is_fws_ptr_OR_15 = prove
 (`!w:A word. ~is_fwd_ptr (wl_Word (word_or w (word 15)))`,
  GEN_TAC THEN MATCH_MP_TAC GCP1AUX_bit0_not_fwd THEN
  MATCH_MP_TAC GCP1AUX_bit0_or_odd THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 661 (0b10111w) *)
let is_fws_ptr_OR_10111 = prove
 (`!w:A word. ~is_fwd_ptr (wl_Word (word_or w (word 0b10111)))`,
  GEN_TAC THEN MATCH_MP_TAC GCP1AUX_bit0_not_fwd THEN
  MATCH_MP_TAC GCP1AUX_bit0_or_odd THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 669 *)
let is_fws_ptr_OR_7 = prove
 (`!w:A word. ~is_fwd_ptr (wl_Word (word_or w (word 7)))`,
  GEN_TAC THEN MATCH_MP_TAC GCP1AUX_bit0_not_fwd THEN
  MATCH_MP_TAC GCP1AUX_bit0_or_odd THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 677 *)
let select_get_lowerbits = prove
 (`!conf a:A word_loc.
     word_bits (shift_length conf - 1) 0 (get_lowerbits conf a) =
     get_lowerbits conf a /\
     word_bits (small_shift_length conf - 1) 0 (get_lowerbits conf a) =
     get_lowerbits conf a`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `small_shift_length conf - 1 <= shift_length conf - 1` MP_TAC THENL
   [REWRITE_TAC[shift_length_def; small_shift_length_def] THEN ARITH_TAC; ALL_TAC] THEN
  CASES_ON `a:A word_loc` THEN REWRITE_TAC[get_lowerbits_def] THEN
  SPEC_TAC(`shift_length conf - 1`,`s:num`) THEN
  SPEC_TAC(`small_shift_length conf - 1`,`r:num`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_BITS; BIT_WORD_OR; BIT_WORD_1; ADD_CLAUSES] THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  GCP1AUX_BIT_SPLIT_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 689 *)
let LE_DIV_LT_IMP = prove
 (`!n l m k. n <= l DIV 2 EXP m /\ k < n ==> k * 2 EXP m < l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2 EXP m`; `l:num`; `k + 1`] LE_RDIV_EQ) THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  SUBGOAL_THEN `k + 1 <= l DIV 2 EXP m` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`2`; `m:num`] EXP_EQ_0) THEN REWRITE_TAC[ARITH_EQ] THEN
  REWRITE_TAC[GSYM LT_NZ; LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC);;

(* HOL4 line 698 *)
let word_bits_eq_slice_shift = prove
 (`!k n w:A word. word_bits k n w = word_ushr (word_slice k n w) n`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_BITS; BIT_WORD_USHR; BIT_WORD_SLICE; LE_ADDR]);;

(* HOL4 line 706 *)
let word_slice_or = prove
 (`!k n (w:A word) v.
     word_slice k n (word_or w v) = word_or (word_slice k n w) (word_slice k n v)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SLICE; BIT_WORD_OR] THEN MESON_TAC[]);;

(* HOL4 line 715 *)
let word_slice_lsl_eq_0 = prove
 (`!k n w:A word. word_slice k n (word_shl w (k + 1)) = word 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SLICE; BIT_WORD_SHL; BIT_WORD_0] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i <= k` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(k + 1 <= i)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

(* HOL4 line 721 *)
let word_slice_2_3_eq_0 = prove
 (`!n. word_slice n 2 (word 3:A word) = word 0`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SLICE; BIT_WORD; BIT_WORD_0] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `2 <= i` THEN
  ASM_REWRITE_TAC[] THEN GCP1AUX_DIV_2EXP_0_TAC THEN REWRITE_TAC[ODD]);;

(* HOL4 line 727 *)
let can_select_def = cake_def
  `can_select k n (w:A word) <=> (word_bits (k - 1) n (word_shl w n) = w)`;;

(* HOL4 line 731 *)
let read_length_lemma = prove
 (`!n k (h:A word).
     can_select (n + 2) 2 (word k:A word) ==>
     word_bits (n + 1) 2
       (word_or (word_or (word_shl h (2 + n)) (word_shl (word k) 2)) (word 3)) =
     word k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[can_select_def] THEN
  SUBGOAL_THEN `(n + 2) - 1 = n + 1` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_BITS; BIT_WORD_OR] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i + 2 <= n + 1` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~bit (i + 2) (word_shl (h:A word) (2 + n)) /\ ~bit (i + 2) (word 3:A word)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[BIT_WORD_SHL; BIT_WORD] THEN CONJ_TAC THENL
     [REWRITE_TAC[DE_MORGAN_THM] THEN DISJ1_TAC THEN ASM_ARITH_TAC;
      GCP1AUX_DIV_2EXP_0_TAC THEN REWRITE_TAC[ODD]];
    GEN_REWRITE_TAC RAND_CONV [BIT_GUARD] THEN CONV_TAC TAUT]);;
let GCP1AUX_word_SUC_NEQ_0 = prove
 (`!n. SUC n < dimword(:A) ==> ~(word (SUC n) = word 0:A word)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM `val:A word->num`) THEN
  REWRITE_TAC[VAL_WORD; VAL_WORD_0] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[dimword_def]) THEN
  ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

let GCP1AUX_word_SUC_SUB_1 = prove
 (`!n. word_sub (word (SUC n)) (word 1) = word n:A word`,
  REWRITE_TAC[ADD1; WORD_ADD; WORD_ADD_SUB]);;

(* HOL4 line 739 *)
let memcpy_thm = prove
 (`!(xs:B list) (a:A word) c b m m1 dm b1 ys frame.
     memcpy (word (LENGTH xs):A word) a b m dm = (b1,m1,c) /\
     (LENGTH ys = LENGTH xs) /\ LENGTH xs < dimword(:A) /\
     (frame STAR misc_word_list a xs STAR misc_word_list b ys) (fun2set (m,dm)) ==>
     (frame STAR misc_word_list a xs STAR misc_word_list b xs) (fun2set (m1,dm)) /\
     b1 = word_add b (word_mul (word (LENGTH xs)) bytes_in_word) /\ c`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[memcpy_def] THEN
    REWRITE_TAC[LENGTH; LENGTH_EQ_NIL; PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[WORD_MUL_0; WORD_ADD_0];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ys:B list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = SUC n)`; SUC_INJ] THEN
  REWRITE_TAC[misc_word_list_def] THEN
  STRIP_TAC THEN
  GCP1AUX_UNDISCH_EQ "memcpy" THEN ONCE_REWRITE_TAC[memcpy_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP GCP1AUX_word_SUC_NEQ_0 th;
                                    GCP1AUX_word_SUC_SUB_1]) THEN
  PAIRARG_TAC THEN PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  GCP1AUX_SEP_R_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `(m:A word->B) a = h` then SUBST_ALL_TAC th
                          else failwith "") THEN
  FIRST_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th)
                        then ASSUME_TAC (GCP1AUX_SEP_WRITE `b:A word` `h:B` th)
                        else failwith "") THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`word_add a bytes_in_word:A word`; `c1:bool`;
    `word_add b bytes_in_word:A word`; `((b:A word) =+ (h:B)) m`; `m1:A word->B`;
    `dm:A word->bool`; `b1:A word`; `t':B list`]) THEN
  GCP1AUX_SEP_FRAME_TAC THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GCP1AUX_SEP_AC_TAC; REWRITE_TAC[ADD1] THEN CONV_TAC WORD_RULE]);;

(* HOL4 line 770 *)
let LESS_EQ_IMP_APPEND = prove
 (`!n (xs:A list). n <= LENGTH xs ==> ?ys zs. xs = APPEND ys zs /\ LENGTH ys = n`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`TAKE n (xs:A list)`; `DROP n (xs:A list)`] THEN
  ASM_SIMP_TAC[TAKE_DROP; LENGTH_TAKE]);;

(* HOL4 line 778 *)
let NOT_is_fwd_ptr = prove
 (`!addrs ll tag tt1 conf (h:A word) ts c5.
     word_payload addrs ll tag tt1 conf = (h,ts,c5) ==> ~is_fwd_ptr (wl_Word h)`,
  REPEAT GEN_TAC THEN
  CASES_ON `tag:data_to_word_memoryProof_tag` THEN
  REWRITE_TAC[word_payload_def; PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN MATCH_MP_TAC GCP1AUX_bit0_not_fwd THEN
  REWRITE_TAC[make_header_def; make_byte_header_def; LET_DEF; LET_END_DEF] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD; DIMINDEX_GT_0; EXP; DIV_1] THEN
  CONV_TAC NUM_REDUCE_CONV);;
(* ------------------------------------------------------------------------- *)
(* Helpers for the heap: reading a data element of a word heap, copying it  *)
(* and leaving a forward pointer (the common core of word_gc_move,           *)
(* word_gen_gc_move and word_gen_gc_partial_move).                           *)
(* ------------------------------------------------------------------------- *)

let GCP1AUX_word_list_exists_intro = prove
 (`!(a:A word) (xs:B list) n p s.
     LENGTH xs = n /\ (misc_word_list a xs STAR p) s ==>
     (word_list_exists a n STAR p) s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[word_list_exists_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  EXISTS_TAC `xs:B list` THEN
  ONCE_REWRITE_TAC[GSYM STAR_ASSOC] THEN ONCE_REWRITE_TAC[STAR_COMM] THEN
  REWRITE_TAC[GSYM STAR_ASSOC; cond_STAR] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[STAR_COMM] THEN ASM_REWRITE_TAC[]);;

(* the goal  p s  with a leaf  word_list_exists a n:  proved from         *)
(* LENGTH xs = n  and  (misc_word_list a xs STAR rest) s                    *)
let GCP1AUX_WLE_INTRO_TAC xs : tactic =
  GCP1AUX_SEP_FOCUS_GOAL_TAC (gcp1_is_app "word_list_exists") THEN
  MATCH_MP_TAC GCP1AUX_word_list_exists_intro THEN EXISTS_TAC xs;;

(* reading the header of a data element of a word heap *)
let GCP1AUX_heap_el_read = prove
 (`!conf (curr:A word) ha ys l tag qs hb R m dm.
     (word_heap curr (APPEND ha (CONS (DataElement ys l (tag,qs)) hb)) conf STAR R)
       (fun2set (m,dm)) ==>
     ?h ts. word_payload ys l tag qs conf = (h,ts,T) /\ LENGTH ts = l /\
            decode_length conf h = word l /\ l < 2 EXP (dimindex (:A) - 4) /\
            m (word_add curr (word_mul bytes_in_word (word (heap_length ha)))) =
              wl_Word h /\
            word_add curr (word_mul bytes_in_word (word (heap_length ha))) IN dm`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_heap_APPEND; word_heap_def; word_el_def] THEN
  PAIRARG_TAC THEN PAIRARG_TAC THEN
  REWRITE_TAC[misc_word_list_def] THEN STRIP_TAC THEN
  GCP1AUX_SEP_COND_TAC THEN GCP1AUX_SEP_R_TAC THEN
  MAP_EVERY EXISTS_TAC [`h:A word`; `ts:(A word_loc)list`] THEN
  SUBGOAL_THEN `LENGTH (ts:(A word_loc)list) = l` ASSUME_TAC THENL
   [MATCH_MP_TAC word_payload_IMP THEN
    MAP_EVERY EXISTS_TAC [`ys:((A word_loc)heap_address)list`; `tag:data_to_word_memoryProof_tag`;
                          `qs:(A word_loc)list`; `conf:data_to_word_config`; `h:A word`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* copying a data element (header and payload) to dst with memcpy and      *)
(* writing a forward pointer to word a' into its header word               *)
let GCP1AUX_heap_el_copy = prove
 (`!conf (curr:A word) ha ys l tag qs hb dst ys0 m dm a' d' h ts dst1 m1 c1 R.
     (word_heap curr (APPEND ha (CONS (DataElement ys l (tag,qs)) hb)) conf STAR
      misc_word_list dst ys0 STAR R) (fun2set (m,dm)) /\
     word_payload ys l tag qs conf = (h,ts,T) /\ LENGTH ts = l /\
     LENGTH (ys0:(A word_loc)list) = l + 1 /\ l + 1 < dimword(:A) /\
     memcpy (word (l + 1):A word)
       (word_add curr (word_mul bytes_in_word (word (heap_length ha)))) dst m dm =
       (dst1,m1,c1) ==>
     c1 /\ dst1 = word_add dst (word_mul (word (l + 1)) bytes_in_word) /\
     (word_heap curr (APPEND ha (CONS (ForwardPointer a' d' l) hb)) conf STAR
      word_heap dst [DataElement ys l (tag,qs)] conf STAR R)
       (fun2set ((word_add curr (word_mul bytes_in_word (word (heap_length ha))) =+
                  wl_Word (word_shl (word a') 2)) m1,dm))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp1_is_fun2set_asm o concl)) THEN
  ASM_REWRITE_TAC[word_heap_APPEND; word_heap_def; word_el_def; el_length_def] THEN
  CASE_REWRITE_TAC[] THEN DISCH_TAC THEN GCP1AUX_SEP_COND_TAC THEN
  MP_TAC(ISPECL [`CONS (wl_Word h) (ts:(A word_loc)list)`;
    `word_add curr (word_mul bytes_in_word (word (heap_length
       (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))):A word`;
    `c1:bool`; `dst:A word`; `m:A word->A word_loc`; `m1:A word->A word_loc`;
    `dm:A word->bool`; `dst1:A word`; `ys0:(A word_loc)list`] memcpy_thm) THEN
  GCP1AUX_SEP_FRAME_TAC THEN
  ASM_REWRITE_TAC[LENGTH; ADD1] THEN STRIP_TAC THEN ASM_REWRITE_TAC[SEP_CLAUSES] THEN
  FIRST_X_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) &&
                             free_in `m1:A word->A word_loc` (concl th)
                          then ASSUME_TAC (REWRITE_RULE[misc_word_list_def] th)
                          else failwith "") THEN
  FIRST_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) &&
                           free_in `m1:A word->A word_loc` (concl th)
                        then ASSUME_TAC (GCP1AUX_SEP_WRITE
                          `word_add curr (word_mul bytes_in_word (word (heap_length
                             (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                                  heap_element)list)))):A word`
                          `wl_Word (word_shl (word a') 2):A word_loc` th)
                        else failwith "") THEN
  REWRITE_TAC[misc_word_list_def] THEN GCP1AUX_WLE_INTRO_TAC `ts:(A word_loc)list` THEN
  ASM_REWRITE_TAC[] THEN GCP1AUX_SEP_AC_TAC);;

let GCP1AUX_len_bound = prove
 (`!l. l < 2 EXP (dimindex (:A) - 4) ==> l + 1 < dimword(:A)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dimword_def] THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `2 EXP (dimindex (:A) - 4)` THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LT_EXP] THEN MP_TAC(ISPEC `(:A)` DIMINDEX_GE_1) THEN ARITH_TAC);;
(* ------------------------------------------------------------------------- *)
(* Helpers for the move functions.                                          *)
(* ------------------------------------------------------------------------- *)

let GCP1AUX_get_addr_and_1 = prove
 (`!conf k a. ~(word_and (get_addr conf k a) (word 1) = word 0:A word)`,
  ONCE_REWRITE_TAC[WORD_AND_SYM] THEN REWRITE_TAC[get_addr_and_1_not_0]);;

let GCP1AUX_update_addr_get_addr = prove
 (`!conf (w:A word) k d.
     update_addr conf w (get_addr conf k d) =
     word_or (word_shl w (shift_length conf)) (get_lowerbits conf d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[update_addr_def; get_addr_def] THEN
  AP_TERM_TAC THEN ONCE_REWRITE_TAC[WORD_OR_SYM] THEN
  W(fun (asl,w) -> MP_TAC(ISPECL [`small_shift_length conf`; `shift_length conf`;
     `get_lowerbits conf (d:A word_loc):A word`; `word k:A word`] select_shift_out)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[shift_length_def; small_shift_length_def] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[select_get_lowerbits]]);;

let GCP1AUX_two_le_shift_length = prove
 (`!conf. 2 <= shift_length conf`,
  REWRITE_TAC[shift_length_def] THEN ARITH_TAC);;

let GCP1AUX_update_addr_word = prove
 (`!conf a k d. update_addr conf (word a) (get_addr conf k d) = get_addr conf a d:A word`,
  REWRITE_TAC[GCP1AUX_update_addr_get_addr; get_addr_def]);;

let GCP1AUX_update_addr_fwd = prove
 (`!conf p k d.
     update_addr conf (word_ushr (word_shl (word p) 2) 2) (get_addr conf k d) =
     get_addr conf p d:A word`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GCP1AUX_update_addr_get_addr; get_addr_def] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC shift_around_under_big_shift THEN
  REWRITE_TAC[GCP1AUX_two_le_shift_length]);;

let GCP1AUX_and_not_1 = prove
 (`!v:A word. word_and (word_and v (word_not (word 1))) (word 1) = word 0 /\
              word_and (word 1) (word_and v (word_not (word 1))) = word 0`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_NOT; BIT_WORD_1;
                           BIT_WORD_0] THEN
  MESON_TAC[]);;

let GCP1AUX_heap_ptr_bound = prove
 (`!ptr (heap:((A,B)heap_element)list) x conf.
     heap_lookup ptr heap = SOME x /\
     heap_length heap <= dimword (:N) DIV 2 EXP shift_length conf ==>
     ptr * 2 EXP shift_length conf < dimword (:N)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_DIV_LT_IMP THEN
  EXISTS_TAC `heap_length (heap:((A,B)heap_element)list)` THEN
  ASM_MESON_TAC[heap_lookup_LESS]);;

(* the goal  k * 2 EXP shift_length conf < dimword(:A)  from assumptions   *)
(* heap_lookup k heap = SOME x  and  heap_length heap <= dimword(:A) DIV   *)
(* 2 EXP shift_length conf                                                  *)
let GCP1AUX_PTR_BOUND_TAC : tactic =
  MATCH_MP_TAC LE_DIV_LT_IMP THEN
  FIRST_ASSUM(fun th -> let c = concl th in
    if is_binary "<=" c && gcp1_is_app "heap_length" (lhand c) then
      EXISTS_TAC (lhand c) THEN CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC] else NO_TAC) THEN
  FIRST_ASSUM(fun th -> try ACCEPT_TAC(MATCH_MP heap_lookup_LESS th) with Failure _ -> NO_TAC);;

let GCP1AUX_ptr_to_addr_get_addr = prove
 (`!k conf curr a.
     k * 2 EXP shift_length conf < dimword (:A) ==>
     ptr_to_addr conf curr (get_addr conf k a) =
     word_add curr (word_mul bytes_in_word (word k)):A word`,
  ONCE_REWRITE_TAC[WORD_MUL_SYM] THEN REWRITE_TAC[ptr_to_addr_get_addr]);;

(* HOL4 line 786 *)
let word_gc_move_thm = prove
 (`!x a n heap limit x1 h1 a1 n1 heap1 conf (curr:A word) pa xs frame m dm
    w i1 pa1 m1 c1.
     (copying_gc_gc_move (x,[],a,n,heap,T,limit) = (x1,h1,a1,n1,heap1,T)) /\
     heap_length heap <= dimword (:A) DIV 2 EXP shift_length conf /\
     (word_heap curr heap conf STAR misc_word_list pa xs STAR frame)
       (fun2set (m,dm)) /\
     (word_gc_move conf (word_addr conf x,word a,pa,curr,m,dm) =
       (w:A word_loc,i1,pa1,m1,c1)) /\
     LENGTH xs = n ==>
     ?xs1.
       (word_heap curr heap1 conf STAR
        word_heap pa h1 conf STAR
        misc_word_list pa1 xs1 STAR frame) (fun2set (m1,dm)) /\
       (w = word_addr conf x1) /\
       heap_length heap1 = heap_length heap /\
       c1 /\ (i1 = word a1) /\ n1 = LENGTH xs1 /\
       pa1 = word_add pa (word_mul bytes_in_word (word (heap_length h1)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `x:(A word_loc)heap_address` (cases "heap_address")) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (X_CHOOSE_THEN `ptr:num` (X_CHOOSE_THEN `dd:A word_loc` SUBST1_TAC))
    (X_CHOOSE_THEN `dv:A word_loc` SUBST1_TAC)) THENL
   [ALL_TAC;
    (* a data value *)
    REWRITE_TAC[copying_gc_gc_move_def; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MP_TAC(ISPEC `dv:A word_loc` (cases "word_loc")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:A word` SUBST_ALL_TAC)
      (X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `l2:num` SUBST_ALL_TAC))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[word_addr_def; word_gc_move_def; GCP1AUX_and_not_1;
                                PAIR_EQ]) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN RVEQ_TAC THEN
    EXISTS_TAC `xs:(A word_loc)list` THEN
    ASM_REWRITE_TAC[word_heap_def; SEP_CLAUSES; word_addr_def; heap_length_NIL;
                    WORD_MUL_0; WORD_ADD_0]] THEN
  (* a pointer *)
  REWRITE_TAC[copying_gc_gc_move_def] THEN
  MP_TAC(ISPEC `heap_lookup ptr (heap:((A word_loc,data_to_word_memoryProof_tag#
                  (A word_loc)list)heap_element)list)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[PAIR_EQ])
    (X_CHOOSE_THEN `el:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                       heap_element`
       (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th] THEN CASE_REWRITE_TAC[]))) THEN
  MP_TAC(ISPEC `el:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                   heap_element` (cases "heap_element")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `u:num` SUBST_ALL_TAC)
    (DISJ_CASES_THEN2
      (X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `pd:A word_loc`
         (X_CHOOSE_THEN `l:num` SUBST_ALL_TAC)))
      (X_CHOOSE_THEN `ys:((A word_loc)heap_address)list` (X_CHOOSE_THEN `l:num`
         (X_CHOOSE_THEN `tg:data_to_word_memoryProof_tag#(A word_loc)list`
            SUBST_ALL_TAC))))) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THENL
   [(* a forward pointer *)
    STRIP_TAC THEN RVEQ_TAC THEN
    SUBGOAL_THEN `ptr * 2 EXP shift_length conf < dimword(:A)` ASSUME_TAC THENL
     [GCP1AUX_PTR_BOUND_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP heap_lookup_SPLIT) THEN
    DISCH_THEN(X_CHOOSE_THEN `ha:((A word_loc,data_to_word_memoryProof_tag#
                                 (A word_loc)list)heap_element)list`
      (X_CHOOSE_THEN `hb:((A word_loc,data_to_word_memoryProof_tag#
                             (A word_loc)list)heap_element)list`
        (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC))) THEN
    FIRST_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) then
       ASSUME_TAC (REWRITE_RULE[word_heap_APPEND; word_heap_def; word_el_def] th)
       else NO_TAC) THEN
    GCP1AUX_SEP_R_TAC THEN
    GCP1AUX_UNDISCH_EQ "word_gc_move" THEN
    ASM_SIMP_TAC[word_addr_def; word_gc_move_def; GCP1AUX_get_addr_and_1;
                 GCP1AUX_ptr_to_addr_get_addr; LET_DEF; LET_END_DEF; is_fws_ptr_OR_3;
                 theWord_def; GCP1AUX_update_addr_fwd; PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `xs:(A word_loc)list` THEN
    ASM_REWRITE_TAC[word_heap_def; SEP_CLAUSES; heap_length_NIL; WORD_MUL_0; WORD_ADD_0];
    ALL_TAC] THEN
  (* a data element *)
  MP_TAC(ISPEC `tg:data_to_word_memoryProof_tag#(A word_loc)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tag:data_to_word_memoryProof_tag`
    (X_CHOOSE_THEN `qs:(A word_loc)list` SUBST_ALL_TAC)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ptr * 2 EXP shift_length conf < dimword(:A)` ASSUME_TAC THENL
   [GCP1AUX_PTR_BOUND_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP heap_lookup_SPLIT) THEN
  DISCH_THEN(X_CHOOSE_THEN `ha:((A word_loc,data_to_word_memoryProof_tag#
                               (A word_loc)list)heap_element)list`
    (X_CHOOSE_THEN `hb:((A word_loc,data_to_word_memoryProof_tag#
                           (A word_loc)list)heap_element)list`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    free_in `x1:(A word_loc)heap_address` (rhs (concl th)))) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[gc_forward_ptr_thm; APPEND] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) then
     let wh = hd (gcp1_star_leaves (rator (concl th))) in
     MP_TAC(MATCH_MP GCP1AUX_heap_el_read (GCP1AUX_STAR_FRONT [wh] th)) else NO_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:A word` (X_CHOOSE_THEN `ts:(A word_loc)list`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NOT_is_fwd_ptr) THEN
  GCP1AUX_UNDISCH_EQ "word_gc_move" THEN
  ASM_SIMP_TAC[word_addr_def; word_gc_move_def; GCP1AUX_get_addr_and_1;
               GCP1AUX_ptr_to_addr_get_addr; LET_DEF; LET_END_DEF; theWord_def; isWord_def;
               GCP1AUX_update_addr_word; GSYM WORD_ADD] THEN
  PAIRARG_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  GCP1AUX_SUBST_VARS_TAC ["w";"i1";"pa1";"m1";"c1"] THEN
  MP_TAC(ISPECL [`l + 1`; `xs:(A word_loc)list`] LESS_EQ_IMP_APPEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ys0:(A word_loc)list` (X_CHOOSE_THEN `zs:(A word_loc)list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_to_word_memoryProof_word_list_APPEND]) THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `curr:A word`;
    `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `ys:((A word_loc)heap_address)list`; `l:num`; `tag:data_to_word_memoryProof_tag`;
    `qs:(A word_loc)list`;
    `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `pa:A word`; `ys0:(A word_loc)list`; `m:A word->A word_loc`; `dm:A word->bool`;
    `a:num`; `dd:A word_loc`; `h:A word`; `ts:(A word_loc)list`; `pa1':A word`;
    `m1':A word->A word_loc`; `c1':bool`] GCP1AUX_heap_el_copy) THEN
  GCP1AUX_SEP_FRAME_TAC THEN
  ASM_SIMP_TAC[GCP1AUX_len_bound] THEN STRIP_TAC THEN
  EXISTS_TAC `zs:(A word_loc)list` THEN
  ASM_REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def;
                  heap_length_NIL; ADD_CLAUSES; ADD_ASSOC; LENGTH_APPEND] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH (ys0:(A word_loc)list) = l + 1`]) THEN
  REPEAT CONJ_TAC THENL
   [GCP1AUX_SEP_AC_TAC; ARITH_TAC; REWRITE_TAC[WORD_MUL_SYM]]);;

(* HOL4 line 879 *)
let word_gc_move_roots_thm = prove
 (`!x a n heap limit pa x1 h1 a1 n1 heap1 pa1 m m1 xs i1 c1 w frame
    conf (curr:A word) dm.
     (copying_gc_gc_move_list (x,[],a,n,heap,T,limit) = (x1,h1,a1,n1,heap1,T)) /\
     heap_length heap <= dimword (:A) DIV 2 EXP shift_length conf /\
     (word_heap curr heap conf STAR misc_word_list pa xs STAR frame)
       (fun2set (m,dm)) /\
     (word_gc_move_roots conf (MAP (word_addr conf) x,word a,pa,curr,m,dm) =
       (w:(A word_loc)list,i1,pa1,m1,c1)) /\
     LENGTH xs = n ==>
     ?xs1.
       (word_heap curr heap1 conf STAR
        word_heap pa h1 conf STAR
        misc_word_list pa1 xs1 STAR frame) (fun2set (m1,dm)) /\
       (w = MAP (word_addr conf) x1) /\
       heap_length heap1 = heap_length heap /\
       c1 /\ (i1 = word a1) /\ n1 = LENGTH xs1 /\
       pa1 = word_add pa (word_mul (word (heap_length h1)) bytes_in_word)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[copying_gc_gc_move_list_def; word_gc_move_roots_def; MAP; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `xs:(A word_loc)list` THEN
    ASM_REWRITE_TAC[word_heap_def; SEP_CLAUSES; heap_length_NIL; WORD_MUL_0; WORD_ADD_0;
                    MAP];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[copying_gc_gc_move_list_def; MAP; word_gc_move_roots_def] THEN
  MP_TAC(ISPEC `copying_gc_gc_move (h:(A word_loc)heap_address,
     []:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list,
     a,n,heap,T,limit)` GC1AUX_PAIR6) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`y2:(A word_loc)heap_address`;
    `h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `a2:num`; `n2:num`;
    `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `c2:bool`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[copying_gc_gc_move_list_ALT] THEN
  MP_TAC(ISPEC `copying_gc_gc_move_list (t:((A word_loc)heap_address)list,
     []:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list,
     a2,n2,heap2,c2,limit)` GC1AUX_PAIR6) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`y3:((A word_loc)heap_address)list`;
    `h3:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `a3:num`; `n3:num`;
    `heap3:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `c3:bool`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `c3:bool` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c2:bool` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP copying_gc_gc_move_list_ok) THEN SIMP_TAC[]; ALL_TAC] THEN
  GCP1AUX_UNDISCH_EQ "pair_CASE" THEN
  GCP1AUX_TUPLE_TAC `word_gc_move conf (word_addr conf (h:(A word_loc)heap_address),
                                        word a,pa,curr,m,dm)`
    ["w2";"i2";"pa2";"m2";"c2"] THEN
  GCP1AUX_TUPLE_TAC `word_gc_move_roots conf (MAP (word_addr conf)
                       (t:((A word_loc)heap_address)list),i2,pa2,curr,m2,dm)`
    ["ws3";"i3";"pa3";"m3";"c3"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  GCP1AUX_SUBST_VARS_TAC ["w";"i1";"pa1";"m1";"c1"] THEN
  MP_TAC(ISPECL [`h:(A word_loc)heap_address`; `a:num`; `LENGTH (xs:(A word_loc)list)`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `y2:(A word_loc)heap_address`;
    `h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `a2:num`; `n2:num`;
    `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `conf:data_to_word_config`; `curr:A word`; `pa:A word`; `xs:(A word_loc)list`;
    `frame:(A word#A word_loc->bool)->bool`; `m:A word->A word_loc`; `dm:A word->bool`;
    `w2:A word_loc`; `i2:A word`; `pa2:A word`; `m2:A word->A word_loc`; `c2':bool`]
    word_gc_move_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  GCP1AUX_SUBST_LVARS_TAC ["w2";"i2";"n2";"pa2"] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a2:num`; `LENGTH (xs1:(A word_loc)list)`;
    `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `word_add pa (word_mul bytes_in_word (word (heap_length
       (h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))):A word`;
    `y3:((A word_loc)heap_address)list`;
    `h3:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `a1:num`; `n1:num`;
    `heap1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `pa3:A word`; `m2:A word->A word_loc`; `m3:A word->A word_loc`; `xs1:(A word_loc)list`;
    `i3:A word`; `c3':bool`; `ws3:(A word_loc)list`;
    `word_heap pa (h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                       heap_element)list) conf STAR (frame:(A word#A word_loc->bool)->bool)`;
    `conf:data_to_word_config`; `curr:A word`; `dm:A word->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [GCP1AUX_SEP_AC_TAC; ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `xs1':(A word_loc)list` THEN
  REWRITE_TAC[word_heap_APPEND; MAP; heap_length_APPEND] THEN
  REPEAT CONJ_TAC THEN TRY GCP1AUX_SEP_AC_TAC THEN ASM_REWRITE_TAC[WORD_ADD] THEN
  CONV_TAC WORD_RULE);;

(* HOL4 line 932 *)
let word_gc_move_list_thm = prove
 (`!x a n heap limit pa x1 h1 a1 n1 heap1 pa1 m m1 xs i1 c1 frame k k1
    conf (curr:A word) dm.
     (copying_gc_gc_move_list (x,[],a,n,heap,T,limit) = (x1,h1,a1,n1,heap1,T)) /\
     heap_length heap <= dimword (:A) DIV 2 EXP shift_length conf /\
     (word_gc_move_list conf (k,word (LENGTH x),word a,pa,curr,m,dm) =
       (k1,i1,pa1,m1,c1)) /\
     (word_heap curr heap conf STAR misc_word_list pa xs STAR
      misc_word_list k (MAP (word_addr conf) x) STAR frame) (fun2set (m,dm)) /\
     LENGTH xs = n /\ LENGTH x < dimword (:A) ==>
     ?xs1.
       (word_heap curr heap1 conf STAR
        word_heap (pa:A word) h1 conf STAR
        misc_word_list pa1 xs1 STAR
        misc_word_list k (MAP (word_addr conf) x1) STAR frame) (fun2set (m1,dm)) /\
       heap_length heap1 = heap_length heap /\
       c1 /\ (i1 = word a1) /\ n1 = LENGTH xs1 /\
       k1 = word_add k (word_mul (word (LENGTH x)) bytes_in_word) /\
       pa1 = word_add pa (word_mul (word (heap_length h1)) bytes_in_word)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[copying_gc_gc_move_list_def; LENGTH; MAP; PAIR_EQ] THEN
    ONCE_REWRITE_TAC[word_gc_move_list_def] THEN REWRITE_TAC[PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `xs:(A word_loc)list` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[misc_word_list_def; MAP; SEP_CLAUSES]) THEN
    ASM_REWRITE_TAC[word_heap_def; misc_word_list_def; SEP_CLAUSES; heap_length_NIL;
                    WORD_MUL_0; WORD_ADD_0; MAP];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[copying_gc_gc_move_list_def; MAP] THEN
  MP_TAC(ISPEC `copying_gc_gc_move (h:(A word_loc)heap_address,
     []:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list,
     a,n,heap,T,limit)` GC1AUX_PAIR6) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`y2:(A word_loc)heap_address`;
    `h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `a2:num`; `n2:num`;
    `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `c2:bool`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[copying_gc_gc_move_list_ALT] THEN
  MP_TAC(ISPEC `copying_gc_gc_move_list (t:((A word_loc)heap_address)list,
     []:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list,
     a2,n2,heap2,c2,limit)` GC1AUX_PAIR6) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`y3:((A word_loc)heap_address)list`;
    `h3:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `a3:num`; `n3:num`;
    `heap3:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `c3:bool`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `c3:bool` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c2:bool` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP copying_gc_gc_move_list_ok) THEN SIMP_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; misc_word_list_def]) THEN
  GCP1AUX_SEP_R_TAC THEN
  GCP1AUX_UNDISCH_EQ "word_gc_move_list" THEN
  ONCE_REWRITE_TAC[word_gc_move_list_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP GCP1AUX_word_SUC_NEQ_0 th;
                                    GCP1AUX_word_SUC_SUB_1]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  FIRST_ASSUM(fun th -> if concl th = `(m:A word->A word_loc) k = word_addr conf (h:(A word_loc)heap_address)`
                        then REWRITE_TAC[th] else NO_TAC) THEN
  GCP1AUX_TUPLE_TAC `word_gc_move conf (word_addr conf (h:(A word_loc)heap_address),
                                        word a,pa,curr,m,dm)`
    ["w2";"i2";"pa2";"m2";"c2"] THEN
  GCP1AUX_TUPLE_TAC `word_gc_move_list conf (word_add (k:A word) bytes_in_word,word (LENGTH (t:((A word_loc)heap_address)list)),
                       i2,pa2,curr,(k =+ w2) m2,dm)`
    ["k3";"i3";"pa3";"m3";"c3"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  GCP1AUX_SUBST_VARS_TAC ["k1";"i1";"pa1";"m1";"c1"] THEN
  MP_TAC(ISPECL [`h:(A word_loc)heap_address`; `a:num`; `LENGTH (xs:(A word_loc)list)`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `y2:(A word_loc)heap_address`;
    `h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `a2:num`; `n2:num`;
    `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `conf:data_to_word_config`; `curr:A word`; `pa:A word`; `xs:(A word_loc)list`;
    `(set_sep_one ((k:A word),word_addr conf (h:(A word_loc)heap_address)) STAR
      misc_word_list (word_add k bytes_in_word) (MAP (word_addr conf) (t:((A word_loc)heap_address)list))) STAR
      (frame:(A word#A word_loc->bool)->bool)`;
    `m:A word->A word_loc`; `dm:A word->bool`;
    `w2:A word_loc`; `i2:A word`; `pa2:A word`; `m2:A word->A word_loc`; `c2':bool`]
    word_gc_move_thm) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [GCP1AUX_SEP_AC_TAC; ALL_TAC] THEN STRIP_TAC THEN
  GCP1AUX_SUBST_LVARS_TAC ["w2";"i2";"n2";"pa2"] THEN
  FIRST_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) &&
                           free_in `m2:A word->A word_loc` (concl th)
                        then ASSUME_TAC (GCP1AUX_SEP_WRITE `k:A word`
                               `word_addr conf (y2:(A word_loc)heap_address)` th)
                        else failwith "") THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a2:num`; `LENGTH (xs1:(A word_loc)list)`;
    `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `word_add pa (word_mul bytes_in_word (word (heap_length
       (h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))):A word`;
    `y3:((A word_loc)heap_address)list`;
    `h3:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `a1:num`; `n1:num`;
    `heap1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `pa3:A word`; `((k:A word) =+ word_addr conf (y2:(A word_loc)heap_address)) m2`;
    `m3:A word->A word_loc`; `xs1:(A word_loc)list`;
    `i3:A word`; `c3':bool`;
    `word_heap pa (h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                       heap_element)list) conf STAR
     set_sep_one ((k:A word),word_addr conf (y2:(A word_loc)heap_address)) STAR
     (frame:(A word#A word_loc->bool)->bool)`;
    `word_add (k:A word) bytes_in_word`; `k3:A word`;
    `conf:data_to_word_config`; `curr:A word`; `dm:A word->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [GCP1AUX_SEP_AC_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `xs1':(A word_loc)list` THEN
  REWRITE_TAC[word_heap_APPEND; MAP; heap_length_APPEND; misc_word_list_def] THEN
  REPEAT CONJ_TAC THEN TRY GCP1AUX_SEP_AC_TAC THEN ASM_REWRITE_TAC[WORD_ADD; LENGTH; ADD1] THEN
  CONV_TAC WORD_RULE);;

(* HOL4 line 996 *)
let word_payload_swap = prove
 (`!l5 tag r conf (h:A word) xs'.
     word_payload l5 (LENGTH l5) tag r conf = (h,MAP (word_addr conf) l5,T) /\
     LENGTH xs' = LENGTH l5 ==>
     word_payload xs' (LENGTH l5) tag r conf = (h,MAP (word_addr conf) xs',T)`,
  REPEAT GEN_TAC THEN CASES_ON `tag:data_to_word_memoryProof_tag` THEN
  REWRITE_TAC[word_payload_def; PAIR_EQ] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_EQ_NIL]) THEN
  ASM_MESON_TAC[LENGTH_EQ_NIL; MAP]);;
(* ------------------------------------------------------------------------- *)
(* Helpers for word_gc_move_loop_thm and word_gen_gc_move_loop_thm          *)
(* ------------------------------------------------------------------------- *)

let GCP1AUX_new_addr_ne = prove
 (`!(new:A word) k1 k2.
     good_dimindex (:A) /\ k1 < k2 /\ k2 * (dimindex (:A) DIV 8) < dimword (:A) ==>
     ~(word_add new (word_mul (word k1) bytes_in_word) =
       word_add new (word_mul (word k2) bytes_in_word))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[WORD_EQ_ADD_LCANCEL; bytes_in_word_def; GSYM WORD_MUL]) THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:A word->num`) THEN
  REWRITE_TAC[VAL_WORD; GSYM dimword_def] THEN
  SUBGOAL_THEN `~(dimindex (:A) DIV 8 = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `k1 * dimindex (:A) DIV 8 < dimword (:A)` ASSUME_TAC THENL
   [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `k2 * dimindex (:A) DIV 8` THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; EQ_MULT_RCANCEL] THEN ASM_ARITH_TAC);;

(* a data element of a word heap split into header, payload and the rest *)
let GCP1AUX_word_heap_DE_split = prove
 (`!conf (curr:A word) ha ys l tag qs hb h ts.
     word_payload ys l tag qs conf = (h,ts,T) /\ LENGTH ts < 2 EXP (dimindex (:A) - 4) /\
     decode_length conf h = word (LENGTH ts) ==>
     word_heap curr (APPEND ha (CONS (DataElement ys l (tag,qs)) hb)) conf =
     word_heap curr ha conf STAR
     set_sep_one (word_add curr (word_mul bytes_in_word (word (heap_length ha))),wl_Word h) STAR
     misc_word_list (word_add (word_add curr (word_mul bytes_in_word (word (heap_length ha))))
                       bytes_in_word) ts STAR
     word_heap (word_add curr (word_mul bytes_in_word (word (heap_length ha + l + 1)))) hb conf`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[word_heap_APPEND; word_heap_def; word_el_def; el_length_def] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[misc_word_list_def; SEP_CLAUSES] THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add (c:A word) (word_mul b (word x))) (word_mul b (word y)) =
                         word_add c (word_mul b (word_add (word x) (word y)))`; GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `a + l + 1 = a + (l + 1)`] THEN
  CONV_TAC(fun t -> GCP1AUX_STAR_AC_EQ (lhs t) (rhs t) |> fun th -> EQT_INTRO th));;

let GCP1AUX_word_list_exists_elim = prove
 (`!(a:A word) n (p:((A word#B)->bool)->bool) s.
     (word_list_exists a n STAR p) s ==>
     ?xs:B list. LENGTH xs = n /\ (misc_word_list a xs STAR p) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_list_exists_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:B list` MP_TAC) THEN
  ONCE_REWRITE_TAC[GSYM STAR_ASSOC] THEN ONCE_REWRITE_TAC[STAR_COMM] THEN
  REWRITE_TAC[GSYM STAR_ASSOC; cond_STAR] THEN STRIP_TAC THEN
  EXISTS_TAC `xs:B list` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[STAR_COMM] THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 1005 *)
let word_gc_move_loop_thm = prove
 (`!h1 h2 a n heap c0 limit h11 a1 n1 heap1 i1 pa1 m1 c1 xs frame m k
    conf (curr:A word) new dm.
     (copying_gc_gc_move_loop (h1,h2,a,n,heap,c0,limit) = (h11,a1,n1,heap1,T)) /\
     c0 /\
     heap_length heap <= dimword (:A) DIV 2 EXP shift_length conf /\
     heap_length heap * (dimindex (:A) DIV 8) < dimword (:A) /\
     data_to_word_config_len_size conf + 2 < dimindex (:A) /\
     (word_heap curr heap conf STAR
      word_heap new (APPEND h1 h2) conf STAR
      misc_word_list
        (word_add new (word_mul (word (heap_length (APPEND h1 h2))) bytes_in_word))
        xs STAR frame) (fun2set (m,dm)) /\
     limit - heap_length h1 <= k /\
     limit = heap_length heap /\ good_dimindex (:A) /\
     (word_gc_move_loop k conf
        (word_add new (word_mul (word (heap_length h1)) bytes_in_word),word a,
         word_add new (word_mul (word (heap_length (APPEND h1 h2))) bytes_in_word),
         curr,m,dm,T) =
       (i1,pa1,m1,c1)) /\ LENGTH xs = n ==>
     ?xs1.
       (word_heap curr heap1 conf STAR
        word_heap (new:A word) h11 conf STAR
        misc_word_list pa1 xs1 STAR frame) (fun2set (m1,dm)) /\
       heap_length heap1 = heap_length heap /\
       c1 /\ (i1 = word a1) /\ n1 = LENGTH xs1 /\
       pa1 = word_add new (word_mul bytes_in_word (word (heap_length h11)))`,
  (MP_TAC(ISPEC `\(h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list,h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list,a:num,n:num,heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list,c0:bool,limit:num). !h11 a1 n1 heap1 i1 pa1 m1 c1 xs frame m k conf (curr:A word) new dm.
     (copying_gc_gc_move_loop (h1,h2,a,n,heap,c0,limit) = (h11,a1,n1,heap1,T)) /\
     c0 /\
     heap_length heap <= dimword (:A) DIV 2 EXP shift_length conf /\
     heap_length heap * (dimindex (:A) DIV 8) < dimword (:A) /\
     data_to_word_config_len_size conf + 2 < dimindex (:A) /\
     (word_heap curr heap conf STAR
      word_heap new (APPEND h1 h2) conf STAR
      misc_word_list
        (word_add new (word_mul (word (heap_length (APPEND h1 h2))) bytes_in_word))
        xs STAR frame) (fun2set (m,dm)) /\
     limit - heap_length h1 <= k /\
     limit = heap_length heap /\ good_dimindex (:A) /\
     (word_gc_move_loop k conf
        (word_add new (word_mul (word (heap_length h1)) bytes_in_word),word a,
         word_add new (word_mul (word (heap_length (APPEND h1 h2))) bytes_in_word),
         curr,m,dm,T) =
       (i1,pa1,m1,c1)) /\ LENGTH xs = n ==>
     ?xs1.
       (word_heap curr heap1 conf STAR
        word_heap (new:A word) h11 conf STAR
        misc_word_list pa1 xs1 STAR frame) (fun2set (m1,dm)) /\
       heap_length heap1 = heap_length heap /\
       c1 /\ (i1 = word a1) /\ n1 = LENGTH xs1 /\
       pa1 = word_add new (word_mul bytes_in_word (word (heap_length h11)))` copying_gc_gc_move_loop_ind) THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC) THENL
  [(REPEAT GEN_TAC THEN REWRITE_TAC[copying_gc_gc_move_loop_def; PAIR_EQ; APPEND_NIL] THEN
  STRIP_TAC THEN GCP1AUX_SUBST_VARS_TAC ["h11";"a1";"n1";"heap1"] THEN
  GCP1AUX_UNDISCH_EQ "word_gc_move_loop" THEN ONCE_REWRITE_TAC[word_gc_move_loop_def] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN GCP1AUX_SUBST_VARS_TAC ["i1";"pa1";"m1";"c1"] THEN
  EXISTS_TAC `xs:(A word_loc)list` THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_MUL_SYM]);
  (REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `limit = heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`)) THEN
  FIRST_X_ASSUM(fun th -> if concl th = `c0:bool` then SUBST_ALL_TAC (EQT_INTRO th)
                          else failwith "") THEN
  GCP1AUX_UNDISCH_EQ "copying_gc_gc_move_loop" THEN
  ONCE_REWRITE_TAC[copying_gc_gc_move_loop_def] THEN
  COND_CASES_TAC THENL [REWRITE_TAC[PAIR_EQ]; ALL_TAC] THEN
  MP_TAC(ISPEC `h:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `u:num` SUBST_ALL_TAC)
    (DISJ_CASES_THEN2
      (X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `pd:A word_loc`
         (X_CHOOSE_THEN `l:num` SUBST_ALL_TAC)))
      (X_CHOOSE_THEN `ys:((A word_loc)heap_address)list` (X_CHOOSE_THEN `l:num`
         (X_CHOOSE_THEN `tg:data_to_word_memoryProof_tag#(A word_loc)list`
            SUBST_ALL_TAC))))) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  MP_TAC(ISPEC `tg:data_to_word_memoryProof_tag#(A word_loc)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tag:data_to_word_memoryProof_tag`
    (X_CHOOSE_THEN `qs:(A word_loc)list` SUBST_ALL_TAC)) THEN
  GCP1AUX_TUPLE_TAC `copying_gc_gc_move_list (ys:((A word_loc)heap_address)list,[]:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list,a,n,heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list,T,heap_length heap)`
    ["ys3";"hn";"a3";"n3";"heap3";"c3"] THEN
  SUBGOAL_THEN `copying_gc_gc_move_list (ys:((A word_loc)heap_address)list,
      CONS (DataElement ys l (tag,qs)) (h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list),a,n,heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list,T,heap_length heap) =
      (ys3,APPEND (CONS (DataElement ys l (tag,qs)) h2) hn,a3,n3,heap3,c3)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[copying_gc_gc_move_list_ALT] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[APPEND; HD; TL; NOT_CONS_NIL; LET_DEF; LET_END_DEF] THEN DISCH_TAC) THEN
  (REMOVE_THEN "IH" (MP_TAC o SPECL [`ys:((A word_loc)heap_address)list`; `l:num`;
     `(tag,qs):data_to_word_memoryProof_tag#(A word_loc)list`; `ys3:((A word_loc)heap_address)list`;
     `APPEND (CONS (DataElement ys l (tag,qs)) h2) hn:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `a3:num`; `n3:num`; `heap3:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
     `c3:bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[APPEND; HD; TL; NOT_CONS_NIL] THEN DISCH_THEN(LABEL_TAC "IH") THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP copying_gc_gc_move_loop_ok) THEN
  DISCH_THEN(fun th -> SUBST_ALL_TAC (EQT_INTRO th)) THEN
  GCP1AUX_UNDISCH_EQ "word_gc_move_loop" THEN
  ONCE_REWRITE_TAC[word_gc_move_loop_def] THEN
  SUBGOAL_THEN `~(word_add new (word_mul (word (heap_length (h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))) bytes_in_word) =
                  word_add new (word_mul (word (heap_length (APPEND h1
                     (CONS (DataElement ys l (tag,qs)) h2)))) bytes_in_word):A word)`
     (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC GCP1AUX_new_addr_ne THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def] THEN ARITH_TAC;
      MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) * dimindex (:A) DIV 8` THEN
      ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(k = 0)` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) - heap_length (h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) <= k` THEN
    UNDISCH_TAC `~(heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) <
                   heap_length (APPEND h1 (CONS (DataElement ys l (tag,qs)) (h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))))` THEN
    REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) then
     let wh = find (fun t -> gcp1_is_app "word_heap" t && free_in `new:A word` t)
                   (gcp1_star_leaves (rator (concl th))) in
     MP_TAC(MATCH_MP GCP1AUX_heap_el_read (GCP1AUX_STAR_FRONT [wh] th)) else NO_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `hh:A word` (X_CHOOSE_THEN `ts:(A word_loc)list` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[ISPECL [`word (heap_length (h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)):A word`; `bytes_in_word:A word`] WORD_MUL_SYM] THEN
  ASM_REWRITE_TAC[theWord_def; isWord_def; LET_DEF; LET_END_DEF] THEN
  GCP1AUX_ASM_MP (ISPECL [`ys:((A word_loc)heap_address)list`; `l:num`; `tag:data_to_word_memoryProof_tag`;
    `qs:(A word_loc)list`; `conf:data_to_word_config`; `hh:A word`; `ts:(A word_loc)list`]
    word_payload_T_IMP) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2)) THEN
  (ASM_CASES_TAC `bit 2 (hh:A word)` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN SUBST_ALL_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in is_eq c &&
      gcp1_is_app "copying_gc_gc_move_list" (lhs c) &&
      free_in `hn:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` (rhs c) && not (free_in `h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` (lhand c)))) THEN
    REWRITE_TAC[copying_gc_gc_move_list_def; PAIR_EQ] THEN STRIP_TAC THEN
    GCP1AUX_SUBST_VARS_TAC ["ys3";"hn";"a3";"n3";"heap3"] THEN
    REMOVE_THEN "IH" (MP_TAC o SPECL [`h11:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `a1:num`; `n1:num`; `heap1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `i1:A word`; `pa1:A word`; `m1:A word->A word_loc`; `c1:bool`; `xs:(A word_loc)list`;
      `frame:(A word#A word_loc->bool)->bool`; `m:A word->A word_loc`; `k - 1`;
      `conf:data_to_word_config`; `curr:A word`; `new:A word`; `dm:A word->bool`]) THEN
    ANTS_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL]) THEN
      REWRITE_TAC[APPEND_NIL; GSYM APPEND_ASSOC; APPEND] THEN
      SUBGOAL_THEN `word_add new (word_mul (word (heap_length (APPEND (h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
                       [DataElement [] l (tag,qs)]))) bytes_in_word) =
                    word_add (word_add new (word_mul bytes_in_word (word (heap_length h1))))
                      (word_mul (word_add (word l) (word 1)) bytes_in_word):A word` SUBST1_TAC THENL
       [REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def; heap_length_NIL;
                    WORD_ADD; ADD_CLAUSES] THEN CONV_TAC WORD_RULE;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
        gcp1_is_app "word_gc_move_loop" (lhs (concl th)))) THEN
      SUBST1_TAC(ISPECL [`bytes_in_word:A word`; `word (heap_length (APPEND (h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
          (CONS (DataElement [] l (tag,qs)) h2))):A word`] WORD_MUL_SYM) THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) - heap_length (h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) <= k` THEN
      UNDISCH_TAC `~(heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) <
                     heap_length (APPEND h1 (CONS (DataElement [] l (tag,qs)) (h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))))` THEN
      REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def; heap_length_NIL] THEN
      ARITH_TAC;
      DISCH_THEN ACCEPT_TAC];
    ALL_TAC]) THEN
  (DISCH_TAC THEN GCP1AUX_SUBST_LVARS_TAC ["ts"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `LENGTH (ys:((A word_loc)heap_address)list) = l`)) THEN
  GCP1AUX_SPLITN_TAC "word_gc_move_list" ["pb3";"i3";"pa3";"m3";"c3"] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `new:A word`; `h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `ys:((A word_loc)heap_address)list`; `LENGTH (ys:((A word_loc)heap_address)list)`;
    `tag:data_to_word_memoryProof_tag`; `qs:(A word_loc)list`; `h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `hh:A word`;
    `MAP (word_addr conf) (ys:((A word_loc)heap_address)list)`] GCP1AUX_word_heap_DE_split) THEN
  REWRITE_TAC[LENGTH_MAP] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp1_is_fun2set_asm o concl)) THEN
  SUBST1_TAC(ISPECL [`word (heap_length (APPEND (h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
      (CONS (DataElement ys (LENGTH (ys:((A word_loc)heap_address)list)) (tag,qs)) h2))):A word`;
      `bytes_in_word:A word`] WORD_MUL_SYM) THEN
  DISCH_TAC) THEN
  (MP_TAC(ISPECL [`ys:((A word_loc)heap_address)list`; `a:num`; `n:num`; `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`;
    `word_add new (word_mul bytes_in_word (word (heap_length (APPEND (h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
       (CONS (DataElement ys (LENGTH (ys:((A word_loc)heap_address)list)) (tag,qs)) h2))))):A word`;
    `ys3:((A word_loc)heap_address)list`; `hn:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `a3:num`; `n3:num`; `heap3:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `pa3:A word`; `m:A word->A word_loc`; `m3:A word->A word_loc`; `xs:(A word_loc)list`;
    `i3:A word`; `c3':bool`;
    `word_heap new (h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) conf STAR
     set_sep_one (word_add new (word_mul bytes_in_word (word (heap_length h1))),wl_Word (hh:A word)) STAR
     word_heap (word_add new (word_mul bytes_in_word
       (word (heap_length h1 + LENGTH (ys:((A word_loc)heap_address)list) + 1)))) (h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) conf STAR
     (frame:(A word#A word_loc->bool)->bool)`;
    `word_add (word_add new (word_mul bytes_in_word (word (heap_length (h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))))) bytes_in_word:A word`;
    `pb3:A word`; `conf:data_to_word_config`; `curr:A word`; `dm:A word->bool`]
    word_gc_move_list_thm) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GCP1AUX_SEP_AC_TAC;
      MP_TAC(SPEC `LENGTH (ys:((A word_loc)heap_address)list)` GCP1AUX_len_bound) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs2:(A word_loc)list` STRIP_ASSUME_TAC)) THEN
  (GCP1AUX_SUBST_LVARS_TAC ["i3";"pb3";"pa3"] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `c3':bool` then SUBST_ALL_TAC (EQT_INTRO th)
                          else failwith "") THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP gc_move_list_IMP_LENGTH) THEN
  MP_TAC(ISPECL [`ys:((A word_loc)heap_address)list`; `tag:data_to_word_memoryProof_tag`;
    `qs:(A word_loc)list`; `conf:data_to_word_config`; `hh:A word`;
    `ys3:((A word_loc)heap_address)list`] word_payload_swap) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `word_add new (word_mul (word (heap_length (APPEND (h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
       [DataElement ys3 (LENGTH (ys:((A word_loc)heap_address)list)) (tag,qs)]))) bytes_in_word) =
    word_add (word_add (word_add new (word_mul bytes_in_word (word (heap_length h1)))) bytes_in_word)
      (word_mul (word (LENGTH ys)) bytes_in_word):A word /\
    word_add new (word_mul (word (heap_length (APPEND h1
       (CONS (DataElement ys3 (LENGTH ys) (tag,qs)) (APPEND (h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) (hn:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))))) bytes_in_word) =
    word_add (word_add new (word_mul bytes_in_word (word (heap_length (APPEND h1
       (CONS (DataElement ys (LENGTH ys) (tag,qs)) h2))))))
      (word_mul (word (heap_length hn)) bytes_in_word):A word /\
    word_add (word_add new (word_mul bytes_in_word (word (heap_length h1 + LENGTH ys + 1))))
      (word_mul bytes_in_word (word (heap_length h2))) =
    word_add new (word_mul bytes_in_word (word (heap_length (APPEND h1
       (CONS (DataElement ys (LENGTH ys) (tag,qs)) h2))))):A word`
   (CONJUNCTS_THEN2 (LABEL_TAC "A1") (CONJUNCTS_THEN2 (LABEL_TAC "A2") (LABEL_TAC "A3"))) THENL
   [REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def; heap_length_NIL;
                WORD_ADD; ADD_CLAUSES] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
  (SUBGOAL_THEN `(word_heap curr heap3 conf STAR
      word_heap new (APPEND (APPEND (h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
        [DataElement ys3 (LENGTH (ys:((A word_loc)heap_address)list)) (tag,qs)]) (APPEND h2 hn)) conf STAR
      misc_word_list (word_add new (word_mul (word (heap_length
        (APPEND (APPEND h1 [DataElement ys3 (LENGTH ys) (tag,qs)]) (APPEND h2 hn)))) bytes_in_word)) xs2 STAR
      (frame:(A word#A word_loc->bool)->bool)) (fun2set ((m3:A word->A word_loc),(dm:A word->bool)))`
    ASSUME_TAC THENL
   [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
    MP_TAC(ISPECL [`conf:data_to_word_config`; `new:A word`; `h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `ys3:((A word_loc)heap_address)list`; `LENGTH (ys:((A word_loc)heap_address)list)`;
      `tag:data_to_word_memoryProof_tag`; `qs:(A word_loc)list`; `APPEND (h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) (hn:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`;
      `hh:A word`; `MAP (word_addr conf) (ys3:((A word_loc)heap_address)list)`]
      GCP1AUX_word_heap_DE_split) THEN
    REWRITE_TAC[LENGTH_MAP] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[word_heap_APPEND] THEN
    USE_THEN "A2" SUBST1_TAC THEN USE_THEN "A3" SUBST1_TAC THEN
    GCP1AUX_SEP_AC_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_gc_move_loop (k - 1) conf
      (word_add (new:A word) (word_mul (word (heap_length (APPEND (h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
         [DataElement ys3 (LENGTH (ys:((A word_loc)heap_address)list)) (tag,qs)]))) bytes_in_word),
       word a3,
       word_add new (word_mul (word (heap_length (APPEND (APPEND h1
         [DataElement ys3 (LENGTH ys) (tag,qs)]) (APPEND h2 hn)))) bytes_in_word),
       curr:A word, m3:A word->A word_loc, dm:A word->bool, T) = (i1,pa1,m1,c1:bool)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
    USE_THEN "A1" SUBST1_TAC THEN USE_THEN "A2" SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) - heap_length (APPEND (h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
      [DataElement ys3 (LENGTH (ys:((A word_loc)heap_address)list)) (tag,qs)]) <= k - 1`
    ASSUME_TAC THENL
   [UNDISCH_TAC `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) - heap_length (h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) <= k` THEN
    UNDISCH_TAC `~(heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) <
      heap_length (APPEND h1 (CONS (DataElement ys (LENGTH (ys:((A word_loc)heap_address)list)) (tag,qs)) (h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))))` THEN
    REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def; heap_length_NIL] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "IH" (MP_TAC o SPECL [`h11:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `a1:num`; `n1:num`; `heap1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `i1:A word`; `pa1:A word`; `m1:A word->A word_loc`; `c1:bool`; `xs2:(A word_loc)list`;
    `frame:(A word#A word_loc->bool)->bool`; `m3:A word->A word_loc`; `k - 1`;
    `conf:data_to_word_config`; `curr:A word`; `new:A word`; `dm:A word->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs9:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `xs9:(A word_loc)list` THEN ASM_REWRITE_TAC[])]);;

(* HOL4 line 1139 *)
let word_full_gc_thm = prove
 (`!roots heap limit roots1 heap1 a1 conf (curr:A word) new frame m dm
    rs1 i1 pa1 m1 c1.
     (full_gc (roots,heap,limit) = (roots1,heap1,a1,T)) /\
     heap_length heap <= dimword (:A) DIV 2 EXP shift_length conf /\
     heap_length heap * (dimindex (:A) DIV 8) < dimword (:A) /\
     data_to_word_config_len_size conf + 2 < dimindex (:A) /\
     (word_heap (curr:A word) heap conf STAR
      word_heap new (heap_expand limit) conf STAR frame) (fun2set (m,dm)) /\
     limit = heap_length heap /\ good_dimindex (:A) /\
     (word_full_gc conf (MAP (word_addr conf) roots,new,curr,m,dm) =
        (rs1,i1,pa1,m1,c1)) ==>
     (word_heap new (APPEND heap1 (heap_expand (limit - a1))) conf STAR
      word_heap curr (heap_expand limit) conf STAR frame) (fun2set (m1,dm)) /\
     c1 /\ i1 = word a1 /\
     rs1 = MAP (word_addr conf) roots1 /\
     pa1 = word_add new (word_mul bytes_in_word (word a1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `limit = heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`)) THEN
  GCP1AUX_UNDISCH_EQ "full_gc" THEN REWRITE_TAC[full_gc_def; LET_DEF; LET_END_DEF] THEN
  GCP1AUX_SPLITN_TAC "copying_gc_gc_move_list" ["r2";"h22";"a2";"n2";"heap2";"c2"] THEN
  GCP1AUX_SPLITN_TAC "copying_gc_gc_move_loop" ["heap3";"a3";"n3";"temp3";"c3"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  GCP1AUX_SUBST_VARS_TAC ["roots1";"heap1";"a1"] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `c3:bool` then SUBST_ALL_TAC (EQT_INTRO th)
                          else failwith "") THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP copying_gc_gc_move_loop_ok) THEN
  DISCH_THEN(fun th -> SUBST_ALL_TAC (EQT_INTRO th)) THEN
  GCP1AUX_UNDISCH_EQ "word_full_gc" THEN REWRITE_TAC[word_full_gc_def; LET_DEF; LET_END_DEF] THEN
  GCP1AUX_SPLITN_TAC "word_gc_move_roots" ["rs4";"i4";"pa4";"m4";"c4"] THEN
  GCP1AUX_SPLITN_TAC "word_gc_move_loop" ["i5";"pa5";"m5";"c5"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  GCP1AUX_SUBST_VARS_TAC ["rs1";"i1";"pa1";"m1";"c1"] THEN
  FIRST_X_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) then
     let th1 = REWRITE_RULE[word_heap_heap_expand] th in
     let wl = find (gcp1_is_app "word_list_exists") (gcp1_star_leaves (rator (concl th1))) in
     MP_TAC(MATCH_MP GCP1AUX_word_list_exists_elim (GCP1AUX_STAR_FRONT [wl] th1))
     else failwith "") THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`roots:((A word_loc)heap_address)list`; `0`; `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`; `new:A word`;
    `r2:((A word_loc)heap_address)list`; `h22:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `a2:num`; `n2:num`; `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `pa4:A word`; `m:A word->A word_loc`; `m4:A word->A word_loc`; `xs:(A word_loc)list`;
    `i4:A word`; `c4:bool`; `rs4:(A word_loc)list`; `frame:(A word#A word_loc->bool)->bool`;
    `conf:data_to_word_config`; `curr:A word`; `dm:A word->bool`] word_gc_move_roots_thm) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN GCP1AUX_SEP_AC_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs1:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  GCP1AUX_SUBST_LVARS_TAC ["pa4";"i4";"rs4"] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `c4:bool` then SUBST_ALL_TAC (EQT_INTRO th)
                          else failwith "") THEN
  MP_TAC(ISPECL [`[]:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `h22:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `a2:num`; `n2:num`; `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `T`;
    `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`; `heap3:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `a3:num`; `n3:num`; `temp3:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `i5:A word`; `pa5:A word`; `m5:A word->A word_loc`; `c5:bool`; `xs1:(A word_loc)list`;
    `frame:(A word#A word_loc->bool)->bool`; `m4:A word->A word_loc`; `dimword(:A)`;
    `conf:data_to_word_config`; `curr:A word`; `new:A word`; `dm:A word->bool`]
    word_gc_move_loop_thm) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[APPEND; heap_length_NIL; WORD_MUL_0; WORD_ADD_0; SUB_0] THEN
    MP_TAC(SPECL [`dimword(:A)`; `2 EXP shift_length conf`] DIV_LE) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs2:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  GCP1AUX_SUBST_LVARS_TAC ["pa5";"i5"] THEN
  FIRST_X_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) && free_in `temp3:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` (concl th) then
     let wh = find (fun t -> gcp1_is_app "word_heap" t && free_in `temp3:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` t)
                   (gcp1_star_leaves (rator (concl th))) in
     ASSUME_TAC (MATCH_MP word_heap_IMP_word_list_exists
                   (ONCE_REWRITE_RULE[STAR_COMM] (GCP1AUX_STAR_FRONT [wh] th)))
     else failwith "") THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `heap_length (temp3:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) = heap_length (heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`;
                              ASSUME `heap_length (heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) = heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`]) THEN
  REWRITE_TAC[word_heap_APPEND; word_heap_heap_expand] THEN
  CONJ_TAC THENL
   [GCP1AUX_SEP_FOCUS_GOAL_TAC (fun t -> gcp1_is_app "word_list_exists" t && free_in `new:A word` t) THEN
    MATCH_MP_TAC GCP1AUX_word_list_exists_intro THEN EXISTS_TAC `xs2:(A word_loc)list` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; GCP1AUX_SEP_AC_TAC];
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 1196 *)
let LIST_REL_EQ_MAP = prove
 (`!(vs:A list) (ws:B list) f. ALL2 (\v w. f v = w) vs ws <=> ws = MAP f vs`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; MAP; NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]);;

(* HOL4 line 1202 *)
let full_gc_IMP = prove
 (`!xs (heap:((A,B)heap_element)list) limit t heap2 n.
     full_gc (xs,heap,limit) = (t,heap2,n,T) ==>
     n <= limit /\ limit = heap_length heap`,
  REPEAT GEN_TAC THEN REWRITE_TAC[full_gc_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  GCP1AUX_TUPLE_TAC `copying_gc_gc_move_list (xs:(A heap_address)list,
     []:((A,B)heap_element)list,0,limit,heap:((A,B)heap_element)list,T,limit)`
    ["r1";"h2";"a2";"n2";"hp2";"c2"] THEN
  GCP1AUX_TUPLE_TAC `copying_gc_gc_move_loop ([]:((A,B)heap_element)list,
     h2:((A,B)heap_element)list,a2,n2,hp2:((A,B)heap_element)list,c2,limit)`
    ["heap3";"a3";"n3";"temp3";"c3"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 1212 *)
let is_ref_header_alt = prove
 (`!w:A word. good_dimindex (:A) ==> (is_ref_header w <=> ~(bit 2 w) /\ bit 3 w)`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN DISCH_TAC THEN
  SUBGOAL_THEN `4 <= dimindex(:A)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[is_ref_header_def; WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD] THEN
  EQ_TAC THENL
   [DISCH_THEN(fun th -> MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `2 < dimindex(:A) /\ 3 < dimindex(:A)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; MESON_TAC[]];
    STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `i < 4` THENL
     [FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o
        MATCH_MP (ARITH_RULE `i < 4 ==> i = 0 \/ i = 1 \/ i = 2 \/ i = 3`)) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      GCP1AUX_DIV_2EXP_0_TAC THEN REWRITE_TAC[ODD]]]);;

(* HOL4 line 1226 *)
let is_ref_header_thm = prove
 (`!addrs ll tt0 tt1 conf (h:A word) ts c5.
     (word_payload addrs ll tt0 tt1 conf = (h,ts,c5)) /\ good_dimindex (:A) /\
     data_to_word_config_len_size conf + 5 <= dimindex (:A) ==>
     (is_ref_header h <=> isMutTag tt0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP is_ref_header_alt th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[good_dimindex_def]) THEN
  SUBGOAL_THEN `~(dimindex(:A) - data_to_word_config_len_size conf <= 3) /\ 3 < dimindex(:A)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `word_payload addrs ll tt0 tt1 conf = (h:A word,ts,c5)` THEN
  CASES_ON `tt0:data_to_word_memoryProof_tag` THEN
  REWRITE_TAC[word_payload_def; PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
  REWRITE_TAC[make_header_def; make_byte_header_def; LET_DEF; LET_END_DEF; isMutTag_def] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN GCP1AUX_DECIDE_TAC THEN
  REWRITE_TAC[distinctness "data_to_word_memoryProof_tag";
              injectivity "data_to_word_memoryProof_tag"] THEN
  MESON_TAC[]);;

(* HOL4 line 1239 *)
let is_Ref_def = cake_def
  `(is_Ref is_ref_tag (DataElement xs l (r:B)) <=> is_ref_tag r) /\
   (is_Ref is_ref_tag (_:(A,B)heap_element) <=> F)`;;

(* HOL4 line 1244 *)
let len_inv_def = cake_def
  `len_inv (s:(A,B)gc_state) <=>
     heap_length (gc_state_heap s) =
     heap_length (APPEND (gc_state_h1 s) (gc_state_h2 s)) + gc_state_n s +
     heap_length (APPEND (APPEND (APPEND (gc_state_r4 s) (gc_state_r3 s))
                                 (gc_state_r2 s)) (gc_state_r1 s))`;;
let GCP1AUX_word_sub = prove
 (`!x y. y <= x ==> word_sub (word x) (word y) = word (x - y):A word`,
  SIMP_TAC[WORD_SUB]);;

let GCP1AUX_pb_sub = prove
 (`!(pa:A word) k j.
     word_sub (word_add pa (word_mul bytes_in_word (word (k + j))))
              (word_mul (word j) bytes_in_word) =
     word_add pa (word_mul (word k) bytes_in_word)`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let GCP1AUX_pb_add = prove
 (`!(pa:A word) k j.
     word_add pa (word_mul bytes_in_word (word (k + j))) =
     word_add (word_add pa (word_mul (word j) bytes_in_word))
              (word_mul bytes_in_word (word k))`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

(* HOL4 line 1250 *)
let word_gen_gc_move_thm = prove
 (`!gen_conf s x x1 s1 conf (curr:A word) pa xs frame m dm w i1 pa1 ib1 pb1 m1 c1.
     (gen_gc_gc_move gen_conf s x = (x1,s1)) /\ gc_state_ok s1 /\
     gc_state_h2 s = [] /\ gc_state_r4 s = [] /\
     heap_length (gc_state_heap s) <= dimword (:A) DIV 2 EXP shift_length conf /\
     (!t r. (gen_gc_conf_isRef gen_conf (t,r) <=> isMutTag t)) /\
     data_to_word_config_len_size conf + 5 <= dimindex (:A) /\
     (word_heap curr (gc_state_heap s) conf STAR
      misc_word_list pa xs STAR frame) (fun2set (m,dm)) /\
     (word_gen_gc_move conf
        (word_addr conf x,word (gc_state_a s),pa,
         word (gc_state_a s + gc_state_n s),
         word_add pa (word_mul bytes_in_word (word (gc_state_n s))),curr,m,dm) =
       (w:A word_loc,i1,pa1,ib1,pb1,m1,c1)) /\
     LENGTH xs = gc_state_n s /\ good_dimindex (:A) /\
     ALL (is_Ref (gen_gc_conf_isRef gen_conf))
       (APPEND (APPEND (APPEND (gc_state_r4 s) (gc_state_r3 s)) (gc_state_r2 s))
          (gc_state_r1 s)) ==>
     ?xs1.
       (word_heap curr (gc_state_heap s1) conf STAR
        word_heap pa (gc_state_h2 s1) conf STAR
        word_heap pb1 (gc_state_r4 s1) conf STAR
        misc_word_list pa1 xs1 STAR
        frame) (fun2set (m1,dm)) /\
       (w = word_addr conf x1) /\
       heap_length (gc_state_heap s1) = heap_length (gc_state_heap s) /\ c1 /\
       (i1 = word (gc_state_a s1)) /\
       (ib1 = word (gc_state_a s1 + gc_state_n s1)) /\
       gc_state_n s1 = LENGTH xs1 /\
       gc_state_n s =
         heap_length (gc_state_h2 s1) + gc_state_n s1 + heap_length (gc_state_r4 s1) /\
       pa1 = word_add pa (word_mul bytes_in_word (word (heap_length (gc_state_h2 s1)))) /\
       pb1 = word_add pa1 (word_mul bytes_in_word (word (gc_state_n s1))) /\
       ALL (is_Ref (gen_gc_conf_isRef gen_conf))
         (APPEND (APPEND (APPEND (gc_state_r4 s1) (gc_state_r3 s1)) (gc_state_r2 s1))
            (gc_state_r1 s1))`,
  (REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `x:(A word_loc)heap_address` (cases "heap_address")) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (X_CHOOSE_THEN `ptr:num` (X_CHOOSE_THEN `dd:A word_loc` SUBST1_TAC))
    (X_CHOOSE_THEN `dv:A word_loc` SUBST1_TAC)) THENL
   [ALL_TAC;
    REWRITE_TAC[gen_gc_gc_move_def; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MP_TAC(ISPEC `dv:A word_loc` (cases "word_loc")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:A word` SUBST_ALL_TAC)
      (X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `l2:num` SUBST_ALL_TAC))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[word_addr_def; word_gen_gc_move_def; GCP1AUX_and_not_1;
                                PAIR_EQ]) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN RVEQ_TAC THEN
    EXISTS_TAC `xs:(A word_loc)list` THEN
    ASM_REWRITE_TAC[word_heap_def; SEP_CLAUSES; word_addr_def; heap_length_NIL;
                    WORD_MUL_0; WORD_ADD_0; ADD_CLAUSES]]) THEN
  (REWRITE_TAC[gen_gc_gc_move_def] THEN
  MP_TAC(ISPEC `heap_lookup ptr (gc_state_heap (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
               RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
               ASM_MESON_TAC[])
    (X_CHOOSE_THEN `el:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element`
       (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th] THEN CASE_REWRITE_TAC[]))) THEN
  MP_TAC(ISPEC `el:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `u:num` SUBST_ALL_TAC)
    (DISJ_CASES_THEN2
      (X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `pd:A word_loc`
         (X_CHOOSE_THEN `l:num` SUBST_ALL_TAC)))
      (X_CHOOSE_THEN `ys:((A word_loc)heap_address)list` (X_CHOOSE_THEN `l:num`
         (X_CHOOSE_THEN `tg:data_to_word_memoryProof_tag#(A word_loc)list`
            SUBST_ALL_TAC))))) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN ASM_MESON_TAC[];
    ALL_TAC;
    ALL_TAC]) THENL
   [(STRIP_TAC THEN GCP1AUX_SUBST_VARS_TAC ["x1";"s1"] THEN
  SUBGOAL_THEN `ptr * 2 EXP shift_length conf < dimword(:A)` ASSUME_TAC THENL
   [GCP1AUX_PTR_BOUND_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP heap_lookup_SPLIT) THEN
  DISCH_THEN(X_CHOOSE_THEN `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` (X_CHOOSE_THEN `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    (CONJUNCTS_THEN2 (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th])
                     SUBST_ALL_TAC))) THEN
  FIRST_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) then
     ASSUME_TAC (REWRITE_RULE[word_heap_APPEND; word_heap_def; word_el_def] th)
     else NO_TAC) THEN
  GCP1AUX_SEP_R_TAC THEN
  GCP1AUX_UNDISCH_EQ "word_gen_gc_move" THEN
  ASM_SIMP_TAC[word_addr_def; word_gen_gc_move_def; get_addr_and_1_not_0;
               GCP1AUX_ptr_to_addr_get_addr; LET_DEF; LET_END_DEF; is_fws_ptr_OR_3;
               theWord_def; isWord_def; GCP1AUX_update_addr_fwd; PAIR_EQ] THEN
  STRIP_TAC THEN GCP1AUX_SUBST_VARS_TAC ["w";"i1";"pa1";"ib1";"pb1";"m1";"c1"] THEN
  EXISTS_TAC `xs:(A word_loc)list` THEN
  ASM_REWRITE_TAC[word_heap_def; SEP_CLAUSES; heap_length_NIL; WORD_MUL_0; WORD_ADD_0;
                  ADD_CLAUSES]);
    (MP_TAC(ISPEC `tg:data_to_word_memoryProof_tag#(A word_loc)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tag:data_to_word_memoryProof_tag`
    (X_CHOOSE_THEN `qs:(A word_loc)list` SUBST_ALL_TAC)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ptr * 2 EXP shift_length conf < dimword(:A)` ASSUME_TAC THENL
   [GCP1AUX_PTR_BOUND_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP heap_lookup_SPLIT) THEN
  DISCH_THEN(X_CHOOSE_THEN `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` (X_CHOOSE_THEN `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    (CONJUNCTS_THEN2 (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th])
                     SUBST_ALL_TAC))) THEN
  FIRST_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) then
     let wh = hd (gcp1_star_leaves (rator (concl th))) in
     MP_TAC(MATCH_MP GCP1AUX_heap_el_read (GCP1AUX_STAR_FRONT [wh] th)) else NO_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:A word` (X_CHOOSE_THEN `ts:(A word_loc)list`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NOT_is_fwd_ptr) THEN
  SUBGOAL_THEN `is_ref_header (h:A word) <=> isMutTag tag` ASSUME_TAC THENL
   [MATCH_MP_TAC is_ref_header_thm THEN
    MAP_EVERY EXISTS_TAC [`ys:((A word_loc)heap_address)list`; `l:num`; `qs:(A word_loc)list`;
      `conf:data_to_word_config`; `ts:(A word_loc)list`; `T`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    free_in `x1:(A word_loc)heap_address` (rhs (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[gc_forward_ptr_thm; APPEND] THEN
  GCP1AUX_UNDISCH_EQ "word_gen_gc_move" THEN
  ASM_SIMP_TAC[word_addr_def; word_gen_gc_move_def; get_addr_and_1_not_0;
               GCP1AUX_ptr_to_addr_get_addr; LET_DEF; LET_END_DEF; theWord_def; isWord_def;
               GCP1AUX_update_addr_word]) THEN
    (ASM_CASES_TAC `isMutTag tag` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ]) THENL
     [(DISCH_TAC THEN STRIP_TAC THEN GCP1AUX_SUBST_VARS_TAC ["x1";"s1"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
    free_in `gc_state_ok (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` (concl th))) THEN
  SUBGOAL_THEN `word_sub (word (gc_state_a (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) + gc_state_n s)) (word_add (word l) (word 1)) =
                word (gc_state_a s + gc_state_n s - (l + 1)):A word /\
                word_sub (word_add pa (word_mul bytes_in_word (word (gc_state_n s))))
                  (word_mul (word_add (word l) (word 1)) bytes_in_word) =
                word_add pa (word_mul (word (gc_state_n s - (l + 1))) bytes_in_word):A word /\
                word_add (word l) (word 1) = word (l + 1):A word`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `gc_state_a (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) + gc_state_n s - (l + 1) =
                    (gc_state_a s + gc_state_n s) - (l + 1)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; MATCH_MP_TAC GCP1AUX_word_sub THEN ASM_ARITH_TAC];
      MP_TAC(ISPECL [`pa:A word`; `gc_state_n (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) - (l + 1)`; `l + 1`] GCP1AUX_pb_sub) THEN
      ASM_SIMP_TAC[SUB_ADD]];
    ALL_TAC]) THEN
      (GCP1AUX_UNDISCH_EQ "pair_CASE" THEN GCP1AUX_SPLITN_TAC "memcpy" ["b0";"m2";"c2"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  GCP1AUX_SUBST_VARS_TAC ["w";"i1";"pa1";"ib1";"pb1";"m1";"c1"] THEN
  MP_TAC(ISPECL [`l + 1`; `xs:(A word_loc)list`] LESS_EQ_IMP_APPEND_ALT) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ys1:(A word_loc)list` (X_CHOOSE_THEN `zs:(A word_loc)list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
  SUBGOAL_THEN `LENGTH (ys1:(A word_loc)list) = gc_state_n (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) - (l + 1)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      gcp1_is_app "LENGTH" (lhs (concl th)) && gcp1_is_app "APPEND" (rand (lhs (concl th))))) THEN
    ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_to_word_memoryProof_word_list_APPEND]) THEN
  FIRST_X_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
      (MP_TAC(ISPECL [`conf:data_to_word_config`; `curr:A word`; `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `ys:((A word_loc)heap_address)list`; `l:num`; `tag:data_to_word_memoryProof_tag`;
    `qs:(A word_loc)list`; `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `word_add pa (word_mul (word (gc_state_n (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) - (l + 1))) bytes_in_word):A word`;
    `zs:(A word_loc)list`; `m:A word->A word_loc`; `dm:A word->bool`;
    `gc_state_a (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) + gc_state_n s - (l + 1)`; `dd:A word_loc`; `h:A word`;
    `ts:(A word_loc)list`; `b0:A word`; `m2:A word->A word_loc`; `c2:bool`]
    GCP1AUX_heap_el_copy) THEN
  GCP1AUX_SEP_FRAME_TAC THEN
  ASM_SIMP_TAC[GCP1AUX_len_bound] THEN STRIP_TAC THEN
  EXISTS_TAC `ys1:(A word_loc)list` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_heap_def; SEP_CLAUSES]) THEN
  ASM_REWRITE_TAC[word_heap_def; SEP_CLAUSES; GCP1AUX_update_addr_word; word_addr_def;
                  heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def;
                  heap_length_NIL; ADD_CLAUSES; WORD_MUL_0; WORD_ADD_0; ALL; APPEND;
                  is_Ref_def] THEN
  REPEAT CONJ_TAC THEN TRY GCP1AUX_SEP_AC_TAC THEN
  TRY(REWRITE_TAC[WORD_MUL_SYM] THEN NO_TAC) THEN
  TRY(GCP1AUX_ARITH_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> gcp1_is_app "ALL" (concl th))) THEN
  ASM_REWRITE_TAC[APPEND]);
      (DISCH_TAC THEN STRIP_TAC THEN GCP1AUX_SUBST_VARS_TAC ["x1";"s1"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
    free_in `gc_state_ok (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` (concl th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD; GSYM ADD_ASSOC]) THEN
  GCP1AUX_UNDISCH_EQ "pair_CASE" THEN GCP1AUX_SPLITN_TAC "memcpy" ["pa2";"m2";"c2"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  GCP1AUX_SUBST_VARS_TAC ["w";"i1";"pa1";"ib1";"pb1";"m1";"c1"] THEN
  MP_TAC(ISPECL [`l + 1`; `xs:(A word_loc)list`] LESS_EQ_IMP_APPEND) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ys0:(A word_loc)list` (X_CHOOSE_THEN `zs:(A word_loc)list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_to_word_memoryProof_word_list_APPEND; LENGTH_APPEND]) THEN
  FIRST_X_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `curr:A word`; `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `ys:((A word_loc)heap_address)list`; `l:num`; `tag:data_to_word_memoryProof_tag`;
    `qs:(A word_loc)list`; `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `pa:A word`;
    `ys0:(A word_loc)list`; `m:A word->A word_loc`; `dm:A word->bool`;
    `gc_state_a (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`; `dd:A word_loc`; `h:A word`;
    `ts:(A word_loc)list`; `pa2:A word`; `m2:A word->A word_loc`; `c2:bool`]
    GCP1AUX_heap_el_copy) THEN
  GCP1AUX_SEP_FRAME_TAC THEN
  ASM_SIMP_TAC[GCP1AUX_len_bound] THEN STRIP_TAC THEN
  EXISTS_TAC `zs:(A word_loc)list` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_heap_def; SEP_CLAUSES]) THEN
  ASM_REWRITE_TAC[word_heap_def; SEP_CLAUSES; GCP1AUX_update_addr_word; word_addr_def;
                  heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def;
                  heap_length_NIL; ADD_CLAUSES; WORD_MUL_0; WORD_ADD_0; ALL; APPEND;
                  LENGTH_APPEND] THEN
  REPEAT CONJ_TAC THEN TRY GCP1AUX_SEP_AC_TAC THEN
  TRY(REWRITE_TAC[WORD_MUL_SYM] THEN NO_TAC) THEN
  TRY(GCP1AUX_ARITH_TAC) THEN
  TRY(AP_TERM_TAC THEN GCP1AUX_ARITH_TAC) THEN
  TRY(MP_TAC(ISPECL [`pa:A word`; `gc_state_n (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) - (l + 1)`; `l + 1`] GCP1AUX_pb_add) THEN
      ASM_SIMP_TAC[SUB_ADD] THEN NO_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> gcp1_is_app "ALL" (concl th))) THEN
  ASM_REWRITE_TAC[APPEND])]]);;

(* HOL4 line 1417 *)
let gc_move_with_NIL = prove
 (CASE_TERM
  `!x (s:(A,B)gc_state) y t gen_conf.
     gen_gc_gc_move gen_conf s x = (y,t) /\ gc_state_ok t ==>
     (let (y,s1) = gen_gc_gc_move gen_conf
                     (gc_state_h2_fupd (K []) (gc_state_r4_fupd (K []) s)) x in
      (y,gc_state_h2_fupd (K (APPEND (gc_state_h2 s) (gc_state_h2 s1)))
           (gc_state_r4_fupd (K (APPEND (gc_state_r4 s1) (gc_state_r4 s))) s1))) =
     (y,t)`,
  GEN_TAC THEN CASES_ON `x:A heap_address` THEN
  REWRITE_TAC[gen_gc_gc_move_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  SIMP[] THEN EVERY_CASE_TAC THEN REPEAT PAIRARG_TAC THEN
  RW[gc_state_component_equality; APPEND_NIL; APPEND] THEN ASM_MESON_TAC[]);;

(* HOL4 line 1435 (the unused bound variables y t h2 r4 are left out) *)
let gc_move_with_NIL_LEMMA = prove
 (`!x (s:(A,B)gc_state) y1 t1 gen_conf.
     gen_gc_gc_move gen_conf s x = (y1,t1) /\ gc_state_ok t1 ==>
     ?x1 x2.
       gc_state_h2 t1 = APPEND (gc_state_h2 s) x1 /\
       gc_state_r4 t1 = APPEND x2 (gc_state_r4 s) /\
       gen_gc_gc_move gen_conf (gc_state_h2_fupd (K []) (gc_state_r4_fupd (K []) s)) x =
         (y1,gc_state_h2_fupd (K x1) (gc_state_r4_fupd (K x2) t1))`,
  GEN_TAC THEN CASES_ON `x:A heap_address` THEN
  REWRITE_TAC[gen_gc_gc_move_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  SIMP[] THEN EVERY_CASE_TAC THEN REPEAT PAIRARG_TAC THEN
  RW[gc_state_component_equality; APPEND_NIL; APPEND] THEN
  TRY(ASM_MESON_TAC[]) THEN
  ASM_MESON_TAC[APPEND_NIL; APPEND]);;

(* HOL4 line 1454 (local) *)
let gc_move_list_ok_irr0 = prove
 (`!x (s:(A,B)gc_state) y1 y2 t1 t2 h2 r4 gen_conf.
     gen_gc_gc_move gen_conf s x = (y1,t1) /\
     gen_gc_gc_move gen_conf (gc_state_h2_fupd (K h2) (gc_state_r4_fupd (K r4) s)) x =
       (y2,t2) ==>
     y1 = y2 /\ ?x1 x2. t2 = gc_state_h2_fupd (K x1) (gc_state_r4_fupd (K x2) t1)`,
  GEN_TAC THEN CASES_ON `x:A heap_address` THEN
  REWRITE_TAC[gen_gc_gc_move_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  SIMP[] THEN EVERY_CASE_TAC THEN REPEAT PAIRARG_TAC THEN
  RW[gc_state_component_equality] THEN ASM_MESON_TAC[]);;

(* HOL4 line 1466 *)
let gc_move_list_ok_irr = prove
 (`!x (s:(A,B)gc_state) y1 y2 t1 t2 h2 r4 gen_conf.
     gen_gc_gc_move_list gen_conf s x = (y1,t1) /\ gc_state_ok t1 /\
     gen_gc_gc_move_list gen_conf (gc_state_h2_fupd (K h2) (gc_state_r4_fupd (K r4) s)) x =
       (y2,t2) ==>
     gc_state_ok t2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_gc_move_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN SIMP[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  GCP1AUX_TUPLE_TAC `gen_gc_gc_move (gen_conf:B gen_gc_conf) (s:(A,B)gc_state) h` ["z1";"s1"] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_gc_move_list (gen_conf:B gen_gc_conf) (s1:(A,B)gc_state) t` ["zs1";"u1"] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_gc_move (gen_conf:B gen_gc_conf)
     (gc_state_h2_fupd (K h2) (gc_state_r4_fupd (K r4) (s:(A,B)gc_state))) h` ["z2";"s2"] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_gc_move_list (gen_conf:B gen_gc_conf) (s2:(A,B)gc_state) t` ["zs2";"u2"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`h:A heap_address`; `s:(A,B)gc_state`; `z1:A heap_address`; `z2:A heap_address`;
    `s1:(A,B)gc_state`; `s2:(A,B)gc_state`; `h2:((A,B)heap_element)list`;
    `r4:((A,B)heap_element)list`; `gen_conf:B gen_gc_conf`] gc_move_list_ok_irr0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 1485 (HOL4: Q.prove ... |> SIMP_RULE std_ss [], which drops    *)
(* the unused bound variables y t h2 r4)                                    *)
let gc_move_list_with_NIL_LEMMA = prove
 (`!x (s:(A,B)gc_state) y1 t1 gen_conf.
     gen_gc_gc_move_list gen_conf s x = (y1,t1) /\ gc_state_ok t1 ==>
     ?x1 x2.
       gc_state_h2 t1 = APPEND (gc_state_h2 s) x1 /\
       gc_state_r4 t1 = APPEND x2 (gc_state_r4 s) /\
       gen_gc_gc_move_list gen_conf
         (gc_state_h2_fupd (K []) (gc_state_r4_fupd (K []) s)) x =
         (y1,gc_state_h2_fupd (K x1) (gc_state_r4_fupd (K x2) t1))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_gc_move_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`[]:((A,B)heap_element)list`; `[]:((A,B)heap_element)list`] THEN
    REWRITE_TAC[APPEND_NIL; APPEND]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  GCP1AUX_TUPLE_TAC `gen_gc_gc_move (gen_conf:B gen_gc_conf) (s:(A,B)gc_state) h` ["z1";"s1"] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_gc_move_list (gen_conf:B gen_gc_conf) (s1:(A,B)gc_state) t` ["zs1";"u1"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `gc_state_ok (s1:(A,B)gc_state)` ASSUME_TAC THENL
   [MATCH_MP_TAC gen_gc_gc_move_list_ok THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A heap_address`; `s:(A,B)gc_state`; `z1:A heap_address`;
    `s1:(A,B)gc_state`; `gen_conf:B gen_gc_conf`] gc_move_with_NIL_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:((A,B)heap_element)list` (X_CHOOSE_THEN
    `e1:((A,B)heap_element)list` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(fun ih -> GCP1AUX_ASM_MP (SPECL [`s1:(A,B)gc_state`; `zs1:(A heap_address)list`;
    `t1:(A,B)gc_state`; `gen_conf:B gen_gc_conf`] ih)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:((A,B)heap_element)list` (X_CHOOSE_THEN
    `e2:((A,B)heap_element)list` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_gc_move_list (gen_conf:B gen_gc_conf)
    (gc_state_h2_fupd (K d1) (gc_state_r4_fupd (K e1) (s1:(A,B)gc_state))) t` ["zs3";"u3"] THEN
  SUBGOAL_THEN `gc_state_ok (u3:(A,B)gc_state)` ASSUME_TAC THENL
   [MATCH_MP_TAC gc_move_list_ok_irr THEN
    MAP_EVERY EXISTS_TAC [`t:(A heap_address)list`; `s1:(A,B)gc_state`;
      `zs1:(A heap_address)list`; `zs3:(A heap_address)list`; `t1:(A,B)gc_state`;
      `d1:((A,B)heap_element)list`; `e1:((A,B)heap_element)list`; `gen_conf:B gen_gc_conf`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun ih -> GCP1AUX_ASM_MP (SPECL [`gc_state_h2_fupd (K d1)
    (gc_state_r4_fupd (K e1) (s1:(A,B)gc_state))`; `zs3:(A heap_address)list`;
    `u3:(A,B)gc_state`; `gen_conf:B gen_gc_conf`] ih)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:((A,B)heap_element)list` (X_CHOOSE_THEN
    `e3:((A,B)heap_element)list` STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  FIRST_X_ASSUM(fun th15 -> if free_in `zs3:(A heap_address)list` (concl th15) &&
      free_in `d3:((A,B)heap_element)list` (concl th15) then
      FIRST_X_ASSUM(fun th10 -> if free_in `zs1:(A heap_address)list` (concl th10) &&
          free_in `d2:((A,B)heap_element)list` (concl th10) &&
          gcp1_is_app "gen_gc_gc_move_list" (lhs (concl th10)) then
          MP_TAC (TRANS (SYM th15) th10) else failwith "")
    else failwith "") THEN
  REWRITE_TAC[PAIR_EQ; gc_state_component_equality] THEN SIMP[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`APPEND d1 d2:((A,B)heap_element)list`;
                        `APPEND e2 e1:((A,B)heap_element)list`] THEN
  ASM_REWRITE_TAC[APPEND_ASSOC; gc_state_component_equality] THEN SIMP[]);;

(* HOL4 line 1507 *)
let gc_move_list_with_NIL = prove
 (CASE_TERM
  `!x (s:(A,B)gc_state) y t gen_conf.
     gen_gc_gc_move_list gen_conf s x = (y,t) /\ gc_state_ok t ==>
     (let (y,s1) = gen_gc_gc_move_list gen_conf
                     (gc_state_h2_fupd (K []) (gc_state_r4_fupd (K []) s)) x in
      (y,gc_state_h2_fupd (K (APPEND (gc_state_h2 s) (gc_state_h2 s1)))
           (gc_state_r4_fupd (K (APPEND (gc_state_r4 s1) (gc_state_r4 s))) s1))) =
     (y,t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP gc_move_list_with_NIL_LEMMA) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:((A,B)heap_element)list` (X_CHOOSE_THEN
    `x2:((A,B)heap_element)list` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  ASM_REWRITE_TAC[gc_state_component_equality] THEN SIMP[]);;

(* HOL4 line 1517 *)
let word_gen_gc_move_roots_thm = prove
 (`!x xs x1 w s1 s pb1 pa1 pa m1 m ib1 i1 frame dm (curr:A word) c1 gen_conf conf.
     (gen_gc_gc_move_list gen_conf s x = (x1,s1)) /\ gc_state_ok s1 /\
     gc_state_h2 s = [] /\ gc_state_r4 s = [] /\
     heap_length (gc_state_heap s) <= dimword (:A) DIV 2 EXP shift_length conf /\
     (!t r. (gen_gc_conf_isRef gen_conf (t,r) <=> isMutTag t)) /\
     data_to_word_config_len_size conf + 5 <= dimindex (:A) /\
     (word_heap curr (gc_state_heap s) conf STAR
      misc_word_list pa xs STAR frame) (fun2set (m,dm)) /\
     (word_gen_gc_move_roots conf
        (MAP (word_addr conf) x,word (gc_state_a s),pa,
         word (gc_state_a s + gc_state_n s),
         word_add pa (word_mul bytes_in_word (word (gc_state_n s))),curr,m,dm) =
       (w:(A word_loc)list,i1,pa1,ib1,pb1,m1,c1)) /\
     ALL (is_Ref (gen_gc_conf_isRef gen_conf))
       (APPEND (APPEND (APPEND (gc_state_r4 s) (gc_state_r3 s)) (gc_state_r2 s))
          (gc_state_r1 s)) /\
     LENGTH xs = gc_state_n s /\ good_dimindex (:A) ==>
     ?xs1.
       (word_heap curr (gc_state_heap s1) conf STAR
        word_heap pa (gc_state_h2 s1) conf STAR
        word_heap pb1 (gc_state_r4 s1) conf STAR
        misc_word_list pa1 xs1 STAR
        frame) (fun2set (m1,dm)) /\
       (w = MAP (word_addr conf) x1) /\
       heap_length (gc_state_heap s1) = heap_length (gc_state_heap s) /\
       c1 /\ (i1 = word (gc_state_a s1)) /\
       (ib1 = word (gc_state_a s1 + gc_state_n s1)) /\
       gc_state_n s1 = LENGTH xs1 /\
       gc_state_n s =
         heap_length (gc_state_h2 s1) + gc_state_n s1 + heap_length (gc_state_r4 s1) /\
       pa1 = word_add pa (word_mul bytes_in_word (word (heap_length (gc_state_h2 s1)))) /\
       pb1 = word_add pa1 (word_mul bytes_in_word (word (gc_state_n s1))) /\
       ALL (is_Ref (gen_gc_conf_isRef gen_conf))
         (APPEND (APPEND (APPEND (gc_state_r4 s1) (gc_state_r3 s1)) (gc_state_r2 s1))
            (gc_state_r1 s1))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[gen_gc_gc_move_list_def; word_gen_gc_move_roots_def; MAP; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `xs:(A word_loc)list` THEN
    ASM_REWRITE_TAC[word_heap_def; SEP_CLAUSES; heap_length_NIL; WORD_MUL_0; WORD_ADD_0;
                    MAP; ADD_CLAUSES];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[gen_gc_gc_move_list_def; MAP; word_gen_gc_move_roots_def] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_gc_move (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list) gen_gc_conf) (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) h` ["y2";"s2"] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_gc_move_list (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list) gen_gc_conf) (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) t` ["y3";"s3"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN GCP1AUX_SUBST_VARS_TAC ["x1";"s1"] THEN
  GCP1AUX_UNDISCH_EQ "pair_CASE" THEN
  GCP1AUX_SPLITN_TAC "word_gen_gc_move" ["w2";"i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
  GCP1AUX_SPLITN_TAC "word_gen_gc_move_roots" ["ws3";"i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  GCP1AUX_SUBST_VARS_TAC ["w";"i1";"pa1";"ib1";"pb1";"m1";"c1"] THEN
  SUBGOAL_THEN `gc_state_ok (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` ASSUME_TAC THENL
   [MATCH_MP_TAC gen_gc_gc_move_list_ok THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`;
    `s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; `h:(A word_loc)heap_address`; `y2:(A word_loc)heap_address`; `s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `conf:data_to_word_config`; `curr:A word`; `pa:A word`; `xs:(A word_loc)list`;
    `frame:(A word#A word_loc->bool)->bool`; `m:A word->A word_loc`; `dm:A word->bool`;
    `w2:A word_loc`; `i2:A word`; `pa2:A word`; `ib2:A word`; `pb2:A word`;
    `m2:A word->A word_loc`; `c2:bool`] word_gen_gc_move_thm) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs2:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:((A word_loc)heap_address)list`; `s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `y3:((A word_loc)heap_address)list`; `s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`]
    gc_move_list_with_NIL_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` (X_CHOOSE_THEN `e1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` STRIP_ASSUME_TAC)) THEN
  GCP1AUX_SUBST_LVARS_TAC ["w2";"i2";"ib2";"pb2"] THEN
  SUBGOAL_THEN `(word_heap curr (gc_state_heap (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) conf STAR misc_word_list (pa2:A word) xs2 STAR
     (word_heap (pa:A word) (gc_state_h2 s2) conf STAR
      word_heap (word_add pa2 (word_mul bytes_in_word (word (gc_state_n s2)))) (gc_state_r4 s2) conf STAR
      (frame:(A word#A word_loc->bool)->bool)))
     (fun2set ((m2:A word->A word_loc),(dm:A word->bool)))` ASSUME_TAC THENL
   [GCP1AUX_SEP_AC_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o ISPECL [`xs2:(A word_loc)list`; `y3:((A word_loc)heap_address)list`;
    `ws3:(A word_loc)list`;
    `gc_state_h2_fupd (K d1) (gc_state_r4_fupd (K e1) (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))`;
    `gc_state_h2_fupd (K []) (gc_state_r4_fupd (K []) (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))`;
    `pb3:A word`; `pa3:A word`; `pa2:A word`; `m3:A word->A word_loc`; `m2:A word->A word_loc`;
    `ib3:A word`; `i3:A word`;
    `word_heap (pa:A word) (gc_state_h2 (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) conf STAR
     word_heap (word_add (pa2:A word) (word_mul bytes_in_word (word (gc_state_n s2)))) (gc_state_r4 s2) conf STAR
     (frame:(A word#A word_loc->bool)->bool)`;
    `dm:A word->bool`; `curr:A word`; `c3:bool`;
    `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`;
    `conf:data_to_word_config`]) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ALL_APPEND; APPEND; ALL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs1:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `xs1:(A word_loc)list` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `word_add (pb3:A word) (word_mul bytes_in_word (word (heap_length (e1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))) =
                  word_add pa2 (word_mul bytes_in_word (word (gc_state_n (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))))` (LABEL_TAC "pbeq") THENL
     [UNDISCH_TAC `gc_state_n (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = heap_length (d1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) + gc_state_n (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) + heap_length (e1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)` THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `pb3 = word_add (pa3:A word) (word_mul bytes_in_word (word (gc_state_n (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))))` THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `pa3 = word_add (pa2:A word) (word_mul bytes_in_word (word (heap_length (d1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))))` THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    SUBGOAL_THEN `word_add (pa:A word) (word_mul bytes_in_word (word (heap_length (gc_state_h2 (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))))) = pa2`
      (LABEL_TAC "paeq") THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "pbeq" (fun th1 -> REMOVE_THEN "paeq" (fun th2 ->
      REWRITE_TAC[ASSUME `gc_state_h2 (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = APPEND (gc_state_h2 (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) (d1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`;
                  ASSUME `gc_state_r4 (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = APPEND (e1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) (gc_state_r4 (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))`;
                  word_heap_APPEND; th1; th2])) THEN
    GCP1AUX_SEP_AC_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND]) THEN
  ASM_REWRITE_TAC[MAP; heap_length_APPEND; ALL_APPEND] THEN
  CONJ_TAC THENL [GCP1AUX_ARITH_TAC; REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE]);;

(* HOL4 line 1571 (HOL4: Q.prove ... |> SIMP_RULE std_ss [], which drops    *)
(* the unused bound variable w)                                             *)
let word_gen_gc_move_list_thm = prove
 (`!x xs x1 s1 s pb1 pa1 pa m1 m ib1 i1 frame dm curr c1 k k1 gen_conf conf.
     (gen_gc_gc_move_list gen_conf s x = (x1,s1)) /\ gc_state_ok s1 /\
     gc_state_h2 s = [] /\ gc_state_r4 s = [] /\
     heap_length (gc_state_heap s) <= dimword (:A) DIV 2 EXP shift_length conf /\
     (!t r. (gen_gc_conf_isRef gen_conf (t,r) <=> isMutTag t)) /\
     data_to_word_config_len_size conf + 5 <= dimindex (:A) /\
     (word_heap curr (gc_state_heap s) conf STAR misc_word_list pa xs STAR
      misc_word_list k (MAP (word_addr conf) x) STAR frame) (fun2set (m,dm)) /\
     (word_gen_gc_move_list conf
        (k,word (LENGTH x),word (gc_state_a s),pa,
         word (gc_state_a s + gc_state_n s),
         word_add pa (word_mul bytes_in_word (word (gc_state_n s))),curr:A word,m,dm) =
       (k1,i1,pa1,ib1,pb1,m1,c1)) /\
     ALL (is_Ref (gen_gc_conf_isRef gen_conf))
       (APPEND (APPEND (APPEND (gc_state_r4 s) (gc_state_r3 s)) (gc_state_r2 s))
          (gc_state_r1 s)) /\
     LENGTH xs = gc_state_n s /\ good_dimindex (:A) /\ LENGTH x < dimword (:A) ==>
     ?xs1.
       (word_heap curr (gc_state_heap s1) conf STAR
        word_heap pa (gc_state_h2 s1) conf STAR
        word_heap pb1 (gc_state_r4 s1) conf STAR
        misc_word_list pa1 xs1 STAR
        misc_word_list k (MAP (word_addr conf) x1) STAR
        frame) (fun2set (m1,dm)) /\
       heap_length (gc_state_heap s1) = heap_length (gc_state_heap s) /\
       c1 /\ (i1 = word (gc_state_a s1)) /\
       (ib1 = word (gc_state_a s1 + gc_state_n s1)) /\
       gc_state_n s1 = LENGTH xs1 /\
       gc_state_n s =
         heap_length (gc_state_h2 s1) + gc_state_n s1 + heap_length (gc_state_r4 s1) /\
       k1 = word_add k (word_mul (word (LENGTH x)) bytes_in_word) /\
       pa1 = word_add pa (word_mul bytes_in_word (word (heap_length (gc_state_h2 s1)))) /\
       pb1 = word_add pa1 (word_mul bytes_in_word (word (gc_state_n s1))) /\
       ALL (is_Ref (gen_gc_conf_isRef gen_conf))
         (APPEND (APPEND (APPEND (gc_state_r4 s1) (gc_state_r3 s1)) (gc_state_r2 s1))
            (gc_state_r1 s1))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[gen_gc_gc_move_list_def; LENGTH; MAP; PAIR_EQ] THEN
    ONCE_REWRITE_TAC[word_gen_gc_move_list_def] THEN REWRITE_TAC[PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `xs:(A word_loc)list` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[misc_word_list_def; SEP_CLAUSES]) THEN
    ASM_REWRITE_TAC[word_heap_def; misc_word_list_def; SEP_CLAUSES; heap_length_NIL;
                    WORD_MUL_0; WORD_ADD_0; MAP; ADD_CLAUSES];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[gen_gc_gc_move_list_def; MAP; LENGTH] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_gc_move (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list) gen_gc_conf) (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) h` ["y2";"s2"] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_gc_move_list (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list) gen_gc_conf) (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) t` ["y3";"s3"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN GCP1AUX_SUBST_VARS_TAC ["x1";"s1"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[misc_word_list_def]) THEN
  GCP1AUX_SEP_R_TAC THEN
  GCP1AUX_UNDISCH_EQ "word_gen_gc_move_list" THEN
  ONCE_REWRITE_TAC[word_gen_gc_move_list_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP GCP1AUX_word_SUC_NEQ_0 th;
                                    GCP1AUX_word_SUC_SUB_1]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  FIRST_ASSUM(fun th -> if concl th = `(m:A word->A word_loc) k = word_addr conf (h:(A word_loc)heap_address)`
                        then REWRITE_TAC[th] else NO_TAC) THEN
  GCP1AUX_SPLITN_TAC "word_gen_gc_move" ["w2";"i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
  GCP1AUX_SPLITN_TAC "word_gen_gc_move_list" ["k3";"i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  GCP1AUX_SUBST_VARS_TAC ["k1";"i1";"pa1";"ib1";"pb1";"m1";"c1"] THEN
  SUBGOAL_THEN `gc_state_ok (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` ASSUME_TAC THENL
   [MATCH_MP_TAC gen_gc_gc_move_list_ok THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`;
    `s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; `h:(A word_loc)heap_address`; `y2:(A word_loc)heap_address`; `s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `conf:data_to_word_config`; `curr:A word`; `pa:A word`; `xs:(A word_loc)list`;
    `(set_sep_one ((k:A word),word_addr conf (h:(A word_loc)heap_address)) STAR
      misc_word_list (word_add k bytes_in_word) (MAP (word_addr conf) (t:((A word_loc)heap_address)list))) STAR
      (frame:(A word#A word_loc->bool)->bool)`;
    `m:A word->A word_loc`; `dm:A word->bool`;
    `w2:A word_loc`; `i2:A word`; `pa2:A word`; `ib2:A word`; `pb2:A word`;
    `m2:A word->A word_loc`; `c2:bool`] word_gen_gc_move_thm) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [GCP1AUX_SEP_AC_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs2:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  GCP1AUX_SUBST_LVARS_TAC ["w2";"i2";"ib2";"pb2"] THEN
  FIRST_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) &&
                           free_in `m2:A word->A word_loc` (concl th)
                        then ASSUME_TAC (GCP1AUX_SEP_WRITE `k:A word`
                               `word_addr conf (y2:(A word_loc)heap_address)` th)
                        else failwith "") THEN
  MP_TAC(ISPECL [`t:((A word_loc)heap_address)list`; `s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `y3:((A word_loc)heap_address)list`; `s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`]
    gc_move_list_with_NIL_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` (X_CHOOSE_THEN `e1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(word_heap curr (gc_state_heap (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) conf STAR misc_word_list (pa2:A word) xs2 STAR
     misc_word_list (word_add (k:A word) bytes_in_word) (MAP (word_addr conf) (t:((A word_loc)heap_address)list)) STAR
     (word_heap (pa:A word) (gc_state_h2 s2) conf STAR
      word_heap (word_add pa2 (word_mul bytes_in_word (word (gc_state_n s2)))) (gc_state_r4 s2) conf STAR
      set_sep_one (k,word_addr conf (y2:(A word_loc)heap_address)) STAR
      (frame:(A word#A word_loc->bool)->bool)))
     (fun2set (((k =+ word_addr conf y2) (m2:A word->A word_loc)),(dm:A word->bool)))` ASSUME_TAC THENL
   [GCP1AUX_SEP_AC_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (t:((A word_loc)heap_address)list) < dimword (:A)` ASSUME_TAC THENL
   [UNDISCH_TAC `SUC (LENGTH (t:((A word_loc)heap_address)list)) < dimword (:A)` THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o ISPECL [`xs2:(A word_loc)list`; `y3:((A word_loc)heap_address)list`;
    `gc_state_h2_fupd (K d1) (gc_state_r4_fupd (K e1) (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))`;
    `gc_state_h2_fupd (K []) (gc_state_r4_fupd (K []) (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))`;
    `pb3:A word`; `pa3:A word`; `pa2:A word`; `m3:A word->A word_loc`;
    `((k:A word) =+ word_addr conf (y2:(A word_loc)heap_address)) (m2:A word->A word_loc)`;
    `ib3:A word`; `i3:A word`;
    `word_heap (pa:A word) (gc_state_h2 (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) conf STAR
     word_heap (word_add (pa2:A word) (word_mul bytes_in_word (word (gc_state_n s2)))) (gc_state_r4 s2) conf STAR
     set_sep_one ((k:A word),word_addr conf (y2:(A word_loc)heap_address)) STAR
     (frame:(A word#A word_loc->bool)->bool)`;
    `dm:A word->bool`; `curr:A word`; `c3:bool`;
    `word_add (k:A word) bytes_in_word`; `k3:A word`;
    `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`;
    `conf:data_to_word_config`]) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ALL_APPEND; APPEND; ALL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs1:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `xs1:(A word_loc)list` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `word_add (pb3:A word) (word_mul bytes_in_word (word (heap_length (e1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))) =
                  word_add pa2 (word_mul bytes_in_word (word (gc_state_n (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))))` (LABEL_TAC "pbeq") THENL
     [UNDISCH_TAC `gc_state_n (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = heap_length (d1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) + gc_state_n (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) + heap_length (e1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)` THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `pb3 = word_add (pa3:A word) (word_mul bytes_in_word (word (gc_state_n (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))))` THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `pa3 = word_add (pa2:A word) (word_mul bytes_in_word (word (heap_length (d1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))))` THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    SUBGOAL_THEN `word_add (pa:A word) (word_mul bytes_in_word (word (heap_length (gc_state_h2 (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))))) = pa2`
      (LABEL_TAC "paeq") THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "pbeq" (fun th1 -> REMOVE_THEN "paeq" (fun th2 ->
      REWRITE_TAC[ASSUME `gc_state_h2 (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = APPEND (gc_state_h2 (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) (d1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`;
                  ASSUME `gc_state_r4 (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = APPEND (e1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) (gc_state_r4 (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))`;
                  word_heap_APPEND; MAP; misc_word_list_def; th1; th2])) THEN
    GCP1AUX_SEP_AC_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND]) THEN
  ASM_REWRITE_TAC[MAP; heap_length_APPEND; ALL_APPEND] THEN
  CONJ_TAC THENL [GCP1AUX_ARITH_TAC; REWRITE_TAC[WORD_ADD; ADD1] THEN CONV_TAC WORD_RULE]);;

(* HOL4 line 1633 *)
let word_heap_parts_def = cake_def
  `word_heap_parts conf (p:A word)
     (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) xs =
     word_heap p (APPEND (gc_state_h1 s) (gc_state_h2 s)) conf STAR
     misc_word_list
       (word_add p (word_mul bytes_in_word
          (word (heap_length (APPEND (gc_state_h1 s) (gc_state_h2 s)))))) xs STAR
     word_heap
       (word_add p (word_mul bytes_in_word
          (word (heap_length (APPEND (gc_state_h1 s) (gc_state_h2 s)) + LENGTH xs))))
       (APPEND (APPEND (APPEND (gc_state_r4 s) (gc_state_r3 s)) (gc_state_r2 s))
          (gc_state_r1 s)) conf`;;

(* HOL4 line 1641 *)
let gc_move_const = prove
 (`!l (s:(A,B)gc_state) xs' s' gen_conf.
     gen_gc_gc_move gen_conf s l = (xs',s') ==>
     gc_state_h1 s' = gc_state_h1 s /\ gc_state_r1 s' = gc_state_r1 s /\
     gc_state_r2 s' = gc_state_r2 s /\ gc_state_r3 s' = gc_state_r3 s`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP gen_gc_gc_move_IMP) THEN
  SIMP_TAC[]);;

(* HOL4 line 1654 *)
let gc_move_list_const = prove
 (`!l (s:(A,B)gc_state) xs' s' gen_conf.
     gen_gc_gc_move_list gen_conf s l = (xs',s') ==>
     gc_state_h1 s' = gc_state_h1 s /\ gc_state_r1 s' = gc_state_r1 s /\
     gc_state_r2 s' = gc_state_r2 s /\ gc_state_r3 s' = gc_state_r3 s`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP gen_gc_gc_move_list_IMP) THEN
  SIMP_TAC[]);;

(* HOL4 line 1665 *)
let gc_move_data_const = prove
 (`!gen_conf (s:(A,B)gc_state) s'.
     gen_gc_gc_move_data gen_conf s = s' ==>
     gc_state_r1 s' = gc_state_r1 s /\ gc_state_r2 s' = gc_state_r2 s /\
     gc_state_r3 s' = gc_state_r3 s`,
  SUBGOAL_THEN
   `!(conf:B gen_gc_conf) (state:(A,B)gc_state).
      gc_state_r1 (gen_gc_gc_move_data conf state) = gc_state_r1 state /\
      gc_state_r2 (gen_gc_gc_move_data conf state) = gc_state_r2 state /\
      gc_state_r3 (gen_gc_gc_move_data conf state) = gc_state_r3 state`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC gen_gc_gc_move_data_ind THEN
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN
  ONCE_REWRITE_TAC[gen_gc_gc_move_data_def] THEN
  GC2AUX_LIST_CASES_TAC `gc_state_h2 (state:(A,B)gc_state)` ALL_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  GC2AUX_ELEMENT_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  USE_THEN "IH" (MP_TAC o SPECL [`t:((A,B)heap_element)list`; `zs:(A heap_address)list`;
    `xs':(A heap_address)list`; `l:num`; `d:B`; `state':(A,B)gc_state`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP gen_gc_gc_move_list_IMP) THEN SIMP_TAC[]);;

(* HOL4 line 1684 *)
let gc_move_refs_const = prove
 (`!gen_conf (s:(A,B)gc_state) s'.
     gc_move_refs gen_conf s = s' ==> gc_state_h1 s' = gc_state_h1 s`,
  SUBGOAL_THEN
   `!(conf:B gen_gc_conf) (state:(A,B)gc_state).
      gc_state_h1 (gc_move_refs conf state) = gc_state_h1 state`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC gc_move_refs_ind THEN
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN
  ONCE_REWRITE_TAC[gc_move_refs_def] THEN
  GC2AUX_LIST_CASES_TAC `gc_state_r2 (state:(A,B)gc_state)`
    (REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
  GC2AUX_ELEMENT_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  USE_THEN "IH" (MP_TAC o SPECL [`zs:(A heap_address)list`; `xs':(A heap_address)list`;
    `l:num`; `d:B`; `t:((A,B)heap_element)list`; `state':(A,B)gc_state`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP gen_gc_gc_move_list_IMP) THEN SIMP_TAC[]);;
let GCP1AUX_fwd_ptr_facts = prove
 (`!n (heap:((A,B)heap_element)list) a (d:A) c x y.
     gc_forward_ptr n heap a d c = (x,y) ==>
     heap_length x = heap_length heap /\ (y ==> c)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[SYM(MATCH_MP gc_forward_ptr_heap_length th)]);
    DISCH_TAC THEN UNDISCH_TAC `gc_forward_ptr n (heap:((A,B)heap_element)list) a (d:A) c = (x,y)` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[gc_shared_gc_forward_ptr_ok]]);;

(* HOL4 line 1702 *)
let heap_length_gc_forward_ptr = prove
 (`!(hs:((A,B)heap_element)list) n k a ok heap.
     gc_forward_ptr n hs k a ok = (heap,T) ==>
     heap_length heap = heap_length hs /\ ok`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP GCP1AUX_fwd_ptr_facts) THEN
  SIMP_TAC[]);;

let GCP1AUX_FWD_PTR_FACTS_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_eq (concl th) && gcp1_is_app "gc_forward_ptr" (lhs (concl th))
    then STRIP_ASSUME_TAC (MATCH_MP GCP1AUX_fwd_ptr_facts th)
    else failwith "GCP1AUX_FWD_PTR_FACTS_TAC"));;

(* HOL4 line 1723 *)
let data_to_word_gcProof_gc_move_thm = prove
 (`!l (s:(A,B)gc_state) l1 s1 gen_conf.
     gen_gc_gc_move gen_conf s l = (l1,s1) /\ gc_state_ok s1 /\ len_inv s ==>
     len_inv s1`,
  GEN_TAC THEN CASES_ON `l:A heap_address` THEN
  REWRITE_TAC[gen_gc_gc_move_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  SIMP[] THEN EVERY_CASE_TAC THEN REPEAT PAIRARG_TAC THEN RW[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[len_inv_def; gc_state_FIELDS.ri_accfupds; K_THM] THEN
  GCP1AUX_FWD_PTR_FACTS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[len_inv_def]) THEN
  GCP1AUX_MP_ASM_TAC THEN
  ASM_REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def;
                  heap_length_NIL] THEN
  GCP1AUX_ARITH_TAC);;

(* HOL4 line 1739 *)
let data_to_word_gcProof_gc_move_list_thm = prove
 (`!l (s:(A,B)gc_state) l1 s1 gen_conf.
     gen_gc_gc_move_list gen_conf s l = (l1,s1) /\ gc_state_ok s1 /\ len_inv s ==>
     len_inv s1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_gc_move_list_def; PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  GCP1AUX_TUPLE_TAC `gen_gc_gc_move (gen_conf:B gen_gc_conf) (s:(A,B)gc_state) h` ["z1";"s2"] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_gc_move_list (gen_conf:B gen_gc_conf) (s2:(A,B)gc_state) t` ["zs1";"u1"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `gc_state_ok (s2:(A,B)gc_state)` ASSUME_TAC THENL
   [MATCH_MP_TAC gen_gc_gc_move_list_ok THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `len_inv (s2:(A,B)gc_state)` ASSUME_TAC THENL
   [MATCH_MP_TAC data_to_word_gcProof_gc_move_thm THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;
let GCP1AUX_sep_one_one = prove
 (`!(a:A) (x:B) y p m dm.
     ~((set_sep_one (a,x) STAR set_sep_one (a,y) STAR p) (fun2set (m,dm)))`,
  REWRITE_TAC[GSYM STAR_ASSOC; one_fun2set; IN_DELETE]);;

let GCP1AUX_word_dimword_bw = prove
 (`good_dimindex (:A) ==>
   word_mul (word (dimword (:A) DIV (dimindex (:A) DIV 8))) bytes_in_word = word 0:A word`,
  REWRITE_TAC[good_dimindex_def; bytes_in_word_def; GSYM WORD_MUL; dimword_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_EQ; CONG] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 1753 *)
let word_list_IMP_limit = prove
 (`!(curr:A word) (hs:B list) frame m dm.
     (misc_word_list curr hs STAR frame) (fun2set (m,dm)) /\
     good_dimindex (:A) ==>
     LENGTH hs <= dimword (:A) DIV (dimindex (:A) DIV 8)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `N = dimword (:A) DIV (dimindex (:A) DIV 8)` THEN
  SUBGOAL_THEN `0 < N` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN UNDISCH_TAC `good_dimindex (:A)` THEN
    REWRITE_TAC[good_dimindex_def; dimword_def] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`N:num`; `hs:B list`] LESS_EQ_IMP_APPEND) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ys1:B list` (X_CHOOSE_THEN `ys2:B list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp1_is_fun2set_asm o concl)) THEN
  REWRITE_TAC[data_to_word_memoryProof_word_list_APPEND] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC GCP1AUX_word_dimword_bw THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[WORD_ADD_0] THEN
  MP_TAC(ISPEC `ys1:B list` list_CASES) THEN MP_TAC(ISPEC `ys2:B list` list_CASES) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; LENGTH_APPEND; APPEND_NIL; LT_REFL]) THEN
  TRY(GCP1AUX_ARITH_TAC) THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (gcp1_is_fun2set_asm o concl)) THEN
  REWRITE_TAC[misc_word_list_def] THEN
  DISCH_THEN(fun th -> MP_TAC(GCP1AUX_STAR_FRONT
    [`set_sep_one ((curr:A word),(h':B))`; `set_sep_one ((curr:A word),(h:B))`] th)) THEN
  REWRITE_TAC[GCP1AUX_sep_one_one]);;

(* HOL4 line 1775 *)
let word_el_eq_word_list = prove
 (`!hs (curr:A word) frame conf (m:A word->B word_loc) dm.
     (word_el curr hs conf STAR frame) (fun2set (m,dm)) ==>
     ?xs. (misc_word_list curr xs STAR frame) (fun2set (m,dm)) /\
          el_length hs = LENGTH xs /\
          !frame1 (curr1:A word) m1.
            (misc_word_list curr1 xs STAR frame1) (fun2set (m1,dm)) ==>
            (word_el curr1 hs conf STAR frame1) (fun2set (m1,dm))`,
  GEN_TAC THEN
  MP_TAC(ISPEC `hs:(B word_loc,data_to_word_memoryProof_tag#(B word_loc)list)heap_element` (cases "heap_element")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[word_el_def; el_length_def] THENL
   [(REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_list_exists_def]) THEN
  GCP1AUX_SEP_EXISTS_TAC THEN GCP1AUX_SEP_COND_TAC THEN
  FIRST_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) then
    EXISTS_TAC (rand(hd(gcp1_star_leaves(rator(concl th))))) else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC GCP1AUX_word_list_exists_intro THEN
  EXISTS_TAC `xs:(B word_loc)list` THEN ASM_REWRITE_TAC[]);
    (REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[word_list_exists_def]) THEN
  GCP1AUX_SEP_EXISTS_TAC THEN GCP1AUX_SEP_COND_TAC THEN
  EXISTS_TAC `CONS (wl_Word (word_shl (word a0) 2):B word_loc) (xs:(B word_loc)list)` THEN
  ASM_REWRITE_TAC[misc_word_list_def; LENGTH; ADD1] THEN CONJ_TAC THENL
   [GCP1AUX_SEP_AC_TAC;
    REPEAT STRIP_TAC THEN GCP1AUX_WLE_INTRO_TAC `xs:(B word_loc)list` THEN
    ASM_REWRITE_TAC[] THEN GCP1AUX_SEP_AC_TAC]);
    (MP_TAC(ISPEC `a2:data_to_word_memoryProof_tag#(B word_loc)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tag:data_to_word_memoryProof_tag`
    (X_CHOOSE_THEN `qs:(B word_loc)list` SUBST_ALL_TAC)) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[word_el_def] THEN
  GCP1AUX_TUPLE_TAC `word_payload (a0:((B word_loc)heap_address)list) a1 tag qs conf:B word#(B word_loc)list#bool`
    ["h";"ts";"c"] THEN
  STRIP_TAC THEN GCP1AUX_SEP_COND_TAC THEN
  SUBGOAL_THEN `LENGTH (ts:(B word_loc)list) = a1` ASSUME_TAC THENL
   [MATCH_MP_TAC word_payload_IMP THEN
    MAP_EVERY EXISTS_TAC [`a0:((B word_loc)heap_address)list`; `tag:data_to_word_memoryProof_tag`;
      `qs:(B word_loc)list`; `conf:data_to_word_config`; `h:B word`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `CONS (wl_Word h:B word_loc) ts` THEN
  ASM_REWRITE_TAC[LENGTH; ADD1] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[SEP_CLAUSES])]);;

(* HOL4 line 1797 *)
let word_heap_eq_word_list_strong = prove
 (`!(hs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
    (curr:A word) frame conf m dm.
     (word_heap curr hs conf STAR frame) (fun2set (m,dm)) ==>
     ?xs. (misc_word_list curr xs STAR frame) (fun2set (m,dm)) /\
          heap_length hs = LENGTH xs /\
          !curr1 frame1 m1.
            (misc_word_list curr1 xs STAR frame1) (fun2set (m1,dm)) ==>
            (word_heap curr1 hs conf STAR frame1) (fun2set (m1,dm))`,
  LIST_INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `[]:(A word_loc)list` THEN
    ASM_REWRITE_TAC[misc_word_list_def; word_heap_def; heap_length_NIL; LENGTH] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[word_heap_def]) THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[word_heap_def] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element`;
    `curr:A word`;
    `word_heap (word_add curr (word_mul bytes_in_word (word (el_length
       (h:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)))))
       (t:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) conf STAR
     (frame:(A word#A word_loc->bool)->bool)`;
    `conf:data_to_word_config`; `m:A word->A word_loc`; `dm:A word->bool`] word_el_eq_word_list) THEN
  ANTS_TAC THENL [GCP1AUX_SEP_AC_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs1:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`word_add curr (word_mul bytes_in_word (word (el_length
       (h:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)))):A word`;
    `misc_word_list (curr:A word) (xs1:(A word_loc)list) STAR (frame:(A word#A word_loc->bool)->bool)`;
    `conf:data_to_word_config`; `m:A word->A word_loc`; `dm:A word->bool`]) THEN
  ANTS_TAC THENL [GCP1AUX_SEP_AC_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs2:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `APPEND xs1 xs2:(A word_loc)list` THEN
  REWRITE_TAC[data_to_word_memoryProof_word_list_APPEND; GC1AUX_heap_length_CONS;
              LENGTH_APPEND] THEN
  SUBGOAL_THEN `word_mul (word (LENGTH (xs1:(A word_loc)list))) bytes_in_word =
                word_mul bytes_in_word (word (el_length
                  (h:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element))):A word`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN MATCH_ACCEPT_TAC WORD_MUL_SYM; ALL_TAC] THEN
  CONJ_TAC THENL [GCP1AUX_SEP_AC_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`word_add curr1 (word_mul bytes_in_word (word (el_length
       (h:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)))):A word`;
    `misc_word_list (curr1:A word) (xs1:(A word_loc)list) STAR (frame1:(A word#A word_loc->bool)->bool)`;
    `m1:A word->A word_loc`]) THEN
  ANTS_TAC THENL [GCP1AUX_SEP_AC_TAC; ALL_TAC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`word_heap (word_add curr1 (word_mul bytes_in_word (word (el_length
       (h:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)))))
       (t:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) conf STAR
     (frame1:(A word#A word_loc->bool)->bool)`; `curr1:A word`; `m1:A word->A word_loc`]) THEN
  ANTS_TAC THENL [GCP1AUX_SEP_AC_TAC; ALL_TAC] THEN DISCH_TAC THEN GCP1AUX_SEP_AC_TAC);;

(* HOL4 line 1821 *)
let word_heap_eq_word_list = prove
 (`!(hs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
    (curr:A word) frame conf m dm.
     (word_heap curr hs conf STAR frame) (fun2set (m,dm)) ==>
     ?xs. (misc_word_list curr xs STAR frame) (fun2set (m,dm)) /\
          heap_length hs = LENGTH xs`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP word_heap_eq_word_list_strong) THEN
  MESON_TAC[]);;

(* HOL4 line 1830 *)
let word_heap_IMP_limit = prove
 (`!(curr:A word)
    (hs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
    conf frame m dm.
     (word_heap curr hs conf STAR frame) (fun2set (m,dm)) /\
     good_dimindex (:A) ==>
     heap_length hs <= dimword (:A) DIV (dimindex (:A) DIV 8)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP word_heap_eq_word_list) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC word_list_IMP_limit THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 1840 *)
let muttag_header_def = cake_def
  `(muttag_header (ThunkTag e) =
      word_or (word_shl (thunk_tag_to_bits e) 3) (word 6):A word) /\
   (muttag_header _ = word 2)`;;

(* HOL4 line 1845 *)
let isMutTag_word_payload_IMP = prove
 (`!x1 x2 x3 ys l t qs conf.
     word_payload ys l t qs conf = (x1,x2,x3) /\
     isMutTag t ==>
     x1 = make_header conf (muttag_header t) (LENGTH ys):A word /\
     x2 = MAP (word_addr conf) ys /\
     x3 = (qs = [] /\ LENGTH ys = l /\ (~(t = RefTag) ==> l = 1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[isMutTag_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_payload_def; PAIR_EQ]) THEN
  FIRST_X_ASSUM STRIP_ASSUME_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[muttag_header_def; distinctness "data_to_word_memoryProof_tag"] THEN
  MESON_TAC[]);;
(* ------------------------------------------------------------------------- *)
(* Address normalisation for the generational GC proofs: every address      *)
(* base + bytes_in_word * word N is collapsed into one product and N is     *)
(* normalised (NUM_NORMALIZE_CONV), so equal addresses become syntactically *)
(* equal                                                                     *)
(* ------------------------------------------------------------------------- *)

let GCP1AUX_bw_comm = prove
 (`!a. word_mul (word a) bytes_in_word = word_mul bytes_in_word (word a):A word`,
  REWRITE_TAC[WORD_MUL_SYM]);;

let GCP1AUX_bw_add2 = prove
 (`!(x:A word) a b.
     word_add (word_add x (word_mul bytes_in_word (word a))) (word_mul bytes_in_word (word b)) =
     word_add x (word_mul bytes_in_word (word (a + b)))`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let GCP1AUX_bw_add1 = prove
 (`!(x:A word) a.
     word_add (word_add x (word_mul bytes_in_word (word a))) bytes_in_word =
     word_add x (word_mul bytes_in_word (word (a + 1)))`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let GCP1AUX_bw_add0 = prove
 (`!(x:A word). word_add x (word_mul bytes_in_word (word 0)) = x`,
  REWRITE_TAC[WORD_MUL_0; WORD_ADD_0]);;

let GCP1AUX_ADDR_NUM_CONV : conv = fun t ->
  match t with
    Comb(Comb(Const("word_mul",_),b),Comb(Const("word",_),n))
      when (match b with Const("bytes_in_word",_) -> true | _ -> false) ->
      RAND_CONV (RAND_CONV NUM_NORMALIZE_CONV) t
  | _ -> failwith "GCP1AUX_ADDR_NUM_CONV";;

let GCP1AUX_ADDR_NORM_CONV : conv =
  REWRITE_CONV[GCP1AUX_bw_comm; GCP1AUX_bw_add2; GCP1AUX_bw_add1; GCP1AUX_bw_add0] THENC
  ONCE_DEPTH_CONV GCP1AUX_ADDR_NUM_CONV;;

let GCP1AUX_ADDR_NORM_TAC : tactic = CONV_TAC GCP1AUX_ADDR_NORM_CONV;;

let GCP1AUX_new_addr_ne2 = prove
 (`!(new:A word) k1 k2.
     good_dimindex (:A) /\ k1 < k2 /\ k2 * (dimindex (:A) DIV 8) < dimword (:A) ==>
     ~(word_add new (word_mul bytes_in_word (word k1)) =
       word_add new (word_mul bytes_in_word (word k2)))`,
  ONCE_REWRITE_TAC[WORD_MUL_SYM] THEN REWRITE_TAC[GCP1AUX_new_addr_ne]);;

(* heap lengths expanded, then addresses normalised *)
let GCP1AUX_NORM_CONV : conv =
  REWRITE_CONV[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def; heap_length_NIL] THENC
  GCP1AUX_ADDR_NORM_CONV;;

(* split  word_heap a (APPEND xs ys) conf  only for the given xs *)
let GCP1AUX_HEAP_SPLIT_AT (xs:term) : conv = fun t ->
  match t with
    Comb(Comb(Comb(Const("word_heap",_),a),Comb(Comb(Const("APPEND",_),l1),l2)),c)
      when aconv l1 xs ->
      REWR_CONV (ISPECL [c; l1; l2; a] word_heap_APPEND) t
  | _ -> failwith "GCP1AUX_HEAP_SPLIT_AT";;

(* split the first  word_heap a (APPEND ha (CONS (DataElement ys l (tag,qs)) hb)) c  *)
(* of the goal into header, payload and rest, using the assumption               *)
(* word_payload ys l tag qs conf = (h,ts,T) and the facts on ts                   *)
let GCP1AUX_DE_SPLIT_TAC : tactic = fun (asl,w as g) ->
  let is_de_heap t =
    match t with
      Comb(Comb(Comb(Const("word_heap",_),_),Comb(Comb(Const("APPEND",_),_),
           Comb(Comb(Const("CONS",_),Comb(Comb(Comb(Const("DataElement",_),_),_),
             Comb(Comb(Const(",",_),_),_))),_))),_) -> true
    | _ -> false in
  let t = find_term is_de_heap w in
  let wh,c = dest_comb t in
  let wh1,lst = dest_comb wh in
  let a = rand wh1 in
  let ha = lhand lst and cons = rand lst in
  let elt = lhand cons and hb = rand cons in
  let de1,tq = dest_comb elt in
  let de2,l = dest_comb de1 in
  let ys = rand de2 in
  let tag,qs = dest_pair tq in
  let pth = snd(find (fun (_,th) -> let cc = concl th in is_eq cc &&
              (let lh = lhs cc in gcp1_is_app "word_payload" lh &&
               (let args = snd(strip_comb lh) in
                aconv (el 0 args) ys && aconv (el 1 args) l))) asl) in
  let h,tsc = dest_pair (rhs (concl pth)) in
  let ts = fst(dest_pair tsc) in
  let th = ISPECL [c; a; ha; ys; l; tag; qs; hb; h; ts] GCP1AUX_word_heap_DE_split in
  (MP_TAC th THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[LENGTH_MAP];
     DISCH_THEN(fun eq -> GEN_REWRITE_TAC ONCE_DEPTH_CONV [eq])]) g;;

(* GCP1AUX_NORM_CONV after collapsing sums of word numerals *)
let GCP1AUX_NORM2_CONV : conv = REWRITE_CONV[GSYM WORD_ADD] THENC GCP1AUX_NORM_CONV;;

(* HOL4 line 1857 *)
let word_gen_gc_move_refs_thm = prove
 (`!k s m dm (curr:A word) xs s1 pb1 pa1 m1 ib1 i1 frame c1 p1 gen_conf conf p.
     (gc_move_refs gen_conf s = s1) /\ gc_state_ok s1 /\
     heap_length (gc_state_heap s) <= dimword (:A) DIV 2 EXP shift_length conf /\
     heap_length (gc_state_heap s) * (dimindex (:A) DIV 8) < dimword (:A) /\
     (!t r. (gen_gc_conf_isRef gen_conf (t,r) <=> isMutTag t)) /\
     data_to_word_config_len_size conf + 5 <= dimindex (:A) /\
     (word_gen_gc_move_refs conf k
        (word_add p (word_mul bytes_in_word
           (word (heap_length (APPEND (APPEND (APPEND (gc_state_h1 s) (gc_state_h2 s))
                                 (gc_state_r4 s)) (gc_state_r3 s)) + LENGTH xs))),
         word_add p (word_mul bytes_in_word
           (word (heap_length (APPEND (APPEND (APPEND (APPEND (gc_state_h1 s)
                    (gc_state_h2 s)) (gc_state_r4 s)) (gc_state_r3 s)) (gc_state_r2 s)) +
                  LENGTH xs))),
         word (gc_state_a s),
         word_add p (word_mul bytes_in_word
           (word (heap_length (APPEND (gc_state_h1 s) (gc_state_h2 s))))),
         word (gc_state_a s + gc_state_n s),
         word_add p (word_mul bytes_in_word
           (word (heap_length (APPEND (gc_state_h1 s) (gc_state_h2 s)) + gc_state_n s))),
         curr,m,dm) =
       (p1,i1,pa1,ib1,pb1,m1,c1)) /\
     LENGTH (gc_state_r2 s) <= k /\ len_inv s /\
     (word_heap curr (gc_state_heap s) conf STAR
      word_heap_parts conf p s xs STAR
      frame) (fun2set (m,dm)) /\
     ALL (is_Ref (gen_gc_conf_isRef gen_conf))
       (APPEND (APPEND (APPEND (gc_state_r4 s) (gc_state_r3 s)) (gc_state_r2 s))
          (gc_state_r1 s)) /\
     LENGTH xs = gc_state_n s /\ good_dimindex (:A) ==>
     ?xs1.
       (word_heap curr (gc_state_heap s1) conf STAR
        word_heap_parts conf p s1 xs1 STAR
        frame) (fun2set (m1,dm)) /\ gc_state_r3 s1 = [] /\ gc_state_r2 s1 = [] /\
       heap_length (gc_state_heap s1) = heap_length (gc_state_heap s) /\
       c1 /\ (i1 = word (gc_state_a s1)) /\
       (ib1 = word (gc_state_a s1 + gc_state_n s1)) /\ gc_state_n s1 = LENGTH xs1 /\
       heap_length (gc_state_h2 s) + gc_state_n s + heap_length (gc_state_r4 s) =
       heap_length (gc_state_h2 s1) + gc_state_n s1 + heap_length (gc_state_r4 s1) /\
       pa1 = word_add p (word_mul bytes_in_word
               (word (heap_length (APPEND (gc_state_h1 s1) (gc_state_h2 s1))))) /\
       pb1 = word_add p (word_mul bytes_in_word
               (word (heap_length (APPEND (gc_state_h1 s1) (gc_state_h2 s1)) +
                      gc_state_n s1))) /\
       p1 = word_add p (word_mul bytes_in_word
              (word (heap_length (APPEND (APPEND (APPEND (APPEND (gc_state_h1 s)
                       (gc_state_h2 s)) (gc_state_r4 s)) (gc_state_r3 s)) (gc_state_r2 s)) +
                     LENGTH xs))) /\
       len_inv s1 /\
       ALL (is_Ref (gen_gc_conf_isRef gen_conf))
         (APPEND (APPEND (APPEND (gc_state_r4 s1) (gc_state_r3 s1)) (gc_state_r2 s1))
            (gc_state_r1 s1))`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `k:num` THEN DISCH_THEN(LABEL_TAC "IH") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GCP1AUX_UNDISCH_EQ "gc_move_refs" THEN ONCE_REWRITE_TAC[gc_move_refs_def] THEN
  MP_TAC(ISPEC `gc_state_r2 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th] THEN CASE_REWRITE_TAC[])
    (X_CHOOSE_THEN `rf:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element` (X_CHOOSE_THEN `r2t:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
       (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th] THEN CASE_REWRITE_TAC[])))) THENL
   [DISCH_TAC THEN GCP1AUX_SUBST_VARS_TAC ["s1"] THEN
    REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM; word_heap_parts_def; len_inv_def] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[word_heap_parts_def; len_inv_def]) THEN
    FIRST_X_ASSUM(fun th -> if concl th = `gc_state_r2 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = []` then SUBST_ALL_TAC th
                            else failwith "") THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL]) THEN
    GCP1AUX_UNDISCH_EQ "word_gen_gc_move_refs" THEN ONCE_REWRITE_TAC[word_gen_gc_move_refs_def] THEN
    REWRITE_TAC[APPEND_NIL; PAIR_EQ] THEN STRIP_TAC THEN
    GCP1AUX_SUBST_VARS_TAC ["p1";"i1";"pa1";"ib1";"pb1";"m1";"c1"] THEN
    EXISTS_TAC `xs:(A word_loc)list` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
    ASM_REWRITE_TAC[APPEND_NIL; GSYM APPEND_ASSOC; APPEND];
    ALL_TAC] THEN
  MP_TAC(ISPEC `rf:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `u:num` SUBST_ALL_TAC)
    (DISJ_CASES_THEN2
      (X_CHOOSE_THEN `pp:num` (X_CHOOSE_THEN `pd:A word_loc`
         (X_CHOOSE_THEN `l:num` SUBST_ALL_TAC)))
      (X_CHOOSE_THEN `ys:((A word_loc)heap_address)list` (X_CHOOSE_THEN `l:num`
         (X_CHOOSE_THEN `tg:data_to_word_memoryProof_tag#(A word_loc)list`
            SUBST_ALL_TAC))))) THEN
  CASE_REWRITE_TAC[] THENL
   [DISCH_TAC THEN GCP1AUX_SUBST_VARS_TAC ["s1"] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN ASM_MESON_TAC[];
    DISCH_TAC THEN GCP1AUX_SUBST_VARS_TAC ["s1"] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `tg:data_to_word_memoryProof_tag#(A word_loc)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tag:data_to_word_memoryProof_tag`
    (X_CHOOSE_THEN `qs:(A word_loc)list` SUBST_ALL_TAC)) THEN
  GCP1AUX_SPLITN_TAC "gen_gc_gc_move_list" ["ys3";"s3"] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN DISCH_TAC THEN
  ABBREV_TAC `s4 = gc_state_r3_fupd (K (APPEND (gc_state_r3 s3)
      [DataElement ys3 l (tag,qs)])) (gc_state_r2_fupd (K r2t) (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))` THEN
  SUBGOAL_THEN `gc_state_h1 (s4:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = gc_state_h1 s3 /\ gc_state_h2 s4 = gc_state_h2 s3 /\
     gc_state_r4 s4 = gc_state_r4 s3 /\
     gc_state_r3 s4 = APPEND (gc_state_r3 s3) [DataElement ys3 l (tag,qs)] /\
     gc_state_r2 s4 = r2t /\ gc_state_r1 s4 = gc_state_r1 s3 /\
     gc_state_heap s4 = gc_state_heap s3 /\ gc_state_a s4 = gc_state_a s3 /\
     gc_state_n s4 = gc_state_n s3 /\ gc_state_ok s4 = gc_state_ok s3` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s4" THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `gc_state_ok (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `gc_state_ok (s4:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = gc_state_ok (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`
                            then SUBST1_TAC (SYM th) else failwith "") THEN
    MATCH_MP_TAC gc_move_refs_ok THEN EXISTS_TAC `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `isMutTag tag` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (is_Ref (gen_gc_conf_isRef (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf)))
       (APPEND (APPEND (APPEND (gc_state_r4 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) (gc_state_r3 s)) (gc_state_r2 s)) (gc_state_r1 s))` THEN
    ASM_REWRITE_TAC[ALL_APPEND; ALL; is_Ref_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `len_inv (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` ASSUME_TAC THENL
   [MATCH_MP_TAC data_to_word_gcProof_gc_move_list_thm THEN
    MAP_EVERY EXISTS_TAC [`ys:((A word_loc)heap_address)list`; `s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
      `ys3:((A word_loc)heap_address)list`;
      `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP gc_move_list_const o
    check (fun th -> gcp1_is_app "gen_gc_gc_move_list" (lhs (concl th)))) THEN
  MP_TAC(ISPECL [`ys:((A word_loc)heap_address)list`; `s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `ys3:((A word_loc)heap_address)list`; `s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`]
    gc_move_list_with_NIL_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` (X_CHOOSE_THEN `e1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `len_inv (s4:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` ASSUME_TAC THENL
   [UNDISCH_TAC `len_inv (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` THEN ASM_REWRITE_TAC[len_inv_def] THEN
    REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def; heap_length_NIL] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  GCP1AUX_UNDISCH_EQ "word_gen_gc_move_refs" THEN ONCE_REWRITE_TAC[word_gen_gc_move_refs_def] THEN
  SUBGOAL_THEN `~(word_add p (word_mul bytes_in_word
           (word (heap_length (APPEND (APPEND (APPEND (gc_state_h1 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) (gc_state_h2 s))
                                 (gc_state_r4 s)) (gc_state_r3 s)) + LENGTH (xs:(A word_loc)list)))) =
                  word_add p (word_mul bytes_in_word
           (word (heap_length (APPEND (APPEND (APPEND (APPEND (gc_state_h1 s)
                    (gc_state_h2 s)) (gc_state_r4 s)) (gc_state_r3 s)) (gc_state_r2 s)) +
                  LENGTH xs))):A word)` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC GCP1AUX_new_addr_ne2 THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `len_inv (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` THEN
    UNDISCH_TAC `heap_length (gc_state_heap (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) * dimindex (:A) DIV 8 < dimword (:A)` THEN
    ASM_REWRITE_TAC[len_inv_def; heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def] THEN
    REPEAT DISCH_TAC THEN CONJ_TAC THENL
     [ARITH_TAC;
      MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `heap_length (gc_state_heap (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) * dimindex (:A) DIV 8` THEN
      ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(k = 0)` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `LENGTH (gc_state_r2 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) <= k` THEN ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `APPEND (APPEND (APPEND (gc_state_r4 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) (gc_state_r3 s)) (gc_state_r2 s))
                  (gc_state_r1 s) =
                APPEND (APPEND (gc_state_r4 s) (gc_state_r3 s))
                  (CONS (DataElement ys l (tag,qs)) (APPEND r2t (gc_state_r1 s)))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) && free_in `xs:(A word_loc)list` (concl th)
    then ASSUME_TAC (REWRITE_RULE[word_heap_parts_def; ASSUME `APPEND (APPEND (APPEND (gc_state_r4 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))
          (gc_state_r3 s)) (gc_state_r2 s)) (gc_state_r1 s) =
        APPEND (APPEND (gc_state_r4 s) (gc_state_r3 s))
          (CONS (DataElement ys l (tag,qs)) (APPEND r2t (gc_state_r1 s)))`] th)
    else failwith "") THEN
  FIRST_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) && free_in `xs:(A word_loc)list` (concl th) then
     let wh = find (fun t -> gcp1_is_app "word_heap" t && free_in `r2t:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` t)
                   (gcp1_star_leaves (rator (concl th))) in
     MP_TAC(MATCH_MP GCP1AUX_heap_el_read (GCP1AUX_STAR_FRONT [wh] th)) else NO_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `hh:A word` (X_CHOOSE_THEN `ts:(A word_loc)list` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(fun pth -> if is_eq (concl pth) && gcp1_is_app "word_payload" (lhs (concl pth)) then
     MP_TAC(MATCH_MP isMutTag_word_payload_IMP (CONJ pth (ASSUME `isMutTag tag`)))
     else failwith "") THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  GCP1AUX_SUBST_LVARS_TAC ["qs";"ts";"hh"] THEN GCP1AUX_SUBST_VARS_TAC ["l"] THEN
  FIRST_X_ASSUM(fun th ->
    if concl th = `LENGTH (xs:(A word_loc)list) = gc_state_n (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`
    then SUBST_ALL_TAC th THEN ASSUME_TAC th else failwith "") THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `gc_state_r2 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`
                          then SUBST_ALL_TAC th THEN ASSUME_TAC th else failwith "") THEN
  FIRST_X_ASSUM(fun th -> let c = concl th in
    if is_eq c && is_comb (lhs c) && rator (lhs c) = `m:A word->A word_loc`
    then ASSUME_TAC (CONV_RULE GCP1AUX_NORM_CONV th)
    else failwith "") THEN
  FIRST_X_ASSUM(fun th -> let c = concl th in
    if gcp1_is_app "IN" c && rand c = `dm:A word->bool`
    then ASSUME_TAC (CONV_RULE GCP1AUX_NORM_CONV th)
    else failwith "") THEN
  CONV_TAC GCP1AUX_NORM_CONV THEN
  ASM_REWRITE_TAC[theWord_def; isWord_def; LET_DEF; LET_END_DEF] THEN
  GCP1AUX_SPLITN_TAC "word_gen_gc_move_list" ["r2a2";"i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
  GCP1AUX_SPLITN_TAC "word_gen_gc_move_refs" ["r2a3";"i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  GCP1AUX_SUBST_VARS_TAC ["p1";"i1";"pa1";"ib1";"pb1";"m1";"c1"] THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`;
    `word_add p (word_mul bytes_in_word (word (gc_state_n (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) + heap_length (gc_state_h1 s) +
       heap_length (gc_state_h2 s)))):A word`;
    `APPEND (gc_state_r4 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) (gc_state_r3 s)`; `ys:((A word_loc)heap_address)list`;
    `LENGTH (ys:((A word_loc)heap_address)list)`; `tag:data_to_word_memoryProof_tag`;
    `[]:(A word_loc)list`; `APPEND r2t (gc_state_r1 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))`;
    `make_header conf (muttag_header tag) (LENGTH (ys:((A word_loc)heap_address)list)):A word`;
    `MAP (word_addr conf) (ys:((A word_loc)heap_address)list)`] GCP1AUX_word_heap_DE_split) THEN
  REWRITE_TAC[LENGTH_MAP] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun dth -> FIRST_X_ASSUM(fun th ->
    if gcp1_is_fun2set_asm (concl th) && free_in `r2t:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` (concl th)
    then ASSUME_TAC (CONV_RULE GCP1AUX_NORM_CONV
           (REWRITE_RULE[dth] (CONV_RULE GCP1AUX_NORM_CONV th)))
    else failwith "")) THEN
  MP_TAC(GEN `fr:(A word#A word_loc->bool)->bool` (CONV_RULE GCP1AUX_NORM_CONV
    (REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM] (ISPECL [
    `ys:((A word_loc)heap_address)list`; `xs:(A word_loc)list`; `ys3:((A word_loc)heap_address)list`;
    `gc_state_h2_fupd (K d1) (gc_state_r4_fupd (K e1) (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))`;
    `gc_state_h2_fupd (K []) (gc_state_r4_fupd (K []) (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))`;
    `pb2:A word`; `pa2:A word`;
    `word_add p (word_mul bytes_in_word (word (heap_length (gc_state_h1 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) +
       heap_length (gc_state_h2 s)))):A word`;
    `m2:A word->A word_loc`; `m:A word->A word_loc`; `ib2:A word`; `i2:A word`;
    `fr:(A word#A word_loc->bool)->bool`; `dm:A word->bool`; `curr:A word`; `c2:bool`;
    `word_add p (word_mul bytes_in_word (word (gc_state_n (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) + heap_length (gc_state_h1 s) +
       heap_length (gc_state_h2 s) + heap_length (gc_state_r3 s) + heap_length (gc_state_r4 s) + 1))):A word`;
    `r2a2:A word`; `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`;
    `conf:data_to_word_config`] word_gen_gc_move_list_thm)))) THEN
  GCP1AUX_SEP_FRAME_TAC THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ALL_APPEND; ALL; APPEND] THEN CONJ_TAC THENL
     [FIRST_ASSUM(fun th -> if gcp1_is_app "ALL" (concl th) then MP_TAC th else failwith "") THEN
      REWRITE_TAC[ALL_APPEND; ALL] THEN MESON_TAC[];
      MP_TAC(SPEC `LENGTH (ys:((A word_loc)heap_address)list)` GCP1AUX_len_bound) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs1:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  GCP1AUX_SUBST_LVARS_TAC ["i2";"ib2";"r2a2";"pb2";"pa2"] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `gc_state_n (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = LENGTH (xs1:(A word_loc)list)`
    then SUBST_ALL_TAC (SYM th) THEN ASSUME_TAC (SYM th) else failwith "") THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `gc_state_n (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` &&
                             free_in `d1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` (rhs (concl th))
    then SUBST_ALL_TAC th THEN ASSUME_TAC th else failwith "") THEN
  MP_TAC(ISPECL [`ys:((A word_loc)heap_address)list`; `tag:data_to_word_memoryProof_tag`;
    `[]:(A word_loc)list`; `conf:data_to_word_config`;
    `make_header conf (muttag_header tag) (LENGTH (ys:((A word_loc)heap_address)list)):A word`;
    `ys3:((A word_loc)heap_address)list`] word_payload_swap) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP gen_gc_gc_move_list_length o
    check (fun th -> concl th = `gen_gc_gc_move_list (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf) (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) ys = (ys3,s3)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) && free_in `m2:A word->A word_loc` (concl th)
    then ASSUME_TAC (CONV_RULE GCP1AUX_NORM_CONV th) else failwith "") THEN
  SUBGOAL_THEN `(word_heap curr (gc_state_heap (s4:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) conf STAR word_heap_parts conf p s4 xs1 STAR
                  (frame:(A word#A word_loc->bool)->bool)) (fun2set ((m2:A word->A word_loc),dm))`
    ASSUME_TAC THENL
   [REWRITE_TAC[word_heap_parts_def] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `APPEND (gc_state_h1 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) (APPEND (gc_state_h2 s) d1) =
                  APPEND (APPEND (gc_state_h1 s) (gc_state_h2 s)) d1` SUBST1_TAC THENL
     [REWRITE_TAC[APPEND_ASSOC]; ALL_TAC] THEN
    SUBGOAL_THEN `APPEND (APPEND (APPEND (APPEND e1 (gc_state_r4 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)))
        (APPEND (gc_state_r3 s) [DataElement ys3 (LENGTH (ys:((A word_loc)heap_address)list)) (tag,[])]))
        r2t) (gc_state_r1 s) =
      APPEND e1 (APPEND (APPEND (gc_state_r4 s) (gc_state_r3 s))
        (CONS (DataElement ys3 (LENGTH ys) (tag,[])) (APPEND r2t (gc_state_r1 s))))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV (GCP1AUX_HEAP_SPLIT_AT `APPEND (gc_state_h1 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) (gc_state_h2 s)`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV (GCP1AUX_HEAP_SPLIT_AT `e1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`)) THEN
    GCP1AUX_DE_SPLIT_TAC THEN
    CONV_TAC GCP1AUX_NORM_CONV THEN
    GCP1AUX_SEP_AC_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && gcp1_is_app "word_gen_gc_move_refs" (lhs (concl th))
    then ASSUME_TAC (CONV_RULE GCP1AUX_NORM_CONV th) else failwith "") THEN
  REMOVE_THEN "IH" (MP_TAC o SPEC `k - 1`) THEN ANTS_TAC THENL [GCP1AUX_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`s4:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; `m2:A word->A word_loc`; `dm:A word->bool`; `curr:A word`;
     `xs1:(A word_loc)list`; `s1:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; `pb3:A word`; `pa3:A word`; `m3:A word->A word_loc`;
     `ib3:A word`; `i3:A word`; `frame:(A word#A word_loc->bool)->bool`; `c3:bool`; `r2a3:A word`;
     `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`;
     `conf:data_to_word_config`; `p:A word`]) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND; ALL; is_Ref_def]) THEN
    ASM_REWRITE_TAC[ALL_APPEND; ALL; is_Ref_def] THEN
    CONV_TAC GCP1AUX_NORM_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN GCP1AUX_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs9:(A word_loc)list` MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC GCP1AUX_NORM_CONV THEN STRIP_TAC THEN
  EXISTS_TAC `xs9:(A word_loc)list` THEN ASM_REWRITE_TAC[] THEN
  GCP1AUX_ARITH_TAC);;

(* HOL4 line 2027 *)
let word_gen_gc_move_data_thm = prove
 (`!k s m dm (curr:A word) xs s1 pb1 pa1 m1 ib1 i1 frame c1 gen_conf conf p.
     (gen_gc_gc_move_data gen_conf s = s1) /\ gc_state_ok s1 /\
     heap_length (gc_state_heap s) <= dimword (:A) DIV 2 EXP shift_length conf /\
     heap_length (gc_state_heap s) * (dimindex (:A) DIV 8) < dimword (:A) /\
     data_to_word_config_len_size conf + 2 < dimindex (:A) /\
     (!t r. (gen_gc_conf_isRef gen_conf (t,r) <=> isMutTag t)) /\
     data_to_word_config_len_size conf + 5 <= dimindex (:A) /\
     (word_gen_gc_move_data conf k
        (word_add p (word_mul bytes_in_word (word (heap_length (gc_state_h1 s)))),
         word (gc_state_a s),
         word_add p (word_mul bytes_in_word
           (word (heap_length (APPEND (gc_state_h1 s) (gc_state_h2 s))))),
         word (gc_state_a s + gc_state_n s),
         word_add p (word_mul bytes_in_word
           (word (heap_length (APPEND (gc_state_h1 s) (gc_state_h2 s)) + gc_state_n s))),
         curr,m,dm) =
       (i1,pa1,ib1,pb1,m1,c1)) /\
     heap_length (gc_state_h2 s) + gc_state_n s + heap_length (gc_state_r4 s) <= k /\
     len_inv s /\
     (word_heap curr (gc_state_heap s) conf STAR
      word_heap_parts conf p s xs STAR
      frame) (fun2set (m,dm)) /\
     ALL (is_Ref (gen_gc_conf_isRef gen_conf))
       (APPEND (APPEND (APPEND (gc_state_r4 s) (gc_state_r3 s)) (gc_state_r2 s))
          (gc_state_r1 s)) /\
     LENGTH xs = gc_state_n s /\ good_dimindex (:A) ==>
     ?xs1.
       (word_heap curr (gc_state_heap s1) conf STAR
        word_heap_parts conf p s1 xs1 STAR
        frame) (fun2set (m1,dm)) /\ gc_state_h2 s1 = [] /\
       heap_length (gc_state_heap s1) = heap_length (gc_state_heap s) /\
       c1 /\ (i1 = word (gc_state_a s1)) /\
       (ib1 = word (gc_state_a s1 + gc_state_n s1)) /\
       gc_state_n s1 = LENGTH xs1 /\ len_inv s1 /\
       heap_length (APPEND (APPEND (gc_state_h1 s1) (gc_state_h2 s1)) (gc_state_r4 s1)) +
         gc_state_n s1 =
       heap_length (APPEND (APPEND (gc_state_h1 s) (gc_state_h2 s)) (gc_state_r4 s)) +
         gc_state_n s /\
       pa1 = word_add p (word_mul bytes_in_word
               (word (heap_length (APPEND (gc_state_h1 s1) (gc_state_h2 s1))))) /\
       pb1 = word_add p (word_mul bytes_in_word
               (word (heap_length (APPEND (gc_state_h1 s1) (gc_state_h2 s1)) +
                      gc_state_n s1))) /\
       ALL (is_Ref (gen_gc_conf_isRef gen_conf))
         (APPEND (APPEND (APPEND (gc_state_r4 s1) (gc_state_r3 s1)) (gc_state_r2 s1))
            (gc_state_r1 s1))`,
  (MATCH_MP_TAC num_WF THEN X_GEN_TAC `k:num` THEN DISCH_THEN(LABEL_TAC "IH") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GCP1AUX_UNDISCH_EQ "gen_gc_gc_move_data" THEN ONCE_REWRITE_TAC[gen_gc_gc_move_data_def] THEN
  MP_TAC(ISPEC `gc_state_h2 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th] THEN CASE_REWRITE_TAC[])
    (X_CHOOSE_THEN `hd:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element` (X_CHOOSE_THEN `h2t:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
       (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th] THEN CASE_REWRITE_TAC[])))) THENL
   [DISCH_TAC THEN GCP1AUX_SUBST_VARS_TAC ["s1"] THEN
    REWRITE_TAC[word_heap_parts_def; len_inv_def] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[word_heap_parts_def; len_inv_def]) THEN
    FIRST_ASSUM(fun th -> if concl th = `gc_state_h2 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = []` then SUBST_ALL_TAC th
                          else failwith "") THEN
    GCP1AUX_UNDISCH_EQ "word_gen_gc_move_data" THEN ONCE_REWRITE_TAC[word_gen_gc_move_data_def] THEN
    REWRITE_TAC[APPEND_NIL; PAIR_EQ] THEN STRIP_TAC THEN
    GCP1AUX_SUBST_VARS_TAC ["i1";"pa1";"ib1";"pb1";"m1";"c1"] THEN
    EXISTS_TAC `xs:(A word_loc)list` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL]) THEN
    ASM_REWRITE_TAC[APPEND_NIL];
    ALL_TAC]) THEN
  (COND_CASES_TAC THENL
   [DISCH_TAC THEN GCP1AUX_SUBST_VARS_TAC ["s1"] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `hd:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `u:num` SUBST_ALL_TAC)
    (DISJ_CASES_THEN2
      (X_CHOOSE_THEN `pp:num` (X_CHOOSE_THEN `pd:A word_loc`
         (X_CHOOSE_THEN `l:num` SUBST_ALL_TAC)))
      (X_CHOOSE_THEN `ys:((A word_loc)heap_address)list` (X_CHOOSE_THEN `l:num`
         (X_CHOOSE_THEN `tg:data_to_word_memoryProof_tag#(A word_loc)list`
            SUBST_ALL_TAC))))) THEN
  CASE_REWRITE_TAC[] THENL
   [DISCH_TAC THEN GCP1AUX_SUBST_VARS_TAC ["s1"] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN ASM_MESON_TAC[];
    DISCH_TAC THEN GCP1AUX_SUBST_VARS_TAC ["s1"] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN ASM_MESON_TAC[];
    ALL_TAC]) THEN
  (MP_TAC(ISPEC `tg:data_to_word_memoryProof_tag#(A word_loc)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tag:data_to_word_memoryProof_tag`
    (X_CHOOSE_THEN `qs:(A word_loc)list` SUBST_ALL_TAC)) THEN
  GCP1AUX_SPLITN_TAC "gen_gc_gc_move_list" ["ys3";"s3"] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN DISCH_TAC THEN
  ABBREV_TAC `s4 = gc_state_ok_fupd (K (gc_state_ok s3 /\ ~(gc_state_h2 s3 = []) /\
      HD (gc_state_h2 s3) = DataElement ys l (tag,qs)))
      (gc_state_h2_fupd (K (TL (gc_state_h2 s3)))
      (gc_state_h1_fupd (K (APPEND (gc_state_h1 s3) [DataElement ys3 l (tag,qs)])) (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)))`) THEN
  (SUBGOAL_THEN `gc_state_h1 (s4:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = APPEND (gc_state_h1 s3) [DataElement ys3 l (tag,qs)] /\
     gc_state_h2 s4 = TL (gc_state_h2 s3) /\
     gc_state_r4 s4 = gc_state_r4 s3 /\ gc_state_r3 s4 = gc_state_r3 s3 /\
     gc_state_r2 s4 = gc_state_r2 s3 /\ gc_state_r1 s4 = gc_state_r1 s3 /\
     gc_state_heap s4 = gc_state_heap s3 /\ gc_state_a s4 = gc_state_a s3 /\
     gc_state_n s4 = gc_state_n s3 /\
     (gc_state_ok s4 <=> gc_state_ok s3 /\ ~(gc_state_h2 s3 = []) /\
        HD (gc_state_h2 s3) = DataElement ys l (tag,qs))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s4" THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `gc_state_ok (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) /\ ~(gc_state_h2 s3 = []) /\
                HD (gc_state_h2 s3) = DataElement ys l (tag,qs)` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `gc_state_ok (s4:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`
                            then SUBST1_TAC (SYM th) else failwith "") THEN
    MATCH_MP_TAC gc_move_data_ok THEN
    EXISTS_TAC `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `len_inv (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` ASSUME_TAC THENL
   [MATCH_MP_TAC data_to_word_gcProof_gc_move_list_thm THEN
    MAP_EVERY EXISTS_TAC [`ys:((A word_loc)heap_address)list`; `s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
      `ys3:((A word_loc)heap_address)list`;
      `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP gc_move_list_const o
    check (fun th -> gcp1_is_app "gen_gc_gc_move_list" (lhs (concl th)))) THEN
  MP_TAC(ISPECL [`ys:((A word_loc)heap_address)list`; `s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `ys3:((A word_loc)heap_address)list`; `s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`]
    gc_move_list_with_NIL_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` (X_CHOOSE_THEN `e1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `TL (gc_state_h2 (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) = APPEND h2t d1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[APPEND; TL]; ALL_TAC] THEN
  SUBGOAL_THEN `len_inv (s4:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` ASSUME_TAC THENL
   [UNDISCH_TAC `len_inv (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` THEN ASM_REWRITE_TAC[len_inv_def] THEN
    REWRITE_TAC[APPEND; heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def; heap_length_NIL] THEN
    ARITH_TAC;
    ALL_TAC]) THEN
  (RULE_ASSUM_TAC(REWRITE_RULE[word_heap_parts_def]) THEN
  FIRST_X_ASSUM(fun th ->
    if concl th = `LENGTH (xs:(A word_loc)list) = gc_state_n (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`
    then SUBST_ALL_TAC th THEN ASSUME_TAC th else failwith "") THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `gc_state_h2 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`
                          then SUBST_ALL_TAC th THEN ASSUME_TAC th else failwith "") THEN
  GCP1AUX_UNDISCH_EQ "word_gen_gc_move_data" THEN ONCE_REWRITE_TAC[word_gen_gc_move_data_def] THEN
  SUBGOAL_THEN `~(word_add p (word_mul bytes_in_word (word (heap_length (gc_state_h1 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))))) =
                  word_add p (word_mul bytes_in_word (word (heap_length (APPEND (gc_state_h1 s)
                     (CONS (DataElement ys l (tag,qs)) h2t))))):A word)` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC GCP1AUX_new_addr_ne2 THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `len_inv (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` THEN
    UNDISCH_TAC `heap_length (gc_state_heap (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) * dimindex (:A) DIV 8 < dimword (:A)` THEN
    ASM_REWRITE_TAC[len_inv_def; heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def] THEN
    REPEAT DISCH_TAC THEN CONJ_TAC THENL
     [ARITH_TAC;
      MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `heap_length (gc_state_heap (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) * dimindex (:A) DIV 8` THEN
      ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(k = 0)` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `heap_length (CONS (DataElement ys l (tag,qs)) (h2t:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)) + gc_state_n (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) +
                 heap_length (gc_state_r4 s) <= k` THEN
    REWRITE_TAC[GC1AUX_heap_length_CONS; el_length_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) && free_in `xs:(A word_loc)list` (concl th) then
     let wh = find (fun t -> gcp1_is_app "word_heap" t && free_in `h2t:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` t)
                   (gcp1_star_leaves (rator (concl th))) in
     MP_TAC(MATCH_MP GCP1AUX_heap_el_read (GCP1AUX_STAR_FRONT [wh] th)) else NO_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `hh:A word` (X_CHOOSE_THEN `ts:(A word_loc)list` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[theWord_def; isWord_def; LET_DEF; LET_END_DEF] THEN
  GCP1AUX_ASM_MP (ISPECL [`ys:((A word_loc)heap_address)list`; `l:num`; `tag:data_to_word_memoryProof_tag`;
    `qs:(A word_loc)list`; `conf:data_to_word_config`; `hh:A word`; `ts:(A word_loc)list`]
    word_payload_T_IMP) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2)) THEN
  (ASM_CASES_TAC `bit 2 (hh:A word)` THEN ASM_REWRITE_TAC[] THENL
   [(DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
      `gen_gc_gc_move_list (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf) (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) [] = (ys3,s3)`)) THEN
    REWRITE_TAC[gen_gc_gc_move_list_def; PAIR_EQ] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> free_in `d1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` (concl th) ||
                                                      free_in `e1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` (concl th)))) THEN
    GCP1AUX_SUBST_VARS_TAC ["ys3";"s3"] THEN
    GCP1AUX_SPLITN_TAC "word_gen_gc_move_data" ["i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    GCP1AUX_SUBST_VARS_TAC ["i1";"pa1";"ib1";"pb1";"m1";"c1"]) THEN
    (REMOVE_THEN "IH" (MP_TAC o SPEC `k - 1`) THEN ANTS_TAC THENL [GCP1AUX_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`s4:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; `m:A word->A word_loc`; `dm:A word->bool`; `curr:A word`;
     `xs:(A word_loc)list`; `s1:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; `pb2:A word`; `pa2:A word`; `m2:A word->A word_loc`;
     `ib2:A word`; `i2:A word`; `frame:(A word#A word_loc->bool)->bool`; `c2:bool`;
     `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`;
     `conf:data_to_word_config`; `p:A word`]) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq (concl th) && gcp1_is_app "word_gen_gc_move_data" (lhs (concl th))
      then ASSUME_TAC (CONV_RULE GCP1AUX_NORM2_CONV th) else failwith "") THEN
    ASM_REWRITE_TAC[TL] THEN CONV_TAC GCP1AUX_NORM2_CONV THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[GC1AUX_heap_length_CONS; el_length_def]) THEN GCP1AUX_ARITH_TAC;
      REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
      FIRST_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) && free_in `xs:(A word_loc)list` (concl th)
        then ASSUME_TAC (CONV_RULE GCP1AUX_NORM2_CONV (REWRITE_RULE[GSYM APPEND_ASSOC; APPEND] th))
        else failwith "") THEN
      CONV_TAC GCP1AUX_NORM2_CONV THEN GCP1AUX_SEP_AC_TAC];
    ALL_TAC]) THEN
    (DISCH_THEN(X_CHOOSE_THEN `xs9:(A word_loc)list` MP_TAC) THEN
  ASM_REWRITE_TAC[TL] THEN STRIP_TAC THEN
  EXISTS_TAC `xs9:(A word_loc)list` THEN REWRITE_TAC[word_heap_parts_def] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def;
                              heap_length_NIL]) THEN
  REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def; heap_length_NIL] THEN
  GCP1AUX_ARITH_TAC);
    (DISCH_TAC THEN GCP1AUX_SUBST_LVARS_TAC ["ts"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `LENGTH (ys:((A word_loc)heap_address)list) = l`)) THEN
  GCP1AUX_SPLITN_TAC "word_gen_gc_move_list" ["h2a2";"i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
  GCP1AUX_SPLITN_TAC "word_gen_gc_move_data" ["i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  GCP1AUX_SUBST_VARS_TAC ["i1";"pa1";"ib1";"pb1";"m1";"c1"] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> gcp1_is_fun2set_asm (concl th) &&
                                          free_in `xs:(A word_loc)list` (concl th))) THEN
  GCP1AUX_DE_SPLIT_TAC THEN
  CONV_TAC(LAND_CONV GCP1AUX_NORM2_CONV) THEN DISCH_TAC) THEN
    (FIRST_X_ASSUM(fun th -> if is_eq (concl th) && gcp1_is_app "word_gen_gc_move_list" (lhs (concl th))
    then ASSUME_TAC (CONV_RULE GCP1AUX_NORM2_CONV th) else failwith "") THEN
  MP_TAC(GEN `fr:(A word#A word_loc->bool)->bool` (CONV_RULE GCP1AUX_NORM2_CONV
    (REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM] (ISPECL [
    `ys:((A word_loc)heap_address)list`; `xs:(A word_loc)list`; `ys3:((A word_loc)heap_address)list`;
    `gc_state_h2_fupd (K d1) (gc_state_r4_fupd (K e1) (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))`;
    `gc_state_h2_fupd (K []) (gc_state_r4_fupd (K []) (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))`;
    `pb2:A word`; `pa2:A word`;
    `word_add p (word_mul bytes_in_word (word (heap_length (APPEND (gc_state_h1 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))
       (CONS (DataElement ys (LENGTH (ys:((A word_loc)heap_address)list)) (tag,qs)) h2t))))):A word`;
    `m2:A word->A word_loc`; `m:A word->A word_loc`; `ib2:A word`; `i2:A word`;
    `fr:(A word#A word_loc->bool)->bool`; `dm:A word->bool`; `curr:A word`; `c2:bool`;
    `word_add (word_add p (word_mul bytes_in_word (word (heap_length (gc_state_h1 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))))))
       bytes_in_word:A word`;
    `h2a2:A word`; `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`;
    `conf:data_to_word_config`] word_gen_gc_move_list_thm)))) THEN
  GCP1AUX_SEP_FRAME_TAC THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ALL_APPEND; ALL; APPEND] THEN CONJ_TAC THENL
     [FIRST_ASSUM(fun th -> if gcp1_is_app "ALL" (concl th) then MP_TAC th else failwith "") THEN
      REWRITE_TAC[ALL_APPEND; ALL] THEN MESON_TAC[];
      MP_TAC(SPEC `LENGTH (ys:((A word_loc)heap_address)list)` GCP1AUX_len_bound) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs1:(A word_loc)list` STRIP_ASSUME_TAC)) THEN
    (GCP1AUX_SUBST_LVARS_TAC ["i2";"ib2";"h2a2";"pb2";"pa2"] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `gc_state_n (s3:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = LENGTH (xs1:(A word_loc)list)`
    then SUBST_ALL_TAC (SYM th) THEN ASSUME_TAC (SYM th) else failwith "") THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `gc_state_n (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` &&
                             free_in `d1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` (rhs (concl th))
    then SUBST_ALL_TAC th THEN ASSUME_TAC th else failwith "") THEN
  MP_TAC(ISPECL [`ys:((A word_loc)heap_address)list`; `tag:data_to_word_memoryProof_tag`;
    `qs:(A word_loc)list`; `conf:data_to_word_config`; `hh:A word`;
    `ys3:((A word_loc)heap_address)list`] word_payload_swap) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP gen_gc_gc_move_list_length o
    check (fun th -> concl th = `gen_gc_gc_move_list (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf) (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) ys = (ys3,s3)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && gcp1_is_app "word_gen_gc_move_data" (lhs (concl th))
    then ASSUME_TAC (CONV_RULE GCP1AUX_NORM2_CONV th) else failwith "") THEN
  FIRST_X_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) && free_in `m2:A word->A word_loc` (concl th)
    then ASSUME_TAC (CONV_RULE GCP1AUX_NORM2_CONV (REWRITE_RULE[GSYM APPEND_ASSOC; APPEND] th))
    else failwith "") THEN
  REMOVE_THEN "IH" (MP_TAC o SPEC `k - 1`) THEN ANTS_TAC THENL [GCP1AUX_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`s4:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; `m2:A word->A word_loc`; `dm:A word->bool`; `curr:A word`;
     `xs1:(A word_loc)list`; `s1:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; `pb3:A word`; `pa3:A word`; `m3:A word->A word_loc`;
     `ib3:A word`; `i3:A word`; `frame:(A word#A word_loc->bool)->bool`; `c3:bool`;
     `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`;
     `conf:data_to_word_config`; `p:A word`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[TL] THEN CONV_TAC GCP1AUX_NORM2_CONV THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[GC1AUX_heap_length_CONS; el_length_def]) THEN GCP1AUX_ARITH_TAC;
      REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
      GCP1AUX_DE_SPLIT_TAC THEN
      CONV_TAC(ONCE_DEPTH_CONV (GCP1AUX_HEAP_SPLIT_AT `h2t:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`)) THEN
      CONV_TAC(ONCE_DEPTH_CONV (GCP1AUX_HEAP_SPLIT_AT `e1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`)) THEN
      CONV_TAC GCP1AUX_NORM2_CONV THEN GCP1AUX_SEP_AC_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND]) THEN ASM_REWRITE_TAC[ALL_APPEND]];
    ALL_TAC]) THEN
    (DISCH_THEN(X_CHOOSE_THEN `xs9:(A word_loc)list` MP_TAC) THEN
  ASM_REWRITE_TAC[TL] THEN STRIP_TAC THEN
  EXISTS_TAC `xs9:(A word_loc)list` THEN REWRITE_TAC[word_heap_parts_def] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def;
                              heap_length_NIL]) THEN
  REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def; heap_length_NIL] THEN
  GCP1AUX_ARITH_TAC)]));;

(* HOL4 line 2229 *)
let LENGTH_LESS_EQ_SUM_el_length = prove
 (`!t:((A,B)heap_element)list. LENGTH t <= SUM (MAP el_length t)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; MAP; SUM; LE_0] THEN
  MP_TAC(ISPEC `h:(A,B)heap_element` el_length_NOT_0) THEN ASM_ARITH_TAC);;

(* HOL4 line 2235 *)
let word_gen_gc_move_loop_thm = prove
 (`!k s m dm (curr:A word) xs s1 pb1 pa1 m1 ib1 i1 frame c1 gen_conf conf p.
     (gen_gc_gc_move_loop gen_conf s k = s1) /\ gc_state_ok s1 /\
     heap_length (gc_state_heap s) <= dimword (:A) DIV 2 EXP shift_length conf /\
     heap_length (gc_state_heap s) * (dimindex (:A) DIV 8) < dimword (:A) /\
     data_to_word_config_len_size conf + 2 < dimindex (:A) /\
     gc_state_r3 s = [] /\ gc_state_r2 s = [] /\
     (!t r. (gen_gc_conf_isRef gen_conf (t,r) <=> isMutTag t)) /\
     data_to_word_config_len_size conf + 5 <= dimindex (:A) /\
     (word_gen_gc_move_loop conf k
        (word_add p (word_mul bytes_in_word (word (heap_length (gc_state_h1 s)))),
         word (gc_state_a s),
         word_add p (word_mul bytes_in_word
           (word (heap_length (APPEND (gc_state_h1 s) (gc_state_h2 s))))),
         word (gc_state_a s + gc_state_n s),
         word_add p (word_mul bytes_in_word
           (word (heap_length (APPEND (gc_state_h1 s) (gc_state_h2 s)) + gc_state_n s))),
         word_add p (word_mul bytes_in_word
           (word (heap_length (APPEND (APPEND (gc_state_h1 s) (gc_state_h2 s))
                                 (gc_state_r4 s)) + gc_state_n s))),
         curr,m,dm) =
       (i1,pa1,ib1,pb1,m1,c1)) /\ len_inv s /\
     (word_heap curr (gc_state_heap s) conf STAR
      word_heap_parts conf p s xs STAR
      frame) (fun2set (m,dm)) /\
     ALL (is_Ref (gen_gc_conf_isRef gen_conf))
       (APPEND (APPEND (APPEND (gc_state_r4 s) (gc_state_r3 s)) (gc_state_r2 s))
          (gc_state_r1 s)) /\
     LENGTH xs = gc_state_n s /\ good_dimindex (:A) ==>
     ?xs1.
       (word_heap curr (gc_state_heap s1) conf STAR
        word_heap_parts conf p s1 xs1 STAR
        frame) (fun2set (m1,dm)) /\
       gc_state_h2 s1 = [] /\ gc_state_r4 s1 = [] /\ gc_state_r3 s1 = [] /\
       gc_state_r2 s1 = [] /\
       heap_length (gc_state_heap s1) = heap_length (gc_state_heap s) /\
       c1 /\ (i1 = word (gc_state_a s1)) /\ gc_state_n s1 = LENGTH xs1 /\ len_inv s1 /\
       pa1 = word_add p (word_mul bytes_in_word (word (heap_length (gc_state_h1 s1)))) /\
       pb1 = word_add p (word_mul bytes_in_word
               (word (heap_length (gc_state_h1 s1) + gc_state_n s1))) /\
       (ib1 = word (gc_state_a s1 + gc_state_n s1)) /\
       ALL (is_Ref (gen_gc_conf_isRef gen_conf)) (gc_state_r1 s1)`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `k:num` THEN DISCH_THEN(LABEL_TAC "IH") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GCP1AUX_UNDISCH_EQ "gen_gc_gc_move_loop" THEN ONCE_REWRITE_TAC[gen_gc_gc_move_loop_def] THEN
  MP_TAC(ISPEC `gc_state_r4 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th] THEN CASE_REWRITE_TAC[])
    (X_CHOOSE_THEN `hr:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element` (X_CHOOSE_THEN `r4t:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
       (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th] THEN CASE_REWRITE_TAC[])))) THENL
   [MP_TAC(ISPEC `gc_state_h2 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2
      (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th] THEN CASE_REWRITE_TAC[])
      (X_CHOOSE_THEN `hd:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element` (X_CHOOSE_THEN `h2t:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
         (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th] THEN CASE_REWRITE_TAC[])))) THENL
     [DISCH_TAC THEN GCP1AUX_SUBST_VARS_TAC ["s1"] THEN
      REWRITE_TAC[word_heap_parts_def; len_inv_def] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[word_heap_parts_def; len_inv_def]) THEN
      REPEAT(FIRST_X_ASSUM(fun th -> let c = concl th in
        if is_eq c && rhs c = `[]:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` && is_comb (lhs c) && rand (lhs c) = `s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`
        then SUBST_ALL_TAC th else failwith "")) THEN
      GCP1AUX_UNDISCH_EQ "word_gen_gc_move_loop" THEN ONCE_REWRITE_TAC[word_gen_gc_move_loop_def] THEN
      REWRITE_TAC[APPEND_NIL; APPEND; PAIR_EQ] THEN STRIP_TAC THEN
      GCP1AUX_SUBST_VARS_TAC ["i1";"pa1";"ib1";"pb1";"m1";"c1"] THEN
      EXISTS_TAC `xs:(A word_loc)list` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL; APPEND; ALL_APPEND; ALL]) THEN
      ASM_REWRITE_TAC[APPEND_NIL; APPEND; heap_length_NIL; ADD_CLAUSES];
      (REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ABBREV_TAC `s7 = gen_gc_gc_move_data (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf) (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN GCP1AUX_SUBST_VARS_TAC ["s1"] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN ASM_MESON_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `gc_state_ok (s7:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` ASSUME_TAC THENL
   [MATCH_MP_TAC gen_gc_gc_move_loop_ok THEN
    MAP_EVERY EXISTS_TAC [`gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`; `k - 1`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GCP1AUX_UNDISCH_EQ "word_gen_gc_move_loop" THEN ONCE_REWRITE_TAC[word_gen_gc_move_loop_def] THEN
  ASM_REWRITE_TAC[APPEND_NIL] THEN
  SUBGOAL_THEN `~(word_add p (word_mul bytes_in_word (word (heap_length (gc_state_h1 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))))) =
                  word_add p (word_mul bytes_in_word (word (heap_length (APPEND (gc_state_h1 s)
                     (CONS hd h2t))))):A word)` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC GCP1AUX_new_addr_ne2 THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `hd:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element` el_length_NOT_0) THEN
    UNDISCH_TAC `len_inv (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` THEN
    UNDISCH_TAC `heap_length (gc_state_heap (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) * dimindex (:A) DIV 8 < dimword (:A)` THEN
    ASM_REWRITE_TAC[len_inv_def; heap_length_APPEND; GC1AUX_heap_length_CONS] THEN
    REPEAT DISCH_TAC THEN CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `heap_length (gc_state_heap (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) * dimindex (:A) DIV 8` THEN
      ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  GCP1AUX_SPLITN_TAC "word_gen_gc_move_data" ["i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
  ASM_REWRITE_TAC[] THEN
  GCP1AUX_SPLITN_TAC "word_gen_gc_move_loop" ["i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  GCP1AUX_SUBST_VARS_TAC ["i1";"pa1";"ib1";"pb1";"m1";"c1"]) THEN
      (MP_TAC(ISPECL [`dimword(:A)`; `s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; `m:A word->A word_loc`; `dm:A word->bool`; `curr:A word`;
     `xs:(A word_loc)list`; `s7:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; `pb2:A word`; `pa2:A word`; `m2:A word->A word_loc`;
     `ib2:A word`; `i2:A word`; `frame:(A word#A word_loc->bool)->bool`; `c2:bool`;
     `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`;
     `conf:data_to_word_config`; `p:A word`] word_gen_gc_move_data_thm) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[APPEND_NIL] THEN
    MP_TAC(SPECL [`dimword(:A)`; `2 EXP shift_length conf`] DIV_LE) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
    UNDISCH_TAC `len_inv (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` THEN ASM_REWRITE_TAC[len_inv_def; heap_length_APPEND] THEN
    REPEAT DISCH_TAC THEN GCP1AUX_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `xs1:(A word_loc)list` STRIP_ASSUME_TAC)]) THEN
      (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP gc_move_data_const o check (fun th -> concl th =
     `gen_gc_gc_move_data (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf) (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = s7`)) THEN
  GCP1AUX_SUBST_LVARS_TAC ["pa2";"pb2";"i2";"ib2"] THEN
  MAP_EVERY (fun t -> FIRST_X_ASSUM(fun th -> let c = concl th in
      if is_eq c && lhs c = t then SUBST_ALL_TAC th THEN ASSUME_TAC th else failwith ""))
    [`gc_state_h2 (s7:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`; `gc_state_h2 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`; `gc_state_r4 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `gc_state_n (s7:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = LENGTH (xs1:(A word_loc)list)`
    then SUBST_ALL_TAC (SYM th) THEN ASSUME_TAC (SYM th) else failwith "") THEN
  RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL]) THEN
  REMOVE_THEN "IH" (MP_TAC o SPEC `k - 1`) THEN ANTS_TAC THENL [GCP1AUX_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`s7:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; `m2:A word->A word_loc`; `dm:A word->bool`; `curr:A word`;
     `xs1:(A word_loc)list`; `s1:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; `pb3:A word`; `pa3:A word`; `m3:A word->A word_loc`;
     `ib3:A word`; `i3:A word`; `frame:(A word#A word_loc->bool)->bool`; `c3:bool`;
     `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`;
     `conf:data_to_word_config`; `p:A word`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[APPEND_NIL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs9:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `xs9:(A word_loc)list` THEN ASM_REWRITE_TAC[])];
    (REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ABBREV_TAC `s2 = gc_state_r4_fupd (K []) (gc_state_r2_fupd (K (CONS hr r4t)) (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))` THEN
  ABBREV_TAC `s7 = gc_move_refs (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf) (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN GCP1AUX_SUBST_VARS_TAC ["s1"] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN ASM_MESON_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `gc_state_ok (s7:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` ASSUME_TAC THENL
   [MATCH_MP_TAC gen_gc_gc_move_loop_ok THEN
    MAP_EVERY EXISTS_TAC [`gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`; `k - 1`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `gc_state_h1 (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = gc_state_h1 s /\ gc_state_h2 s2 = gc_state_h2 s /\
     gc_state_r4 s2 = [] /\ gc_state_r3 s2 = gc_state_r3 s /\ gc_state_r2 s2 = CONS hr r4t /\
     gc_state_r1 s2 = gc_state_r1 s /\ gc_state_heap s2 = gc_state_heap s /\
     gc_state_a s2 = gc_state_a s /\ gc_state_n s2 = gc_state_n s /\
     gc_state_ok s2 = gc_state_ok s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s2" THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM]; ALL_TAC] THEN
  GCP1AUX_UNDISCH_EQ "word_gen_gc_move_loop" THEN ONCE_REWRITE_TAC[word_gen_gc_move_loop_def] THEN
  SUBGOAL_THEN `~(word_add p (word_mul bytes_in_word
           (word (heap_length (APPEND (APPEND (gc_state_h1 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) (gc_state_h2 s))
                                 (gc_state_r4 s)) + gc_state_n s))) =
                  word_add p (word_mul bytes_in_word
           (word (heap_length (APPEND (gc_state_h1 s) (gc_state_h2 s)) + gc_state_n s))):A word)`
    (fun th -> REWRITE_TAC[th]) THENL
   [ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    MATCH_MP_TAC GCP1AUX_new_addr_ne2 THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `hr:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element` el_length_NOT_0) THEN
    UNDISCH_TAC `len_inv (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` THEN
    UNDISCH_TAC `heap_length (gc_state_heap (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) * dimindex (:A) DIV 8 < dimword (:A)` THEN
    ASM_REWRITE_TAC[len_inv_def; heap_length_APPEND; GC1AUX_heap_length_CONS] THEN
    REPEAT DISCH_TAC THEN CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `heap_length (gc_state_heap (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) * dimindex (:A) DIV 8` THEN
      ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  GCP1AUX_SPLITN_TAC "word_gen_gc_move_refs" ["p2";"i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
  ASM_REWRITE_TAC[] THEN
  GCP1AUX_SPLITN_TAC "word_gen_gc_move_loop" ["i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  GCP1AUX_SUBST_VARS_TAC ["i1";"pa1";"ib1";"pb1";"m1";"c1"]) THEN
    (FIRST_X_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `gc_state_r4 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`
     then SUBST_ALL_TAC th THEN ASSUME_TAC th else failwith "") THEN
  MP_TAC(ISPECL [`dimword(:A)`; `s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; `m:A word->A word_loc`; `dm:A word->bool`; `curr:A word`;
     `xs:(A word_loc)list`; `s7:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; `pb2:A word`; `pa2:A word`; `m2:A word->A word_loc`;
     `ib2:A word`; `i2:A word`; `frame:(A word#A word_loc->bool)->bool`; `c2:bool`; `p2:A word`;
     `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`;
     `conf:data_to_word_config`; `p:A word`] word_gen_gc_move_refs_thm) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[word_heap_parts_def; len_inv_def] THEN ASM_REWRITE_TAC[APPEND_NIL; APPEND] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `heap_length (CONS (hr:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element) r4t)` THEN CONJ_TAC THENL
       [REWRITE_TAC[heap_length_def; LENGTH_LESS_EQ_SUM_el_length];
        MP_TAC(SPECL [`dimword(:A)`; `2 EXP shift_length conf`] DIV_LE) THEN
        REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN UNDISCH_TAC `len_inv (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` THEN
        ASM_REWRITE_TAC[len_inv_def; heap_length_APPEND] THEN REPEAT DISCH_TAC THEN
        GCP1AUX_ARITH_TAC];
      ALL_TAC] THEN
    MAP_EVERY (fun pr -> FIRST_ASSUM(fun th -> if pr (concl th) then
        MP_TAC (REWRITE_RULE[len_inv_def; word_heap_parts_def; APPEND_NIL; APPEND;
          ASSUME `gc_state_r4 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = CONS hr r4t`; ASSUME `gc_state_r3 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = []`;
          ASSUME `gc_state_r2 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = []`;
          ASSUME `LENGTH (xs:(A word_loc)list) = gc_state_n (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`] th) else failwith ""))
      [(fun c -> c = `len_inv (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`);
       (fun c -> gcp1_is_fun2set_asm c && free_in `xs:(A word_loc)list` c);
       gcp1_is_app "ALL"] THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `xs1:(A word_loc)list` STRIP_ASSUME_TAC)]) THEN
    (GCP1AUX_SUBST_LVARS_TAC ["i2";"ib2";"pa2";"pb2"] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `gc_state_n (s7:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = LENGTH (xs1:(A word_loc)list)`
    then SUBST_ALL_TAC (SYM th) THEN ASSUME_TAC (SYM th) else failwith "") THEN
  FIRST_ASSUM(fun th -> if concl th =
    `gc_move_refs (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf) (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = s7`
    then let th2 = TRANS (MATCH_MP gc_move_refs_const th)
                         (ASSUME `gc_state_h1 (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = gc_state_h1 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`) in
         SUBST_ALL_TAC th2 THEN ASSUME_TAC th2
    else failwith "") THEN
  SUBGOAL_THEN `word_add p (word_mul bytes_in_word (word (heap_length (APPEND (APPEND
       (gc_state_h1 (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) (gc_state_h2 (s7:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))) (gc_state_r4 s7)) + gc_state_n s7))) =
     word_add p (word_mul bytes_in_word (word (heap_length (APPEND (gc_state_h1 s)
       (gc_state_h2 s)) + gc_state_n s))):A word` ASSUME_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(fun th -> if is_eq (concl th) && free_in `gc_state_n (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` (lhs (concl th)) &&
                             free_in `gc_state_r4 (s7:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` (rhs (concl th))
      then MP_TAC (REWRITE_RULE[ASSUME `gc_state_h2 (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = gc_state_h2 s`;
             ASSUME `gc_state_n (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = gc_state_n (s:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`; ASSUME `gc_state_r4 (s2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = []`] th)
      else failwith "") THEN
    REWRITE_TAC[heap_length_APPEND; heap_length_NIL] THEN ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "IH" (MP_TAC o SPEC `k - 1`) THEN ANTS_TAC THENL [GCP1AUX_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`s7:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; `m2:A word->A word_loc`; `dm:A word->bool`; `curr:A word`;
     `xs1:(A word_loc)list`; `s1:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; `pb3:A word`; `pa3:A word`; `m3:A word->A word_loc`;
     `ib3:A word`; `i3:A word`; `frame:(A word#A word_loc->bool)->bool`; `c3:bool`;
     `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`;
     `conf:data_to_word_config`; `p:A word`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs9:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `xs9:(A word_loc)list` THEN ASM_REWRITE_TAC[])]);;
(* ------------------------------------------------------------------------- *)
(* Helpers for word_gen_gc_thm                                               *)
(* ------------------------------------------------------------------------- *)

let GCP1AUX_ushr_bw = prove
 (`!n. n * (dimindex (:A) DIV 8) < dimword (:A) /\ good_dimindex (:A) ==>
       word_ushr (word_mul bytes_in_word (word n)) (backend_common_word_shift (:A)) =
       word n:A word`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; bytes_in_word_def; GSYM WORD_MUL; VAL_WORD;
              backend_common_word_shift_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (DISJ_CASES_THEN SUBST1_TAC)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n * 4 < m ==> n < m`; ARITH_RULE `n * 8 < m ==> n < m`;
               ARITH_RULE `n * 4 < m ==> 4 * n < m`; ARITH_RULE `n * 8 < m ==> 8 * n < m`] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

(* HOL4 line 2388 *)
let word_gen_gc_thm = prove
 (`!m dm (curr:A word) s1 pb1 pa1 m1 ib1 i1 frame c1 roots heap roots1 roots1' new
    gen_conf conf.
     (gen_gc gen_conf (roots,heap) = (roots1,s1)) /\ gc_state_ok s1 /\
     (word_gen_gc conf
        (MAP (word_addr conf) roots,curr,new,
         word_mul bytes_in_word (word (heap_length heap)),m,dm) =
       (roots1',i1,pa1:A word,ib1,pb1,m1,c1)) /\
     heap_length heap <= dimword (:A) DIV 2 EXP shift_length conf /\
     heap_length heap * (dimindex (:A) DIV 8) < dimword (:A) /\
     data_to_word_config_len_size conf + 2 < dimindex (:A) /\
     (!t r. (gen_gc_conf_isRef gen_conf (t,r) <=> isMutTag t)) /\
     data_to_word_config_len_size conf + 5 <= dimindex (:A) /\
     good_dimindex (:A) /\
     (word_heap curr heap conf STAR
      word_list_exists new (heap_length heap) STAR
      frame) (fun2set (m,dm)) /\ good_dimindex (:A) ==>
     ?xs1.
       (word_heap curr (gc_state_heap s1) conf STAR
        word_heap_parts conf new s1 xs1 STAR
        frame) (fun2set (m1,dm)) /\
       gc_state_h2 s1 = [] /\ gc_state_r4 s1 = [] /\ gc_state_r3 s1 = [] /\
       gc_state_r2 s1 = [] /\
       roots1' = MAP (word_addr conf) roots1 /\
       heap_length (gc_state_heap s1) = heap_length heap /\
       c1 /\ (i1 = word (gc_state_a s1)) /\
       (ib1 = word (gc_state_a s1 + gc_state_n s1)) /\
       pa1 = word_add new (word_mul bytes_in_word (word (heap_length (gc_state_h1 s1)))) /\
       pb1 = word_add new (word_mul bytes_in_word
               (word (heap_length (gc_state_h1 s1) + gc_state_n s1))) /\
       roots1' = MAP (word_addr conf) roots1 /\
       gc_state_n s1 = LENGTH xs1 /\ len_inv s1 /\
       ALL (is_Ref (gen_gc_conf_isRef gen_conf)) (gc_state_r1 s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GCP1AUX_UNDISCH_EQ "gen_gc" THEN REWRITE_TAC[gen_gc_def; LET_DEF; LET_END_DEF] THEN
  ABBREV_TAC `s0 = gc_state_ok_fupd (K (heap_length heap = gen_gc_conf_limit gen_conf))
     (gc_state_n_fupd (K (gen_gc_conf_limit (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf)))
     (gc_state_heap_fupd (K heap) (empty_state:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)))` THEN
  GCP1AUX_SPLITN_TAC "gen_gc_gc_move_list" ["r2";"st2"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN GCP1AUX_SUBST_VARS_TAC ["roots1"] THEN
  SUBGOAL_THEN `gc_state_h1 (s0:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = [] /\ gc_state_h2 s0 = [] /\ gc_state_r4 s0 = [] /\
     gc_state_r3 s0 = [] /\ gc_state_r2 s0 = [] /\ gc_state_r1 s0 = [] /\
     gc_state_a s0 = 0 /\
     gc_state_n s0 = gen_gc_conf_limit (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf) /\
     gc_state_heap s0 = heap /\
     (gc_state_ok s0 <=> heap_length heap = gen_gc_conf_limit gen_conf)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN
    REWRITE_TAC[gc_state_FIELDS.ri_accfupds; gc_state_FIELDS.ri_accessors; K_THM; empty_state_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `gc_state_ok (st2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` ASSUME_TAC THENL
   [MATCH_MP_TAC gen_gc_gc_move_loop_ok THEN
    MAP_EVERY EXISTS_TAC [`gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`;
                          `gen_gc_conf_limit (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `gen_gc_conf_limit (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf) =
                heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)` (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THENL
   [SUBGOAL_THEN `gc_state_ok (s0:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` MP_TAC THENL
     [MATCH_MP_TAC gen_gc_gc_move_list_ok THEN ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) then
     let wl = find (gcp1_is_app "word_list_exists") (gcp1_star_leaves (rator (concl th))) in
     MP_TAC(MATCH_MP GCP1AUX_word_list_exists_elim (GCP1AUX_STAR_FRONT [wl] th))
     else failwith "") THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  GCP1AUX_UNDISCH_EQ "word_gen_gc" THEN REWRITE_TAC[word_gen_gc_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(SPEC `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)` GCP1AUX_ushr_bw) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `val (word (heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)):A word) = heap_length heap` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD; GSYM dimword_def] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(SPECL [`dimword(:A)`; `2 EXP shift_length conf`] DIV_LE) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN `~(heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) = dimword (:A))` MP_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) * dimindex (:A) DIV 8 < dimword (:A)` THEN
      ASM_REWRITE_TAC[NOT_LT] THEN GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = x * 1`] THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
      UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  GCP1AUX_SPLITN_TAC "word_gen_gc_move_roots" ["rs4";"i4";"pa4";"ib4";"pb4";"m4";"c4"] THEN
  GCP1AUX_SPLITN_TAC "word_gen_gc_move_loop" ["i5";"pa5";"ib5";"pb5";"m5";"c5"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  GCP1AUX_SUBST_VARS_TAC ["roots1'";"i1";"pa1";"ib1";"pb1";"m1";"c1"] THEN
  MP_TAC(ISPECL [`roots:((A word_loc)heap_address)list`; `xs:(A word_loc)list`;
    `r2:((A word_loc)heap_address)list`; `rs4:(A word_loc)list`; `st2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; `s0:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`;
    `pb4:A word`; `pa4:A word`; `new:A word`; `m4:A word->A word_loc`; `m:A word->A word_loc`;
    `ib4:A word`; `i4:A word`; `frame:(A word#A word_loc->bool)->bool`; `dm:A word->bool`;
    `curr:A word`; `c4:bool`;
    `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`;
    `conf:data_to_word_config`] word_gen_gc_move_roots_thm) THEN
  ASM_REWRITE_TAC[ALL; APPEND; ADD_CLAUSES] THEN
  ANTS_TAC THENL [GCP1AUX_SEP_AC_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs1:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP gc_move_list_const o check (fun th -> concl th =
     `gen_gc_gc_move_list (gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf) (s0:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) roots = r2,st2`)) THEN
  GCP1AUX_SUBST_LVARS_TAC ["rs4";"i4";"ib4";"pb4";"pa4"] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `gc_state_n (st2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state) = LENGTH (xs1:(A word_loc)list)`
    then SUBST_ALL_TAC (SYM th) THEN ASSUME_TAC (SYM th) else failwith "") THEN
  SUBGOAL_THEN `word_add new (word_mul bytes_in_word (word (heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))) =
     word_add new (word_mul bytes_in_word (word (heap_length (APPEND (APPEND (gc_state_h1 (st2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))
       (gc_state_h2 st2)) (gc_state_r4 st2)) + gc_state_n st2))):A word` ASSUME_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[heap_length_APPEND; heap_length_NIL; ADD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`; `st2:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; `m4:A word->A word_loc`; `dm:A word->bool`;
    `curr:A word`; `xs1:(A word_loc)list`; `s1:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`; `pb5:A word`; `pa5:A word`;
    `m5:A word->A word_loc`; `ib5:A word`; `i5:A word`; `frame:(A word#A word_loc->bool)->bool`;
    `c5:bool`; `gen_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_conf`;
    `conf:data_to_word_config`; `new:A word`] word_gen_gc_move_loop_thm) THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) =
      `word_add new (word_mul bytes_in_word (word (heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))):A word`
    then REWRITE_TAC[GSYM th] else failwith "") THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `heap_length (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`
    then ASSUME_TAC (SYM th) else failwith "") THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq (concl th) && gcp1_is_app "word_gen_gc_move_loop" (lhs (concl th))
      then ASSUME_TAC (CONV_RULE GCP1AUX_NORM2_CONV th) else failwith "") THEN
    FIRST_X_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) && free_in `m4:A word->A word_loc` (concl th)
      then ASSUME_TAC (CONV_RULE GCP1AUX_NORM2_CONV th) else failwith "") THEN
    REWRITE_TAC[word_heap_parts_def; len_inv_def] THEN ASM_REWRITE_TAC[APPEND; APPEND_NIL] THEN
    CONV_TAC GCP1AUX_NORM2_CONV THEN ASM_REWRITE_TAC[] THEN GCP1AUX_SEP_AC_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs9:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `xs9:(A word_loc)list` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 2454 *)
let data_to_word_gcProof_gc_forward_ptr_APPEND = prove
 (`!(h1:((A,B)heap_element)list) n h2 a b ok.
     gc_forward_ptr n (APPEND h1 h2) a b ok =
     if n < heap_length h1 then
       (\(h,ok). (APPEND h h2,ok)) (gc_forward_ptr n h1 a b ok)
     else
       (\(h,ok). (APPEND h1 h,ok)) (gc_forward_ptr (n - heap_length h1) h2 a b ok)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; heap_length_NIL; LT; SUB_0] THEN REPEAT GEN_TAC THEN
    GCP1AUX_TUPLE_TAC `gc_forward_ptr n (h2:((A,B)heap_element)list) a (b:A) ok` ["p1";"p2"] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[APPEND; GC1AUX_heap_length_CONS] THEN
  ONCE_REWRITE_TAC[gc_forward_ptr_def] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `0 < el_length (h:(A,B)heap_element) + heap_length (t:((A,B)heap_element)list)`
      (fun th -> REWRITE_TAC[th]) THENL
     [MP_TAC(ISPEC `h:(A,B)heap_element` el_length_NOT_0) THEN ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[APPEND];
    ALL_TAC] THEN
  ASM_CASES_TAC `n < el_length (h:(A,B)heap_element)` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `n < el_length (h:(A,B)heap_element) + heap_length (t:((A,B)heap_element)list)`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN `(n - el_length (h:(A,B)heap_element) < heap_length (t:((A,B)heap_element)list) <=>
                 n < el_length h + heap_length t) /\
                n - el_length h - heap_length t = n - (el_length h + heap_length t)`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN GCP1AUX_SPLIT_APP_TAC "gc_forward_ptr" THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[APPEND]);;

(* HOL4 line 2470 *)
let heap_split_APPEND = prove
 (`!(h1:((A,B)heap_element)list) h2.
     heap_split (heap_length h1) (APPEND h1 h2) = SOME (h1,h2)`,
  LIST_INDUCT_TAC THENL
   [GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `h2:((A,B)heap_element)list` list_CASES) THEN
    REWRITE_TAC[heap_length_NIL; APPEND; heap_split_def];
    ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[APPEND; GC1AUX_heap_length_CONS] THEN
  ONCE_REWRITE_TAC[heap_split_def] THEN
  MP_TAC(ISPEC `h:(A,B)heap_element` el_length_NOT_0) THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `~(e = 0) ==> ~(e + l = 0) /\ ~(e + l < e) /\ (e + l) - e = l`] THEN
  CASE_REWRITE_TAC[]);;

(* HOL4 line 2476 *)
let heap_split_APPEND' = prove
 (`!(h1:((A,B)heap_element)list) h2.
     heap_split (SUM (MAP el_length h1)) (APPEND h1 h2) = SOME (h1,h2)`,
  REWRITE_TAC[GSYM heap_length_def; heap_split_APPEND]);;

(* HOL4 line 2482 *)
let heap_drop_APPEND = prove
 (`!(h1:((A,B)heap_element)list) h2.
     heap_drop (heap_length h1) (APPEND h1 h2) = h2`,
  REWRITE_TAC[heap_drop_def; heap_split_APPEND] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 2488 *)
let heap_take_APPEND = prove
 (`!(h1:((A,B)heap_element)list) h2.
     heap_take (heap_length h1) (APPEND h1 h2) = h1`,
  REWRITE_TAC[heap_take_def; heap_split_APPEND] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 2494 *)
let heap_drop_0 = prove
 (`!h:((A,B)heap_element)list. heap_drop 0 h = h`,
  GEN_TAC THEN MP_TAC(ISPECL [`[]:((A,B)heap_element)list`; `h:((A,B)heap_element)list`]
    heap_drop_APPEND) THEN
  REWRITE_TAC[heap_length_NIL; APPEND]);;

(* HOL4 line 2500 *)
let gc_forward_ptr_heap_split = prove
 (`!(h1:((A,B)heap_element)list) h2 n h3 l n' b ok ok1 heap a b'.
     (heap_lookup n (APPEND (APPEND h1 h2) h3) = SOME (DataElement l n' b)) /\
     (gc_forward_ptr n (APPEND (APPEND h1 h2) h3) a b' ok = (heap,ok1)) /\
     n >= heap_length h1 /\ n < heap_length (APPEND h1 h2) ==>
     heap = APPEND (APPEND h1 (heap_take (heap_length h2)
                                 (heap_drop (heap_length h1) heap))) h3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GE] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_to_word_gcProof_gc_forward_ptr_APPEND]) THEN
  SUBGOAL_THEN `~(n < heap_length (h1:((A,B)heap_element)list))` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    free_in `heap:((A,B)heap_element)list` (rhs (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  GCP1AUX_SPLIT_APP_TAC "gc_forward_ptr" THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs (concl th) =
    `heap:((A,B)heap_element)list`)) THEN
  FIRST_ASSUM(fun th -> if gcp1_is_app "gc_forward_ptr" (lhs (concl th)) then
    ASSUME_TAC (MATCH_MP gc_forward_ptr_heap_length th) else NO_TAC) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; heap_drop_APPEND] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
    gcp1_is_app "heap_length" (lhs (concl th)))) THEN
  REWRITE_TAC[heap_take_APPEND]);;

(* the goal  heap = APPEND (APPEND h1 (heap_take ..)) h3  for the heap of a *)
(* forward-pointer step (gc_forward_ptr_heap_split with the lookup and the  *)
(* forward-pointer equation of the assumptions)                             *)
let GCP1AUX_FWD_SPLIT_TAC : tactic =
  FIRST_ASSUM(fun lk -> if is_eq (concl lk) && gcp1_is_app "heap_lookup" (lhs (concl lk)) then
    FIRST_ASSUM(fun fw -> if is_eq (concl fw) && gcp1_is_app "gc_forward_ptr" (lhs (concl fw))
      then
        let _,args = strip_comb (lhs (concl fw)) in
        let n = el 0 args and a = el 2 args and d = el 3 args and ok = el 4 args in
        let _,y = dest_pair (rhs (concl fw)) in
        let _,ls = strip_comb (rand (rhs (concl lk))) in
        MATCH_MP_TAC gc_forward_ptr_heap_split THEN
        MAP_EVERY EXISTS_TAC [n; el 0 ls; el 1 ls; el 2 ls; ok; y; a; d] THEN
        ASM_REWRITE_TAC[]
      else NO_TAC)
    else NO_TAC);;

(* HOL4 line 2512 *)
let partial_gc_move_heap_split = prove
 (`!conf (s:(A,B)gc_state) x x1 s1 h1 h2 h3.
     (gen_gc_partial_gc_move conf s x = (x1,s1)) /\
     heap_segment (gen_gc_partial_conf_gen_start conf,
                   gen_gc_partial_conf_refs_start conf) (gc_state_heap s) =
       SOME (h1,h2,h3) /\
     gen_gc_partial_conf_gen_start conf <= gen_gc_partial_conf_refs_start conf ==>
     gc_state_heap s1 =
       APPEND (APPEND h1 (heap_take (heap_length h2)
                            (heap_drop (heap_length h1) (gc_state_heap s1)))) h3`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN CASES_ON `x:A heap_address` THEN
  REWRITE_TAC[gen_gc_partial_gc_move_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  SIMP[] THEN EVERY_CASE_TAC THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    rhs (concl th) = `s1:(A,B)gc_state`))) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP heap_segment_IMP) THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
      rhs (concl th) = `gc_state_heap (s:(A,B)gc_state)` &&
      is_comb (lhs (concl th)) && gcp1_is_app "APPEND" (lhs (concl th))
    then RULE_ASSUM_TAC(REWRITE_RULE[SYM th]) THEN REWRITE_TAC[SYM th]
    else failwith "") THEN
  TRY(REWRITE_TAC[GSYM APPEND_ASSOC; heap_drop_APPEND; heap_take_APPEND] THEN NO_TAC) THEN
  GCP1AUX_FWD_SPLIT_TAC THEN GCP1AUX_ARITH_TAC);;
let GCP1AUX_heap_segment_APPEND = prove
 (`!(h1:((A,B)heap_element)list) h2 h3.
     heap_segment (heap_length h1,heap_length (APPEND h1 h2)) (APPEND (APPEND h1 h2) h3) =
     SOME (h1,h2,h3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_segment_def; GSYM APPEND_ASSOC; heap_split_APPEND] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[heap_length_APPEND; ARITH_RULE `~(a + b < a)`; ADD_SUB2; heap_split_APPEND] THEN
  CASE_REWRITE_TAC[]);;

(* HOL4 line 2532 *)
let partial_gc_move_list_heap_split = prove
 (`!x conf (s:(A,B)gc_state) x1 s1 h1 h2 h3.
     (gen_gc_partial_gc_move_list conf s x = (x1,s1)) /\
     heap_segment (gen_gc_partial_conf_gen_start conf,
                   gen_gc_partial_conf_refs_start conf) (gc_state_heap s) =
       SOME (h1,h2,h3) /\
     gen_gc_partial_conf_gen_start conf <= gen_gc_partial_conf_refs_start conf ==>
     gc_state_heap s1 =
       APPEND (APPEND h1 (heap_take (heap_length h2)
                            (heap_drop (heap_length h1) (gc_state_heap s1)))) h3`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_partial_gc_move_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP heap_segment_IMP) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      gcp1_is_app "APPEND" (lhs (concl th)))) THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; heap_drop_APPEND; heap_take_APPEND];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  GCP1AUX_TUPLE_TAC `gen_gc_partial_gc_move (conf:B gen_gc_partial_conf) (s:(A,B)gc_state) h`
    ["z1";"s2"] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_partial_gc_move_list (conf:B gen_gc_partial_conf) (s2:(A,B)gc_state) t`
    ["zs1";"u1"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP heap_segment_IMP) THEN
  GCP1AUX_ASM_MP (ISPECL [`conf:B gen_gc_partial_conf`; `s:(A,B)gc_state`; `h:A heap_address`;
    `z1:A heap_address`; `s2:(A,B)gc_state`; `h1:((A,B)heap_element)list`;
    `h2:((A,B)heap_element)list`; `h3:((A,B)heap_element)list`] partial_gc_move_heap_split) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP gc_move_heap_length) THEN
  SUBGOAL_THEN `?y. gc_state_heap (s2:(A,B)gc_state) = APPEND (APPEND h1 y) h3 /\
                    heap_length (y:((A,B)heap_element)list) = heap_length (h2:((A,B)heap_element)list)`
    STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `heap_take (heap_length (h2:((A,B)heap_element)list))
      (heap_drop (heap_length (h1:((A,B)heap_element)list)) (gc_state_heap (s2:(A,B)gc_state)))` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MAP_EVERY (fun t -> FIRST_ASSUM(MP_TAC o check (fun th -> concl th = t)))
      [`heap_length (gc_state_heap (s:(A,B)gc_state)) = heap_length (gc_state_heap (s2:(A,B)gc_state))`;
       `APPEND (APPEND h1 h2) h3 = gc_state_heap (s:(A,B)gc_state)`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `gc_state_heap (s2:(A,B)gc_state)`
      then GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th] else NO_TAC) THEN
    REWRITE_TAC[heap_length_APPEND] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`conf:B gen_gc_partial_conf`; `s2:(A,B)gc_state`;
    `zs1:(A heap_address)list`; `s1:(A,B)gc_state`; `h1:((A,B)heap_element)list`;
    `y:((A,B)heap_element)list`; `h3:((A,B)heap_element)list`]) THEN
  SUBGOAL_THEN `gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) = heap_length (h1:((A,B)heap_element)list) /\
                gen_gc_partial_conf_refs_start conf = heap_length (APPEND h1 (y:((A,B)heap_element)list))`
    (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REWRITE_TAC[heap_length_APPEND] THEN
    FIRST_X_ASSUM(fun th -> if is_eq (concl th) && rhs (concl th) =
      `gen_gc_partial_conf_refs_start (conf:B gen_gc_partial_conf)` then
      REWRITE_TAC[SYM th; heap_length_APPEND] else NO_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GCP1AUX_heap_segment_APPEND]);;
(* ------------------------------------------------------------------------- *)
(* Helpers for word_gen_gc_partial_move_thm: the range test of a pointer,   *)
(* a heap element inside the current segment, header addresses.             *)
(* ------------------------------------------------------------------------- *)

let GCP1AUX_word_range_test = prove
 (`!conf (curr:A word) ptr d gs rs hl.
     good_dimindex (:A) /\ hl * (dimindex (:A) DIV 8) < dimword (:A) /\
     ptr < hl /\ gs <= hl /\ rs <= hl /\ ptr * 2 EXP shift_length conf < dimword (:A) ==>
     (word_ult (word_sub (ptr_to_addr conf curr (get_addr conf ptr d)) curr)
               (word_mul bytes_in_word (word gs)) <=> ptr < gs) /\
     (word_ule (word_mul bytes_in_word (word rs))
               (word_sub (ptr_to_addr conf curr (get_addr conf ptr d)) curr) <=> rs <= ptr)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GCP1AUX_ptr_to_addr_get_addr] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add (c:A word) x) c = x`] THEN
  REWRITE_TAC[bytes_in_word_def; GSYM WORD_MUL; WORD_ULT; WORD_ULE; VAL_WORD] THEN
  SUBGOAL_THEN `~(dimindex (:A) DIV 8 = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. k <= hl ==> dimindex (:A) DIV 8 * k < 2 EXP dimindex (:A)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `dimindex (:A) DIV 8 * hl` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[LE_MULT_LCANCEL];
      ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[GSYM dimword_def]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ptr <= hl` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[dimword_def] THEN ASM_SIMP_TAC[MOD_LT; LT_MULT_LCANCEL; LE_MULT_LCANCEL]);;

let GCP1AUX_heap_segment_lookup = prove
 (`!heap gs rs old current refs ptr (el:(A,B)heap_element).
     heap_segment (gs,rs) heap = SOME (old,current,refs) /\ gs <= ptr /\ ptr < rs /\
     heap_lookup ptr heap = SOME el ==>
     ?ha hb. current = APPEND ha (CONS el hb) /\ ptr = heap_length old + heap_length ha /\
             heap = APPEND (APPEND old current) refs /\ heap_length old = gs /\
             heap_length (APPEND old current) = rs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP heap_segment_IMP) THEN
  SUBGOAL_THEN `heap_lookup (ptr - heap_length (old:((A,B)heap_element)list)) current =
                SOME (el:(A,B)heap_element)` MP_TAC THENL
   [UNDISCH_TAC `heap_lookup ptr (heap:((A,B)heap_element)list) = SOME el` THEN
    FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
                               rhs (concl th) = `heap:((A,B)heap_element)list`
                            then SUBST1_TAC (SYM th) else NO_TAC) THEN
    SUBGOAL_THEN `ptr < heap_length (APPEND old current:((A,B)heap_element)list) /\
                  ~(ptr < heap_length (old:((A,B)heap_element)list))` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[gen_gc_heap_lookup_APPEND];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP heap_lookup_SPLIT) THEN
  DISCH_THEN(X_CHOOSE_THEN `ha:((A,B)heap_element)list` (X_CHOOSE_THEN `hb:((A,B)heap_element)list`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`ha:((A,B)heap_element)list`; `hb:((A,B)heap_element)list`] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let GCP1AUX_ptr_to_addr_split = prove
 (`!conf (curr:A word) o1 o2 d.
     (o1 + o2) * 2 EXP shift_length conf < dimword (:A) ==>
     ptr_to_addr conf curr (get_addr conf (o1 + o2) d) =
     word_add (word_add curr (word_mul bytes_in_word (word o1)))
              (word_mul bytes_in_word (word o2))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GCP1AUX_ptr_to_addr_get_addr] THEN
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let GCP1AUX_get_addr_and_1_not_0 = prove
 (`!conf k a. ~(word_and (get_addr conf k a) (word 1) = word 0:A word)`,
  ONCE_REWRITE_TAC[WORD_AND_SYM] THEN REWRITE_TAC[get_addr_and_1_not_0]);;

(* HOL4 line 2574 *)
let word_gen_gc_partial_move_thm = prove
 (`!gc_conf gcstate x x1 gcstate1 conf (curr:A word) old current refs pa xs frame
    m dm w i1 pa1 m1 c1.
     (gen_gc_partial_gc_move gc_conf gcstate x = (x1,gcstate1)) /\
     gc_state_h2 gcstate = [] /\ gc_state_r4 gcstate = [] /\ gc_state_ok gcstate1 /\
     gen_gc_partial_conf_limit gc_conf = heap_length (gc_state_heap gcstate) /\
     good_dimindex (:A) /\
     heap_length (gc_state_heap gcstate) <= dimword (:A) DIV 2 EXP shift_length conf /\
     gen_gc_partial_conf_gen_start gc_conf <= gen_gc_partial_conf_refs_start gc_conf /\
     gen_gc_partial_conf_refs_start gc_conf <= heap_length (gc_state_heap gcstate) /\
     (heap_segment (gen_gc_partial_conf_gen_start gc_conf,
                    gen_gc_partial_conf_refs_start gc_conf) (gc_state_heap gcstate) =
        SOME (old,current,refs)) /\
     heap_length (gc_state_heap gcstate) * (dimindex (:A) DIV 8) < dimword (:A) /\
     (word_heap (word_add curr (word_mul bytes_in_word (word (heap_length old))))
        current conf STAR misc_word_list pa xs STAR frame) (fun2set (m,dm)) /\
     (!t r. (gen_gc_partial_conf_isRef gc_conf (t,r) <=> isMutTag t)) /\
     (word_gen_gc_partial_move conf
        (word_addr conf x,word (gc_state_a gcstate),pa,curr,m,dm,
         word_mul bytes_in_word (word (gen_gc_partial_conf_gen_start gc_conf)),
         word_mul bytes_in_word (word (gen_gc_partial_conf_refs_start gc_conf))) =
       (w:A word_loc,i1,pa1,m1,c1)) /\
     LENGTH xs = gc_state_n gcstate ==>
     ?xs1 current1.
       (word_heap (word_add curr (word_mul bytes_in_word (word (heap_length old))))
          current1 conf STAR
        word_heap pa (gc_state_h2 gcstate1) conf STAR
        misc_word_list pa1 xs1 STAR frame) (fun2set (m1,dm)) /\
       (w = word_addr conf x1) /\
       heap_length (gc_state_heap gcstate1) = heap_length (gc_state_heap gcstate) /\
       (heap_segment (gen_gc_partial_conf_gen_start gc_conf,
                      gen_gc_partial_conf_refs_start gc_conf) (gc_state_heap gcstate1) =
          SOME (old,current1,refs)) /\
       c1 /\ (i1 = word (gc_state_a gcstate1)) /\ gc_state_n gcstate1 = LENGTH xs1 /\
       gc_state_n gcstate =
         heap_length (gc_state_h2 gcstate1) + gc_state_n gcstate1 +
         heap_length (gc_state_r4 gcstate1) /\
       pa1 = word_add pa (word_mul bytes_in_word
               (word (heap_length (gc_state_h2 gcstate1))))`,
  (REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `x:(A word_loc)heap_address` (cases "heap_address")) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (X_CHOOSE_THEN `ptr:num` (X_CHOOSE_THEN `dd:A word_loc` SUBST1_TAC))
    (X_CHOOSE_THEN `dv:A word_loc` SUBST1_TAC)) THENL
   [ALL_TAC;
    REWRITE_TAC[gen_gc_partial_gc_move_def; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MP_TAC(ISPEC `dv:A word_loc` (cases "word_loc")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:A word` SUBST_ALL_TAC)
      (X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `l2:num` SUBST_ALL_TAC))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[word_addr_def; word_gen_gc_partial_move_def; GCP1AUX_and_not_1;
                                PAIR_EQ]) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`xs:(A word_loc)list`; `current:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
    ASM_REWRITE_TAC[word_heap_def; SEP_CLAUSES; word_addr_def; heap_length_NIL;
                    WORD_MUL_0; WORD_ADD_0; ADD_CLAUSES]]) THEN
  (REWRITE_TAC[gen_gc_partial_gc_move_def; LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `ptr < gen_gc_partial_conf_gen_start (gc_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf) \/
                 gen_gc_partial_conf_refs_start gc_conf <= ptr` THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN GCP1AUX_SUBST_VARS_TAC ["x1";"gcstate1"] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
    REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
      free_in `gc_state_ok (gcstate:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` (concl th))) THEN
    SUBGOAL_THEN `ptr * 2 EXP shift_length conf < dimword(:A)` ASSUME_TAC THENL
     [MATCH_MP_TAC LE_DIV_LT_IMP THEN
      EXISTS_TAC `heap_length (gc_state_heap (gcstate:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`conf:data_to_word_config`; `curr:A word`; `ptr:num`; `dd:A word_loc`;
      `gen_gc_partial_conf_gen_start (gc_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf)`;
      `gen_gc_partial_conf_refs_start (gc_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf)`;
      `heap_length (gc_state_heap (gcstate:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))`] GCP1AUX_word_range_test) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
    GCP1AUX_UNDISCH_EQ "word_gen_gc_partial_move" THEN
    ASM_REWRITE_TAC[word_addr_def; word_gen_gc_partial_move_def; GCP1AUX_get_addr_and_1_not_0;
                    LET_DEF; LET_END_DEF; PAIR_EQ] THEN
    STRIP_TAC THEN GCP1AUX_SUBST_VARS_TAC ["w";"i1";"pa1";"m1";"c1"] THEN
    MAP_EVERY EXISTS_TAC [`xs:(A word_loc)list`; `current:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
    ASM_REWRITE_TAC[word_heap_def; SEP_CLAUSES; word_addr_def; heap_length_NIL;
                    WORD_MUL_0; WORD_ADD_0; ADD_CLAUSES];
    ALL_TAC]) THEN
  (MP_TAC(ISPEC `heap_lookup ptr (gc_state_heap (gcstate:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
               RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
               ASM_MESON_TAC[])
    (X_CHOOSE_THEN `el:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th] THEN CASE_REWRITE_TAC[]))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ptr * 2 EXP shift_length conf < dimword(:A)` ASSUME_TAC THENL
   [GCP1AUX_PTR_BOUND_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ptr < heap_length (gc_state_heap (gcstate:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[heap_lookup_LESS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `curr:A word`; `ptr:num`; `dd:A word_loc`;
    `gen_gc_partial_conf_gen_start (gc_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf)`;
    `gen_gc_partial_conf_refs_start (gc_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf)`;
    `heap_length (gc_state_heap (gcstate:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state))`] GCP1AUX_word_range_test) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  GCP1AUX_UNDISCH_EQ "word_gen_gc_partial_move" THEN
  ASM_REWRITE_TAC[word_addr_def; word_gen_gc_partial_move_def; GCP1AUX_get_addr_and_1_not_0;
                  LET_DEF; LET_END_DEF] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`gc_state_heap (gcstate:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`;
    `gen_gc_partial_conf_gen_start (gc_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf)`;
    `gen_gc_partial_conf_refs_start (gc_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf)`;
    `old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `current:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `refs:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `ptr:num`; `el:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element`] GCP1AUX_heap_segment_lookup) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` (X_CHOOSE_THEN `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` STRIP_ASSUME_TAC)) THEN
  GCP1AUX_SUBST_LVARS_TAC ["current";"ptr"] THEN
  FIRST_X_ASSUM(fun th -> if lhs (concl th) = `heap_length (old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)` then ASSUME_TAC (SYM th)
                          else failwith "") THEN
  FIRST_X_ASSUM(fun th -> if gcp1_is_app "word_gen_gc_partial_move" (lhs (concl th)) then failwith "" else
     if is_eq (concl th) && free_in `w:A word_loc` (rhs (concl th)) then
     MP_TAC th else failwith "") THEN
  SIMP_TAC[GCP1AUX_ptr_to_addr_split; ASSUME `(heap_length (old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) + heap_length (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)) *
                                               2 EXP shift_length conf < dimword (:A)`] THEN
  DISCH_TAC) THEN
  (MP_TAC(ISPEC `el:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `u:num` SUBST_ALL_TAC)
    (DISJ_CASES_THEN2
      (X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `pd:A word_loc`
         (X_CHOOSE_THEN `l:num` SUBST_ALL_TAC)))
      (X_CHOOSE_THEN `ys:((A word_loc)heap_address)list` (X_CHOOSE_THEN `l:num`
         (X_CHOOSE_THEN `tg:data_to_word_memoryProof_tag#(A word_loc)list`
            SUBST_ALL_TAC))))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in is_eq c &&
     rhs c = `x1:(A word_loc)heap_address, gcstate1:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state`)) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN ASM_MESON_TAC[];
    (STRIP_TAC THEN GCP1AUX_SUBST_VARS_TAC ["x1";"gcstate1"] THEN
  FIRST_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) then
     ASSUME_TAC (REWRITE_RULE[word_heap_APPEND; word_heap_def; word_el_def] th)
     else NO_TAC) THEN
  GCP1AUX_SEP_R_TAC THEN
  GCP1AUX_UNDISCH_EQ "COND" THEN
  ASM_REWRITE_TAC[is_fws_ptr_OR_3; theWord_def; GCP1AUX_update_addr_fwd; PAIR_EQ] THEN
  STRIP_TAC THEN GCP1AUX_SUBST_VARS_TAC ["w";"i1";"pa1";"m1";"c1"] THEN
  MAP_EVERY EXISTS_TAC [`xs:(A word_loc)list`;
    `APPEND ha (CONS (ForwardPointer p pd l) hb):((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
  ASM_REWRITE_TAC[word_heap_def; SEP_CLAUSES; word_addr_def; heap_length_NIL;
                  WORD_MUL_0; WORD_ADD_0; ADD_CLAUSES]);
    ((MP_TAC(ISPEC `tg:data_to_word_memoryProof_tag#(A word_loc)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `tag:data_to_word_memoryProof_tag`
    (X_CHOOSE_THEN `qs:(A word_loc)list` SUBST_ALL_TAC)) THEN
  SUBGOAL_THEN `!okk. gc_forward_ptr (heap_length (old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) + heap_length (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))
      (gc_state_heap (gcstate:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) (gc_state_a gcstate) (dd:A word_loc) okk =
      (APPEND (APPEND old (APPEND ha (CONS (ForwardPointer (gc_state_a gcstate) dd l) hb))) refs,
       okk)` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN REWRITE_TAC[APPEND_ASSOC] THEN
    REWRITE_TAC[GSYM heap_length_APPEND; gc_forward_ptr_thm];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  GCP1AUX_SUBST_VARS_TAC ["x1";"gcstate1"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
    free_in `gc_state_ok (gcstate:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)` (concl th)))) THEN
  (SUBGOAL_THEN `~isMutTag tag` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) then
     let wh = hd (gcp1_star_leaves (rator (concl th))) in
     MP_TAC(MATCH_MP GCP1AUX_heap_el_read (GCP1AUX_STAR_FRONT [wh] th)) else NO_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:A word` (X_CHOOSE_THEN `ts:(A word_loc)list`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NOT_is_fwd_ptr) THEN
  GCP1AUX_UNDISCH_EQ "COND" THEN
  ASM_REWRITE_TAC[theWord_def; isWord_def; GCP1AUX_update_addr_word] THEN
  REWRITE_TAC[GSYM WORD_ADD; GSYM ADD_ASSOC] THEN
  GCP1AUX_SPLITN_TAC "memcpy" ["pa2";"m2";"c2"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  GCP1AUX_SUBST_VARS_TAC ["w";"i1";"pa1";"m1";"c1"]) THEN
  (MP_TAC(ISPECL [`l + 1`; `xs:(A word_loc)list`] LESS_EQ_IMP_APPEND) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ys0:(A word_loc)list` (X_CHOOSE_THEN `zs:(A word_loc)list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_to_word_memoryProof_word_list_APPEND; LENGTH_APPEND]) THEN
  FIRST_X_ASSUM(fun th -> if gcp1_is_fun2set_asm (concl th) then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`;
    `word_add (curr:A word) (word_mul bytes_in_word (word (heap_length (old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))))`;
    `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `ys:((A word_loc)heap_address)list`; `l:num`; `tag:data_to_word_memoryProof_tag`;
    `qs:(A word_loc)list`; `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `pa:A word`;
    `ys0:(A word_loc)list`; `m:A word->A word_loc`; `dm:A word->bool`;
    `gc_state_a (gcstate:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)`; `dd:A word_loc`; `h:A word`;
    `ts:(A word_loc)list`; `pa2:A word`; `m2:A word->A word_loc`; `c2:bool`]
    GCP1AUX_heap_el_copy) THEN
  GCP1AUX_SEP_FRAME_TAC THEN
  ASM_SIMP_TAC[GCP1AUX_len_bound] THEN STRIP_TAC THEN
  SUBGOAL_THEN `heap_segment (heap_length (old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list),
       gen_gc_partial_conf_refs_start (gc_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf))
     (APPEND (APPEND old (APPEND ha (CONS (ForwardPointer (gc_state_a (gcstate:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) (dd:A word_loc) l) hb))) refs) =
     SOME (old, APPEND ha (CONS (ForwardPointer (gc_state_a gcstate) dd l) hb), refs)` ASSUME_TAC THENL
   [SUBGOAL_THEN `gen_gc_partial_conf_refs_start (gc_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf) =
        heap_length (APPEND (old:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) (APPEND ha (CONS (ForwardPointer (gc_state_a (gcstate:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) (dd:A word_loc) l) hb)))`
      SUBST1_TAC THENL
     [FIRST_ASSUM(fun th -> if is_eq (concl th) &&
          rhs (concl th) = `gen_gc_partial_conf_refs_start (gc_conf:(data_to_word_memoryProof_tag#(A word_loc)list)gen_gc_partial_conf)` &&
          gcp1_is_app "heap_length" (lhs (concl th)) then SUBST1_TAC (SYM th) else failwith "") THEN
      REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def];
      REWRITE_TAC[GCP1AUX_heap_segment_APPEND]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`zs:(A word_loc)list`;
    `APPEND ha (CONS (ForwardPointer (gc_state_a (gcstate:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)gc_state)) (dd:A word_loc) l) hb):((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_heap_def; SEP_CLAUSES]) THEN
  ASM_REWRITE_TAC[word_heap_def; SEP_CLAUSES; word_addr_def; APPEND;
                  heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def;
                  heap_length_NIL; ADD_CLAUSES] THEN
  REPEAT CONJ_TAC THENL
   [GCP1AUX_SEP_AC_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def]) THEN
    GCP1AUX_ARITH_TAC;
    GCP1AUX_ARITH_TAC;
    GCP1AUX_ARITH_TAC;
    REWRITE_TAC[WORD_MUL_SYM]]))]));;

(* HOL4 line 2780 *)
let gc_partial_move_ok_irr = prove
 (`!x (s:(A,B)gc_state) y1 y2 t1 t2 h2 r4 gen_conf.
     gen_gc_partial_gc_move gen_conf s x = (y1,t1) /\
     gen_gc_partial_gc_move gen_conf
       (gc_state_h2_fupd (K h2) (gc_state_r4_fupd (K r4) s)) x = (y2,t2) ==>
     y1 = y2 /\ ?x1 x2. t2 = gc_state_h2_fupd (K x1) (gc_state_r4_fupd (K x2) t1)`,
  GEN_TAC THEN CASES_ON `x:A heap_address` THEN
  REWRITE_TAC[gen_gc_partial_gc_move_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  SIMP[] THEN EVERY_CASE_TAC THEN REPEAT PAIRARG_TAC THEN
  RW[gc_state_component_equality] THEN ASM_MESON_TAC[]);;

(* HOL4 line 2792 *)
let gc_partial_move_ok_before = prove
 (`!gen_conf (s:(A,B)gc_state) x x1 s1.
     gen_gc_partial_gc_move gen_conf s x = (x1,s1) /\ gc_state_ok s1 ==> gc_state_ok s`,
  MATCH_ACCEPT_TAC gc_move_ok');;

(* HOL4 line 2811 *)
let gc_partial_move_list_ok_before = prove
 (`!x (s:(A,B)gc_state) x1 s1 gen_conf.
     gen_gc_partial_gc_move_list gen_conf s x = (x1,s1) /\ gc_state_ok s1 ==>
     gc_state_ok s`,
  MESON_TAC[gc_move_list_ok']);;

(* HOL4 line 2818 *)
let gc_partial_move_ref_list_ok_before = prove
 (`!x (s:(A,B)gc_state) (x1:((A,C)heap_element)list) s1 gen_conf.
     gc_move_ref_list gen_conf s x = (x1,s1) /\ gc_state_ok s1 ==> gc_state_ok s`,
  MESON_TAC[gc_move_ref_list_ok']);;

(* HOL4 line 2825 *)
let gc_partial_move_data_ok_before = prove
 (`!gen_conf (s:(A,B)gc_state) s1.
     gen_gc_partial_gc_move_data gen_conf s = s1 /\ gc_state_ok s1 ==> gc_state_ok s`,
  MESON_TAC[gc_move_data_ok']);;

(* HOL4 line 2835 *)
let gc_partial_move_list_ok_irr = prove
 (`!x (s:(A,B)gc_state) y1 y2 t1 t2 h2 r4 gen_conf.
     gen_gc_partial_gc_move_list gen_conf s x = (y1,t1) /\ gc_state_ok t1 /\
     gen_gc_partial_gc_move_list gen_conf
       (gc_state_h2_fupd (K h2) (gc_state_r4_fupd (K r4) s)) x = (y2,t2) ==>
     gc_state_ok t2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_partial_gc_move_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN SIMP[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  GCP1AUX_TUPLE_TAC `gen_gc_partial_gc_move (gen_conf:B gen_gc_partial_conf) (s:(A,B)gc_state) h`
    ["z1";"s1"] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_partial_gc_move_list (gen_conf:B gen_gc_partial_conf) (s1:(A,B)gc_state) t`
    ["zs1";"u1"] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_partial_gc_move (gen_conf:B gen_gc_partial_conf)
     (gc_state_h2_fupd (K h2) (gc_state_r4_fupd (K r4) (s:(A,B)gc_state))) h` ["z2";"s2"] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_partial_gc_move_list (gen_conf:B gen_gc_partial_conf) (s2:(A,B)gc_state) t`
    ["zs2";"u2"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`h:A heap_address`; `s:(A,B)gc_state`; `z1:A heap_address`; `z2:A heap_address`;
    `s1:(A,B)gc_state`; `s2:(A,B)gc_state`; `h2:((A,B)heap_element)list`;
    `r4:((A,B)heap_element)list`; `gen_conf:B gen_gc_partial_conf`] gc_partial_move_ok_irr) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 2861 *)
let gc_partial_move_list_ok_irr' = prove
 (`!x (s:(A,B)gc_state) y1 y2 t1 t2 h2 r4 gen_conf.
     gen_gc_partial_gc_move_list gen_conf s x = (y1,t1) /\
     gen_gc_partial_gc_move_list gen_conf
       (gc_state_h2_fupd (K h2) (gc_state_r4_fupd (K r4) s)) x = (y2,t2) ==>
     y1 = y2 /\ ?x1 x2. t2 = gc_state_h2_fupd (K x1) (gc_state_r4_fupd (K x2) t1)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_partial_gc_move_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`h2:((A,B)heap_element)list`; `r4:((A,B)heap_element)list`] THEN
    REFL_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  GCP1AUX_TUPLE_TAC `gen_gc_partial_gc_move (gen_conf:B gen_gc_partial_conf) (s:(A,B)gc_state) h`
    ["z1";"s1"] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_partial_gc_move_list (gen_conf:B gen_gc_partial_conf) (s1:(A,B)gc_state) t`
    ["zs1";"u1"] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_partial_gc_move (gen_conf:B gen_gc_partial_conf)
     (gc_state_h2_fupd (K h2) (gc_state_r4_fupd (K r4) (s:(A,B)gc_state))) h` ["z2";"s2"] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_partial_gc_move_list (gen_conf:B gen_gc_partial_conf) (s2:(A,B)gc_state) t`
    ["zs2";"u2"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`h:A heap_address`; `s:(A,B)gc_state`; `z1:A heap_address`; `z2:A heap_address`;
    `s1:(A,B)gc_state`; `s2:(A,B)gc_state`; `h2:((A,B)heap_element)list`;
    `r4:((A,B)heap_element)list`; `gen_conf:B gen_gc_partial_conf`] gc_partial_move_ok_irr) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s1:(A,B)gc_state`; `zs1:(A heap_address)list`;
    `zs2:(A heap_address)list`; `t1:(A,B)gc_state`; `t2:(A,B)gc_state`;
    `x1:((A,B)heap_element)list`; `x2:((A,B)heap_element)list`;
    `gen_conf:B gen_gc_partial_conf`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4 line 2875 *)
let gc_partial_move_ref_list_ok_irr = prove
 (`!x (s:(A,B)gc_state) (y1:((A,C)heap_element)list) y2 t1 t2 h2 r4 gen_conf.
     gc_move_ref_list gen_conf s x = (y1,t1) /\ gc_state_ok t1 /\
     gc_move_ref_list gen_conf
       (gc_state_h2_fupd (K h2) (gc_state_r4_fupd (K r4) s)) x = (y2,t2) ==>
     gc_state_ok t2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN SIMP[]; ALL_TAC] THEN
  MP_TAC(ISPEC `h:(A,C)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  GCP1AUX_TUPLE_TAC `gen_gc_partial_gc_move_list (gen_conf:B gen_gc_partial_conf)
     (s:(A,B)gc_state) a0` ["p1";"s1"] THEN
  GCP1AUX_TUPLE_TAC `gc_move_ref_list (gen_conf:B gen_gc_partial_conf) (s1:(A,B)gc_state)
     (t:((A,C)heap_element)list)` ["r1";"u1"] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_partial_gc_move_list (gen_conf:B gen_gc_partial_conf)
     (gc_state_h2_fupd (K h2) (gc_state_r4_fupd (K r4) (s:(A,B)gc_state))) a0` ["p2";"s2"] THEN
  GCP1AUX_TUPLE_TAC `gc_move_ref_list (gen_conf:B gen_gc_partial_conf) (s2:(A,B)gc_state)
     (t:((A,C)heap_element)list)` ["r2";"u2"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`a0:(A heap_address)list`; `s:(A,B)gc_state`; `p1:(A heap_address)list`;
    `p2:(A heap_address)list`; `s1:(A,B)gc_state`; `s2:(A,B)gc_state`;
    `h2:((A,B)heap_element)list`; `r4:((A,B)heap_element)list`;
    `gen_conf:B gen_gc_partial_conf`] gc_partial_move_list_ok_irr') THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 2901 *)
let gc_partial_move_with_NIL = prove
 (CASE_TERM
  `!x (s:(A,B)gc_state) y t gen_conf.
     gen_gc_partial_gc_move gen_conf s x = (y,t) /\ gc_state_ok t ==>
     (let (y,s1) = gen_gc_partial_gc_move gen_conf
                     (gc_state_h2_fupd (K []) (gc_state_r4_fupd (K []) s)) x in
      (y,gc_state_h2_fupd (K (APPEND (gc_state_h2 s) (gc_state_h2 s1)))
           (gc_state_r4_fupd (K (APPEND (gc_state_r4 s1) (gc_state_r4 s))) s1))) =
     (y,t)`,
  GEN_TAC THEN CASES_ON `x:A heap_address` THEN
  REWRITE_TAC[gen_gc_partial_gc_move_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  SIMP[] THEN EVERY_CASE_TAC THEN REPEAT PAIRARG_TAC THEN
  RW[gc_state_component_equality; APPEND_NIL; APPEND] THEN ASM_MESON_TAC[]);;

(* HOL4 line 2917 (the unused bound variables y t h2 r4 are left out) *)
let gc_partial_move_with_NIL_LEMMA = prove
 (`!x (s:(A,B)gc_state) y1 t1 gen_conf.
     gen_gc_partial_gc_move gen_conf s x = (y1,t1) /\ gc_state_ok t1 ==>
     ?x1 x2.
       gc_state_h2 t1 = APPEND (gc_state_h2 s) x1 /\
       gc_state_r4 t1 = APPEND x2 (gc_state_r4 s) /\
       gen_gc_partial_gc_move gen_conf
         (gc_state_h2_fupd (K []) (gc_state_r4_fupd (K []) s)) x =
         (y1,gc_state_h2_fupd (K x1) (gc_state_r4_fupd (K x2) t1))`,
  GEN_TAC THEN CASES_ON `x:A heap_address` THEN
  REWRITE_TAC[gen_gc_partial_gc_move_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  SIMP[] THEN EVERY_CASE_TAC THEN REPEAT PAIRARG_TAC THEN
  RW[gc_state_component_equality; APPEND_NIL; APPEND] THEN
  TRY(ASM_MESON_TAC[]) THEN
  ASM_MESON_TAC[APPEND_NIL; APPEND]);;

(* HOL4 line 2935 (HOL4: Q.prove ... |> SIMP_RULE std_ss [], which drops    *)
(* the unused bound variables y t h2 r4)                                    *)
let gc_partial_move_list_with_NIL_LEMMA = prove
 (`!x (s:(A,B)gc_state) y1 t1 gen_conf.
     gen_gc_partial_gc_move_list gen_conf s x = (y1,t1) /\ gc_state_ok t1 ==>
     ?x1 x2.
       gc_state_h2 t1 = APPEND (gc_state_h2 s) x1 /\
       gc_state_r4 t1 = APPEND x2 (gc_state_r4 s) /\
       gen_gc_partial_gc_move_list gen_conf
         (gc_state_h2_fupd (K []) (gc_state_r4_fupd (K []) s)) x =
         (y1,gc_state_h2_fupd (K x1) (gc_state_r4_fupd (K x2) t1))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_partial_gc_move_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`[]:((A,B)heap_element)list`; `[]:((A,B)heap_element)list`] THEN
    REWRITE_TAC[APPEND_NIL; APPEND]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  GCP1AUX_TUPLE_TAC `gen_gc_partial_gc_move (gen_conf:B gen_gc_partial_conf) (s:(A,B)gc_state) h` ["z1";"s1"] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_partial_gc_move_list (gen_conf:B gen_gc_partial_conf) (s1:(A,B)gc_state) t` ["zs1";"u1"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `gc_state_ok (s1:(A,B)gc_state)` ASSUME_TAC THENL
   [MATCH_MP_TAC gc_partial_move_list_ok_before THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A heap_address`; `s:(A,B)gc_state`; `z1:A heap_address`;
    `s1:(A,B)gc_state`; `gen_conf:B gen_gc_partial_conf`] gc_partial_move_with_NIL_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:((A,B)heap_element)list` (X_CHOOSE_THEN
    `e1:((A,B)heap_element)list` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(fun ih -> GCP1AUX_ASM_MP (SPECL [`s1:(A,B)gc_state`; `zs1:(A heap_address)list`;
    `t1:(A,B)gc_state`; `gen_conf:B gen_gc_partial_conf`] ih)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:((A,B)heap_element)list` (X_CHOOSE_THEN
    `e2:((A,B)heap_element)list` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  GCP1AUX_TUPLE_TAC `gen_gc_partial_gc_move_list (gen_conf:B gen_gc_partial_conf)
    (gc_state_h2_fupd (K d1) (gc_state_r4_fupd (K e1) (s1:(A,B)gc_state))) t` ["zs3";"u3"] THEN
  SUBGOAL_THEN `gc_state_ok (u3:(A,B)gc_state)` ASSUME_TAC THENL
   [MATCH_MP_TAC gc_partial_move_list_ok_irr THEN
    MAP_EVERY EXISTS_TAC [`t:(A heap_address)list`; `s1:(A,B)gc_state`;
      `zs1:(A heap_address)list`; `zs3:(A heap_address)list`; `t1:(A,B)gc_state`;
      `d1:((A,B)heap_element)list`; `e1:((A,B)heap_element)list`; `gen_conf:B gen_gc_partial_conf`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun ih -> GCP1AUX_ASM_MP (SPECL [`gc_state_h2_fupd (K d1)
    (gc_state_r4_fupd (K e1) (s1:(A,B)gc_state))`; `zs3:(A heap_address)list`;
    `u3:(A,B)gc_state`; `gen_conf:B gen_gc_partial_conf`] ih)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:((A,B)heap_element)list` (X_CHOOSE_THEN
    `e3:((A,B)heap_element)list` STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  FIRST_X_ASSUM(fun th15 -> if free_in `zs3:(A heap_address)list` (concl th15) &&
      free_in `d3:((A,B)heap_element)list` (concl th15) then
      FIRST_X_ASSUM(fun th10 -> if free_in `zs1:(A heap_address)list` (concl th10) &&
          free_in `d2:((A,B)heap_element)list` (concl th10) &&
          gcp1_is_app "gen_gc_partial_gc_move_list" (lhs (concl th10)) then
          MP_TAC (TRANS (SYM th15) th10) else failwith "")
    else failwith "") THEN
  REWRITE_TAC[PAIR_EQ; gc_state_component_equality] THEN SIMP[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`APPEND d1 d2:((A,B)heap_element)list`;
                        `APPEND e2 e1:((A,B)heap_element)list`] THEN
  ASM_REWRITE_TAC[APPEND_ASSOC; gc_state_component_equality] THEN SIMP[]);;

(* HOL4 line 2957 *)
let gc_partial_move_list_with_NIL = prove
 (CASE_TERM
  `!x (s:(A,B)gc_state) y t gen_conf.
     gen_gc_partial_gc_move_list gen_conf s x = (y,t) /\ gc_state_ok t ==>
     (let (y,s1) = gen_gc_partial_gc_move_list gen_conf
                     (gc_state_h2_fupd (K []) (gc_state_r4_fupd (K []) s)) x in
      (y,gc_state_h2_fupd (K (APPEND (gc_state_h2 s) (gc_state_h2 s1)))
           (gc_state_r4_fupd (K (APPEND (gc_state_r4 s1) (gc_state_r4 s))) s1))) =
     (y,t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP gc_partial_move_list_with_NIL_LEMMA) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:((A,B)heap_element)list` (X_CHOOSE_THEN
    `x2:((A,B)heap_element)list` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  ASM_REWRITE_TAC[gc_state_component_equality] THEN SIMP[]);;

(* HOL4 line 2967 (HOL4: Q.prove ... |> SIMP_RULE std_ss [], which drops    *)
(* the unused bound variables y t h2 r4)                                    *)
let gc_partial_move_ref_list_with_NIL_LEMMA = prove
 (`!x (s:(A,B)gc_state) (y1:((A,C)heap_element)list) t1 gen_conf.
     gc_move_ref_list gen_conf s x = (y1,t1) /\ gc_state_ok t1 ==>
     ?x1 x2.
       gc_state_h2 t1 = APPEND (gc_state_h2 s) x1 /\
       gc_state_r4 t1 = APPEND x2 (gc_state_r4 s) /\
       gc_move_ref_list gen_conf
         (gc_state_h2_fupd (K []) (gc_state_r4_fupd (K []) s)) x =
         (y1,gc_state_h2_fupd (K x1) (gc_state_r4_fupd (K x2) t1))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`[]:((A,B)heap_element)list`; `[]:((A,B)heap_element)list`] THEN
    REWRITE_TAC[APPEND_NIL; APPEND]; ALL_TAC] THEN
  MP_TAC(ISPEC `h:(A,C)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  GCP1AUX_TUPLE_TAC `gen_gc_partial_gc_move_list (gen_conf:B gen_gc_partial_conf)
     (s:(A,B)gc_state) a0` ["z1";"s1"] THEN
  GCP1AUX_TUPLE_TAC `gc_move_ref_list (gen_conf:B gen_gc_partial_conf) (s1:(A,B)gc_state)
     (t:((A,C)heap_element)list)` ["zs1";"u1"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `gc_state_ok (s1:(A,B)gc_state)` ASSUME_TAC THENL
   [MATCH_MP_TAC gc_partial_move_ref_list_ok_before THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a0:(A heap_address)list`; `s:(A,B)gc_state`; `z1:(A heap_address)list`;
    `s1:(A,B)gc_state`; `gen_conf:B gen_gc_partial_conf`]
    gc_partial_move_list_with_NIL_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:((A,B)heap_element)list` (X_CHOOSE_THEN
    `e1:((A,B)heap_element)list` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(fun ih -> GCP1AUX_ASM_MP (SPECL [`s1:(A,B)gc_state`;
    `zs1:((A,C)heap_element)list`;
    `t1:(A,B)gc_state`; `gen_conf:B gen_gc_partial_conf`] ih)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:((A,B)heap_element)list` (X_CHOOSE_THEN
    `e2:((A,B)heap_element)list` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  GCP1AUX_TUPLE_TAC `gc_move_ref_list (gen_conf:B gen_gc_partial_conf)
    (gc_state_h2_fupd (K d1) (gc_state_r4_fupd (K e1) (s1:(A,B)gc_state)))
    (t:((A,C)heap_element)list)` ["zs3";"u3"] THEN
  SUBGOAL_THEN `gc_state_ok (u3:(A,B)gc_state)` ASSUME_TAC THENL
   [MATCH_MP_TAC gc_partial_move_ref_list_ok_irr THEN
    MAP_EVERY EXISTS_TAC [`t:((A,C)heap_element)list`; `s1:(A,B)gc_state`;
      `zs1:((A,C)heap_element)list`; `zs3:((A,C)heap_element)list`; `t1:(A,B)gc_state`;
      `d1:((A,B)heap_element)list`; `e1:((A,B)heap_element)list`;
      `gen_conf:B gen_gc_partial_conf`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun ih -> GCP1AUX_ASM_MP (SPECL [`gc_state_h2_fupd (K d1)
    (gc_state_r4_fupd (K e1) (s1:(A,B)gc_state))`; `zs3:((A,C)heap_element)list`;
    `u3:(A,B)gc_state`; `gen_conf:B gen_gc_partial_conf`] ih)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:((A,B)heap_element)list` (X_CHOOSE_THEN
    `e3:((A,B)heap_element)list` STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  FIRST_X_ASSUM(fun th15 -> if free_in `zs3:((A,C)heap_element)list` (concl th15) &&
      free_in `d3:((A,B)heap_element)list` (concl th15) then
      FIRST_X_ASSUM(fun th10 -> if free_in `zs1:((A,C)heap_element)list` (concl th10) &&
          free_in `d2:((A,B)heap_element)list` (concl th10) &&
          gcp1_is_app "gc_move_ref_list" (lhs (concl th10)) then
          MP_TAC (TRANS (SYM th15) th10) else failwith "")
    else failwith "") THEN
  REWRITE_TAC[PAIR_EQ; gc_state_component_equality] THEN SIMP[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`APPEND d1 d2:((A,B)heap_element)list`;
                        `APPEND e2 e1:((A,B)heap_element)list`] THEN
  ASM_REWRITE_TAC[APPEND_ASSOC; gc_state_component_equality] THEN SIMP[]);;

(* HOL4 line 2991 *)
let gc_partial_move_ref_list_with_NIL = prove
 (CASE_TERM
  `!x (s:(A,B)gc_state) (y:((A,C)heap_element)list) t gen_conf.
     gc_move_ref_list gen_conf s x = (y,t) /\ gc_state_ok t ==>
     (let (y,s1) = gc_move_ref_list gen_conf
                     (gc_state_h2_fupd (K []) (gc_state_r4_fupd (K []) s)) x in
      (y,gc_state_h2_fupd (K (APPEND (gc_state_h2 s) (gc_state_h2 s1)))
           (gc_state_r4_fupd (K (APPEND (gc_state_r4 s1) (gc_state_r4 s))) s1))) =
     (y,t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP gc_partial_move_ref_list_with_NIL_LEMMA) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:((A,B)heap_element)list` (X_CHOOSE_THEN
    `x2:((A,B)heap_element)list` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  ASM_REWRITE_TAC[gc_state_component_equality] THEN SIMP[]);;
