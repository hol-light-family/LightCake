(* ========================================================================= *)
(* data_to_word_memoryProof_p4: part 4 of 7 (HOL4 lines 8235-10991) of the   *)
(* port of HOL4 compiler/backend/proofs/data_to_word_memoryProofScript.sml   *)
(* (CakeML v3479).  Part of the correctness proof for data_to_word.          *)
(* The parts _p1 ... _p7 are loaded one after the other (each needs the     *)
(* previous one); data_to_word_memoryProof.ml needs the last.                *)
(* MP4AUX_ names are local helpers of this part.                            *)
(* ========================================================================= *)

needs "compiler/backend/proofs/data_to_word_memoryProof_p3.ml";;

prioritize_num();;
type_invention_error := true;;
(* ------------------------------------------------------------------------- *)
(* Helpers (MP4AUX_ names, mp4_ functions): see the comments at each.       *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Separation-logic helpers (the work of HOL4 helperLib's SEP_R_TAC,         *)
(* SEP_W_TAC, SEP_F_TAC and of fs [AC STAR_ASSOC STAR_COMM]).                *)
(* An assertion is a left-associated STAR tree; its leaves are compared up   *)
(* to alpha-conversion.                                                      *)
(* ------------------------------------------------------------------------- *)

let MP4AUX_write_fun2set_one = prove
 (`!(y:A) (a:B) x f d.
     set_sep_one (a,x) (fun2set (f,d))
     ==> set_sep_one (a,y) (fun2set ((a =+ y) f,d))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!(p:(B#A->bool)->bool) s. p s <=> (p STAR emp) s`
    (fun th -> ONCE_REWRITE_TAC[th]) THENL [REWRITE_TAC[SEP_CLAUSES]; ALL_TAC] THEN
  REWRITE_TAC[one_fun2set; APPLY_UPDATE_THM; emp_def; fun2set_EMPTY] THEN
  SIMP_TAC[]);;

let mp4_is_star tm =
  try let f,_ = dest_comb tm in
      let s,_ = dest_comb f in
      is_const s && fst(dest_const s) = "STAR"
  with Failure _ -> false;;

let rec mp4_star_leaves tm =
  if mp4_is_star tm then mp4_star_leaves (rand(rator tm)) @ mp4_star_leaves (rand tm)
  else [tm];;

let mp4_mk_star p q =
  let x = fst(dest_fun_ty(fst(dest_fun_ty(type_of p)))) in
  mk_comb(mk_comb(mk_const("STAR",[x,`:A`]),p),q);;

let mp4_list_mk_star l =
  match l with
    [] -> failwith "mp4_list_mk_star"
  | h::t -> rev_itlist (fun x acc -> mp4_mk_star acc x) t h;;

let mp4_is_app name tm =
  try let f,_ = strip_comb tm in is_const f && fst(dest_const f) = name
  with Failure _ -> false;;

let mp4_is_one tm =
  try let f,_ = dest_comb tm in is_const f && fst(dest_const f) = "set_sep_one"
  with Failure _ -> false;;

let rec mp4_remove_first p l =
  match l with
    [] -> failwith "mp4_remove_first"
  | h::t -> if p h then t else h :: mp4_remove_first p t;;

(* |- p = q for STAR trees p, q equal up to AC *)
let MP4AUX_STAR_AC_EQ p q =
  if aconv p q then REFL p else AC LSORTAUX_STAR_AC (mk_eq(p,q));;

(* th : |- p s  ->  |- q s  (p, q equal up to AC) *)
let MP4AUX_STAR_AC_RULE q th =
  let p,s = dest_comb(concl th) in
  EQ_MP (AP_THM (MP4AUX_STAR_AC_EQ p q) s) th;;

(* th : |- p s; puts the first leaf satisfying pr in front:                 *)
(*   |- (leaf STAR rest) s   (rest a left-associated STAR of the others)     *)
let MP4AUX_STAR_FOCUS pr th =
  let p,s = dest_comb(concl th) in
  let leaves = mp4_star_leaves p in
  let leaf = find pr leaves in
  let rest = mp4_remove_first (fun l -> l == leaf) leaves in
  MP4AUX_STAR_AC_RULE (mp4_mk_star leaf (mp4_list_mk_star rest)) th;;

(* the same, the leaves selected (in this order) put in front *)
let MP4AUX_STAR_FOCUS_LIST prs th =
  let p,s = dest_comb(concl th) in
  let leaves = mp4_star_leaves p in
  let rec pick prs ls =
    match prs with
      [] -> [],ls
    | pr::prs' -> let l = find pr ls in
                  let ls' = mp4_remove_first (fun x -> x == l) ls in
                  let a,b = pick prs' ls' in l::a,b in
  let front,rest = pick prs leaves in
  let q = if rest = [] then mp4_list_mk_star front
          else mp4_mk_star (mp4_list_mk_star front) (mp4_list_mk_star rest) in
  MP4AUX_STAR_AC_RULE q th;;

(* reading: th : |- p (fun2set (m,dm)) gives |- m a = x /\ a IN dm for     *)
(* every leaf set_sep_one (a,x) of p                                        *)
let MP4AUX_SEP_READS th =
  let p,s = dest_comb(concl th) in
  let leaves = mp4_star_leaves p in
  let ones = filter mp4_is_one leaves in
  if length leaves = 1 then
    (if ones = [] then [] else [MATCH_MP one_fun2set_IMP th])
  else
    map (fun leaf ->
           let rest = mp4_remove_first (fun l -> l == leaf) leaves in
           let th1 = MP4AUX_STAR_AC_RULE
                       (mp4_mk_star leaf (mp4_list_mk_star rest)) th in
           MATCH_MP read_fun2set th1) ones;;

let mp4_is_fun2set_asm tm =
  try let _,s = dest_comb tm in
      let f,_ = dest_comb s in
      is_const f && fst(dest_const f) = "fun2set"
  with Failure _ -> false;;

(* HOL4 SEP_R_TAC: the reads of every fun2set assumption as assumptions   *)
let MP4AUX_SEP_R_TAC : tactic = fun (asl,w as g) ->
  let ths = flat (map (fun (_,th) ->
                   if mp4_is_fun2set_asm (concl th)
                   then (try MP4AUX_SEP_READS th with Failure _ -> [])
                   else []) asl) in
  let ths = flat (map CONJUNCTS ths) in
  let ths = filter (fun th -> not (exists (fun (_,a) -> aconv (concl a) (concl th)) asl))
                   ths in
  MAP_EVERY ASSUME_TAC ths g;;

(* writing: th : |- p (fun2set (m,dm)) with a leaf set_sep_one (a,x) gives *)
(* |- p' (fun2set ((a =+ y) m,dm)), p' = p with that leaf set_sep_one (a,y) *)
let MP4AUX_SEP_WRITE a y th =
  let p,s = dest_comb(concl th) in
  let leaves = mp4_star_leaves p in
  let leaf = find (fun l -> mp4_is_one l && aconv (fst(dest_pair(rand l))) a) leaves in
  let newleaf = mk_comb(rator leaf,mk_pair(a,y)) in
  let leaves' = map (fun l -> if l == leaf then newleaf else l) leaves in
  if length leaves = 1 then
    SPEC y (MATCH_MP MP4AUX_write_fun2set_one th)
  else
    let rest = mp4_remove_first (fun l -> l == leaf) leaves in
    let th1 = MP4AUX_STAR_AC_RULE (mp4_mk_star leaf (mp4_list_mk_star rest)) th in
    let th2 = SPEC y (MATCH_MP write_fun2set th1) in
    MP4AUX_STAR_AC_RULE (mp4_list_mk_star leaves') th2;;

(* the updates of an update chain (a1 =+ y1) ((a2 =+ y2) ... m), outermost *)
(* first, and m                                                              *)
let rec mp4_dest_updates tm =
  try let f,m = dest_comb tm in
      let g,y = dest_comb f in
      let u,a = dest_comb g in
      if is_const u && fst(dest_const u) = "=+" then
        let l,m0 = mp4_dest_updates m in (a,y)::l,m0
      else [],tm
  with Failure _ -> [],tm;;

(* th : |- p (fun2set (m,dm)); upd an update chain over m: the assertion    *)
(* with the written leaves, on fun2set (upd,dm)                             *)
let MP4AUX_SEP_WRITES upd th =
  let ups,_ = mp4_dest_updates upd in
  rev_itlist (fun (a,y) th -> MP4AUX_SEP_WRITE a y th) (rev ups) th;;

(* HOL4 SEP_W_TAC: for a fun2set assumption over m and the biggest update  *)
(* chain over m in the goal, the written assertion as a new assumption     *)
let MP4AUX_SEP_W_TAC : tactic = fun (asl,w as g) ->
  let cands = filter (fun (_,th) -> mp4_is_fun2set_asm (concl th)) asl in
  let try_one (_,th) =
    let _,s = dest_comb(concl th) in
    let m = lhand(rand s) in
    let ups = find_terms (fun t -> let l,m0 = mp4_dest_updates t in
                                   l <> [] && aconv m0 m) w in
    let ups = sort (fun x y -> length(fst(mp4_dest_updates x)) >
                               length(fst(mp4_dest_updates y))) ups in
    let up = hd ups in
    MP4AUX_SEP_WRITES up th in
  ASSUME_TAC (tryfind try_one cands) g;;

(* closes a goal  q s  with an assumption  p s,  p and q equal up to AC    *)
let MP4AUX_SEP_AC_TAC : tactic = fun (asl,w as g) ->
  let q,s = dest_comb w in
  let ql = mp4_star_leaves q in
  let ok (_,th) =
    let c = concl th in
    is_comb c && aconv (rand c) s &&
    let pl = mp4_star_leaves (rator c) in
    length pl = length ql in
  tryfind (fun (_,th as a) ->
             if ok a then ACCEPT_TAC (MP4AUX_STAR_AC_RULE q th) g
             else failwith "") asl;;

(* the goal  q s  with q AC-normalised as the assumption p s would be       *)
let MP4AUX_STAR_NORM_CONV = PURE_REWRITE_CONV[LSORTAUX_STAR_AC];;

(* ------------------------------------------------------------------------- *)
(* Bit-level reasoning about words built from numerals (for any word size,  *)
(* or with the size fixed by an assumption).                                *)
(* ------------------------------------------------------------------------- *)

let MP4AUX_DIV_2EXP_0 = prove
 (`!n k i. n < 2 EXP k /\ k <= i ==> n DIV 2 EXP i = 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_LT THEN MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `2 EXP k` THEN ASM_REWRITE_TAC[LE_EXP; ARITH_EQ]);;

let mp4_num_bits n =
  let rec f k p = if n </ p then k else f (k + 1) (p */ Num.num_of_int 2) in f 0 (Num.num_of_int 1);;

(* rewrites every  n DIV 2 EXP e  (n a numeral, e not) with 0 when the      *)
(* assumptions give  k <= e  for the bit length k of n                       *)
let MP4AUX_DIV_2EXP_0_TAC : tactic = fun (asl,w as g) ->
  let is_target t =
    is_binary "DIV" t && is_numeral (lhand t) &&
    (let r = rand t in is_binary "EXP" r && is_numeral (lhand r) &&
                       dest_numeral (lhand r) =/ Num.num_of_int 2 && not (is_numeral (rand r))) in
  let tms = setify (find_terms is_target w) in
  let tac tm =
    let n = dest_numeral (lhand tm) in
    let k = mp4_num_bits n in
    let e = rand(rand tm) in
    let th = SPECL [lhand tm; mk_small_numeral k; e] MP4AUX_DIV_2EXP_0 in
    TRY(SUBGOAL_THEN (mk_eq(tm,`0`)) SUBST1_TAC THENL
         [MATCH_MP_TAC th THEN CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
          REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC]) in
  MAP_EVERY tac tms g;;

let MP4AUX_BIT_REWRS =
  [BIT_WORD_OR; BIT_WORD_AND; BIT_WORD_SHL; BIT_WORD_USHR; BIT_WORD_NOT;
   BIT_WORD_XOR; BIT_WORD; BIT_WORD_0];;

(* goal  !i. i < dimindex(:N) ==> P i  over bits of numeral words: split    *)
(* i < k (enumerated) and k <= i (numerals of at most k bits vanish)         *)
let MP4AUX_BITS_CASES_TAC k =
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
    MP4AUX_DIV_2EXP_0_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC];;

(* equations of words built with numerals, or, and, not, shifts *)
let MP4AUX_WORD_BITS_TAC k =
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN REWRITE_TAC MP4AUX_BIT_REWRS THEN
  MP4AUX_BITS_CASES_TAC k;;

(* the first assumption whose conclusion is an application of the constant *)
(* name (with or without removing it)                                       *)
let MP4_ASM name (ttac:thm_tactic) : tactic =
  FIRST_ASSUM (fun th -> if mp4_is_app name (concl th) then ttac th
                         else failwith "MP4_ASM");;

let MP4_X_ASM name (ttac:thm_tactic) : tactic =
  FIRST_X_ASSUM (fun th -> if mp4_is_app name (concl th) then ttac th
                           else failwith "MP4_X_ASM");;

(* the first assumption  v = t  with v the variable named s *)
let MP4_VAR_ASM s (ttac:thm_tactic) : tactic =
  FIRST_X_ASSUM (fun th -> let c = concl th in
                   if is_eq c && is_var (lhs c) && fst(dest_var(lhs c)) = s
                   then ttac th else failwith "MP4_VAR_ASM");;

(* the first assumption  f ... = t  with f the constant named name *)
let MP4_EQ_ASM name (ttac:thm_tactic) : tactic =
  FIRST_ASSUM (fun th -> let c = concl th in
                 if is_eq c && mp4_is_app name (lhs c) then ttac th
                 else failwith "MP4_EQ_ASM");;

let MP4_X_EQ_ASM name (ttac:thm_tactic) : tactic =
  FIRST_X_ASSUM (fun th -> let c = concl th in
                   if is_eq c && mp4_is_app name (lhs c) then ttac th
                   else failwith "MP4_X_EQ_ASM");;

(* th : |- p s; the first leaf satisfying pr put last: |- (rest STAR leaf) s *)
let MP4AUX_STAR_LAST pr th =
  let p,s = dest_comb(concl th) in
  let leaves = mp4_star_leaves p in
  let leaf = find pr leaves in
  let rest = mp4_remove_first (fun l -> l == leaf) leaves in
  MP4AUX_STAR_AC_RULE (mp4_mk_star (mp4_list_mk_star rest) leaf) th;;
(* ------------------------------------------------------------------------- *)
(* Helpers: reading and writing one field of a heap element in memory.      *)
(* ------------------------------------------------------------------------- *)

(* the payload of a block of pointers (BlockTag, RefTag, ThunkTag) *)
let MP4AUX_word_payload_ptr = prove
 (`!(ys:((A word_loc)heap_address)list) l tag (qs:(A word_loc)list) conf.
     ((?n. tag = BlockTag n) \/ tag = RefTag \/ (?e. tag = ThunkTag e)) ==>
     ?(h:A word) c. !ys'. LENGTH ys' = LENGTH ys ==>
       word_payload ys' l tag qs conf = (h,MAP (word_addr conf) ys',c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`FST (word_payload ys l tag qs conf):A word`;
                        `SND (SND (word_payload ys l tag qs conf:A word#(A word_loc)list#bool))`] THEN
  GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[word_payload_def; LET_DEF; LET_END_DEF; FST; SND]);;

let MP4AUX_word_el_ptr = prove
 (`!(a:A word) (xs:((A word_loc)heap_address)list) l tag (qs:(A word_loc)list) conf.
     ((?n. tag = BlockTag n) \/ tag = RefTag \/ (?e. tag = ThunkTag e)) ==>
     ?(h:A word) c. !ys'. LENGTH ys' = LENGTH xs ==>
       word_el a (DataElement ys' l (tag,qs)) conf =
       misc_word_list a (CONS (wl_Word h) (MAP (word_addr conf) ys')) STAR
       cond (LENGTH ys' < 2 EXP (dimindex (:A) - 4) /\
             decode_length conf h = word (LENGTH ys') /\ c)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`xs:((A word_loc)heap_address)list`; `l:num`;
                             `qs:(A word_loc)list`; `conf:data_to_word_config`] o
             MATCH_MP MP4AUX_word_payload_ptr) THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`h:A word`; `c:bool`] THEN
  REPEAT STRIP_TAC THEN SIMP[word_el_def; LENGTH_MAP]);;

(* reading and writing an element of a word list *)
let MP4AUX_word_list_field = prove
 (`!(a:A word) (xs:B list) i R m dm.
     (misc_word_list a xs STAR R) (fun2set (m,dm)) /\ i < LENGTH xs ==>
     m (word_add a (word_mul (word i) bytes_in_word)) = EL i xs /\
     word_add a (word_mul (word i) bytes_in_word) IN dm /\
     !y. (misc_word_list a (LUPDATE y i xs) STAR R)
           (fun2set ((word_add a (word_mul (word i) bytes_in_word) =+ y) m,dm))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `ys1:B list` (X_CHOOSE_THEN `y0:B`
    (X_CHOOSE_THEN `ys2:B list` STRIP_ASSUME_TAC)) o MATCH_MP LESS_LENGTH) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[LUPDATE_LENGTH; EL_APPEND; LT_REFL; SUB_REFL; EL; HD] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[data_to_word_memoryProof_word_list_APPEND;
                                       misc_word_list_def]) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP read_fun2set o MP4AUX_STAR_FOCUS mp4_is_one) THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  REWRITE_TAC[data_to_word_memoryProof_word_list_APPEND; misc_word_list_def] THEN
  FIRST_X_ASSUM(fun th ->
    if mp4_is_fun2set_asm (concl th) then
      ASSUME_TAC (MP4AUX_SEP_WRITE
        `word_add (a:A word) (word_mul (word (LENGTH (ys1:B list))) bytes_in_word)`
        `y:B` th)
    else failwith "") THEN
  MP4AUX_SEP_AC_TAC);;

let MP4AUX_heap_addr_eq = prove
 (`!(curr:A word) p i.
     word_add curr (word_mul (word (p + 1 + i)) bytes_in_word) =
     word_add (word_add (word_add curr (word_mul bytes_in_word (word p))) bytes_in_word)
              (word_mul (word i) bytes_in_word)`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

(* reading and writing field i of a block of pointers in the heap *)
let MP4AUX_word_heap_field = prove
 (`!(curr:A word) ha xs l tag qs hb conf i R m dm.
     ((?n. tag = BlockTag n) \/ tag = RefTag \/ (?e. tag = ThunkTag e)) /\
     i < LENGTH xs /\
     (word_heap curr (APPEND ha (CONS (DataElement xs l (tag,qs)) hb)) conf STAR R)
       (fun2set (m,dm)) ==>
     m (word_add curr (word_mul (word (heap_length ha + 1 + i)) bytes_in_word)) =
       word_addr conf (EL i xs) /\
     word_add curr (word_mul (word (heap_length ha + 1 + i)) bytes_in_word) IN dm /\
     !y. (word_heap curr (APPEND ha (CONS (DataElement (LUPDATE y i xs) l (tag,qs)) hb))
            conf STAR R)
           (fun2set ((word_add curr (word_mul (word (heap_length ha + 1 + i))
                                         bytes_in_word) =+ word_addr conf y) m,dm))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPECL
    [`word_add (curr:A word) (word_mul bytes_in_word (word (heap_length
        (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))))`;
     `xs:((A word_loc)heap_address)list`; `l:num`; `qs:(A word_loc)list`;
     `conf:data_to_word_config`] o MATCH_MP MP4AUX_word_el_ptr) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:A word` (X_CHOOSE_TAC `c:bool`)) THEN
  REWRITE_TAC[word_heap_APPEND; word_heap_def; el_length_def] THEN
  ASM_SIMP_TAC[LENGTH_LUPDATE] THEN
  REWRITE_TAC[misc_word_list_def; MP4AUX_heap_addr_eq] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] MP4AUX_word_list_field) o
    MP4AUX_STAR_FOCUS (fun l -> mp4_is_app "misc_word_list" l &&
                                not (mp4_is_app "CONS" (rand l)))) THEN
  ASM_SIMP_TAC[LENGTH_MAP; EL_MAP] THEN STRIP_TAC THEN X_GEN_TAC `y:(A word_loc)heap_address` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word_addr conf (y:(A word_loc)heap_address):A word_loc`) THEN
  REWRITE_TAC[GSYM LUPDATE_MAP] THEN DISCH_TAC THEN MP4AUX_SEP_AC_TAC);;

let MP4AUX_heap_addr_eq2 = prove
 (`!(curr:A word) p i.
     word_add curr (word_mul (word (p + 1 + i)) bytes_in_word) =
     word_add (word_add (word_add curr (word_mul (word p) bytes_in_word)) bytes_in_word)
              (word_mul bytes_in_word (word i))`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Helpers: memory_rel unfolded, a heap change that keeps the shape.        *)
(* ------------------------------------------------------------------------- *)

let MP4AUX_memory_rel_unfold = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars.
     memory_rel c be ts refs sp st m dm vars <=>
     ?heap limit a sp0 sp1 gens hs.
       heap_in_memory_store heap a sp0 sp1 gens c st m dm limit /\
       abs_ml_inv c (MAP FST vars) refs (hs,heap,be,a,sp0,sp1,gens) limit ts /\
       ALL2 (\v w. word_addr c v = w) hs (MAP SND vars) /\
       (limit + 3) * (dimindex (:A) DIV 8) + 1 < dimword (:A) /\ sp <= sp0`,
  REWRITE_TAC[memory_rel_def; word_ml_inv_def] THEN MESON_TAC[]);;

let MP4AUX_heap_in_memory_store_change = prove
 (`!heap heap2 a sp sp1 gens c st (m:A word -> A word_loc) m2 dm limit.
     heap_in_memory_store heap a sp sp1 gens c st m dm limit /\
     heap_length heap2 = heap_length heap /\
     (!curr other.
        FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
        FLOOKUP st OtherHeap = SOME (wl_Word other) /\
        (word_heap curr heap c STAR word_heap other (heap_expand limit) c)
          (fun2set (m,dm)) ==>
        (word_heap curr heap2 c STAR word_heap other (heap_expand limit) c)
          (fun2set (m2,dm))) ==>
     heap_in_memory_store heap2 a sp sp1 gens c st m2 dm limit`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_in_memory_store_def] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[GSYM CONJ_ASSOC]) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`curr:A word`; `other:A word`] THEN
  ASM_SIMP_TAC[]);;

let MP4AUX_heap_deref_SOME = prove
 (`!p (heap:((A,data_to_word_memoryProof_tag#B list)heap_element)list) vs.
     heap_deref p heap = SOME vs <=>
     ?l. heap_lookup p heap = SOME (DataElement vs l (RefTag,[]))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_deref_def] THEN
  EVERY_CASE_TAC THEN SIMP[] THEN MESON_TAC[]);;

let MP4AUX_thunk_deref_SOME = prove
 (`!p (heap:((A,data_to_word_memoryProof_tag#B list)heap_element)list) vs.
     thunk_deref p heap = SOME vs <=>
     ?l. heap_lookup p heap = SOME (DataElement vs l (ThunkTag NotEvaluated,[]))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[thunk_deref_def] THEN
  EVERY_CASE_TAC THEN SIMP[] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Helpers: allocation of a heap element in the unused space, at its start  *)
(* (heap_store_unused_alt, NextFree) or at its end (heap_store_unused,     *)
(* EndOfHeap and TriggerGC).                                                *)
(* ------------------------------------------------------------------------- *)

let MP4AUX_addr_add = prove
 (`!(c:A word) b m n.
     word_add (word_add c (word_mul b (word m))) (word_mul b (word n)) =
     word_add c (word_mul b (word (m + n)))`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let MP4AUX_heap_length_SING = prove
 (`!x:(A,B)heap_element. heap_length [x] = el_length x`,
  REWRITE_TAC[heap_length_def; MAP; SUM; ADD_CLAUSES]);;

let MP4AUX_heap_store_unused_alt_SPLIT = prove
 (`!a n (x:(A,B)heap_element) heap heap2.
     heap_store_unused_alt a n x heap = (heap2,T) ==>
     ?ha hb. heap = APPEND ha (CONS (Unused (n - 1)) hb) /\ a = heap_length ha /\
             el_length x <= n /\
             heap2 = APPEND (APPEND ha (CONS x (heap_expand (n - el_length x)))) hb`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_store_unused_alt_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP heap_lookup_SPLIT)
                                 ASSUME_TAC) THEN
  ASM_REWRITE_TAC[heap_store_lemma; PAIR_EQ; APPEND] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`ha:((A,B)heap_element)list`;
                                       `hb:((A,B)heap_element)list`] THEN
  ASM_REWRITE_TAC[]);;

let MP4AUX_heap_store_unused_SPLIT = prove
 (`!a n (x:(A,B)heap_element) heap heap2.
     heap_store_unused a n x heap = (heap2,T) ==>
     ?ha hb. heap = APPEND ha (CONS (Unused (n - 1)) hb) /\ a = heap_length ha /\
             el_length x <= n /\
             heap2 = APPEND (APPEND ha (APPEND (heap_expand (n - el_length x)) [x])) hb`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_store_unused_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP heap_lookup_SPLIT)
                                 ASSUME_TAC) THEN
  ASM_REWRITE_TAC[heap_store_lemma; PAIR_EQ] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`ha:((A,B)heap_element)list`;
                                       `hb:((A,B)heap_element)list`] THEN
  ASM_REWRITE_TAC[]);;

(* the side condition of the word_el of a heap element *)
let MP4AUX_word_heap_el_cond = prove
 (`!(curr:A word) ha xs l tag (qs:(A word_loc)list) hb conf R m dm.
     (word_heap curr (APPEND ha (CONS (DataElement xs l (tag,qs)) hb)) conf STAR R)
       (fun2set (m,dm)) ==>
     LENGTH (FST (SND (word_payload xs l tag qs conf))) < 2 EXP (dimindex (:A) - 4) /\
     decode_length conf (FST (word_payload xs l tag qs conf)) =
       word (LENGTH (FST (SND (word_payload xs l tag qs conf)))) /\
     SND (SND (word_payload xs l tag qs conf))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_heap_APPEND; word_heap_def; word_el_def] THEN
  SPEC_TAC(`word_payload xs l tag qs conf:A word#(A word_loc)list#bool`,
           `w:A word#(A word_loc)list#bool`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(MP_TAC o MP4AUX_STAR_FOCUS (mp4_is_app "cond")) THEN
  REWRITE_TAC[cond_STAR] THEN SIMP_TAC[]);;
let MP4AUX_word_and_not_1 = prove
 (`!n. word_and (word (4 * n)) (word_not (word 1)):A word = word (4 * n)`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_NOT; BIT_WORD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[EXP; DIV_1; ODD_MULT; ARITH] THEN
  SUBGOAL_THEN `1 DIV 2 EXP i = 0` (fun th -> REWRITE_TAC[th; ARITH]) THEN
  MATCH_MP_TAC MP4AUX_DIV_2EXP_0 THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC);;

(* a small natural number on the stack is represented by 4 times n *)
let MP4AUX_memory_rel_Number_IMP = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm n i vars.
     good_dimindex (:A) /\ small_int (:A) (&n) /\
     memory_rel c be ts refs sp st m dm (CONS (data_Number (&n),i) vars) ==>
     i = wl_Word (word (4 * n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MP4AUX_memory_rel_unfold; MAP; FST; SND] THEN
  REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN STRIP_TAC THEN
  CASES_ON `hs:((A word_loc)heap_address)list` THEN RULE_ASSUM_TAC(REWRITE_RULE[ALL2]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  MP4_X_ASM "/\\" (STRIP_ASSUME_TAC o
    check (fun th -> mp4_is_app "v_inv" (lhand(concl th)))) THEN
  MP4_X_ASM "/\\" (STRIP_ASSUME_TAC o
    check (fun th -> mp4_is_app "word_addr" (lhand(lhand(concl th))))) THEN
  RVEQ_TAC THEN MP4_X_ASM "v_inv" (MP_TAC o REWRITE_RULE[v_inv_def]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[word_addr_def; data_to_word_Smallnum_def; INT_ARITH `~(&n:int < &0)`;
              INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM; injectivity "word_loc";
              MP4AUX_word_and_not_1]);;

(* the length of a reference array is bounded (its header holds it) *)
let MP4AUX_memory_rel_ValueArray_LENGTH = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl nn ptr vars vals.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl nn,ptr) vars) /\
     lookup nn refs = SOME (bvl_ValueArray vals) ==>
     LENGTH vals < 2 EXP (dimindex (:A) - 4)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MP4AUX_memory_rel_unfold; MAP; FST; SND] THEN
  REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN STRIP_TAC THEN
  CASES_ON `hs:((A word_loc)heap_address)list` THEN RULE_ASSUM_TAC(REWRITE_RULE[ALL2]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  MP4_X_ASM "/\\" (STRIP_ASSUME_TAC o
    check (fun th -> mp4_is_app "v_inv" (lhand(concl th)))) THEN
  MP4_X_ASM "v_inv" (MP_TAC o REWRITE_RULE[v_inv_def]) THEN
  ASM_REWRITE_TAC[distinctness "bvl_ref"; option_INJ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `reachable_refs (CONS (data_RefPtr bl nn)
                  (MAP FST (vars:(data_v#A word_loc)list))) refs nn` ASSUME_TAC THENL
   [REWRITE_TAC[reachable_refs_def] THEN
    MAP_EVERY EXISTS_TAC [`data_RefPtr bl nn`; `nn:num`] THEN
    REWRITE_TAC[MEM; get_refs_def; RTC_REFL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `nn:num` o check (fun th -> is_forall (concl th) &&
    can (find_term (mp4_is_app "bc_ref_inv")) (concl th))) THEN
  ASM_REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `zs:((A word_loc)heap_address)list` STRIP_ASSUME_TAC) THEN
  MP4_X_EQ_ASM "heap_lookup" (X_CHOOSE_THEN
    `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    (X_CHOOSE_THEN
      `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
      STRIP_ASSUME_TAC) o MATCH_MP heap_lookup_SPLIT) THEN
  MP4_VAR_ASM "heap" SUBST_ALL_TAC THEN
  MP4_ASM "heap_in_memory_store"
    (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
  MP4_X_ASM "STAR"
    (MP_TAC o MATCH_MP MP4AUX_word_heap_el_cond o REWRITE_RULE[RefBlock_def]) THEN
  REWRITE_TAC[word_payload_def; LENGTH_MAP] THEN
  MP4_X_ASM "ALL2" (MP_TAC o MATCH_MP EVERY2_LENGTH o
                    check (fun th -> rand(concl th) = `vals:data_v list`)) THEN
  SIMP_TAC[]);;
let MP4AUX_small_int_LT = prove
 (`!n. good_dimindex (:A) /\ n < 2 EXP (dimindex (:A) - 4) ==> small_int (:A) (&n)`,
  GEN_TAC THEN REWRITE_TAC[small_int_def; dimword_def; good_dimindex_def] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[INT_OF_NUM_LT] THEN CONJ_TAC THEN TRY INT_ARITH_TAC THEN ASM_ARITH_TAC);;

let MP4AUX_heap_in_memory_store_field = prove
 (`!heap heap2 a sp sp1 gens c st (m:A word -> A word_loc) dm limit p xs l tag
    (qs:(A word_loc)list) i y u.
     heap_in_memory_store heap a sp sp1 gens c st m dm limit /\
     heap_lookup p heap = SOME (DataElement xs l (tag,qs)) /\
     ((?n. tag = BlockTag n) \/ tag = RefTag \/ (?e. tag = ThunkTag e)) /\
     i < LENGTH xs /\
     heap_store p [DataElement (LUPDATE y i xs) l (tag,qs)] heap = (heap2,T) /\
     good_dimindex (:A) ==>
     ?curr.
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       get_real_addr c st (get_addr c p u) =
         SOME (word_add curr (word_mul (word p) bytes_in_word)) /\
       m (word_add curr (word_mul (word (p + 1 + i)) bytes_in_word)) =
         word_addr c (EL i xs) /\
       word_add curr (word_mul (word (p + 1 + i)) bytes_in_word) IN dm /\
       heap_in_memory_store heap2 a sp sp1 gens c st
         ((word_add curr (word_mul (word (p + 1 + i)) bytes_in_word) =+
           word_addr c y) m) dm limit`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP4_ASM "heap_in_memory_store"
    (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
  EXISTS_TAC `curr:A word` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `c:data_to_word_config`; `p:num`;
                 `DataElement (xs:((A word_loc)heap_address)list) l
                    (tag:data_to_word_memoryProof_tag,qs:(A word_loc)list)`;
                 `st:(store_name,A word_loc)fmap`; `curr:A word`; `u:A word_loc`]
                get_real_addr_get_addr) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP4_EQ_ASM "heap_lookup" (X_CHOOSE_THEN
    `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    (X_CHOOSE_THEN
      `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
      STRIP_ASSUME_TAC) o MATCH_MP heap_lookup_SPLIT) THEN
  MP4_VAR_ASM "heap" SUBST_ALL_TAC THEN MP4_VAR_ASM "p" SUBST_ALL_TAC THEN
  MP4_X_EQ_ASM "heap_store" (MP_TAC o REWRITE_RULE[heap_store_lemma; PAIR_EQ;
     el_length_def; MP4AUX_heap_length_SING]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`curr:A word`;
     `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
     `xs:((A word_loc)heap_address)list`; `l:num`;
     `tag:data_to_word_memoryProof_tag`; `qs:(A word_loc)list`;
     `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
     `c:data_to_word_config`; `i:num`;
     `word_heap (other:A word) (heap_expand limit) c`; `m:A word -> A word_loc`;
     `dm:A word -> bool`]
     MP4AUX_word_heap_field) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  MATCH_MP_TAC MP4AUX_heap_in_memory_store_change THEN
  MAP_EVERY EXISTS_TAC
    [`APPEND (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
        (CONS (DataElement (xs:((A word_loc)heap_address)list) l
        (tag:data_to_word_memoryProof_tag,qs:(A word_loc)list)) hb)`;
     `m:A word -> A word_loc`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[heap_length_def; MAP_APPEND; MAP; SUM_APPEND; SUM; el_length_def];
    ALL_TAC] THEN
  REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
    (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[]);;

(* a pointer to a MutBlock is never compared by pointer *)
let MP4AUX_memory_rel_MutBlock_F = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl nn ptr vars tag fin l cv r.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl nn,ptr) vars) /\
     lookup nn refs = SOME (MutBlock tag fin l cv r) ==> ~bl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MP4AUX_memory_rel_unfold; MAP; FST; SND] THEN
  REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN STRIP_TAC THEN
  CASES_ON `hs:((A word_loc)heap_address)list` THEN RULE_ASSUM_TAC(REWRITE_RULE[ALL2]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  MP4_X_ASM "/\\" (STRIP_ASSUME_TAC o
    check (fun th -> mp4_is_app "v_inv" (lhand(concl th)))) THEN
  MP4_X_ASM "v_inv" (MP_TAC o REWRITE_RULE[v_inv_def]) THEN
  ASM_REWRITE_TAC[distinctness "bvl_ref"; option_INJ] THEN MESON_TAC[]);;

(* the length of a MutBlock is bounded (its header holds it) *)
let MP4AUX_memory_rel_MutBlock_LENGTH = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl nn ptr vars tag fin l cv r.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl nn,ptr) vars) /\
     lookup nn refs = SOME (MutBlock tag fin l cv r) ==>
     LENGTH l + 1 + LENGTH r < 2 EXP (dimindex (:A) - 4)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MP4AUX_memory_rel_unfold; MAP; FST; SND] THEN
  REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN STRIP_TAC THEN
  CASES_ON `hs:((A word_loc)heap_address)list` THEN RULE_ASSUM_TAC(REWRITE_RULE[ALL2]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  MP4_X_ASM "/\\" (STRIP_ASSUME_TAC o
    check (fun th -> mp4_is_app "v_inv" (lhand(concl th)))) THEN
  MP4_X_ASM "v_inv" (MP_TAC o REWRITE_RULE[v_inv_def]) THEN
  ASM_REWRITE_TAC[distinctness "bvl_ref"; option_INJ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `reachable_refs (CONS (data_RefPtr bl nn)
                  (MAP FST (vars:(data_v#A word_loc)list))) refs nn` ASSUME_TAC THENL
   [REWRITE_TAC[reachable_refs_def] THEN
    MAP_EVERY EXISTS_TAC [`data_RefPtr bl nn`; `nn:num`] THEN
    REWRITE_TAC[MEM; get_refs_def; RTC_REFL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `nn:num` o check (fun th -> is_forall (concl th) &&
    can (find_term (mp4_is_app "bc_ref_inv")) (concl th))) THEN
  ASM_REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `zs:((A word_loc)heap_address)list` STRIP_ASSUME_TAC o
             CONJUNCT2 o CONJUNCT2) THEN
  MP4_X_EQ_ASM "heap_lookup" (X_CHOOSE_THEN
    `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    (X_CHOOSE_THEN
      `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
      STRIP_ASSUME_TAC) o MATCH_MP heap_lookup_SPLIT) THEN
  MP4_VAR_ASM "heap" SUBST_ALL_TAC THEN
  MP4_ASM "heap_in_memory_store"
    (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
  MP4_X_ASM "STAR"
    (MP_TAC o MATCH_MP MP4AUX_word_heap_el_cond o REWRITE_RULE[BlockRep_def]) THEN
  REWRITE_TAC[word_payload_def; LENGTH_MAP] THEN
  MP4_X_ASM "ALL2" (MP_TAC o MATCH_MP EVERY2_LENGTH o
                    check (fun th -> mp4_is_app "APPEND" (rand(concl th)))) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o CONJUNCT1) THEN MP_TAC th) THEN
  ARITH_TAC);;

let MP4AUX_heap_in_memory_store_el_cond = prove
 (`!heap a sp sp1 gens c st (m:A word -> A word_loc) dm limit p xs l tag
    (qs:(A word_loc)list).
     heap_in_memory_store heap a sp sp1 gens c st m dm limit /\
     heap_lookup p heap = SOME (DataElement xs l (tag,qs)) ==>
     LENGTH (FST (SND (word_payload xs l tag qs c))) < 2 EXP (dimindex (:A) - 4) /\
     decode_length c (FST (word_payload xs l tag qs c)) =
       word (LENGTH (FST (SND (word_payload xs l tag qs c)))) /\
     SND (SND (word_payload xs l tag qs c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP4_ASM "heap_in_memory_store"
    (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
  MP4_X_EQ_ASM "heap_lookup" (X_CHOOSE_THEN
    `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    (X_CHOOSE_THEN
      `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
      STRIP_ASSUME_TAC) o MATCH_MP heap_lookup_SPLIT) THEN
  MP4_VAR_ASM "heap" SUBST_ALL_TAC THEN
  MP4_X_ASM "STAR" (ACCEPT_TAC o MATCH_MP MP4AUX_word_heap_el_cond));;
(* ===== PART 4: HOL4 lines 8235-10991 ===== *)

(* HOL4 line 8235 *)
let memory_rel_Deref = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl nn ptr index i vars vals.
     memory_rel c be ts refs sp st m dm
       (CONS (data_RefPtr bl nn,ptr) (CONS (data_Number (&index),i) vars)) /\
     lookup nn refs = SOME (bvl_ValueArray vals) /\
     good_dimindex (:A) /\
     index < LENGTH vals ==>
     ?ptr_w i_w x y:A word.
       ptr = wl_Word ptr_w /\ i = wl_Word i_w /\
       get_real_addr c st ptr_w = SOME x /\
       get_real_offset i_w = SOME y /\
       word_add x y IN dm /\
       memory_rel c be ts refs sp st m dm
         (CONS (EL index vals,m (word_add x y))
          (CONS (data_RefPtr bl nn,ptr) (CONS (data_Number (&index),i) vars)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `small_int (:A) (&index)` ASSUME_TAC THENL
   [MATCH_MP_TAC MP4AUX_small_int_LT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `LENGTH (vals:data_v list)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MP4AUX_memory_rel_ValueArray_LENGTH THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `i = wl_Word (word (4 * index):A word)` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MP4AUX_memory_rel_Number_IMP THEN ASM_MESON_TAC[memory_rel_tl];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                 `dm:A word -> bool`; `bl:bool`; `nn:num`; `ptr:A word_loc`;
                 `CONS (data_Number (&index),wl_Word (word (4 * index):A word))
                       (vars:(data_v#A word_loc)list)`;
                 `vals:data_v list`; `index:num`] memory_rel_Deref') THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr_w:A word` (X_CHOOSE_THEN `x:A word` STRIP_ASSUME_TAC)) THEN
  MP4_VAR_ASM "ptr" SUBST_ALL_TAC THEN
  MAP_EVERY EXISTS_TAC
    [`ptr_w:A word`; `word (4 * index):A word`; `x:A word`;
     `word_add bytes_in_word (word_mul (word index) bytes_in_word):A word`] THEN
  ASM_SIMP_TAC[get_real_offset_thm] THEN
  REWRITE_TAC[WORD_RULE `word_add (x:A word) (word_add b (word_mul i b)) =
                         word_add (word_add x b) (word_mul b i)`] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 8297 *)
let LENGTH_EQ_1 = prove
 (`!xs:A list. (LENGTH xs = 1 <=> ?a1. xs = [a1]) /\
               (1 = LENGTH xs <=> ?a1. xs = [a1])`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `1 = n <=> n = 1`] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

(* HOL4 line 8305 *)
let LENGTH_EQ_2 = prove
 (`!xs:A list. (LENGTH xs = 2 <=> ?a1 a2. xs = [a1;a2]) /\
               (2 = LENGTH xs <=> ?a1 a2. xs = [a1;a2])`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `2 = n <=> n = 2`] THEN
  REWRITE_TAC[ARITH_RULE `2 = SUC (SUC 0)`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

(* HOL4 line 8314 *)
let LENGTH_EQ_3 = prove
 (`!xs:A list. (LENGTH xs = 3 <=> ?a1 a2 a3. xs = [a1;a2;a3]) /\
               (3 = LENGTH xs <=> ?a1 a2 a3. xs = [a1;a2;a3])`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `3 = n <=> n = 3`] THEN
  REWRITE_TAC[ARITH_RULE `3 = SUC (SUC (SUC 0))`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

(* HOL4 line 8325 *)
let heap_split_SOME_APPEND = prove
 (`!xs ys:((A,B)heap_element)list a h1 h2.
     heap_split a (APPEND xs ys) = SOME (h1,h2) <=>
     if a < heap_length xs then
       ?ha hb. heap_split a xs = SOME (ha,hb) /\ h1 = ha /\ h2 = APPEND hb ys
     else
       ?ha hb. heap_split (a - heap_length xs) ys = SOME (ha,hb) /\
               h1 = APPEND xs ha /\ h2 = hb`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_split_APPEND_if] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[option_case_eq; pair_case_eq; option_DISTINCT; option_INJ; PAIR_EQ] THEN
  MESON_TAC[]);;

let MP4AUX_heap_split_heap_length = prove
 (`!h:((A,B)heap_element)list. heap_split (heap_length h) h = SOME (h,[])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[heap_length_NIL; heap_split_def] THEN
  REWRITE_TAC[heap_length_CONS] THEN
  MP_TAC(ISPEC `h:(A,B)heap_element` el_length_NOT_0) THEN
  ASM_SIMP_TAC[ADD_EQ_0; ARITH_RULE `~(a + b < a:num)`; ADD_SUB2] THEN
  DISCH_TAC THEN CASE_REWRITE_TAC[]);;

let MP4AUX_heap_split_le = prove
 (CASE_TERM `!n (ha:((A,B)heap_element)list) hb.
     n <= heap_length ha ==>
     heap_split n (APPEND ha hb) =
     match heap_split n ha with
       NONE -> NONE
     | SOME (h1,h2) -> SOME (h1,APPEND h2 hb)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_LT] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[heap_split_APPEND_if; LT_REFL; SUB_REFL; heap_split_0;
                  MP4AUX_heap_split_heap_length] THEN
  SIMP[APPEND_NIL; APPEND]);;

let MP4AUX_gen_start_ok_replace = prove
 (`!s refs_start (ha:((A,B)heap_element)list) e e' hb.
     s <= heap_length ha ==>
     (gen_start_ok (APPEND ha (CONS e hb)) refs_start s <=>
      gen_start_ok (APPEND ha (CONS e' hb)) refs_start s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gen_start_ok_def] THEN
  ASM_SIMP_TAC[MP4AUX_heap_split_le] THEN
  CASES_ON `heap_split s (ha:((A,B)heap_element)list)` THEN SIMP[] THEN
  CASES_ON `a:((A,B)heap_element)list#((A,B)heap_element)list` THEN SIMP[]);;

(* HOL4 line 8340 *)
let gc_kind_update_Ref = prove
 (`!c a sp sp1 gens (ha:((A,data_to_word_memoryProof_tag#B list)heap_element)list)
    ys1 y ys2 l hb z.
     gc_kind_inv c a sp sp1 gens
       (APPEND ha (CONS (DataElement (APPEND ys1 (CONS y ys2)) l (RefTag,[])) hb)) ==>
     gc_kind_inv c a sp sp1 gens
       (APPEND ha (CONS (DataElement (APPEND ys1 (CONS z ys2)) l (RefTag,[])) hb))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gc_kind_inv_def] THEN
  CASES_ON `data_to_word_config_gc_kind c` THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `a + sp + sp1 <= heap_length
                  (ha:((A,data_to_word_memoryProof_tag#B list)heap_element)list)`
    ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    MP4_EQ_ASM "heap_split" (MP_TAC o REWRITE_RULE[heap_split_SOME_APPEND]) THEN
    ASM_SIMP_TAC[ARITH_RULE `h < n ==> ~(n < h:num)`; heap_split_def;
                 ARITH_RULE `h < n ==> ~(n - h = 0)`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    REWRITE_TAC[option_case_eq; pair_case_eq; option_DISTINCT; option_INJ; PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    MP4_X_ASM "ALL" (MP_TAC o check (fun th -> mp4_is_app "APPEND" (rand(concl th)))) THEN
    REWRITE_TAC[ALL_APPEND; ALL; isRef_def; isMutTag_def]; ALL_TAC] THEN
  MP4_X_EQ_ASM "heap_split" MP_TAC THEN ASM_SIMP_TAC[MP4AUX_heap_split_le] THEN
  REWRITE_TAC[option_case_eq; pair_case_eq; option_DISTINCT; option_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[option_INJ; PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  CONJ_TAC THENL [ALL_TAC;
    MP4_X_ASM "ALL" (MP_TAC o check (fun th -> mp4_is_app "APPEND" (rand (concl th)))) THEN
    SIMP[ALL_APPEND; ALL; isRef_def; isMutTag_def]] THEN
  MP4_X_ASM "gen_state_ok" MP_TAC THEN CASES_ON `gens:gen_state` THEN
  REWRITE_TAC[gen_state_ok_def; GSYM ALL_MEM] THEN BETA_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `s <= heap_length
                  (ha:((A,data_to_word_memoryProof_tag#B list)heap_element)list)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `a:num` THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_MESON_TAC[MP4AUX_gen_start_ok_replace]);;

(* HOL4 line 8370 *)
let memory_rel_Update' = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm h w bl nn ptr vars vals index.
     memory_rel c be ts refs sp st m dm
       (CONS (h,w) (CONS (data_RefPtr bl nn,ptr) vars)) /\
     lookup nn refs = SOME (bvl_ValueArray vals) /\
     good_dimindex (:A) /\
     index < LENGTH vals ==>
     ?ptr_w x:A word.
       ptr = wl_Word ptr_w /\
       get_real_addr c st ptr_w = SOME x /\
       word_add (word_add x bytes_in_word) (word_mul bytes_in_word (word index))
         IN dm /\
       memory_rel c be ts (insert nn (bvl_ValueArray (LUPDATE h index vals)) refs)
         sp st
         ((word_add (word_add x bytes_in_word) (word_mul bytes_in_word (word index))
           =+ w) m) dm
         (CONS (h,w) (CONS (data_RefPtr bl nn,ptr) vars))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MP4AUX_memory_rel_unfold; MAP; FST; SND] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `[h:data_v]`; `bl:bool`; `nn:num`;
                 `MAP FST (vars:(data_v#A word_loc)list)`; `refs:(data_v bvl_ref)spt`;
                 `hs:((A word_loc)heap_address)list`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `be:bool`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
                 `limit:num`; `ts:num`; `vals:data_v list`; `index:num`]
                update_ref_thm1) THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; ARITH; LENGTH_EQ_1; HD] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `rs:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `roots2:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `vs1:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                           heap_element)list`
    (X_CHOOSE_THEN `u:A word_loc` STRIP_ASSUME_TAC)))))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[APPEND; ALL2; HD]) THEN
  MP4_X_ASM "/\\" STRIP_ASSUME_TAC THEN RVEQ_TAC THEN
  MP4_X_EQ_ASM "heap_deref" (X_CHOOSE_TAC `l0:num` o REWRITE_RULE[MP4AUX_heap_deref_SOME]) THEN
  SUBGOAL_THEN `index < LENGTH (vs1:((A word_loc)heap_address)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP4_X_EQ_ASM "LENGTH" (K ALL_TAC) THEN
  MP4_ASM "heap_in_memory_store" (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
  MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `c:data_to_word_config`; `p:num`;
                 `DataElement (vs1:((A word_loc)heap_address)list) l0
                    (RefTag,[]:(A word_loc)list)`;
                 `st:(store_name,A word_loc)fmap`; `curr:A word`; `u:A word_loc`]
                get_real_addr_get_addr) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP4_EQ_ASM "heap_lookup" (X_CHOOSE_THEN
    `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    (X_CHOOSE_THEN
      `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
      STRIP_ASSUME_TAC) o MATCH_MP heap_lookup_SPLIT) THEN
  MP4_VAR_ASM "heap" SUBST_ALL_TAC THEN MP4_VAR_ASM "p" SUBST_ALL_TAC THEN
  MP4_X_EQ_ASM "heap_store" (MP_TAC o REWRITE_RULE[heap_store_lemma; PAIR_EQ; RefBlock_def;
     el_length_def; MP4AUX_heap_length_SING; LENGTH_LUPDATE; EQ_ADD_RCANCEL]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`get_addr c (heap_length (ha:((A word_loc,data_to_word_memoryProof_tag#
                                   (A word_loc)list)heap_element)list)) (u:A word_loc)`;
    `word_add (curr:A word) (word_mul (word (heap_length (ha:((A word_loc,
        data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))) bytes_in_word)`] THEN
  ASM_REWRITE_TAC[word_addr_def; GSYM MP4AUX_heap_addr_eq2] THEN
  MP_TAC(ISPECL [`curr:A word`;
     `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
     `vs1:((A word_loc)heap_address)list`; `LENGTH (vs1:((A word_loc)heap_address)list)`;
     `RefTag`; `[]:(A word_loc)list`;
     `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
     `c:data_to_word_config`; `index:num`;
     `word_heap (other:A word) (heap_expand limit) c`; `m:A word -> A word_loc`;
     `dm:A word -> bool`]
     MP4AUX_word_heap_field) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC
    [`APPEND ha (CONS (DataElement (LUPDATE (a1:(A word_loc)heap_address) index vs1)
        (LENGTH (vs1:((A word_loc)heap_address)list)) (RefTag,[]:(A word_loc)list)) hb)`;
     `limit:num`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
     `CONS (a1:(A word_loc)heap_address)
        (CONS (Pointer (heap_length (ha:((A word_loc,data_to_word_memoryProof_tag#
                    (A word_loc)list)heap_element)list)) u) roots2)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC; APPEND]) THEN
  ASM_REWRITE_TAC[ALL2; word_addr_def] THEN
  MATCH_MP_TAC MP4AUX_heap_in_memory_store_change THEN
  MAP_EVERY EXISTS_TAC
    [`APPEND ha (CONS (DataElement (vs1:((A word_loc)heap_address)list)
        (LENGTH vs1) (RefTag,[]:(A word_loc)list)) hb)`;
     `m:A word -> A word_loc`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[heap_length_def; MAP_APPEND; MAP; SUM_APPEND; SUM; el_length_def];
    ALL_TAC] THEN
  REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
    (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 8435 *)
let memory_rel_Update = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm h w bl nn ptr index i vars vals.
     memory_rel c be ts refs sp st m dm
       (CONS (h,w) (CONS (data_RefPtr bl nn,ptr)
                    (CONS (data_Number (&index),i) vars))) /\
     lookup nn refs = SOME (bvl_ValueArray vals) /\
     good_dimindex (:A) /\
     index < LENGTH vals ==>
     ?ptr_w i_w x y:A word.
       ptr = wl_Word ptr_w /\ i = wl_Word i_w /\
       get_real_addr c st ptr_w = SOME x /\
       get_real_offset i_w = SOME y /\
       word_add x y IN dm /\
       memory_rel c be ts (insert nn (bvl_ValueArray (LUPDATE h index vals)) refs)
         sp st ((word_add x y =+ w) m) dm
         (CONS (h,w) (CONS (data_RefPtr bl nn,ptr)
                      (CONS (data_Number (&index),i) vars)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `small_int (:A) (&index)` ASSUME_TAC THENL
   [MATCH_MP_TAC MP4AUX_small_int_LT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `LENGTH (vals:data_v list)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MP4AUX_memory_rel_ValueArray_LENGTH THEN
    ASM_MESON_TAC[memory_rel_tl]; ALL_TAC] THEN
  SUBGOAL_THEN `i = wl_Word (word (4 * index):A word)` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MP4AUX_memory_rel_Number_IMP THEN ASM_MESON_TAC[memory_rel_tl];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                 `dm:A word -> bool`; `h:data_v`; `w:A word_loc`; `bl:bool`; `nn:num`;
                 `ptr:A word_loc`;
                 `CONS (data_Number (&index),wl_Word (word (4 * index):A word))
                       (vars:(data_v#A word_loc)list)`;
                 `vals:data_v list`; `index:num`] memory_rel_Update') THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr_w:A word` (X_CHOOSE_THEN `x:A word` STRIP_ASSUME_TAC)) THEN
  MP4_VAR_ASM "ptr" SUBST_ALL_TAC THEN
  MAP_EVERY EXISTS_TAC
    [`ptr_w:A word`; `word (4 * index):A word`; `x:A word`;
     `word_add bytes_in_word (word_mul (word index) bytes_in_word):A word`] THEN
  ASM_SIMP_TAC[get_real_offset_thm] THEN
  REWRITE_TAC[WORD_RULE `word_add (x:A word) (word_add b (word_mul i b)) =
                         word_add (word_add x b) (word_mul b i)`] THEN
  ASM_REWRITE_TAC[]);;

let MP4AUX_heap_addr_eq3 = prove
 (`!(curr:A word) p i.
     word_add (word_add curr (word_mul (word p) bytes_in_word))
              (word_add bytes_in_word (word_mul (word i) bytes_in_word)) =
     word_add curr (word_mul (word (p + 1 + i)) bytes_in_word)`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

(* HOL4 line 8509 *)
let memory_rel_UpdateCons = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm h w bl nn ptr index i vars
    tag l cv r.
     memory_rel c be ts refs sp st m dm
       (CONS (h,w) (CONS (data_RefPtr bl nn,ptr)
                    (CONS (data_Number (&index),i) vars))) /\
     lookup nn refs = SOME (MutBlock tag F l cv r) /\
     good_dimindex (:A) /\
     index = LENGTH l ==>
     ?ptr_w i_w x y:A word.
       ptr = wl_Word ptr_w /\ i = wl_Word i_w /\
       get_real_addr c st ptr_w = SOME x /\
       get_real_offset i_w = SOME y /\
       word_add x y IN dm /\
       memory_rel c be ts (insert nn (MutBlock tag F l h r) refs) sp st
         ((word_add x y =+ w) m) dm
         (CONS (h,w) (CONS (data_RefPtr bl nn,ptr)
                      (CONS (data_Number (&index),i) vars)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~bl` ASSUME_TAC THENL
   [MATCH_MP_TAC MP4AUX_memory_rel_MutBlock_F THEN ASM_MESON_TAC[memory_rel_tl];
    ALL_TAC] THEN
  SUBGOAL_THEN `small_int (:A) (&index)` ASSUME_TAC THENL
   [MATCH_MP_TAC MP4AUX_small_int_LT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `LENGTH (l:data_v list) + 1 + LENGTH (r:data_v list)` THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MP4AUX_memory_rel_MutBlock_LENGTH THEN ASM_MESON_TAC[memory_rel_tl];
    ALL_TAC] THEN
  SUBGOAL_THEN `i = wl_Word (word (4 * index):A word)` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MP4AUX_memory_rel_Number_IMP THEN ASM_MESON_TAC[memory_rel_tl];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `~bl` then SUBST_ALL_TAC (EQF_INTRO th)
                          else NO_TAC) THEN
  MP4_VAR_ASM "index" SUBST_ALL_TAC THEN
  MP4_X_ASM "memory_rel" (STRIP_ASSUME_TAC o
    REWRITE_RULE[MP4AUX_memory_rel_unfold; MAP; FST; SND]) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `h:data_v`; `nn:num`;
                 `CONS (data_Number (&(LENGTH (l:data_v list))))
                       (MAP FST (vars:(data_v#A word_loc)list))`;
                 `refs:(data_v bvl_ref)spt`; `hs:((A word_loc)heap_address)list`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `be:bool`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
                 `limit:num`; `ts:num`; `tag:num`; `l:data_v list`; `cv:data_v`;
                 `r:data_v list`] update_mutblock_thm) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `rr:(A word_loc)heap_address`
    (X_CHOOSE_THEN `roots2:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `vs1:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                           heap_element)list`
    (X_CHOOSE_THEN `u:A word_loc` STRIP_ASSUME_TAC)))))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ALL2]) THEN
  MP4_X_ASM "/\\" STRIP_ASSUME_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`; `c:data_to_word_config`;
                 `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                 `dm:A word -> bool`; `limit:num`; `p:num`;
                 `vs1:((A word_loc)heap_address)list`;
                 `LENGTH (vs1:((A word_loc)heap_address)list)`;
                 `BlockTag tag`; `[]:(A word_loc)list`; `LENGTH (l:data_v list)`;
                 `rr:(A word_loc)heap_address`; `u:A word_loc`]
                MP4AUX_heap_in_memory_store_field) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BlockRep_def; LENGTH_LUPDATE]) THEN
  ASM_REWRITE_TAC[injectivity "data_to_word_memoryProof_tag"] THEN
  ANTS_TAC THENL [CONJ_TAC THENL [MESON_TAC[]; ASM_ARITH_TAC]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `curr:A word` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
    [`get_addr c p (u:A word_loc):A word`; `word (4 * LENGTH (l:data_v list)):A word`;
     `word_add (curr:A word) (word_mul (word p) bytes_in_word)`;
     `word_add bytes_in_word (word_mul (word (LENGTH (l:data_v list))) bytes_in_word):A word`] THEN
  ASM_SIMP_TAC[get_real_offset_thm; word_addr_def; MP4AUX_heap_addr_eq3] THEN
  REWRITE_TAC[MP4AUX_memory_rel_unfold; MAP; FST; SND] THEN
  MAP_EVERY EXISTS_TAC
    [`heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
     `limit:num`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
     `CONS (rr:(A word_loc)heap_address) (CONS (Pointer p u) roots2)`] THEN
  ASM_REWRITE_TAC[ALL2; word_addr_def]);;

(* HOL4 line 8580: store_list *)
let data_to_word_memoryProof_store_list_def = cake_def
  `(data_to_word_memoryProof_store_list (a:A word) [] (m:A word -> A word_loc) dm =
      SOME m) /\
   (data_to_word_memoryProof_store_list a (CONS w ws) m dm =
      if a IN dm then
        data_to_word_memoryProof_store_list (word_add a bytes_in_word) ws
          ((a =+ w) m) dm
      else NONE)`;;

let MP4AUX_word_add_bw_SUC = prove
 (`!(a:A word) n.
     word_add (word_add a bytes_in_word) (word_mul bytes_in_word (word n)) =
     word_add a (word_mul bytes_in_word (word (SUC n)))`,
  REWRITE_TAC[ADD1; WORD_ADD] THEN CONV_TAC WORD_RULE);;

(* HOL4 line 8588 *)
let store_list_append = prove
 (`!xs ys (a:A word) dm (m:A word -> A word_loc) m1.
     data_to_word_memoryProof_store_list a (APPEND xs ys) m dm = SOME m1 <=>
     ?m0. data_to_word_memoryProof_store_list a xs m dm = SOME m0 /\
          data_to_word_memoryProof_store_list
            (word_add a (word_mul bytes_in_word (word (LENGTH xs)))) ys m0 dm =
          SOME m1`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; data_to_word_memoryProof_store_list_def] THENL
   [REWRITE_TAC[option_INJ; WORD_RULE `word_add (a:A word) (word_mul b (word 0)) = a`] THEN
    MESON_TAC[];
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[option_DISTINCT; MP4AUX_word_add_bw_SUC]]);;

(* HOL4 line 8599 *)
let minus_lemma = prove
 (`!w:A word.
     word_mul (word_neg (word 1)) (word_mul bytes_in_word w) =
     word_mul bytes_in_word (word_neg w)`,
  CONV_TAC WORD_RULE);;

(* HOL4 line 8605 *)
let n2w_lsr_eq_0 = prove
 (`!n k. n DIV 2 EXP k = 0 /\ n < dimword (:A) ==> word_ushr (word n) k = word 0:A word`,
  REWRITE_TAC[dimword_def] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  ASM_SIMP_TAC[VAL_WORD_USHR; VAL_WORD; VAL_WORD_0; MOD_LT]);;

(* HOL4 line 8611 *)
let LESS_EXO_SUB = prove
 (`!n k m. n < 2 EXP (k - m) ==> n < 2 EXP k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `2 EXP (k - m)` THEN ASM_REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
  ARITH_TAC);;

(* HOL4 line 8618 *)
let LESS_EXO_SUB_ALT = prove
 (`!m k n. m <= k ==> n < 2 EXP (k - m) ==> n * 2 EXP m < 2 EXP k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `2 EXP (k - m) * 2 EXP m` THEN
  ASM_REWRITE_TAC[LT_MULT_RCANCEL; GSYM EXP_ADD; EXP_EQ_0; ARITH_EQ] THEN
  ASM_SIMP_TAC[SUB_ADD; LE_REFL]);;

(* HOL4 line 8626 *)
let less_pow_dimindex_sub_imp = prove
 (`!n k. n < 2 EXP (dimindex (:A) - k) ==> n < dimword (:A)`,
  REWRITE_TAC[dimword_def] THEN MESON_TAC[LESS_EXO_SUB]);;

(* HOL4 line 8632 *)
let encode_header_NEQ_0 = prove
 (`!c n k (w:A word). encode_header c n k = SOME w ==> ~(w = word 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[encode_header_def; make_header_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(MP_TAC o AP_TERM `bit 0:A word->bool`) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; BIT_WORD_OR; BIT_WORD_0; BIT_WORD] THEN
  REWRITE_TAC[DIMINDEX_GE_1; ARITH_RULE `0 < n <=> 1 <= n`] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 8641 *)
let encode_header_IMP = prove
 (`!c tag len (hd:A word).
     encode_header c tag len = SOME hd /\
     data_to_word_config_len_size c + 5 < dimindex (:A) /\ good_dimindex (:A) ==>
     len < 2 EXP (dimindex (:A) - 4) /\
     decode_length c hd = word len`,
  REPEAT GEN_TAC THEN REWRITE_TAC[encode_header_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[decode_length_def; make_header_def; LET_DEF; LET_END_DEF] THEN
  ABBREV_TAC `ls = data_to_word_config_len_size c` THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN REWRITE_TAC MP4AUX_BIT_REWRS THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th))) THEN
  SUBGOAL_THEN `(i + dimindex (:A) - ls) - (dimindex (:A) - ls) = i` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `tag DIV 2 EXP ((i + dimindex (:A) - ls) - 2) = 0` SUBST1_TAC THENL
   [MATCH_MP_TAC MP4AUX_DIV_2EXP_0 THEN EXISTS_TAC `(dimindex (:A) - ls) - 2` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `3 DIV 2 EXP (i + dimindex (:A) - ls) = 0` SUBST1_TAC THENL
   [MATCH_MP_TAC MP4AUX_DIV_2EXP_0 THEN EXISTS_TAC `2` THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ODD] THEN
  ASM_CASES_TAC `i + dimindex (:A) - ls < dimindex (:A)` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `dimindex (:A) - ls <= i + dimindex (:A) - ls`
      (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    SUBGOAL_THEN `len DIV 2 EXP i = 0` (fun th -> REWRITE_TAC[th; ODD]) THEN
    MATCH_MP_TAC MP4AUX_DIV_2EXP_0 THEN EXISTS_TAC `ls:num` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

(* HOL4 line 8675 *)
let memory_rel_UpdateThunk_NotEvaluated = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm h w nn ptr vars v.
     memory_rel c be ts refs sp st m dm
       (CONS (h,w) (CONS (data_RefPtr F nn,ptr) vars)) /\
     lookup nn refs = SOME (bvl_Thunk NotEvaluated v) /\
     good_dimindex (:A) ==>
     ?ptr_w x:A word.
       ptr = wl_Word ptr_w /\
       get_real_addr c st ptr_w = SOME x /\
       word_add x bytes_in_word IN dm /\
       memory_rel c be ts (insert nn (bvl_Thunk NotEvaluated h) refs) sp st
         ((word_add x bytes_in_word =+ w) m) dm
         (CONS (h,w) (CONS (data_RefPtr F nn,ptr) vars))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MP4AUX_memory_rel_unfold; MAP; FST; SND] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `h:data_v`; `nn:num`;
                 `MAP FST (vars:(data_v#A word_loc)list)`;
                 `refs:(data_v bvl_ref)spt`; `hs:((A word_loc)heap_address)list`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `be:bool`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
                 `limit:num`; `ts:num`; `v:data_v`; `NotEvaluated`] update_thunk_thm) THEN
  ASM_REWRITE_TAC[distinctness "thunk_mode"] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `rr:(A word_loc)heap_address`
    (X_CHOOSE_THEN `roots2:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `v1:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                           heap_element)list`
    (X_CHOOSE_THEN `u:A word_loc` STRIP_ASSUME_TAC)))))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ALL2]) THEN
  MP4_X_ASM "/\\" STRIP_ASSUME_TAC THEN RVEQ_TAC THEN
  MP4_X_EQ_ASM "thunk_deref" (X_CHOOSE_TAC `l1:num` o REWRITE_RULE[MP4AUX_thunk_deref_SOME]) THEN
  MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`; `c:data_to_word_config`;
                 `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                 `dm:A word -> bool`; `limit:num`; `p:num`;
                 `v1:((A word_loc)heap_address)list`; `l1:num`;
                 `ThunkTag NotEvaluated`; `[]:(A word_loc)list`]
                MP4AUX_heap_in_memory_store_el_cond) THEN
  ASM_REWRITE_TAC[word_payload_def; LENGTH_EQ_1] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`; `c:data_to_word_config`;
                 `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                 `dm:A word -> bool`; `limit:num`; `p:num`;
                 `[a1:(A word_loc)heap_address]`; `1`;
                 `ThunkTag NotEvaluated`; `[]:(A word_loc)list`; `0`;
                 `rr:(A word_loc)heap_address`; `u:A word_loc`]
                MP4AUX_heap_in_memory_store_field) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ThunkBlock_def]) THEN
  ASM_REWRITE_TAC[LUPDATE_def; LENGTH; ARITH] THEN
  ANTS_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `curr:A word` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
    [`get_addr c p (u:A word_loc):A word`;
     `word_add (curr:A word) (word_mul (word p) bytes_in_word)`] THEN
  ASM_REWRITE_TAC[word_addr_def; WORD_RULE
    `word_add (word_add (curr:A word) (word_mul (word p) b)) b =
     word_add curr (word_mul (word (p + 1)) b)`] THEN
  MAP_EVERY EXISTS_TAC
    [`heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
     `limit:num`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
     `CONS (rr:(A word_loc)heap_address) (CONS (Pointer p u) roots2)`] THEN
  ASM_REWRITE_TAC[ALL2; word_addr_def]);;

(* HOL4 line 8734 *)
let thunk_tag_bits_lemma = prove
 (`word_or (word_shl (thunk_tag_to_bits Evaluated) 3) (word 6) = word 14:A word`,
  REWRITE_TAC[thunk_tag_to_bits_def] THEN MP4AUX_WORD_BITS_TAC 4);;

(* HOL4 line 8740 *)
let memory_rel_UpdateThunk_Evaluated = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm h w nn ptr vars v hdr.
     memory_rel c be ts refs sp st m dm
       (CONS (h,w) (CONS (data_RefPtr F nn,ptr) vars)) /\
     lookup nn refs = SOME (bvl_Thunk NotEvaluated v) /\
     encode_header c (8 + 6) 1 = SOME hdr /\
     data_dest_thunk h refs = data_NotThunk /\
     good_dimindex (:A) ==>
     ?ptr_w x:A word.
       ptr = wl_Word ptr_w /\
       get_real_addr c st ptr_w = SOME x /\
       x IN dm /\ word_add x bytes_in_word IN dm /\
       memory_rel c be ts (insert nn (bvl_Thunk Evaluated h) refs) sp st
         (m =++ [(x,wl_Word hdr); (word_add x bytes_in_word,w)]) dm
         (CONS (h,w) (CONS (data_RefPtr F nn,ptr) vars))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MP4AUX_memory_rel_unfold; MAP; FST; SND] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `h:data_v`; `nn:num`;
                 `MAP FST (vars:(data_v#A word_loc)list)`;
                 `refs:(data_v bvl_ref)spt`; `hs:((A word_loc)heap_address)list`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `be:bool`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
                 `limit:num`; `ts:num`; `v:data_v`; `Evaluated`] update_thunk_thm) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `rr:(A word_loc)heap_address`
    (X_CHOOSE_THEN `roots2:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `v1:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                           heap_element)list`
    (X_CHOOSE_THEN `u:A word_loc` STRIP_ASSUME_TAC)))))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ALL2]) THEN
  MP4_X_ASM "/\\" STRIP_ASSUME_TAC THEN RVEQ_TAC THEN
  MP4_X_EQ_ASM "thunk_deref" (X_CHOOSE_TAC `l1:num` o REWRITE_RULE[MP4AUX_thunk_deref_SOME]) THEN
  MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`; `c:data_to_word_config`;
                 `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                 `dm:A word -> bool`; `limit:num`; `p:num`;
                 `v1:((A word_loc)heap_address)list`; `l1:num`;
                 `ThunkTag NotEvaluated`; `[]:(A word_loc)list`]
                MP4AUX_heap_in_memory_store_el_cond) THEN
  ASM_REWRITE_TAC[word_payload_def; LENGTH_EQ_1] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN RVEQ_TAC THEN
  MP4_ASM "heap_in_memory_store" (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
  MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `c:data_to_word_config`; `p:num`;
                 `DataElement [a1:(A word_loc)heap_address] 1
                    (ThunkTag NotEvaluated,[]:(A word_loc)list)`;
                 `st:(store_name,A word_loc)fmap`; `curr:A word`; `u:A word_loc`]
                get_real_addr_get_addr) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP4_EQ_ASM "heap_lookup" (X_CHOOSE_THEN
    `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    (X_CHOOSE_THEN
      `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
      STRIP_ASSUME_TAC) o MATCH_MP heap_lookup_SPLIT) THEN
  MP4_VAR_ASM "heap" SUBST_ALL_TAC THEN MP4_VAR_ASM "p" SUBST_ALL_TAC THEN
  MP4_X_EQ_ASM "heap_store" (MP_TAC o REWRITE_RULE[heap_store_lemma; PAIR_EQ;
     ThunkBlock_def; el_length_def; MP4AUX_heap_length_SING]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  (SUBGOAL_THEN `make_header c (word 14) 1 = (hdr:A word) /\ decode_length c hdr = word 1`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP4_EQ_ASM "encode_header" (MP_TAC o REWRITE_RULE[encode_header_def; ARITH]) THEN
      COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ];
      MP_TAC(ISPECL [`c:data_to_word_config`; `8 + 6`; `1`; `hdr:A word`]
        encode_header_IMP) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC]) THEN
  MP4_X_ASM "STAR" (MP_TAC o CAKE_SIMP_RULE[word_heap_APPEND; word_heap_def; word_el_def;
      el_length_def; word_payload_def; misc_word_list_def; SEP_CLAUSES; LENGTH]) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[cond_STAR] o
     MP4AUX_STAR_FOCUS (mp4_is_app "cond")) THEN
   MP4_ASM "STAR" (fun th -> MAP_EVERY (STRIP_ASSUME_TAC) (MP4AUX_SEP_READS th)) THEN
   MAP_EVERY EXISTS_TAC
    [`get_addr c (heap_length (ha:((A word_loc,data_to_word_memoryProof_tag#
                                   (A word_loc)list)heap_element)list)) (u:A word_loc)`;
     `word_add (curr:A word) (word_mul bytes_in_word (word (heap_length (ha:((A word_loc,
        data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))))`] THEN
   ONCE_REWRITE_TAC[WORD_MUL_SYM] THEN ASM_REWRITE_TAC[word_addr_def] THEN
   ONCE_REWRITE_TAC[WORD_MUL_SYM] THEN ASM_REWRITE_TAC[UPDATE_LIST_THM; FST; SND] THEN
  MAP_EVERY EXISTS_TAC
    [`APPEND ha (CONS (DataElement [rr:(A word_loc)heap_address] 1
        (ThunkTag Evaluated,[]:(A word_loc)list)) hb)`;
     `limit:num`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
     `CONS (rr:(A word_loc)heap_address) (CONS (Pointer (heap_length (ha:((A word_loc,
        data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)) u) roots2)`] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC; APPEND]) THEN
   ASM_REWRITE_TAC[ALL2; word_addr_def] THEN
   MATCH_MP_TAC MP4AUX_heap_in_memory_store_change THEN
   MAP_EVERY EXISTS_TAC
    [`APPEND ha (CONS (DataElement [a1:(A word_loc)heap_address] 1
        (ThunkTag NotEvaluated,[]:(A word_loc)list)) hb)`; `m:A word -> A word_loc`] THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [REWRITE_TAC[heap_length_def; MAP_APPEND; MAP; SUM_APPEND; SUM; el_length_def];
     ALL_TAC] THEN
   REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN
   REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
     (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (K ALL_TAC))) THEN
   CONV_TAC(CAKE_SIMP_CONV[word_heap_APPEND; word_heap_def; word_el_def;
      el_length_def; word_payload_def; misc_word_list_def; SEP_CLAUSES; LENGTH;
      thunk_tag_bits_lemma]) THEN
   ASM_REWRITE_TAC[SEP_CLAUSES] THEN
  MP4AUX_SEP_W_TAC THEN MP4AUX_SEP_AC_TAC);;

(* HOL4 line 8809: word_list_exists_thm *)
let data_to_word_memoryProof_word_list_exists_thm = prove
 (`!(a:A word) n.
     (word_list_exists a 0 = emp:((A word#B)->bool)->bool) /\
     (word_list_exists a (SUC n) =
        SEP_EXISTS w:B. set_sep_one (a,w) STAR
                        word_list_exists (word_add a bytes_in_word) n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_list_exists_def; SEP_CLAUSES] THEN
  REWRITE_TAC[FUN_EQ_THM; SEP_EXISTS_THM; STAR_ASSOC; cond_STAR] THEN
  REWRITE_TAC[LENGTH_EQ_NIL; LENGTH_EQ_CONS] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[UNWIND_THM2; misc_word_list_def] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`h:B`; `t:B list`] THEN
    UNDISCH_TAC `misc_word_list (a:A word) (xs:B list) x` THEN
    ASM_REWRITE_TAC[misc_word_list_def];
    MAP_EVERY EXISTS_TAC [`CONS (w:B) xs`; `w:B`; `xs:B list`] THEN
    ASM_REWRITE_TAC[misc_word_list_def]]);;

let MP4AUX_word_add_mul_SUC = prove
 (`!(a:A word) b n.
     word_add a (word_mul (word (SUC n)) b) =
     word_add (word_add a b) (word_mul (word n) b)`,
  REWRITE_TAC[ADD1; WORD_ADD] THEN CONV_TAC WORD_RULE);;

(* HOL4 line 8827: word_list_exists_ADD *)
let data_to_word_memoryProof_word_list_exists_ADD = prove
 (`!m n (a:A word).
     word_list_exists a (m + n):((A word#B)->bool)->bool =
     word_list_exists a m STAR
     word_list_exists (word_add a (word_mul bytes_in_word (word m))) n`,
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; data_to_word_memoryProof_word_list_exists_thm; SEP_CLAUSES;
                WORD_RULE `word_add (a:A word) (word_mul b (word 0)) = a`];
    ASM_REWRITE_TAC[ADD_CLAUSES; data_to_word_memoryProof_word_list_exists_thm;
                    SEP_CLAUSES] THEN
    REWRITE_TAC[STAR_ASSOC; MP4AUX_word_add_bw_SUC]]);;

(* HOL4 line 8838 *)
let store_list_thm = prove
 (`!xs (a:A word) frame (m:A word -> A word_loc) dm.
     (word_list_exists a (LENGTH xs) STAR frame) (fun2set (m,dm)) ==>
     ?m1.
       data_to_word_memoryProof_store_list a xs m dm = SOME m1 /\
       (misc_word_list a xs STAR frame) (fun2set (m1,dm))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; data_to_word_memoryProof_store_list_def;
                data_to_word_memoryProof_word_list_exists_thm; misc_word_list_def;
                SEP_CLAUSES; option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "ih") THEN
  REWRITE_TAC[LENGTH; data_to_word_memoryProof_store_list_def;
              data_to_word_memoryProof_word_list_exists_thm; misc_word_list_def;
              SEP_CLAUSES; SEP_EXISTS_THM] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC `w:A word_loc`) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP read_fun2set o
              MP4AUX_STAR_FOCUS mp4_is_one) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th ->
    if mp4_is_fun2set_asm (concl th) then
      let thw = MP4AUX_SEP_WRITE `a:A word` `h:A word_loc` th in
      let thf = MP4AUX_STAR_FOCUS (mp4_is_app "word_list_exists") thw in
      REMOVE_THEN "ih" (MP_TAC o C MATCH_MP thf)
    else failwith "") THEN
  STRIP_TAC THEN EXISTS_TAC `m1:A word -> A word_loc` THEN ASM_REWRITE_TAC[] THEN
  MP4AUX_SEP_AC_TAC);;

(* HOL4 line 8851 *)
let store_list_domain = prove
 (`!(a:A word) xs (m:A word -> A word_loc) dm m1.
     data_to_word_memoryProof_store_list a xs m dm = SOME m1 ==>
     !n. n < LENGTH xs ==> word_add a (word_mul (word n) bytes_in_word) IN dm`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[data_to_word_memoryProof_store_list_def; LENGTH; CONJUNCT1 LT] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  DISCH_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[LT_SUC; LT_0; MP4AUX_word_add_mul_SUC;
                  WORD_RULE `word_add (a:A word) (word_mul (word 0) b) = a`]);;

(* HOL4 line 8861 *)
let store_list_append_imp = prove
 (`!w1 (a:A word) (m:A word -> A word_loc) dm m' w2.
     data_to_word_memoryProof_store_list a (APPEND w1 w2) m dm = SOME m' ==>
     ?m''. data_to_word_memoryProof_store_list a w1 m dm = SOME m'' /\
           data_to_word_memoryProof_store_list
             (word_add a (word_mul (word (LENGTH w1)) bytes_in_word)) w2 m'' dm =
           SOME m'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[store_list_append] THEN
  DISCH_THEN(ACCEPT_TAC o ONCE_REWRITE_RULE[WORD_MUL_SYM]));;

(* HOL4 line 8872 *)
let store_list_update_m_outside = prove
 (`!ws (a:A word) (m:A word -> A word_loc) dm m' a' v.
     data_to_word_memoryProof_store_list a ws m dm = SOME m' /\
     (!i. i < LENGTH ws ==> ~(word_add a (word_mul (word i) bytes_in_word) = a'))
     ==>
     data_to_word_memoryProof_store_list a ws ((a' =+ v) m) dm =
     SOME ((a' =+ v) m')`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[data_to_word_memoryProof_store_list_def; LENGTH; option_INJ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(a:A word = a')` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[LT_0; WORD_RULE `word_add (a:A word) (word_mul (word 0) b) = a`];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP UPDATE_COMMUTES th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC i`) THEN
  ASM_REWRITE_TAC[LT_SUC; MP4AUX_word_add_mul_SUC]);;

(* HOL4 line 8892 *)
let word_payload_IMP = prove
 (`!addrs ll tags tt1 conf (h:A word) ts.
     word_payload addrs ll tags tt1 conf = (h,ts,T) ==> LENGTH ts = ll`,
  REPEAT GEN_TAC THEN CASES_ON `tags:data_to_word_memoryProof_tag` THEN
  REWRITE_TAC[word_payload_def; PAIR_EQ; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[LENGTH_MAP]);;

(* HOL4 line 8898 *)
let word_el_IMP_word_list_exists = prove
 (`!conf s (temp:((B)word_loc,data_to_word_memoryProof_tag#((B)word_loc)list)
                 heap_element) p (curr:A word).
     (p STAR word_el curr temp conf) s ==>
     (p STAR word_list_exists curr (el_length temp)) s`,
  REPEAT GEN_TAC THEN
  CASES_ON `temp:((B)word_loc,data_to_word_memoryProof_tag#((B)word_loc)list)
                 heap_element` THEN
  REWRITE_TAC[word_el_def; el_length_def; GSYM ADD1;
              data_to_word_memoryProof_word_list_exists_thm] THENL
   [REWRITE_TAC[SEP_CLAUSES; SEP_EXISTS_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBST1_TAC(ISPEC `a2:data_to_word_memoryProof_tag#((B)word_loc)list` (GSYM PAIR)) THEN
  REWRITE_TAC[word_el_def] THEN
  MP_TAC(ISPECL [`a0:(((B)word_loc)heap_address)list`; `a1:num`;
     `FST (a2:data_to_word_memoryProof_tag#((B)word_loc)list)`;
     `SND (a2:data_to_word_memoryProof_tag#((B)word_loc)list)`; `conf:data_to_word_config`]
     word_payload_IMP) THEN
  SPEC_TAC(`word_payload a0 a1 (FST (a2:data_to_word_memoryProof_tag#((B)word_loc)list))
              (SND a2) conf:B word#(B word_loc)list#bool`,
           `w:B word#(B word_loc)list#bool`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN CASE_REWRITE_TAC[] THEN
  DISCH_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[cond_STAR] o
    MP4AUX_STAR_FOCUS (mp4_is_app "cond")) THEN
  SUBGOAL_THEN `LENGTH (p1':(B word_loc)list) = a1` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[word_list_exists_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  MAP_EVERY EXISTS_TAC [`wl_Word (p1:B word)`; `p1':(B word_loc)list`] THEN
  ASM_REWRITE_TAC[SEP_CLAUSES] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[misc_word_list_def]) THEN MP4AUX_SEP_AC_TAC);;

(* HOL4 line 8914 *)
let word_heap_IMP_word_list_exists = prove
 (`!conf s temp p (curr:A word).
     (p STAR word_heap curr temp conf) s ==>
     (p STAR word_list_exists curr (heap_length temp)) s`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[word_heap_def; heap_length_NIL; heap_length_CONS;
              data_to_word_memoryProof_word_list_exists_thm;
              data_to_word_memoryProof_word_list_exists_ADD] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun ih -> if is_forall (concl ih) then
    FIRST_X_ASSUM(fun th ->
      ASSUME_TAC(MATCH_MP word_el_IMP_word_list_exists
        (MP4AUX_STAR_LAST (mp4_is_app "word_el")
          (MATCH_MP ih (MP4AUX_STAR_LAST (mp4_is_app "word_heap") th)))))
    else failwith "") THEN
  MP4AUX_SEP_AC_TAC);;

(* HOL4 line 8928 *)
let EVERY2_f_EQ = prove
 (`!rs ws (f:A->B). ALL2 (\v w. f v = w) rs ws <=> MAP f rs = ws`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; MAP; NOT_CONS_NIL; NOT_NIL_CONS; CONS_11]);;

(* HOL4 line 8934 *)
let word_heap_heap_expand = prove
 (`!(a:A word) n conf.
     word_heap a (heap_expand n) conf = word_list_exists a n`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[heap_expand_def; word_heap_def;
                data_to_word_memoryProof_word_list_exists_thm];
    REWRITE_TAC[heap_expand_def; NOT_SUC; SUC_SUB1; word_heap_def; word_el_def;
                SEP_CLAUSES; ADD1]]);;

(* HOL4 line 8942 *)
let get_lowerbits_or_1 = prove
 (`!c v. get_lowerbits c v = word_or (get_lowerbits c v) (word 1):A word`,
  REPEAT GEN_TAC THEN CASES_ON `v:A word_loc` THEN REWRITE_TAC[get_lowerbits_def] THEN
  WORD_BITWISE_TAC);;
(* allocation helpers *)

let MP4AUX_alloc_bottom = prove
 (`!heap heap2 a sp sp1 gens c st (m:A word -> A word_loc) dm limit
    (x:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element) hd ws.
     heap_in_memory_store heap a sp sp1 gens c st m dm limit /\
     heap_store_unused_alt a (sp + sp1) x heap = (heap2,T) /\
     el_length x = LENGTH ws + 1 /\ el_length x <= sp /\
     (!(b:A word) R s. (misc_word_list b (CONS (wl_Word hd) ws) STAR R) s ==>
              (word_el b x c STAR R) s) ==>
     ?curr. FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       FLOOKUP st NextFree =
         SOME (wl_Word (word_add curr (word_mul bytes_in_word (word a)))) /\
       ?m1. data_to_word_memoryProof_store_list
              (word_add curr (word_mul bytes_in_word (word a))) (CONS (wl_Word hd) ws)
              m dm = SOME m1 /\
            heap_in_memory_store heap2 (a + el_length x) (sp - el_length x) sp1 gens c
              (st |+ (NextFree,wl_Word (word_add curr
                         (word_mul bytes_in_word (word (a + el_length x)))))) m1 dm limit`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
   MP4_X_EQ_ASM "heap_store_unused_alt" (STRIP_ASSUME_TAC o
     MATCH_MP MP4AUX_heap_store_unused_alt_SPLIT) THEN
   MP4_X_ASM "heap_in_memory_store" (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
   MP4_VAR_ASM "heap" SUBST_ALL_TAC THEN MP4_VAR_ASM "heap2" SUBST_ALL_TAC THEN
   MP4_VAR_ASM "a" SUBST_ALL_TAC THEN
   EXISTS_TAC `curr:A word` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `b0 = word_add (curr:A word) (word_mul bytes_in_word (word (heap_length
     (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))))` THEN
   SUBGOAL_THEN `word_list_exists (b0:A word) (sp + sp1):((A word#A word_loc)->bool)->bool =
     word_list_exists b0 (LENGTH (ws:(A word_loc)list) + 1) STAR
     word_list_exists (word_add b0 (word_mul bytes_in_word (word (LENGTH ws + 1))))
       ((sp + sp1) - (LENGTH ws + 1))` (LABEL_TAC "split") THENL
    [MP_TAC(ISPECL [`LENGTH (ws:(A word_loc)list) + 1`; `(sp + sp1) - (LENGTH (ws:(A word_loc)list) + 1)`;
       `b0:A word`] (INST_TYPE [`:A word_loc`,`:B`] data_to_word_memoryProof_word_list_exists_ADD)) THEN
     SUBGOAL_THEN `(LENGTH (ws:(A word_loc)list) + 1) + (sp + sp1) - (LENGTH ws + 1) = sp + sp1`
       (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
   MP4_X_ASM "STAR" (MP_TAC o REWRITE_RULE[word_heap_APPEND; word_heap_def; word_el_def;
     el_length_def]) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `((sp + sp1) - 1) + 1 = sp + sp1` (fun th -> REWRITE_TAC[th]) THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
   USE_THEN "split" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
  MP4_X_ASM "STAR" (fun th ->
     let thf = MP4AUX_STAR_FOCUS (fun l -> mp4_is_app "word_list_exists" l &&
                 rand l = `LENGTH (ws:(A word_loc)list) + 1`) th in
     let p,s = dest_comb (concl thf) in
     let frame = rand p in
     let sl = REWRITE_RULE[LENGTH; ADD1] (ISPECL [`CONS (wl_Word (hd:A word)) ws`;
                `b0:A word`; frame; `m:A word -> A word_loc`; `dm:A word -> bool`]
                store_list_thm) in
     MP_TAC (MATCH_MP sl thf)) THEN
   DISCH_THEN(X_CHOOSE_THEN `m1:A word -> A word_loc` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `m1:A word -> A word_loc` THEN ASM_REWRITE_TAC[] THEN
   MP4_X_ASM "STAR" (fun th -> FIRST_X_ASSUM(fun imp ->
     if is_forall (concl imp) then ASSUME_TAC (MATCH_MP imp th) else failwith "")) THEN
  SUBGOAL_THEN `heap_length (APPEND (APPEND ha (CONS (x:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)
       (heap_expand ((sp + sp1) - (LENGTH (ws:(A word_loc)list) + 1))))) hb) =
     heap_length (APPEND ha (CONS (Unused ((sp + sp1) - 1)) hb))` ASSUME_TAC THENL
    [REWRITE_TAC[heap_length_APPEND; heap_length_CONS; gc_shared_heap_length_heap_expand;
                 el_length_def] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[heap_in_memory_store_def] THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[FLOOKUP_UPDATE; FDOM_FUPDATE; IN_INSERT; distinctness "store_name"] THEN
   ASM_REWRITE_TAC[] THEN
   MAP_EVERY EXISTS_TAC [`curr:A word`; `other:A word`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (ws:(A word_loc)list) + 1 <= sp` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[ARITH_RULE `k <= s ==> (a + k) + (s - k) = a + s:num`;
                ARITH_RULE `k <= s ==> (a + k) + ((s - k) + t) = a + s + t:num`] THEN
  REWRITE_TAC[word_heap_APPEND; word_heap_def; word_heap_heap_expand] THEN
   SUBGOAL_THEN `word_add (curr:A word) (word_mul bytes_in_word (word (heap_length (APPEND ha
       (CONS (x:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)
       (heap_expand ((sp + sp1) - (LENGTH (ws:(A word_loc)list) + 1)))))))) =
     word_add b0 (word_mul bytes_in_word (word (sp + sp1)))` SUBST1_TAC THENL
    [EXPAND_TAC "b0" THEN REWRITE_TAC[MP4AUX_addr_add] THEN
     REWRITE_TAC[heap_length_APPEND; heap_length_CONS;
                 gc_shared_heap_length_heap_expand] THEN
     AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[word_heap_heap_expand]) THEN
   MP4AUX_SEP_AC_TAC);;

let MP4AUX_word_bits_0 = prove
 (`!h l. word_bits h l (word 0:A word) = word 0`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; word_bits_def; BIT_WORD_OF_BITS; BIT_WORD_0; IN]);;

let MP4AUX_make_ptr_get_addr = prove
 (`!c a (curr:A word) (tag:B) (len:C).
     good_dimindex (:A) /\ backend_common_word_shift (:A) <= shift_length c ==>
     make_ptr c (word_sub (word_add curr (word_mul bytes_in_word (word a))) curr) tag len =
     wl_Word (get_addr c a (wl_Word (word 0)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[make_ptr_def; get_addr_def; get_lowerbits_def; MP4AUX_word_bits_0;
              WORD_RULE `word_sub (word_add x y) x = y:A word`; WORD_OR_0] THEN
  ASM_SIMP_TAC[bytes_in_word_mul_eq_shift; WORD_SHL_COMPOSE;
               ARITH_RULE `a <= b ==> a + b - a = b:num`]);;

(* HOL4 line 8948 *)
let memory_rel_Word64_alt = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vs vars w64 ws hd.
     memory_rel c be ts refs sp st m dm (APPEND vs vars) /\ good_dimindex (:A) /\
     Word64Rep (:A) w64 = DataElement [] (LENGTH ws) (Word64Tag,ws) /\
     LENGTH ws < sp /\
     encode_header c 3 (LENGTH ws) = SOME hd
     ==>
     ?ne curr m1.
       FLOOKUP st NextFree = SOME (wl_Word ne) /\
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       data_to_word_memoryProof_store_list ne (CONS (wl_Word hd) ws) m dm =
         SOME m1 /\
       memory_rel c be ts refs (sp - (LENGTH ws + 1))
         (st |+ (NextFree,
                 wl_Word (word_add ne (word_mul bytes_in_word (word (LENGTH ws + 1))))))
         m1 dm
         (CONS (data_Word64 w64,
                make_ptr c (word_sub ne curr) (word 0:A word) (LENGTH ws)) vars)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MP4AUX_memory_rel_unfold; MAP_APPEND] THEN STRIP_TAC THEN
   MP4_X_ASM "ALL2" (MP_TAC o MATCH_MP EVERY2_APPEND_IMP_APPEND o MATCH_MP EVERY2_SWAP) THEN
   DISCH_THEN(X_CHOOSE_THEN `rs:((A word_loc)heap_address)list`
     (X_CHOOSE_THEN `roots:((A word_loc)heap_address)list` STRIP_ASSUME_TAC)) THEN
   RVEQ_TAC THEN
   MP4_X_ASM "ALL2" (ASSUME_TAC o BETA_RULE o MATCH_MP EVERY2_SWAP o
     check (fun th -> rand(rator(concl th)) = `MAP SND (vars:(data_v#A word_loc)list)`)) THEN
   MP4_ASM "ALL2" (ASSUME_TAC o MATCH_MP EVERY2_LENGTH o
     check (fun th -> rand(rator(concl th)) = `MAP SND (vs:(data_v#A word_loc)list)`)) THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `MAP FST (vs:(data_v#A word_loc)list)`;
                  `MAP FST (vars:(data_v#A word_loc)list)`; `refs:(data_v bvl_ref)spt`;
                  `rs:((A word_loc)heap_address)list`; `roots:((A word_loc)heap_address)list`;
                  `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list`;
                  `be:bool`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`; `limit:num`;
                  `ts:num`; `w64:int64`; `LENGTH (ws:(A word_loc)list)`; `ws:(A word_loc)list`]
                 word64_alt_thm) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN ASM_REWRITE_TAC[LENGTH_MAP] THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                           heap_element)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `make_header c (word 3) (LENGTH (ws:(A word_loc)list)) = (hd:A word) /\
                 LENGTH ws < 2 EXP (dimindex (:A) - 4) /\ decode_length c hd = word (LENGTH ws)`
     STRIP_ASSUME_TAC THENL
    [MP4_ASM "heap_in_memory_store" (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
     MP_TAC(ISPECL [`c:data_to_word_config`; `3`; `LENGTH (ws:(A word_loc)list)`; `hd:A word`]
       encode_header_IMP) THEN
     ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]] THEN
     MP4_EQ_ASM "encode_header" (MP_TAC o REWRITE_RULE[encode_header_def]) THEN
     COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list`;
                  `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list`;
                  `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`; `c:data_to_word_config`;
                  `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                  `dm:A word -> bool`; `limit:num`; `Word64Rep (:A) w64`; `hd:A word`;
                  `ws:(A word_loc)list`] MP4AUX_alloc_bottom) THEN
   ASM_REWRITE_TAC[el_length_def] THEN ANTS_TAC THENL
    [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     SIMP[word_el_def; word_payload_def; SEP_CLAUSES]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `curr:A word` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `m1:A word -> A word_loc` STRIP_ASSUME_TAC)))) THEN
   MAP_EVERY EXISTS_TAC [`word_add (curr:A word) (word_mul bytes_in_word (word a))`;
     `curr:A word`; `m1:A word -> A word_loc`] THEN
   ASM_REWRITE_TAC[MP4AUX_addr_add] THEN
   MAP_EVERY EXISTS_TAC
    [`heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
     `limit:num`; `a + LENGTH (ws:(A word_loc)list) + 1`;
     `sp0 - (LENGTH (ws:(A word_loc)list) + 1)`; `sp1:num`; `gens:gen_state`;
     `CONS (Pointer a (wl_Word (word 0))) (roots:((A word_loc)heap_address)list)`] THEN
   ASM_REWRITE_TAC[MAP; FST; SND; ALL2; word_addr_def] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `a - b - 1 = a - (b + 1)`]) THEN
   ASM_REWRITE_TAC[] THEN
   MP4_ASM "heap_in_memory_store" (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def] o
     check (fun th -> rand(rator(rator(rator(rator(rator(rator(rator(rator(rator(concl th))))))))))
                      = `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`)) THEN
   ASM_SIMP_TAC[MP4AUX_make_ptr_get_addr] THEN ASM_ARITH_TAC);;

(* HOL4 line 9026 *)
let memory_rel_WordOp64_alt = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm w1 w2 vars w64 ws hd.
     memory_rel c be ts refs sp st m dm (CONS w1 (CONS w2 vars)) /\
     good_dimindex (:A) /\
     Word64Rep (:A) w64 = DataElement [] (LENGTH ws) (Word64Tag,ws) /\
     LENGTH ws < sp /\
     encode_header c 3 (LENGTH ws) = SOME hd
     ==>
     ?ne curr m1.
       FLOOKUP st NextFree = SOME (wl_Word ne) /\
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       data_to_word_memoryProof_store_list ne (CONS (wl_Word hd) ws) m dm =
         SOME m1 /\
       memory_rel c be ts refs (sp - (LENGTH ws + 1))
         (st |+ (NextFree,
                 wl_Word (word_add ne (word_mul bytes_in_word (word (LENGTH ws + 1))))))
         m1 dm
         (CONS (data_Word64 w64,
                make_ptr c (word_sub ne curr) (word 0:A word) (LENGTH ws)) vars)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC memory_rel_Word64_alt THEN
  EXISTS_TAC `[w1:data_v#A word_loc; w2]` THEN ASM_REWRITE_TAC[APPEND]);;

let MP4AUX_memory_rel_alloc_bottom = prove
 (`!c be ts2 refs2 sp st (m:A word -> A word_loc) dm vars heap heap2 limit a sp0 sp1
    gens roots2 x hd ws v annot.
     heap_in_memory_store heap a sp0 sp1 gens c st m dm limit /\
     (limit + 3) * (dimindex (:A) DIV 8) + 1 < dimword (:A) /\
     heap_store_unused_alt a (sp0 + sp1) x heap = (heap2,T) /\
     el_length x = LENGTH ws + 1 /\ el_length x <= sp0 /\ sp <= sp0 /\
     (!(b:A word) R s. (misc_word_list b (CONS (wl_Word hd) ws) STAR R) s ==>
                       (word_el b x c STAR R) s) /\
     abs_ml_inv c (CONS v (MAP FST vars)) refs2
       (CONS (Pointer a annot) roots2,heap2,be,a + el_length x,sp0 - el_length x,
        sp1,gens) limit ts2 /\
     ALL2 (\v w. word_addr c v = w) roots2 (MAP SND (vars:(data_v#A word_loc)list)) ==>
     ?curr m1.
       FLOOKUP st NextFree = SOME (wl_Word (word_add curr (word_mul bytes_in_word (word a)))) /\
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       data_to_word_memoryProof_store_list (word_add curr (word_mul bytes_in_word (word a)))
         (CONS (wl_Word hd) ws) m dm = SOME m1 /\
       memory_rel c be ts2 refs2 (sp - (LENGTH ws + 1))
         (st |+ (NextFree,wl_Word (word_add curr
                   (word_mul bytes_in_word (word (a + LENGTH ws + 1)))))) m1 dm
         (CONS (v,wl_Word (get_addr c a annot)) vars)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP4_X_EQ_ASM "el_length" (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
  MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`; `c:data_to_word_config`;
                 `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                 `dm:A word -> bool`; `limit:num`;
                 `x:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element`;
                 `hd:A word`; `ws:(A word_loc)list`] MP4AUX_alloc_bottom) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `curr:A word` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `m1:A word -> A word_loc`
       STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`curr:A word`; `m1:A word -> A word_loc`] THEN
  ASM_REWRITE_TAC[MP4AUX_memory_rel_unfold] THEN
  MAP_EVERY EXISTS_TAC
   [`heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `a + el_length
       (x:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)`;
    `sp0 - el_length
       (x:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)`;
    `sp1:num`; `gens:gen_state`;
    `CONS (Pointer a annot) (roots2:((A word_loc)heap_address)list)`] THEN
  ASM_REWRITE_TAC[MAP; FST; SND; ALL2; word_addr_def] THEN
  MATCH_MP_TAC(ARITH_RULE `sp <= sp0 ==> sp - k <= sp0 - k:num`) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 9030 (local; the theorem of line 9113 rebinds the name) *)
let IMP_memory_rel_bignum_alt = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vs vars i ws is_neg hd.
     memory_rel c be ts refs sp st m dm (APPEND vs vars) /\
     good_dimindex (:A) /\ ~small_int (:A) i /\
     Bignum i = DataElement [] (LENGTH ws) (NumTag is_neg,MAP wl_Word ws) /\
     LENGTH ws < sp /\
     encode_header c (val (word_or (word_shl (b2w is_neg) 2) (word 3):A word))
       (LENGTH ws) = SOME (hd:A word) ==>
     ?next curr m1.
       FLOOKUP st NextFree = SOME (wl_Word next) /\
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       (data_to_word_memoryProof_store_list next (MAP wl_Word (CONS hd ws)) m dm =
          SOME m1 /\
        memory_rel c be ts refs (sp - (LENGTH ws + 1))
          (st |+ (NextFree,
                  wl_Word (word_add next
                             (word_mul bytes_in_word (word (LENGTH ws + 1))))))
          m1 dm
          (CONS (data_Number i,make_ptr c (word_sub next curr) (word 0:A word)
                                  (LENGTH ws)) vars))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP4_X_ASM "memory_rel" (STRIP_ASSUME_TAC o
    REWRITE_RULE[MP4AUX_memory_rel_unfold; MAP_APPEND]) THEN
  MP4_X_ASM "ALL2" (MP_TAC o MATCH_MP EVERY2_APPEND_IMP_APPEND o MATCH_MP EVERY2_SWAP) THEN
  DISCH_THEN(X_CHOOSE_THEN `rs:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `roots:((A word_loc)heap_address)list` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  MP4_X_ASM "ALL2" (ASSUME_TAC o BETA_RULE o MATCH_MP EVERY2_SWAP o
    check (fun th -> rand(rator(concl th)) = `MAP SND (vars:(data_v#A word_loc)list)`)) THEN
  MP4_ASM "ALL2" (ASSUME_TAC o MATCH_MP EVERY2_LENGTH o
    check (fun th -> rand(rator(concl th)) = `MAP SND (vs:(data_v#A word_loc)list)`)) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `MAP FST (vs:(data_v#A word_loc)list)`;
                 `MAP FST (vars:(data_v#A word_loc)list)`; `refs:(data_v bvl_ref)spt`;
                 `rs:((A word_loc)heap_address)list`; `roots:((A word_loc)heap_address)list`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `be:bool`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`; `limit:num`;
                 `ts:num`; `i:int`; `LENGTH (ws:(A word)list)`; `NumTag is_neg`;
                 `MAP wl_Word (ws:(A word)list)`] bignum_alt_thm) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN ASM_REWRITE_TAC[LENGTH_MAP] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                          heap_element)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `make_header c (word_or (word_shl (b2w is_neg) 2) (word 3))
                  (LENGTH (ws:(A word)list)) = (hd:A word) /\
                LENGTH ws < 2 EXP (dimindex (:A) - 4) /\ decode_length c hd = word (LENGTH ws)`
    STRIP_ASSUME_TAC THENL
   [MP4_ASM "heap_in_memory_store"
      (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
    MP_TAC(ISPECL [`c:data_to_word_config`;
      `val (word_or (word_shl (b2w is_neg) 2) (word 3):A word)`;
      `LENGTH (ws:(A word)list)`; `hd:A word`] encode_header_IMP) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]] THEN
    MP4_EQ_ASM "encode_header" (MP_TAC o REWRITE_RULE[encode_header_def; WORD_VAL]) THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                 `dm:A word -> bool`; `vars:(data_v#A word_loc)list`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `limit:num`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
                 `roots:((A word_loc)heap_address)list`; `Bignum i:(A word_loc,
                    data_to_word_memoryProof_tag#(A word_loc)list)heap_element`;
                 `hd:A word`; `MAP wl_Word (ws:(A word)list)`; `data_Number i`;
                 `wl_Word (word 0):A word_loc`] MP4AUX_memory_rel_alloc_bottom) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `a - b - 1 = a - (b + 1)`]) THEN
  ASM_REWRITE_TAC[el_length_def; LENGTH_MAP] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP[word_el_def; word_payload_def; SEP_CLAUSES; LENGTH_MAP]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `curr:A word` (X_CHOOSE_THEN `m1:A word -> A word_loc`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`word_add (curr:A word) (word_mul bytes_in_word (word a))`;
    `curr:A word`; `m1:A word -> A word_loc`] THEN
  ASM_REWRITE_TAC[MAP; MP4AUX_addr_add] THEN
  MP4_ASM "heap_in_memory_store" (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def] o
    check (fun th -> rand(rator(rator(rator(rator(rator(rator(rator(rator(rator(concl th))))))))))
                     = `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                              heap_element)list`)) THEN
  ASM_SIMP_TAC[MP4AUX_make_ptr_get_addr]);;

(* HOL4 line 9113 *)
let IMP_memory_rel_bignum_alt = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars i ws is_neg hd.
     memory_rel c be ts refs sp st m dm vars /\
     good_dimindex (:A) /\ ~small_int (:A) i /\
     Bignum i = DataElement [] (LENGTH ws) (NumTag is_neg,MAP wl_Word ws) /\
     LENGTH ws < sp /\
     encode_header c (val (word_or (word_shl (b2w is_neg) 2) (word 3):A word))
       (LENGTH ws) = SOME (hd:A word) ==>
     ?next curr m1.
       FLOOKUP st NextFree = SOME (wl_Word next) /\
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       (data_to_word_memoryProof_store_list next (MAP wl_Word (CONS hd ws)) m dm =
          SOME m1 /\
        memory_rel c be ts refs (sp - (LENGTH ws + 1))
          (st |+ (NextFree,
                  wl_Word (word_add next
                             (word_mul bytes_in_word (word (LENGTH ws + 1))))))
          m1 dm
          (CONS (data_Number i,make_ptr c (word_sub next curr) (word 0:A word)
                                  (LENGTH ws)) vars))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC IMP_memory_rel_bignum_alt THEN
  MAP_EVERY EXISTS_TAC [`[]:(data_v#A word_loc)list`; `is_neg:bool`] THEN
  ASM_REWRITE_TAC[APPEND]);;

let MP4AUX_make_cons_ptr_get_addr = prove
 (`!c a (curr:A word) tag len.
     good_dimindex (:A) /\ backend_common_word_shift (:A) <= shift_length c ==>
     make_cons_ptr c (word_sub (word_add curr (word_mul bytes_in_word (word a))) curr)
       tag len =
     wl_Word (get_addr c a (wl_Word (ptr_bits c tag len)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[make_cons_ptr_def; get_addr_def;
              WORD_RULE `word_sub (word_add x y) x = y:A word`] THEN
  ASM_SIMP_TAC[bytes_in_word_mul_eq_shift; WORD_SHL_COMPOSE;
               ARITH_RULE `a <= b ==> a + b - a = b:num`] THEN
  REWRITE_TAC[injectivity "word_loc"] THEN
  ONCE_REWRITE_TAC[get_lowerbits_or_1] THEN WORD_BITWISE_TAC);;

(* HOL4 line 9116 *)
let memory_rel_Cons1 = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vals ws vars tag hd.
     memory_rel c be ts refs sp st m dm (APPEND (ZIP vals ws) vars) /\
     LENGTH vals = LENGTH (ws:(A word_loc)list) /\ ~(vals = []) /\
     encode_header c (4 * tag) (LENGTH ws) = SOME hd /\
     LENGTH ws < sp /\ good_dimindex (:A) ==>
     ?free (curr:A word) m1.
       FLOOKUP st NextFree = SOME (wl_Word free) /\
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       let w = word_add free (word_mul bytes_in_word (word (LENGTH ws + 1))) in
       data_to_word_memoryProof_store_list free (CONS (wl_Word hd) ws) m dm =
         SOME m1 /\
       memory_rel c be (ts + 1) refs (sp - (LENGTH ws + 1))
         (st |+ (NextFree,wl_Word w)) m1 dm
         (CONS (data_Block ts tag vals,
                make_cons_ptr c (word_sub free curr) tag (LENGTH ws)) vars)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
   MP4_X_ASM "memory_rel" (STRIP_ASSUME_TAC o
     REWRITE_RULE[MP4AUX_memory_rel_unfold; MAP_APPEND]) THEN
   SUBGOAL_THEN `MAP FST (ZIP (vals:data_v list) (ws:(A word_loc)list)) = vals /\
                 MAP SND (ZIP vals ws) = ws` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [ASM_SIMP_TAC[MAP_ZIP]; ALL_TAC] THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `vals:data_v list`;
                  `MAP FST (vars:(data_v#A word_loc)list)`; `refs:(data_v bvl_ref)spt`;
                  `hs:((A word_loc)heap_address)list`;
                  `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list`;
                  `be:bool`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`; `limit:num`;
                  `ts:num`; `tag:num`] cons_thm_alt) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `rs:((A word_loc)heap_address)list`
     (X_CHOOSE_THEN `roots:((A word_loc)heap_address)list`
     (X_CHOOSE_THEN `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                           heap_element)list` STRIP_ASSUME_TAC))) THEN
   RVEQ_TAC THEN
   MP4_X_ASM "ALL2" (MP_TAC o check (fun th -> mp4_is_app "APPEND" (rand(concl th)))) THEN
   ASM_SIMP_TAC[LIST_REL_APPEND_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o REWRITE_RULE[EVERY2_f_EQ; ETA_AX]) ASSUME_TAC) THEN
  SUBGOAL_THEN `make_header c (word_shl (word tag) 2) (LENGTH (ws:(A word_loc)list)) = (hd:A word) /\
                 LENGTH ws < 2 EXP (dimindex (:A) - 4) /\ decode_length c hd = word (LENGTH ws)`
     STRIP_ASSUME_TAC THENL
    [MP4_ASM "heap_in_memory_store"
       (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
     MP_TAC(ISPECL [`c:data_to_word_config`; `4 * tag`; `LENGTH (ws:(A word_loc)list)`;
       `hd:A word`] encode_header_IMP) THEN
     ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]] THEN
     MP4_EQ_ASM "encode_header" (MP_TAC o REWRITE_RULE[encode_header_def]) THEN
     COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; WORD_SHL_WORD] THEN
     CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `LENGTH (rs:((A word_loc)heap_address)list) = LENGTH (ws:(A word_loc)list)`
     ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts + 1`; `refs:(data_v bvl_ref)spt`;
                  `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                  `dm:A word -> bool`; `vars:(data_v#A word_loc)list`;
                  `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list`;
                  `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list`;
                  `limit:num`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
                  `roots:((A word_loc)heap_address)list`;
                  `BlockRep tag (rs:((A word_loc)heap_address)list):(A word_loc,
                     data_to_word_memoryProof_tag#(A word_loc)list)heap_element`;
                  `hd:A word`; `ws:(A word_loc)list`; `data_Block ts tag vals`;
                  `wl_Word (ptr_bits c tag (LENGTH (vals:data_v list))):A word_loc`]
                 MP4AUX_memory_rel_alloc_bottom) THEN
   ASM_REWRITE_TAC[BlockRep_def; el_length_def] THEN ANTS_TAC THENL
    [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[BlockRep_def]) THEN
     SIMP[word_el_def; word_payload_def; SEP_CLAUSES; LENGTH_MAP] THEN
     SUBGOAL_THEN `encode_header c (tag * 4) (LENGTH (ws:(A word_loc)list)) = SOME (hd:A word)`
     ASSUME_TAC THENL [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MP4_X_ASM "abs_ml_inv" (ASSUME_TAC o REWRITE_RULE[BlockRep_def; el_length_def;
     ASSUME `LENGTH (rs:((A word_loc)heap_address)list) = LENGTH (ws:(A word_loc)list)`;
     ASSUME `LENGTH (vals:data_v list) = LENGTH (ws:(A word_loc)list)`] o
     check (fun th -> mp4_is_app "insert" (rand(rator(rator(concl th)))) = false &&
                      can (find_term (fun t -> t = `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`)) (concl th))) THEN
   ASM_REWRITE_TAC[SEP_CLAUSES]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `curr:A word` (X_CHOOSE_THEN `m1:A word -> A word_loc`
     STRIP_ASSUME_TAC)) THEN
   MAP_EVERY EXISTS_TAC [`word_add (curr:A word) (word_mul bytes_in_word (word a))`;
     `curr:A word`; `m1:A word -> A word_loc`] THEN
   ASM_REWRITE_TAC[MP4AUX_addr_add] THEN
   MP4_ASM "heap_in_memory_store" (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def] o
     check (fun th -> rand(rator(rator(rator(rator(rator(rator(rator(rator(rator(concl th))))))))))
                      = `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                               heap_element)list`)) THEN
   ASM_SIMP_TAC[MP4AUX_make_cons_ptr_get_addr]);;

(* HOL4 line 9202 *)
let memory_rel_MutCons = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vals ws vars tag hd index ptr.
     memory_rel c be ts refs sp st m dm (APPEND (ZIP vals ws) vars) /\
     LENGTH vals = LENGTH (ws:(A word_loc)list) /\ ~(vals = []) /\
     encode_header c (4 * tag) (LENGTH ws) = SOME hd /\
     LENGTH ws < sp /\ good_dimindex (:A) /\
     index < LENGTH vals /\ ~(ptr IN domain refs) /\
     (!gs. ~(data_to_word_config_gc_kind c = Generational gs)) ==>
     ?free (curr:A word) m1.
       FLOOKUP st NextFree = SOME (wl_Word free) /\
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       let w = word_add free (word_mul bytes_in_word (word (LENGTH ws + 1))) in
       data_to_word_memoryProof_store_list free (CONS (wl_Word hd) ws) m dm =
         SOME m1 /\
       memory_rel c be ts
         (insert ptr (MutBlock tag F (TAKE index vals) (EL index vals)
                                     (DROP (index + 1) vals)) refs)
         (sp - (LENGTH ws + 1))
         (st |+ (NextFree,wl_Word w)) m1 dm
         (CONS (data_RefPtr F ptr,
                make_cons_ptr c (word_sub free curr) tag (LENGTH ws)) vars)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
   MP4_X_ASM "memory_rel" (STRIP_ASSUME_TAC o
     REWRITE_RULE[MP4AUX_memory_rel_unfold; MAP_APPEND]) THEN
   SUBGOAL_THEN `MAP FST (ZIP (vals:data_v list) (ws:(A word_loc)list)) = vals /\
                 MAP SND (ZIP vals ws) = ws` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [ASM_SIMP_TAC[MAP_ZIP]; ALL_TAC] THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `vals:data_v list`;
                  `MAP FST (vars:(data_v#A word_loc)list)`; `refs:(data_v bvl_ref)spt`;
                  `hs:((A word_loc)heap_address)list`;
                  `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list`;
                  `be:bool`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`; `limit:num`;
                  `ts:num`; `index:num`; `ptr:num`; `tag:num`] mutcons_thm) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `rs:((A word_loc)heap_address)list`
     (X_CHOOSE_THEN `roots:((A word_loc)heap_address)list`
     (X_CHOOSE_THEN `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                           heap_element)list` STRIP_ASSUME_TAC))) THEN
   RVEQ_TAC THEN
   MP4_X_ASM "ALL2" (MP_TAC o check (fun th -> mp4_is_app "APPEND" (rand(concl th)))) THEN
   ASM_SIMP_TAC[LIST_REL_APPEND_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o REWRITE_RULE[EVERY2_f_EQ; ETA_AX]) ASSUME_TAC) THEN
  SUBGOAL_THEN `make_header c (word_shl (word tag) 2) (LENGTH (ws:(A word_loc)list)) = (hd:A word) /\
                 LENGTH ws < 2 EXP (dimindex (:A) - 4) /\ decode_length c hd = word (LENGTH ws)`
     STRIP_ASSUME_TAC THENL
    [MP4_ASM "heap_in_memory_store"
       (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
     MP_TAC(ISPECL [`c:data_to_word_config`; `4 * tag`; `LENGTH (ws:(A word_loc)list)`;
       `hd:A word`] encode_header_IMP) THEN
     ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]] THEN
     MP4_EQ_ASM "encode_header" (MP_TAC o REWRITE_RULE[encode_header_def]) THEN
     COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; WORD_SHL_WORD] THEN
     CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `LENGTH (rs:((A word_loc)heap_address)list) = LENGTH (ws:(A word_loc)list)`
     ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
                  `insert ptr (MutBlock tag F (TAKE index vals) (EL index vals)
                     (DROP (index + 1) vals)) (refs:(data_v bvl_ref)spt)`;
                  `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                  `dm:A word -> bool`; `vars:(data_v#A word_loc)list`;
                  `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list`;
                  `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list`;
                  `limit:num`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
                  `roots:((A word_loc)heap_address)list`;
                  `BlockRep tag (rs:((A word_loc)heap_address)list):(A word_loc,
                     data_to_word_memoryProof_tag#(A word_loc)list)heap_element`;
                  `hd:A word`; `ws:(A word_loc)list`; `data_RefPtr F ptr`;
                  `wl_Word (ptr_bits c tag (LENGTH (vals:data_v list))):A word_loc`]
                 MP4AUX_memory_rel_alloc_bottom) THEN
   ASM_REWRITE_TAC[BlockRep_def; el_length_def] THEN ANTS_TAC THENL
    [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[BlockRep_def]) THEN
     SIMP[word_el_def; word_payload_def; SEP_CLAUSES; LENGTH_MAP] THEN
     SUBGOAL_THEN `encode_header c (tag * 4) (LENGTH (ws:(A word_loc)list)) = SOME (hd:A word)`
     ASSUME_TAC THENL [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MP4_X_ASM "abs_ml_inv" (ASSUME_TAC o REWRITE_RULE[BlockRep_def; el_length_def;
     ASSUME `LENGTH (rs:((A word_loc)heap_address)list) = LENGTH (ws:(A word_loc)list)`;
     ASSUME `LENGTH (vals:data_v list) = LENGTH (ws:(A word_loc)list)`] o
     check (fun th -> mp4_is_app "insert" (rand(rator(rator(concl th)))) = false &&
                      can (find_term (fun t -> t = `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`)) (concl th))) THEN
   ASM_REWRITE_TAC[SEP_CLAUSES]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `curr:A word` (X_CHOOSE_THEN `m1:A word -> A word_loc`
     STRIP_ASSUME_TAC)) THEN
   MAP_EVERY EXISTS_TAC [`word_add (curr:A word) (word_mul bytes_in_word (word a))`;
     `curr:A word`; `m1:A word -> A word_loc`] THEN
   ASM_REWRITE_TAC[MP4AUX_addr_add] THEN
   MP4_ASM "heap_in_memory_store" (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def] o
     check (fun th -> rand(rator(rator(rator(rator(rator(rator(rator(rator(rator(concl th))))))))))
                      = `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                               heap_element)list`)) THEN
   ASM_SIMP_TAC[MP4AUX_make_cons_ptr_get_addr]);;

(* HOL4 line 9289 *)
let INJ_FUPDATE = prove
 (`!(tf:(A,B)fmap) s ts2 x.
     INJ (FAPPLY tf) (FDOM tf) s /\ ~(ts2 IN FDOM tf) /\ ~(x IN FRANGE tf) /\
     x IN s ==>
     INJ (FAPPLY (tf |+ (ts2,x))) (FDOM (tf |+ (ts2,x))) s`,
  REWRITE_TAC[INJ; FDOM_FUPDATE; FAPPLY_FUPDATE_THM; FRANGE_DEF; IN_INSERT;
              IN_ELIM_THM] THEN
  MESON_TAC[]);;

(* HOL4 line 9296 *)
let finalise_cons_none = prove
 (`!ptr v refs ts_opt v' refs' ts'.
     data_finalise_cons v refs ts_opt = SOME (v',refs',ts') /\
     lookup ptr refs = NONE ==>
     lookup ptr refs' = NONE`,
  GEN_TAC THEN MATCH_MP_TAC data_finalise_cons_ind THEN
  REWRITE_TAC[data_finalise_cons_def; option_INJ; PAIR_EQ] THEN
  CONJ_TAC THENL [ALL_TAC; REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[option_case_eq; case_eq "bvl_ref"; COND_CASE_EQ; pair_case_eq;
              option_DISTINCT; option_INJ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[lookup_insert] THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]) THEN
  ASM_MESON_TAC[lookup_delete]);;

let MP4AUX_dest_thunk_swap = prove
 (`!v refs refs1.
     (!n. lookup n refs = lookup n refs1) ==>
     data_dest_thunk v refs = data_dest_thunk v refs1`,
  GEN_TAC THEN CASES_ON `v:data_v` THEN REWRITE_TAC[data_dest_thunk_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MP4AUX_v_inv_ck_swap_refs = prove
 (`!ck conf v refs1 (p:(A word_loc)heap_address#(num,num)fmap#(num,num)fmap#
                      ((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                       heap_element)list).
     v_inv_ck ck conf v refs1 p ==>
     !refs. (!n. lookup n refs = lookup n refs1) ==> v_inv_ck ck conf v refs p`,
  let gen_tac =
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[v_inv_ck_cases] THEN
    REWRITE_TAC[distinctness "data_v"; injectivity "data_v"; PAIR_EQ] THEN
    ASM_MESON_TAC[] in
  MATCH_MP_TAC v_inv_ck_ind THEN REPEAT CONJ_TAC THENL
   [gen_tac; gen_tac; gen_tac; gen_tac; gen_tac;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC v_inv_ck_RefPtrThunk THEN
    MAP_EVERY EXISTS_TAC [`ev:thunk_mode`; `v:data_v`; `x:(A word_loc)heap_address`] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MP4AUX_dest_thunk_swap th]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC v_inv_ck_RefPtrThunkInlined THEN
    EXISTS_TAC `v:data_v` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MP4AUX_dest_thunk_swap th]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    gen_tac;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC v_inv_ck_BlockCons THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `~(ck = 0)`) o
      check (fun th -> is_imp (concl th) && concl th <> `F`)) THEN
    MATCH_MP_TAC MONO_ALL2 THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 9311 *)
let v_inv_swap_refs = prove
 (`!c v refs1 (x:(A word_loc)heap_address) f tf heap refs.
     v_inv c v refs1 (x,f,tf,heap) /\
     (!n. lookup n refs = lookup n refs1) ==>
     v_inv c v refs (x,f,tf,heap)`,
  REWRITE_TAC[v_inv_eq] THEN MESON_TAC[MP4AUX_v_inv_ck_swap_refs]);;

(* HOL4 line 9333 *)
let bc_stack_ref_inv_swap_refs = prove
 (`!c ts vars refs xs
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be refs1.
     bc_stack_ref_inv c ts vars refs (xs,heap,be) /\
     (!n. lookup n refs = lookup n refs1) ==>
     bc_stack_ref_inv c ts vars refs1 (xs,heap,be)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `domain refs = domain (refs1:(data_v bvl_ref)spt) /\
    (!v (x:(A word_loc)heap_address) f tf
       (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
              heap_element)list).
       v_inv c v refs (x,f,tf,heap) <=> v_inv c v refs1 (x,f,tf,heap)) /\
    (!v. data_dest_thunk v refs = data_dest_thunk v refs1) /\
    ref_edge refs = ref_edge refs1 /\
    (!stack. all_ts refs stack = all_ts refs1 stack) /\
    (!stack. all_vs refs stack = all_vs refs1 stack)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; domain_lookup] THEN ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC v_inv_swap_refs THENL
       [EXISTS_TAC `refs:(data_v bvl_ref)spt`; EXISTS_TAC `refs1:(data_v bvl_ref)spt`] THEN
      ASM_REWRITE_TAC[];
      GEN_TAC THEN MATCH_MP_TAC MP4AUX_dest_thunk_swap THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FUN_EQ_THM; ref_edge_def] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[all_ts_def] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[all_vs_def] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP4_X_ASM "bc_stack_ref_inv" MP_TAC THEN
  REWRITE_TAC[bc_stack_ref_inv_def; reachable_refs_def; bc_ref_inv_def] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 9364 *)
let blocks_unique_SUBSET = prove
 (`!ts vs1 vs2. blocks_unique ts vs2 /\ vs1 SUBSET vs2 ==> blocks_unique ts vs1`,
  REWRITE_TAC[blocks_unique_def; SUBSET] THEN MESON_TAC[]);;

(* HOL4 line 9370 *)
let blocks_unique_INSERT = prove
 (`!ts vs tag l.
     blocks_unique ts vs ==> blocks_unique (SUC ts) (data_Block ts tag l INSERT vs)`,
  REWRITE_TAC[blocks_unique_def; IN_INSERT; injectivity "data_v"] THEN
  MESON_TAC[LT_REFL; LT_SUC; LT]);;

(* HOL4 line 9377 *)
let all_ts_CONS_SUBSET = prove
 (`!refs stack x. all_ts refs stack SUBSET all_ts refs (CONS x stack)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC all_ts_SUBSET_gen THEN REWRITE_TAC[MEM] THEN
  MESON_TAC[]);;

(* HOL4 line 9383 *)
let in_all_vs_stack = prove
 (`!v stack (refs:(data_v bvl_ref)spt).
     MEM v (v_all_vs stack) ==> v IN all_vs refs stack`,
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]);;

(* HOL4 line 9389 *)
let in_all_vs_MutBlock = prove
 (`!n refs tg fin l c r v stack.
     lookup n refs = SOME (MutBlock tg fin l c r) /\
     MEM v (v_all_vs (APPEND (APPEND l [c]) r)) ==>
     v IN all_vs refs stack`,
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]);;

(* HOL4 line 9399 *)
let all_vs_CONS_SUBSET = prove
 (`!x refs stack.
     x IN all_vs refs stack ==> all_vs refs (CONS x stack) SUBSET all_vs refs stack`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:data_v` THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [CONS_APPEND] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [all_vs_def] THEN
  REWRITE_TAC[IN_UNION; IN_ELIM_THM; v_all_vs_append; MEM_APPEND] THEN
  STRIP_TAC THEN
  FIRST [MATCH_MP_TAC v_in_all_vs THEN EXISTS_TAC `x:data_v` THEN ASM_REWRITE_TAC[] THEN
         NO_TAC;
         REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM; v_all_vs_append; MEM_APPEND] THEN
         ASM_MESON_TAC[]]);;

(* HOL4 line 9422 *)
let all_vs_MutBlock_centre = prove
 (`!ptr refs tag fin left cen right stack.
     lookup ptr refs = SOME (MutBlock tag fin left cen right) ==>
     all_vs refs (CONS cen stack) SUBSET all_vs refs stack`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC all_vs_CONS_SUBSET THEN
  MATCH_MP_TAC in_all_vs_MutBlock THEN
  MAP_EVERY EXISTS_TAC [`ptr:num`; `tag:num`; `fin:bool`; `left:data_v list`;
                        `cen:data_v`; `right:data_v list`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEM_v_all_vs THEN
  REWRITE_TAC[MEM_APPEND; MEM]);;

(* HOL4 line 9433 *)
let all_vs_MutBlock_T = prove
 (`!ptr refs tag left cen right ts2 res vars b.
     lookup ptr refs = SOME (MutBlock tag F left cen right) ==>
     all_vs (insert ptr (MutBlock tag T left cen right) refs)
       (CONS (data_Block ts2 tag (APPEND (APPEND left [res]) right)) vars) SUBSET
     data_Block ts2 tag (APPEND (APPEND left [res]) right) INSERT
     all_vs refs (CONS res (CONS (data_RefPtr b ptr) vars))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `v_all_vs (CONS res (CONS (data_RefPtr b ptr) vars)) =
                APPEND (v_all_vs [res]) (CONS (data_RefPtr b ptr) (v_all_vs vars))`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`[res:data_v]`; `CONS (data_RefPtr b ptr) vars`] v_all_vs_append) THEN
    REWRITE_TAC[APPEND; v_all_vs_def]; ALL_TAC] THEN
  ASM_REWRITE_TAC[SUBSET; IN_INSERT; all_vs_def; IN_UNION; IN_ELIM_THM; lookup_insert;
              v_all_vs_def; v_all_vs_append; MEM_APPEND; MEM; COND_CASE_EQ;
              option_INJ; distinctness "bvl_ref"; injectivity "bvl_ref"] THEN
  X_GEN_TAC `y:data_v` THEN STRIP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 9477 *)
let reachable_refs_MutBlock_centre = prove
 (`!ptr refs tag fin left cen right b vars n.
     lookup ptr refs = SOME (MutBlock tag fin left cen right) /\
     reachable_refs (CONS cen (CONS (data_RefPtr b ptr) vars)) refs n ==>
     reachable_refs (CONS (data_RefPtr b ptr) vars) refs n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[reachable_refs_def; MEM] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`data_RefPtr b ptr`; `ptr:num`] THEN
    REWRITE_TAC[MEM; get_refs_def] THEN MATCH_MP_TAC RTC_TRANS THEN
    EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RTC_INC THEN
    ASM_REWRITE_TAC[ref_edge_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[get_refs_def; MEM_FLAT; MEM_MAP; MEM_APPEND; MEM] THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* HOL4 line 9491 *)
let ref_edge_insert_MutBlock = prove
 (`!ptr refs tg fin1 fin2 l c r.
     lookup ptr refs = SOME (MutBlock tg fin1 l c r) ==>
     ref_edge (insert ptr (MutBlock tg fin2 l c r) refs) = ref_edge refs`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; ref_edge_MutBlock] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ref_edge_def] THEN
  CASE_REWRITE_TAC[]);;

(* HOL4 line 9500 *)
let reachable_refs_MutBlock_T = prove
 (`!ptr refs tag left cen right ts2 res vars b n.
     lookup ptr refs = SOME (MutBlock tag F left cen right) /\
     reachable_refs
       (CONS (data_Block ts2 tag (APPEND (APPEND left [res]) right)) vars)
       (insert ptr (MutBlock tag T left cen right) refs) n ==>
     reachable_refs (CONS res (CONS (data_RefPtr b ptr) vars)) refs n`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[reachable_refs_def; MEM] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP ref_edge_insert_MutBlock th]) THEN
  STRIP_TAC THEN RVEQ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[get_refs_def; MEM_FLAT; MEM_MAP; MEM_APPEND; MEM] o
      check (fun th -> mp4_is_app "MEM" (concl th) &&
                       mp4_is_app "get_refs" (rand (concl th)))) THEN
    STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`data_RefPtr b ptr`; `ptr:num`];
      MAP_EVERY EXISTS_TAC [`res:data_v`; `r:num`];
      MAP_EVERY EXISTS_TAC [`data_RefPtr b ptr`; `ptr:num`]] THEN
    REWRITE_TAC[MEM; get_refs_def] THEN TRY(ASM_MESON_TAC[]) THEN
    MATCH_MP_TAC RTC_TRANS THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RTC_INC THEN ASM_REWRITE_TAC[ref_edge_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[get_refs_def; MEM_FLAT; MEM_MAP; MEM_APPEND; MEM] THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* HOL4 line 9524 *)
let dest_thunk_insert_MutBlock = prove
 (`!ptr refs tg fin1 fin2 l c r v.
     lookup ptr refs = SOME (MutBlock tg fin1 l c r) ==>
     data_dest_thunk v (insert ptr (MutBlock tg fin2 l c r) refs) =
     data_dest_thunk v refs`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CASES_ON `v:data_v` THEN
  REWRITE_TAC[data_dest_thunk_def; lookup_insert] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

(* HOL4 line 9532 *)
let bc_stack_ref_inv_MutBlock_centre = prove
 (`!c ts b ptr vars refs x xs
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be tag left cen right.
     bc_stack_ref_inv c ts (CONS (data_RefPtr b ptr) vars) refs
       (CONS x xs,heap,be) /\
     lookup ptr refs = SOME (MutBlock tag F left cen right) ==>
     ?ptr_n zs.
       x = Pointer ptr_n (ref_ptr_annot c (lookup ptr refs)) /\
       heap_lookup ptr_n heap = SOME (BlockRep tag zs) /\
       LENGTH zs = LENGTH left + 1 + LENGTH right /\
       bc_stack_ref_inv c ts (CONS cen (CONS (data_RefPtr b ptr) vars)) refs
         (CONS (EL (LENGTH left) zs) (CONS x xs),heap,be)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bc_stack_ref_inv_def; ALL2] THEN STRIP_TAC THEN
  MP4_ASM "v_inv" (MP_TAC o REWRITE_RULE[v_inv_def]) THEN
  ASM_REWRITE_TAC[distinctness "bvl_ref"; option_INJ] THEN STRIP_TAC THEN
  MP4_VAR_ASM "x" SUBST_ALL_TAC THEN
  SUBGOAL_THEN `reachable_refs (CONS (data_RefPtr b ptr) vars) refs ptr` ASSUME_TAC THENL
   [REWRITE_TAC[reachable_refs_def] THEN
    MAP_EVERY EXISTS_TAC [`data_RefPtr b ptr`; `ptr:num`] THEN
    REWRITE_TAC[MEM; get_refs_def; RTC_REFL]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_forall (concl th) &&
      can (find_term (mp4_is_app "bc_ref_inv")) (concl th)
    then MP_TAC (CASE_REWRITE_RULE[] (REWRITE_RULE[bc_ref_inv_def; FLOOKUP_DEF;
           ASSUME `ptr IN FDOM (f:(num,num)fmap)`;
           ASSUME `lookup ptr (refs:(data_v bvl_ref)spt) =
                   SOME (MutBlock tag F (left:data_v list) cen right)`]
         (MP (SPEC `ptr:num` th)
           (CONJ (ASSUME `reachable_refs (CONS (data_RefPtr b ptr) vars) refs ptr`)
                 (ASSUME `ptr IN FDOM (f:(num,num)fmap)`)))))
    else failwith "") THEN
  DISCH_THEN(X_CHOOSE_THEN `zs:((A word_loc)heap_address)list` STRIP_ASSUME_TAC o
             CONJUNCT2 o CONJUNCT2) THEN
  MAP_EVERY EXISTS_TAC [`FAPPLY f (ptr:num):num`; `zs:((A word_loc)heap_address)list`] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP EVERY2_LENGTH o
    check (fun th -> mp4_is_app "ALL2" (concl th) &&
                     rand(concl th) = `APPEND (APPEND (left:data_v list) [cen]) right`)) THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `all_ts refs (CONS (data_RefPtr b ptr) vars)` THEN
    ASM_REWRITE_TAC[all_ts_CONS_SUBSET];
    MATCH_MP_TAC blocks_unique_SUBSET THEN
    EXISTS_TAC `all_vs refs (CONS (data_RefPtr b ptr) vars)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC all_vs_MutBlock_centre THEN ASM_MESON_TAC[];
    MP4_ASM "ALL2" (MP_TAC o REWRITE_RULE[LIST_REL_EL_EQN] o
      check (fun th -> rand(concl th) = `APPEND (APPEND (left:data_v list) [cen]) right`)) THEN
    DISCH_THEN(MP_TAC o SPEC `LENGTH (left:data_v list)` o CONJUNCT2) THEN
    REWRITE_TAC[EL_APPEND_EQN; LENGTH_APPEND; LENGTH] THEN
    REWRITE_TAC[LT_REFL; SUB_REFL; EL; HD; ARITH_RULE `n < n + SUC 0`] THEN
    ANTS_TAC THENL [MP4_EQ_ASM "LENGTH" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC; SIMP_TAC[]];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC reachable_refs_MutBlock_centre THEN ASM_MESON_TAC[]]);;

(* HOL4 line 9564 *)
let bc_stack_ref_inv_union_del_ins_lemma = prove
 (`!c ts vars refs frame xs
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be ptr x.
     bc_stack_ref_inv c ts vars (union refs frame) (xs,heap,be) /\
     lookup ptr refs = SOME x ==>
     bc_stack_ref_inv c ts vars (union (delete ptr refs) (insert ptr x frame))
       (xs,heap,be)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC bc_stack_ref_inv_swap_refs THEN
  EXISTS_TAC `union refs frame:(data_v bvl_ref)spt` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[lookup_union; lookup_delete; lookup_insert] THEN
  ASM_CASES_TAC `n:num = ptr` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* values keep their invariant when a MutBlock is finalised and a time stamp *)
(* is added for the new block                                                *)
let MP4AUX_v_inv_MutBlock_T = prove
 (`!c v refs (x:(A word_loc)heap_address) f tf
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) ptr tag left cen right ts2 p.
     v_inv c v refs (x,f,tf,heap) /\
     lookup ptr refs = SOME (MutBlock tag F left cen right) /\
     ~(ts2 IN FDOM tf) ==>
     v_inv c v (insert ptr (MutBlock tag T left cen right) refs)
       (x,f,tf |+ (ts2,p),heap)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC v_inv_MutBlock_fin THEN
  MAP_EVERY EXISTS_TAC [`F`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC v_inv_SUBMAP THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
  ASM_REWRITE_TAC[SUBMAP_REFL; SUBMAP_FUPDATE_EQN; heap_store_rel_def]);;

(* HOL4 line 9577 *)
let bc_stack_ref_inv_MutBlock_F = prove
 (`!c ts2 res b ptr vars refs zs ptr_n tag left right xs
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be cen.
     bc_stack_ref_inv c ts2
       (CONS res (CONS (data_RefPtr b ptr) vars)) refs
       (CONS (EL (LENGTH left) zs)
          (CONS (Pointer ptr_n
                   (wl_Word (ptr_bits c tag (LENGTH left + (LENGTH right + 1)))))
             xs),heap,be) /\
     heap_lookup ptr_n heap = SOME (BlockRep tag zs) /\
     lookup ptr refs = SOME (MutBlock tag F left cen right) ==>
     bc_stack_ref_inv c (SUC ts2)
       (CONS (data_Block ts2 tag (APPEND (APPEND left [res]) right)) vars)
       (insert ptr (MutBlock tag T left cen right) refs)
       (CONS (Pointer ptr_n
                (wl_Word (ptr_bits c tag (LENGTH left + (LENGTH right + 1))))) xs,
        heap,be)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bc_stack_ref_inv_def; ALL2] THEN STRIP_TAC THEN
   MP4_ASM "v_inv" (MP_TAC o REWRITE_RULE[v_inv_def] o
     check (fun th -> rand(rator(rator(concl th))) = `data_RefPtr b ptr`)) THEN
   ASM_REWRITE_TAC[distinctness "bvl_ref"; option_INJ; injectivity "heap_address"] THEN
   STRIP_TAC THEN MP4_VAR_ASM "ptr_n" SUBST_ALL_TAC THEN
  SUBGOAL_THEN `reachable_refs (CONS res (CONS (data_RefPtr b ptr) vars)) refs ptr` ASSUME_TAC THENL
    [REWRITE_TAC[reachable_refs_def] THEN
     MAP_EVERY EXISTS_TAC [`data_RefPtr b ptr`; `ptr:num`] THEN
     REWRITE_TAC[MEM; get_refs_def; RTC_REFL]; ALL_TAC] THEN
   FIRST_ASSUM(fun th -> if is_forall (concl th) &&
       can (find_term (mp4_is_app "bc_ref_inv")) (concl th)
     then MP_TAC (CASE_REWRITE_RULE[] (REWRITE_RULE[bc_ref_inv_def; FLOOKUP_DEF;
            ASSUME `ptr IN FDOM (f:(num,num)fmap)`;
            ASSUME `lookup ptr (refs:(data_v bvl_ref)spt) =
                    SOME (MutBlock tag F (left:data_v list) cen right)`]
          (MP (SPEC `ptr:num` th)
            (CONJ (ASSUME `reachable_refs (CONS res (CONS (data_RefPtr b ptr) vars)) refs ptr`)
                  (ASSUME `ptr IN FDOM (f:(num,num)fmap)`)))))
     else failwith "") THEN
   REWRITE_TAC[] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `zs1:((A word_loc)heap_address)list` STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `zs1:((A word_loc)heap_address)list = zs` SUBST_ALL_TAC THENL
    [MP4_EQ_ASM "heap_lookup" (MP_TAC o check (fun th -> rand(rand(concl th)) =
       `BlockRep tag (zs1:((A word_loc)heap_address)list):(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element`)) THEN
     ASM_REWRITE_TAC[option_INJ; BlockRep_def; injectivity "heap_element"] THEN MESON_TAC[];
     ALL_TAC] THEN
  SUBGOAL_THEN `~(ts2 IN FDOM (tf:(num,num)fmap))` ASSUME_TAC THENL
    [MP4_ASM "SUBSET" (MP_TAC o check (fun th -> aconv (rand(concl th)) `{n:num | n < ts2}`)) THEN
     REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[LT_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (zs:((A word_loc)heap_address)list) = LENGTH (left:data_v list) + 1 + LENGTH (right:data_v list)`
     ASSUME_TAC THENL
    [MP4_ASM "ALL2" (MP_TAC o MATCH_MP EVERY2_LENGTH o check (fun th ->
       rand(concl th) = `APPEND (APPEND (left:data_v list) [cen]) right`)) THEN
     REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`;
     `(tf:(num,num)fmap) |+ (ts2,FAPPLY f (ptr:num))`] THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC[domain_insert] THEN MP4_ASM "SUBSET" (MP_TAC o check (fun th ->
     rand(concl th) = `domain (refs:(data_v bvl_ref)spt)`)) THEN SET_TAC[];
   MATCH_MP_TAC INJ_FUPDATE THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
    [MP4_ASM "~" (MP_TAC o check (fun th -> can (find_term (mp4_is_app "IMAGE")) (concl th))) THEN
     REWRITE_TAC[FRANGE_DEF; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
     REWRITE_TAC[isSomeDataElement_def; BlockRep_def] THEN MESON_TAC[]];
   REWRITE_TAC[FDOM_FUPDATE; INSERT_SUBSET] THEN CONJ_TAC THENL
    [REWRITE_TAC[all_ts_def; LET_DEF; LET_END_DEF; IN_ELIM_THM] THEN
     EXISTS_TAC `data_Block ts2 tag (APPEND (APPEND left [res]) right)` THEN
     REWRITE_TAC[MEM; v_all_ts_def];
     ALL_TAC] THEN
   MATCH_MP_TAC SUBSET_TRANS THEN
   EXISTS_TAC `all_ts refs (CONS res (CONS (data_RefPtr b ptr) vars))` THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC all_ts_SUBSET_ts THEN
   REWRITE_TAC[MEM; lookup_insert] THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC `x:data_v` THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
   ASM_CASES_TAC `n:num = ptr` THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN
     SUBGOAL_THEN `r':data_v bvl_ref = MutBlock tag F left cen right` SUBST_ALL_TAC THENL
      [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
     MAP_EVERY EXISTS_TAC [`ptr:num`; `MutBlock tag T (left:data_v list) cen right`] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[find_ref_def]) THEN ASM_REWRITE_TAC[find_ref_def];
     MAP_EVERY EXISTS_TAC [`n:num`; `r':data_v bvl_ref`] THEN ASM_REWRITE_TAC[]];
    RVEQ_TAC THEN
   EXISTS_TAC `data_Block ts2 tag (APPEND (APPEND left [res]) right)` THEN
   REWRITE_TAC[v_all_ts_def; MAP_APPEND; FLAT_APPEND; MAP; FLAT; MEM_APPEND; MEM;
               APPEND_NIL] THEN ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[v_all_ts_def; MEM]) THEN RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[v_all_ts_def; MEM]) THEN ASM_REWRITE_TAC[] THEN FIRST_ASSUM CONTR_TAC;
    EXISTS_TAC `x:data_v` THEN ASM_REWRITE_TAC[]];
   REWRITE_TAC[FDOM_FUPDATE; INSERT_SUBSET; IN_ELIM_THM; LT] THEN
   MP4_ASM "SUBSET" (MP_TAC o check (fun th -> aconv (rand(concl th)) `{n:num | n < ts2}`)) THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM; LT] THEN MESON_TAC[];
   MATCH_MP_TAC blocks_unique_SUBSET THEN
   EXISTS_TAC `data_Block ts2 tag (APPEND (APPEND left [res]) right) INSERT
               all_vs refs (CONS res (CONS (data_RefPtr b ptr) vars))` THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC blocks_unique_INSERT THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC all_vs_MutBlock_T THEN ASM_REWRITE_TAC[]];
   REWRITE_TAC[v_inv_def; APPEND_EQ_NIL; NOT_CONS_NIL; ref_ptr_annot_def] THEN
   MAP_EVERY EXISTS_TAC [`FAPPLY f (ptr:num):num`; `zs:((A word_loc)heap_address)list`] THEN
   ASM_REWRITE_TAC[FLOOKUP_UPDATE; injectivity "heap_address"] THEN
   REWRITE_TAC[LIST_REL_EL_EQN; LENGTH_APPEND; LENGTH] THEN
  CONJ_TAC THENL [MP4_EQ_ASM "LENGTH" (fun th -> REWRITE_TAC[th]) THEN ARITH_TAC; ALL_TAC] THEN
   X_GEN_TAC `k:num` THEN DISCH_TAC THEN
   MATCH_MP_TAC MP4AUX_v_inv_MutBlock_T THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k = LENGTH (left:data_v list)` THENL
    [ASM_REWRITE_TAC[EL_APPEND_EQN; LENGTH_APPEND; LENGTH; LT_REFL; SUB_REFL;
                     ARITH_RULE `n < n + SUC 0`; EL; HD];
     MP4_ASM "ALL2" (MP_TAC o REWRITE_RULE[LIST_REL_EL_EQN] o check (fun th ->
       rand(concl th) = `APPEND (APPEND (left:data_v list) [cen]) right`)) THEN
     DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT2) THEN
     REWRITE_TAC[EL_APPEND_EQN; LENGTH_APPEND; LENGTH] THEN
     ANTS_TAC THENL
      [MP4_EQ_ASM "LENGTH" (fun th -> REWRITE_TAC[th]) THEN
       UNDISCH_TAC `k < (LENGTH (left:data_v list) + SUC 0) + LENGTH (right:data_v list)` THEN
       ARITH_TAC; ALL_TAC] THEN
     COND_CASES_TAC THEN REWRITE_TAC[] THEN
     SUBGOAL_THEN `k < LENGTH (left:data_v list)` (fun th -> REWRITE_TAC[th]) THEN
     UNDISCH_TAC `~(k = LENGTH (left:data_v list))` THEN
     UNDISCH_TAC `k < LENGTH (left:data_v list) + SUC 0` THEN ARITH_TAC];
   MP4_ASM "ALL2" (MP_TAC o check (fun th -> rand(concl th) = `xs:((A word_loc)heap_address)list`)) THEN
   MATCH_MP_TAC MONO_ALL2 THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC MP4AUX_v_inv_MutBlock_T THEN ASM_REWRITE_TAC[];
   X_GEN_TAC `n:num` THEN STRIP_TAC THEN
   SUBGOAL_THEN `bc_ref_inv c n refs (f,tf,heap:((A word_loc,data_to_word_memoryProof_tag#
     (A word_loc)list)heap_element)list,be)` MP_TAC THENL
    [FIRST_ASSUM(fun th -> if is_forall (concl th) &&
         can (find_term (mp4_is_app "bc_ref_inv")) (concl th) &&
         can (find_term (fun t -> t = `refs:(data_v bvl_ref)spt`)) (concl th)
       then MATCH_MP_TAC th else failwith "") THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC reachable_refs_MutBlock_T THEN
     MAP_EVERY EXISTS_TAC [`tag:num`; `left:data_v list`; `cen:data_v`;
       `right:data_v list`; `ts2:num`] THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF; lookup_insert] THEN
   ASM_CASES_TAC `n:num = ptr` THEN ASM_REWRITE_TAC[] THENL
   [CASE_REWRITE_TAC[] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN
     `zs2:((A word_loc)heap_address)list` STRIP_ASSUME_TAC)) THEN
   EXISTS_TAC `zs2:((A word_loc)heap_address)list` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> mp4_is_app "ALL2" (concl th) &&
     rand(rator(concl th)) = `zs2:((A word_loc)heap_address)list`)) THEN
   MATCH_MP_TAC MONO_ALL2 THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC MP4AUX_v_inv_MutBlock_T THEN ASM_REWRITE_TAC[];
    CASE_REWRITE_TAC[] THEN
   CASES_ON `lookup n (refs:(data_v bvl_ref)spt)` THEN CASE_REWRITE_TAC[] THEN
   CASES_ON `a:data_v bvl_ref` THEN CASE_REWRITE_TAC[] THENL
    [DISCH_THEN(X_CHOOSE_THEN `zs2:((A word_loc)heap_address)list` STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `zs2:((A word_loc)heap_address)list` THEN ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> mp4_is_app "ALL2" (concl th) &&
       rand(rator(concl th)) = `zs2:((A word_loc)heap_address)list`)) THEN
     MATCH_MP_TAC MONO_ALL2 THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
     MATCH_MP_TAC MP4AUX_v_inv_MutBlock_T THEN ASM_REWRITE_TAC[];
     DISCH_THEN(X_CHOOSE_THEN `z:(A word_loc)heap_address` STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `z:(A word_loc)heap_address` THEN ASM_REWRITE_TAC[] THEN
     FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP dest_thunk_insert_MutBlock th]) THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MP4AUX_v_inv_MutBlock_T THEN ASM_REWRITE_TAC[];
     DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN
       `zs2:((A word_loc)heap_address)list` STRIP_ASSUME_TAC)) THEN
     CONJ_TAC THENL
      [REWRITE_TAC[IN_IMAGE; FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM] THEN
       DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `~(a1:bool)`) o
         check (fun th -> is_imp (concl th) && lhand(concl th) = `~(a1:bool)`)) THEN
       REWRITE_TAC[IN_IMAGE] THEN
       MP4_ASM "INJ" (MP_TAC o check (fun th -> rand(rator(concl th)) = `FDOM (f:(num,num)fmap)`)) THEN
       REWRITE_TAC[INJ] THEN ASM_MESON_TAC[];
       EXISTS_TAC `zs2:((A word_loc)heap_address)list` THEN ASM_REWRITE_TAC[] THEN
       FIRST_X_ASSUM(MP_TAC o check (fun th -> mp4_is_app "ALL2" (concl th) &&
         rand(rator(concl th)) = `zs2:((A word_loc)heap_address)list`)) THEN
       MATCH_MP_TAC MONO_ALL2 THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
       MATCH_MP_TAC MP4AUX_v_inv_MutBlock_T THEN ASM_REWRITE_TAC[]]]]]);;

(* HOL4 line 9706 *)
let bc_stack_ref_inv_FinaliseCons_lemma = prove
 (`!c heap be v refs ts_opt v' refs' ts' ts vars frame
    (x:(A word_loc)heap_address) xs.
     data_finalise_cons v refs ts_opt = SOME (v',refs',ts') /\ ts_opt = SOME ts /\
     bc_stack_ref_inv c ts (CONS v vars) (union refs frame) (CONS x xs,heap,be) ==>
     IS_SOME ts' /\
     bc_stack_ref_inv c (THE ts') (CONS v' vars) (union refs' frame)
       (CONS x xs,heap,be)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC data_finalise_cons_ind THEN
  REWRITE_TAC[data_finalise_cons_def; option_INJ; PAIR_EQ] THEN
  CONJ_TAC THENL [ALL_TAC; REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF; THE_DEF]] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[option_case_eq; case_eq "bvl_ref"; COND_CASE_EQ; pair_case_eq; option_INJ;
              PAIR_EQ; option_DISTINCT] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF; THE_DEF] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o EQF_INTRO o check (fun th -> concl th = `~(a1:bool)`)) THEN
  SUBGOAL_THEN `lookup ptr (union refs frame) =
                SOME (MutBlock a0 F (a2:data_v list) a3 a4)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[lookup_union] THEN CASE_REWRITE_TAC[]; ALL_TAC] THEN
  MP4_X_ASM "bc_stack_ref_inv" (fun th -> MP_TAC(MATCH_MP bc_stack_ref_inv_MutBlock_centre
    (CONJ th (ASSUME `lookup ptr (union refs frame) =
                SOME (MutBlock a0 F (a2:data_v list) a3 a4)`)))) THEN
  ASM_REWRITE_TAC[ref_ptr_annot_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr_n:num` (X_CHOOSE_THEN `zs:((A word_loc)heap_address)list`
    STRIP_ASSUME_TAC)) THEN
  MP4_X_ASM "bc_stack_ref_inv" (fun th -> MP_TAC(MATCH_MP
    bc_stack_ref_inv_union_del_ins_lemma (CONJ th (ASSUME
      `lookup ptr refs = SOME (MutBlock a0 F (a2:data_v list) a3 a4)`)))) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a0:num`; `a2:data_v list`; `a4:data_v list`; `F`; `a3:data_v`] o
    check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`x':data_v`; `x'':(data_v bvl_ref)spt`; `y':num option`;
    `ts'':num`; `CONS (data_RefPtr b ptr) vars`;
    `insert ptr (MutBlock a0 F (a2:data_v list) a3 a4) frame`;
    `EL (LENGTH (a2:data_v list)) (zs:((A word_loc)heap_address)list)`;
    `CONS (x:(A word_loc)heap_address) xs`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP4_X_ASM "IS_SOME" (X_CHOOSE_THEN `ts2:num` SUBST_ALL_TAC o REWRITE_RULE[IS_SOME_EXISTS]) THEN
  REWRITE_TAC[OPTION_MAP_DEF; IS_SOME_DEF; THE_DEF; option_CASE] THEN
  SUBGOAL_THEN `lookup ptr (x'':(data_v bvl_ref)spt) = NONE` ASSUME_TAC THENL
   [MATCH_MP_TAC finalise_cons_none THEN
    MAP_EVERY EXISTS_TAC [`a3:data_v`; `delete ptr (refs:(data_v bvl_ref)spt)`;
                          `SOME (ts'':num)`; `x':data_v`; `SOME (ts2:num)`] THEN
    ASM_REWRITE_TAC[lookup_delete];
    ALL_TAC] THEN
  SUBGOAL_THEN `lookup ptr (union (x'':(data_v bvl_ref)spt)
                  (insert ptr (MutBlock a0 F (a2:data_v list) a3 a4) frame)) =
                SOME (MutBlock a0 F a2 a3 a4)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[lookup_union; lookup_insert; option_CASE]; ALL_TAC] THEN
  MP4_X_ASM "bc_stack_ref_inv" (fun th -> MP_TAC(MATCH_MP bc_stack_ref_inv_MutBlock_F
    (CONJ (REWRITE_RULE[ARITH_RULE `a + 1 + b = a + (b + 1)`] th)
      (CONJ (ASSUME `heap_lookup ptr_n (heap:((A word_loc,data_to_word_memoryProof_tag#
               (A word_loc)list)heap_element)list) = SOME (BlockRep a0 zs)`)
        (ASSUME `lookup ptr (union (x'':(data_v bvl_ref)spt)
                  (insert ptr (MutBlock a0 F (a2:data_v list) a3 a4) frame)) =
                SOME (MutBlock a0 F a2 a3 a4)`))))) THEN
  REWRITE_TAC[ARITH_RULE `a + 1 + b = a + (b + 1)`; THE_DEF] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] bc_stack_ref_inv_swap_refs)) THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[lookup_insert; lookup_union] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_CASE]);;

(* HOL4 line 9740 *)
let memory_rel_FinaliseCons = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm v w vars v' refs' ts'.
     memory_rel c be ts refs sp st m dm (CONS (v,w) vars) /\
     data_finalise_cons v refs (SOME ts) = SOME (v',refs',ts') ==>
     IS_SOME ts' /\
     memory_rel c be (THE ts') refs' sp st m dm (CONS (v',w) vars)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MP4AUX_memory_rel_unfold; MAP; FST; SND] THEN
  REWRITE_TAC[LIST_REL_CONS2] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[abs_ml_inv_def]) THEN
  MP4_X_ASM "/\\" STRIP_ASSUME_TAC THEN
  MP_TAC(REWRITE_RULE[union_LN] (ISPECL
    [`c:data_to_word_config`;
     `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
     `be:bool`; `v:data_v`; `refs:(data_v bvl_ref)spt`; `SOME (ts:num)`; `v':data_v`;
     `refs':(data_v bvl_ref)spt`; `ts':num option`; `ts:num`;
     `MAP FST (vars:(data_v#A word_loc)list)`; `LN:(data_v bvl_ref)spt`;
     `h':(A word_loc)heap_address`; `t':((A word_loc)heap_address)list`]
    bc_stack_ref_inv_FinaliseCons_lemma)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC
   [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
    `CONS (h':(A word_loc)heap_address) t'`] THEN
  ASM_REWRITE_TAC[abs_ml_inv_def] THEN
  MAP_EVERY EXISTS_TAC [`h':(A word_loc)heap_address`;
                        `t':((A word_loc)heap_address)list`] THEN
  ASM_REWRITE_TAC[]);;

let MP4AUX_BlockNil_and = prove
 (`!n. word_and (BlockNil n) (word_not (word 1)) = BlockNil n:A word`,
  GEN_TAC THEN REWRITE_TAC[BlockNil_def] THEN
  SUBGOAL_THEN `word 2:A word = word (2 EXP 1)` SUBST1_TAC THENL
   [REWRITE_TAC[EXP_1]; ALL_TAC] THEN
  SUBGOAL_THEN `word_add (word_shl (word n) 4) (word (2 EXP 1)) =
                word_or (word_shl (word n) 4) (word (2 EXP 1)):A word` SUBST1_TAC THENL
   [MATCH_MP_TAC WORD_ADD_OR; ALL_TAC] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND_ALT; BIT_WORD_OR_ALT; BIT_WORD_SHL;
              BIT_WORD_NOT; BIT_WORD_1; BIT_WORD_0; BIT_WORD_POW2] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i = 1` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ARITH_RULE `4 <= i ==> ~(i = 0)`) THEN CONV_TAC TAUT);;

(* HOL4 line 9759 *)
let memory_rel_Cons_empty = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) (dm:A word->bool) vars tag.
     memory_rel c be ts refs sp st m dm vars /\
     tag < dimword (:A) DIV 16 /\ good_dimindex (:A) ==>
     memory_rel c be ts refs sp st m dm
       (CONS (data_Block 0 tag [],wl_Word (BlockNil tag)) vars)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MP4AUX_memory_rel_unfold; MAP; FST; SND] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
    `CONS (gc_shared_Data (wl_Word (BlockNil tag:A word))) hs`] THEN
  ASM_SIMP_TAC[cons_thm_EMPTY; ALL2; word_addr_def; MP4AUX_BlockNil_and]);;

let MP4AUX_alloc_top = prove
 (`!heap heap2 a sp sp1 gens c st (m:A word -> A word_loc) dm limit
    (x:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element) hd ws.
     heap_in_memory_store heap a sp sp1 gens c st m dm limit /\
     heap_store_unused a (sp + sp1) x heap = (heap2,T) /\
     el_length x = LENGTH ws + 1 /\ el_length x <= sp /\
     (!(b:A word) R s. (misc_word_list b (CONS (wl_Word hd) ws) STAR R) s ==>
              (word_el b x c STAR R) s) ==>
     ?curr. FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       FLOOKUP st EndOfHeap =
         SOME (wl_Word (word_add curr (word_mul bytes_in_word (word (a + sp + sp1))))) /\
       FLOOKUP st TriggerGC =
         SOME (wl_Word (word_add curr (word_mul bytes_in_word (word (a + sp))))) /\
       ?m1. data_to_word_memoryProof_store_list
              (word_add curr (word_mul bytes_in_word (word ((a + sp + sp1) - el_length x))))
              (CONS (wl_Word hd) ws) m dm = SOME m1 /\
            heap_in_memory_store heap2 a (sp - el_length x) sp1 gens c
              (st |+ (EndOfHeap,wl_Word (word_add curr
                         (word_mul bytes_in_word (word ((a + sp + sp1) - el_length x)))))
                  |+ (TriggerGC,wl_Word (word_add curr
                         (word_mul bytes_in_word (word ((a + sp) - el_length x))))))
              m1 dm limit`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP4_X_EQ_ASM "heap_store_unused" (STRIP_ASSUME_TAC o
    MATCH_MP MP4AUX_heap_store_unused_SPLIT) THEN
  MP4_X_ASM "heap_in_memory_store" (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
  MP4_VAR_ASM "heap" SUBST_ALL_TAC THEN MP4_VAR_ASM "heap2" SUBST_ALL_TAC THEN
  MP4_VAR_ASM "a" SUBST_ALL_TAC THEN
  MP4_X_EQ_ASM "el_length" (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
  EXISTS_TAC `curr:A word` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `b0 = word_add (curr:A word) (word_mul bytes_in_word (word (heap_length
     (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))))` THEN
  SUBGOAL_THEN `word_list_exists (b0:A word) (sp + sp1):((A word#A word_loc)->bool)->bool =
     word_list_exists b0 ((sp + sp1) - (LENGTH (ws:(A word_loc)list) + 1)) STAR
     word_list_exists (word_add b0 (word_mul bytes_in_word
       (word ((sp + sp1) - (LENGTH ws + 1))))) (LENGTH ws + 1)`
     (LABEL_TAC "split") THENL
   [MP_TAC(ISPECL [`(sp + sp1) - (LENGTH (ws:(A word_loc)list) + 1)`;
                   `LENGTH (ws:(A word_loc)list) + 1`; `b0:A word`]
      (INST_TYPE [`:A word_loc`,`:B`] data_to_word_memoryProof_word_list_exists_ADD)) THEN
    SUBGOAL_THEN `((sp + sp1) - (LENGTH (ws:(A word_loc)list) + 1)) + (LENGTH ws + 1) =
                  sp + sp1` (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  MP4_X_ASM "STAR" (MP_TAC o REWRITE_RULE[word_heap_APPEND; word_heap_def; word_el_def;
    el_length_def]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((sp + sp1) - 1) + 1 = sp + sp1` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "split" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
  ABBREV_TAC `b1 = word_add (b0:A word) (word_mul bytes_in_word
     (word ((sp + sp1) - (LENGTH (ws:(A word_loc)list) + 1))))` THEN
  SUBGOAL_THEN `word_add curr (word_mul bytes_in_word (word ((heap_length
       (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) +
       sp + sp1) - (LENGTH (ws:(A word_loc)list) + 1)))) = b1:A word` SUBST1_TAC THENL
   [EXPAND_TAC "b1" THEN EXPAND_TAC "b0" THEN REWRITE_TAC[MP4AUX_addr_add] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP4_X_ASM "STAR" (fun th ->
    let thf = MP4AUX_STAR_FOCUS (fun l -> mp4_is_app "word_list_exists" l &&
                rand l = `LENGTH (ws:(A word_loc)list) + 1`) th in
    let p,s = dest_comb (concl thf) in
    let frame = rand p in
    let sl = REWRITE_RULE[LENGTH; ADD1] (ISPECL [`CONS (wl_Word (hd:A word)) ws`;
               `b1:A word`; frame; `m:A word -> A word_loc`; `dm:A word -> bool`]
               store_list_thm) in
    MP_TAC (MATCH_MP sl thf)) THEN
  DISCH_THEN(X_CHOOSE_THEN `m1:A word -> A word_loc` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `m1:A word -> A word_loc` THEN ASM_REWRITE_TAC[] THEN
  MP4_X_ASM "STAR" (fun th -> FIRST_X_ASSUM(fun imp ->
    if is_forall (concl imp) then ASSUME_TAC (MATCH_MP imp th) else failwith "")) THEN
  SUBGOAL_THEN `heap_length (APPEND (APPEND ha (APPEND (heap_expand ((sp + sp1) -
       (LENGTH (ws:(A word_loc)list) + 1))) [x])) hb) =
     heap_length (APPEND ha (CONS (Unused ((sp + sp1) - 1))
       (hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))`
     ASSUME_TAC THENL
   [REWRITE_TAC[heap_length_APPEND; heap_length_CONS;
                gc_shared_heap_length_heap_expand; MP4AUX_heap_length_SING;
                el_length_def] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[heap_in_memory_store_def] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FLOOKUP_UPDATE; FDOM_FUPDATE; IN_INSERT; distinctness "store_name"] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`curr:A word`; `other:A word`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (ws:(A word_loc)list) + 1 <= sp` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= s ==> (h + s) - k = h + (s - k):num`] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "b1" THEN EXPAND_TAC "b0" THEN
    REWRITE_TAC[MP4AUX_addr_add; option_INJ; injectivity "word_loc"] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[word_heap_APPEND] THEN
  SUBGOAL_THEN `word_add curr (word_mul bytes_in_word (word (heap_length (APPEND ha
       (APPEND (heap_expand ((sp + sp1) - (LENGTH (ws:(A word_loc)list) + 1)))
       [x:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element]))))) =
     word_add b0 (word_mul bytes_in_word (word (sp + sp1))):A word` SUBST1_TAC THENL
   [EXPAND_TAC "b0" THEN REWRITE_TAC[MP4AUX_addr_add] THEN
    REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand;
                MP4AUX_heap_length_SING] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[word_heap_APPEND; word_heap_def; word_heap_heap_expand; SEP_CLAUSES;
              gc_shared_heap_length_heap_expand] THEN
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[word_heap_heap_expand]) THEN
  MP4AUX_SEP_AC_TAC);;

let MP4AUX_addr_sub = prove
 (`!(c:A word) b n k. k <= n ==>
     word_sub (word_add c (word_mul b (word n))) (word_mul b (word k)) =
     word_add c (word_mul b (word (n - k)))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE);;

let MP4AUX_memory_rel_alloc_top = prove
 (`!c be ts2 refs2 sp st (m:A word -> A word_loc) dm vars heap heap2 limit a sp0 sp1
    gens roots2 x hd ws v annot.
     heap_in_memory_store heap a sp0 sp1 gens c st m dm limit /\
     (limit + 3) * (dimindex (:A) DIV 8) + 1 < dimword (:A) /\
     heap_store_unused a (sp0 + sp1) x heap = (heap2,T) /\
     el_length x = LENGTH ws + 1 /\ el_length x <= sp0 /\ sp <= sp0 /\
     (!(b:A word) R s. (misc_word_list b (CONS (wl_Word hd) ws) STAR R) s ==>
                       (word_el b x c STAR R) s) /\
     abs_ml_inv c (CONS v (MAP FST vars)) refs2
       (CONS (Pointer ((a + sp0 + sp1) - el_length x) annot) roots2,heap2,be,a,
        sp0 - el_length x,sp1,gens) limit ts2 /\
     ALL2 (\v w. word_addr c v = w) roots2 (MAP SND (vars:(data_v#A word_loc)list)) ==>
     ?curr m1.
       FLOOKUP st EndOfHeap =
         SOME (wl_Word (word_add curr (word_mul bytes_in_word (word (a + sp0 + sp1))))) /\
       FLOOKUP st TriggerGC =
         SOME (wl_Word (word_add curr (word_mul bytes_in_word (word (a + sp0))))) /\
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       data_to_word_memoryProof_store_list
         (word_add curr (word_mul bytes_in_word (word ((a + sp0 + sp1) - (LENGTH ws + 1)))))
         (CONS (wl_Word hd) ws) m dm = SOME m1 /\
       memory_rel c be ts2 refs2 (sp - (LENGTH ws + 1))
         (st |+ (EndOfHeap,wl_Word (word_add curr
                   (word_mul bytes_in_word (word ((a + sp0 + sp1) - (LENGTH ws + 1))))))
             |+ (TriggerGC,wl_Word (word_add curr
                   (word_mul bytes_in_word (word ((a + sp0) - (LENGTH ws + 1)))))))
         m1 dm
         (CONS (v,wl_Word (get_addr c ((a + sp0 + sp1) - (LENGTH ws + 1)) annot)) vars)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`; `c:data_to_word_config`;
                 `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                 `dm:A word -> bool`; `limit:num`;
                 `x:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element`;
                 `hd:A word`; `ws:(A word_loc)list`] MP4AUX_alloc_top) THEN
  ASM_REWRITE_TAC[] THEN
  MP4_X_EQ_ASM "el_length" (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
  DISCH_THEN(X_CHOOSE_THEN `curr:A word` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `m1:A word -> A word_loc` STRIP_ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`curr:A word`; `m1:A word -> A word_loc`] THEN
  ASM_REWRITE_TAC[MP4AUX_memory_rel_unfold] THEN
  MAP_EVERY EXISTS_TAC
   [`heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp0 - (LENGTH (ws:(A word_loc)list) + 1)`;
    `sp1:num`; `gens:gen_state`;
    `CONS (Pointer ((a + sp0 + sp1) - (LENGTH (ws:(A word_loc)list) + 1)) annot)
       (roots2:((A word_loc)heap_address)list)`] THEN
  ASM_REWRITE_TAC[MAP; FST; SND; ALL2; word_addr_def] THEN
  MATCH_MP_TAC(ARITH_RULE `sp <= sp0 ==> sp - k <= sp0 - k:num`) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 9776 *)
let memory_rel_Ref = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vals ws vars hd new.
     memory_rel c be ts refs sp st m dm (APPEND (ZIP vals ws) vars) /\
     LENGTH vals = LENGTH (ws:(A word_loc)list) /\
     encode_header c 2 (LENGTH ws) = SOME hd /\ ~(new IN domain refs) /\
     LENGTH ws < sp /\ good_dimindex (:A) ==>
     ?eoh (curr:A word) trig m1.
       FLOOKUP st EndOfHeap = SOME (wl_Word eoh) /\
       FLOOKUP st TriggerGC = SOME (wl_Word trig) /\
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       let w = word_sub eoh (word_mul bytes_in_word (word (LENGTH ws + 1))) in
       let w1 = word_sub trig (word_mul bytes_in_word (word (LENGTH ws + 1))) in
       data_to_word_memoryProof_store_list w (CONS (wl_Word hd) ws) m dm =
         SOME m1 /\
       memory_rel c be ts (insert new (bvl_ValueArray vals) refs)
         (sp - (LENGTH ws + 1))
         (st |+ (EndOfHeap,wl_Word w) |+ (TriggerGC,wl_Word w1)) m1 dm
         (CONS (data_RefPtr T new,make_ptr c (word_sub w curr) (word 0:A word)
                                     (LENGTH ws)) vars)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  MP4_X_ASM "memory_rel" (STRIP_ASSUME_TAC o
    REWRITE_RULE[MP4AUX_memory_rel_unfold; MAP_APPEND]) THEN
  SUBGOAL_THEN `MAP FST (ZIP (vals:data_v list) (ws:(A word_loc)list)) = vals /\
                MAP SND (ZIP vals ws) = ws` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_SIMP_TAC[MAP_ZIP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `vals:data_v list`;
                 `MAP FST (vars:(data_v#A word_loc)list)`; `refs:(data_v bvl_ref)spt`;
                 `hs:((A word_loc)heap_address)list`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `be:bool`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`; `limit:num`;
                 `ts:num`; `new:num`] new_ref_thm) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rs:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `roots2:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                          heap_element)list` STRIP_ASSUME_TAC))) THEN
  RVEQ_TAC THEN
  MP4_X_ASM "ALL2" (MP_TAC o check (fun th -> mp4_is_app "APPEND" (rand(concl th)))) THEN
  ASM_SIMP_TAC[LIST_REL_APPEND_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o REWRITE_RULE[EVERY2_f_EQ; ETA_AX]) ASSUME_TAC) THEN
  SUBGOAL_THEN `LENGTH (vals:data_v list) = LENGTH (rs:((A word_loc)heap_address)list)`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP4_X_ASM "abs_ml_inv" (fun th ->
    if can (find_term (fun t -> t = `heap2:((A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`)) (concl th)
    then ASSUME_TAC (MATCH_MP pop_thm (CONJ th (ASSUME `LENGTH (vals:data_v list) =
           LENGTH (rs:((A word_loc)heap_address)list)`)))
    else failwith "pop") THEN
  SUBGOAL_THEN `make_header c (word 2) (LENGTH (ws:(A word_loc)list)) = (hd:A word) /\
                LENGTH ws < 2 EXP (dimindex (:A) - 4) /\ decode_length c hd = word (LENGTH ws)`
     STRIP_ASSUME_TAC THENL
   [MP4_ASM "heap_in_memory_store"
      (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
    MP_TAC(ISPECL [`c:data_to_word_config`; `2`; `LENGTH (ws:(A word_loc)list)`;
      `hd:A word`] encode_header_IMP) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]] THEN
    MP4_EQ_ASM "encode_header" (MP_TAC o REWRITE_RULE[encode_header_def]) THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
                 `insert new (bvl_ValueArray vals) (refs:(data_v bvl_ref)spt)`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                 `dm:A word -> bool`; `vars:(data_v#A word_loc)list`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `limit:num`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
                 `roots2:((A word_loc)heap_address)list`;
                 `RefBlock (rs:((A word_loc)heap_address)list):(A word_loc,
                     data_to_word_memoryProof_tag#(A word_loc)list)heap_element`;
                 `hd:A word`; `ws:(A word_loc)list`; `data_RefPtr T new`;
                 `wl_Word (word 0):A word_loc`]
                MP4AUX_memory_rel_alloc_top) THEN
  ASM_REWRITE_TAC[RefBlock_def; el_length_def] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP[word_el_def; word_payload_def; SEP_CLAUSES; LENGTH_MAP] THEN
    ASM_REWRITE_TAC[SEP_CLAUSES];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `curr:A word` (X_CHOOSE_THEN `m1:A word -> A word_loc`
     STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`word_add (curr:A word) (word_mul bytes_in_word (word (a + sp0 + sp1)))`;
    `curr:A word`; `word_add (curr:A word) (word_mul bytes_in_word (word (a + sp0)))`;
    `m1:A word -> A word_loc`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (ws:(A word_loc)list) + 1 <= a + sp0 + sp1 /\
                LENGTH ws + 1 <= a + sp0` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MP4AUX_addr_sub] THEN
  MP4_ASM "heap_in_memory_store" (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def] o
    check (fun th -> can (find_term (fun t -> t = `heap:((A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`)) (concl th))) THEN
  ASM_SIMP_TAC[MP4AUX_make_ptr_get_addr]);;

let MP4AUX_thunk_header = prove
 (CASE_TERM `!c ev (hd:A word).
     encode_header c (match ev with Evaluated -> 14 | NotEvaluated -> 6) 1 = SOME hd /\
     data_to_word_config_len_size c + 5 < dimindex (:A) /\ good_dimindex (:A) ==>
     make_header c (word_or (word_shl (thunk_tag_to_bits ev) 3) (word 6)) 1 = hd /\
     decode_length c hd = word 1`,
  GEN_TAC THEN MATCH_MP_TAC thunk_mode_INDUCT THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[thunk_tag_bits_lemma] THEN
  REWRITE_TAC[thunk_tag_to_bits_def; WORD_SHL_0; WORD_OR_0] THEN
  CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP4_EQ_ASM "encode_header" (MP_TAC o REWRITE_RULE[encode_header_def]) THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ];
    MP4_EQ_ASM "encode_header" (fun th -> MP_TAC(MATCH_MP encode_header_IMP
      (CONJ th (CONJ (ASSUME `data_to_word_config_len_size c + 5 < dimindex (:A)`)
                     (ASSUME `good_dimindex (:A)`))))) THEN SIMP_TAC[];
    MP4_EQ_ASM "encode_header" (MP_TAC o REWRITE_RULE[encode_header_def]) THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ];
    MP4_EQ_ASM "encode_header" (fun th -> MP_TAC(MATCH_MP encode_header_IMP
      (CONJ th (CONJ (ASSUME `data_to_word_config_len_size c + 5 < dimindex (:A)`)
                     (ASSUME `good_dimindex (:A)`))))) THEN SIMP_TAC[]]);;

(* HOL4 line 9843 *)
let memory_rel_AllocThunk = prove
 (CASE_TERM
  `!c be ts refs sp st (m:A word -> A word_loc) dm v w vars ev hd new.
     memory_rel c be ts refs sp st m dm (CONS (v,w) vars) /\
     encode_header c (match ev with Evaluated -> 14 | NotEvaluated -> 6) 1 =
       SOME hd /\
     ~(new IN domain refs) /\
     (ev = Evaluated ==> data_dest_thunk v refs = data_NotThunk) /\
     2 <= sp /\ good_dimindex (:A) ==>
     ?eoh (curr:A word) trig m1.
       FLOOKUP st EndOfHeap = SOME (wl_Word eoh) /\
       FLOOKUP st TriggerGC = SOME (wl_Word trig) /\
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       let w' = word_sub eoh (word_mul bytes_in_word (word 2)) in
       let w1 = word_sub trig (word_mul bytes_in_word (word 2)) in
       data_to_word_memoryProof_store_list w' [wl_Word hd; w] m dm = SOME m1 /\
       memory_rel c be ts (insert new (bvl_Thunk ev v) refs) (sp - 2)
         (st |+ (EndOfHeap,wl_Word w') |+ (TriggerGC,wl_Word w1)) m1 dm
         (CONS (data_RefPtr F new,make_ptr c (word_sub w' curr) (word 0:A word) 1)
               vars)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  MP4_X_ASM "memory_rel" (STRIP_ASSUME_TAC o
    REWRITE_RULE[MP4AUX_memory_rel_unfold; MAP; FST; SND]) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `v:data_v`;
                 `MAP FST (vars:(data_v#A word_loc)list)`; `refs:(data_v bvl_ref)spt`;
                 `hs:((A word_loc)heap_address)list`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `be:bool`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`; `limit:num`;
                 `ts:num`; `new:num`; `ev:thunk_mode`] new_thunk_thm) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A word_loc)heap_address`
    (X_CHOOSE_THEN `roots2:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                          heap_element)list` STRIP_ASSUME_TAC))) THEN
  RVEQ_TAC THEN
  MP4_X_ASM "ALL2" (STRIP_ASSUME_TAC o REWRITE_RULE[ALL2]) THEN
  MP4_X_ASM "abs_ml_inv" (fun th ->
    if can (find_term (fun t -> t = `heap2:((A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`)) (concl th)
    then ASSUME_TAC (MATCH_MP (REWRITE_RULE[APPEND; LENGTH] (ISPECL
      [`c:data_to_word_config`; `[v:data_v]`;
       `CONS (data_RefPtr F new) (MAP FST (vars:(data_v#A word_loc)list))`;
       `insert new (bvl_Thunk ev v) (refs:(data_v bvl_ref)spt)`;
       `[r:(A word_loc)heap_address]`;
       `CONS (Pointer ((a + sp0 + sp1) - 2) (wl_Word (word 0)))
          (roots2:((A word_loc)heap_address)list)`;
       `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
       `be:bool`; `a:num`; `sp0 - 2`; `sp1:num`; `gens:gen_state`; `limit:num`; `ts:num`]
      pop_thm)) th)
    else failwith "pop") THEN
  SUBGOAL_THEN `make_header c (word_or (word_shl (thunk_tag_to_bits ev) 3) (word 6)) 1 =
                (hd:A word) /\ decode_length c hd = word 1` STRIP_ASSUME_TAC THENL
   [MP4_ASM "heap_in_memory_store"
      (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
    MATCH_MP_TAC MP4AUX_thunk_header THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ThunkBlock_def]) THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ThunkBlock_def; el_length_def; LENGTH]
         (ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
                 `insert new (bvl_Thunk ev v) (refs:(data_v bvl_ref)spt)`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                 `dm:A word -> bool`; `vars:(data_v#A word_loc)list`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `limit:num`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
                 `roots2:((A word_loc)heap_address)list`;
                 `ThunkBlock ev (r:(A word_loc)heap_address):(A word_loc,
                     data_to_word_memoryProof_tag#(A word_loc)list)heap_element`;
                 `hd:A word`; `[w:A word_loc]`; `data_RefPtr F new`;
                 `wl_Word (word 0):A word_loc`]
                MP4AUX_memory_rel_alloc_top))) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP[word_el_def; word_payload_def; SEP_CLAUSES; LENGTH_MAP; MAP; LENGTH] THEN
    ASM_REWRITE_TAC[SEP_CLAUSES] THEN
    SUBGOAL_THEN `0 < dimindex (:A) - 4` (fun th -> REWRITE_TAC[th; SEP_CLAUSES]) THEN
    UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `curr:A word` (X_CHOOSE_THEN `m1:A word -> A word_loc`
     STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`word_add (curr:A word) (word_mul bytes_in_word (word (a + sp0 + sp1)))`;
    `curr:A word`; `word_add (curr:A word) (word_mul bytes_in_word (word (a + sp0)))`;
    `m1:A word -> A word_loc`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `2 <= a + sp0 + sp1 /\ 2 <= a + sp0` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MP4AUX_addr_sub] THEN
  MP4_ASM "heap_in_memory_store" (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def] o
    check (fun th -> can (find_term (fun t -> t = `heap:((A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`)) (concl th))) THEN
  ASM_SIMP_TAC[MP4AUX_make_ptr_get_addr]);;

(* writing a word of an unused region *)
let MP4AUX_word_list_exists_write = prove
 (`!(a:A word) k n R m dm.
     (word_list_exists a k STAR R) (fun2set (m,dm)) /\ n < k ==>
     word_add a (word_mul bytes_in_word (word n)) IN dm /\
     !w:A word_loc. (word_list_exists a k STAR R)
       (fun2set ((word_add a (word_mul bytes_in_word (word n)) =+ w) m,dm))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[WORD_MUL_SYM] THEN
  REWRITE_TAC[word_list_exists_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `xs:(A word_loc)list`) ASSUME_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[cond_STAR] o
    MP4AUX_STAR_FOCUS (mp4_is_app "cond")) THEN
  SUBGOAL_THEN `n < LENGTH (xs:(A word_loc)list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if mp4_is_fun2set_asm (concl th) then
      MP_TAC(MATCH_MP MP4AUX_word_list_field (CONJ
        (MP4AUX_STAR_FOCUS (mp4_is_app "misc_word_list") th)
        (ASSUME `n < LENGTH (xs:(A word_loc)list)`)))
    else failwith "") THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:A word_loc` THEN
  EXISTS_TAC `LUPDATE (w:A word_loc) n xs` THEN
  ASM_REWRITE_TAC[LENGTH_LUPDATE; SEP_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:A word_loc`) THEN
  MP4AUX_SEP_AC_TAC);;

(* HOL4 line 9918 *)
let memory_rel_write = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars w.
     memory_rel c be ts refs sp st m dm vars ==>
     ?free:A word.
       FLOOKUP st NextFree = SOME (wl_Word free) /\
       !n. n < sp ==>
           let a = word_add free (word_mul bytes_in_word (word n)) in
           a IN dm /\ memory_rel c be ts refs sp st ((a =+ w) m) dm vars`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MP4AUX_memory_rel_unfold; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN
  MP4_ASM "heap_in_memory_store" (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
  EXISTS_TAC `word_add (curr:A word) (word_mul bytes_in_word (word a))` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `n < sp0 + sp1` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add curr (word_mul bytes_in_word (word a)))
      (word_mul bytes_in_word (word n)) IN dm /\
    (word_heap curr heap c STAR word_heap (other:A word) (heap_expand limit) c)
      (fun2set ((word_add (word_add curr (word_mul bytes_in_word (word a)))
                   (word_mul bytes_in_word (word n)) =+ w) m,dm))`
    STRIP_ASSUME_TAC THENL
   [MP4_ASM "abs_ml_inv" (MP_TAC o REWRITE_RULE[abs_ml_inv_def]) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o REWRITE_RULE[unused_space_inv_def] o
      CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN
      `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
      (X_CHOOSE_THEN
        `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
        STRIP_ASSUME_TAC) o MATCH_MP heap_lookup_SPLIT) THEN
    MP4_X_ASM "STAR" (MP_TAC o REWRITE_RULE[word_heap_APPEND; word_heap_def; word_el_def;
      el_length_def] o check (fun th -> mp4_is_fun2set_asm (concl th))) THEN
    ASM_REWRITE_TAC[word_heap_APPEND; word_heap_def; word_el_def; el_length_def] THEN
    SUBGOAL_THEN `((sp0 + sp1) - 1) + 1 = sp0 + sp1` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th ->
      let thf = MP4AUX_STAR_FOCUS (mp4_is_app "word_list_exists") th in
      MP_TAC(MATCH_MP MP4AUX_word_list_exists_write
        (CONJ thf (ASSUME `n < sp0 + sp1`)))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `w:A word_loc`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP4AUX_SEP_AC_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC
   [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
    `hs:((A word_loc)heap_address)list`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MP4AUX_heap_in_memory_store_change THEN
  MAP_EVERY EXISTS_TAC
   [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `m:A word -> A word_loc`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
    (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 9956 *)
let word_list_AND_word_list_exists_IMP = prove
 (`!(m:A word -> A word_loc) dm ws aa frame n.
     (misc_word_list aa ws STAR SEP_T) (fun2set (m,dm)) /\
     (word_list_exists aa n STAR frame) (fun2set (m,dm)) /\
     LENGTH ws <= n ==>
     (misc_word_list aa ws STAR
      word_list_exists (word_add aa (word_mul bytes_in_word (word (LENGTH ws))))
        (n - LENGTH ws) STAR
      frame) (fun2set (m,dm))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[WORD_MUL_SYM] THEN
  REWRITE_TAC[word_list_exists_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `xs:(A word_loc)list`) ASSUME_TAC)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[cond_STAR] o
    MP4AUX_STAR_FOCUS (mp4_is_app "cond") o
    check (fun th -> can (find_term ((=) `xs:(A word_loc)list`)) (concl th))) THEN
  SUBGOAL_THEN `TAKE (LENGTH (ws:(A word_loc)list)) (xs:(A word_loc)list) = ws`
    ASSUME_TAC THENL
   [REWRITE_TAC[LIST_EQ] THEN ASM_SIMP_TAC[LENGTH_TAKE] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_TAKE] THEN
    SUBGOAL_THEN `i < LENGTH (xs:(A word_loc)list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th ->
      if mp4_is_fun2set_asm (concl th) &&
         can (find_term ((=) `xs:(A word_loc)list`)) (concl th) then
        MP_TAC(CONJUNCT1(MATCH_MP MP4AUX_word_list_field (CONJ
          (MP4AUX_STAR_FOCUS (mp4_is_app "misc_word_list") th)
          (ASSUME `i < LENGTH (xs:(A word_loc)list)`))))
      else failwith "") THEN
    FIRST_ASSUM(fun th ->
      if mp4_is_fun2set_asm (concl th) &&
         can (find_term ((=) `ws:(A word_loc)list`)) (concl th) then
        MP_TAC(CONJUNCT1(MATCH_MP MP4AUX_word_list_field (CONJ
          (MP4AUX_STAR_FOCUS (mp4_is_app "misc_word_list") th)
          (ASSUME `i < LENGTH (ws:(A word_loc)list)`))))
      else failwith "") THEN
    MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `DROP (LENGTH (ws:(A word_loc)list)) (xs:(A word_loc)list)` THEN
  ASM_REWRITE_TAC[LENGTH_DROP; SEP_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> mp4_is_fun2set_asm (concl th) &&
         can (find_term ((=) `xs:(A word_loc)list`)) (concl th))) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM(ISPECL
    [`LENGTH (ws:(A word_loc)list)`; `xs:(A word_loc)list`] TAKE_DROP)] THEN
  ASM_REWRITE_TAC[data_to_word_memoryProof_word_list_APPEND] THEN
  DISCH_TAC THEN MP4AUX_SEP_AC_TAC);;

let MP4AUX_alloc_bottom_inplace = prove
 (`!heap heap2 a sp sp1 gens c st (m:A word -> A word_loc) dm limit
    (x:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element) hd ws.
     heap_in_memory_store heap a sp sp1 gens c st m dm limit /\
     heap_store_unused_alt a (sp + sp1) x heap = (heap2,T) /\
     el_length x = LENGTH ws + 1 /\ el_length x <= sp /\
     (!(b:A word) R s. (misc_word_list b (CONS (wl_Word hd) ws) STAR R) s ==>
              (word_el b x c STAR R) s) ==>
     ?curr. FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       FLOOKUP st NextFree =
         SOME (wl_Word (word_add curr (word_mul bytes_in_word (word a)))) /\
       ((misc_word_list (word_add curr (word_mul bytes_in_word (word a)))
           (CONS (wl_Word hd) ws) STAR SEP_T) (fun2set (m,dm)) ==>
        heap_in_memory_store heap2 (a + el_length x) (sp - el_length x) sp1 gens c
          (st |+ (NextFree,wl_Word (word_add curr
                     (word_mul bytes_in_word (word (a + el_length x)))))) m dm limit)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP4_X_EQ_ASM "heap_store_unused_alt" (STRIP_ASSUME_TAC o
    MATCH_MP MP4AUX_heap_store_unused_alt_SPLIT) THEN
  MP4_X_ASM "heap_in_memory_store" (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
  MP4_VAR_ASM "heap" SUBST_ALL_TAC THEN MP4_VAR_ASM "heap2" SUBST_ALL_TAC THEN
  MP4_VAR_ASM "a" SUBST_ALL_TAC THEN
  EXISTS_TAC `curr:A word` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `b0 = word_add (curr:A word) (word_mul bytes_in_word (word (heap_length
     (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))))` THEN
  MP4_X_ASM "STAR" (MP_TAC o REWRITE_RULE[word_heap_APPEND; word_heap_def; word_el_def;
    el_length_def] o check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "word_heap"
      with Failure _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((sp + sp1) - 1) + 1 = sp + sp1` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (CONS (wl_Word (hd:A word)) ws) <= sp + sp1` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th ->
    let thf = MP4AUX_STAR_FOCUS (mp4_is_app "word_list_exists") th in
    MP_TAC(MATCH_MP word_list_AND_word_list_exists_IMP (CONJ
      (ASSUME `(misc_word_list (b0:A word) (CONS (wl_Word (hd:A word)) ws) STAR SEP_T)
                 (fun2set (m,dm))`)
      (CONJ thf (ASSUME `LENGTH (CONS (wl_Word (hd:A word)) ws) <= sp + sp1`))))) THEN
  REWRITE_TAC[LENGTH; ADD1] THEN DISCH_TAC THEN
  MP4_X_ASM "STAR" ((fun th -> FIRST_X_ASSUM(fun imp ->
    if is_forall (concl imp) then ASSUME_TAC (MATCH_MP imp
      (MP4AUX_STAR_FOCUS (mp4_is_app "misc_word_list") th)) else failwith "")) o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "word_heap"
      with Failure _ -> false)) (concl th))) THEN
  SUBGOAL_THEN `heap_length (APPEND (APPEND ha (CONS (x:(A word_loc,
       data_to_word_memoryProof_tag#(A word_loc)list)heap_element)
       (heap_expand ((sp + sp1) - (LENGTH (ws:(A word_loc)list) + 1))))) hb) =
     heap_length (APPEND ha (CONS (Unused ((sp + sp1) - 1)) hb))` ASSUME_TAC THENL
   [REWRITE_TAC[heap_length_APPEND; heap_length_CONS;
                gc_shared_heap_length_heap_expand; el_length_def] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[heap_in_memory_store_def] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FLOOKUP_UPDATE; FDOM_FUPDATE; IN_INSERT; distinctness "store_name"] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`curr:A word`; `other:A word`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (ws:(A word_loc)list) + 1 <= sp` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= s ==> (a + k) + (s - k) = a + s:num`;
               ARITH_RULE `k <= s ==> (a + k) + ((s - k) + t) = a + s + t:num`] THEN
  REWRITE_TAC[word_heap_APPEND; word_heap_def; word_heap_heap_expand] THEN
  SUBGOAL_THEN `word_add (curr:A word) (word_mul bytes_in_word (word (heap_length (APPEND ha
       (CONS (x:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)
       (heap_expand ((sp + sp1) - (LENGTH (ws:(A word_loc)list) + 1)))))))) =
     word_add b0 (word_mul bytes_in_word (word (sp + sp1)))` SUBST1_TAC THENL
   [EXPAND_TAC "b0" THEN REWRITE_TAC[MP4AUX_addr_add] THEN
    REWRITE_TAC[heap_length_APPEND; heap_length_CONS;
                gc_shared_heap_length_heap_expand] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[word_heap_heap_expand]) THEN
  MP4AUX_SEP_AC_TAC);;

let MP4AUX_memory_rel_alloc_bottom_inplace = prove
 (`!c be ts2 refs2 sp st (m:A word -> A word_loc) dm vars heap heap2 limit a sp0 sp1
    gens roots2 x hd ws v annot.
     heap_in_memory_store heap a sp0 sp1 gens c st m dm limit /\
     (limit + 3) * (dimindex (:A) DIV 8) + 1 < dimword (:A) /\
     heap_store_unused_alt a (sp0 + sp1) x heap = (heap2,T) /\
     el_length x = LENGTH ws + 1 /\ el_length x <= sp0 /\ sp <= sp0 /\
     (!(b:A word) R s. (misc_word_list b (CONS (wl_Word hd) ws) STAR R) s ==>
                       (word_el b x c STAR R) s) /\
     abs_ml_inv c (CONS v (MAP FST vars)) refs2
       (CONS (Pointer a annot) roots2,heap2,be,a + el_length x,sp0 - el_length x,
        sp1,gens) limit ts2 /\
     ALL2 (\v w. word_addr c v = w) roots2 (MAP SND (vars:(data_v#A word_loc)list)) ==>
     ?curr.
       FLOOKUP st NextFree =
         SOME (wl_Word (word_add curr (word_mul bytes_in_word (word a)))) /\
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       ((misc_word_list (word_add curr (word_mul bytes_in_word (word a)))
           (CONS (wl_Word hd) ws) STAR SEP_T) (fun2set (m,dm)) ==>
        memory_rel c be ts2 refs2 (sp - (LENGTH ws + 1))
          (st |+ (NextFree,wl_Word (word_add curr
                    (word_mul bytes_in_word (word (a + LENGTH ws + 1)))))) m dm
          (CONS (v,wl_Word (get_addr c a annot)) vars))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP4_X_EQ_ASM "el_length" (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
  MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`; `c:data_to_word_config`;
                 `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                 `dm:A word -> bool`; `limit:num`;
                 `x:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element`;
                 `hd:A word`; `ws:(A word_loc)list`] MP4AUX_alloc_bottom_inplace) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `curr:A word` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  EXISTS_TAC `curr:A word` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(fun imp -> ASSUME_TAC(MP imp th))) THEN
  REWRITE_TAC[MP4AUX_memory_rel_unfold] THEN
  MAP_EVERY EXISTS_TAC
   [`heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `a + LENGTH (ws:(A word_loc)list) + 1`;
    `sp0 - (LENGTH (ws:(A word_loc)list) + 1)`;
    `sp1:num`; `gens:gen_state`;
    `CONS (Pointer a annot) (roots2:((A word_loc)heap_address)list)`] THEN
  ASM_REWRITE_TAC[MAP; FST; SND; ALL2; word_addr_def] THEN
  MATCH_MP_TAC(ARITH_RULE `sp <= sp0 ==> sp - k <= sp0 - k:num`) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 9989 (the unused bound variable m1 of HOL4 is left out) *)
let memory_rel_Cons_alt = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vals ws vars tag hd.
     memory_rel c be ts refs sp st m dm (APPEND (ZIP vals ws) vars) /\
     LENGTH vals = LENGTH (ws:(A word_loc)list) /\ ~(vals = []) /\
     encode_header c (4 * tag) (LENGTH ws) = SOME hd /\
     LENGTH ws < sp /\ good_dimindex (:A) ==>
     ?free (curr:A word).
       FLOOKUP st NextFree = SOME (wl_Word free) /\
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       ((misc_word_list free (CONS (wl_Word hd) ws) STAR SEP_T) (fun2set (m,dm)) ==>
        memory_rel c be (ts + 1) refs (sp - (LENGTH ws + 1))
          (st |+ (NextFree,
                  wl_Word (word_add free
                             (word_mul bytes_in_word (word (LENGTH ws + 1)))))) m dm
          (CONS (data_Block ts tag vals,
                 make_cons_ptr c (word_sub free curr) tag (LENGTH ws)) vars))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
   MP4_X_ASM "memory_rel" (STRIP_ASSUME_TAC o
     REWRITE_RULE[MP4AUX_memory_rel_unfold; MAP_APPEND]) THEN
   SUBGOAL_THEN `MAP FST (ZIP (vals:data_v list) (ws:(A word_loc)list)) = vals /\
                 MAP SND (ZIP vals ws) = ws` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [ASM_SIMP_TAC[MAP_ZIP]; ALL_TAC] THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `vals:data_v list`;
                  `MAP FST (vars:(data_v#A word_loc)list)`; `refs:(data_v bvl_ref)spt`;
                  `hs:((A word_loc)heap_address)list`;
                  `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list`;
                  `be:bool`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`; `limit:num`;
                  `ts:num`; `tag:num`] cons_thm_alt) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `rs:((A word_loc)heap_address)list`
     (X_CHOOSE_THEN `roots:((A word_loc)heap_address)list`
     (X_CHOOSE_THEN `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                           heap_element)list` STRIP_ASSUME_TAC))) THEN
   RVEQ_TAC THEN
   MP4_X_ASM "ALL2" (MP_TAC o check (fun th -> mp4_is_app "APPEND" (rand(concl th)))) THEN
   ASM_SIMP_TAC[LIST_REL_APPEND_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o REWRITE_RULE[EVERY2_f_EQ; ETA_AX]) ASSUME_TAC) THEN
  SUBGOAL_THEN `make_header c (word_shl (word tag) 2) (LENGTH (ws:(A word_loc)list)) = (hd:A word) /\
                 LENGTH ws < 2 EXP (dimindex (:A) - 4) /\ decode_length c hd = word (LENGTH ws)`
     STRIP_ASSUME_TAC THENL
    [MP4_ASM "heap_in_memory_store"
       (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
     MP_TAC(ISPECL [`c:data_to_word_config`; `4 * tag`; `LENGTH (ws:(A word_loc)list)`;
       `hd:A word`] encode_header_IMP) THEN
     ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]] THEN
     MP4_EQ_ASM "encode_header" (MP_TAC o REWRITE_RULE[encode_header_def]) THEN
     COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; WORD_SHL_WORD] THEN
     CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `LENGTH (rs:((A word_loc)heap_address)list) = LENGTH (ws:(A word_loc)list)`
     ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts + 1`; `refs:(data_v bvl_ref)spt`;
                  `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                  `dm:A word -> bool`; `vars:(data_v#A word_loc)list`;
                  `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list`;
                  `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list`;
                  `limit:num`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
                  `roots:((A word_loc)heap_address)list`;
                  `BlockRep tag (rs:((A word_loc)heap_address)list):(A word_loc,
                     data_to_word_memoryProof_tag#(A word_loc)list)heap_element`;
                  `hd:A word`; `ws:(A word_loc)list`; `data_Block ts tag vals`;
                  `wl_Word (ptr_bits c tag (LENGTH (vals:data_v list))):A word_loc`]
                 MP4AUX_memory_rel_alloc_bottom_inplace) THEN
   ASM_REWRITE_TAC[BlockRep_def; el_length_def] THEN ANTS_TAC THENL
    [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[BlockRep_def]) THEN
     SIMP[word_el_def; word_payload_def; SEP_CLAUSES; LENGTH_MAP] THEN
     SUBGOAL_THEN `encode_header c (tag * 4) (LENGTH (ws:(A word_loc)list)) = SOME (hd:A word)`
     ASSUME_TAC THENL [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MP4_X_ASM "abs_ml_inv" (ASSUME_TAC o REWRITE_RULE[BlockRep_def; el_length_def;
     ASSUME `LENGTH (rs:((A word_loc)heap_address)list) = LENGTH (ws:(A word_loc)list)`;
     ASSUME `LENGTH (vals:data_v list) = LENGTH (ws:(A word_loc)list)`] o
     check (fun th -> mp4_is_app "insert" (rand(rator(rator(concl th)))) = false &&
                      can (find_term (fun t -> t = `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`)) (concl th))) THEN
   ASM_REWRITE_TAC[SEP_CLAUSES]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `curr:A word` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`word_add (curr:A word) (word_mul bytes_in_word (word a))`;
    `curr:A word`] THEN
  ASM_REWRITE_TAC[MP4AUX_addr_add] THEN
  MP4_ASM "heap_in_memory_store" (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def] o
    check (fun th -> rand(rator(rator(rator(rator(rator(rator(rator(rator(rator(concl th))))))))))
                     = `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                              heap_element)list`)) THEN
  ASM_SIMP_TAC[MP4AUX_make_cons_ptr_get_addr]);;

(* HOL4 line 10070 *)
let memory_rel_REPLICATE = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm v w vars n.
     memory_rel c be ts refs sp st m dm (CONS (v,w) vars) ==>
     memory_rel c be ts refs sp st m dm (APPEND (REPLICATE n (v,w)) vars)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC memory_rel_rearrange THEN
  REWRITE_TAC[MEM_APPEND; MEM_REPLICATE; MEM] THEN MESON_TAC[]);;

(* HOL4 line 10078 (memory_rel_Ref for REPLICATE n v and REPLICATE n w, with *)
(* memory_rel_REPLICATE; the let variable w of memory_rel_Ref is w' here)  *)
let memory_rel_RefArray = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm v w vars n hd new.
     memory_rel c be ts refs sp st m dm (CONS (v,w) vars) /\
     encode_header c 2 n = SOME hd /\ ~(new IN domain refs) /\
     n < sp /\ good_dimindex (:A) ==>
     ?eoh (curr:A word) trig m1.
       FLOOKUP st EndOfHeap = SOME (wl_Word eoh) /\
       FLOOKUP st TriggerGC = SOME (wl_Word trig) /\
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       let w' = word_sub eoh (word_mul bytes_in_word (word (n + 1))) in
       let w1 = word_sub trig (word_mul bytes_in_word (word (n + 1))) in
       data_to_word_memoryProof_store_list w' (CONS (wl_Word hd) (REPLICATE n w))
         m dm = SOME m1 /\
       memory_rel c be ts (insert new (bvl_ValueArray (REPLICATE n v)) refs)
         (sp - (n + 1))
         (st |+ (EndOfHeap,wl_Word w') |+ (TriggerGC,wl_Word w1)) m1 dm
         (CONS (data_RefPtr T new,make_ptr c (word_sub w' curr) (word 0:A word) n)
               vars)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[ZIP_REPLICATE; LENGTH_REPLICATE] (ISPECL
    [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`; `sp:num`;
     `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`; `dm:A word -> bool`;
     `REPLICATE n (v:data_v)`; `REPLICATE n (w:A word_loc)`;
     `vars:(data_v#A word_loc)list`; `hd:A word`; `new:num`] memory_rel_Ref)) THEN
  ASM_SIMP_TAC[memory_rel_REPLICATE]);;

(* HOL4 line 10086 *)
let word_of_byte_def = cake_def
  `word_of_byte (w:A word) =
     let w = word_or (word_shl w 8) w in
     let w = word_or (word_shl w 16) w in
     if dimindex (:A) = 32 then w else word_or (word_shl w 32) w`;;

(* ------------------------------------------------------------------------- *)
(* Helpers: the bits of set_byte, word_of_byte and bytes_to_word.           *)
(* ------------------------------------------------------------------------- *)

let MP4AUX_bit_set_byte = prove
 (`!(a:A word) (b:byte) w be j.
     bit j (set_byte a b w be) <=>
     j < dimindex(:A) /\
     (if byte_index a be <= j /\ j < byte_index a be + 8
      then bit (j - byte_index a be) b else bit j w)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[set_byte_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SPEC_TAC(`byte_index (a:A word) be`, `i:num`) THEN GEN_TAC THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SLICE_ALT; BIT_WORD_SHL; BIT_WORD_ZX; DIMINDEX_8] THEN
  MP_TAC(ISPECL [`b:byte`; `j - i`] BIT_TRIVIAL) THEN
  MP_TAC(ISPECL [`w:A word`; `j:num`] BIT_TRIVIAL) THEN
  REWRITE_TAC[DIMINDEX_8] THEN
  ASM_CASES_TAC `bit (j - i) (b:byte)` THEN ASM_CASES_TAC `bit j (w:A word)` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MP4AUX_byte_index_mul8 = prove
 (`!(a:A word) be. ?k. byte_index a be = 8 * k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[byte_index_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN COND_CASES_TAC THEN MESON_TAC[]);;

let MP4AUX_MOD8_LANE = prove
 (`!j k. 8 * k <= j /\ j < 8 * k + 8 ==> j MOD 8 = j - 8 * k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `k:num` THEN
  ASM_ARITH_TAC);;

let MP4AUX_ENUM_STEP = prove
 (`!a b c d. (a ==> b \/ c) ==> (b ==> d) ==> (a ==> d \/ c)`,
  CONV_TAC TAUT);;

(* |- j < n ==> j = 0 \/ ... \/ j = n - 1 (n >= 1), one small step at a time *)
let mp4_lt_enum (j:term) n =
  let lt k = mk_binary "<" (j, mk_small_numeral k) in
  let eq k = mk_eq (j, mk_small_numeral k) in
  let rec go k =
    if k = 1 then ARITH_RULE (mk_imp (lt 1, eq 0))
    else
      let th = go (k - 1) in
      let step = ARITH_RULE (mk_imp (lt k, mk_disj (lt (k - 1), eq (k - 1)))) in
      MP (MP (SPECL [lt k; lt (k - 1); eq (k - 1); rand (concl th)] MP4AUX_ENUM_STEP)
            step) th in
  go n;;

(* splits a goal on the values of the variable j below n (j < n an assumption) *)
let MP4AUX_ENUM_TAC (j:term) n =
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o
    MATCH_MP (mp4_lt_enum j n) o
    check (fun th -> concl th = mk_binary "<" (j, mk_small_numeral n)));;

let MP4AUX_bit_word_of_byte = prove
 (`!(w:byte) j. good_dimindex(:A) ==>
     (bit j (word_of_byte (word_zx w):A word) <=> j < dimindex(:A) /\ bit (j MOD 8) w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  REWRITE_TAC[word_of_byte_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_ZX; DIMINDEX_8] THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `j < 32` THEN ASM_REWRITE_TAC[] THEN
    MP4AUX_ENUM_TAC `j:num` 32 THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[BIT_TRIVIAL; DIMINDEX_8; ARITH];
    ASM_CASES_TAC `j < 64` THEN ASM_REWRITE_TAC[] THEN
    MP4AUX_ENUM_TAC `j:num` 64 THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[BIT_TRIVIAL; DIMINDEX_8; ARITH]]);;

(* HOL4 line 10093 *)
let ADD_DIV_EQ = prove
 (`(!n. 0 < n ==> !x r. x + r DIV n = (x * n + r) DIV n) /\
   (!n. 0 < n ==> !x r. r DIV n + x = (r + x * n) DIV n)`,
  SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `0 < n ==> ~(n = 0)`]);;

(* HOL4 line 10098 *)
let set_byte_word_of_byte = prove
 (`!a (w:byte) be.
     good_dimindex (:A) ==>
     set_byte a w (word_of_byte (word_zx w:A word)) be = word_of_byte (word_zx w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `8 <= dimindex(:A)` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MP4AUX_bit_set_byte; MP4AUX_bit_word_of_byte] THEN
  X_CHOOSE_TAC `k:num` (SPECL [`a:A word`; `be:bool`] MP4AUX_byte_index_mul8) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MP4AUX_MOD8_LANE]);;

(* HOL4 line 10114 *)
let w2w_word_of_byte_w2w = prove
 (`!w:byte. good_dimindex(:A) ==> word_zx (word_of_byte (word_zx w:A word)) = w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_8] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `j < dimindex(:A)` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[BIT_WORD_ZX; MP4AUX_bit_word_of_byte; DIMINDEX_8; MOD_LT]);;

let MP4AUX_bytes_to_word_REPLICATE_word_of_byte = prove
 (`!k (a:A word) m (w:byte) be. good_dimindex(:A) ==>
     bytes_to_word k a (REPLICATE m w) (word_of_byte (word_zx w)) be =
     word_of_byte (word_zx w)`,
  INDUCT_TAC THEN REWRITE_TAC[bytes_to_word_eq] THEN
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[REPLICATE; bytes_to_word_eq] THEN
  ASM_SIMP_TAC[set_byte_word_of_byte]);;

(* HOL4 line 10122 *)
let write_bytes_REPLICATE = prove
 (`!(w:byte) be n m.
     good_dimindex (:A) ==>
     write_bytes (REPLICATE m w) (REPLICATE n (word_of_byte (word_zx w))) be =
     REPLICATE n (word_of_byte (word_zx w:A word))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[REPLICATE; write_bytes_def; LET_DEF; LET_END_DEF; DROP_REPLICATE;
               MP4AUX_bytes_to_word_REPLICATE_word_of_byte]);;

(* HOL4 line 10137 *)
let IMP_EXP_LESS = prove
 (`!m l. m <= l ==> 2 EXP m <= 2 EXP l`,
  SIMP_TAC[LE_EXP; ARITH_EQ]);;

(* HOL4 line 10143: shift_shift_lemma *)
let data_to_word_memoryProof_shift_shift_lemma = prove
 (`!l k t n i.
     l = k + backend_common_word_shift (:A) /\ t < k /\ n DIV i < 2 EXP t /\
     l = dimindex (:A) /\
     i = 2 EXP backend_common_word_shift (:A) /\ n < dimword (:A) ==>
     word_ushr (word_shl (word n) (k - t)) (l - t) = word (n DIV i):A word`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `s = backend_common_word_shift (:A)` THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dimword_def]) THEN
  SUBGOAL_THEN `n < 2 EXP s * 2 EXP t` ASSUME_TAC THENL
   [UNDISCH_TAC `n DIV i < 2 EXP t` THEN ASM_SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP (k - t) * n < 2 EXP dimindex(:A)` ASSUME_TAC THENL
   [SUBGOAL_THEN `2 EXP dimindex(:A) = 2 EXP (k - t) * (2 EXP s * 2 EXP t)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD_SHL; VAL_WORD] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  SUBGOAL_THEN `n DIV 2 EXP s < 2 EXP dimindex(:A)`
    (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[DIV_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k + s) - t = (k - t) + s` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ]);;

(* HOL4 line 10167 *)
let write_bytes_APPEND = prove
 (`!xs (ys:(A word)list) vals be.
     write_bytes vals (APPEND xs ys) be =
     APPEND (write_bytes vals xs be)
            (write_bytes (DROP ((dimindex (:A) DIV 8) * LENGTH xs) vals) ys be)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; write_bytes_def; LENGTH; MULT_CLAUSES; DROP_0; LET_DEF;
                  LET_END_DEF; DROP_DROP_T] THEN
  REWRITE_TAC[ADD_SYM]);;

let MP4AUX_byte_index_word = prove
 (`!n be. n < dimindex(:A) DIV 8 ==>
     byte_index (word n:A word) be =
     8 * (if be then dimindex(:A) DIV 8 - 1 - n else n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[byte_index_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `val (word n:A word) = n` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN MATCH_MP_TAC LT_TRANS THEN
    EXISTS_TAC `dimindex(:A)` THEN REWRITE_TAC[LT_POW2_REFL] THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `dimindex(:A) DIV 8` THEN ASM_REWRITE_TAC[DIV_LE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* HOL4 line 10176 *)
let set_byte_sort = prove
 (`!b1 b2 (w:A word) be n1 n2.
     set_byte (word n1) b1 (set_byte (word n2:A word) b2 w be) be =
     if n1 = n2 then set_byte (word n1) b1 w be else
     if n1 < dimindex(:A) DIV 8 /\ n2 < dimindex(:A) DIV 8 /\
        good_dimindex(:A) /\ ~(n2 = n1)
     then set_byte (word n2) b2 (set_byte (word n1) b1 w be) be
     else set_byte (word n1) b1 (set_byte (word n2) b2 w be) be`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; MP4AUX_bit_set_byte] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  ASM_SIMP_TAC[WORD_EQ_BITS_ALT; MP4AUX_bit_set_byte; MP4AUX_byte_index_word] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ABBREV_TAC `d = dimindex(:A) DIV 8` THEN
  BOOL_CASES_TAC `be:bool` THEN REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;


let MP4AUX_set_byte_eq_indep = prove
 (`!(a:A word) x y h h' be.
     set_byte a x h be = set_byte a x h' be <=>
     set_byte a y h be = set_byte a y h' be`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; MP4AUX_bit_set_byte] THEN
  SUBGOAL_THEN `!(z:byte).
      (!j. j < dimindex(:A) ==>
           ((j < dimindex(:A) /\
             (if byte_index (a:A word) be <= j /\ j < byte_index a be + 8
              then bit (j - byte_index a be) z else bit j (h:A word))) <=>
            (j < dimindex(:A) /\
             (if byte_index a be <= j /\ j < byte_index a be + 8
              then bit (j - byte_index a be) z else bit j (h':A word))))) <=>
      (!j. j < dimindex(:A) ==>
           ~(byte_index a be <= j /\ j < byte_index a be + 8) ==>
           (bit j h <=> bit j h'))`
    (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[];
    COND_CASES_TAC THEN ASM_SIMP_TAC[]]);;

(* HOL4 line 10203: set_byte_sort_dec and set_byte_sort_asc are generated   *)
(* by ML (the instances of set_byte_sort for the numerals 0..7 with n1 < n2 *)
(* and n2 < n1, simplified with good_dimindex_def): not stated here         *)

(* HOL4 line 10215 *)
let set_byte_eq_ARB = prove
 (`!be. good_dimindex (:A) ==>
     !x h h'.
       (set_byte (word 0) x h be = set_byte (word 0) x (h':A word) be <=>
        set_byte (word 0) ARB h be = set_byte (word 0) ARB h' be) /\
       (set_byte (word 1) x h be = set_byte (word 1) x (h':A word) be <=>
        set_byte (word 1) ARB h be = set_byte (word 1) ARB h' be) /\
       (set_byte (word 2) x h be = set_byte (word 2) x (h':A word) be <=>
        set_byte (word 2) ARB h be = set_byte (word 2) ARB h' be) /\
       (set_byte (word 3) x h be = set_byte (word 3) x (h':A word) be <=>
        set_byte (word 3) ARB h be = set_byte (word 3) ARB h' be) /\
       (set_byte (word 4) x h be = set_byte (word 4) x (h':A word) be <=>
        set_byte (word 4) ARB h be = set_byte (word 4) ARB h' be) /\
       (set_byte (word 5) x h be = set_byte (word 5) x (h':A word) be <=>
        set_byte (word 5) ARB h be = set_byte (word 5) ARB h' be) /\
       (set_byte (word 6) x h be = set_byte (word 6) x (h':A word) be <=>
        set_byte (word 6) ARB h be = set_byte (word 6) ARB h' be) /\
       (set_byte (word 7) x h be = set_byte (word 7) x (h':A word) be <=>
        set_byte (word 7) ARB h be = set_byte (word 7) ARB h' be)`,
  REPEAT STRIP_TAC THEN REPEAT CONJ_TAC THEN MATCH_ACCEPT_TAC MP4AUX_set_byte_eq_indep);;

(* the bits of bytes_to_word: the positions written depend only on the     *)
(* number of bytes                                                          *)
let MP4AUX_bytes_to_word_shape = prove
 (`!k (a:A word) n be. ?P. !bs. LENGTH bs = n ==> ?Q. !h j.
     bit j (bytes_to_word k a bs h be) <=> if P j then Q j else bit j h`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN EXISTS_TAC `\j:num. F` THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `\j:num. F` THEN REWRITE_TAC[bytes_to_word_eq];
    ALL_TAC] THEN
  GEN_TAC THEN INDUCT_TAC THENL
   [GEN_TAC THEN EXISTS_TAC `\j:num. F` THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `\j:num. F` THEN
    FIRST_X_ASSUM(SUBST1_TAC o REWRITE_RULE[LENGTH_EQ_NIL]) THEN
    REWRITE_TAC[bytes_to_word_eq];
    ALL_TAC] THEN
  GEN_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `P':num->bool` o
    SPECL [`word_add a (word 1):A word`; `n:num`; `be:bool`] o
    check (fun th -> can (find_term (fun t -> t = `bytes_to_word:num->A word->byte list->
      A word->bool->A word`)) (concl th) && is_forall (concl th) &&
      (let v,_ = dest_forall (concl th) in type_of v = `:A word`))) THEN
  EXISTS_TAC `\j. (byte_index (a:A word) be <= j /\ j < byte_index a be + 8) \/ P' j` THEN
  REWRITE_TAC[LENGTH_EQ_CONS] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `Q':num->bool` o C MATCH_MP
    (ASSUME `LENGTH (t:byte list) = n`)) THEN
  EXISTS_TAC `\j. j < dimindex(:A) /\
    (if byte_index (a:A word) be <= j /\ j < byte_index a be + 8
     then bit (j - byte_index a be) (h:byte) else Q' j)` THEN
  ASM_REWRITE_TAC[bytes_to_word_eq; MP4AUX_bit_set_byte] THEN
  MAP_EVERY X_GEN_TAC [`x:A word`; `j:num`] THEN
  MP_TAC(ISPECL [`x:A word`; `j:num`] BIT_TRIVIAL) THEN REWRITE_TAC[GSYM NOT_LT] THEN
  ASM_CASES_TAC `j < dimindex(:A)` THEN ASM_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;


let MP4AUX_bytes_to_word_eq_indep = prove
 (`!k (a:A word) bs bs' h h' be.
     LENGTH bs' = LENGTH bs ==>
     (bytes_to_word k a bs h be = bytes_to_word k a bs h' be <=>
      bytes_to_word k a bs' h be = bytes_to_word k a bs' h' be)`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC `P:num->bool` (SPECL [`k:num`; `a:A word`; `LENGTH (bs:byte list)`;
    `be:bool`] MP4AUX_bytes_to_word_shape) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `Q:num->bool` o C MATCH_MP (REFL `LENGTH (bs:byte list)`)) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `Q':num->bool` o C MATCH_MP
    (ASSUME `LENGTH (bs':byte list) = LENGTH (bs:byte list)`)) THEN
  ASM_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

(* HOL4 line 10241 *)
let bytes_to_word_eq_lemma = prove
 (`!bs bs' (h:A word) h' be.
     good_dimindex (:A) /\ LENGTH bs' = LENGTH bs /\
     bytes_to_word (dimindex (:A) DIV 8) (word 0) bs h be =
     bytes_to_word (dimindex (:A) DIV 8) (word 0) bs h' be ==>
     bytes_to_word (dimindex (:A) DIV 8) (word 0) bs' h be =
     bytes_to_word (dimindex (:A) DIV 8) (word 0) bs' h' be`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`dimindex (:A) DIV 8`; `word 0:A word`; `bs:byte list`; `bs':byte list`;
                 `h:A word`; `h':A word`; `be:bool`] MP4AUX_bytes_to_word_eq_indep) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 10263 *)
let write_bytes_inj_lemma = prove
 (`!be. good_dimindex(:A) ==>
     !w1 w2 bs bs'.
       write_bytes bs w1 be = write_bytes bs (w2:(A word)list) be /\
       LENGTH w1 = LENGTH w2 /\
       LENGTH bs' = LENGTH bs
       ==>
       write_bytes bs' w1 be = write_bytes bs' w2 be`,
  GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; write_bytes_def; LET_DEF; LET_END_DEF;
              CONS_11; SUC_INJ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`dimindex (:A) DIV 8`; `word 0:A word`; `bs:byte list`;
                   `bs':byte list`; `h:A word`; `h':A word`; `be:bool`]
                  MP4AUX_bytes_to_word_eq_indep) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `DROP (dimindex (:A) DIV 8) (bs:byte list)` THEN
    ASM_REWRITE_TAC[LENGTH_DROP]]);;

(* HOL4 line 10282 *)
let set_byte_all_64 = prove
 (`!b1 b2 b3 b4 b5 b6 b7 b8 x y be.
     dimindex(:A) = 64 ==>
     set_byte (word 0:A word) b1
       (set_byte (word 1) b2
         (set_byte (word 2) b3
           (set_byte (word 3) b4
             (set_byte (word 4) b5
               (set_byte (word 5) b6
                 (set_byte (word 6) b7
                   (set_byte (word 7) b8 x be) be) be) be) be) be) be) be
     =
     set_byte (word 0) b1
       (set_byte (word 1) b2
         (set_byte (word 2) b3
           (set_byte (word 3) b4
             (set_byte (word 4) b5
               (set_byte (word 5) b6
                 (set_byte (word 6) b7
                   (set_byte (word 7) b8 y be) be) be) be) be) be) be) be`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `dimindex(:A) DIV 8 = 8` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `good_dimindex(:A)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[good_dimindex_def]; ALL_TAC] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  ASM_SIMP_TAC[MP4AUX_bit_set_byte; MP4AUX_byte_index_word; MP4AUX_bit_word_of_byte; ARITH] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  BOOL_CASES_TAC `be:bool` THEN MP4AUX_ENUM_TAC `j:num` 64 THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 10307 *)
let set_byte_all_32 = prove
 (`!b1 b2 b3 b8 x y be.
     dimindex(:A) = 32 ==>
     set_byte (word 0:A word) b1
       (set_byte (word 1) b2
         (set_byte (word 2) b3
           (set_byte (word 3) b8 x be) be) be) be
     =
     set_byte (word 0) b1
       (set_byte (word 1) b2
         (set_byte (word 2) b3
           (set_byte (word 3) b8 y be) be) be) be`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `dimindex(:A) DIV 8 = 4` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `good_dimindex(:A)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[good_dimindex_def]; ALL_TAC] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  ASM_SIMP_TAC[MP4AUX_bit_set_byte; MP4AUX_byte_index_word; MP4AUX_bit_word_of_byte; ARITH] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  BOOL_CASES_TAC `be:bool` THEN MP4AUX_ENUM_TAC `j:num` 32 THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 10325 *)
let word_of_byte_set_byte_64 = prove
 (`!(w:byte) x be.
     dimindex(:A) = 64 ==>
     word_of_byte (word_zx w) =
     set_byte (word 0) w
       (set_byte (word 1) w
         (set_byte (word 2) w
           (set_byte (word 3) w
             (set_byte (word 4) w
               (set_byte (word 5) w
                 (set_byte (word 6) w
                   (set_byte (word 7) w (x:A word) be) be) be) be) be) be) be) be`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `dimindex(:A) DIV 8 = 8` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `good_dimindex(:A)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[good_dimindex_def]; ALL_TAC] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  ASM_SIMP_TAC[MP4AUX_bit_set_byte; MP4AUX_byte_index_word; MP4AUX_bit_word_of_byte; ARITH] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  BOOL_CASES_TAC `be:bool` THEN MP4AUX_ENUM_TAC `j:num` 64 THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 10341 *)
let word_of_byte_set_byte_32 = prove
 (`!(w:byte) x be.
     dimindex(:A) = 32 ==>
     word_of_byte (word_zx w) =
     set_byte (word 0) w
       (set_byte (word 1) w
         (set_byte (word 2) w
           (set_byte (word 3) w (x:A word) be) be) be) be`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `dimindex(:A) DIV 8 = 4` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `good_dimindex(:A)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[good_dimindex_def]; ALL_TAC] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  ASM_SIMP_TAC[MP4AUX_bit_set_byte; MP4AUX_byte_index_word; MP4AUX_bit_word_of_byte; ARITH] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  BOOL_CASES_TAC `be:bool` THEN MP4AUX_ENUM_TAC `j:num` 32 THEN
  CONV_TAC NUM_REDUCE_CONV);;
(* the bytes of the lanes i .. i + k - 1 of bytes_to_word do not depend on  *)
(* the word written into                                                    *)
let MP4AUX_bytes_to_word_lanes = prove
 (`!k i bs (w:A word) (w':A word) be j.
     good_dimindex(:A) /\ k <= LENGTH bs /\ i + k <= dimindex(:A) DIV 8 /\
     (if be then 8 * (dimindex(:A) DIV 8 - (i + k)) <= j /\
                 j < 8 * (dimindex(:A) DIV 8 - i)
      else 8 * i <= j /\ j < 8 * (i + k)) ==>
     (bit j (bytes_to_word k (word i) bs w be) <=>
      bit j (bytes_to_word k (word i) bs w' be))`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC k <= 0)`] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_SUC] THEN STRIP_TAC THEN
  REWRITE_TAC[bytes_to_word_eq; MP4AUX_bit_set_byte; GSYM WORD_ADD] THEN
  SUBGOAL_THEN `i < dimindex(:A) DIV 8` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MP4AUX_byte_index_word] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  BOOL_CASES_TAC `be:bool` THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MP4AUX_bytes_to_word_full = prove
 (`!bs (w:A word) w' be.
     good_dimindex(:A) /\ dimindex(:A) DIV 8 <= LENGTH bs ==>
     bytes_to_word (dimindex(:A) DIV 8) (word 0) bs w be =
     bytes_to_word (dimindex(:A) DIV 8) (word 0) bs w' be`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC MP4AUX_bytes_to_word_lanes THEN ASM_REWRITE_TAC[ADD_CLAUSES; SUB_0; LE_REFL] THEN
  UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let MP4AUX_byte_len = prove
 (`!n. good_dimindex(:A) ==> byte_len (:A) n = n DIV (dimindex(:A) DIV 8) + 1`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def; byte_len_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 10353 *)
let write_bytes_change_extra = prove
 (`!ws bs be ws'.
     good_dimindex(:A) /\
     LENGTH ws = LENGTH ws' /\
     LENGTH ws < byte_len (:A) (LENGTH bs)
     ==>
     write_bytes bs (ws:(A word)list) be = write_bytes bs ws' be`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[LENGTH] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o REWRITE_RULE[LENGTH_EQ_NIL] o SYM o
      check (is_eq o concl)) THEN REWRITE_TAC[write_bytes_def];
    ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `ws':(A word)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ] THEN STRIP_TAC THEN
  REWRITE_TAC[write_bytes_def; LET_DEF; LET_END_DEF; CONS_11] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP MP4AUX_byte_len (ASSUME `good_dimindex(:A)`)]) THEN
  ASM_SIMP_TAC[MP4AUX_byte_len] THEN
  SUBGOAL_THEN `0 < dimindex(:A) DIV 8` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ABBREV_TAC `d = dimindex(:A) DIV 8` THEN
  SUBGOAL_THEN `d <= LENGTH (bs:byte list)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~(n < d) ==> d <= n`) THEN DISCH_TAC THEN
    UNDISCH_TAC `SUC (LENGTH (t:(A word)list)) < LENGTH (bs:byte list) DIV d + 1` THEN
    ASM_SIMP_TAC[DIV_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC MP4AUX_bytes_to_word_full THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH_DROP] THEN
  SUBGOAL_THEN `LENGTH (bs:byte list) DIV d = (LENGTH bs - d) DIV d + 1` ASSUME_TAC THENL
   [SUBGOAL_THEN `LENGTH (bs:byte list) = 1 * d + (LENGTH bs - d)` (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `0 < d ==> ~(d = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* HOL4 line 10393 *)
let last_bytes_def = cake_def
  `last_bytes k b (a:A word) (w:A word) be =
     if k = 0 then w else
       set_byte a b (last_bytes (k - 1) b (word_add a (word 1)) w be) be`;;

(* HOL4 line 10399 (HOL4 also converts the SUC clause to numeral clauses   *)
(* with SUC_TO_NUMERAL_DEFN_CONV, for EVAL; here the SUC form)              *)
let last_bytes_simp = prove
 (`(!b (a:A word) w be. last_bytes 0 b a w be = w) /\
   (!n b (a:A word) w be.
      last_bytes (SUC n) b a w be =
      set_byte a b (last_bytes n b (word_add a (word 1)) w be) be)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [last_bytes_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1]);;

(* HOL4 line 10405 *)
let last_bytes_bytes_to_word_REPLICATE = prove
 (`!b1 b2 be n1 n k a (w:A word).
     n <= k /\ b1 = b2 /\ n1 = n ==>
     bytes_to_word k a (REPLICATE n b2) w be = last_bytes n1 b1 a w be`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN SUBST1_TAC)) THEN
  SPEC_TAC(`a:A word`,`a:A word`) THEN SPEC_TAC(`k:num`,`k:num`) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[REPLICATE; bytes_to_word_eq; last_bytes_simp] THEN
  INDUCT_TAC THEN REWRITE_TAC[ARITH_RULE `~(SUC n <= 0)`; LE_SUC] THEN
  ASM_SIMP_TAC[bytes_to_word_eq; last_bytes_simp]);;

(* HOL4 line 10417 *)
let decode_length_make_byte_header = prove
 (`!c fl len.
     good_dimindex(:A) /\ data_to_word_config_len_size c + 7 < dimindex(:A) /\
     len + 2 EXP backend_common_word_shift(:A) <
       2 EXP (data_to_word_config_len_size c + backend_common_word_shift(:A)) ==>
     len <= val (decode_length c (make_byte_header c fl len):A word) *
            (dimindex(:A) DIV 8) /\
     val (decode_length c (make_byte_header c fl len):A word) <=
       len DIV (dimindex(:A) DIV 8) + 1`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `ls = data_to_word_config_len_size c` THEN
  REWRITE_TAC[good_dimindex_def; decode_length_def; make_byte_header_def;
              backend_common_word_shift_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[ARITH_EQ; WORD_USHR_OR] THEN CONV_TAC NUM_REDUCE_CONV THEN
  FIRST_X_ASSUM(MP_TAC o check (is_conj o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THENL
   [
    (* dimindex 32 *)
    SUBGOAL_THEN `word_ushr (if fl then word 7 else word 23:A word) (32 - ls) = word 0`
      (fun th -> REWRITE_TAC[th; WORD_OR_0]) THENL
     [REWRITE_TAC[WORD_USHR_EQ_0] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 8` THEN
      REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `word_ushr (word_shl (word (len + 4)) (30 - ls)) (32 - ls) =
                  word ((len + 4) DIV 4):A word` SUBST1_TAC THENL
     [MATCH_MP_TAC data_to_word_memoryProof_shift_shift_lemma THEN
      ASM_REWRITE_TAC[backend_common_word_shift_def; dimword_def] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[EXP_ADD]) THEN
      RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP ls * 4` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP 24 * 4` THEN CONJ_TAC THENL
       [REWRITE_TAC[LE_MULT_RCANCEL; LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
        ASM_ARITH_TAC;
        CONV_TAC NUM_REDUCE_CONV];
      ALL_TAC] THEN
    SUBGOAL_THEN `(len + 4) DIV 4 = len DIV 4 + 1` SUBST1_TAC THENL
     [SUBGOAL_THEN `len + 4 = len + 1 * 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[DIV_MULT_ADD; ARITH_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `val (word (len DIV 4 + 1):A word) = len DIV 4 + 1` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `len + 4` THEN CONJ_TAC THENL
       [MP_TAC(SPECL [`len:num`; `4`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP (ls + 2)` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`len:num`; `4`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN
    ARITH_TAC;
    (* dimindex 64 *)
    SUBGOAL_THEN `word_ushr (if fl then word 7 else word 23:A word) (64 - ls) = word 0`
      (fun th -> REWRITE_TAC[th; WORD_OR_0]) THENL
     [REWRITE_TAC[WORD_USHR_EQ_0] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 8` THEN
      REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `word_ushr (word_shl (word (len + 8)) (61 - ls)) (64 - ls) =
                  word ((len + 8) DIV 8):A word` SUBST1_TAC THENL
     [MATCH_MP_TAC data_to_word_memoryProof_shift_shift_lemma THEN
      ASM_REWRITE_TAC[backend_common_word_shift_def; dimword_def] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[EXP_ADD]) THEN
      RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP ls * 8` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP 56 * 8` THEN CONJ_TAC THENL
       [REWRITE_TAC[LE_MULT_RCANCEL; LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
        ASM_ARITH_TAC;
        CONV_TAC NUM_REDUCE_CONV];
      ALL_TAC] THEN
    SUBGOAL_THEN `(len + 8) DIV 8 = len DIV 8 + 1` SUBST1_TAC THENL
     [SUBGOAL_THEN `len + 8 = len + 1 * 8` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[DIV_MULT_ADD; ARITH_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `val (word (len DIV 8 + 1):A word) = len DIV 8 + 1` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `len + 8` THEN CONJ_TAC THENL
       [MP_TAC(SPECL [`len:num`; `8`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP (ls + 3)` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`len:num`; `8`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN
    ARITH_TAC]);;


let MP4AUX_decode_length_make_byte_header_eq = prove
 (`!c fl len.
     good_dimindex(:A) /\ data_to_word_config_len_size c + 7 < dimindex(:A) /\
     len + 2 EXP backend_common_word_shift(:A) <
       2 EXP (data_to_word_config_len_size c + backend_common_word_shift(:A)) ==>
     decode_length c (make_byte_header c fl len):A word =
     word (len DIV (dimindex(:A) DIV 8) + 1)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `ls = data_to_word_config_len_size c` THEN
  REWRITE_TAC[good_dimindex_def; decode_length_def; make_byte_header_def;
              backend_common_word_shift_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[ARITH_EQ; WORD_USHR_OR] THEN CONV_TAC NUM_REDUCE_CONV THEN
  FIRST_X_ASSUM(MP_TAC o check (is_conj o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THENL
   [
    SUBGOAL_THEN `word_ushr (if fl then word 7 else word 23:A word) (32 - ls) = word 0`
      (fun th -> REWRITE_TAC[th; WORD_OR_0]) THENL
     [REWRITE_TAC[WORD_USHR_EQ_0] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 8` THEN
      REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `word_ushr (word_shl (word (len + 4)) (30 - ls)) (32 - ls) =
                  word ((len + 4) DIV 4):A word` SUBST1_TAC THENL
     [MATCH_MP_TAC data_to_word_memoryProof_shift_shift_lemma THEN
      ASM_REWRITE_TAC[backend_common_word_shift_def; dimword_def] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[EXP_ADD]) THEN
      RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP ls * 4` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP 24 * 4` THEN CONJ_TAC THENL
       [REWRITE_TAC[LE_MULT_RCANCEL; LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
        ASM_ARITH_TAC;
        CONV_TAC NUM_REDUCE_CONV];
      ALL_TAC] THEN
    SUBGOAL_THEN `len + 4 = len + 1 * 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[DIV_MULT_ADD; ARITH_EQ];
    SUBGOAL_THEN `word_ushr (if fl then word 7 else word 23:A word) (64 - ls) = word 0`
      (fun th -> REWRITE_TAC[th; WORD_OR_0]) THENL
     [REWRITE_TAC[WORD_USHR_EQ_0] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 8` THEN
      REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `word_ushr (word_shl (word (len + 8)) (61 - ls)) (64 - ls) =
                  word ((len + 8) DIV 8):A word` SUBST1_TAC THENL
     [MATCH_MP_TAC data_to_word_memoryProof_shift_shift_lemma THEN
      ASM_REWRITE_TAC[backend_common_word_shift_def; dimword_def] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[EXP_ADD]) THEN
      RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP ls * 8` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP 56 * 8` THEN CONJ_TAC THENL
       [REWRITE_TAC[LE_MULT_RCANCEL; LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
        ASM_ARITH_TAC;
        CONV_TAC NUM_REDUCE_CONV];
      ALL_TAC] THEN
    SUBGOAL_THEN `len + 8 = len + 1 * 8` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[DIV_MULT_ADD; ARITH_EQ]]);;


let MP4AUX_byte_len_bound = prove
 (`!n m. good_dimindex(:A) /\ byte_len (:A) n < 2 EXP m ==>
     n + 2 EXP backend_common_word_shift(:A) <
     2 EXP (m + backend_common_word_shift(:A))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def; byte_len_def;
    backend_common_word_shift_def; EXP_ADD] THEN
  DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`n:num`; `4`] DIVISION); MP_TAC(SPECL [`n:num`; `8`] DIVISION)] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

(* HOL4 line 10470 *)
let memory_rel_RefByte_content = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars new n bytes fl.
     memory_rel c be ts refs sp st m dm vars /\
     ~(new IN domain refs) /\ byte_len (:A) n < sp /\
     byte_len (:A) n < 2 EXP (dimindex (:A) - 4) /\
     byte_len (:A) n < 2 EXP data_to_word_config_len_size c /\ n = LENGTH bytes /\
     good_dimindex (:A) ==>
     ?free curr m1.
       FLOOKUP st NextFree = SOME (wl_Word free) /\
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       (let w' = word_mul bytes_in_word (word (byte_len (:A) n + 1)):A word in
        let ws = REPLICATE (byte_len (:A) n) (word 0) in
        let ws = write_bytes bytes ws be in
        data_to_word_memoryProof_store_list free
          (CONS (wl_Word (make_byte_header c fl n)) (MAP wl_Word ws)) m dm =
          SOME m1 /\
        memory_rel c be ts (insert new (bvl_ByteArray fl bytes) refs)
          (sp - (byte_len (:A) n + 1)) (st |+ (NextFree,wl_Word (word_add free w')))
          m1 dm
          (CONS (data_RefPtr T new,make_ptr c (word_sub free curr) (word 0:A word)
                                     (byte_len (:A) n)) vars))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  MP4_X_ASM "memory_rel" (STRIP_ASSUME_TAC o REWRITE_RULE[MP4AUX_memory_rel_unfold]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `n = LENGTH (bytes:byte list)`)) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `MAP FST (vars:(data_v#A word_loc)list)`;
                 `refs:(data_v bvl_ref)spt`; `hs:((A word_loc)heap_address)list`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `be:bool`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`; `limit:num`;
                 `ts:num`; `byte_len (:A) (LENGTH (bytes:byte list))`; `bytes:byte list`;
                 `new:num`; `fl:bool`; `T`] new_byte_alt_thm) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MP4AUX_byte_len] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP MP4AUX_byte_len (ASSUME `good_dimindex(:A)`)]) THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `heap2:((A word_loc,data_to_word_memoryProof_tag#
    (A word_loc)list)heap_element)list` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `k = byte_len (:A) (LENGTH (bytes:byte list))` THEN
  MP4_ASM "heap_in_memory_store" (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
  SUBGOAL_THEN `decode_length c (make_byte_header c fl (LENGTH (bytes:byte list))) =
                word k:A word /\
                LENGTH bytes + 2 EXP backend_common_word_shift(:A) <
                2 EXP (data_to_word_config_len_size c + backend_common_word_shift(:A))`
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
     [EXPAND_TAC "k" THEN MATCH_MP_TAC MP4AUX_byte_len_bound THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN ASM_SIMP_TAC[MP4AUX_decode_length_make_byte_header_eq] THEN
      EXPAND_TAC "k" THEN
      REWRITE_TAC[MATCH_MP MP4AUX_byte_len (ASSUME `good_dimindex(:A)`)]];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_to_word_memoryProof_Bytes_def; LET_DEF; LET_END_DEF]) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
                 `insert new (bvl_ByteArray fl bytes) (refs:(data_v bvl_ref)spt)`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                 `dm:A word -> bool`; `vars:(data_v#A word_loc)list`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `limit:num`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
                 `hs:((A word_loc)heap_address)list`;
                 `DataElement [] (LENGTH (write_bytes bytes (REPLICATE k (word 0:A word)) be))
                    (BytesTag fl (LENGTH (bytes:byte list)),
                     MAP wl_Word (write_bytes bytes (REPLICATE k (word 0:A word)) be)):
                    (A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element`;
                 `make_byte_header c fl (LENGTH (bytes:byte list)):A word`;
                 `MAP wl_Word (write_bytes bytes (REPLICATE k (word 0:A word)) be)`;
                 `data_RefPtr T new`; `wl_Word (word 0):A word_loc`]
                MP4AUX_memory_rel_alloc_bottom) THEN
  ASM_REWRITE_TAC[el_length_def; LENGTH_MAP; LENGTH_write_bytes; LENGTH_REPLICATE] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP[word_el_def; word_payload_def; SEP_CLAUSES; LENGTH_MAP; LENGTH_write_bytes;
         LENGTH_REPLICATE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[backend_common_word_shift_def]) THEN
    ASM_REWRITE_TAC[SEP_CLAUSES];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cur2:A word` (X_CHOOSE_THEN `m1:A word -> A word_loc`
     STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`word_add (cur2:A word) (word_mul bytes_in_word (word a))`;
    `cur2:A word`; `m1:A word -> A word_loc`] THEN
  ASM_REWRITE_TAC[MP4AUX_addr_add] THEN
  ASM_SIMP_TAC[MP4AUX_make_ptr_get_addr]);;


let MP4AUX_write_bytes_REPLICATE_last = prove
 (`!n (w:byte) be. good_dimindex(:A) ==>
     MAP wl_Word (write_bytes (REPLICATE n w) (REPLICATE (byte_len (:A) n) (word 0:A word)) be) =
     LUPDATE (wl_Word (last_bytes (n MOD (dimindex(:A) DIV 8)) w (word 0) (word 0) be))
       (byte_len (:A) n - 1)
       (REPLICATE (byte_len (:A) n) (wl_Word (word_of_byte (word_zx w):A word)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MP4AUX_byte_len; ADD_SUB] THEN
  SUBGOAL_THEN `0 < dimindex(:A) DIV 8` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ABBREV_TAC `l = n DIV (dimindex(:A) DIV 8)` THEN
  REWRITE_TAC[GSYM ADD1; REPLICATE_SNOC; SNOC_APPEND] THEN
  REWRITE_TAC[write_bytes_APPEND; MAP_APPEND; LENGTH_REPLICATE] THEN
  MP_TAC(ISPECL [`REPLICATE l (wl_Word (word_of_byte (word_zx (w:byte)):A word))`;
    `wl_Word (last_bytes (n MOD (dimindex(:A) DIV 8)) w (word 0) (word 0) be:A word)`;
    `wl_Word (word_of_byte (word_zx (w:byte)):A word)`; `[]:(A word_loc)list`]
    LUPDATE_LENGTH) THEN
  REWRITE_TAC[LENGTH_REPLICATE] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `write_bytes (REPLICATE n (w:byte)) (REPLICATE l (word 0:A word)) be =
                REPLICATE l (word_of_byte (word_zx w))` SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `write_bytes (REPLICATE n (w:byte))
                  (REPLICATE l (word_of_byte (word_zx w):A word)) be` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC write_bytes_change_extra THEN
      ASM_SIMP_TAC[LENGTH_REPLICATE; MP4AUX_byte_len] THEN ARITH_TAC;
      ASM_SIMP_TAC[write_bytes_REPLICATE]];
    ALL_TAC] THEN
  REWRITE_TAC[map_replicate; DROP_REPLICATE; write_bytes_def; LET_DEF; LET_END_DEF; MAP] THEN
  AP_TERM_TAC THEN REWRITE_TAC[CONS_11; injectivity "word_loc"] THEN
  MATCH_MP_TAC last_bytes_bytes_to_word_REPLICATE THEN REWRITE_TAC[] THEN
  MP_TAC(SPECL [`n:num`; `dimindex(:A) DIV 8`] DIVISION) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < d ==> ~(d = 0)`] THEN ARITH_TAC);;

(* HOL4 line 10565 *)
let memory_rel_RefByte_alt = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars new n w fl.
     memory_rel c be ts refs sp st m dm vars /\
     ~(new IN domain refs) /\ byte_len (:A) n < sp /\
     byte_len (:A) n < 2 EXP (dimindex (:A) - 4) /\
     byte_len (:A) n < 2 EXP data_to_word_config_len_size c /\
     good_dimindex (:A) ==>
     ?free curr m1.
       FLOOKUP st NextFree = SOME (wl_Word free) /\
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       (let w' = word_mul bytes_in_word (word (byte_len (:A) n + 1)):A word in
        let ws = REPLICATE (byte_len (:A) n) (wl_Word (word_of_byte (word_zx w))) in
        let nb = n MOD (dimindex(:A) DIV 8) in
        let ws = LUPDATE (wl_Word (last_bytes nb w (word 0) (word 0) be))
                   (byte_len (:A) n - 1) ws in
        data_to_word_memoryProof_store_list free
          (CONS (wl_Word (make_byte_header c fl n)) ws) m dm = SOME m1 /\
        memory_rel c be ts (insert new (bvl_ByteArray fl (REPLICATE n w)) refs)
          (sp - (byte_len (:A) n + 1)) (st |+ (NextFree,wl_Word (word_add free w')))
          m1 dm
          (CONS (data_RefPtr T new,make_ptr c (word_sub free curr) (word 0:A word)
                                     (byte_len (:A) n)) vars))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                 `dm:A word -> bool`; `vars:(data_v#A word_loc)list`; `new:num`; `n:num`;
                 `REPLICATE n (w:byte)`; `fl:bool`] memory_rel_RefByte_content) THEN
  ASM_REWRITE_TAC[LENGTH_REPLICATE; LET_DEF; LET_END_DEF] THEN
  ASM_SIMP_TAC[MP4AUX_write_bytes_REPLICATE_last]);;

(* HOL4 line 10689 *)
let memory_rel_tail = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm v vars.
     memory_rel c be ts refs sp st m dm (CONS v vars) ==>
     memory_rel c be ts refs sp st m dm vars`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC memory_rel_rearrange THEN
  REWRITE_TAC[MEM] THEN MESON_TAC[]);;

(* HOL4 line 10696 *)
let memory_rel_drop = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vs vars.
     memory_rel c be ts refs sp st m dm (APPEND vs vars) ==>
     memory_rel c be ts refs sp st m dm vars`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC memory_rel_rearrange THEN
  REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[]);;

let MP4AUX_STAR_SEP_T = prove
 (`!p q (s:A->bool). (p STAR q) s ==> (p STAR SEP_T) s`,
  REWRITE_TAC[STAR_def; SEP_T_def] THEN MESON_TAC[]);;

(* HOL4 line 10703 *)
let memory_rel_IMP_word_list_exists = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars n f.
     memory_rel c be ts refs sp st m dm vars /\ n <= sp /\
     FLOOKUP st NextFree = SOME (wl_Word f) ==>
     (word_list_exists f n STAR SEP_T) (fun2set (m,dm))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MP4AUX_memory_rel_unfold] THEN STRIP_TAC THEN
  MP4_ASM "heap_in_memory_store" (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
  SUBGOAL_THEN `f = word_add (curr:A word) (word_mul bytes_in_word (word a))`
    SUBST_ALL_TAC THENL
   [UNDISCH_TAC `FLOOKUP st NextFree = SOME (wl_Word (f:A word))` THEN
    ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[data_to_word_memoryProof_word_list_exists_thm; SEP_CLAUSES; SEP_T_def];
    ALL_TAC] THEN
  MP4_ASM "abs_ml_inv" (MP_TAC o REWRITE_RULE[abs_ml_inv_def]) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o REWRITE_RULE[unused_space_inv_def] o
    CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN
    `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    (X_CHOOSE_THEN
      `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
      STRIP_ASSUME_TAC) o MATCH_MP heap_lookup_SPLIT) THEN
  MP4_VAR_ASM "heap" SUBST_ALL_TAC THEN MP4_VAR_ASM "a" SUBST_ALL_TAC THEN
  MP4_X_ASM "STAR" (MP_TAC o REWRITE_RULE[word_heap_APPEND; word_heap_def; word_el_def;
    el_length_def] o check (fun th -> mp4_is_fun2set_asm (concl th))) THEN
  SUBGOAL_THEN `((sp0 + sp1) - 1) + 1 = n + ((sp0 + sp1) - n)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[data_to_word_memoryProof_word_list_exists_ADD] THEN
  DISCH_THEN(MATCH_ACCEPT_TAC o MATCH_MP MP4AUX_STAR_SEP_T o
    MP4AUX_STAR_FOCUS (fun l -> mp4_is_app "word_list_exists" l && rand l = `n:num`)));;

(* HOL4 line 10731 *)
let get_addr_0 = prove
 (`!c n u. bit 0 (get_addr c n u:A word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[get_addr_def] THEN
  ONCE_REWRITE_TAC[get_lowerbits_or_1] THEN
  SIMP_TAC[BIT_WORD_OR; BIT_WORD_1; ARITH_RULE `1 <= n ==> 0 < n`; DIMINDEX_GE_1]);;

(* HOL4 line 10738 *)
let word_addr_eq_Loc = prove
 (`!c (v:(A word_loc)heap_address) l1 l2.
     word_addr c v = wl_Loc l1 l2 <=>
     l2 = 0 /\ ?l2. v = gc_shared_Data (wl_Loc l1 l2)`,
  REPEAT GEN_TAC THEN CASES_ON `v:(A word_loc)heap_address` THEN
  TRY(CASES_ON `a:A word_loc`) THEN
  REWRITE_TAC[word_addr_def; injectivity "word_loc"; distinctness "word_loc";
              injectivity "heap_address"; distinctness "heap_address"] THEN
  MESON_TAC[]);;

(* HOL4 line 10746 *)
let blocks_unique_CodePtr = prove
 (`!ts refs (vars:(data_v#A)list) lab.
     blocks_unique ts (all_vs refs (MAP FST vars)) ==>
     blocks_unique ts (all_vs refs (CONS (data_CodePtr lab) (MAP FST vars)))`,
  REWRITE_TAC[blocks_unique_def; all_vs_def; IN_UNION; IN_ELIM_THM; v_all_vs_def; MEM;
              distinctness "data_v"] THEN
  MESON_TAC[]);;


let MP4AUX_abs_ml_inv_CodePtr = prove
 (`!conf stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts lab.
     abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts ==>
     abs_ml_inv conf (CONS (data_CodePtr lab) stack) refs
       (CONS (gc_shared_Data (wl_Loc lab 0)) roots,heap,be,a,sp,sp1,gens) limit ts`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP4_ASM "roots_ok" MP_TAC THEN
    REWRITE_TAC[roots_ok_def; MEM; distinctness "heap_address"] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`] THEN
  ASM_SIMP_TAC[all_ts_cons_no_block; distinctness "data_v"; ALL2] THEN
  REPEAT CONJ_TAC THENL
   [MP4_ASM "blocks_unique" MP_TAC THEN
    REWRITE_TAC[blocks_unique_def; all_vs_def; IN_UNION; IN_ELIM_THM; v_all_vs_def; MEM;
                distinctness "data_v"] THEN
    MESON_TAC[];
    ASM_REWRITE_TAC[v_inv_def];
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    REWRITE_TAC[reachable_refs_def; MEM; get_refs_def] THEN
    SIMP[LEFT_AND_OVER_OR; RIGHT_OR_DISTRIB; EXISTS_OR_THM; get_refs_def; MEM]]);;

(* HOL4 line 10759 *)
let memory_rel_CodePtr = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars lab.
     memory_rel c be ts refs sp st m dm vars ==>
     memory_rel c be ts refs sp st m dm (CONS (data_CodePtr lab,wl_Loc lab 0) vars)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MP4AUX_memory_rel_unfold; MAP; FST; SND] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
    `CONS (gc_shared_Data (wl_Loc lab 0:A word_loc)) hs`] THEN
  ASM_SIMP_TAC[MP4AUX_abs_ml_inv_CodePtr; ALL2; word_addr_def]);;

let MP4AUX_heap_in_memory_store_header = prove
 (`!heap a sp sp1 gens c st (m:A word -> A word_loc) dm limit p xs l tag
    (qs:(A word_loc)list).
     heap_in_memory_store heap a sp sp1 gens c st m dm limit /\
     heap_lookup p heap = SOME (DataElement xs l (tag,qs)) ==>
     ?curr. FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       m (word_add curr (word_mul (word p) bytes_in_word)) =
         wl_Word (FST (word_payload xs l tag qs c)) /\
       word_add curr (word_mul (word p) bytes_in_word) IN dm`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP4_ASM "heap_in_memory_store"
    (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
  EXISTS_TAC `curr:A word` THEN ASM_REWRITE_TAC[] THEN
  MP4_X_EQ_ASM "heap_lookup" (X_CHOOSE_THEN
    `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    (X_CHOOSE_THEN
      `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
      STRIP_ASSUME_TAC) o MATCH_MP heap_lookup_SPLIT) THEN
  MP4_VAR_ASM "heap" SUBST_ALL_TAC THEN MP4_VAR_ASM "p" SUBST_ALL_TAC THEN
  ONCE_REWRITE_TAC[WORD_MUL_SYM] THEN
  MP4_X_ASM "STAR" (MP_TAC o REWRITE_RULE[word_heap_APPEND; word_heap_def; word_el_def] o
    check (fun th -> mp4_is_fun2set_asm (concl th))) THEN
  SPEC_TAC(`word_payload xs l tag qs c:A word#(A word_loc)list#bool`,
           `w:A word#(A word_loc)list#bool`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[FST; SND; misc_word_list_def] THEN
  DISCH_THEN(MP_TAC o MATCH_MP read_fun2set o MP4AUX_STAR_FOCUS mp4_is_one) THEN
  SIMP_TAC[]);;

(* HOL4 line 10776 *)
let memory_rel_Block_IMP = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm ts' tag vals v vars.
     memory_rel c be ts refs sp st m dm (CONS (data_Block ts' tag vals,v) vars) /\
     good_dimindex (:A) ==>
     ?w. v = wl_Word w /\
         if vals = [] then
           w = word_add (word_mul (word tag) (word 16)) (word 2) /\ ~bit 0 w /\
           tag < dimword (:A) DIV 16 /\ ts' = 0
         else
           ?a x.
             bit 0 w /\ ~bit 3 x /\ ~bit 2 x /\
             get_real_addr c st w = SOME a /\ m a = wl_Word x /\ a IN dm /\
             decode_length c x = word (LENGTH vals) /\
             LENGTH vals < 2 EXP (dimindex (:A) - 4) /\
             encode_header c (4 * tag) (LENGTH vals) = SOME x /\
             ts' < ts`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MP4AUX_memory_rel_unfold; MAP; FST; SND; LIST_REL_CONS2] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  MP4_ASM "abs_ml_inv" (STRIP_ASSUME_TAC o REWRITE_RULE[abs_ml_inv_def; bc_stack_ref_inv_def; ALL2]) THEN
  MP4_X_ASM "v_inv" (MP_TAC o REWRITE_RULE[v_inv_def]) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[word_addr_def; injectivity "word_loc"; MP4AUX_BlockNil_and] THEN
   EXISTS_TAC `BlockNil tag:A word` THEN REWRITE_TAC[] THEN
   REWRITE_TAC[BlockNil_def; WORD_SHL_WORD; GSYM WORD_MUL; GSYM WORD_ADD] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[BIT_WORD; EXP; DIV_1; ODD_ADD; ODD_MULT; ARITH] THEN
   AP_TERM_TAC THEN ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `ptr:num` (X_CHOOSE_THEN `xs:((A word_loc)heap_address)list`
     STRIP_ASSUME_TAC)) THEN
   RVEQ_TAC THEN REWRITE_TAC[word_addr_def; injectivity "word_loc"] THEN
   EXISTS_TAC `get_addr c ptr (wl_Word (ptr_bits c tag (LENGTH (xs:((A word_loc)heap_address)list)))):A word` THEN
   REWRITE_TAC[get_addr_0] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[BlockRep_def]) THEN
   MP4_ASM "heap_in_memory_store" (fun th -> MP_TAC(MATCH_MP MP4AUX_heap_in_memory_store_header
     (CONJ th (ASSUME `heap_lookup ptr (heap:((A word_loc,data_to_word_memoryProof_tag#
        (A word_loc)list)heap_element)list) = SOME (DataElement
        (xs:((A word_loc)heap_address)list) (LENGTH xs) (BlockTag tag,[]:(A word_loc)list))`)))) THEN
   MP4_ASM "heap_in_memory_store" (fun th -> MP_TAC(MATCH_MP MP4AUX_heap_in_memory_store_el_cond
     (CONJ th (ASSUME `heap_lookup ptr (heap:((A word_loc,data_to_word_memoryProof_tag#
        (A word_loc)list)heap_element)list) = SOME (DataElement
        (xs:((A word_loc)heap_address)list) (LENGTH xs) (BlockTag tag,[]:(A word_loc)list))`)))) THEN
   REWRITE_TAC[word_payload_def; FST; SND; LENGTH_MAP] THEN
   STRIP_TAC THEN DISCH_THEN(X_CHOOSE_THEN `curr:A word` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`word_add curr (word_mul (word ptr) bytes_in_word):A word`;
     `make_header c (word_shl (word tag) 2) (LENGTH (xs:((A word_loc)heap_address)list)):A word`] THEN
   SUBGOAL_THEN `LENGTH (vals:data_v list) = LENGTH (xs:((A word_loc)heap_address)list)` ASSUME_TAC THENL
    [MP4_ASM "ALL2" (fun th -> if rand(rator(concl th)) = `vals:data_v list` then
        ACCEPT_TAC (MATCH_MP EVERY2_LENGTH th) else failwith "");
     ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[] THEN
   MP4_ASM "heap_in_memory_store" (STRIP_ASSUME_TAC o REWRITE_RULE[heap_in_memory_store_def]) THEN
   CONJ_TAC THENL
    [REWRITE_TAC[make_header_def; LET_DEF; LET_END_DEF; BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD] THEN
     CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
   CONJ_TAC THENL
    [REWRITE_TAC[make_header_def; LET_DEF; LET_END_DEF; BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD] THEN
     CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
   CONJ_TAC THENL
    [MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                          heap_element)list`;
                   `c:data_to_word_config`; `ptr:num`;
                   `DataElement (xs:((A word_loc)heap_address)list) (LENGTH xs)
                      (BlockTag tag,[]:(A word_loc)list)`;
                   `st:(store_name,A word_loc)fmap`; `curr:A word`;
                   `wl_Word (ptr_bits c tag (LENGTH (xs:((A word_loc)heap_address)list))):A word_loc`]
                  get_real_addr_get_addr) THEN
     ASM_SIMP_TAC[];
     ALL_TAC] THEN
   MP4_ASM "blocks_unique" (MP_TAC o REWRITE_RULE[blocks_unique_def]) THEN
   DISCH_THEN(MP_TAC o SPECL [`ts':num`; `tag:num`; `vals:data_v list`; `tag:num`;
                              `vals:data_v list`]) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   MATCH_MP_TAC in_all_vs_stack THEN REWRITE_TAC[v_all_vs_def; MEM; APPEND]]);;


let MP4AUX_Smallnum_and_not_1 = prove
 (`!i. good_dimindex (:A) ==>
     word_and (Smallnum i) (word_not (word 1)) = Smallnum i:A word`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[data_to_word_Smallnum_def] THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `?n. &0 - (i:int) = &n` (X_CHOOSE_THEN `n:num` SUBST1_TAC) THENL
     [EXISTS_TAC `num_of_int (&0 - (i:int))` THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM] THEN
    SUBGOAL_THEN `word_sub (word 0) (word (4 * n)) = word_mul (word_neg (word 4)) (word n):A word /\
                  word_not (word 1) = word_neg (word 2):A word`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THENL [REWRITE_TAC[WORD_MUL] THEN CONV_TAC WORD_RULE; CONV_TAC WORD_RULE];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[WORD_AND_SYM] THEN ASM_SIMP_TAC[word_ml_inv_neg_num_lemma];
    SUBGOAL_THEN `?n. (i:int) = &n` (X_CHOOSE_THEN `n:num` SUBST1_TAC) THENL
     [EXISTS_TAC `num_of_int (i:int)` THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM; MP4AUX_word_and_not_1]]);;

(* HOL4 line 10816 *)
let IMP_memory_rel_Number = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars i.
     good_dimindex (:A) /\ small_int (:A) i /\
     memory_rel c be ts refs sp st m dm vars ==>
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number i,wl_Word (Smallnum i):A word_loc) vars)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MP4AUX_memory_rel_unfold; MAP; FST; SND] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`;
    `CONS (gc_shared_Data (wl_Word (Smallnum i:A word))) hs`] THEN
  ASM_SIMP_TAC[abs_ml_inv_Num; ALL2; word_addr_def; MP4AUX_Smallnum_and_not_1]);;

(* HOL4 line 10830 *)
let memory_rel_El_any = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm ts' tag vals ptr vars index.
     memory_rel c be ts refs sp st m dm (CONS (data_Block ts' tag vals,ptr) vars) /\
     good_dimindex (:A) /\
     index < LENGTH vals ==>
     ?ptr_w x (y:A word).
       ptr = wl_Word ptr_w /\
       get_real_addr c st ptr_w = SOME x /\
       word_add (word_add x bytes_in_word) (word_mul bytes_in_word (word index))
         IN dm /\
       memory_rel c be ts refs sp st m dm
         (CONS (EL index vals,
                m (word_add (word_add x bytes_in_word)
                            (word_mul bytes_in_word (word index))))
               (CONS (data_Block ts' tag vals,ptr) vars))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Block_IMP o C CONJ (ASSUME `good_dimindex(:A)`)) THEN
  SUBGOAL_THEN `~(vals:data_v list = [])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; CONJUNCT1 LT]) THEN
    FIRST_ASSUM CONTR_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `x0:A word` (X_CHOOSE_THEN `hd0:A word` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `small_int (:A) (&index)` ASSUME_TAC THENL
   [MATCH_MP_TAC MP4AUX_small_int_LT THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_swap o MATCH_MP IMP_memory_rel_Number o
    (fun th -> CONJ (ASSUME `good_dimindex(:A)`) (CONJ (ASSUME `small_int (:A) (&index)`) th)) o
    check (fun th -> mp4_is_app "memory_rel" (concl th))) THEN
  DISCH_THEN(MP_TAC o MATCH_MP memory_rel_El o C CONJ (CONJ (ASSUME `good_dimindex(:A)`)
    (ASSUME `index < LENGTH (vals:data_v list)`))) THEN
  REWRITE_TAC[injectivity "word_loc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr_w:A word` (X_CHOOSE_THEN `i_w:A word`
    (X_CHOOSE_THEN `x:A word` (X_CHOOSE_THEN `y:A word` STRIP_ASSUME_TAC)))) THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `y = word_add bytes_in_word (word_mul bytes_in_word (word index)):A word`
     SUBST_ALL_TAC THENL
   [UNDISCH_TAC `get_real_offset (Smallnum (&index)) = SOME (y:A word)` THEN
    REWRITE_TAC[get_real_offset_def; data_to_word_Smallnum_def; INT_ARITH `~(&n:int < &0)`;
                INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM; bytes_in_word_def] THEN
    UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[option_INJ; WORD_SHL_WORD] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM WORD_ADD; GSYM WORD_MUL] THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `x0 = x:A word` SUBST_ALL_TAC THENL
   [MP_TAC(TRANS (SYM (ASSUME `get_real_addr c st ptr_w = SOME (x0:A word)`))
      (ASSUME `get_real_addr c st ptr_w = SOME (x:A word)`)) THEN
    REWRITE_TAC[option_INJ];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`ptr_w:A word`; `x:A word`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_ASSOC]) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> mp4_is_app "memory_rel" (concl th) &&
    can (find_term (fun t -> t = `EL index (vals:data_v list)`)) (concl th))) THEN
  MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM] THEN MESON_TAC[]);;

(* HOL4 line 10858 *)
let copy_list_def = cake_def_wf
  `measure (\p:data_to_word_config#(store_name,A word_loc)fmap#num#
               (A word_loc#A word_loc#A word#(A word->A word_loc)#(A word->bool)).
              FST (SND (SND p)))`
  TERM_TAC
  `copy_list c' st k (a,x,b:A word,m:A word -> A word_loc,dm) =
     let c = (b IN dm) in
     let m = (b =+ x) m in
     let b = word_add b bytes_in_word in
     if k = 0 then (if c then SOME (b,m) else NONE) else
       match a with
         wl_Loc _ _ -> NONE
       | wl_Word a ->
           match get_real_addr c' st a with
             NONE -> NONE
           | SOME a ->
               let c = (c /\ word_add a (word_mul (word 2) bytes_in_word) IN dm /\
                        word_add a bytes_in_word IN dm) in
               let x = m (word_add a bytes_in_word) in
               let a = m (word_add a (word_mul (word 2) bytes_in_word)) in
               if c then copy_list c' st (k - 1) (a,x,b,m,dm) else NONE`;;

let MP4AUX_data_v_to_list_CONS = prove
 (`!v h t. data_v_to_list v = SOME (CONS h t) <=>
           ?ts h2. v = data_Block ts cons_tag [h; h2] /\ data_v_to_list h2 = SOME t`,
  MATCH_MP_TAC data_v_to_list_ind THEN
  REWRITE_TAC[data_v_to_list_def; distinctness "data_v"; injectivity "data_v";
              option_DISTINCT; CONS_11; NOT_CONS_NIL; GSYM NOT_CONS_NIL] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; NOT_CONS_NIL];
    DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[option_DISTINCT; option_case_eq; option_INJ; CONS_11] THEN
    MESON_TAC[]]);;

(* the two fields of a cons cell, read for copy_list *)
let MP4AUX_memory_rel_El_pair = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm ts' tag h h2 w vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Block ts' tag [h; h2],wl_Word w) vars) /\
     good_dimindex (:A) ==>
     ?ra. get_real_addr c st w = SOME ra /\
          word_add ra bytes_in_word IN dm /\
          word_add ra (word_mul (word 2) bytes_in_word) IN dm /\
          memory_rel c be ts refs sp st m dm
            (CONS (h2,m (word_add ra (word_mul (word 2) bytes_in_word)))
              (CONS (h,m (word_add ra bytes_in_word)) vars))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                 `dm:A word -> bool`; `ts':num`; `tag:num`; `[h:data_v; h2]`;
                 `wl_Word (w:A word)`; `vars:(data_v#A word_loc)list`; `0`]
                memory_rel_El_any) THEN
  ASM_REWRITE_TAC[LENGTH; ARITH; EL; HD; injectivity "word_loc"] THEN
  REWRITE_TAC[UNWIND_THM1; UNWIND_THM2; WORD_RULE `word_add (word_add x b) (word_mul b (word 0)) =
                                      word_add x b:A word`] THEN
  DISCH_THEN(X_CHOOSE_THEN `pw:A word` (X_CHOOSE_THEN `ra:A word` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `w:A word = pw`)) THEN
  EXISTS_TAC `ra:A word` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_swap o
    check (fun th -> mp4_is_app "memory_rel" (concl th) &&
      fst(dest_pair(lhand(rand(concl th)))) = `h:data_v`)) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                 `dm:A word -> bool`; `ts':num`; `tag:num`; `[h:data_v; h2]`;
                 `wl_Word (w:A word)`;
                 `CONS (h:data_v,(m:A word -> A word_loc) (word_add ra bytes_in_word)) vars`; `1`]
                memory_rel_El_any) THEN
  ASM_REWRITE_TAC[LENGTH; ARITH; injectivity "word_loc"] THEN
  REWRITE_TAC[UNWIND_THM1; UNWIND_THM2; ONE; EL; TL; HD] THEN
  REWRITE_TAC[GSYM ONE; WORD_RULE `word_add (word_add x b) (word_mul b (word 1)) =
                                   word_add x (word_mul (word 2) b):A word`] THEN
  DISCH_THEN(X_CHOOSE_THEN `pw2:A word` (X_CHOOSE_THEN `ra':A word` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `w:A word = pw2`)) THEN
  SUBGOAL_THEN `ra' = ra:A word` SUBST_ALL_TAC THENL
   [MP_TAC(TRANS (SYM (ASSUME `get_real_addr c st w = SOME (ra':A word)`))
      (ASSUME `get_real_addr c st w = SOME (ra:A word)`)) THEN
    REWRITE_TAC[option_INJ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> mp4_is_app "memory_rel" (concl th) &&
    fst(dest_pair(lhand(rand(concl th)))) = `h2:data_v`)) THEN
  MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM] THEN MESON_TAC[]);;


(* copy_list_thm for a copy starting at word k of the free space *)
let MP4AUX_copy_list_gen = prove
 (`!vs c be ts refs sp st dm v k b (m:A word -> A word_loc) vars a x frame.
     memory_rel c be ts refs sp st m dm (CONS (v,a) vars) /\
     data_v_to_list v = SOME vs /\
     (word_list_exists (word_add b (word_mul bytes_in_word (word k))) (SUC (LENGTH vs))
        STAR frame) (fun2set (m,dm)) /\
     good_dimindex (:A) /\
     FLOOKUP st NextFree = SOME (wl_Word b) /\
     k + LENGTH vs < sp ==>
     ?xs m1.
       copy_list c st (LENGTH vs) (a,x,word_add b (word_mul bytes_in_word (word k)),m,dm) =
         SOME (word_add b (word_mul bytes_in_word (word (k + LENGTH vs + 1))),m1) /\
       LENGTH vs = LENGTH xs /\
       memory_rel c be ts refs sp st m1 dm (APPEND (ZIP vs xs) vars) /\
       (misc_word_list (word_add b (word_mul bytes_in_word (word k))) (CONS x xs) STAR frame)
         (fun2set (m1,dm))`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH; ADD_CLAUSES] THEN STRIP_TAC THEN
   EXISTS_TAC `[]:(A word_loc)list` THEN
   ONCE_REWRITE_TAC[copy_list_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   ABBREV_TAC `bk = word_add b (word_mul bytes_in_word (word k)):A word` THEN
   MP4_X_ASM "STAR" (MP_TAC o REWRITE_RULE[data_to_word_memoryProof_word_list_exists_thm;
     SEP_CLAUSES; SEP_EXISTS_THM]) THEN
   DISCH_THEN(X_CHOOSE_TAC `w0:A word_loc`) THEN
   FIRST_ASSUM(ASSUME_TAC o CONJUNCT2 o MATCH_MP read_fun2set o MP4AUX_STAR_FOCUS mp4_is_one) THEN
   ASM_REWRITE_TAC[option_INJ; PAIR_EQ; LENGTH; ZIP; APPEND; misc_word_list_def; SEP_CLAUSES] THEN
    EXISTS_TAC `(bk =+ x) (m:A word -> A word_loc)` THEN REWRITE_TAC[] THEN
   CONJ_TAC THENL
    [EXPAND_TAC "bk" THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
   CONJ_TAC THENL
    [MP4_ASM "memory_rel" (MP_TAC o SPEC `x:A word_loc` o MATCH_MP memory_rel_write o MATCH_MP memory_rel_tail) THEN
     DISCH_THEN(X_CHOOSE_THEN `free:A word` (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPEC `k:num`))) THEN
     SUBGOAL_THEN `free = b:A word` SUBST_ALL_TAC THENL
      [MP_TAC(TRANS (SYM (ASSUME `FLOOKUP st NextFree = SOME (wl_Word (free:A word))`))
         (ASSUME `FLOOKUP st NextFree = SOME (wl_Word (b:A word))`)) THEN
       REWRITE_TAC[option_INJ; injectivity "word_loc"]; ALL_TAC] THEN
     ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN SIMP_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(fun th -> if mp4_is_fun2set_asm (concl th) then
     MP_TAC (MP4AUX_SEP_WRITE `bk:A word` `x:A word_loc` th) else failwith "") THEN
   DISCH_TAC THEN MP4AUX_SEP_AC_TAC;
    REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH] THEN STRIP_TAC THEN
   MP4_X_EQ_ASM "data_v_to_list" (X_CHOOSE_THEN `ts0:num` (X_CHOOSE_THEN `h2:data_v`
     STRIP_ASSUME_TAC) o REWRITE_RULE[MP4AUX_data_v_to_list_CONS]) THEN
   RVEQ_TAC THEN
   MP4_ASM "memory_rel" (MP_TAC o MATCH_MP memory_rel_Block_IMP o
     C CONJ (ASSUME `good_dimindex(:A)`)) THEN
   REWRITE_TAC[NOT_CONS_NIL] THEN
   DISCH_THEN(X_CHOOSE_THEN `w:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
   DISCH_THEN(K ALL_TAC) THEN
   ABBREV_TAC `bk = word_add b (word_mul bytes_in_word (word k)):A word` THEN
   MP4_ASM "memory_rel" (MP_TAC o SPEC `x:A word_loc` o MATCH_MP memory_rel_write) THEN
   DISCH_THEN(X_CHOOSE_THEN `free:A word` (CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o SPEC `k:num`))) THEN
   SUBGOAL_THEN `free = b:A word` SUBST_ALL_TAC THENL
    [MP_TAC(TRANS (SYM (ASSUME `FLOOKUP st NextFree = SOME (wl_Word (free:A word))`))
       (ASSUME `FLOOKUP st NextFree = SOME (wl_Word (b:A word))`)) THEN
     REWRITE_TAC[option_INJ; injectivity "word_loc"]; ALL_TAC] THEN
   ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
   ABBREV_TAC `m0 = (bk =+ x) (m:A word -> A word_loc)` THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP MP4AUX_memory_rel_El_pair o
     C CONJ (ASSUME `good_dimindex(:A)`) o
     check (fun th -> mp4_is_app "memory_rel" (concl th) &&
       can (find_term (fun t -> t = `m0:A word -> A word_loc`)) (concl th))) THEN
   DISCH_THEN(X_CHOOSE_THEN `ra:A word` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`; `sp:num`;
      `st:(store_name,A word_loc)fmap`; `dm:A word -> bool`; `h2:data_v`; `k + 1`;
      `b:A word`; `m0:A word -> A word_loc`;
      `CONS (h:data_v,(m0:A word -> A word_loc) (word_add ra bytes_in_word)) vars`;
      `(m0:A word -> A word_loc) (word_add ra (word_mul (word 2) bytes_in_word))`;
      `(m0:A word -> A word_loc) (word_add ra bytes_in_word)`;
      `set_sep_one (bk:A word,x:A word_loc) STAR frame`] o
     check (is_forall o concl)) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `word_add b (word_mul bytes_in_word (word (k + 1))) =
                 word_add bk bytes_in_word:A word` SUBST1_TAC THENL
    [EXPAND_TAC "bk" THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
     MP4_X_ASM "STAR" (MP_TAC o REWRITE_RULE[SEP_CLAUSES; SEP_EXISTS_THM] o
       ONCE_REWRITE_RULE[data_to_word_memoryProof_word_list_exists_thm] o check (fun th -> can (find_term (fun t ->
         t = `word_list_exists:A word->num->((A word#A word_loc)->bool)->bool`)) (concl th))) THEN
     DISCH_THEN(X_CHOOSE_THEN `w0:A word_loc` (fun th ->
       MP_TAC (MP4AUX_SEP_WRITE `bk:A word` `x:A word_loc` th))) THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP4AUX_SEP_AC_TAC;
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `xs:(A word_loc)list` (X_CHOOSE_THEN `m1:A word -> A word_loc`
     STRIP_ASSUME_TAC)) THEN
   MAP_EVERY EXISTS_TAC [`CONS ((m0:A word -> A word_loc) (word_add ra bytes_in_word)) xs`;
                         `m1:A word -> A word_loc`] THEN
   ASM_REWRITE_TAC[LENGTH; ZIP; APPEND] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[copy_list_def] THEN
      ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; NOT_SUC; SUC_SUB1] THEN CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[option_INJ; PAIR_EQ] THEN
      FIRST_X_ASSUM(fun th -> if concl th = `LENGTH (t:data_v list) = LENGTH (xs:(A word_loc)list)`
        then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th else failwith "") THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[option_INJ; PAIR_EQ] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      ARITH_TAC;
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> mp4_is_app "memory_rel" (concl th) &&
          can (find_term (fun t -> t = `m1:A word -> A word_loc`)) (concl th))) THEN
        MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[];
        ONCE_REWRITE_TAC[misc_word_list_def] THEN MP4AUX_SEP_AC_TAC]]]);;

(* HOL4 line 10872 (the HOL4 theorem is the k = 0 instance of the proved   *)
(* statement, simplified; its vacuous ?w is left out)                       *)
let copy_list_thm = prove
 (`!c be ts refs sp st dm v vs b (m:A word -> A word_loc) vars a x frame.
     memory_rel c be ts refs sp st m dm (CONS (v,a) vars) /\
     data_v_to_list v = SOME vs /\
     (word_list_exists b (SUC (LENGTH vs)) STAR frame) (fun2set (m,dm)) /\
     good_dimindex (:A) /\
     FLOOKUP st NextFree = SOME (wl_Word b) /\
     LENGTH vs < sp ==>
     ?xs m1.
       copy_list c st (LENGTH vs) (a,x,b,m,dm) =
         SOME (word_add b (word_mul bytes_in_word (word (LENGTH vs + 1))),m1) /\
       LENGTH vs = LENGTH xs /\
       memory_rel c be ts refs sp st m1 dm (APPEND (ZIP vs xs) vars) /\
       (misc_word_list b (CONS x xs) STAR frame) (fun2set (m1,dm))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`vs:data_v list`; `c:data_to_word_config`; `be:bool`; `ts:num`;
                 `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,A word_loc)fmap`;
                 `dm:A word -> bool`; `v:data_v`; `0`; `b:A word`; `m:A word -> A word_loc`;
                 `vars:(data_v#A word_loc)list`; `a:A word_loc`; `x:A word_loc`;
                 `frame:((A word#A word_loc)->bool)->bool`] MP4AUX_copy_list_gen) THEN
  REWRITE_TAC[WORD_RULE `word_add b (word_mul c (word 0)) = b:A word`; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[]);;

let MP4AUX_memory_rel_NextFree = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars.
     memory_rel c be ts refs sp st m dm vars ==>
     ?f:A word. FLOOKUP st NextFree = SOME (wl_Word f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MP4AUX_memory_rel_unfold; heap_in_memory_store_def] THEN
  STRIP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 10967 (the unused bound variable xs of HOL4 is left out) *)
let memory_rel_FromList = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm v vs a vars tag hd.
     data_v_to_list v = SOME vs /\ ~(vs = []) /\
     memory_rel c be ts refs sp st m dm (CONS (v,a) vars) /\
     encode_header c (4 * tag) (LENGTH vs) = SOME hd /\ LENGTH vs < sp /\
     good_dimindex (:A) ==>
     ?free curr m1 f1.
       FLOOKUP st NextFree = SOME (wl_Word free) /\
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       copy_list c st (LENGTH vs) (a,wl_Word hd,free,m,dm) = SOME (f1,m1) /\
       memory_rel c be (ts + 1) refs (sp - (LENGTH vs + 1))
         (st |+ (NextFree,wl_Word f1)) m1 dm
         (CONS (data_Block ts tag vs,
                make_cons_ptr c (word_sub free curr) tag (LENGTH vs)) vars)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `f:A word` o MATCH_MP MP4AUX_memory_rel_NextFree) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`;
                 `dm:A word -> bool`; `CONS (v:data_v,a:A word_loc) vars`;
                 `SUC (LENGTH (vs:data_v list))`; `f:A word`]
                memory_rel_IMP_word_list_exists) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `dm:A word -> bool`; `v:data_v`;
                 `vs:data_v list`; `f:A word`; `m:A word -> A word_loc`;
                 `vars:(data_v#A word_loc)list`; `a:A word_loc`; `wl_Word (hd:A word)`;
                 `SEP_T:((A word#A word_loc)->bool)->bool`] copy_list_thm) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:(A word_loc)list` (X_CHOOSE_THEN `m1:A word -> A word_loc`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m1:A word -> A word_loc`;
                 `dm:A word -> bool`; `vs:data_v list`; `xs:(A word_loc)list`;
                 `vars:(data_v#A word_loc)list`; `tag:num`; `hd:A word`]
                memory_rel_Cons_alt) THEN
  FIRST_ASSUM(fun th -> if concl th = `LENGTH (vs:data_v list) = LENGTH (xs:(A word_loc)list)`
    then RULE_ASSUM_TAC(fun a -> if concl a = concl th then a else REWRITE_RULE[th] a)
    else failwith "") THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `free:A word` (X_CHOOSE_THEN `curr:A word` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    concl th = `SOME (wl_Word (f:A word)) = SOME (wl_Word free)`)) THEN
  REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  MAP_EVERY EXISTS_TAC [`f:A word`; `curr:A word`; `m1:A word -> A word_loc`;
    `word_add f (word_mul bytes_in_word (word (LENGTH (xs:(A word_loc)list) + 1))):A word`] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;
