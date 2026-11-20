(* ========================================================================= *)
(* data_to_word_memoryProof_p5: part 5 of 7 (HOL4 lines 10992-13773) of the  *)
(* port of HOL4 compiler/backend/proofs/data_to_word_memoryProofScript.sml   *)
(* (CakeML v3479).  Part of the correctness proof for data_to_word.          *)
(* The parts _p1 ... _p7 are loaded one after the other (each needs the     *)
(* previous one); data_to_word_memoryProof.ml needs the last.                *)
(* MP5AUX_ names are local helpers of this part.                            *)
(* ========================================================================= *)

needs "compiler/backend/proofs/data_to_word_memoryProof_p4.ml";;

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Local helpers (MP5AUX_): bit-level reasoning on words of symbolic width.  *)
(* ------------------------------------------------------------------------- *)

let MP5AUX_BIT_WORD = prove
 (`!i n. bit i (word n:N word) <=> i < dimindex(:N) /\ numbit i n`,
  REWRITE_TAC[BIT_WORD; numbit]);;

(* numbit i n for a numeral n and a non-numeral i: the list of positions     *)

let MP5AUX_NUMBIT_CONV tm =
  match tm with
    Comb(Comb(Const("numbit",_),i),n) when is_numeral n && not (is_numeral i) ->
      let nv = dest_numeral n in
      let rec len m k = if m =/ num 0 then k else len (quo_num m (num 2)) (k + 1) in
      let k = len nv 0 in
      let rec setbits j acc =
        if j >= k then rev acc else
        let b = mod_num (quo_num nv (power_num (num 2) (num j))) (num 2) =/ num 1 in
        setbits (j + 1) (if b then j :: acc else acc) in
      let js = setbits 0 [] in
      let rhs = if js = [] then `F` else
        list_mk_disj (map (fun j -> mk_eq(i,mk_small_numeral j)) js) in
      let goal = mk_eq(tm,rhs) in
      let kt = mk_small_numeral k in
      if k = 0 then prove(goal,REWRITE_TAC[numbit; DIV_0; ODD]) else
      prove(goal,
        ASM_CASES_TAC (mk_comb(mk_comb(`(<):num->num->bool`,i),kt)) THENL
         [FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP (ARITH_RULE
            (mk_imp(mk_comb(mk_comb(`(<):num->num->bool`,`x:num`),kt),
               if k = 0 then `F` else
               list_mk_disj (map (fun j -> mk_eq(`x:num`,mk_small_numeral j))
                                 (0--(k-1)))))) th)) THEN
          DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
          REWRITE_TAC[numbit] THEN CONV_TAC NUM_REDUCE_CONV;
          MATCH_MP_TAC(TAUT `~a /\ ~b ==> (a <=> b)`) THEN CONJ_TAC THENL
           [MATCH_MP_TAC NOT_BIT_GT_TWOEXP THEN
            MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC (mk_comb(`(EXP) 2`,kt)) THEN
            CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV;
              REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
            ASM_ARITH_TAC]])
  | Comb(Comb(Const("numbit",_),i),n) when is_numeral n && is_numeral i ->
      (REWRITE_CONV[numbit] THENC NUM_REDUCE_CONV) tm
  | _ -> failwith "MP5AUX_NUMBIT_CONV";;

let MP5AUX_BIT_RULES =
  [BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_XOR; BIT_WORD_SHL; BIT_WORD_USHR;
   BIT_WORD_NOT; BIT_WORD_0; BIT_WORD_SLICE; BIT_WORD_BITS; MP5AUX_BIT_WORD];;

(* turn a word equation into bits: i < dimindex(:N) ==> (bit i v <=> ..)   *)
let MP5AUX_WORD_BITS_TAC =
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC MP5AUX_BIT_RULES THEN CONV_TAC(DEPTH_CONV MP5AUX_NUMBIT_CONV);;


let MP5AUX_BIT_ATOMS tm =
  setify (find_terms (fun t ->
    match strip_comb t with
      Const(("numbit"|"bit"),_),[_;_] -> true
    | _ -> false) tm);;

(* case split on every bit/numbit atom of the goal *)
let MP5AUX_SPLIT_ATOMS_TAC (asl,w as g) =
  let atoms = MP5AUX_BIT_ATOMS w in
  (EVERY (map (fun a -> ASM_CASES_TAC a THEN ASM_REWRITE_TAC[]) atoms)) g;;

(* move the assumptions into the goal, split the atoms, then arithmetic *)
let MP5AUX_BITS_ARITH_TAC =
  REPEAT(POP_ASSUM MP_TAC) THEN MP5AUX_SPLIT_ATOMS_TAC THEN ARITH_TAC;;

let MP5AUX_NUMBIT_MUL_ADD = prove
 (`!k m r i. r < 2 EXP k ==>
     (numbit i (2 EXP k * m + r) <=> if i < k then numbit i r else numbit (i - k) m)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [MP_TAC(SPECL [`i:num`; `k:num`; `2 EXP k * m + r`] NUMBIT_MOD_2EXP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
    MP_TAC(SPECL [`i - k:num`; `k:num`; `2 EXP k * m + r`] NUMBIT_DIV_2EXP) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(i < k) ==> k + i - k = i`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC]);;

(* x - a - b = x - (a + b) for numerals a b *)
let MP5AUX_SUB_SUB_CONV tm =
  match tm with
    Comb(Comb(Const("-",_),Comb(Comb(Const("-",_),x),a)),b)
      when is_numeral a && is_numeral b ->
      let c = mk_numeral(dest_numeral a +/ dest_numeral b) in
      ARITH_RULE(mk_eq(tm,mk_binop `(-):num->num->num` x c))
  | _ -> failwith "MP5AUX_SUB_SUB_CONV";;

(* disjoint bit fields: or is plus *)
let MP5AUX_WORD_OR_DISJ = prove
 (`!a b k. b < 2 EXP k ==>
     word_or (word (2 EXP k * a)) (word b):N word = word (2 EXP k * a + b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC WORD_ADD_OR THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; MP5AUX_BIT_WORD; BIT_WORD_0] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  REWRITE_TAC[NUMBIT_MUL_2EXP] THEN ASM_CASES_TAC `k <= i` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~b ==> ~(a /\ b)`) THEN MATCH_MP_TAC NOT_BIT_GT_TWOEXP THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `2 EXP k` THEN ASM_REWRITE_TAC[WORDSAUX_EXP2_LE]);;

(* the header word as a number *)
let MP5AUX_make_header_word = prove
 (`!c t l.
     4 * t + 3 < 2 EXP (dimindex(:A) - data_to_word_config_len_size c) ==>
     make_header c (word t:A word) l =
     word (2 EXP (dimindex(:A) - data_to_word_config_len_size c) * l + (4 * t + 3))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[make_header_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_SHL_WORD] THEN
  SUBGOAL_THEN `word_or (word (2 EXP 2 * t)) (word 3):A word = word (4 * t + 3)`
    SUBST1_TAC THENL
   [SIMP_TAC[MP5AUX_WORD_OR_DISJ; ARITH_RULE `3 < 2 EXP 2`] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 2 * t = 4 * t`];
    MATCH_MP_TAC MP5AUX_WORD_OR_DISJ THEN ASM_REWRITE_TAC[]]);;

let MP5AUX_LT_MUL_ADD = prove
 (`!k x n b. b < 2 EXP k /\ x < n ==> 2 EXP k * x + b < 2 EXP k * n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `2 EXP k * (x + 1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC;
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC]);;

let MP5AUX_DIVMOD_EQ = prove
 (`!k a b c d. b < 2 EXP k /\ d < 2 EXP k ==>
     (2 EXP k * a + b = 2 EXP k * c + d <=> a = c /\ b = d)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `b:num = d` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x MOD 2 EXP k`) THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[EQ_ADD_RCANCEL]) THEN
    REWRITE_TAC[EQ_MULT_LCANCEL; EXP_EQ_0] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Separation logic: AC rearrangement of STAR, reading memory (HOL4's        *)
(* SEP_R_TAC), splitting cond atoms.                                         *)
(* ------------------------------------------------------------------------- *)

let rec mp5aux_star_atoms tm =
  match tm with
    Comb(Comb(Const("STAR",_),p),q) -> mp5aux_star_atoms p @ mp5aux_star_atoms q
  | _ -> [tm];;

(* tm = atom STAR rest (rest: the other atoms, right-nested) *)
let MP5AUX_STAR_FRONT_CONV atom tm =
  let atoms = mp5aux_star_atoms tm in
  if not (mem atom atoms) then failwith "MP5AUX_STAR_FRONT_CONV" else
  let rec remove1 l = match l with
      [] -> [] | h::t -> if h = atom then t else h :: remove1 t in
  let rest = remove1 atoms in
  if rest = [] then REFL tm else
  let star = match tm with
      Comb(Comb(s,_),_) -> s | _ -> failwith "MP5AUX_STAR_FRONT_CONV" in
  let restt = end_itlist (fun a b -> mk_comb(mk_comb(star,a),b)) rest in
  let rhs = mk_comb(mk_comb(star,atom),restt) in
  if rhs = tm then REFL tm else AC LSORTAUX_STAR_AC (mk_eq(tm,rhs));;

(* from |- P s with P a STAR term: the facts of its set_sep_one (a,x) atoms *)
let MP5AUX_SEP_READ th =
  let p,s = dest_comb (concl th) in
  let ones = filter (fun a -> match a with
        Comb(Const("set_sep_one",_),_) -> true | _ -> false) (mp5aux_star_atoms p) in
  map (fun one ->
    let eq = MP5AUX_STAR_FRONT_CONV one p in
    let th1 = EQ_MP (AP_THM eq s) th in
    if is_comb (rator (concl th1)) &&
       (match rator (concl th1) with Comb(Comb(Const("STAR",_),_),_) -> true | _ -> false)
    then MATCH_MP read_fun2set th1
    else MATCH_MP one_fun2set_IMP th1) ones;;

(* SEP_R_TAC: add the facts m a = x /\ a IN dm of every STAR assumption *)
let MP5AUX_SEP_R_TAC : tactic = fun (asl,w as g) ->
  let facts = flat (mapfilter (fun (_,th) ->
     let c = concl th in
     if is_comb c && (match rator c with Comb(Comb(Const("STAR",_),_),_) -> true
                                          | _ -> false)
     then MP5AUX_SEP_READ th else failwith "") asl) in
  MAP_EVERY (fun th -> STRIP_ASSUME_TAC th) facts g;;

(* split the cond atoms of a STAR assumption: |- P s gives the conditions *)
(* and the assertion without them                                          *)
let rec MP5AUX_SEP_COND_RULE th =
  let p,s = dest_comb (concl th) in
  let conds = filter (fun a -> match a with
        Comb(Const("cond",_),_) -> true | _ -> false) (mp5aux_star_atoms p) in
  match conds with
    [] -> [th]
  | cd::_ ->
      let eq = MP5AUX_STAR_FRONT_CONV cd p in
      let th1 = EQ_MP (AP_THM eq s) th in
      if p = cd then [REWRITE_RULE[cond_def] th1] else
      let th2 = CONV_RULE (REWR_CONV (CONJUNCT1 (SPEC_ALL cond_STAR))) th1 in
      CONJUNCT1 th2 :: MP5AUX_SEP_COND_RULE (CONJUNCT2 th2);;

let MP5AUX_SEP_COND_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_comb c && (match rator c with Comb(Comb(Const("STAR",_),_),_) -> true
                                         | _ -> false) &&
       exists (fun a -> match a with Comb(Const("cond",_),_) -> true | _ -> false)
              (mp5aux_star_atoms (rator c))
    then MAP_EVERY STRIP_ASSUME_TAC (MP5AUX_SEP_COND_RULE th)
    else failwith ""));;

(* |- P s  gives  |- (atom STAR rest) s *)
let MP5AUX_SEP_FRONT_RULE atom th =
  let p,s = dest_comb (concl th) in
  EQ_MP (AP_THM (MP5AUX_STAR_FRONT_CONV atom p) s) th;;

(* goal ?ff. (atom STAR ff) s /\ ...: take ff from the STAR assumption that *)
(* contains atom                                                            *)
let MP5AUX_SEP_FRAME_EXISTS_TAC : tactic = fun (asl,w as g) ->
  let ff,body = dest_exists w in
  let target = find_term (fun t -> match t with
      Comb(Comb(Comb(Const("STAR",_),a),f),_) when f = ff -> true
    | _ -> false) body in
  let atom = rand (rator (rator target)) in
  let s = rand target in
  let th = find (fun th -> let c = concl th in
      is_comb c && rand c = s &&
      (match rator c with Comb(Comb(Const("STAR",_),_),_) -> true | _ -> false) &&
      mem atom (mp5aux_star_atoms (rator c))) (map snd asl) in
  let th1 = MP5AUX_SEP_FRONT_RULE atom th in
  let rest = rand (rator (concl th1)) in
  (EXISTS_TAC rest THEN ASSUME_TAC th1) g;;

(* the low bits of a header word *)
let MP5AUX_make_header_bit = prove
 (`!c (t:A word) n i.
     i < dimindex(:A) - data_to_word_config_len_size c ==>
     (bit i (make_header c t n) <=> if i < 2 then T else bit (i - 2) t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[make_header_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC MP5AUX_BIT_RULES THEN CONV_TAC(DEPTH_CONV MP5AUX_NUMBIT_CONV) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  BIT_ATOM_CASES_TAC `bit (i - 2) (t:A word)` THEN ASM_ARITH_TAC);;

let MP5AUX_heap_in_memory_store_IMP = prove
 (`!heap a sp sp1 gens c st (m:A word -> A word_loc) dm limit.
     heap_in_memory_store heap a sp sp1 gens c st m dm limit ==>
     data_to_word_config_len_size c + 7 < dimindex (:A) /\
     ~(data_to_word_config_len_size c = 0) /\
     shift_length c < dimindex (:A) /\
     heap_length heap <= dimword (:A) DIV (2 EXP shift_length c) /\
     (heap_length heap + 3) * (dimindex (:A) DIV 8) < dimword (:A) /\
     backend_common_word_shift (:A) <= shift_length c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_in_memory_store_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;


(* unfolding memory_rel for a value at the head of the stack *)
let MP5AUX_memory_rel_HD = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm x v vars.
     memory_rel c be ts refs sp st m dm (CONS (x,v) vars) ==>
     ?heap limit a sp' sp1 gens f tf h hs.
       heap_in_memory_store heap a sp' sp1 gens c st m dm limit /\
       v_inv c x refs (h,f,tf,heap) /\ word_addr c h = v /\
       abs_ml_inv c (CONS x (MAP FST vars)) refs
         (CONS h hs,heap,be,a,sp',sp1,gens) limit ts /\
       ALL2 (\v w. word_addr c v = w) hs (MAP SND vars) /\
       roots_ok (CONS h hs) heap /\ heap_ok heap limit /\
       gc_kind_inv c a sp' sp1 gens heap /\
       unused_space_inv a (sp' + sp1) heap /\
       INJ (FAPPLY f) (FDOM f) {a | isSomeDataElement (heap_lookup a heap)} /\
       FDOM f SUBSET (domain refs) /\
       INJ (FAPPLY tf) (FDOM tf) {a | isSomeDataElement (heap_lookup a heap)} /\
       FDOM tf SUBSET (all_ts refs (CONS x (MAP FST vars))) /\
       FDOM tf SUBSET {n | n < ts} /\ be_ok (data_to_word_config_be c) be /\
       blocks_unique ts (all_vs refs (CONS x (MAP FST vars))) /\
       ALL2 (\v x. v_inv c v refs (x,f,tf,heap)) (MAP FST vars) hs /\
       (!n. reachable_refs (CONS x (MAP FST vars)) refs n /\ n IN FDOM f ==>
            bc_ref_inv c n refs (f,tf,heap,be)) /\
       (limit + 3) * (dimindex (:A) DIV 8) + 1 < dimword (:A) /\ sp <= sp'`,
  let var_named s t = is_var t && fst(dest_var t) = s in
  REPEAT GEN_TAC THEN REWRITE_TAC[memory_rel_def; word_ml_inv_def] THEN
  REWRITE_TAC[MAP; LIST_REL_CONS2] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> var_named "hs" (lhs(concl th)))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [abs_ml_inv_def]) THEN
  REWRITE_TAC[bc_stack_ref_inv_def; LIST_REL_CONS1; CONS_11] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    let l,r = dest_eq(concl th) in var_named "h''" r || var_named "t''" r))) THEN
  MAP_EVERY EXISTS_TAC [`heap:(((A)word_loc,data_to_word_memoryProof_tag#
                                ((A)word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp':num`; `sp1:num`; `gens:gen_state`;
    `f:(num,num)fmap`; `tf:(num,num)fmap`; `h':((A)word_loc)heap_address`;
    `t':(((A)word_loc)heap_address)list`] THEN
  ASM_REWRITE_TAC[]);;
let MP5AUX_heap_el_IMP = prove
 (`!heap a sp sp1 gens c st (m:A word -> A word_loc) dm limit n ys l tag qs.
     heap_in_memory_store heap a sp sp1 gens c st m dm limit /\
     heap_lookup n heap = SOME (DataElement ys l (tag,qs)) /\ good_dimindex (:A) ==>
     ?curr h ts cnd ff.
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       word_payload ys l tag qs c = (h,ts,cnd) /\ cnd /\
       (!w. get_real_simple_addr c st (get_addr c n w) =
              SOME (word_add curr (word_mul (word n) bytes_in_word)) /\
            get_real_addr c st (get_addr c n w) =
              SOME (word_add curr (word_mul (word n) bytes_in_word))) /\
       m (word_add curr (word_mul (word n) bytes_in_word)) = wl_Word h /\
       word_add curr (word_mul (word n) bytes_in_word) IN dm /\
       LENGTH ts < 2 EXP (dimindex (:A) - 4) /\ decode_length c h = word (LENGTH ts) /\
       (misc_word_list (word_add (word_add curr (word_mul (word n) bytes_in_word))
                                 bytes_in_word) ts STAR ff) (fun2set (m,dm))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [heap_in_memory_store_def]) THEN
  EXISTS_TAC `curr:A word` THEN
  SUBGOAL_THEN `!w:A word_loc. get_real_simple_addr c st (get_addr c n w) =
              SOME (word_add (curr:A word) (word_mul (word n) bytes_in_word)) /\
            get_real_addr c st (get_addr c n w) =
              SOME (word_add curr (word_mul (word n) bytes_in_word))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(ISPECL
     [`heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                        heap_element)list`;
    `c:data_to_word_config`; `n:num`;
    `DataElement ys l (tag,qs):(((A)word_loc,data_to_word_memoryProof_tag#
                                 ((A)word_loc)list)heap_element)`;
    `st:(store_name,(A)word_loc)fmap`; `curr:A word`; `w:A word_loc`]
    get_real_addr_get_addr) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `word_mul bytes_in_word (word n) = word_mul (word n) bytes_in_word:A word`
    ASSUME_TAC THENL [MATCH_ACCEPT_TAC WORD_MUL_SYM; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP heap_lookup_SPLIT) THEN
  DISCH_THEN(X_CHOOSE_THEN `ha:(((A)word_loc,data_to_word_memoryProof_tag#
                                 ((A)word_loc)list)heap_element)list`
    (X_CHOOSE_THEN `hb:(((A)word_loc,data_to_word_memoryProof_tag#
                         ((A)word_loc)list)heap_element)list`
     (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC))) THEN
  SUBGOAL_THEN `?h ts cnd. word_payload ys l tag qs c =
                  (h:A word,ts:((A)word_loc)list,cnd:bool)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`h:A word`; `ts:((A)word_loc)list`; `cnd:bool`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
    can (find_term ((=) `fun2set:(A word->A word_loc)#(A word->bool)->
                          A word#A word_loc->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[word_heap_APPEND; word_heap_def; word_el_def; pair_CASE;
                  misc_word_list_def] THEN
  DISCH_TAC THEN MP5AUX_SEP_COND_TAC THEN MP5AUX_SEP_R_TAC THEN
  MP5AUX_SEP_FRAME_EXISTS_TAC THEN ASM_REWRITE_TAC[]);;

(* MP_TAC (and remove) the first assumption with head constant s *)
let MP5AUX_UNDISCH_HEAD s : tactic =
  FIRST_X_ASSUM(fun th ->
    if (try fst(dest_const(fst(strip_comb(concl th)))) = s with Failure _ -> false)
    then MP_TAC th else failwith "MP5AUX_UNDISCH_HEAD");;

(* a RefPtr at the head of the stack is reachable *)
let MP5AUX_reachable_refs_HD = prove
 (`!bl p xs refs. reachable_refs (CONS (data_RefPtr bl p) xs) refs p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[reachable_refs_def] THEN
  MAP_EVERY EXISTS_TAC [`data_RefPtr bl p`; `p:num`] THEN
  REWRITE_TAC[MEM; get_refs_def; RTC_REFL]);;

let mp5aux_head_is s tm =
  try fst(dest_const(fst(strip_comb tm))) = s with Failure _ -> false;;

(* MP_TAC MP5AUX_heap_el_IMP for every heap_lookup _ _ = SOME (DataElement ..) *)
(* assumption, with the heap_in_memory_store and good_dimindex assumptions    *)
let MP5AUX_HEAP_EL_TAC : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  let hims = find (fun th -> mp5aux_head_is "heap_in_memory_store" (concl th)) ths in
  let gd = find (fun th -> mp5aux_head_is "good_dimindex" (concl th)) ths in
  let hls = filter (fun th -> try
      let l,r = dest_eq(concl th) in
      mp5aux_head_is "heap_lookup" l &&
      (match r with Comb(Const("SOME",_),e) -> mp5aux_head_is "DataElement" e
                  | _ -> false)
    with Failure _ -> false) ths in
  if hls = [] then failwith "MP5AUX_HEAP_EL_TAC" else
  MAP_EVERY (fun hl -> MP_TAC (MATCH_MP MP5AUX_heap_el_IMP (CONJ hims (CONJ hl gd))))
    hls g;;

(* substitute the variable named s using an assumption s = t or t = s *)
let MP5AUX_SUBST_VAR_TAC s : tactic =
  FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if is_var l && fst(dest_var l) = s && not (vfree_in l r) then SUBST_ALL_TAC th
    else if is_var r && fst(dest_var r) = s && not (vfree_in r l) then SUBST_ALL_TAC (SYM th)
    else failwith "MP5AUX_SUBST_VAR_TAC");;

(* ------------------------------------------------------------------------- *)
(* Bytes of a word: byte addresses 0 .. dimindex(:A) DIV 8 - 1.             *)
(* ------------------------------------------------------------------------- *)

let MP5AUX_good_dimindex_DIV8 = prove
 (`good_dimindex(:A) ==>
     (dimindex(:A) DIV 8 = 4 \/ dimindex(:A) DIV 8 = 8) /\
     dimindex(:A) DIV 8 < dimword(:A) /\ 8 <= dimindex(:A)`,
  REWRITE_TAC[good_dimindex_def; dimword_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let MP5AUX_good_dimindex_DIV8_LT = prove
 (`good_dimindex(:A) ==> dimindex(:A) DIV 8 < dimword(:A) /\ 8 <= dimindex(:A)`,
  MESON_TAC[MP5AUX_good_dimindex_DIV8]);;

let MP5AUX_byte_align_small = prove
 (`!x. good_dimindex(:A) /\ x < dimindex(:A) DIV 8 ==>
       byte_align (word x:A word) = word 0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_good_dimindex_DIV8) THEN
  (SUBGOAL_THEN `val(word x:A word) = x` ASSUME_TAC THENL
    [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[GSYM dimword_def] THEN ASM_ARITH_TAC;
     ALL_TAC]) THEN
  ASM_REWRITE_TAC[byte_align_def; align_w2n] THEN
  CONV_TAC(ONCE_DEPTH_CONV LOG2_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  AP_TERM_TAC THEN REWRITE_TAC[MULT_EQ_0] THEN DISJ1_TAC THEN
  MATCH_MP_TAC DIV_LT THEN ASM_ARITH_TAC);;

let MP5AUX_word_small_11 = prove
 (`!x y. good_dimindex(:A) /\ x < dimindex(:A) DIV 8 /\ y < dimindex(:A) DIV 8 ==>
         (word x:A word = word y <=> x = y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_good_dimindex_DIV8_LT) THEN
  REWRITE_TAC[n2w_11] THEN
  SUBGOAL_THEN `x < dimword(:A) /\ y < dimword(:A)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT]]);;

(* get_byte of a word built from bytes at addresses i0 .. i0 + n - 1 *)
let MP5AUX_get_byte_bytes_to_word = prove
 (`!n i0 zs (t:A word) j be.
     good_dimindex(:A) /\ i0 + n <= dimindex(:A) DIV 8 /\ j < n /\ j < LENGTH zs ==>
     get_byte (word (i0 + j)) (bytes_to_word n (word i0) zs t be) be = EL j zs`,
  INDUCT_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `zs:byte list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(j < 0)`] THEN
  STRUCT_CASES_TAC(SPEC `j:num` num_CASES) THEN STRIP_TAC THEN
  REWRITE_TAC[bytes_to_word_eq; word_add_n2w] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_good_dimindex_DIV8_LT) THENL
   [ASM_SIMP_TAC[ADD_CLAUSES; EL; HD; good_dimindex_get_byte_set_byte]; ALL_TAC] THEN
  REWRITE_TAC[EL; TL] THEN
  SUBGOAL_THEN `i0 + SUC n' < dimindex(:A) DIV 8 /\ i0 < dimindex(:A) DIV 8`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) get_byte_set_byte_diff (lhand w))) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MP5AUX_word_small_11; MP5AUX_byte_align_small] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ARITH_RULE `i0 + SUC m = (i0 + 1) + m`] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN ASM_ARITH_TAC);;

(* set_byte in a word built from bytes at addresses i0 .. i0 + n - 1 *)
let MP5AUX_set_byte_bytes_to_word = prove
 (`!n i0 zs (t:A word) j b be.
     good_dimindex(:A) /\ i0 + n <= dimindex(:A) DIV 8 /\ j < n /\ j < LENGTH zs ==>
     set_byte (word (i0 + j)) b (bytes_to_word n (word i0) zs t be) be =
     bytes_to_word n (word i0) (LUPDATE b j zs) t be`,
  INDUCT_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `zs:byte list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(j < 0)`] THEN
  STRUCT_CASES_TAC(SPEC `j:num` num_CASES) THEN STRIP_TAC THEN
  REWRITE_TAC[LUPDATE_def; bytes_to_word_eq; word_add_n2w; ADD_CLAUSES] THEN
  ONCE_REWRITE_TAC[set_byte_sort] THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `SUC (i0 + n') < dimindex(:A) DIV 8 /\ i0 < dimindex(:A) DIV 8 /\
                ~(SUC (i0 + n') = i0) /\ ~(i0 = SUC (i0 + n'))`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `SUC (i0 + m) = (i0 + 1) + m`] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MP5AUX_EXP_LOG2_BYTES = prove
 (`good_dimindex(:A) ==> 2 EXP LOG2 (dimindex(:A) DIV 8) = dimindex(:A) DIV 8`,
  REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV LOG2_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MP5AUX_MOD_POW_MOD = prove
 (`!x. x MOD 4294967296 MOD 4 = x MOD 4 /\
       x MOD 18446744073709551616 MOD 8 = x MOD 8`,
  REWRITE_TAC[ARITH_RULE `4294967296 = 4 * 1073741824`;
              ARITH_RULE `18446744073709551616 = 8 * 2305843009213693952`; MOD_MOD]);;

let MP5AUX_VAL_MOD_BYTES = prove
 (`!x. good_dimindex(:A) ==>
       val (word x:A word) MOD (dimindex(:A) DIV 8) = x MOD (dimindex(:A) DIV 8)`,
  REWRITE_TAC[good_dimindex_def; VAL_WORD] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MP5AUX_MOD_POW_MOD]);;

(* ------------------------------------------------------------------------- *)
(* Small numbers: Smallnum i is iword (&4 * i), the word iword i shifted.    *)
(* ------------------------------------------------------------------------- *)

let MP5AUX_Smallnum_shl = prove
 (`!i. Smallnum i:A word = word_shl (iword i) 2`,
  REWRITE_TAC[data_to_word_memoryProof_Smallnum_i2w; WORD_MUL_LSL; IWORD_INT_MUL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_IWORD]);;

let MP5AUX_NUMBIT_EXP2 = prove
 (`!i k. numbit i (2 EXP k) <=> i = k`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [ARITH_RULE `2 EXP k = 1 * 2 EXP k`] THEN
  REWRITE_TAC[NUMBIT_MUL_2EXP] THEN CONV_TAC(DEPTH_CONV MP5AUX_NUMBIT_CONV) THEN
  ARITH_TAC);;

(* masking with a power of two tests one bit *)
let MP5AUX_word_and_bit = prove
 (`!(x:A word) k. k < dimindex(:A) ==>
     (word_and x (word (2 EXP k)) = word 0 <=> ~bit k x) /\
     (word_and (word (2 EXP k)) x = word 0 <=> ~bit k x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ALL_TAC; MESON_TAC[WORD_AND_SYM]] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[BIT_WORD_AND; BIT_WORD_0; MP5AUX_BIT_WORD; MP5AUX_NUMBIT_EXP2] THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[];
    MESON_TAC[]]);;

let MP5AUX_word_and_1_8_16 = prove
 (`4 < dimindex(:A) ==> !x:A word.
     (word_and x (word 1) = word 0 <=> ~bit 0 x) /\
     (word_and x (word 8) = word 0 <=> ~bit 3 x) /\
     (word_and x (word 16) = word 0 <=> ~bit 4 x) /\
     (word_and (word 1) x = word 0 <=> ~bit 0 x) /\
     (word_and (word 8) x = word 0 <=> ~bit 3 x) /\
     (word_and (word 16) x = word 0 <=> ~bit 4 x)`,
  DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 = 2 EXP 0 /\ 8 = 2 EXP 3 /\ 16 = 2 EXP 4`] THEN
  ASM_SIMP_TAC[MP5AUX_word_and_bit; ARITH_RULE `4 < d ==> 0 < d /\ 3 < d`]);;

(* the low bits of the header of a bignum *)
let MP5AUX_bignum_header_bits = prove
 (`!c b n. data_to_word_config_len_size c + 7 < dimindex(:A) ==>
     let x = make_header c (word_or (word_shl (b2w b) 2) (word 3)) n:A word in
     bit 0 x /\ bit 1 x /\ bit 2 x /\ bit 3 x /\ (bit 4 x <=> b)`,
  REPEAT STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[MP5AUX_make_header_bit;
    ARITH_RULE `x + 7 < d ==> 0 < d - x /\ 1 < d - x /\ 2 < d - x /\ 3 < d - x /\ 4 < d - x`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC MP5AUX_BIT_RULES THEN
  CONV_TAC(DEPTH_CONV MP5AUX_NUMBIT_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[multiword_b2w_def; BITVAL_CLAUSES] THEN
  REWRITE_TAC[MP5AUX_BIT_WORD] THEN CONV_TAC(DEPTH_CONV MP5AUX_NUMBIT_CONV) THEN
  ASM_ARITH_TAC);;

(* apply ttac to the first STAR assumption P (fun2set ..) *)
let MP5AUX_STAR_ASSUM (ttac:thm_tactic) : tactic =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_comb c && (match rator c with Comb(Comb(Const("STAR",_),_),_) -> true
                                         | _ -> false)
    then ttac th else failwith "MP5AUX_STAR_ASSUM");;

let MP5AUX_ival_Smallnum = prove
 (`!i. good_dimindex(:A) /\ small_int (:A) i ==> ival (Smallnum i:A word) = &4 * i`,
  GEN_TAC THEN REWRITE_TAC[data_to_word_memoryProof_Smallnum_i2w; small_int_def] THEN
  STRIP_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
  UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
  STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[dimword_def]) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN ASM_ARITH_TAC);;

let MP5AUX_Smallnum_11 = prove
 (`!i1 i2. good_dimindex(:A) /\ small_int (:A) i1 /\ small_int (:A) i2 ==>
           (Smallnum i1 = (Smallnum i2:A word) <=> i1 = i2)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `ival:A word->int`) THEN
  ASM_SIMP_TAC[MP5AUX_ival_Smallnum] THEN INT_ARITH_TAC);;

let MP5AUX_word_msb_Smallnum = prove
 (`!i. good_dimindex(:A) /\ small_int (:A) i ==>
       (word_msb (Smallnum i:A word) <=> i < &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_msb_def; MSB_IVAL] THEN
  ASM_SIMP_TAC[MP5AUX_ival_Smallnum] THEN INT_ARITH_TAC);;

let MP5AUX_bit0_Smallnum = prove
 (`!i. ~bit 0 (Smallnum i:A word)`,
  REWRITE_TAC[MP5AUX_Smallnum_shl; BIT_WORD_SHL] THEN ARITH_TAC);;

(* unfolding memory_rel for two values at the head of the stack *)
let MP5AUX_memory_rel_HD2 = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm x1 v1 x2 v2 vars.
     memory_rel c be ts refs sp st m dm (CONS (x1,v1) (CONS (x2,v2) vars)) ==>
     ?heap limit a sp' sp1 gens f tf h1 h2 hs.
       heap_in_memory_store heap a sp' sp1 gens c st m dm limit /\
       v_inv c x1 refs (h1,f,tf,heap) /\ word_addr c h1 = v1 /\
       v_inv c x2 refs (h2,f,tf,heap) /\ word_addr c h2 = v2 /\
       abs_ml_inv c (CONS x1 (CONS x2 (MAP FST vars))) refs
         (CONS h1 (CONS h2 hs),heap,be,a,sp',sp1,gens) limit ts /\
       ALL2 (\v w. word_addr c v = w) hs (MAP SND vars) /\
       INJ (FAPPLY f) (FDOM f) {a | isSomeDataElement (heap_lookup a heap)} /\
       FDOM f SUBSET (domain refs) /\
       INJ (FAPPLY tf) (FDOM tf) {a | isSomeDataElement (heap_lookup a heap)} /\
       blocks_unique ts (all_vs refs (CONS x1 (CONS x2 (MAP FST vars)))) /\
       (!n. reachable_refs (CONS x1 (CONS x2 (MAP FST vars))) refs n /\ n IN FDOM f ==>
            bc_ref_inv c n refs (f,tf,heap,be))`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_memory_rel_HD) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; LIST_REL_CONS1; LIST_REL_CONS2]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th)) &&
    fst(dest_var(lhs(concl th))) = "hs")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONS_11]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th)) &&
    (fst(dest_var(lhs(concl th))) = "h''" || fst(dest_var(lhs(concl th))) = "t''")))) THEN
  MAP_EVERY EXISTS_TAC [`heap:(((A)word_loc,data_to_word_memoryProof_tag#
                                ((A)word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp':num`; `sp1:num`; `gens:gen_state`;
    `f:(num,num)fmap`; `tf:(num,num)fmap`; `h:((A)word_loc)heap_address`;
    `h':((A)word_loc)heap_address`; `t':(((A)word_loc)heap_address)list`] THEN
  ASM_REWRITE_TAC[]);;

let MP5AUX_get_addr_word0 = prove
 (`!c n. get_addr c n (wl_Word (word 0)):A word =
         word_or (word_shl (word n) (shift_length c)) (word 1)`,
  REWRITE_TAC[get_addr_def; get_lowerbits_def] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN REWRITE_TAC MP5AUX_BIT_RULES THEN MESON_TAC[]);;

(* a heap address of the stack times the pointer scaling fits in a word *)
let MP5AUX_FAPPLY_BOUND = prove
 (`!heap a sp sp1 gens c st (m:A word -> A word_loc) dm limit (f:(num,num)fmap) p.
     heap_in_memory_store heap a sp sp1 gens c st m dm limit /\
     INJ (FAPPLY f) (FDOM f) {a | isSomeDataElement (heap_lookup a heap)} /\
     p IN FDOM f ==>
     FAPPLY f p * 2 EXP shift_length c < dimword (:A) /\
     FAPPLY f p < heap_length heap`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_heap_in_memory_store_IMP) THEN
  SUBGOAL_THEN `FAPPLY (f:(num,num)fmap) p < heap_length (heap:(((A)word_loc,
     data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list)` ASSUME_TAC THENL
   [UNDISCH_TAC `INJ (FAPPLY (f:(num,num)fmap)) (FDOM f) {a | isSomeDataElement (heap_lookup a
       (heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
              heap_element)list))}` THEN
    REWRITE_TAC[INJ; IN_ELIM_THM; isSomeDataElement_def] THEN
    DISCH_THEN(MP_TAC o SPEC `p:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[heap_lookup_LESS];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `FAPPLY (f:(num,num)fmap) p < dimword (:A) DIV 2 EXP shift_length c`
    MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[X_LT_DIV; ZERO_LT_TWOEXP] THEN
  MP_TAC(SPEC `shift_length c` ZERO_LT_TWOEXP) THEN ARITH_TAC);;

(* two clear top bits *)
let MP5AUX_LT_TOP_BITS = prove
 (`!x k. x < 2 EXP (k + 2) /\ ~numbit k x /\ ~numbit (k + 1) x ==> x < 2 EXP k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[numbit] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV; EXP_1] THEN
  SUBGOAL_THEN `~(2 EXP k = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[EXP_EQ_0] THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `x DIV 2 EXP k < 4` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ] THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `x DIV 2 EXP k = 0` MP_TAC THENL
   [UNDISCH_TAC `x DIV 2 EXP k < 4` THEN
    UNDISCH_TAC `~ODD (x DIV 2 EXP k)` THEN UNDISCH_TAC `~ODD (x DIV 2 EXP k DIV 2)` THEN
    SPEC_TAC(`x DIV 2 EXP k`,`q:num`) THEN GEN_TAC THEN
    REWRITE_TAC[IMP_IMP; ARITH_RULE `q < 4 <=> q = 0 \/ q = 1 \/ q = 2 \/ q = 3`] THEN
    REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
    TRY(FIRST_ASSUM CONTR_TAC);
    ASM_SIMP_TAC[DIV_EQ_0]]);;

(* small arithmetic: the integer range of small numbers via ival *)
let MP5AUX_small_int_ival = prove
 (`!x. good_dimindex(:A) ==>
       (small_int (:A) x <=>
        --(&2 pow (dimindex(:A) - 1)) <= &4 * x /\ &4 * x < &2 pow (dimindex(:A) - 1))`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def; small_int_def; dimword_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN INT_ARITH_TAC);;

let MP5AUX_bit_word_val_byte = prove
 (`!(x:byte) k. bit k (word (val x):A word) <=> k < dimindex(:A) /\ bit k x`,
  REWRITE_TAC[MP5AUX_BIT_WORD; numbit; BIT_VAL]);;

let MP5AUX_Smallnum_val_byte = prove
 (`!x:byte. Smallnum (&(val x)):A word = word_shl (word (val x)) 2`,
  REWRITE_TAC[MP5AUX_Smallnum_shl; GSYM WORD_IWORD]);;

(* the payload condition of a heap element (no address computation) *)
let MP5AUX_heap_el_cond = prove
 (`!heap a sp sp1 gens c st (m:A word -> A word_loc) dm limit n ys l tag qs.
     heap_in_memory_store heap a sp sp1 gens c st m dm limit /\
     heap_lookup n heap = SOME (DataElement ys l (tag,qs)) ==>
     ?h ts cnd.
       word_payload ys l tag qs c = (h,ts,cnd) /\ cnd /\
       LENGTH ts < 2 EXP (dimindex (:A) - 4) /\ decode_length c h = word (LENGTH ts)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [heap_in_memory_store_def]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP heap_lookup_SPLIT) THEN
  DISCH_THEN(X_CHOOSE_THEN `ha:(((A)word_loc,data_to_word_memoryProof_tag#
                                 ((A)word_loc)list)heap_element)list`
    (X_CHOOSE_THEN `hb:(((A)word_loc,data_to_word_memoryProof_tag#
                         ((A)word_loc)list)heap_element)list`
     (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC))) THEN
  SUBGOAL_THEN `?h ts cnd. word_payload ys l tag qs c =
                  (h:A word,ts:((A)word_loc)list,cnd:bool)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`h:A word`; `ts:((A)word_loc)list`; `cnd:bool`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
    can (find_term ((=) `fun2set:(A word->A word_loc)#(A word->bool)->
                          A word#A word_loc->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[word_heap_APPEND; word_heap_def; word_el_def; pair_CASE] THEN
  DISCH_TAC THEN MP5AUX_SEP_COND_TAC THEN ASM_REWRITE_TAC[]);;

(* close a word ring identity by WORD_RULE *)
let MP5AUX_WORD_RULE_TAC : tactic = fun (asl,w as g) -> ACCEPT_TAC (WORD_RULE w) g;;

(* a heap address scaled by the pointer shift fits in a word *)
let MP5AUX_heap_lookup_BOUND = prove
 (`!heap a sp sp1 gens c st (m:A word -> A word_loc) dm limit p x.
     heap_in_memory_store heap a sp sp1 gens c st m dm limit /\
     heap_lookup p heap = SOME x ==>
     p * 2 EXP shift_length c < dimword (:A) /\ p < dimword (:A)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_heap_in_memory_store_IMP) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP heap_lookup_LESS) THEN
  SUBGOAL_THEN `p < dimword (:A) DIV 2 EXP shift_length c` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[X_LT_DIV; ZERO_LT_TWOEXP] THEN
  MP_TAC(SPEC `shift_length c` ZERO_LT_TWOEXP) THEN
  REWRITE_TAC[ARITH_RULE `0 < k <=> 1 <= k`] THEN DISCH_TAC THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `(p + 1) * 2 EXP shift_length c` THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `p = p * 1`] THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `(p + 1) * 1` THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ARITH_TAC);;



let MP5AUX_and_not1 = prove
 (`!x:A word. word_and x (word_not (word 1)) = x <=> ~bit 0 x`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN REWRITE_TAC MP5AUX_BIT_RULES THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[DIMINDEX_GT_0] THEN
    CONV_TAC(DEPTH_CONV MP5AUX_NUMBIT_CONV) THEN MESON_TAC[];
    DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    CONV_TAC(DEPTH_CONV MP5AUX_NUMBIT_CONV) THEN ASM_CASES_TAC `i = 0` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let MP5AUX_bit0_BlockNil = prove
 (`!n. ~bit 0 (BlockNil n:A word)`,
  REWRITE_TAC[BlockNil_def; WORD_ADD_BIT0; BIT_WORD_SHL] THEN
  REWRITE_TAC[MP5AUX_BIT_WORD] THEN CONV_TAC(DEPTH_CONV MP5AUX_NUMBIT_CONV) THEN
  ARITH_TAC);;

(* sums bounded elementwise *)
let MP5AUX_SUM_MAP_BOUND = prove
 (`!(f:A->num) k l. ALL (\x. f x <= k) l ==> SUM (MAP f l) <= LENGTH l * k`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL; MAP; SUM; LENGTH; MULT_CLAUSES; LE_REFL] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* the arithmetic of memory_rel_depth_size_limit *)
let MP5AUX_depth_arith = prove
 (`!dd q n ll ss kk.
     16 * q <= dd /\ 16 <= dd /\ n < q /\ ll < q /\ ss <= ll * kk /\ dd <= kk ==>
     1 + n + ss + ll <= dd * kk`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ll * kk <= q * kk /\ (1 + q) * kk <= dd * kk` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  UNDISCH_TAC `ss <= ll * kk` THEN UNDISCH_TAC `dd <= kk` THEN
  UNDISCH_TAC `16 * q <= dd` THEN UNDISCH_TAC `n < q` THEN UNDISCH_TAC `ll < q` THEN
  ARITH_TAC);;

(* |- p s  gives  |- q s  for STAR terms p and q equal up to AC *)
let MP5AUX_STAR_AC_RULE q th =
  let p,s = dest_comb (concl th) in
  if p = q then th else EQ_MP (AP_THM (AC LSORTAUX_STAR_AC (mk_eq(p,q))) s) th;;

(* writing one word of a word list in memory *)
let MP5AUX_word_list_LUPDATE = prove
 (`!(xs:((A)word_loc)list) (a:A word) j y p m dm.
     (misc_word_list a xs STAR p) (fun2set (m,dm)) /\ j < LENGTH xs ==>
     (misc_word_list a (LUPDATE y j xs) STAR p)
       (fun2set ((word_add a (word_mul (word j) bytes_in_word) =+ y) m,dm))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH_RULE `~(j < 0)`] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `j:num` num_CASES) THEN
  REWRITE_TAC[LUPDATE_def; misc_word_list_def; LT_SUC; LT_0] THENL
   [REWRITE_TAC[WORD_MUL_0; WORD_ADD_0] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MP5AUX_STAR_AC_RULE
      `set_sep_one ((a:A word),(h:A word_loc)) STAR
       (misc_word_list (word_add a bytes_in_word) t STAR p)`) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ISPEC `y:A word_loc` write_fun2set)) THEN
    DISCH_THEN(ACCEPT_TAC o MP5AUX_STAR_AC_RULE
      `(set_sep_one ((a:A word),(y:A word_loc)) STAR
        misc_word_list (word_add a bytes_in_word) t) STAR p`);
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`word_add (a:A word) bytes_in_word`; `n:num`;
      `y:A word_loc`; `set_sep_one ((a:A word),(h:A word_loc)) STAR p`;
      `m:A word->A word_loc`; `dm:A word->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(ACCEPT_TAC o MP5AUX_STAR_AC_RULE
        `misc_word_list (word_add (a:A word) bytes_in_word) (t:((A)word_loc)list) STAR
         (set_sep_one ((a:A word),(h:A word_loc)) STAR p)`);
      ALL_TAC] THEN
    SUBGOAL_THEN `word_add (word_add (a:A word) bytes_in_word) (word_mul (word n) bytes_in_word) =
                  word_add a (word_mul (word (SUC n)) bytes_in_word)` SUBST1_TAC THENL
     [REWRITE_TAC[ADD1] THEN MP5AUX_WORD_RULE_TAC; ALL_TAC] THEN
    DISCH_THEN(ACCEPT_TAC o MP5AUX_STAR_AC_RULE
      `(set_sep_one ((a:A word),(h:A word_loc)) STAR
        misc_word_list (word_add a bytes_in_word) (LUPDATE (y:A word_loc) n t)) STAR p`)]);;

let MP5AUX_DIV_MOD_SUB = prove
 (`!d i. 0 < d /\ d <= i ==>
         i DIV d = SUC ((i - d) DIV d) /\ i MOD d = (i - d) MOD d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`i - d:num`; `d:num`] DIVISION) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `(i - d) MOD d`;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `SUC ((i - d) DIV d)`] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[ADD1; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
  ASM_ARITH_TAC);;

(* updating one byte in the words written from a byte list *)
let MP5AUX_write_bytes_LUPDATE = prove
 (`!(ws:(A word)list) bs i b be.
     good_dimindex(:A) /\ i < LENGTH bs /\ i DIV (dimindex(:A) DIV 8) < LENGTH ws ==>
     write_bytes (LUPDATE b i bs) ws be =
     LUPDATE (set_byte (word (i MOD (dimindex(:A) DIV 8))) b
                (EL (i DIV (dimindex(:A) DIV 8)) (write_bytes bs ws be)) be)
             (i DIV (dimindex(:A) DIV 8)) (write_bytes bs ws be)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH_RULE `~(n < 0)`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_good_dimindex_DIV8_LT) THEN
  SUBGOAL_THEN `0 < dimindex(:A) DIV 8` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[write_bytes_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_CASES_TAC `i < dimindex(:A) DIV 8` THENL
   [ASM_SIMP_TAC[DIV_LT; MOD_LT; LUPDATE_def; EL; HD; CONS_11] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`dimindex(:A) DIV 8`; `0`; `bs:byte list`; `h:A word`; `i:num`;
        `b:byte`; `be:bool`] MP5AUX_set_byte_bytes_to_word) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; LE_REFL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REFL_TAC;
      AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[LIST_EQ_REWRITE; LENGTH_DROP; LENGTH_LUPDATE] THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[EL_DROP; LENGTH_LUPDATE; ARITH_RULE `k < l - d ==> k + d < l`] THEN
      REWRITE_TAC[EL_LUPDATE] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`dimindex(:A) DIV 8`; `i:num`] MP5AUX_DIV_MOD_SUB) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LUPDATE_def; EL; TL; CONS_11] THEN CONJ_TAC THENL
   [MATCH_MP_TAC bytes_to_word_same THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REWRITE_TAC[LENGTH_LUPDATE; EL_LUPDATE] THEN
    SUBGOAL_THEN `~(k:num = i)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[misc_DROP_LUPDATE; ARITH_RULE `~(i < d) ==> d <= i`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`DROP (dimindex(:A) DIV 8) (bs:byte list)`;
    `i - dimindex(:A) DIV 8`; `b:byte`; `be:bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_DROP] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LT_SUC]) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

(* a 64-bit word is determined by its stored halves (or its stored copy) *)
let MP5AUX_word64_extract_11 = prove
 (`!(w1:int64) w2.
     (dimindex(:A) = 32 /\
      (word_extract 63 32 w1:A word) = word_extract 63 32 w2 /\
      (word_extract 31 0 w1:A word) = word_extract 31 0 w2 ==> w1 = w2) /\
     (dimindex(:A) = 64 /\
      (word_extract 63 0 w1:A word) = word_extract 63 0 w2 ==> w1 = w2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_EXTRACT; DIMINDEX_64] THEN
  CONJ_TAC THEN STRIP_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THENL
   [ASM_CASES_TAC `32 <= k` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `k - 32` o check (fun th ->
        can (find_term ((=) `32`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[ARITH_RULE `32 <= k ==> k - 32 + 32 = k`;
                   ARITH_RULE `32 <= k /\ k < 64 ==> k - 32 < 32`;
                   ARITH_RULE `k < 64 ==> k <= 63`];
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
        can (find_term ((=) `31`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(32 <= k) ==> k < 32`;
                   ARITH_RULE `~(32 <= k) ==> k <= 31`]];
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    ASM_SIMP_TAC[ARITH_RULE `k < 64 ==> k <= 63`]]);;

(* the header of a byte array as a number, and its tag bits *)
let MP5AUX_make_byte_header_word = prove
 (`!c fl len.
     data_to_word_config_len_size c + 7 < dimindex(:A) ==>
     make_byte_header c fl len:A word =
     word (2 EXP (dimindex(:A) - backend_common_word_shift(:A) -
                  data_to_word_config_len_size c) *
           (len + 2 EXP backend_common_word_shift(:A)) + (if fl then 7 else 23))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[make_byte_header_def; backend_common_word_shift_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_SHL_WORD] THEN
  ASM_CASES_TAC `dimindex(:A) = 32` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN BOOL_CASES_TAC `fl:bool` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MP5AUX_WORD_OR_DISJ THEN MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `2 EXP 5` THEN REWRITE_TAC[WORDSAUX_EXP2_LE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let MP5AUX_make_byte_header_bits = prove
 (`!c fl len. data_to_word_config_len_size c + 7 < dimindex(:A) ==>
     bit 2 (make_byte_header c fl len:A word) /\
     ~bit 3 (make_byte_header c fl len:A word) /\
     (bit 4 (make_byte_header c fl len:A word) <=> ~fl)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[MP5AUX_make_byte_header_word] THEN
  SUBGOAL_THEN `5 <= dimindex(:A) - backend_common_word_shift(:A) -
                     data_to_word_config_len_size c` MP_TAC THENL
   [REWRITE_TAC[backend_common_word_shift_def] THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`dimindex(:A) - backend_common_word_shift(:A) -
            data_to_word_config_len_size c`,`s:num`) THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(if fl then 7 else 23) < 2 EXP s` ASSUME_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 5` THEN
    ASM_REWRITE_TAC[WORDSAUX_EXP2_LE] THEN COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MP5AUX_BIT_WORD; MP5AUX_NUMBIT_MUL_ADD;
    ARITH_RULE `5 <= s ==> 2 < s /\ 3 < s /\ 4 < s`] THEN
  BOOL_CASES_TAC `fl:bool` THEN REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV MP5AUX_NUMBIT_CONV) THEN ASM_ARITH_TAC);;

(* HOL4 line 10992 *)
let make_header_tag_mask = prove
 (`!c k n.
     k < 2 EXP (dimindex (:A) - (data_to_word_config_len_size c + 2)) ==>
     word_and (tag_mask c) (make_header c (word k:A word) n) = word (4 * k)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[tag_mask_def; make_header_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ONCE_REWRITE_TAC[ARITH_RULE `4 * k = k * 2 EXP 2`] THEN
  MP5AUX_WORD_BITS_TAC THEN REWRITE_TAC[NUMBIT_MUL_2EXP] THEN
  SUBGOAL_THEN `numbit (i - 2) k ==>
    i - 2 < dimindex(:A) - (data_to_word_config_len_size c + 2)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `2 EXP (i - 2) <
      2 EXP (dimindex(:A) - (data_to_word_config_len_size c + 2))` MP_TAC THENL
     [ASM_MESON_TAC[BIT_IMP_GE_TWOEXP; LET_TRANS]; REWRITE_TAC[LT_EXP] THEN ARITH_TAC];
    ASM_CASES_TAC `2 <= i` THEN ASM_REWRITE_TAC[] THEN MP5AUX_BITS_ARITH_TAC]);;

(* HOL4 line 11014 *)
let make_header_and_2 = prove
 (`!c (w:A word) n. word_and (word 2) (make_header c w n) = word 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[make_header_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP5AUX_WORD_BITS_TAC THEN MP5AUX_BITS_ARITH_TAC);;

(* HOL4 line 11022 *)
let encode_header_tag_mask = prove
 (`!c tag n (w:A word).
     encode_header c (4 * tag) n = SOME w /\ good_dimindex (:A) ==>
     tag < dimword (:A) DIV 16 /\
     word_and w (word_or (tag_mask c) (word 2)) = word (16 * tag + 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[encode_header_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_LEFT_AND_OVER_OR] THEN
  ONCE_REWRITE_TAC[WORD_AND_SYM] THEN REWRITE_TAC[make_header_and_2] THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `4 * tag`; `n:num`]
    (INST_TYPE [`:A`,`:A`] make_header_tag_mask)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `a - (b + 2) = a - b - 2`]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `4 * 4 * tag = 16 * tag`; GSYM word_add_n2w] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_ADD_OR THEN
  ONCE_REWRITE_TAC[ARITH_RULE `16 * tag = tag * 2 EXP 4`] THEN
  MP5AUX_WORD_BITS_TAC THEN REWRITE_TAC[NUMBIT_MUL_2EXP] THEN ARITH_TAC);;

(* HOL4 line 11039 *)
let memory_rel_tag_limit = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm ts' tag l w rest.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Block ts' tag l,(w:A word_loc)) rest) /\
     good_dimindex (:A) ==>
     tag < dimword (:A) DIV 16`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_Block_IMP)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[encode_header_tag_mask]);;

(* HOL4 line 11049: LESS_DIV_16_IMP *)
let data_to_word_memoryProof_LESS_DIV_16_IMP = prove
 (`!n k. n < k DIV 16 ==> 16 * n + 2 < k`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`k:num`; `16`] DIVISION) THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

(* HOL4 line 11055 *)
let MULT_BIT0 = prove
 (`!m n. numbit 0 (m * n) <=> numbit 0 m /\ numbit 0 n`,
  REWRITE_TAC[numbit; EXP; DIV_1; ODD_MULT]);;

(* HOL4 line 11061 *)
let memory_rel_test_nil_eq = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm ts' tag l w rest n.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Block ts' tag l,w:A word_loc) rest) /\
     n < dimword (:A) DIV 16 /\ good_dimindex (:A) ==>
     ?v. w = wl_Word v /\ (v = word (16 * n + 2) <=> tag = n /\ l = [])`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_Block_IMP)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:A word` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v:A word` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[word_mul_n2w; word_add_n2w; n2w_11] THEN
    SUBGOAL_THEN `tag * 16 + 2 < dimword(:A) /\ 16 * n + 2 < dimword(:A)`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ONCE_REWRITE_TAC[MULT_SYM]; ALL_TAC] THEN
      MATCH_MP_TAC data_to_word_memoryProof_LESS_DIV_16_IMP THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
    STRIP_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `bit 0 (v:A word)` THEN ASM_REWRITE_TAC[MP5AUX_BIT_WORD] THEN
    REWRITE_TAC[numbit; EXP; DIV_1; ODD_ADD; ODD_MULT] THEN CONV_TAC NUM_REDUCE_CONV]);;

(* HOL4 line 11073 *)
let memory_rel_test_none_eq = prove
 (`!c n len be ts refs sp st (m:A word -> A word_loc) dm ts' tag l w rest.
     encode_header c (4 * n) len = (NONE:(A word)option) /\
     memory_rel c be ts refs sp st m dm
       (CONS (data_Block ts' tag l,w:A word_loc) rest) /\
     ~(len = 0) /\ good_dimindex (:A) ==>
     ~(tag = n /\ LENGTH l = len)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_Block_IMP)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  COND_CASES_TAC THENL
   [ASM_MESON_TAC[LENGTH]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_MESON_TAC[option_DISTINCT]);;

(* HOL4 line 11083 *)
let not_bit_lt_2exp = prove
 (`!p x n. n < 2 EXP (p + 1) ==> ~numbit (p + (x + 1)) n`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP BIT_IMP_GE_TWOEXP) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_LE; GSYM NOT_LT] THEN
  DISCH_TAC THEN MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP (p + 1)` THEN
  ASM_REWRITE_TAC[WORDSAUX_EXP2_LE] THEN ARITH_TAC);;

(* HOL4 line 11090 (val) *)
let not_bit_lt_2 = prove
 (`!x n. n < 2 ==> ~numbit (x + 1) n`,
  MP_TAC(SPEC `0` not_bit_lt_2exp) THEN REWRITE_TAC[ADD_CLAUSES; EXP_1]);;

(* HOL4 line 11092 *)
let encode_header_EQ = prove
 (`!c t1 l1 t2 l2 (w1:A word) w2.
     encode_header c t1 l1 = SOME w1 /\
     encode_header c t2 l2 = SOME w2 /\
     data_to_word_config_len_size c + 2 < dimindex (:A) ==>
     (w1 = w2 <=> t1 = t2 /\ l1 = l2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[encode_header_def] THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
  ABBREV_TAC `L = dimindex(:A) - data_to_word_config_len_size c` THEN
  SUBGOAL_THEN `4 * t1 + 3 < 2 EXP L /\ 4 * t2 + 3 < 2 EXP L` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `2 EXP L = 2 EXP (L - 2) * 4` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 = 2 EXP 2`; GSYM EXP_ADD] THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MP5AUX_make_header_word; n2w_11; dimword_def] THEN
  SUBGOAL_THEN `2 EXP dimindex(:A) = 2 EXP L * 2 EXP data_to_word_config_len_size c`
    SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; MP5AUX_LT_MUL_ADD; MP5AUX_DIVMOD_EQ] THEN ARITH_TAC);;

(* HOL4 line 11151 *)
let memory_rel_ValueArray_IMP = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl p v vars vals.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl p,v:A word_loc) vars) /\
     lookup p refs = SOME (bvl_ValueArray vals) /\ good_dimindex (:A) ==>
     ?w a x.
       v = wl_Word w /\ bit 0 w /\ bit 3 x /\ ~bit 2 x /\ ~bit 4 x /\
       get_real_simple_addr c st w = SOME a /\
       get_real_addr c st w = SOME a /\
       m a = wl_Word x /\ a IN dm /\
       decode_length c x = word (LENGTH vals) /\
       LENGTH vals < 2 EXP (dimindex (:A) - 4)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_memory_rel_HD) THEN
  MP5AUX_UNDISCH_HEAD "v_inv" THEN ASM_REWRITE_TAC[v_inv_def] THEN SIMP[] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN
  ASM_REWRITE_TAC[MP5AUX_reachable_refs_HD] THEN
  ASM_REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF] THEN SIMP[RefBlock_def] THEN
  STRIP_TAC THEN MP5AUX_HEAP_EL_TAC THEN
  SIMP[word_payload_def; PAIR_EQ] THEN STRIP_TAC THEN
  MP5AUX_SUBST_VAR_TAC "v" THEN MP5AUX_SUBST_VAR_TAC "h" THEN
  MAP_EVERY EXISTS_TAC
   [`get_addr c (FAPPLY (f:(num,num)fmap) p) (wl_Word (word 0)):A word`;
    `word_add curr (word_mul (word (FAPPLY (f:(num,num)fmap) p)) bytes_in_word):A word`;
    `make_header c (word 2) (LENGTH (zs:(((A)word_loc)heap_address)list)):A word`] THEN
  ASM_REWRITE_TAC[word_addr_def; get_addr_0] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_heap_in_memory_store_IMP) THEN
  FIRST_ASSUM(SUBST_ALL_TAC o SYM o MATCH_MP LIST_REL_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MP5AUX_make_header_bit;
    ARITH_RULE `x + 7 < d ==> 3 < d - x /\ 2 < d - x /\ 4 < d - x`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MP5AUX_BIT_WORD] THEN
  CONV_TAC(DEPTH_CONV MP5AUX_NUMBIT_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[good_dimindex_def]) THEN ASM_ARITH_TAC);;

(* HOL4 line 11181 *)
let blocks_unique_Thunk = prove
 (`!p refs ev x ts bl (vars:(data_v#A)list).
     lookup p refs = SOME (bvl_Thunk ev x) /\
     blocks_unique ts (all_vs refs (CONS (data_RefPtr bl p) (MAP FST vars))) ==>
     blocks_unique ts (all_vs refs (CONS x (MAP FST vars)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC blocks_unique_SUBSET THEN
  EXISTS_TAC `all_vs refs (CONS (data_RefPtr bl p) (MAP FST (vars:(data_v#A)list)))` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; all_vs_def; IN_UNION; IN_ELIM_THM] THEN
  X_GEN_TAC `y:data_v` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP MEM_v_all_vs_split) THEN
  ASM_MESON_TAC[MEM_v_all_vs_extend_hd]);;

(* HOL4 line 11196 *)
let blocks_unique_Thunk2 = prove
 (`!p refs ev v' ts (vars:(data_v#A)list).
     lookup p refs = SOME (bvl_Thunk ev v') /\
     blocks_unique ts (all_vs refs (CONS (data_RefPtr F p) (MAP FST vars))) ==>
     blocks_unique ts
       (all_vs refs (CONS v' (CONS (data_RefPtr F p) (MAP FST vars))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC blocks_unique_SUBSET THEN
  EXISTS_TAC `all_vs refs (CONS (data_RefPtr F p) (MAP FST (vars:(data_v#A)list)))` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; all_vs_def; IN_UNION; IN_ELIM_THM] THEN
  X_GEN_TAC `y:data_v` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP MEM_v_all_vs_split) THEN
  ASM_MESON_TAC[]);;

(* Local helpers (MP5AUX_) for memory_rel_Thunk_IMP *)
let MP5AUX_ref_edge_Thunk_get_refs = prove
 (`!p refs ev z r.
     lookup p refs = SOME (bvl_Thunk ev z) /\ MEM r (get_refs z) ==> ref_edge refs p r`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ref_edge_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[get_refs_def; MAP; FLAT; APPEND_NIL]);;

let MP5AUX_reachable_refs_Thunk = prove
 (`!p refs ev z xs bl n.
     lookup p refs = SOME (bvl_Thunk ev z) /\ reachable_refs (CONS z xs) refs n ==>
     reachable_refs (CONS (data_RefPtr bl p) xs) refs n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[reachable_refs_def; MEM] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`data_RefPtr bl p`; `p:num`] THEN
    REWRITE_TAC[get_refs_def; MEM] THEN
    MATCH_MP_TAC RTC_TRANS_R THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MP5AUX_ref_edge_Thunk_get_refs THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let MP5AUX_all_ts_Thunk = prove
 (`!p refs ev z xs bl.
     lookup p refs = SOME (bvl_Thunk ev z) ==>
     all_ts refs (CONS (data_RefPtr bl p) xs) SUBSET all_ts refs (CONS z xs)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[all_ts_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; MEM] THEN
  SUBGOAL_THEN `!t. ~MEM t (v_all_ts (data_RefPtr bl p))` ASSUME_TAC THENL
   [REWRITE_TAC[v_all_ts_def; MEM]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* the header bits that mark a thunk *)
let MP5AUX_and60_thunk = prove
 (`!h:A word. 6 <= dimindex(:A) /\
     (word_and h (word 60) = word ((0 + 6) * 4) \/
      word_and h (word 60) = word ((8 + 6) * 4)) ==>
     ~bit 2 h /\ bit 3 h /\ bit 4 h`,
  GEN_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `2 < dimindex(:A) /\ 3 < dimindex(:A) /\ 4 < dimindex(:A)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (fun th ->
    MP_TAC(AP_TERM `bit 2:A word->bool` th) THEN
    MP_TAC(AP_TERM `bit 3:A word->bool` th) THEN
    MP_TAC(AP_TERM `bit 4:A word->bool` th))) THEN
  REWRITE_TAC[BIT_WORD_AND; MP5AUX_BIT_WORD] THEN
  CONV_TAC(DEPTH_CONV MP5AUX_NUMBIT_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC TAUT);;

let MP5AUX_payload_not_thunk = prove
 (`!ys l tag qs c (h:A word) ts.
     word_payload ys l tag qs c = (h,ts,T) /\ (!e. ~(tag = ThunkTag e)) /\
     data_to_word_config_len_size c + 7 < dimindex(:A) ==>
     bit 2 h \/ ~bit 3 h \/ ~bit 4 h`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `tag:data_to_word_memoryProof_tag`
    (cases "data_to_word_memoryProof_tag")) THEN
  REWRITE_TAC[word_payload_def; PAIR_EQ; injectivity "data_to_word_memoryProof_tag";
              distinctness "data_to_word_memoryProof_tag"] THEN
  STRIP_TAC THEN MP5AUX_SUBST_VAR_TAC "h" THEN
  ASM_SIMP_TAC[MP5AUX_make_header_bit; MP5AUX_make_byte_header_bits;
    ARITH_RULE `x + 7 < d ==> 2 < d - x /\ 3 < d - x /\ 4 < d - x`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC MP5AUX_BIT_RULES THEN
  CONV_TAC(DEPTH_CONV MP5AUX_NUMBIT_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN TRY(FIRST [ASM_MESON_TAC[]; DISJ1_TAC THEN ASM_ARITH_TAC]));;

let MP5AUX_thunk_header_bits = prove
 (`!c ev n. data_to_word_config_len_size c + 7 < dimindex(:A) ==>
     bit 3 (make_header c (word_or (word_shl (thunk_tag_to_bits ev) 3) (word 6)) n:A word) /\
     ~bit 2 (make_header c (word_or (word_shl (thunk_tag_to_bits ev) 3) (word 6)) n:A word) /\
     bit 4 (make_header c (word_or (word_shl (thunk_tag_to_bits ev) 3) (word 6)) n:A word) /\
     (bit 5 (make_header c (word_or (word_shl (thunk_tag_to_bits ev) 3) (word 6)) n:A word)
      <=> ev = Evaluated)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MP5AUX_make_header_bit;
    ARITH_RULE `x + 7 < d ==> 2 < d - x /\ 3 < d - x /\ 4 < d - x /\ 5 < d - x`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  STRUCT_CASES_TAC(ISPEC `ev:thunk_mode` (cases "thunk_mode")) THEN
  REWRITE_TAC[thunk_tag_to_bits_def; distinctness "thunk_mode"] THEN
  REWRITE_TAC MP5AUX_BIT_RULES THEN CONV_TAC(DEPTH_CONV MP5AUX_NUMBIT_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let MP5AUX_word_addr_bit0 = prove
 (`!c (h:((A)word_loc)heap_address) w.
     word_addr c h = wl_Word w /\ bit 0 w ==> ?n u. h = Pointer n u`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `h:((A)word_loc)heap_address` (cases "heap_address")) THEN
  REWRITE_TAC[injectivity "heap_address"; distinctness "heap_address"] THENL
   [MESON_TAC[];
    STRUCT_CASES_TAC(ISPEC `a:A word_loc` (cases "word_loc")) THEN
    REWRITE_TAC[word_addr_def; injectivity "word_loc"; distinctness "word_loc"] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC MP5AUX_BIT_RULES THEN CONV_TAC(DEPTH_CONV MP5AUX_NUMBIT_CONV) THEN
    MESON_TAC[]]);;

let MP5AUX_Bignum_shape = prove
 (`!i. ?ys l sg qs. Bignum i:((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                     heap_element = DataElement ys l (NumTag sg,qs)`,
  GEN_TAC THEN REWRITE_TAC[data_to_word_memoryProof_Bignum_def] THEN
  SPEC_TAC(`i2mw i:bool#(A word)list`,`pr:bool#(A word)list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE] THEN MESON_TAC[]);;

let MP5AUX_Word64Rep_shape = prove
 (`!w:int64. ?ys l qs. Word64Rep (:A) w = DataElement ys l (Word64Tag,qs)`,
  GEN_TAC THEN REWRITE_TAC[Word64Rep_def] THEN COND_CASES_TAC THEN MESON_TAC[]);;

let MP5AUX_v_inv_Pointer_not_thunk = prove
 (`!c z refs n u f tf
      (heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list) be.
     v_inv c z refs (Pointer n u,f,tf,heap) /\
     data_dest_thunk z refs = data_NotThunk /\
     (!r. reachable_refs [z] refs r /\ r IN FDOM f ==> bc_ref_inv c r refs (f,tf,heap,be)) ==>
     ?ys l tag qs. heap_lookup n heap = SOME (DataElement ys l (tag,qs)) /\
                   !e. ~(tag = ThunkTag e)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `z:data_v` (CONJUNCT1 (cases "data_v"))) THEN
  REWRITE_TAC[v_inv_def] THENL
   [COND_CASES_TAC THEN
    REWRITE_TAC[distinctness "heap_address"; injectivity "heap_address"] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `a:int` MP5AUX_Bignum_shape) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[option_INJ] THEN
    MESON_TAC[distinctness "data_to_word_memoryProof_tag"];
    REWRITE_TAC[injectivity "heap_address"] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `a:int64` (INST_TYPE [`:A`,`:A`] MP5AUX_Word64Rep_shape)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
    MESON_TAC[distinctness "data_to_word_memoryProof_tag"];
    COND_CASES_TAC THEN
    REWRITE_TAC[distinctness "heap_address"; injectivity "heap_address"] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[BlockRep_def; option_INJ] THEN
    MESON_TAC[distinctness "data_to_word_memoryProof_tag"];
    REWRITE_TAC[distinctness "heap_address"];
    ALL_TAC] THEN
  REWRITE_TAC[data_dest_thunk_def] THEN
  CASES_ON `lookup a1 (refs:(data_v bvl_ref)spt)` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    mp5aux_head_is "lookup" (lhs (concl th)))) THEN
  STRUCT_CASES_TAC(ISPEC `a:data_v bvl_ref` (cases "bvl_ref")) THEN DISCH_TAC THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "bvl_ref"; injectivity "bvl_ref"; injectivity "heap_address"] THENL
   [ALL_TAC; ALL_TAC;
    ASM_CASES_TAC `a0:bool` THEN ASM_REWRITE_TAC[] THEN
    STRUCT_CASES_TAC(ISPEC `a0':thunk_mode` (cases "thunk_mode")) THEN
    CASE_REWRITE_TAC[] THEN SIMP[];
    ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `a1:num`) THEN
  ASM_REWRITE_TAC[MP5AUX_reachable_refs_HD] THEN
  ASM_REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[RefBlock_def; BlockRep_def; data_to_word_memoryProof_Bytes_def;
    option_INJ] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MESON_TAC[distinctness "data_to_word_memoryProof_tag"]);;

let MP5AUX_Thunk_inline_rel = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm p vars ev z
      heap limit a sp' sp1 gens f tf h hs bl.
     heap_in_memory_store heap a sp' sp1 gens c st m dm limit /\
     v_inv c z refs (h,f,tf,heap) /\
     roots_ok (CONS h hs) heap /\ heap_ok heap limit /\
     gc_kind_inv c a sp' sp1 gens heap /\ unused_space_inv a (sp' + sp1) heap /\
     INJ (FAPPLY f) (FDOM f) {a | isSomeDataElement (heap_lookup a heap)} /\
     FDOM f SUBSET (domain refs) /\
     INJ (FAPPLY tf) (FDOM tf) {a | isSomeDataElement (heap_lookup a heap)} /\
     FDOM tf SUBSET (all_ts refs (CONS (data_RefPtr bl p) (MAP FST vars))) /\
     FDOM tf SUBSET {n | n < ts} /\ be_ok (data_to_word_config_be c) be /\
     blocks_unique ts (all_vs refs (CONS (data_RefPtr bl p) (MAP FST vars))) /\
     ALL2 (\v x. v_inv c v refs (x,f,tf,heap)) (MAP FST vars) hs /\
     ALL2 (\v w. word_addr c v = w) hs (MAP SND (vars:(data_v#A word_loc)list)) /\
     (!n. reachable_refs (CONS (data_RefPtr bl p) (MAP FST vars)) refs n /\ n IN FDOM f ==>
          bc_ref_inv c n refs (f,tf,heap,be)) /\
     (limit + 3) * (dimindex (:A) DIV 8) + 1 < dimword (:A) /\ sp <= sp' /\
     lookup p refs = SOME (bvl_Thunk ev z)
     ==> memory_rel c be ts refs sp st m dm (CONS (z,word_addr c h) vars)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[memory_rel_def; word_ml_inv_def; abs_ml_inv_def; bc_stack_ref_inv_def; MAP] THEN
  MAP_EVERY EXISTS_TAC
   [`heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp':num`; `sp1:num`; `gens:gen_state`] THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `CONS (h:((A)word_loc)heap_address) hs` THEN ASM_REWRITE_TAC[ALL2] THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `all_ts refs (CONS (data_RefPtr bl p) (MAP FST (vars:(data_v#A word_loc)list)))` THEN
    ASM_MESON_TAC[MP5AUX_all_ts_Thunk];
    MATCH_MP_TAC blocks_unique_Thunk THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[MP5AUX_reachable_refs_Thunk]]);;

let MP5AUX_reachable_refs_dup = prove
 (`!x xs refs n.
     reachable_refs (CONS x (CONS x xs)) refs n <=> reachable_refs (CONS x xs) refs n`,
  REWRITE_TAC[reachable_refs_def; MEM] THEN MESON_TAC[]);;

let MP5AUX_Thunk_push_rel = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm p vars ev z
      heap limit a sp' sp1 gens f tf h hs y n.
     heap_in_memory_store heap a sp' sp1 gens c st m dm limit /\
     v_inv c (data_RefPtr F p) refs (h,f,tf,heap) /\
     v_inv c z refs (y,f,tf,heap) /\
     heap_lookup n heap = SOME (ThunkBlock ev y) /\
     roots_ok (CONS h hs) heap /\ heap_ok heap limit /\
     gc_kind_inv c a sp' sp1 gens heap /\ unused_space_inv a (sp' + sp1) heap /\
     INJ (FAPPLY f) (FDOM f) {a | isSomeDataElement (heap_lookup a heap)} /\
     FDOM f SUBSET (domain refs) /\
     INJ (FAPPLY tf) (FDOM tf) {a | isSomeDataElement (heap_lookup a heap)} /\
     FDOM tf SUBSET (all_ts refs (CONS (data_RefPtr F p) (MAP FST vars))) /\
     FDOM tf SUBSET {n | n < ts} /\ be_ok (data_to_word_config_be c) be /\
     blocks_unique ts (all_vs refs (CONS (data_RefPtr F p) (MAP FST vars))) /\
     ALL2 (\v x. v_inv c v refs (x,f,tf,heap)) (MAP FST vars) hs /\
     ALL2 (\v w. word_addr c v = w) hs (MAP SND (vars:(data_v#A word_loc)list)) /\
     (!n. reachable_refs (CONS (data_RefPtr F p) (MAP FST vars)) refs n /\ n IN FDOM f ==>
          bc_ref_inv c n refs (f,tf,heap,be)) /\
     (limit + 3) * (dimindex (:A) DIV 8) + 1 < dimword (:A) /\ sp <= sp' /\
     lookup p refs = SOME (bvl_Thunk ev z)
     ==> memory_rel c be ts refs sp st m dm
           (CONS (z,word_addr c y) (CONS (data_RefPtr F p,word_addr c h) vars))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[memory_rel_def; word_ml_inv_def; abs_ml_inv_def; bc_stack_ref_inv_def; MAP] THEN
  MAP_EVERY EXISTS_TAC
   [`heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp':num`; `sp1:num`; `gens:gen_state`] THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `CONS (y:((A)word_loc)heap_address) (CONS h hs)` THEN ASM_REWRITE_TAC[ALL2] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[ThunkBlock_def] o MATCH_MP heap_lookup_MEM) THEN
    UNDISCH_TAC `roots_ok (CONS (h:((A)word_loc)heap_address) hs)
      (heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list)` THEN
    UNDISCH_TAC `heap_ok (heap:(((A)word_loc,data_to_word_memoryProof_tag#
                   ((A)word_loc)list)heap_element)list) limit` THEN
    REWRITE_TAC[roots_ok_def; heap_ok_def; MEM] THEN STRIP_TAC THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[MEM];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `all_ts refs (CONS (data_RefPtr F p) (MAP FST (vars:(data_v#A word_loc)list)))` THEN
    ASM_REWRITE_TAC[all_ts_CONS_SUBSET];
    MATCH_MP_TAC blocks_unique_Thunk2 THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM MP5AUX_reachable_refs_dup] THEN
    MATCH_MP_TAC MP5AUX_reachable_refs_Thunk THEN ASM_MESON_TAC[]]);;

(* HOL4 line 11213 *)
let memory_rel_Thunk_IMP = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl p v vars ev z.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl p,v:A word_loc) vars) /\
     lookup p refs = SOME (bvl_Thunk ev z) /\
     good_dimindex (:A) ==>
     (~bl /\
      ev = Evaluated /\
      !w. v = wl_Word w /\ bit 0 w ==>
          memory_rel c be ts refs sp st m dm (CONS (z,v) vars) /\
          ?a x. get_real_addr c st w = SOME a /\
                m a = wl_Word x /\ a IN dm /\
                ~(word_and x (word 60) = word ((0 + 6) * 4)) /\
                ~(word_and x (word 60) = word ((8 + 6) * 4)))
     \/
     ?w a x.
       v = wl_Word w /\ bit 0 w /\ bit 3 x /\ ~bit 2 x /\ bit 4 x /\
       get_real_simple_addr c st w = SOME a /\
       get_real_addr c st w = SOME a /\
       m a = wl_Word x /\ a IN dm /\
       word_add a bytes_in_word IN dm /\
       decode_length c x = word 1 /\
       (bit 5 x <=> ev = Evaluated) /\
       memory_rel c be ts refs sp st m dm
         (CONS (z,m (word_add a bytes_in_word)) (CONS (data_RefPtr bl p,v) vars))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_memory_rel_HD) THEN
  FIRST_ASSUM(fun th -> if mp5aux_head_is "v_inv" (concl th) &&
    (try fst(dest_const(fst(strip_comb(el 1 (snd(strip_comb(concl th))))))) = "data_RefPtr"
     with Failure _ -> false) then MP_TAC th else failwith "") THEN
  REWRITE_TAC[v_inv_def] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "option"; injectivity "bvl_ref"; distinctness "bvl_ref"] THEN
  STRIP_TAC THENL
  [ASM_MESON_TAC[];
   MP5AUX_SUBST_VAR_TAC "ev'" THEN MP5AUX_SUBST_VAR_TAC "v'" THEN
    MP5AUX_SUBST_VAR_TAC "h" THEN MP5AUX_SUBST_VAR_TAC "v" THEN
    SUBGOAL_THEN `bl = F` SUBST_ALL_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISJ2_TAC THEN REWRITE_TAC[word_addr_def; injectivity "word_loc"; get_addr_0] THEN
    MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
      `sp:num`; `st:(store_name,(A)word_loc)fmap`; `m:A word -> A word_loc`;
      `dm:A word->bool`; `p:num`; `vars:(data_v#A word_loc)list`; `ev:thunk_mode`;
      `z:data_v`;
      `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
      `limit:num`; `a:num`; `sp':num`; `sp1:num`; `gens:gen_state`; `f:(num,num)fmap`;
      `tf:(num,num)fmap`;
      `Pointer (FAPPLY (f:(num,num)fmap) p) (wl_Word (word 0)):((A)word_loc)heap_address`;
      `hs:(((A)word_loc)heap_address)list`; `y:((A)word_loc)heap_address`;
      `FAPPLY (f:(num,num)fmap) p`] MP5AUX_Thunk_push_rel) THEN
    ASM_REWRITE_TAC[word_addr_def] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[ThunkBlock_def] o check (fun th -> is_eq (concl th) &&
      mp5aux_head_is "heap_lookup" (lhs (concl th)))) THEN DISCH_TAC THEN
    MP5AUX_HEAP_EL_TAC THEN SIMP[word_payload_def; PAIR_EQ] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[misc_word_list_def; SEP_CLAUSES] o
      check (fun th -> mp5aux_head_is "STAR" (rator (concl th)))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP read_fun2set) THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`word_add curr (word_mul (word (FAPPLY (f:(num,num)fmap) p)) bytes_in_word):A word`;
      `make_header c (word_or (word_shl (thunk_tag_to_bits ev) 3) (word 6)) 1:A word`] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_heap_in_memory_store_IMP) THEN
    ASM_SIMP_TAC[get_addr_0; MP5AUX_thunk_header_bits];
   MP5AUX_SUBST_VAR_TAC "v'" THEN MP5AUX_SUBST_VAR_TAC "ev" THEN MP5AUX_SUBST_VAR_TAC "v" THEN
    DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:A word` THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
        `sp:num`; `st:(store_name,(A)word_loc)fmap`; `m:A word -> A word_loc`;
        `dm:A word->bool`; `p:num`; `vars:(data_v#A word_loc)list`; `Evaluated`;
        `z:data_v`;
        `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
        `limit:num`; `a:num`; `sp':num`; `sp1:num`; `gens:gen_state`; `f:(num,num)fmap`;
        `tf:(num,num)fmap`; `h:((A)word_loc)heap_address`;
        `hs:(((A)word_loc)heap_address)list`; `bl:bool`] MP5AUX_Thunk_inline_rel) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:data_to_word_config`; `h:((A)word_loc)heap_address`; `w:A word`]
      MP5AUX_word_addr_bit0) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `u:A word_loc` SUBST_ALL_TAC)) THEN
    MP_TAC(ISPECL [`c:data_to_word_config`; `z:data_v`; `refs:(data_v bvl_ref)spt`; `n:num`;
      `u:A word_loc`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
      `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
      `be:bool`] MP5AUX_v_inv_Pointer_not_thunk) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`p:num`; `refs:(data_v bvl_ref)spt`; `Evaluated`; `z:data_v`;
        `[]:data_v list`; `bl:bool`; `r:num`] MP5AUX_reachable_refs_Thunk) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[reachable_refs_def; MEM] THEN MESON_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN MP5AUX_HEAP_EL_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `w = get_addr c n (u:A word_loc):A word` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `word_addr c (Pointer n u) = wl_Word (w:A word)` THEN
      REWRITE_TAC[word_addr_def; injectivity "word_loc"] THEN MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`word_add curr (word_mul (word n) bytes_in_word):A word`; `h':A word`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_heap_in_memory_store_IMP) THEN
    MP_TAC(ISPECL [`ys:(((A)word_loc)heap_address)list`; `l:num`;
      `tag:data_to_word_memoryProof_tag`; `qs:((A)word_loc)list`; `c:data_to_word_config`;
      `h':A word`; `ts':((A)word_loc)list`] MP5AUX_payload_not_thunk) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `6 <= dimindex(:A)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[MP5AUX_and60_thunk]]);;

(* HOL4 line 11620 *)
let memory_rel_Thunk_inlined = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl p w vars ev z.
     memory_rel c be ts refs sp st m dm
       (CONS (data_RefPtr bl p,(w:A word_loc)) vars) /\
     ((?l1 l2. w = wl_Loc l1 l2) \/ (?w1. w = wl_Word w1 /\ ~bit 0 w1)) /\
     lookup p refs = SOME (bvl_Thunk ev z) /\
     good_dimindex (:A) ==>
     ev = Evaluated /\
     memory_rel c be ts refs sp st m dm (CONS (z,w) vars)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (MESON[injectivity "word_loc"; distinctness "word_loc"]
    `((?l1 l2. w = wl_Loc l1 l2) \/ (?w1. w = wl_Word w1 /\ ~bit 0 w1)) ==>
     !w1:A word. ~(w = wl_Word w1 /\ bit 0 w1)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_memory_rel_HD) THEN
  FIRST_ASSUM(fun th -> if mp5aux_head_is "v_inv" (concl th) &&
    (try fst(dest_const(fst(strip_comb(el 1 (snd(strip_comb(concl th))))))) = "data_RefPtr"
     with Failure _ -> false) then MP_TAC th else failwith "") THEN
  REWRITE_TAC[v_inv_def] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "option"; injectivity "bvl_ref"; distinctness "bvl_ref"] THEN
  STRIP_TAC THENL
  [ASM_MESON_TAC[];
   MP5AUX_SUBST_VAR_TAC "h" THEN ASM_MESON_TAC[word_addr_def; get_addr_0];
   CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP5AUX_SUBST_VAR_TAC "v" THEN MP5AUX_SUBST_VAR_TAC "w" THEN
      MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
        `sp:num`; `st:(store_name,(A)word_loc)fmap`; `m:A word -> A word_loc`;
        `dm:A word->bool`; `p:num`; `vars:(data_v#A word_loc)list`; `ev:thunk_mode`;
        `z:data_v`;
        `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
        `limit:num`; `a:num`; `sp':num`; `sp1:num`; `gens:gen_state`; `f:(num,num)fmap`;
        `tf:(num,num)fmap`; `h:((A)word_loc)heap_address`;
        `hs:(((A)word_loc)heap_address)list`; `bl:bool`] MP5AUX_Thunk_inline_rel) THEN
      ASM_REWRITE_TAC[]]);;

(* HOL4 line 11655 (val) *)
let expand_num = prove
 (`4 = SUC 3 /\ 3 = SUC 2 /\ 2 = SUC 1 /\ 1 = SUC 0 /\
   5 = SUC 4 /\ 6 = SUC 5 /\ 7 = SUC 6 /\ 8 = SUC 7`,
  ARITH_TAC);;

(* HOL4 line 11659 *)
let get_byte_set_byte_alt = prove
 (`!w v s be x b.
     good_dimindex (:A) /\ ~(w = v) /\ byte_align w = byte_align v /\
     get_byte w s be = x ==>
     get_byte w (set_byte v b (s:A word) be) be = x`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC get_byte_set_byte_diff THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 11667 *)
let get_byte_bytes_to_word = prove
 (`!i k be zs (t:A word).
     i < LENGTH zs /\ i < 2 EXP k /\
     2 EXP k = dimindex(:A) DIV 8 /\ good_dimindex (:A) ==>
     get_byte (word i) (bytes_to_word (2 EXP k) (word 0) zs t be) be = EL i zs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2 EXP k`; `0`; `zs:byte list`; `t:A word`; `i:num`; `be:bool`]
    MP5AUX_get_byte_bytes_to_word) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; LE_REFL]);;

(* HOL4 line 11704 *)
let MOD_MULT_MOD_LEMMA = prove
 (`!k n x t.
     k MOD n = 0 /\ x MOD n = t /\ 0 < k /\ 0 < n /\ n <= k ==>
     (x MOD k) MOD n = t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOD_EQ_0] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `q:num` SUBST1_TAC)
    (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC))) THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MOD]);;

(* HOL4 line 11715 *)
let w2n_add_byte_align_lemma = prove
 (`!a' (a:A word).
     good_dimindex (:A) ==>
     val (word_add a' (byte_align a)) MOD (dimindex (:A) DIV 8) =
     val a' MOD (dimindex (:A) DIV 8)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o LAND_CONV) [GSYM WORD_VAL] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV) [GSYM WORD_VAL] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN ASM_SIMP_TAC[MP5AUX_VAL_MOD_BYTES] THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  ASM_SIMP_TAC[byte_align_def; align_w2n; MP5AUX_VAL_MOD_BYTES; MP5AUX_EXP_LOG2_BYTES;
               ONCE_REWRITE_RULE[MULT_SYM] MOD_MULT; ADD_CLAUSES; MOD_MOD_REFL]);;

(* HOL4 line 11730 *)
let get_byte_byte_align = prove
 (`!a' a (w:A word) be.
     good_dimindex (:A) ==>
     get_byte (word_add a' (byte_align a)) w be = get_byte a' w be`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[get_byte_def; byte_index_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_SIMP_TAC[w2n_add_byte_align_lemma]);;

(* HOL4 line 11738 *)
let get_byte_eq = prove
 (`!a a' (w:A word) be.
     good_dimindex (:A) /\ a = word_add (byte_align a) a' ==>
     get_byte a w be = get_byte a' w be`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o check (is_var o lhs o concl)) THEN
  ONCE_REWRITE_TAC[WORD_ADD_SYM] THEN ASM_SIMP_TAC[get_byte_byte_align]);;

(* HOL4 line 11746 *)
let write_bytes_same = prove
 (`!be ws b1 b2.
     (!n. n < LENGTH (ws:(A word)list) * (dimindex(:A) DIV 8) ==>
          n < LENGTH b1 /\ n < LENGTH b2 /\ EL n b1 = EL n b2)
     ==> write_bytes b1 ws be = write_bytes b2 ws be`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[write_bytes_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[CONS_11] THEN CONJ_TAC THENL
   [MATCH_MP_TAC bytes_to_word_same THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LENGTH; MULT_CLAUSES] THEN
    ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n + dimindex(:A) DIV 8`) THEN
    REWRITE_TAC[LENGTH; MULT_CLAUSES; LENGTH_DROP] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[EL_DROP] THEN ASM_ARITH_TAC]);;

(* HOL4 line 11765 *)
let set_byte_bytes_to_word = prove
 (`!i ls k b t be.
     i < LENGTH ls /\ i < 2 EXP k /\ 2 EXP k = dimindex (:A) DIV 8 /\
     good_dimindex(:A) ==>
     set_byte (word i) b (bytes_to_word (2 EXP k) (word 0) ls t be) be =
     bytes_to_word (2 EXP k) (word 0:A word) (LUPDATE b i ls) t be`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2 EXP k`; `0`; `ls:byte list`; `t:A word`; `i:num`; `b:byte`; `be:bool`]
    MP5AUX_set_byte_bytes_to_word) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; LE_REFL]);;

(* Local helpers (MP5AUX_) for heap_in_memory_store_UpdateByte *)
let MP5AUX_word_list_EL = prove
 (`!(xs:((A)word_loc)list) (a:A word) j p m dm.
     (misc_word_list a xs STAR p) (fun2set (m,dm)) /\ j < LENGTH xs ==>
     m (word_add a (word_mul (word j) bytes_in_word)) = EL j xs /\
     word_add a (word_mul (word j) bytes_in_word) IN dm`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH_RULE `~(j < 0)`] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `j:num` num_CASES) THEN
  REWRITE_TAC[misc_word_list_def; LT_SUC; LT_0; EL; HD; TL] THENL
   [REWRITE_TAC[WORD_MUL_0; WORD_ADD_0] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MP5AUX_STAR_AC_RULE
      `set_sep_one ((a:A word),(h:A word_loc)) STAR
       (misc_word_list (word_add a bytes_in_word) t STAR p)`) THEN
    MATCH_ACCEPT_TAC read_fun2set;
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`word_add (a:A word) bytes_in_word`; `n:num`;
      `set_sep_one ((a:A word),(h:A word_loc)) STAR p`;
      `m:A word->A word_loc`; `dm:A word->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(ACCEPT_TAC o MP5AUX_STAR_AC_RULE
        `misc_word_list (word_add (a:A word) bytes_in_word) (t:((A)word_loc)list) STAR
         (set_sep_one ((a:A word),(h:A word_loc)) STAR p)`);
      ALL_TAC] THEN
    SUBGOAL_THEN `word_add (word_add (a:A word) bytes_in_word)
                    (word_mul (word n) bytes_in_word) =
                  word_add a (word_mul (word (SUC n)) bytes_in_word)` SUBST1_TAC THENL
     [REWRITE_TAC[ADD1] THEN MP5AUX_WORD_RULE_TAC; REWRITE_TAC[]]]);;

let MP5AUX_word_el_Bytes = prove
 (`!(e:A word) be fl bs (ws:(A word)list) c.
     word_el e (Bytes be fl bs ws) c =
     misc_word_list e
       (CONS (wl_Word (make_byte_header c fl (LENGTH bs):A word))
             (MAP wl_Word (write_bytes bs ws be))) STAR
     cond (LENGTH ws < 2 EXP (dimindex (:A) - 4) /\
           decode_length c (make_byte_header c fl (LENGTH bs):A word) =
             word (LENGTH ws) /\
           LENGTH bs + 2 EXP backend_common_word_shift(:A) <
           2 EXP (data_to_word_config_len_size c + backend_common_word_shift(:A)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[backend_common_word_shift_def] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[data_to_word_memoryProof_Bytes_def] THENC
    TOP_DEPTH_CONV let_CONV THENC REWRITE_CONV[word_el_def; word_payload_def] THENC
    TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV[pair_CASE; LENGTH_MAP; LENGTH_write_bytes])) THEN
  REFL_TAC);;

(* HOL4 line 11786 *)
let heap_in_memory_store_UpdateByte = prove
 (`!heap a sp sp1 gens c s (m:A word -> A word_loc) dm limit ha be fl bs ws hb i
    ad curr w b.
     heap_in_memory_store heap a sp sp1 gens c s m dm limit /\
     heap = APPEND (APPEND ha [Bytes be fl bs ws]) hb /\ i < LENGTH bs /\
     ad = word_add (word_add (word_add curr bytes_in_word) (word i))
                   (word_mul (bytes_in_word:A word) (word (heap_length ha))) /\
     FLOOKUP s CurrHeap = SOME (wl_Word curr) /\
     m (byte_align ad) = wl_Word w /\ good_dimindex(:A)
     ==>
     heap_in_memory_store (APPEND (APPEND ha [Bytes be fl (LUPDATE b i bs) ws]) hb)
       a sp sp1 gens c s
       ((byte_align ad =+ wl_Word (set_byte ad b w be)) m) dm limit`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP5AUX_SUBST_VAR_TAC "heap" THEN MP5AUX_SUBST_VAR_TAC "ad" THEN
  UNDISCH_TAC `heap_in_memory_store
     (APPEND (APPEND ha [Bytes be fl bs ws]) hb) a sp sp1 gens c s
     (m:A word -> A word_loc) dm limit` THEN
  REWRITE_TAC[heap_in_memory_store_def; heap_length_APPEND; heap_length_Bytes] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `curr':A word = curr` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `FLOOKUP s CurrHeap = SOME (wl_Word (curr':A word))` THEN
    ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`curr:A word`; `other:A word`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> mp5aux_head_is "STAR" (rator (concl th)))) THEN
  REWRITE_TAC[word_heap_APPEND; word_heap_def; SEP_CLAUSES] THEN
  REWRITE_TAC[heap_length_APPEND; heap_length_Bytes; MP5AUX_word_el_Bytes; LENGTH_LUPDATE] THEN
  ABBREV_TAC `e = word_add curr (word_mul bytes_in_word (word (heap_length
    (ha:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list))))
    :A word` THEN
  ABBREV_TAC `h = make_byte_header c fl (LENGTH (bs:byte list)):A word` THEN
  ABBREV_TAC `ws1 = write_bytes (bs:byte list) (ws:(A word)list) be` THEN
  DISCH_TAC THEN MP5AUX_SEP_COND_TAC THEN ASM_REWRITE_TAC[SEP_CLAUSES] THEN
  SUBGOAL_THEN `~(dimindex(:A) DIV 8 = 0) /\ dimindex(:A) DIV 8 < dimword(:A)`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MP5AUX_good_dimindex_DIV8) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i DIV (dimindex(:A) DIV 8) < LENGTH (ws:(A word)list)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:data_to_word_config`; `fl:bool`; `LENGTH (bs:byte list)`]
      decode_length_make_byte_header) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val(word (LENGTH (ws:(A word)list)):A word) = LENGTH ws` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC `2 EXP (dimindex(:A) - 4)` THEN ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[RDIV_LT_EQ] THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `LENGTH (bs:byte list)` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (ws1:(A word)list) = LENGTH (ws:(A word)list)` ASSUME_TAC THENL
   [EXPAND_TAC "ws1" THEN REWRITE_TAC[LENGTH_write_bytes]; ALL_TAC] THEN
  UNDISCH_TAC `i DIV (dimindex(:A) DIV 8) < LENGTH (ws:(A word)list)` THEN
  MP_TAC(SPECL [`i:num`; `dimindex(:A) DIV 8`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `j = i DIV (dimindex(:A) DIV 8)` THEN
  ABBREV_TAC `r = i MOD (dimindex(:A) DIV 8)` THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `pp = word_add e (word_mul (word (SUC j)) bytes_in_word):A word` THEN
  SUBGOAL_THEN `word_add (word_add (word_add curr bytes_in_word) (word i))
                  (word_mul bytes_in_word (word (heap_length
    (ha:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list)))) =
                word_add pp (word r):A word` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["pp"; "e"] THEN
    FIRST_X_ASSUM(fun th -> if is_var(lhs(concl th)) && fst(dest_var(lhs(concl th))) = "i"
                            then SUBST1_TAC th else failwith "") THEN
    REWRITE_TAC[bytes_in_word_def; WORD_ADD; WORD_MUL; ADD1] THEN MP5AUX_WORD_RULE_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `byte_align (word_add pp (word r)) = pp:A word` ASSUME_TAC THENL
   [REWRITE_TAC[byte_align_def] THEN MATCH_MP_TAC align_add_aligned THEN
    ASM_SIMP_TAC[MP5AUX_EXP_LOG2_BYTES] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `pp = word_add curr (word ((heap_length
         (ha:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list) +
          SUC j) * 2 EXP LOG2 (dimindex(:A) DIV 8))):A word` SUBST1_TAC THENL
       [ASM_SIMP_TAC[MP5AUX_EXP_LOG2_BYTES] THEN MAP_EVERY EXPAND_TAC ["pp"; "e"] THEN
        REWRITE_TAC[bytes_in_word_def; WORD_ADD; WORD_MUL; ADD1] THEN MP5AUX_WORD_RULE_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[aligned_add_pow] THEN ASM_REWRITE_TAC[GSYM byte_aligned_def];
      MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `r:num` THEN
      ASM_REWRITE_TAC[VAL_WORD; MOD_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `val (word_add pp (word r):A word) MOD (dimindex(:A) DIV 8) =
                val (word r:A word) MOD (dimindex(:A) DIV 8)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`word r:A word`; `word_add pp (word r):A word`]
      w2n_add_byte_align_lemma) THEN
    ASM_REWRITE_TAC[ISPECL [`word r:A word`; `pp:A word`] WORD_ADD_SYM]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    (try fst(dest_const(rator(lhs(concl th)))) = "byte_align" with Failure _ -> false))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq (concl th) &&
    is_var (lhs (concl th)) && fst (dest_var (lhs (concl th))) = "i")) THEN
  SUBGOAL_THEN `w = EL j (ws1:(A word)list)` SUBST_ALL_TAC THENL
   [FIRST_ASSUM(fun th ->
      let atom = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
        "misc_word_list" with Failure _ -> false) (concl th) in
      MP_TAC(SPEC `SUC j` (MATCH_MP (REWRITE_RULE[IMP_CONJ] MP5AUX_word_list_EL)
        (MP5AUX_SEP_FRONT_RULE atom th)))) THEN
    ASM_REWRITE_TAC[LENGTH; LENGTH_MAP; LT_SUC; EL; TL] THEN
    ASM_SIMP_TAC[EL_MAP; injectivity "word_loc"];
    ALL_TAC] THEN
  SUBGOAL_THEN `set_byte (word_add pp (word r)) b (EL j ws1) be =
                set_byte (word r) b (EL j (ws1:(A word)list)) be:A word` SUBST1_TAC THENL
   [MATCH_MP_TAC set_byte_change_a THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ws:(A word)list`; `bs:byte list`; `i:num`; `b:byte`; `be:bool`]
    MP5AUX_write_bytes_LUPDATE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LUPDATE_MAP] THEN
  SUBGOAL_THEN `!(y:A word_loc) l. CONS (wl_Word h) (LUPDATE y j l) =
                                   LUPDATE y (SUC j) (CONS (wl_Word h) l)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[LUPDATE_def]; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    let atom = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
      "misc_word_list" with Failure _ -> false) (concl th) in
    MP_TAC(SPECL [`SUC j`; `wl_Word (set_byte (word r) b (EL j ws1) be):A word_loc`]
      (MATCH_MP (REWRITE_RULE[IMP_CONJ] MP5AUX_word_list_LUPDATE)
        (MP5AUX_SEP_FRONT_RULE atom th)))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LENGTH; LENGTH_MAP; LT_SUC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th (asl,w) -> ACCEPT_TAC (MP5AUX_STAR_AC_RULE (rator w) th) (asl,w)));;

(* HOL4 line 11980 *)
let hide_memory_rel_def = new_definition
  `hide_memory_rel = memory_rel:data_to_word_config->bool->num->
     (data_v bvl_ref)spt->num->(store_name,A word_loc)fmap->
     (A word->A word_loc)->(A word->bool)->(data_v#A word_loc)list->bool`;;

(* HOL4 line 11984 *)
let hide_heap_in_memory_store_def = new_definition
  `hide_heap_in_memory_store =
     heap_in_memory_store:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
       heap_element)list->num->num->num->gen_state->data_to_word_config->
       (store_name,A word_loc)fmap->(A word->A word_loc)->(A word->bool)->num->bool`;;

(* Local helpers (MP5AUX_) for memory_rel_ByteArray_IMP *)
let MP5AUX_byte_aligned_add_mul = prove
 (`!(x:A word) n. good_dimindex(:A) /\ byte_aligned x ==>
     byte_aligned (word_add x (word_mul (word n) bytes_in_word))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_add x (word_mul (word n) bytes_in_word) =
                word_add x (word (n * 2 EXP LOG2 (dimindex(:A) DIV 8))):A word`
    SUBST1_TAC THENL
   [ASM_SIMP_TAC[MP5AUX_EXP_LOG2_BYTES] THEN REWRITE_TAC[bytes_in_word_def; WORD_MUL];
    ALL_TAC] THEN
  REWRITE_TAC[byte_aligned_def; aligned_add_pow] THEN
  ASM_REWRITE_TAC[GSYM byte_aligned_def]);;

let MP5AUX_ByteArray_layout = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl p v vars fl vals.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl p,v:A word_loc) vars) /\
     lookup p refs = SOME (bvl_ByteArray fl vals) /\ good_dimindex (:A) ==>
     ?w a ff.
       v = wl_Word w /\ bit 0 w /\ byte_aligned a /\
       get_real_simple_addr c st w = SOME a /\ get_real_addr c st w = SOME a /\
       m a = wl_Word (make_byte_header c fl (LENGTH vals)) /\ a IN dm /\
       data_to_word_config_len_size c + 7 < dimindex (:A) /\
       LENGTH vals + 2 EXP backend_common_word_shift(:A) <
         2 EXP (data_to_word_config_len_size c + backend_common_word_shift(:A)) /\
       (misc_word_list (word_add a bytes_in_word)
          (MAP wl_Word (write_bytes vals
             (REPLICATE (LENGTH vals DIV (dimindex(:A) DIV 8) + 1) (word 0)) be)) STAR ff)
         (fun2set (m,dm))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_memory_rel_HD) THEN
  MP5AUX_UNDISCH_HEAD "v_inv" THEN ASM_REWRITE_TAC[v_inv_def] THEN SIMP[] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN
  ASM_REWRITE_TAC[MP5AUX_reachable_refs_HD] THEN
  ASM_REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF] THEN
  SIMP[data_to_word_memoryProof_Bytes_def] THEN
  STRIP_TAC THEN MP5AUX_HEAP_EL_TAC THEN
  SIMP[word_payload_def; PAIR_EQ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `byte_aligned (curr:A word)` ASSUME_TAC THENL
   [MP5AUX_UNDISCH_HEAD "heap_in_memory_store" THEN
    REWRITE_TAC[heap_in_memory_store_def] THEN STRIP_TAC THEN
    UNDISCH_TAC `FLOOKUP st CurrHeap = SOME (wl_Word (curr:A word))` THEN
    ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP5AUX_SUBST_VAR_TAC "v" THEN MP5AUX_SUBST_VAR_TAC "h" THEN
  MAP_EVERY EXISTS_TAC
   [`get_addr c (FAPPLY (f:(num,num)fmap) p) (wl_Word (word 0)):A word`;
    `word_add curr (word_mul (word (FAPPLY (f:(num,num)fmap) p)) bytes_in_word):A word`] THEN
  MP5AUX_SEP_FRAME_EXISTS_TAC THEN
  ASM_SIMP_TAC[word_addr_def; get_addr_0; backend_common_word_shift_def;
               MP5AUX_byte_aligned_add_mul] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_heap_in_memory_store_IMP) THEN
  ASM_REWRITE_TAC[]);;

let MP5AUX_make_byte_header_ushr = prove
 (`!c fl len.
     data_to_word_config_len_size c + 7 < dimindex(:A) /\
     len + 2 EXP backend_common_word_shift(:A) <
       2 EXP (data_to_word_config_len_size c + backend_common_word_shift(:A)) ==>
     word_ushr (make_byte_header c fl len:A word)
       (dimindex(:A) - data_to_word_config_len_size c - backend_common_word_shift(:A)) =
     word (len + 2 EXP backend_common_word_shift(:A))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[MP5AUX_make_byte_header_word] THEN
  SUBGOAL_THEN `dimindex(:A) - data_to_word_config_len_size c - backend_common_word_shift(:A) =
                dimindex(:A) - backend_common_word_shift(:A) - data_to_word_config_len_size c`
    SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `backend_common_word_shift(:A) <= 3` ASSUME_TAC THENL
   [REWRITE_TAC[backend_common_word_shift_def] THEN COND_CASES_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `k = backend_common_word_shift(:A)` THEN
  ABBREV_TAC `s = dimindex(:A) - k - data_to_word_config_len_size c` THEN
  SUBGOAL_THEN `(if fl then 7 else 23) < 2 EXP s` ASSUME_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 5` THEN
    REWRITE_TAC[WORDSAUX_EXP2_LE] THEN CONJ_TAC THENL
     [COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP s * 2 EXP (data_to_word_config_len_size c + k) = dimword(:A)`
    ASSUME_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD; dimword_def] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  W(fun (asl,w) -> MP_TAC(ISPECL [rand(lhand(lhand w)); `s:num`]
    (INST_TYPE [`:A`,`:N`] n2w_DIV))) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MP5AUX_LT_MUL_ADD THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `if fl then 7 else 23` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* a byte read back from the words written from a byte list *)
let MP5AUX_get_byte_write_bytes = prove
 (`!(ws:(A word)list) bs i be.
     good_dimindex(:A) /\ i < LENGTH bs /\ i DIV (dimindex(:A) DIV 8) < LENGTH ws ==>
     get_byte (word (i MOD (dimindex(:A) DIV 8)))
       (EL (i DIV (dimindex(:A) DIV 8)) (write_bytes bs ws be)) be = EL i bs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH_RULE `~(n < 0)`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_good_dimindex_DIV8_LT) THEN
  SUBGOAL_THEN `0 < dimindex(:A) DIV 8` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[write_bytes_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_CASES_TAC `i < dimindex(:A) DIV 8` THENL
   [ASM_SIMP_TAC[DIV_LT; MOD_LT; EL; HD] THEN
    MP_TAC(ISPECL [`dimindex(:A) DIV 8`; `0`; `bs:byte list`; `h:A word`; `i:num`;
      `be:bool`] MP5AUX_get_byte_bytes_to_word) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; LE_REFL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`dimindex(:A) DIV 8`; `i:num`] MP5AUX_DIV_MOD_SUB) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[EL; TL] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`DROP (dimindex(:A) DIV 8) (bs:byte list)`;
    `i - dimindex(:A) DIV 8`; `be:bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_DROP] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LT_SUC]) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`i - dimindex(:A) DIV 8`; `dimindex(:A) DIV 8`; `bs:byte list`] EL_DROP) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let MP5AUX_ByteArray_byte = prove
 (`!(m:A word -> A word_loc) dm (a:A word) vals be ff i ws1.
     good_dimindex(:A) /\ byte_aligned a /\ i < LENGTH vals /\
     ws1 = write_bytes vals
             (REPLICATE (LENGTH vals DIV (dimindex(:A) DIV 8) + 1) (word 0)) be /\
     (misc_word_list (word_add a bytes_in_word) (MAP wl_Word ws1) STAR ff)
       (fun2set (m,dm)) ==>
     m (byte_align (word_add (word_add a bytes_in_word) (word i))) =
       wl_Word (EL (i DIV (dimindex(:A) DIV 8)) ws1) /\
     byte_align (word_add (word_add a bytes_in_word) (word i)) IN dm /\
     get_byte (word_add (word_add a bytes_in_word) (word i))
       (EL (i DIV (dimindex(:A) DIV 8)) ws1) be = EL i vals`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(dimindex(:A) DIV 8 = 0) /\ dimindex(:A) DIV 8 < dimword(:A)`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MP5AUX_good_dimindex_DIV8) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i DIV (dimindex(:A) DIV 8) <
                LENGTH (vals:byte list) DIV (dimindex(:A) DIV 8) + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x <= y ==> x < y + 1`) THEN MATCH_MP_TAC DIV_MONO THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `get_byte (word (i MOD (dimindex(:A) DIV 8)))
                  (EL (i DIV (dimindex(:A) DIV 8)) (ws1:(A word)list)) be = EL i (vals:byte list)`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MP5AUX_get_byte_write_bytes THEN
    ASM_REWRITE_TAC[LENGTH_REPLICATE]; ALL_TAC] THEN
  SUBGOAL_THEN `i MOD (dimindex(:A) DIV 8) < dimindex(:A) DIV 8` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOD_LT_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `word_add (word_add a bytes_in_word) (word i) =
                word_add (word_add (word_add a bytes_in_word)
                  (word_mul (word (i DIV (dimindex(:A) DIV 8))) bytes_in_word))
                  (word (i MOD (dimindex(:A) DIV 8))):A word` SUBST1_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
      [CONJUNCT1(SPEC `i:num` (MATCH_MP DIVISION th))]) THEN
    REWRITE_TAC[bytes_in_word_def; WORD_ADD; WORD_MUL] THEN MP5AUX_WORD_RULE_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `pp = word_add (word_add a bytes_in_word)
     (word_mul (word (i DIV (dimindex(:A) DIV 8))) bytes_in_word):A word` THEN
  ABBREV_TAC `r = i MOD (dimindex(:A) DIV 8)` THEN
  ABBREV_TAC `j = i DIV (dimindex(:A) DIV 8)` THEN
  SUBGOAL_THEN `byte_align (word_add pp (word r)) = pp:A word` ASSUME_TAC THENL
   [REWRITE_TAC[byte_align_def] THEN MATCH_MP_TAC align_add_aligned THEN
    ASM_SIMP_TAC[MP5AUX_EXP_LOG2_BYTES] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `pp = word_add a (word (SUC j * 2 EXP LOG2 (dimindex(:A) DIV 8))):A word`
        SUBST1_TAC THENL
       [ASM_SIMP_TAC[MP5AUX_EXP_LOG2_BYTES] THEN EXPAND_TAC "pp" THEN
        REWRITE_TAC[bytes_in_word_def; WORD_ADD; WORD_MUL; ADD1] THEN MP5AUX_WORD_RULE_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[aligned_add_pow] THEN ASM_REWRITE_TAC[GSYM byte_aligned_def];
      MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `r:num` THEN
      REWRITE_TAC[VAL_WORD; MOD_LE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `j < LENGTH (ws1:(A word)list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_write_bytes; LENGTH_REPLICATE]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq (concl th) &&
    is_var (lhs (concl th)) && fst (dest_var (lhs (concl th))) = "ws1")) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] MP5AUX_word_list_EL)) THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[LENGTH_MAP] THEN
  ASM_SIMP_TAC[EL_MAP] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`word r:A word`; `word_add pp (word r):A word`;
    `EL j (ws1:(A word)list)`; `be:bool`] get_byte_byte_align) THEN
  ASM_REWRITE_TAC[ISPECL [`word r:A word`; `pp:A word`] WORD_ADD_SYM]);;

let MP5AUX_ByteArray_update = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl p v vars fl vals w a i b w0.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl p,v:A word_loc) vars) /\
     lookup p refs = SOME (bvl_ByteArray fl vals) /\ good_dimindex (:A) /\
     v = wl_Word w /\ get_real_addr c st w = SOME a /\ i < LENGTH vals /\
     m (byte_align (word_add (word_add a bytes_in_word) (word i))) = wl_Word w0 ==>
     memory_rel c be ts (insert p (bvl_ByteArray fl (LUPDATE b i vals)) refs) sp st
       ((byte_align (word_add (word_add a bytes_in_word) (word i)) =+
         wl_Word (set_byte (word_add (word_add a bytes_in_word) (word i)) b w0 be)) m) dm
       (CONS (data_RefPtr bl p,v) vars)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `memory_rel c be ts refs sp st (m:A word -> A word_loc) dm
                 (CONS (data_RefPtr bl p,v:A word_loc) vars)` THEN
  REWRITE_TAC[memory_rel_def; word_ml_inv_def; MAP] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] update_byte_ref_thm)) THEN
  DISCH_THEN(MP_TAC o SPECL [`fl:bool`; `vals:byte list`; `LUPDATE (b:byte) i vals`]) THEN
  ASM_REWRITE_TAC[LENGTH_LUPDATE] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`roots2:(((A)word_loc)heap_address)list`;
    `h1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
    `h2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
    `ws:(A word)list`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`APPEND (APPEND h1 [Bytes be fl (LUPDATE (b:byte) i vals) (ws:(A word)list)]) h2`;
    `limit:num`; `a':num`; `sp':num`; `sp1:num`; `gens:gen_state`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [(SUBGOAL_THEN `?curr:A word. FLOOKUP st CurrHeap = SOME (wl_Word curr)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `heap_in_memory_store heap a' sp' sp1 gens c st
                   (m:A word -> A word_loc) dm limit` THEN
    REWRITE_TAC[heap_in_memory_store_def] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `w = get_addr c (heap_length
     (h1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list))
     (wl_Word (word 0)):A word` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `ALL2 (\v w. word_addr c v = w) hs
                   (CONS (v:A word_loc) (MAP SND (vars:(data_v#A word_loc)list)))` THEN
    ASM_REWRITE_TAC[ALL2; word_addr_def; injectivity "word_loc"] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a = word_add curr (word_mul (word (heap_length
     (h1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list)))
     bytes_in_word):A word` SUBST_ALL_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_heap_in_memory_store_IMP) THEN
    MP_TAC(ISPECL
     [`heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
      `c:data_to_word_config`;
      `heap_length
        (h1:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list)`;
      `Bytes be fl vals (ws:(A word)list)`; `st:(store_name,(A)word_loc)fmap`;
      `curr:A word`; `wl_Word (word 0):A word_loc`] get_real_addr_get_addr) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; heap_lookup_PREFIX]; ALL_TAC] THEN
    ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC heap_in_memory_store_UpdateByte THEN
  MAP_EVERY EXISTS_TAC
   [`heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
    `curr:A word`] THEN
  ASM_REWRITE_TAC[] THEN MP5AUX_WORD_RULE_TAC);
    EXISTS_TAC `hs:(((A)word_loc)heap_address)list` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (mp5aux_head_is "ALL2" o concl)) THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 11988 (the unused bound variable l of HOL4 is left out) *)
let memory_rel_ByteArray_IMP = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl p v vars fl vals.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl p,v:A word_loc) vars) /\
     lookup p refs = SOME (bvl_ByteArray fl vals) /\ good_dimindex (:A) ==>
     ?w a x.
       v = wl_Word w /\ bit 0 w /\
       make_byte_header c fl (LENGTH vals) = x /\
       ~bit 3 x /\ (bit 4 x <=> ~fl) /\ bit 2 x /\
       get_real_simple_addr c st w = SOME a /\
       get_real_addr c st w = SOME a /\
       m a = wl_Word x /\ a IN dm /\
       (!i. i < LENGTH vals ==>
            mem_load_byte_aux m dm be (word_add (word_add a bytes_in_word) (word i)) =
            SOME (EL i vals)) /\
       (!i w. i < LENGTH vals ==>
          let addr = word_add (word_add a bytes_in_word) (word i) in
          memory_rel c be ts (insert p (bvl_ByteArray fl (LUPDATE w i vals)) refs)
            sp st
            ((byte_align addr =+
              wl_Word (set_byte addr w (theWord (m (byte_align addr))) be)) m) dm
            (CONS (data_RefPtr bl p,v) vars)) /\
       if dimindex (:A) = 32 then
         LENGTH vals + 4 < 2 EXP (dimindex (:A) - 3) /\
         word_ushr x (dimindex (:A) - data_to_word_config_len_size c - 2) =
           word (LENGTH vals + 4)
       else
         LENGTH vals + 8 < 2 EXP (dimindex (:A) - 3) /\
         word_ushr x (dimindex (:A) - data_to_word_config_len_size c - 3) =
           word (LENGTH vals + 8)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`fl:bool`; `vals:byte list`] o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] MP5AUX_ByteArray_layout)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word` (X_CHOOSE_THEN `a:A word` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `LENGTH (vals:byte list) + 2 EXP backend_common_word_shift(:A) <
                2 EXP (dimindex(:A) - 3)` ASSUME_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `2 EXP (data_to_word_config_len_size c + backend_common_word_shift(:A))` THEN
    ASM_REWRITE_TAC[WORDSAUX_EXP2_LE] THEN REWRITE_TAC[backend_common_word_shift_def] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`w:A word`; `a:A word`;
    `make_byte_header c fl (LENGTH (vals:byte list)):A word`] THEN
  ASM_SIMP_TAC[MP5AUX_make_byte_header_bits] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`m:A word -> A word_loc`; `dm:A word->bool`; `a:A word`;
      `vals:byte list`; `be:bool`; `ff:((A word#A word_loc)->bool)->bool`; `i:num`;
      `write_bytes vals (REPLICATE (LENGTH (vals:byte list) DIV (dimindex(:A) DIV 8) + 1)
         (word 0)) be:(A word)list`] MP5AUX_ByteArray_byte) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[mem_load_byte_aux_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`i:num`; `b:byte`] THEN DISCH_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    MP_TAC(ISPECL [`m:A word -> A word_loc`; `dm:A word->bool`; `a:A word`;
      `vals:byte list`; `be:bool`; `ff:((A word#A word_loc)->bool)->bool`; `i:num`;
      `write_bytes vals (REPLICATE (LENGTH (vals:byte list) DIV (dimindex(:A) DIV 8) + 1)
         (word 0)) be:(A word)list`] MP5AUX_ByteArray_byte) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[theWord_def] THEN
    MATCH_MP_TAC MP5AUX_ByteArray_update THEN EXISTS_TAC `w:A word` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (mp5aux_head_is "memory_rel" o concl)) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`c:data_to_word_config`; `fl:bool`; `LENGTH (vals:byte list)`]
      MP5AUX_make_byte_header_ushr) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `LENGTH (vals:byte list) + 2 EXP backend_common_word_shift(:A) <
                 2 EXP (dimindex(:A) - 3)` THEN
    REWRITE_TAC[backend_common_word_shift_def] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[]]);;

(* HOL4 line 12265 *)
let memory_rel_RefPtr_IMP_lemma = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl p v vars.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl p,v:A word_loc) vars) ==>
     ?res. lookup p refs = SOME res`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_memory_rel_HD) THEN
  MP5AUX_UNDISCH_HEAD "v_inv" THEN REWRITE_TAC[v_inv_def] THEN STRIP_TAC THEN
  ASM_MESON_TAC[SUBSET; domain_lookup]);;

(* HOL4 line 12281 *)
let memory_rel_MutBlock_IMP_F = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm p v vars tg fin ls cv rs.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr T p,v:A word_loc) vars) /\
     lookup p refs = SOME (MutBlock tg fin ls cv rs) ==> F`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_memory_rel_HD) THEN
  MP5AUX_UNDISCH_HEAD "v_inv" THEN ASM_REWRITE_TAC[v_inv_RefPtr_T] THEN
  MESON_TAC[]);;

(* HOL4 line 12290 *)
let memory_rel_RefPtr_T_IMP = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm p v vars.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr T p,v) vars) /\
     good_dimindex (:A) ==>
     ?w a x.
       v = wl_Word w /\ bit 0 w /\
       (bit 3 x <=> ~bit 2 x) /\
       get_real_addr c st w = SOME a /\
       get_real_simple_addr c st w = SOME a /\
       m a = wl_Word (x:A word) /\ a IN dm`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `res:data_v bvl_ref` MP_TAC o
    MATCH_MP memory_rel_RefPtr_IMP_lemma) THEN
  STRUCT_CASES_TAC(ISPEC `res:data_v bvl_ref` (cases "bvl_ref")) THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
      `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
      `m:A word -> A word_loc`; `dm:A word->bool`; `T`; `p:num`; `v:A word_loc`;
      `vars:(data_v#A word_loc)list`; `a:data_v list`] memory_rel_ValueArray_IMP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:A word` (X_CHOOSE_THEN `a:A word`
      (X_CHOOSE_THEN `x:A word` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`w:A word`; `a:A word`; `x:A word`] THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
      `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
      `m:A word -> A word_loc`; `dm:A word->bool`; `T`; `p:num`; `v:A word_loc`;
      `vars:(data_v#A word_loc)list`; `a0:bool`; `a1:byte list`] memory_rel_ByteArray_IMP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:A word` (X_CHOOSE_THEN `a:A word`
      (X_CHOOSE_THEN `x:A word` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`w:A word`; `a:A word`; `x:A word`] THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
      `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
      `m:A word -> A word_loc`; `dm:A word->bool`; `T`; `p:num`; `v:A word_loc`;
      `vars:(data_v#A word_loc)list`; `a0:thunk_mode`; `a1:data_v`] memory_rel_Thunk_IMP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:A word` (X_CHOOSE_THEN `a:A word`
      (X_CHOOSE_THEN `x:A word` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`w:A word`; `a:A word`; `x:A word`] THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[memory_rel_MutBlock_IMP_F]]);;

(* HOL4 line 12311 *)
let memory_rel_RefPtr_IMP = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl p v vars.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl p,v) vars) /\
     good_dimindex (:A) /\
     (!t a. ~(lookup p refs = SOME (bvl_Thunk t a))) /\
     (!tg fin l cv rs. ~(lookup p refs = SOME (MutBlock tg fin l cv rs))) ==>
     ?w a x.
       v = wl_Word w /\ bit 0 w /\
       (bit 3 x <=> ~bit 2 x) /\
       get_real_addr c st w = SOME a /\
       get_real_simple_addr c st w = SOME a /\
       m a = wl_Word (x:A word) /\ a IN dm`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `res:data_v bvl_ref` MP_TAC o
    MATCH_MP memory_rel_RefPtr_IMP_lemma) THEN
  STRUCT_CASES_TAC(ISPEC `res:data_v bvl_ref` (cases "bvl_ref")) THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
      `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
      `m:A word -> A word_loc`; `dm:A word->bool`; `bl:bool`; `p:num`; `v:A word_loc`;
      `vars:(data_v#A word_loc)list`; `a:data_v list`] memory_rel_ValueArray_IMP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:A word` (X_CHOOSE_THEN `a:A word`
      (X_CHOOSE_THEN `x:A word` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`w:A word`; `a:A word`; `x:A word`] THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
      `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
      `m:A word -> A word_loc`; `dm:A word->bool`; `bl:bool`; `p:num`; `v:A word_loc`;
      `vars:(data_v#A word_loc)list`; `a0:bool`; `a1:byte list`] memory_rel_ByteArray_IMP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:A word` (X_CHOOSE_THEN `a:A word`
      (X_CHOOSE_THEN `x:A word` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`w:A word`; `a:A word`; `x:A word`] THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* HOL4 line 12330.  A MutBlock carries a BlockTag header, for which the     *)
(* bit pattern below does not hold; this theorem has no users, so the case *)
(* is left trivial (HOL4 comment)                                           *)
let memory_rel_RefPtr_gen_IMP = prove
 (CASE_TERM
  `!c be ts refs sp st (m:A word -> A word_loc) dm bl p v vars.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl p,v) vars) /\
     good_dimindex (:A) ==>
     ?r. lookup p refs = SOME r /\
         match r with
           bvl_Thunk Evaluated x ->
             (!w. v = wl_Word w /\ bit 0 w ==>
                  ?a x. get_real_addr c st w = SOME a /\
                        m a = wl_Word x /\ a IN dm /\
                        ~(word_and x (word 60) = word ((0 + 6) * 4)))
         | MutBlock _ _ _ _ _ -> T
         | _ ->
             (?w a x.
                v = wl_Word w /\ bit 0 w /\
                (bit 3 x <=> ~bit 2 x) /\
                get_real_addr c st w = SOME a /\
                get_real_simple_addr c st w = SOME a /\
                m a = wl_Word (x:A word) /\ a IN dm)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `res:data_v bvl_ref` ASSUME_TAC o
    MATCH_MP memory_rel_RefPtr_IMP_lemma) THEN
  EXISTS_TAC `res:data_v bvl_ref` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `lookup p refs = SOME (res:data_v bvl_ref)` THEN
  STRUCT_CASES_TAC(ISPEC `res:data_v bvl_ref` (cases "bvl_ref")) THEN DISCH_TAC THEN
  CASE_REWRITE_TAC[] THENL
  [MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
         `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
         `m:A word -> A word_loc`; `dm:A word->bool`; `bl:bool`; `p:num`; `v:A word_loc`;
         `vars:(data_v#A word_loc)list`; `a:data_v list`] memory_rel_ValueArray_IMP) THEN
       ASM_REWRITE_TAC[] THEN
       DISCH_THEN(X_CHOOSE_THEN `w:A word` (X_CHOOSE_THEN `a:A word`
         (X_CHOOSE_THEN `x:A word` STRIP_ASSUME_TAC))) THEN
       MAP_EVERY EXISTS_TAC [`w:A word`; `a:A word`; `x:A word`] THEN ASM_REWRITE_TAC[];
   MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
         `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
         `m:A word -> A word_loc`; `dm:A word->bool`; `bl:bool`; `p:num`; `v:A word_loc`;
         `vars:(data_v#A word_loc)list`; `a0:bool`; `a1:byte list`] memory_rel_ByteArray_IMP) THEN
       ASM_REWRITE_TAC[] THEN
       DISCH_THEN(X_CHOOSE_THEN `w:A word` (X_CHOOSE_THEN `a:A word`
         (X_CHOOSE_THEN `x:A word` STRIP_ASSUME_TAC))) THEN
       MAP_EVERY EXISTS_TAC [`w:A word`; `a:A word`; `x:A word`] THEN ASM_REWRITE_TAC[];
   MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
         `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
         `m:A word -> A word_loc`; `dm:A word->bool`; `bl:bool`; `p:num`; `v:A word_loc`;
         `vars:(data_v#A word_loc)list`; `a0:thunk_mode`; `a1:data_v`] memory_rel_Thunk_IMP) THEN
     ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `lookup p refs = SOME (bvl_Thunk a0 (a1:data_v))` THEN
     STRUCT_CASES_TAC(ISPEC `a0:thunk_mode` (cases "thunk_mode")) THEN
     CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "thunk_mode"] THEN
     DISCH_TAC THENL
   [STRIP_TAC THENL
       [X_GEN_TAC `w1:A word` THEN STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `w1:A word`) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[];
        X_GEN_TAC `w1:A word` THEN STRIP_TAC THEN
        SUBGOAL_THEN `w1:A word = w` SUBST_ALL_TAC THENL
         [ASM_MESON_TAC[injectivity "word_loc"]; ALL_TAC] THEN
        MAP_EVERY EXISTS_TAC [`a:A word`; `x:A word`] THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        DISCH_THEN(MP_TAC o AP_TERM `bit 5:A word->bool`) THEN
        REWRITE_TAC[BIT_WORD_AND; MP5AUX_BIT_WORD] THEN CONV_TAC(DEPTH_CONV MP5AUX_NUMBIT_CONV) THEN
        ASM_REWRITE_TAC[] THEN FIRST_ASSUM(MP_TAC o MATCH_MP MP5AUX_good_dimindex_DIV8_LT) THEN
        ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `w:A word` (X_CHOOSE_THEN `a:A word`
        (X_CHOOSE_THEN `x:A word` STRIP_ASSUME_TAC))) THEN
      MAP_EVERY EXISTS_TAC [`w:A word`; `a:A word`; `x:A word`] THEN ASM_REWRITE_TAC[]]]);;

(* HOL4 line 12368: Smallnum_bits *)
let data_to_word_memoryProof_Smallnum_bits = prove
 (`!i. word_and (word 1) (Smallnum i) = word 0:A word /\
       word_and (word 2) (Smallnum i) = word 0:A word`,
  GEN_TAC THEN REWRITE_TAC[MP5AUX_Smallnum_shl] THEN CONJ_TAC THEN
  MP5AUX_WORD_BITS_TAC THEN ARITH_TAC);;

(* HOL4 line 12377 *)
let memory_rel_any_Number_IMP = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i v vars.
     good_dimindex (:A) /\
     memory_rel c be ts refs sp st m dm (CONS (data_Number i,v:A word_loc) vars) ==>
     ?w. v = wl_Word w /\ (bit 0 w <=> ~small_int (:A) i)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_memory_rel_HD) THEN
  MP5AUX_UNDISCH_HEAD "v_inv" THEN REWRITE_TAC[v_inv_def] THEN
  COND_CASES_TAC THEN STRIP_TAC THEN
  MP5AUX_SUBST_VAR_TAC "v" THEN MP5AUX_SUBST_VAR_TAC "h" THEN
  ASM_REWRITE_TAC[word_addr_def; get_addr_0] THEN SIMP[get_addr_0] THEN
  REWRITE_TAC MP5AUX_BIT_RULES THEN CONV_TAC(DEPTH_CONV MP5AUX_NUMBIT_CONV) THEN
  MESON_TAC[]);;

(* HOL4 line 12391 *)
let memory_rel_Number_IMP = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i v vars.
     good_dimindex (:A) /\ small_int (:A) i /\
     memory_rel c be ts refs sp st m dm (CONS (data_Number i,v:A word_loc) vars) ==>
     v = wl_Word (Smallnum i)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_memory_rel_HD) THEN
  MP5AUX_UNDISCH_HEAD "v_inv" THEN ASM_REWRITE_TAC[v_inv_def] THEN
  DISCH_TAC THEN MP5AUX_SUBST_VAR_TAC "v" THEN MP5AUX_SUBST_VAR_TAC "h" THEN
  REWRITE_TAC[word_addr_def] THEN AP_TERM_TAC THEN REWRITE_TAC[MP5AUX_Smallnum_shl] THEN
  MP5AUX_WORD_BITS_TAC THEN ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* HOL4 line 12403 (the unused bound variable y of HOL4 is left out) *)
let memory_rel_Number_bignum_IMP_ALT = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i v vars.
     memory_rel c be ts refs sp st m dm (CONS (data_Number i,v) vars) /\
     ~small_int (:A) i /\ good_dimindex (:A) ==>
     ?ff w x a.
       v = wl_Word w /\ ~(word_and w (word 1) = (word 0:A word)) /\
       get_real_addr c st w = SOME a /\
       a IN dm /\ m a = wl_Word x /\ ~(word_and x (word 8) = word 0) /\
       bit 2 x /\ bit 3 x /\
       (bit 4 x <=> i < &0) /\
       (misc_word_list (word_add a bytes_in_word)
          (MAP wl_Word (n2mw (num_of_int (abs i)))) STAR ff) (fun2set (m,dm)) /\
       word_add a bytes_in_word IN dm /\
       m (word_add a bytes_in_word) = wl_Word (word (num_of_int (abs i))) /\
       (word_and x (word 16) = word 0 <=> &0 <= i) /\
       LENGTH (n2mw (num_of_int (abs i)):(A word)list) < 2 EXP (dimindex (:A) - 4) /\
       LENGTH (n2mw (num_of_int (abs i)):(A word)list) < dimword (:A) /\
       decode_length c x = word (LENGTH (n2mw (num_of_int (abs i)):(A word)list))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_memory_rel_HD) THEN
  MP5AUX_UNDISCH_HEAD "v_inv" THEN ASM_REWRITE_TAC[v_inv_def] THEN STRIP_TAC THEN
  MP5AUX_SUBST_VAR_TAC "v" THEN MP5AUX_SUBST_VAR_TAC "h" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_to_word_memoryProof_Bignum_def; i2mw_def; pair_CASE]) THEN
  MP5AUX_HEAP_EL_TAC THEN SIMP[word_payload_def; PAIR_EQ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(num_of_int (abs i) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `~small_int (:A) i` THEN UNDISCH_TAC `good_dimindex(:A)` THEN
    REWRITE_TAC[small_int_def; good_dimindex_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?ns. n2mw (num_of_int (abs i)) =
                     CONS (word (num_of_int (abs i))) ns:(A word)list`
    STRIP_ASSUME_TAC THENL
   [GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV) [n2mw_def] THEN
    ASM_REWRITE_TAC[CONS_11; n2w_mod] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_comb(rhs(concl th)) &&
     fst(dest_const(fst(strip_comb(rhs(concl th))))) = "CONS" &&
     fst(dest_const(fst(strip_comb(lhs(concl th))))) = "n2mw")) THEN
  MP5AUX_STAR_ASSUM(ASSUME_TAC o REWRITE_RULE[MAP; misc_word_list_def]) THEN
  MP5AUX_SEP_R_TAC THEN
  EXISTS_TAC `ff:(A word#A word_loc->bool)->bool` THEN
  MAP_EVERY EXISTS_TAC [`get_addr c ptr (wl_Word (word 0)):A word`;
     `make_header c (word_or (word_shl (b2w (i < &0)) 2) (word 3))
        (LENGTH (CONS (word (num_of_int (abs i))) ns:(A word)list)):A word`;
     `word_add curr (word_mul (word ptr) bytes_in_word):A word`] THEN
  ASM_REWRITE_TAC[word_addr_def] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_heap_in_memory_store_IMP) THEN
  SUBGOAL_THEN `4 < dimindex(:A)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MATCH_MP MP5AUX_word_and_1_8_16 (ASSUME `4 < dimindex(:A)`); get_addr_0] THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `(i:int) < &0`;
    `LENGTH (CONS (word (num_of_int (abs i))) ns:(A word)list)`]
    (INST_TYPE [`:A`,`:A`] MP5AUX_bignum_header_bits)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[INT_NOT_LT] THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP (dimindex (:A) - 4)` THEN
  ASM_REWRITE_TAC[dimword_def; WORDSAUX_EXP2_LE] THEN ARITH_TAC);;

(* HOL4 line 12461 (the unused bound variables ff x y of HOL4 are left out) *)
let memory_rel_Number_bignum_header = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i v vars.
     memory_rel c be ts refs sp st m dm (CONS (data_Number i,v:A word_loc) vars) /\
     ~small_int (:A) i /\ good_dimindex (:A) ==>
     ?w a.
       v = wl_Word w /\ get_real_addr c st w = SOME a /\
       IS_SOME (encode_header c
                  (val (word_or (word_shl (b2w (i < &0)) 2) (word 3):A word))
                  (LENGTH (n2mw (num_of_int (abs i)):(A word)list)):(A word)option) /\
       m a = wl_Word (make_header c (word_or (word_shl (b2w (i < &0)) 2) (word 3))
                        (LENGTH (n2mw (num_of_int (abs i)):(A word)list)))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_memory_rel_HD) THEN
  MP5AUX_UNDISCH_HEAD "v_inv" THEN ASM_REWRITE_TAC[v_inv_def] THEN STRIP_TAC THEN
  MP5AUX_SUBST_VAR_TAC "v" THEN MP5AUX_SUBST_VAR_TAC "h" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_to_word_memoryProof_Bignum_def; i2mw_def; pair_CASE]) THEN
  MP5AUX_HEAP_EL_TAC THEN SIMP[word_payload_def; PAIR_EQ] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`get_addr c ptr (wl_Word (word 0)):A word`;
     `word_add curr (word_mul (word ptr) bytes_in_word):A word`] THEN
  ASM_REWRITE_TAC[word_addr_def]);;

(* local helpers for memory_rel_bignum_cmp and memory_rel_Number_cmp,       *)
(* instead of ASM_MESON_TAC and ASM_ARITH_TAC over their 25-47 assumptions  *)
(* (each call took 3-14 s):                                                 *)
(* the goal by rewriting with r1 = r2 for the pairs of assumptions l = r1   *)
(* and l = r2 (a function read twice), simplified by injectivity and by the *)
(* iff assumptions                                                           *)
let MP5AUX_FUNC_EQ_TAC : tactic =
  let inj = [option_INJ; injectivity "word_loc"] in
  fun (asl,w as gl) ->
    let eqs = mapfilter (fun (_,th) -> if is_eq (concl th) then th else failwith "") asl in
    let rec pairs = function
        [] -> []
      | th::rest ->
          mapfilter (fun th2 ->
            if aconv (lhs (concl th)) (lhs (concl th2)) &&
               not (aconv (rhs (concl th)) (rhs (concl th2)))
            then TRANS (SYM th) th2 else failwith "") rest @ pairs rest in
    let iffs = filter (fun th -> type_of (lhs (concl th)) = bool_ty) eqs in
    let simp th =
      let th1 = REWRITE_RULE inj th in
      let th2 = REWRITE_RULE iffs th1 in
      if not (aconv (concl th2) (concl th1)) || not (is_eq (concl th1)) then th2
      else REWRITE_RULE iffs (SYM th1) in
    let news1 = map simp (pairs eqs) in
    (* a second round with the equations rewritten by the first-round facts *)
    (* (x = x' from m a = wl_Word x and m a' = wl_Word x' once a = a')       *)
    let vareqs = itlist (fun th acc ->
        let c = concl th in
        if is_eq c && is_var (lhs c) &&
           not (exists (fun t -> free_in (lhs c) (concl t) || free_in (rhs c) (concl t)) acc)
        then th::acc else acc) news1 [] in
    let news2 = if vareqs = [] then [] else
      map simp (pairs (map (REWRITE_RULE vareqs) eqs)) in
    (REWRITE_TAC (news1 @ news2) THEN NO_TAC) gl;;

(* ARITH_TAC with the integer facts among the assumptions only *)
let MP5AUX_INT_ARITH_TAC : tactic =
  let int_ty = `:int` in
  let rec intprop tm =
    if is_neg tm then intprop (rand tm) else
    if is_conj tm || is_disj tm || is_imp tm then intprop (lhand tm) && intprop (rand tm) else
    match tm with
      Comb(Comb(Const(("int_le"|"int_lt"|"int_ge"|"int_gt"|"="),_),a),_) -> type_of a = int_ty
    | _ -> false in
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (intprop o concl))) THEN ARITH_TAC;;

(* ASM_MESON_TAC thl after cheaper attempts: the functional consistency step  *)
(* above, then MESON with the equational assumptions only (on goals like       *)
(* x = x' from get_real_addr c st w = SOME a, m a = wl_Word x, w = w', ...,    *)
(* ASM_MESON_TAC took 3-14 s with all of them)                                 *)
let MP5AUX_FAST_MESON_TAC thl : tactic =
  MP5AUX_FUNC_EQ_TAC ORELSE
  (fun (asl,w as gl) ->
     MESON_TAC (thl @ filter (fun th -> is_eq (concl th)) (map snd asl)) gl) ORELSE
  ASM_MESON_TAC thl;;

(* ASM_MESON_TAC thl, first with the assumptions that mention the head      *)
(* constant of the goal only (chains like option_le a b, option_le b c:      *)
(* ASM_MESON_TAC[option_le_trans] took 15 s with all of them)                 *)
let MP5AUX_HEAD_MESON_TAC thl : tactic =
  (fun (asl,w as gl) ->
     let h = fst (strip_comb (if is_neg w then rand w else w)) in
     if not (is_const h) then failwith "MP5AUX_HEAD_MESON_TAC" else
     MESON_TAC (thl @ filter (fun th -> free_in h (concl th)) (map snd asl)) gl) ORELSE
  ASM_MESON_TAC thl;;

(* ASM_ARITH_TAC on each conjunct of the goal with fewer facts (the          *)
(* conjuncts of the arithmetic assumptions): first those whose atoms all     *)
(* occur in the goal, then those near it (sharing an atom with it or with    *)
(* such a fact), then all assumptions.  With all of them, ARITH_TAC took     *)
(* 9-40 s on goals of the data_to_word proofs.                               *)
let MP5AUX_ARITH_TAC : tactic =
  let num_ty = `:num` in
  let rec atoms tm = match tm with
      Comb(Comb(Const(("+"|"-"|"*"|"DIV"|"MOD"|"<="|"<"|">="|">"|"/\\"|"\\/"|"==>"),_),a),b) ->
        union (atoms a) (atoms b)
    | Comb(Comb(Const("=",_),a),b) -> union (atoms a) (atoms b)
    | Comb(Const("~",_),a) -> atoms a
    | Comb(Comb(Comb(Const("COND",_),c),a),b) -> union (atoms c) (union (atoms a) (atoms b))
    | _ -> if is_numeral tm || is_const tm && type_of tm = bool_ty then [] else [tm] in
  let rec isarith tm =
    if is_neg tm then isarith (rand tm) else
    if is_conj tm || is_disj tm || is_imp tm then isarith (lhand tm) && isarith (rand tm) else
    match tm with
      Comb(Comb(Const(("<="|"<"|">="|">"),_),a),_) -> type_of a = num_ty
    | Comb(Comb(Const("=",_),a),_) -> type_of a = num_ty
    | _ -> false in
  let facts asl = mapfilter (fun th -> let c = concl th in
                               if isarith c then (th,atoms c) else failwith "")
                            (flat (map (CONJUNCTS o snd) asl)) in
  (* the atoms of the goal; for the goal F, those of the newest arithmetic fact *)
  let seed afs w =
    match atoms w, afs with
      [],(_,a)::_ -> a
    | ws,_ -> ws in
  let within_tac (asl,w as gl) =
    let afs = facts asl in
    let ws = seed afs w in
    (MAP_EVERY (MP_TAC o fst) (filter (fun (_,a) -> subset a ws) afs) THEN ARITH_TAC) gl in
  let near_tac (asl,w as gl) =
    let afs = facts asl in
    let near ats = filter (fun (_,a) -> intersect a ats <> []) afs in
    let ws = seed afs w in
    let ats1 = itlist (union o snd) (near ws) ws in
    (MAP_EVERY (MP_TAC o fst) (near ats1) THEN ARITH_TAC) gl in
  REPEAT CONJ_TAC THEN (within_tac ORELSE near_tac ORELSE ASM_ARITH_TAC);;

(* HOL4 line 12484 *)
let memory_rel_bignum_cmp = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i1 v1 i2 v2 vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number i1,v1) (CONS (data_Number i2,v2:A word_loc) vars)) /\
     good_dimindex (:A) /\ ~small_int (:A) i1 /\ ~small_int (:A) i2 ==>
     ?w1 w2 a1 a2 x1 x2.
       v1 = wl_Word w1 /\ v2 = wl_Word w2 /\
       get_real_addr c st w1 = SOME a1 /\
       get_real_addr c st w2 = SOME a2 /\
       m a1 = wl_Word x1 /\
       m a2 = wl_Word x2 /\
       (~(x1 = x2) ==>
        decode_length c x1 = decode_length c x2 ==>
        ~((word_and (word 16) x1 = word 0) <=> (word_and (word 16) x2 = word 0)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tail) THEN
  MAP_EVERY (fun th -> MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,(A)word_loc)fmap`; `m:A word -> A word_loc`;
    `dm:A word->bool`; `i1:int`; `v1:A word_loc`;
    `CONS (data_Number i2,v2:A word_loc) vars`] th))
    [memory_rel_Number_bignum_header; memory_rel_Number_bignum_IMP_ALT] THEN
  MAP_EVERY (fun th -> MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,(A)word_loc)fmap`; `m:A word -> A word_loc`;
    `dm:A word->bool`; `i2:int`; `v2:A word_loc`; `vars:(data_v#(A)word_loc)list`] th))
    [memory_rel_Number_bignum_header; memory_rel_Number_bignum_IMP_ALT] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`w'':A word`; `w:A word`; `a'':A word`; `a:A word`;
                       `x':A word`; `x:A word`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(x':A word) = make_header c (word_or (word_shl (b2w (i1 < &0)) 2) (word 3))
           (LENGTH (n2mw (num_of_int (abs i1)):(A word)list)) /\
    (x:A word) = make_header c (word_or (word_shl (b2w (i2 < &0)) 2) (word 3))
           (LENGTH (n2mw (num_of_int (abs i2)):(A word)list))`
    MP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      let l,r = dest_eq(concl th) in
      is_var l && (fst(dest_var l) = "v1" || fst(dest_var l) = "v2")))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "word_loc"]) THEN
    MP5AUX_FAST_MESON_TAC[injectivity "word_loc"; option_INJ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(word (LENGTH (n2mw (num_of_int (abs i1)):(A word)list)):A word =
     word (LENGTH (n2mw (num_of_int (abs i2)):(A word)list)) <=>
     LENGTH (n2mw (num_of_int (abs i1)):(A word)list) =
     LENGTH (n2mw (num_of_int (abs i2)):(A word)list))` SUBST1_TAC THENL
   [REWRITE_TAC[n2w_11] THEN ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `4 < dimindex(:A)` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MATCH_MP MP5AUX_word_and_1_8_16 (ASSUME `4 < dimindex(:A)`)] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[TAUT `(~a <=> ~b) <=> (a <=> b)`] THEN
  ASM_CASES_TAC `(i1:int) < &0 <=> (i2:int) < &0` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 12510 (the unused bound variable y of HOL4 is left out) *)
let memory_rel_Number_bignum_IMP = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i v vars.
     memory_rel c be ts refs sp st m dm (CONS (data_Number i,v) vars) /\
     ~small_int (:A) i /\ good_dimindex (:A) ==>
     ?w x a.
       v = wl_Word w /\ ~(word_and w (word 1) = (word 0:A word)) /\
       get_real_addr c st w = SOME a /\
       a IN dm /\ m a = wl_Word x /\ ~(word_and x (word 8) = word 0) /\
       word_add a bytes_in_word IN dm /\
       m (word_add a bytes_in_word) = wl_Word (word (num_of_int (abs i))) /\
       (word_and x (word 16) = word 0 <=> &0 <= i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL memory_rel_Number_bignum_IMP_ALT) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`w:A word`; `x:A word`; `a:A word`] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 12524 *)
let memory_rel_Word64_IMP = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm w64 v vars.
     memory_rel c be ts refs sp st m dm (CONS (data_Word64 w64,v:A word_loc) vars) /\
     good_dimindex (:A) ==>
     ?ptr x w.
       v = wl_Word (get_addr c ptr (wl_Word (word 0))) /\
       get_real_addr c st (get_addr c ptr (wl_Word (word 0))) = SOME x /\
       x IN dm /\ m x = wl_Word w /\ bit 3 w /\ ~bit 4 w /\ bit 2 w /\
       word_add x bytes_in_word IN dm /\
       if dimindex (:A) < 64 then
         (m (word_add x bytes_in_word) = wl_Word (word_extract 63 32 w64) /\
          word_add x (word_shl bytes_in_word 1) IN dm /\
          m (word_add x (word_shl bytes_in_word 1)) = wl_Word (word_extract 31 0 w64) /\
          decode_length c w = word 2 /\
          w = make_header c (word 3) 2)
       else
         m (word_add x bytes_in_word) = wl_Word (word_extract 63 0 w64) /\
         decode_length c w = word 1 /\
         w = make_header c (word 3) 1`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_memory_rel_HD) THEN
  MP5AUX_UNDISCH_HEAD "v_inv" THEN ASM_REWRITE_TAC[v_inv_def] THEN STRIP_TAC THEN
  MP5AUX_SUBST_VAR_TAC "v" THEN MP5AUX_SUBST_VAR_TAC "h" THEN
  EXISTS_TAC `ptr:num` THEN REWRITE_TAC[word_addr_def] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_heap_in_memory_store_IMP) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    mp5aux_head_is "heap_lookup" (lhs (concl th)))) THEN
  REWRITE_TAC[Word64Rep_def] THEN
  ASM_CASES_TAC `dimindex(:A) < 64` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP5AUX_HEAP_EL_TAC THEN SIMP[word_payload_def; PAIR_EQ] THEN STRIP_TAC THEN
  MP5AUX_STAR_ASSUM(ASSUME_TAC o REWRITE_RULE[MAP; misc_word_list_def]) THEN
  MP5AUX_SEP_R_TAC THEN
  EXISTS_TAC `word_add curr (word_mul (word ptr) bytes_in_word):A word` THEN
  ASM_REWRITE_TAC[LSL_ONE; WORD_ADD_ASSOC] THEN
  ASM_SIMP_TAC[MP5AUX_make_header_bit;
    ARITH_RULE `x + 7 < d ==> 3 < d - x /\ 2 < d - x /\ 4 < d - x`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MP5AUX_BIT_WORD] THEN
  CONV_TAC(DEPTH_CONV MP5AUX_NUMBIT_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[good_dimindex_def]) THEN ASM_ARITH_TAC);;

(* HOL4 line 12568 *)
let IMP_memory_rel_Number_num3 = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars n.
     good_dimindex (:A) /\ n < 2 EXP (dimindex (:A) - 3) /\
     memory_rel c be ts refs sp st m dm vars ==>
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number (&n),wl_Word (word_shl (word n) 2:A word)) vars)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_shl (word n) 2 = Smallnum (&n):A word` SUBST1_TAC THENL
   [REWRITE_TAC[data_to_word_Smallnum_def; INT_ARITH `~(&n:int < &0)`; WORD_SHL_WORD;
                INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM] THEN
    AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC IMP_memory_rel_Number THEN ASM_REWRITE_TAC[small_int_def] THEN
  UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[INT_OF_NUM_LT; INT_ARITH `-- &a <= &n:int`] THEN ASM_ARITH_TAC);;

(* HOL4 line 12581 *)
let IMP_memory_rel_Number_num = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars n.
     good_dimindex (:A) /\ n < 2 EXP (dimindex (:A) - 4) /\
     memory_rel c be ts refs sp st m dm vars ==>
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number (&n),wl_Word (word_shl (word n) 2:A word)) vars)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IMP_memory_rel_Number_num3 THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `2 EXP (dimindex (:A) - 4)` THEN
  ASM_REWRITE_TAC[WORDSAUX_EXP2_LE] THEN ARITH_TAC);;

(* HOL4 line 12594 *)
let memory_rel_Number_EQ = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i1 w1 i2 w2 vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number i1,w1) (CONS (data_Number i2,w2) vars)) /\
     (small_int (:A) i1 \/ small_int (:A) i2) /\
     good_dimindex (:A) ==>
     ?v1 v2. w1 = wl_Word v1 /\ w2 = wl_Word (v2:A word) /\ (v1 = v2 <=> i1 = i2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tail) THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,(A)word_loc)fmap`; `m:A word -> A word_loc`;
    `dm:A word->bool`; `i1:int`; `w1:A word_loc`;
    `CONS (data_Number i2,w2:A word_loc) vars`] memory_rel_any_Number_IMP) THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,(A)word_loc)fmap`; `m:A word -> A word_loc`;
    `dm:A word->bool`; `i2:int`; `w2:A word_loc`; `vars:(data_v#(A)word_loc)list`]
    memory_rel_any_Number_IMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v2:A word` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:A word` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`v1:A word`; `v2:A word`] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `small_int (:A) i1` THEN ASM_CASES_TAC `small_int (:A) i2` THENL
   [MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
      `sp:num`; `st:(store_name,(A)word_loc)fmap`; `m:A word -> A word_loc`;
      `dm:A word->bool`; `i1:int`; `w1:A word_loc`;
      `CONS (data_Number i2,w2:A word_loc) vars`] memory_rel_Number_IMP) THEN
    MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
      `sp:num`; `st:(store_name,(A)word_loc)fmap`; `m:A word -> A word_loc`;
      `dm:A word->bool`; `i2:int`; `w2:A word_loc`; `vars:(data_v#(A)word_loc)list`]
      memory_rel_Number_IMP) THEN
    ASM_REWRITE_TAC[injectivity "word_loc"] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN ASM_SIMP_TAC[MP5AUX_Smallnum_11];
    MATCH_MP_TAC(TAUT `~a /\ ~b ==> (a <=> b)`) THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC(TAUT `~a /\ ~b ==> (a <=> b)`) THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* HOL4 line 12618 *)
let memory_rel_Number_LESS = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i1 w1 i2 w2 vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number i1,w1) (CONS (data_Number i2,w2) vars)) /\
     small_int (:A) i1 /\
     small_int (:A) i2 /\
     good_dimindex (:A) ==>
     ?v1 v2. w1 = wl_Word v1 /\ w2 = wl_Word v2 /\
             (word_ilt v1 (v2:A word) <=> i1 < i2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tail) THEN
  MAP_EVERY EXISTS_TAC [`Smallnum i1:A word`; `Smallnum i2:A word`] THEN
  ASM_MESON_TAC[memory_rel_Number_IMP; num_less_thm]);;

(* HOL4 line 12633 *)
let memory_rel_Number_LESS_EQ = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i1 w1 i2 w2 vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number i1,w1) (CONS (data_Number i2,w2) vars)) /\
     small_int (:A) i1 /\
     small_int (:A) i2 /\
     good_dimindex (:A) ==>
     ?v1 v2. w1 = wl_Word v1 /\ w2 = wl_Word v2 /\
             (word_ile v1 (v2:A word) <=> i1 <= i2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tail) THEN
  MAP_EVERY EXISTS_TAC [`Smallnum i1:A word`; `Smallnum i2:A word`] THEN
  REWRITE_TAC[WORD_LESS_OR_EQ; INT_LE_LT] THEN
  ASM_MESON_TAC[memory_rel_Number_IMP; num_less_thm; MP5AUX_Smallnum_11]);;

(* HOL4 line 12646 *)
let memory_rel_Number_word_msb = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i1 w vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number i1,wl_Word (w:A word)) vars) /\
     good_dimindex(:A) /\ small_int (:A) i1 ==>
     (word_msb w <=> i1 < &0)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    (ONCE_REWRITE_RULE[CONJ_ASSOC] memory_rel_Number_IMP))) THEN
  ASM_REWRITE_TAC[injectivity "word_loc"] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[MP5AUX_word_msb_Smallnum]);;

(* HOL4 line 12660 *)
let memory_rel_RefPtr_EQ_lemma = prove
 (`!n m k.
     n * 2 EXP k < dimword (:A) /\ m * 2 EXP k < dimword (:A) /\ 0 < k /\
     word_or (word_shl (word n) k) (word 1) =
     word_or (word_shl (word m) k) (word 1:A word) ==> n = m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_shl (word n) k = word_shl (word m) k:A word` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      mp5aux_head_is "word_or" (lhs (concl th)))) THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT] THEN REWRITE_TAC MP5AUX_BIT_RULES THEN
    CONV_TAC(DEPTH_CONV MP5AUX_NUMBIT_CONV) THEN
    DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    REWRITE_TAC[WORD_SHL_WORD; n2w_11] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_LT] THEN
    REWRITE_TAC[EQ_MULT_RCANCEL; EXP_EQ_0] THEN ARITH_TAC]);;

(* HOL4 line 12677 *)
let memory_rel_RefPtr_EQ = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i1 w1 i2 w2 vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_RefPtr T i1,w1) (CONS (data_RefPtr T i2,w2) vars)) /\
     good_dimindex (:A) ==>
     ?v1 v2. w1 = wl_Word v1 /\ w2 = wl_Word (v2:A word) /\ (v1 = v2 <=> i1 = i2)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_memory_rel_HD2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_inv_RefPtr_T]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  MP5AUX_SUBST_VAR_TAC "w1" THEN MP5AUX_SUBST_VAR_TAC "w2" THEN
  MP5AUX_SUBST_VAR_TAC "h1" THEN MP5AUX_SUBST_VAR_TAC "h2" THEN
  REWRITE_TAC[word_addr_def; injectivity "word_loc"] THEN
  MAP_EVERY EXISTS_TAC
   [`get_addr c (FAPPLY (f:(num,num)fmap) i1) (wl_Word (word 0)):A word`;
    `get_addr c (FAPPLY (f:(num,num)fmap) i2) (wl_Word (word 0)):A word`] THEN
  REWRITE_TAC[] THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REWRITE_TAC[MP5AUX_get_addr_word0] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`FAPPLY (f:(num,num)fmap) i1`; `FAPPLY (f:(num,num)fmap) i2`;
    `shift_length c`] (INST_TYPE [`:A`,`:A`] memory_rel_RefPtr_EQ_lemma)) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MP5AUX_FAPPLY_BOUND; INJ; shift_length_def; ARITH_RULE `0 < x + 1`]);;

(* HOL4 line 12709 *)
let memory_rel_RefPtr_EQ_IMP = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) (dm:A word->bool) b1 i1 w1 b2 w2
    vars ys_fl ys.
     memory_rel c be ts refs sp st m dm
       (CONS (data_RefPtr b1 i1,wl_Word w1) (CONS (data_RefPtr b2 i1,wl_Word w2) vars)) /\
     good_dimindex (:A) /\
     lookup i1 refs = SOME (bvl_ByteArray ys_fl ys) ==>
     w1 = w2`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_memory_rel_HD2) THEN
  REPEAT(MP5AUX_UNDISCH_HEAD "v_inv") THEN ASM_REWRITE_TAC[v_inv_def] THEN SIMP[] THEN
  REPEAT STRIP_TAC THEN
  MP5AUX_SUBST_VAR_TAC "h1" THEN MP5AUX_SUBST_VAR_TAC "h2" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_addr_def; injectivity "word_loc"]) THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 12720 *)
let memory_rel_Boolv_T = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars.
     memory_rel c be ts refs sp st m dm vars /\ good_dimindex (:A)
     ==> memory_rel c be ts refs sp st m dm
           (CONS (data_Boolv T,wl_Word (word 18:A word)) vars)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[memory_rel_def; word_ml_inv_def] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`heap:(((A)word_loc,data_to_word_memoryProof_tag#
                                ((A)word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp':num`; `sp1:num`; `gens:gen_state`] THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `CONS (gc_shared_Data (wl_Word (BlockNil 1:A word))) hs` THEN
  REWRITE_TAC[MAP; ALL2] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[data_Boolv_def; bool_to_tag_def; true_tag_def] THEN
    MATCH_MP_TAC cons_thm_EMPTY THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `good_dimindex(:A)` THEN
    REWRITE_TAC[good_dimindex_def; dimword_def] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[word_addr_def; BlockNil_def; injectivity "word_loc";
                WORD_SHL_WORD; word_add_n2w] THEN
    CONV_TAC NUM_REDUCE_CONV THEN MP5AUX_WORD_BITS_TAC THEN
    MP5AUX_BITS_ARITH_TAC]);;

(* HOL4 line 12733 *)
let memory_rel_Boolv_F = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars.
     memory_rel c be ts refs sp st m dm vars /\ good_dimindex (:A)
     ==> memory_rel c be ts refs sp st m dm
           (CONS (data_Boolv F,wl_Word (word 2:A word)) vars)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[memory_rel_def; word_ml_inv_def] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`heap:(((A)word_loc,data_to_word_memoryProof_tag#
                                ((A)word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp':num`; `sp1:num`; `gens:gen_state`] THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `CONS (gc_shared_Data (wl_Word (BlockNil 0:A word))) hs` THEN
  REWRITE_TAC[MAP; ALL2] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[data_Boolv_def; bool_to_tag_def; false_tag_def] THEN
    MATCH_MP_TAC cons_thm_EMPTY THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `good_dimindex(:A)` THEN
    REWRITE_TAC[good_dimindex_def; dimword_def] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[word_addr_def; BlockNil_def; injectivity "word_loc";
                WORD_SHL_WORD; word_add_n2w] THEN
    CONV_TAC NUM_REDUCE_CONV THEN MP5AUX_WORD_BITS_TAC THEN
    MP5AUX_BITS_ARITH_TAC]);;

(* HOL4 line 12746 *)
let memory_rel_Boolv = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars b v.
     memory_rel c be ts refs sp st m dm vars /\ good_dimindex (:A) /\
     (b ==> v = wl_Word (word 18)) /\ (~b ==> v = wl_Word (word 2:A word)) ==>
     memory_rel c be ts refs sp st m dm (CONS (data_Boolv b,v) vars)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[memory_rel_Boolv_T; memory_rel_Boolv_F]);;

(* HOL4 line 12756 *)
let word_ml_inv_SP_LIMIT = prove
 (`!heap be a sp sp1 gens limit ts c refs (stack:(data_v#A word_loc)list).
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs stack ==> sp <= limit`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_ml_inv_def; abs_ml_inv_def; heap_ok_def; unused_space_inv_def] THEN
  STRIP_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 12767 (val) *)
let lt8 = prove
 (`!n. n < 8 <=> n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/
                 n = 4 \/ n = 5 \/ n = 6 \/ n = 7`,
  ARITH_TAC);;

(* HOL4 line 12771: Smallnum_test *)
let data_to_word_memoryProof_Smallnum_test = prove
 (`!i. word_and (Smallnum i) (word_shl (word_neg (word 1)) (dimindex (:A) - 2)) =
       word 0:A word /\
       good_dimindex (:A) /\ small_int (:A) i ==>
       ~(i < &0) /\ i < &2 pow (dimindex (:A) - 4)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~bit (dimindex(:A) - 1) (Smallnum i:A word) /\
                ~bit (dimindex(:A) - 2) (Smallnum i:A word)` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; WORD_NEG_1] THEN REWRITE_TAC MP5AUX_BIT_RULES THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `dimindex(:A) - 1` th) THEN
                         MP_TAC(SPEC `dimindex(:A) - 2` th)) THEN
    UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(i:int < &0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MP5AUX_word_msb_Smallnum; word_msb_def]; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `?n. (i:int) = &n` (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `num_of_int (i:int)` THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_to_word_memoryProof_Smallnum_i2w; INT_OF_NUM_MUL; GSYM WORD_IWORD;
                              MP5AUX_BIT_WORD; small_int_def; dimword_def]) THEN
  MP_TAC(SPECL [`4 * n`; `dimindex(:A) - 2`] MP5AUX_LT_TOP_BITS) THEN
  UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(NUM_REDUCE_CONV THENC INT_REDUCE_CONV)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_LT; INT_ARITH `-- &a <= &b:int`]) THEN
  ASM_ARITH_TAC);;

(* HOL4 line 12843 *)
let small_int_w2i_i2w = prove
 (`!i. small_int (:A) i /\ good_dimindex (:A) ==>
       ival (iword (&4 * i):A word) = &4 * i`,
  REWRITE_TAC[GSYM data_to_word_memoryProof_Smallnum_i2w] THEN MESON_TAC[MP5AUX_ival_Smallnum]);;

(* HOL4 line 12853 *)
let memory_rel_Add = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i wi j wj vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number i,wl_Word wi) (CONS (data_Number j,wl_Word wj) vars)) /\
     ~bit 0 wi /\ ~bit 0 wj /\
     good_dimindex (:A) /\ ival (word_add wi wj) = ival wi + ival wj ==>
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number (i + j),wl_Word (word_add wi wj:A word)) vars)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tail) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tail) THEN
  SUBGOAL_THEN `small_int (:A) i /\ small_int (:A) j` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[memory_rel_any_Number_IMP; injectivity "word_loc"]; ALL_TAC] THEN
  SUBGOAL_THEN `wi = Smallnum i:A word /\ wj = Smallnum j:A word`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [ASM_MESON_TAC[memory_rel_Number_IMP; injectivity "word_loc"]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_to_word_memoryProof_Smallnum_i2w; GSYM IWORD_INT_ADD]) THEN
  REWRITE_TAC[data_to_word_memoryProof_Smallnum_i2w; GSYM IWORD_INT_ADD;
              INT_ARITH `&4 * (i + j):int = &4 * i + &4 * j`] THEN
  REWRITE_TAC[GSYM INT_ADD_LDISTRIB; GSYM data_to_word_memoryProof_Smallnum_i2w] THEN
  MATCH_MP_TAC IMP_memory_rel_Number THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MP5AUX_small_int_ival] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    mp5aux_head_is "ival" (lhs (concl th)))) THEN
  ASM_SIMP_TAC[GSYM data_to_word_memoryProof_Smallnum_i2w; MP5AUX_ival_Smallnum; INT_ADD_LDISTRIB] THEN
  REWRITE_TAC[data_to_word_memoryProof_Smallnum_i2w; GSYM IWORD_INT_ADD] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IVAL_BOUND]);;

(* HOL4 line 12879 *)
let memory_rel_Sub = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i wi j wj vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number i,wl_Word wi) (CONS (data_Number j,wl_Word wj) vars)) /\
     ~bit 0 wi /\ ~bit 0 wj /\
     good_dimindex (:A) /\ ival (word_sub wi wj) = ival wi - ival wj ==>
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number (i - j),wl_Word (word_sub wi wj:A word)) vars)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tail) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tail) THEN
  SUBGOAL_THEN `small_int (:A) i /\ small_int (:A) j` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[memory_rel_any_Number_IMP; injectivity "word_loc"]; ALL_TAC] THEN
  SUBGOAL_THEN `wi = Smallnum i:A word /\ wj = Smallnum j:A word`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [ASM_MESON_TAC[memory_rel_Number_IMP; injectivity "word_loc"]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_to_word_memoryProof_Smallnum_i2w; GSYM IWORD_INT_SUB]) THEN
  REWRITE_TAC[data_to_word_memoryProof_Smallnum_i2w; GSYM IWORD_INT_SUB] THEN
  REWRITE_TAC[GSYM INT_SUB_LDISTRIB; GSYM data_to_word_memoryProof_Smallnum_i2w] THEN
  MATCH_MP_TAC IMP_memory_rel_Number THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MP5AUX_small_int_ival] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    mp5aux_head_is "ival" (lhs (concl th)))) THEN
  ASM_SIMP_TAC[GSYM data_to_word_memoryProof_Smallnum_i2w; MP5AUX_ival_Smallnum; INT_SUB_LDISTRIB] THEN
  REWRITE_TAC[data_to_word_memoryProof_Smallnum_i2w; GSYM IWORD_INT_SUB] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IVAL_BOUND]);;

(* HOL4 line 12905 *)
let exists_num = prove
 (`!i:int. ~(i < &0) <=> ?n. i = &n`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC NUM_POSINT_EXISTS THEN ASM_ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[INT_POS; INT_NOT_LT]]);;

(* HOL4 line 12911 *)
let small_int_w2n = prove
 (`!w:byte. good_dimindex (:A) ==> small_int (:A) (&(val w))`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def; small_int_def; dimword_def] THEN
  MP_TAC(ISPEC `w:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[INT_OF_NUM_LT; INT_ARITH `-- &a <= &b:int`] THEN
  ASM_ARITH_TAC);;
let _ = cake_add_simps [small_int_w2n];;

(* HOL4 line 12919 *)
let memory_rel_And = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm (i:byte) wi j wj vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number (&(val i)),wl_Word wi)
             (CONS (data_Number (&(val j)),wl_Word wj) vars)) /\
     good_dimindex (:A) ==>
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number (&(val (word_and i j))),wl_Word (word_and wi wj:A word))
             vars)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tail) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tail) THEN
  SUBGOAL_THEN `wi = Smallnum (&(val (i:byte))):A word /\
                wj = Smallnum (&(val (j:byte))):A word`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [ASM_MESON_TAC[memory_rel_Number_IMP; small_int_w2n; injectivity "word_loc"];
    ALL_TAC] THEN
  SUBGOAL_THEN `word_and (Smallnum (&(val (i:byte)))) (Smallnum (&(val (j:byte)))) =
                Smallnum (&(val (word_and i j))):A word` SUBST1_TAC THENL
   [REWRITE_TAC[MP5AUX_Smallnum_val_byte; WORD_EQ_BITS_ALT] THEN
    REWRITE_TAC[BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_XOR; BIT_WORD_SHL;
                MP5AUX_bit_word_val_byte] THEN
    REWRITE_TAC[BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_XOR; DIMINDEX_8] THEN
    ONCE_REWRITE_TAC[word_bit_thm] THEN REWRITE_TAC[DIMINDEX_8] THEN
    GEN_TAC THEN MP5AUX_BITS_ARITH_TAC;
    MATCH_MP_TAC IMP_memory_rel_Number THEN ASM_SIMP_TAC[small_int_w2n]]);;

(* HOL4 line 12948 *)
let memory_rel_Or = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm (i:byte) wi j wj vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number (&(val i)),wl_Word wi)
             (CONS (data_Number (&(val j)),wl_Word wj) vars)) /\
     good_dimindex (:A) ==>
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number (&(val (word_or i j))),wl_Word (word_or wi wj:A word))
             vars)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tail) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tail) THEN
  SUBGOAL_THEN `wi = Smallnum (&(val (i:byte))):A word /\
                wj = Smallnum (&(val (j:byte))):A word`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [ASM_MESON_TAC[memory_rel_Number_IMP; small_int_w2n; injectivity "word_loc"];
    ALL_TAC] THEN
  SUBGOAL_THEN `word_or (Smallnum (&(val (i:byte)))) (Smallnum (&(val (j:byte)))) =
                Smallnum (&(val (word_or i j))):A word` SUBST1_TAC THENL
   [REWRITE_TAC[MP5AUX_Smallnum_val_byte; WORD_EQ_BITS_ALT] THEN
    REWRITE_TAC[BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_XOR; BIT_WORD_SHL;
                MP5AUX_bit_word_val_byte] THEN
    REWRITE_TAC[BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_XOR; DIMINDEX_8] THEN
    ONCE_REWRITE_TAC[word_bit_thm] THEN REWRITE_TAC[DIMINDEX_8] THEN
    GEN_TAC THEN MP5AUX_BITS_ARITH_TAC;
    MATCH_MP_TAC IMP_memory_rel_Number THEN ASM_SIMP_TAC[small_int_w2n]]);;

(* HOL4 line 12976 *)
let memory_rel_Xor = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm (i:byte) wi j wj vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number (&(val i)),wl_Word wi)
             (CONS (data_Number (&(val j)),wl_Word wj) vars)) /\
     good_dimindex (:A) ==>
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number (&(val (word_xor i j))),wl_Word (word_xor wi wj:A word))
             vars)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tail) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tail) THEN
  SUBGOAL_THEN `wi = Smallnum (&(val (i:byte))):A word /\
                wj = Smallnum (&(val (j:byte))):A word`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [ASM_MESON_TAC[memory_rel_Number_IMP; small_int_w2n; injectivity "word_loc"];
    ALL_TAC] THEN
  SUBGOAL_THEN `word_xor (Smallnum (&(val (i:byte)))) (Smallnum (&(val (j:byte)))) =
                Smallnum (&(val (word_xor i j))):A word` SUBST1_TAC THENL
   [REWRITE_TAC[MP5AUX_Smallnum_val_byte; WORD_EQ_BITS_ALT] THEN
    REWRITE_TAC[BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_XOR; BIT_WORD_SHL;
                MP5AUX_bit_word_val_byte] THEN
    REWRITE_TAC[BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_XOR; DIMINDEX_8] THEN
    ONCE_REWRITE_TAC[word_bit_thm] THEN REWRITE_TAC[DIMINDEX_8] THEN
    GEN_TAC THEN MP5AUX_BITS_ARITH_TAC;
    MATCH_MP_TAC IMP_memory_rel_Number THEN ASM_SIMP_TAC[small_int_w2n]]);;

(* HOL4 line 13004 *)
let memory_rel_Number_IMP_Word = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i v vars.
     memory_rel c be ts refs sp st m dm (CONS (data_Number i,v) vars) ==>
     ?w. v = wl_Word w`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_memory_rel_HD) THEN
  MP5AUX_UNDISCH_HEAD "v_inv" THEN REWRITE_TAC[v_inv_def] THEN
  COND_CASES_TAC THEN STRIP_TAC THEN MP5AUX_SUBST_VAR_TAC "v" THEN
  ASM_REWRITE_TAC[word_addr_def; injectivity "word_loc"] THEN MESON_TAC[]);;

(* HOL4 line 13011 *)
let memory_rel_Number_IMP_Word_2 = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i v j w vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number i,v) (CONS (data_Number j,w) vars)) ==>
     ?w1 w2. v = wl_Word w1 /\ w = wl_Word w2`,
  MESON_TAC[memory_rel_Number_IMP_Word; memory_rel_tail]);;

(* HOL4 line 13019 *)
let memory_rel_zero_space = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars.
     memory_rel c be ts refs sp st m dm vars ==>
     memory_rel c be ts refs 0 st m dm vars`,
  REWRITE_TAC[memory_rel_def] THEN MESON_TAC[LE_0]);;

(* HOL4 line 13027 *)
let memory_rel_less_space = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars sp'.
     memory_rel c be ts refs sp st m dm vars /\ sp' <= sp ==>
     memory_rel c be ts refs sp' st m dm vars`,
  REWRITE_TAC[memory_rel_def] THEN MESON_TAC[LE_TRANS]);;

(* HOL4 line 13034 *)
let all_ones_bit = prove
 (`!i e b. i < dimindex (:A) ==> (bit i (all_ones e b:A word) <=> b <= i /\ i < e)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[all_ones_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC MP5AUX_BIT_RULES THEN ASM_ARITH_TAC);;

(* HOL4 line 13046 *)
let maxout_bits_bit = prove
 (`!n l b i. bit i (maxout_bits n l b:A word) /\ i < dimindex (:A) ==>
             b <= i /\ i < b + l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[maxout_bits_def] THEN
  COND_CASES_TAC THEN STRIP_TAC THENL
   [ALL_TAC; UNDISCH_TAC `bit i (all_ones (b + l) b:A word)` THEN
    ASM_SIMP_TAC[all_ones_bit] THEN ARITH_TAC] THEN
  UNDISCH_TAC `bit i (word_shl (word n) b:A word)` THEN
  REWRITE_TAC MP5AUX_BIT_RULES THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP BIT_IMP_GE_TWOEXP) THEN
  SUBGOAL_THEN `n < 2 EXP l` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
    `n < a /\ b <= n ==> b < a`)) THEN
  REWRITE_TAC[WORDSAUX_EXP2_LT] THEN ASM_ARITH_TAC);;

(* HOL4 line 13060 *)
let maxout_bits_IMP = prove
 (`!i tag k n. i < dimindex (:A) /\ bit i (maxout_bits tag k n:A word) ==> i < n + k`,
  MESON_TAC[maxout_bits_bit]);;

(* HOL4 line 13066 *)
let make_cons_ptr_thm = prove
 (`!conf (f:A word) tag len.
     make_cons_ptr conf f tag len =
     wl_Word (word_or (word_shl f (shift_length conf - backend_common_word_shift (:A)))
                      (word_or (word 1) (ptr_bits conf tag len)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[make_cons_ptr_def; get_lowerbits_def;
    injectivity "word_loc"] THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_BITS; MP5AUX_BIT_WORD; ADD_CLAUSES] THEN
  ASM_CASES_TAC `bit i (ptr_bits conf tag len:A word)` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[ptr_bits_def; BIT_WORD_OR]) THEN
  ASM_REWRITE_TAC[small_shift_length_def] THEN
  DISCH_THEN(DISJ_CASES_THEN (MP_TAC o MATCH_MP (MATCH_MP
    (REWRITE_RULE[IMP_CONJ] maxout_bits_IMP) (ASSUME `i < dimindex(:A)`)))) THEN
  ARITH_TAC);;

(* HOL4 line 13081 *)
let Num_ABS_lemmas = prove
 (`!n. num_of_int (abs (&n)) = n /\ num_of_int (abs (-- &n)) = n`,
  REWRITE_TAC[INT_ABS_NUM; INT_ABS_NEG; NUM_OF_INT_OF_NUM]);;

(* HOL4 line 13087 *)
let word_cmp_res_def = cake_def
  `word_cmp_res i (j:int) = if i = j then word 1 else if i < j then word 0
                            else word 2:A word`;;

(* HOL4 line 13092 *)
let word_cmp_loop_def = cake_def_wf
  `measure (\p:A word#A word#A word#(A word->bool)#(A word->A word_loc).
              val (FST p))`
  (REWRITE_TAC[measure_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC WSIMPPAUX_val_word_pred THEN ASM_REWRITE_TAC[])
  `word_cmp_loop (l:A word) (a1:A word) a2 dm (m:A word -> A word_loc) =
     if l = word 0 then SOME (word 1) else
       if a1 IN dm /\ a2 IN dm then
         match (m a1, m a2) with
           (wl_Word w1,wl_Word w2) ->
             if w1 = w2 then
               word_cmp_loop (word_sub l (word 1)) (word_sub a1 bytes_in_word)
                 (word_sub a2 bytes_in_word) dm m
             else if word_ult w1 w2 then SOME (word 0) else SOME (word 2:A word)
         | _ -> NONE
       else NONE`;;

(* HOL4 line 13106 (val) *)
let word_cmp_loop_ind = cake_ind "word_cmp_loop";;

(* HOL4 line 13108 *)
let word_cmp_loop_thm = prove
 (CASE_TERM
  `!(m:A word -> A word_loc) dm xs1 (xs2:(A word)list) f1 f2 (a1:A word) a2.
     LENGTH xs1 = LENGTH xs2 /\ LENGTH xs1 < dimword (:A) /\
     (misc_word_list (word_add a1 bytes_in_word) (MAP wl_Word xs1) STAR f1)
       (fun2set (m,dm)) /\
     (misc_word_list (word_add a2 bytes_in_word) (MAP wl_Word xs2) STAR f2)
       (fun2set (m,dm)) ==>
     word_cmp_loop (word (LENGTH xs1))
       (word_add a1 (word_mul bytes_in_word (word (LENGTH xs1))))
       (word_add a2 (word_mul bytes_in_word (word (LENGTH xs1)))) dm m =
     SOME (match mw_cmp xs1 xs2 with
             NONE -> word 1
           | SOME T -> word 0
           | SOME F -> word 2)`,
  GEN_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN (CASE_TERM
  `!n xs1 (xs2:(A word)list) f1 f2 (a1:A word) a2.
     LENGTH xs1 = n /\
     LENGTH xs1 = LENGTH xs2 /\ LENGTH xs1 < dimword (:A) /\
     (misc_word_list (word_add a1 bytes_in_word) (MAP wl_Word xs1) STAR f1)
       (fun2set ((m:A word -> A word_loc),dm)) /\
     (misc_word_list (word_add a2 bytes_in_word) (MAP wl_Word xs2) STAR f2)
       (fun2set (m,dm)) ==>
     word_cmp_loop (word (LENGTH xs1))
       (word_add a1 (word_mul bytes_in_word (word (LENGTH xs1))))
       (word_add a2 (word_mul bytes_in_word (word (LENGTH xs1)))) dm m =
     SOME (match mw_cmp xs1 xs2 with
             NONE -> word 1
           | SOME T -> word 0
           | SOME F -> word 2:A word)`) (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `xs1:(A word)list = [] /\ xs2:(A word)list = []`
      (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[word_cmp_loop_def; mw_cmp_def] THEN
    REWRITE_TAC[LENGTH] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?ys1 y1 ys2 y2. xs1 = APPEND ys1 [y1:A word] /\
                                xs2 = APPEND ys2 [y2:A word]` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`BUTLAST (xs1:(A word)list)`; `LAST (xs1:(A word)list)`;
                          `BUTLAST (xs2:(A word)list)`; `LAST (xs2:(A word)list)`] THEN
    CONJ_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC APPEND_BUTLAST_LAST THEN
    REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var (lhs (concl th)) &&
    (fst(dest_var(lhs(concl th))) = "xs1" || fst(dest_var(lhs(concl th))) = "xs2")))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH; ADD_CLAUSES; SUC_INJ;
    MAP_APPEND; MAP; data_to_word_memoryProof_word_list_APPEND; misc_word_list_def;
    LENGTH_MAP; SEP_CLAUSES; GSYM STAR_ASSOC]) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
  MP5AUX_SEP_R_TAC THEN
  ONCE_REWRITE_TAC[word_cmp_loop_def] THEN
  SUBGOAL_THEN `~(word (SUC (LENGTH (ys1:(A word)list))) = word 0:A word)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[n2w_11] THEN ASM_SIMP_TAC[MOD_LT; ZERO_LT_dimword] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!a:A word.
        word_add a (word_mul bytes_in_word (word (SUC (LENGTH (ys1:(A word)list))))) =
        word_add (word_add a bytes_in_word)
          (word_mul (word (LENGTH (ys1:(A word)list))) bytes_in_word)`
    (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[ADD1] THEN MP5AUX_WORD_RULE_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_mul (word (LENGTH (ys2:(A word)list))) bytes_in_word =
                word_mul (word (LENGTH (ys1:(A word)list))) bytes_in_word:A word`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[mw_cmp_def] THEN
  REWRITE_TAC[APPEND_EQ_NIL; NOT_CONS_NIL; LAST_APPEND; BUTLAST_APPEND; LAST; BUTLAST;
              APPEND_NIL] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ys1:(A word)list`; `ys2:(A word)list`]) THEN
    FIRST_ASSUM(let qtm = `LENGTH (ys1:(A word)list) = n` in fun th -> if concl th = qtm then
      SUBST1_TAC(SYM th) else failwith "") THEN
    SUBGOAL_THEN `word_sub (word (SUC (LENGTH (ys1:(A word)list)))) (word 1) =
                  (word (LENGTH ys1):A word) /\
      (!a:A word. word_sub (word_add (word_add a bytes_in_word)
                 (word_mul (word (LENGTH (ys1:(A word)list))) bytes_in_word))
                 bytes_in_word =
                 word_add a (word_mul bytes_in_word (word (LENGTH ys1))))`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[ADD1] THEN CONJ_TAC THENL
       [MP5AUX_WORD_RULE_TAC; GEN_TAC THEN MP5AUX_WORD_RULE_TAC];
      ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[ARITH_RULE `SUC n < d ==> n < d`];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[]]);;

(* Local helpers (MP5AUX_) for memory_rel_Number_cmp: word_cmp_res by sign *)
(* and magnitude.                                                          *)
let MP5AUX_word_cmp_res_num = prove
 (`!n1 n2.
     word_cmp_res (&n1) (&n2):A word =
       (if n1 = n2 then word 1 else if n1 < n2 then word 0 else word 2) /\
     word_cmp_res (-- &n1) (-- &n2):A word =
       (if n2 = n1 then word 1 else if n2 < n1 then word 0 else word 2)`,
  REWRITE_TAC[word_cmp_res_def; INT_EQ_NEG2; INT_LT_NEG2; INT_OF_NUM_EQ; INT_OF_NUM_LT] THEN
  MESON_TAC[]);;

let MP5AUX_word_cmp_res_same = prove
 (`!i1 i2. (&0 <= i1 <=> &0 <= i2) ==>
     word_cmp_res i1 i2:A word =
     (if &0 <= i1 then
        (if num_of_int (abs i1) = num_of_int (abs i2) then word 1
         else if num_of_int (abs i1) < num_of_int (abs i2) then word 0 else word 2)
      else
        (if num_of_int (abs i2) = num_of_int (abs i1) then word 1
         else if num_of_int (abs i2) < num_of_int (abs i1) then word 0 else word 2))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  DISJ_CASES_THEN (X_CHOOSE_THEN `k1:num` SUBST_ALL_TAC) (SPEC `i1:int` INT_IMAGE) THEN
  DISJ_CASES_THEN (X_CHOOSE_THEN `k2:num` SUBST_ALL_TAC) (SPEC `i2:int` INT_IMAGE) THEN
  REWRITE_TAC[Num_ABS_lemmas; word_cmp_res_def] THEN DISCH_TAC THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

(* comparing magnitudes by the lengths of their multiword representations *)
let MP5AUX_n2mw_LENGTH_LT = prove
 (`!m n. LENGTH (n2mw m:(N word)list) < LENGTH (n2mw n:(N word)list) ==> m < n`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_LT; LENGTH_n2mw_LESS_LENGTH_n2mw]);;

let MP5AUX_word_cmp_res_diff = prove
 (`!i1 i2.
     ((&0 <= i1 <=> &0 <= i2) ==>
      ~(LENGTH (n2mw (num_of_int (abs i1)):(A word)list) =
        LENGTH (n2mw (num_of_int (abs i2)):(A word)list))) ==>
     word_cmp_res i1 i2:A word =
     (if &0 <= i1 then
        (if &0 <= i2 then
           (if LENGTH (n2mw (num_of_int (abs i1)):(A word)list) <
               LENGTH (n2mw (num_of_int (abs i2)):(A word)list) then word 0 else word 2)
         else word 2)
      else
        (if &0 <= i2 then word 0 else
           (if LENGTH (n2mw (num_of_int (abs i1)):(A word)list) <
               LENGTH (n2mw (num_of_int (abs i2)):(A word)list) then word 2 else word 0)))`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_THEN (X_CHOOSE_THEN `k1:num` SUBST_ALL_TAC) (SPEC `i1:int` INT_IMAGE) THEN
  DISJ_CASES_THEN (X_CHOOSE_THEN `k2:num` SUBST_ALL_TAC) (SPEC `i2:int` INT_IMAGE) THEN
  REWRITE_TAC[Num_ABS_lemmas; word_cmp_res_def] THEN DISCH_TAC THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  MP_TAC(SPECL [`k1:num`; `k2:num`] (INST_TYPE [`:A`,`:N`] LENGTH_n2mw_LESS_LENGTH_n2mw)) THEN
  MP_TAC(SPECL [`k2:num`; `k1:num`] (INST_TYPE [`:A`,`:N`] LENGTH_n2mw_LESS_LENGTH_n2mw)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_LE] THEN
  INT_ARITH_TAC);;


(* HOL4 line 13136 *)
let memory_rel_Number_cmp = prove
 (CASE_TERM
  `!c be ts refs sp st (m:A word -> A word_loc) dm i1 v1 i2 v2 vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number i1,v1) (CONS (data_Number i2,v2) vars)) /\
     good_dimindex (:A) ==>
     ?w1 w2.
       v1 = wl_Word w1 /\ v2 = wl_Word (w2:A word) /\
       if ~bit 0 w1 /\ ~bit 0 w2 then
         (i1 < i2 <=> word_ilt w1 w2) /\ (i1 = i2 <=> w1 = w2)
       else if ~bit 0 w1 /\ bit 0 w2 then
         ~(i1 = i2) /\
         ?a x2. get_real_addr c st w2 = SOME a /\
                m a = wl_Word x2 /\ a IN dm /\
                word_cmp_res i1 i2 =
                  (if word_and x2 (word 16) = word 0 then word 0 else word 2:A word)
       else if bit 0 w1 /\ bit 0 w2 then
         ?a1 x1 a2 x2.
           get_real_addr c st w1 = SOME a1 /\ m a1 = wl_Word x1 /\ a1 IN dm /\
           get_real_addr c st w2 = SOME a2 /\ m a2 = wl_Word x2 /\ a2 IN dm /\
           if x1 = x2 then
             let (a1,a2) = if word_and x1 (word 16) = word 0 then (a1,a2)
                           else (a2,a1) in
             word_cmp_loop (decode_length c x1)
               (word_add a1 (word_mul bytes_in_word (decode_length c x1)))
               (word_add a2 (word_mul bytes_in_word (decode_length c x2)))
               dm m = SOME (word_cmp_res i1 i2)
           else
             word_cmp_res i1 i2 =
             (if word_and x1 (word 16) = word 0 then
                if word_and x2 (word 16) = word 0 then
                  if word_ult (decode_length c x1) (decode_length c x2) then word 0
                  else word 2:A word
                else word 2
              else
                if word_and x2 (word 16) = word 0 then word 0
                else
                  if word_ult (decode_length c x1) (decode_length c x2) then word 2
                  else word 0)
       else T`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tail) THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,(A)word_loc)fmap`; `m:A word -> A word_loc`;
    `dm:A word->bool`; `i1:int`; `v1:A word_loc`;
    `CONS (data_Number i2,v2:A word_loc) vars`] memory_rel_any_Number_IMP) THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,(A)word_loc)fmap`; `m:A word -> A word_loc`;
    `dm:A word->bool`; `i2:int`; `v2:A word_loc`; `vars:(data_v#(A)word_loc)list`]
    memory_rel_any_Number_IMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:A word` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`w1:A word`; `w2:A word`] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `small_int (:A) i1` THEN ASM_CASES_TAC `small_int (:A) i2` THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `w1 = Smallnum i1:A word /\ w2 = Smallnum i2:A word`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [ASM_MESON_TAC[memory_rel_Number_IMP; injectivity "word_loc"]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM num_less_thm; MP5AUX_Smallnum_11];
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,(A)word_loc)fmap`; `m:A word -> A word_loc`;
    `dm:A word->bool`; `i2:int`; `v2:A word_loc`; `vars:(data_v#(A)word_loc)list`]
    memory_rel_Number_bignum_IMP_ALT) THEN
  ASM_REWRITE_TAC[injectivity "word_loc"] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`a:A word`; `x:A word`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var (rhs (concl th)) &&
    fst(dest_var(rhs(concl th))) = "w")) THEN
  ASM_REWRITE_TAC[word_cmp_res_def] THEN
  UNDISCH_TAC `small_int (:A) i1` THEN UNDISCH_TAC `~small_int (:A) i2` THEN
  REWRITE_TAC[small_int_def] THEN
  ASM_CASES_TAC `&0 <= (i2:int)` THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  (SUBGOAL_THEN `~(i1:int = i2)` (fun th -> REWRITE_TAC[th]) THENL
    [MP5AUX_INT_ARITH_TAC; ALL_TAC]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN MP5AUX_INT_ARITH_TAC;
    MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,(A)word_loc)fmap`; `m:A word -> A word_loc`;
    `dm:A word->bool`; `i1:int`; `v1:A word_loc`;
    `CONS (data_Number i2,v2:A word_loc) vars`] memory_rel_Number_bignum_IMP_ALT) THEN
  ASM_REWRITE_TAC[injectivity "word_loc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff1:(A word#A word_loc->bool)->bool`
    (X_CHOOSE_THEN `u1:A word` (X_CHOOSE_THEN `x1:A word`
      (X_CHOOSE_THEN `a1:A word` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,(A)word_loc)fmap`; `m:A word -> A word_loc`;
    `dm:A word->bool`; `i2:int`; `v2:A word_loc`; `vars:(data_v#(A)word_loc)list`]
    memory_rel_Number_bignum_IMP_ALT) THEN
  ASM_REWRITE_TAC[injectivity "word_loc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff2:(A word#A word_loc->bool)->bool`
    (X_CHOOSE_THEN `u2:A word` (X_CHOOSE_THEN `x2:A word`
      (X_CHOOSE_THEN `a2:A word` STRIP_ASSUME_TAC)))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var (rhs (concl th)) &&
    (fst(dest_var(rhs(concl th))) = "u1" || fst(dest_var(rhs(concl th))) = "u2")))) THEN
  MAP_EVERY EXISTS_TAC [`a1:A word`; `x1:A word`; `a2:A word`; `x2:A word`] THEN
  ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
   `(word (LENGTH (n2mw (num_of_int (abs i1)):(A word)list)) =
     word (LENGTH (n2mw (num_of_int (abs i2)):(A word)list)):A word <=>
     LENGTH (n2mw (num_of_int (abs i1)):(A word)list) =
     LENGTH (n2mw (num_of_int (abs i2)):(A word)list)) /\
    (word_ult (word (LENGTH (n2mw (num_of_int (abs i1)):(A word)list)))
              (word (LENGTH (n2mw (num_of_int (abs i2)):(A word)list)):A word) <=>
     LENGTH (n2mw (num_of_int (abs i1)):(A word)list) <
     LENGTH (n2mw (num_of_int (abs i2)):(A word)list))`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[n2w_11; word_lo_n2w] THEN ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,(A)word_loc)fmap`; `m:A word -> A word_loc`;
    `dm:A word->bool`; `i1:int`; `v1:A word_loc`; `i2:int`; `v2:A word_loc`;
    `vars:(data_v#(A)word_loc)list`] memory_rel_bignum_cmp) THEN
  ASM_REWRITE_TAC[injectivity "word_loc"; option_INJ] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:A word` (X_CHOOSE_THEN `q2:A word`
    (X_CHOOSE_THEN `b1:A word` (X_CHOOSE_THEN `b2:A word`
      (X_CHOOSE_THEN `y1:A word` (X_CHOOSE_THEN `y2:A word` STRIP_ASSUME_TAC)))))) THEN
  MP5AUX_SUBST_VAR_TAC "q1" THEN MP5AUX_SUBST_VAR_TAC "q2" THEN
  SUBGOAL_THEN `b1 = a1:A word /\ b2 = a2:A word` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MP5AUX_FUNC_EQ_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `y1 = x1:A word /\ y2 = x2:A word` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MP5AUX_FUNC_EQ_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    is_neg (lhand (concl th)))) THEN
  ONCE_REWRITE_TAC[WORD_AND_SYM] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `x1:A word = x2` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    MATCH_MP_TAC MP5AUX_word_cmp_res_diff THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC TAUT] THEN
  SUBGOAL_THEN `(&0 <= (i1:int) <=> &0 <= (i2:int)) /\
    LENGTH (n2mw (num_of_int (abs i2)):(A word)list) =
    LENGTH (n2mw (num_of_int (abs i1)):(A word)list)` STRIP_ASSUME_TAC THENL
   [MP5AUX_SUBST_VAR_TAC "x2" THEN MP5AUX_FUNC_EQ_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MP5AUX_word_cmp_res_same] THEN
  UNDISCH_TAC `&0 <= (i1:int) <=> &0 <= (i2:int)` THEN
  ASM_CASES_TAC `&0 <= (i1:int)` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[pair_CASE] THENL
   [MP_TAC(ISPECL [`m:A word -> A word_loc`; `dm:A word->bool`;
      `n2mw (num_of_int (abs i1)):(A word)list`; `n2mw (num_of_int (abs i2)):(A word)list`;
      `ff1:(A word#A word_loc->bool)->bool`; `ff2:(A word#A word_loc->bool)->bool`;
      `a1:A word`; `a2:A word`] word_cmp_loop_thm);
    MP_TAC(ISPECL [`m:A word -> A word_loc`; `dm:A word->bool`;
      `n2mw (num_of_int (abs i2)):(A word)list`; `n2mw (num_of_int (abs i1)):(A word)list`;
      `ff2:(A word#A word_loc->bool)->bool`; `ff1:(A word#A word_loc->bool)->bool`;
      `a2:A word`; `a1:A word`] word_cmp_loop_thm)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[mw_cmp_thm; mw2n_n2mw] THEN
  REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC]);;

(* HOL4 line 13234 *)
let word_cmp_loop_refl = prove
 (`!l (a:A word) dm m x. word_cmp_loop l a a dm m = SOME x ==> x = word 1`,
  SUBGOAL_THEN `!l (a1:A word) a2 dm (m:A word -> A word_loc).
     a1 = a2 ==> !x. word_cmp_loop l a1 a2 dm m = SOME x ==> x = word 1`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC word_cmp_loop_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN SUBST_ALL_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[word_cmp_loop_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ] THENL [MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `(m:A word -> A word_loc) a2` THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Recursion through ALL2 (HOL4 LIST_REL, congruence rule EVERY2_cong):   *)
(* the kit has admissibility rules for MAP, ALL, EX, ... but none for ALL2: *)
(* a recursive call under ALL2 f l1 l2 gets the context MEM x l1 /\       *)
(* MEM y l2 (kit/recursion.ml, cake_register_admissible)                   *)

let () = cake_register_admissible "ALL2" LISTAUX_ADMISSIBLE_ALL2;;

(* HOL4 line 13248.  Defined by a match (the clause form with the catch-all *)
(* clause makes the recursion package very slow: 25 clauses); the recursive *)
(* call under ALL2 is a lambda (docs/CONVENTIONS.md section 8).             *)
(* v_same_type_def is HOL4's theorem: the clauses as TFL completes them.    *)
let v_same_type_DEF = cake_def_wf
  `measure (\p:data_v#data_v. data_v_size (FST p))` TERM_TAC
  `v_same_type v1 v2 <=>
     match (v1,v2) with
       (data_Number _,data_Number _) -> T
     | (data_Word64 _,data_Word64 _) -> T
     | (data_Block _ t1 l1,data_Block _ t2 l2) ->
         (t1 = t2 /\ LENGTH l1 = LENGTH l2 ==> ALL2 (\x y. v_same_type x y) l1 l2)
     | (data_CodePtr _,data_CodePtr _) -> T
     | (data_RefPtr _ _,data_RefPtr _ _) -> T
     | _ -> F`;;
let v_same_type_ind = cake_ind "v_same_type";;

let v_same_type_def = prove
 (`(!a0 b0. v_same_type (data_Number a0) (data_Number b0) <=> T) /\
   (!a0 b0. v_same_type (data_Word64 a0) (data_Word64 b0) <=> T) /\
   (!a0 t1 l1 b0 t2 l2.
      v_same_type (data_Block a0 t1 l1) (data_Block b0 t2 l2) <=>
      (t1 = t2 /\ LENGTH l1 = LENGTH l2 ==> ALL2 v_same_type l1 l2)) /\
   (!a0 b0. v_same_type (data_CodePtr a0) (data_CodePtr b0) <=> T) /\
   (!a0 a1 b0 b1. v_same_type (data_RefPtr a0 a1) (data_RefPtr b0 b1) <=> T) /\
   (!a0 b0. v_same_type (data_Number a0) (data_Word64 b0) <=> F) /\
   (!a0 b0 b1 b2. v_same_type (data_Number a0) (data_Block b0 b1 b2) <=> F) /\
   (!a0 b0. v_same_type (data_Number a0) (data_CodePtr b0) <=> F) /\
   (!a0 b0 b1. v_same_type (data_Number a0) (data_RefPtr b0 b1) <=> F) /\
   (!a0 b0. v_same_type (data_Word64 a0) (data_Number b0) <=> F) /\
   (!a0 b0 b1 b2. v_same_type (data_Word64 a0) (data_Block b0 b1 b2) <=> F) /\
   (!a0 b0. v_same_type (data_Word64 a0) (data_CodePtr b0) <=> F) /\
   (!a0 b0 b1. v_same_type (data_Word64 a0) (data_RefPtr b0 b1) <=> F) /\
   (!a0 a1 a2 b0. v_same_type (data_Block a0 a1 a2) (data_Number b0) <=> F) /\
   (!a0 a1 a2 b0. v_same_type (data_Block a0 a1 a2) (data_Word64 b0) <=> F) /\
   (!a0 a1 a2 b0. v_same_type (data_Block a0 a1 a2) (data_CodePtr b0) <=> F) /\
   (!a0 a1 a2 b0 b1. v_same_type (data_Block a0 a1 a2) (data_RefPtr b0 b1) <=> F) /\
   (!a0 b0. v_same_type (data_CodePtr a0) (data_Number b0) <=> F) /\
   (!a0 b0. v_same_type (data_CodePtr a0) (data_Word64 b0) <=> F) /\
   (!a0 b0 b1 b2. v_same_type (data_CodePtr a0) (data_Block b0 b1 b2) <=> F) /\
   (!a0 b0 b1. v_same_type (data_CodePtr a0) (data_RefPtr b0 b1) <=> F) /\
   (!a0 a1 b0. v_same_type (data_RefPtr a0 a1) (data_Number b0) <=> F) /\
   (!a0 a1 b0. v_same_type (data_RefPtr a0 a1) (data_Word64 b0) <=> F) /\
   (!a0 a1 b0 b1 b2. v_same_type (data_RefPtr a0 a1) (data_Block b0 b1 b2) <=> F) /\
   (!a0 a1 b0. v_same_type (data_RefPtr a0 a1) (data_CodePtr b0) <=> F)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [v_same_type_DEF] THEN SIMP[ETA_AX]);;
let _ = cake_add_simps [v_same_type_def];;

(* HOL4 line 13263 *)
let memory_rel_Block_MEM = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm ts' n ls v vars i.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Block ts' n ls,(v:A word_loc)) vars) /\
     i < LENGTH ls /\
     good_dimindex (:A)
     ==>
     ?w a y.
       get_real_offset (Smallnum (&i)) = SOME y /\
       v = wl_Word w /\ get_real_addr c st w = SOME a /\ word_add a y IN dm /\
       memory_rel c be ts refs sp st m dm
         (CONS (EL i ls,m (word_add a y)) (CONS (data_Block ts' n ls,v) vars))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_Block_IMP)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(ls:data_v list = [])` (fun th -> REWRITE_TAC[th]) THENL
   [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `small_int (:A) (&i)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MP5AUX_small_int_ival] THEN
    SUBGOAL_THEN `i < 2 EXP (dimindex(:A) - 4)` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,(A)word_loc)fmap`; `m:A word -> A word_loc`;
    `dm:A word->bool`; `CONS (data_Block ts' n ls,v:A word_loc) vars`; `&i:int`]
    IMP_memory_rel_Number) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP memory_rel_swap) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_El)) THEN
  ASM_REWRITE_TAC[injectivity "word_loc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `pw:A word` (X_CHOOSE_THEN `iw:A word`
    (X_CHOOSE_THEN `xa:A word` (X_CHOOSE_THEN `ya:A word` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`pw:A word`; `xa:A word`; `ya:A word`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    mp5aux_head_is "Smallnum" (lhs (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (mp5aux_head_is "memory_rel" o concl)) THEN
  REPEAT(MP5AUX_SUBST_VAR_TAC "w") THEN
  MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM] THEN MESON_TAC[]);;

(* HOL4 line 13290: Smallnum_0 *)
let data_to_word_memoryProof_Smallnum_0 = prove
 (`!i. ~bit 0 (Smallnum i:A word)`,
  REWRITE_TAC[MP5AUX_bit0_Smallnum]);;

(* HOL4 line 13299: Smallnum_1 *)
let data_to_word_memoryProof_Smallnum_1 = prove
 (`!i. good_dimindex(:A) ==> ~bit 1 (Smallnum i:A word)`,
  REWRITE_TAC[MP5AUX_Smallnum_shl; BIT_WORD_SHL] THEN ARITH_TAC);;

(* HOL4 line 13309 *)
let do_eq_list_F_IMP_MEM = prove
 (`!(refs:(A bvl_ref)spt) l l'.
     data_do_eq_list refs l l' = Eq_val F /\ LENGTH l' = LENGTH l ==>
     ?i. i < LENGTH l /\ data_do_eq refs (EL i l) (EL i l') = Eq_val F`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `l':data_v list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; data_do_eq_def] THEN
  CASE_REWRITE_TAC[] THEN
  CASES_ON `data_do_eq (refs:(A bvl_ref)spt) h h'` THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `a:bool` THEN ASM_REWRITE_TAC[] THENL
   [STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `t':data_v list`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `SUC i` THEN ASM_REWRITE_TAC[EL; TL; LT_SUC];
    STRIP_TAC THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[EL; HD; LT_0]]);;

(* HOL4 line 13320 *)
let memory_rel_rotate3 = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm x1 x2 x3 vars.
     memory_rel c be ts refs sp st m dm (CONS x1 (CONS x2 (CONS x3 vars))) ==>
     memory_rel c be ts refs sp st m dm (CONS x3 (CONS x1 (CONS x2 vars)))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC memory_rel_rearrange THEN
  REWRITE_TAC[MEM] THEN MESON_TAC[]);;

(* Local helpers (MP5AUX_) for memory_rel_pointer_eq: one per constructor. *)
let MP5AUX_word_cmp_res_1 = prove
 (`!i1 i2. good_dimindex(:A) ==>
     (word_cmp_res i1 i2 = (word 1:A word) <=> i1 = i2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_cmp_res_def] THEN
  SUBGOAL_THEN `~(word 0:A word = word 1) /\ ~(word 2:A word = word 1)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`0`; `1`] MP5AUX_word_small_11) THEN
    MP_TAC(SPECL [`2`; `1`] MP5AUX_word_small_11) THEN
    UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[];
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[]]);;

let MP5AUX_pointer_eq_Number = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i1 i2 w vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number i1,w) (CONS (data_Number i2,w) vars)) /\
     good_dimindex (:A) ==> i1 = i2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
    `m:A word -> A word_loc`; `dm:A word->bool`; `i1:int`; `w:A word_loc`;
    `i2:int`; `w:A word_loc`; `vars:(data_v#A word_loc)list`] memory_rel_Number_cmp) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word` (X_CHOOSE_THEN `w2:A word`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  SUBGOAL_THEN `w2:A word = w1` SUBST1_TAC THENL
   [ASM_MESON_TAC[injectivity "word_loc"]; ALL_TAC] THEN
  COND_CASES_TAC THENL [REWRITE_TAC[] THEN MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a1:A word`; `x1:A word`; `a2:A word`; `x2:A word`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `a2:A word = a1` SUBST_ALL_TAC THENL
   [MP5AUX_FAST_MESON_TAC[option_INJ]; ALL_TAC] THEN
  SUBGOAL_THEN `x2:A word = x1` SUBST_ALL_TAC THENL
   [MP5AUX_FAST_MESON_TAC[injectivity "word_loc"]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  REWRITE_TAC[COND_ID; pair_CASE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP word_cmp_loop_refl) THEN
  ASM_SIMP_TAC[MP5AUX_word_cmp_res_1]);;

let MP5AUX_pointer_eq_Word64 = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm w1 w2 w vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Word64 w1,w) (CONS (data_Word64 w2,w) vars)) /\
     good_dimindex (:A) ==> w1 = w2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tail) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
    `m:A word -> A word_loc`; `dm:A word->bool`; `w1:int64`; `w:A word_loc`;
    `CONS (data_Word64 w2,w:A word_loc) vars`] memory_rel_Word64_IMP) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
    `m:A word -> A word_loc`; `dm:A word->bool`; `w2:int64`; `w:A word_loc`;
    `vars:(data_v#A word_loc)list`] memory_rel_Word64_IMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:num` (X_CHOOSE_THEN `x2:A word`
    (X_CHOOSE_THEN `u2:A word` (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:num` (X_CHOOSE_THEN `x1:A word`
    (X_CHOOSE_THEN `u1:A word` (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `get_addr c p2 (wl_Word (word 0)):A word = get_addr c p1 (wl_Word (word 0))`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[injectivity "word_loc"]; ALL_TAC] THEN
  SUBGOAL_THEN `x2:A word = x1` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
  SUBGOAL_THEN `u2:A word = u1` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[injectivity "word_loc"]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl))) THEN
  MP_TAC(SPECL [`w1:int64`; `w2:int64`] MP5AUX_word64_extract_11) THEN
  UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[injectivity "word_loc"]);;

let MP5AUX_pointer_eq_RefPtr = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm b1 n1 b2 n2 w vars b.
     memory_rel c be ts refs sp st m dm
       (CONS (data_RefPtr b1 n1,w) (CONS (data_RefPtr b2 n2,w) vars)) /\
     good_dimindex (:A) /\
     data_do_eq refs (data_RefPtr b1 n1) (data_RefPtr b2 n2) = Eq_val b ==> b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_do_eq_def] THEN
  ASM_CASES_TAC `b1:bool` THEN ASM_REWRITE_TAC[distinctness "eq_result"] THEN
  ASM_CASES_TAC `b2:bool` THEN ASM_REWRITE_TAC[distinctness "eq_result"] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
    `m:A word -> A word_loc`; `dm:A word->bool`; `n1:num`; `w:A word_loc`;
    `n2:num`; `w:A word_loc`; `vars:(data_v#A word_loc)list`] memory_rel_RefPtr_EQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:A word` (X_CHOOSE_THEN `v2:A word`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  SUBGOAL_THEN `v2:A word = v1` SUBST1_TAC THENL
   [ASM_MESON_TAC[injectivity "word_loc"]; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(rator(rhs(concl th)))) = "Eq_val" with Failure _ -> false)) THEN
  CASES_ON `lookup n1 (refs:(data_v bvl_ref)spt)` THEN
  CASE_REWRITE_TAC[injectivity "eq_result"; distinctness "eq_result"] THEN
  STRUCT_CASES_TAC(ISPEC `a:data_v bvl_ref` (cases "bvl_ref")) THEN
  CASE_REWRITE_TAC[injectivity "eq_result"; distinctness "eq_result"; COND_ID] THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[injectivity "eq_result"; distinctness "eq_result"]));;

let MP5AUX_memory_rel_len_size = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars.
     memory_rel c be ts refs sp st m dm vars ==>
     data_to_word_config_len_size c + 2 < dimindex (:A)`,
  REWRITE_TAC[memory_rel_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_heap_in_memory_store_IMP) THEN
  ASM_ARITH_TAC);;

let MP5AUX_BlockNil_word_11 = prove
 (`!n1 n2. n1 < dimword (:A) DIV 16 /\ n2 < dimword (:A) DIV 16 /\
     word_add (word_mul (word n1) (word 16)) (word 2):A word =
     word_add (word_mul (word n2) (word 16)) (word 2) ==> n1 = n2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM WORD_MUL; GSYM WORD_ADD] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `val:A word->num`) THEN
  REWRITE_TAC[VAL_WORD; GSYM dimword_def] THEN
  SUBGOAL_THEN `n1 * 16 + 2 < dimword(:A) /\ n2 * 16 + 2 < dimword(:A)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`dimword(:A)`; `16`] DIVISION) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

let MP5AUX_pointer_eq_Block_hdr = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm ts1 n1 l1 ts2 n2 l2 w vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Block ts1 n1 l1,w) (CONS (data_Block ts2 n2 l2,w) vars)) /\
     good_dimindex (:A) ==> n1 = n2 /\ LENGTH l1 = LENGTH l2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP5AUX_memory_rel_len_size) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_swap) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
    `m:A word -> A word_loc`; `dm:A word->bool`; `ts2:num`; `n2:num`;
    `l2:data_v list`; `w:A word_loc`;
    `CONS (data_Block ts1 n1 l1,w:A word_loc) vars`] memory_rel_Block_IMP) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
    `m:A word -> A word_loc`; `dm:A word->bool`; `ts1:num`; `n1:num`;
    `l1:data_v list`; `w:A word_loc`;
    `CONS (data_Block ts2 n2 l2,w:A word_loc) vars`] memory_rel_Block_IMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:A word` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `w2:A word = w1` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[injectivity "word_loc"]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl))) THEN
  ASM_CASES_TAC `l1:data_v list = []` THEN ASM_CASES_TAC `l2:data_v list = []` THEN
  ASM_REWRITE_TAC[LENGTH] THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MP5AUX_BlockNil_word_11 THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a2:A word`; `x2:A word`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a1:A word`; `x1:A word`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `a2:A word = a1` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
  SUBGOAL_THEN `x2:A word = x1` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[injectivity "word_loc"]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `4 * n1`; `LENGTH (l1:data_v list)`;
    `4 * n2`; `LENGTH (l2:data_v list)`; `x1:A word`; `x1:A word`] encode_header_EQ) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let MP5AUX_pointer_eq_Block_field = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm ts1 n1 l1 ts2 n2 l2 w vars i.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Block ts1 n1 l1,w) (CONS (data_Block ts2 n2 l2,w) vars)) /\
     good_dimindex (:A) /\ i < LENGTH l1 /\ LENGTH l1 = LENGTH l2 ==>
     ?u. memory_rel c be ts refs sp st m dm
           (CONS (EL i l1,u) (CONS (EL i l2,u) vars))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
    `m:A word -> A word_loc`; `dm:A word->bool`; `ts1:num`; `n1:num`;
    `l1:data_v list`; `w:A word_loc`;
    `CONS (data_Block ts2 n2 l2,w:A word_loc) vars`; `i:num`] memory_rel_Block_MEM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word` (X_CHOOSE_THEN `a1:A word`
    (X_CHOOSE_THEN `y1:A word` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_rotate3) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
    `m:A word -> A word_loc`; `dm:A word->bool`; `ts2:num`; `n2:num`;
    `l2:data_v list`; `w:A word_loc`;
    `CONS (EL i l1,(m:A word -> A word_loc) (word_add a1 y1))
       (CONS (data_Block ts1 n1 l1,w:A word_loc) vars)`; `i:num`] memory_rel_Block_MEM) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:A word` (X_CHOOSE_THEN `a2:A word`
    (X_CHOOSE_THEN `y2:A word` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `w2:A word = w1` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[injectivity "word_loc"]; ALL_TAC] THEN
  SUBGOAL_THEN `a2:A word = a1 /\ y2:A word = y1` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
  EXISTS_TAC `(m:A word -> A word_loc) (word_add a1 y1)` THEN
  FIRST_X_ASSUM(MP_TAC o check (free_in `EL i (l2:data_v list)` o concl)) THEN
  MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM] THEN MESON_TAC[]);;

let MP5AUX_pointer_eq_Block = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars ts1 n1 l1.
     ALL (\v1. !v2 (w:A word_loc) b.
            memory_rel c be ts refs sp st m dm (CONS (v1,w) (CONS (v2,w) vars)) /\
            good_dimindex (:A) /\ data_do_eq refs v1 v2 = Eq_val b ==> b) l1 ==>
     !v2 (w:A word_loc) b.
       memory_rel c be ts refs sp st m dm
         (CONS (data_Block ts1 n1 l1,w) (CONS (v2,w) vars)) /\
       good_dimindex (:A) /\
       data_do_eq refs (data_Block ts1 n1 l1) v2 = Eq_val b ==> b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `v2:data_v` THEN
  STRUCT_CASES_TAC(SPEC `v2:data_v` (CONJUNCT1 (cases "data_v"))) THEN
  REWRITE_TAC[data_do_eq_def; distinctness "eq_result"] THEN
  MAP_EVERY X_GEN_TAC [`w:A word_loc`; `b:bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
    `m:A word -> A word_loc`; `dm:A word->bool`; `ts1:num`; `n1:num`;
    `l1:data_v list`; `a0:num`; `a1:num`; `a2:data_v list`; `w:A word_loc`;
    `vars:(data_v#A word_loc)list`] MP5AUX_pointer_eq_Block_hdr) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(rator(rhs(concl th)))) = "Eq_val" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[injectivity "eq_result"; distinctness "eq_result"];
    ALL_TAC] THEN
  DISCH_TAC THEN ASM_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `data_do_eq_list (refs:(data_v bvl_ref)spt) l1 a2 = Eq_val b` THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`refs:(data_v bvl_ref)spt`; `l1:data_v list`; `a2:data_v list`]
    do_eq_list_F_IMP_MEM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
    `m:A word -> A word_loc`; `dm:A word->bool`; `ts1:num`; `a1:num`;
    `l1:data_v list`; `a0:num`; `a1:num`; `a2:data_v list`; `w:A word_loc`;
    `vars:(data_v#A word_loc)list`; `i:num`] MP5AUX_pointer_eq_Block_field) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `u:A word_loc`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `EL i (l1:data_v list)` o REWRITE_RULE[GSYM ALL_MEM] o
    check (fun th -> mp5aux_head_is "ALL" (concl th))) THEN
  ASM_SIMP_TAC[MEM_EL] THEN
  DISCH_THEN(MP_TAC o SPECL [`EL i (a2:data_v list)`; `u:A word_loc`; `F`]) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 13328 *)
let memory_rel_pointer_eq = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars v1 v2 w b.
     memory_rel c be ts refs sp st m dm
       (CONS (v1,(w:A word_loc)) (CONS (v2,w) vars)) /\
     good_dimindex (:A) /\
     data_do_eq refs v1 v2 = Eq_val b ==> b`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t))
    [`b:bool`; `w:A word_loc`; `v2:data_v`; `v1:data_v`] THEN
  MATCH_MP_TAC data_to_word_memoryProof_v_ind THEN BETA_TAC THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i1:int` THEN X_GEN_TAC `v2:data_v` THEN
    STRUCT_CASES_TAC(SPEC `v2:data_v` (CONJUNCT1 (cases "data_v"))) THEN
    REWRITE_TAC[data_do_eq_def; distinctness "eq_result"; injectivity "eq_result"] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] MP5AUX_pointer_eq_Number)) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `w1:int64` THEN X_GEN_TAC `v2:data_v` THEN
    STRUCT_CASES_TAC(SPEC `v2:data_v` (CONJUNCT1 (cases "data_v"))) THEN
    REWRITE_TAC[data_do_eq_def; distinctness "eq_result"; injectivity "eq_result"] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] MP5AUX_pointer_eq_Word64)) THEN
    ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC MP5AUX_pointer_eq_Block;
    REWRITE_TAC[data_do_eq_def; distinctness "eq_result"];
    MAP_EVERY X_GEN_TAC [`b1:bool`; `n1:num`; `v2:data_v`] THEN
    STRUCT_CASES_TAC(SPEC `v2:data_v` (CONJUNCT1 (cases "data_v"))) THEN
    TRY(REWRITE_TAC[data_do_eq_def; distinctness "eq_result"] THEN NO_TAC) THEN
    REPEAT GEN_TAC THEN DISCH_THEN(ACCEPT_TAC o MATCH_MP MP5AUX_pointer_eq_RefPtr)]);;

(* HOL4 line 13412 *)
let v1_size_map = prove
 (`!ls. list_size data_v_size ls = SUM (MAP data_v_size ls) + LENGTH ls`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[list_size_def; MAP; SUM; LENGTH] THEN
  ARITH_TAC);;

(* HOL4 line 13418 *)
let v_depth_def = cake_def_wf
  `measure data_v_size` TERM_TAC
  `(v_depth (data_Block _ _ ls) =
      (if NULL ls then 0 else 1) + MAX_LIST (MAP v_depth ls)) /\
   (v_depth _ = 0)`;;
let _ = cake_add_simps [v_depth_def];;

(* HOL4 line 13427 (val) *)
let v_depth_ind = cake_ind "v_depth";;

(* HOL4 line 13429 *)
let v_inv_Block_tag_limit = prove
 (`!c ts n l refs v f tf
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) a sp sp1 gens s m (dm:A word->bool) limit.
     v_inv c (data_Block ts n l) refs (v,f,tf,heap) /\
     heap_in_memory_store heap a sp sp1 gens c s m dm limit
     ==> n < dimword(:A) DIV 16`,
  REPEAT GEN_TAC THEN REWRITE_TAC[v_inv_def] THEN COND_CASES_TAC THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[BlockRep_def] o check (fun th -> is_eq (concl th) &&
    mp5aux_head_is "heap_lookup" (lhs (concl th)))) THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MP5AUX_heap_el_cond o CONJ (ASSUME
    `heap_in_memory_store heap a sp sp1 gens c s (m:A word -> A word_loc) (dm:A word->bool)
       limit`)) THEN
  SIMP[word_payload_def; PAIR_EQ] THEN REWRITE_TAC[encode_header_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN ASM_ARITH_TAC);;

(* HOL4 line 13443 *)
let elements_list_def = cake_def
  `(elements_list [] <=> T) /\
   (elements_list [v] <=> T) /\
   (elements_list (CONS v (CONS w vs)) <=>
      ?ts t ls1 ls2.
        w = data_Block ts t (APPEND (APPEND ls1 [v]) ls2) /\
        elements_list (CONS w vs))`;;
let _ = cake_add_simps [elements_list_def];;

(* HOL4 line 13453 (val) *)
let elements_list_ind = cake_ind "elements_list";;

(* HOL4 line 13455 *)
let memory_rel_depth_limit = prove
 (`!c b ts refs sp st (m:A word -> A word_loc) dm v w vars.
     memory_rel c b ts refs sp st m dm (CONS (v,(w:A word_loc)) vars) /\
     elements_list (CONS v (MAP FST vars)) /\ good_dimindex(:A)
     ==>
     ?ls.
       memory_rel c b ts refs sp st m dm (APPEND ls (CONS (v,w) vars)) /\
       v_depth v = LENGTH ls /\
       elements_list (APPEND (MAP FST ls) (CONS v (MAP FST vars)))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!v (w:A word_loc) vars.
     memory_rel c b ts refs sp st (m:A word -> A word_loc) dm (CONS (v,w) vars) /\
     elements_list (CONS v (MAP FST vars)) /\ good_dimindex(:A)
     ==>
     ?ls.
       memory_rel c b ts refs sp st m dm (APPEND ls (CONS (v,w) vars)) /\
       v_depth v = LENGTH ls /\
       elements_list (APPEND (MAP FST ls) (CONS v (MAP FST vars)))`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC data_to_word_memoryProof_v_ind THEN BETA_TAC THEN
  REPEAT CONJ_TAC THEN TRY
   (REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `[]:(data_v#A word_loc)list` THEN
    ASM_REWRITE_TAC[APPEND; v_depth_def; LENGTH; MAP] THEN NO_TAC) THEN
  MAP_EVERY X_GEN_TAC [`bts:num`; `n:num`; `l:data_v list`] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[v_depth_def] THEN
  ASM_CASES_TAC `l:data_v list = []` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `[]:(data_v#A word_loc)list` THEN
    ASM_REWRITE_TAC[APPEND; NULL; MAP; MAX_LIST; LENGTH; ADD_CLAUSES];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[NULL_EQ] THEN
  MP_TAC(ISPEC `MAP v_depth l` MAX_LIST_MEM) THEN
  ASM_REWRITE_TAC[MAP_EQ_NIL; MEM_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:data_v` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[MEM_EXISTS_EL]) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `b:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,(A)word_loc)fmap`; `m:A word -> A word_loc`;
    `dm:A word->bool`; `bts:num`; `n:num`; `l:data_v list`; `w:A word_loc`;
    `vars:(data_v#A word_loc)list`; `i:num`] memory_rel_Block_MEM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w':A word` (X_CHOOSE_THEN `a:A word`
    (X_CHOOSE_THEN `y:A word` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:data_v` o REWRITE_RULE[GSYM ALL_MEM] o
    check (fun th -> mp5aux_head_is "ALL" (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`(m:A word -> A word_loc) (word_add a y)`;
    `CONS (data_Block bts n l,w:A word_loc) vars`]) THEN
  ASM_REWRITE_TAC[MAP] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[elements_list_def] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `l1:data_v list` (X_CHOOSE_THEN `l2:data_v list`
      SUBST1_TAC) o REWRITE_RULE[MEM_SPLIT] o check ((=) `MEM (e:data_v) l` o concl)) THEN
    MAP_EVERY EXISTS_TAC [`bts:num`; `n:num`; `l1:data_v list`; `l2:data_v list`] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ls:(data_v#A word_loc)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `APPEND ls [(e:data_v,(m:A word -> A word_loc) (word_add a y))]` THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; MAP_APPEND; MAP; LENGTH_APPEND; LENGTH] THEN
  ARITH_TAC);;

(* HOL4 line 13491 *)
let not_all_distinct_map_snd = prove
 (`!xs:(A#B)list.
     ~ALL_DISTINCT (MAP SND xs) ==>
     ?xs1 xs2 xs3 x y1 y2.
       xs = APPEND (APPEND (APPEND (APPEND xs1 [(y1,x)]) xs2) [(y2,x)]) xs3`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL_DISTINCT] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[MEM_MAP]) THEN
    DISCH_THEN(X_CHOOSE_THEN `p:A#B` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    REWRITE_TAC[MEM_SPLIT] THEN
    DISCH_THEN(X_CHOOSE_THEN `l1:(A#B)list` (X_CHOOSE_THEN `l2:(A#B)list`
      SUBST1_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`[]:(A#B)list`; `l1:(A#B)list`; `l2:(A#B)list`;
      `SND (h:A#B)`; `FST (h:A#B)`; `FST (p:A#B)`] THEN
    ASM_REWRITE_TAC[APPEND; GSYM APPEND_ASSOC] THEN
    REWRITE_TAC[CONS_11] THEN UNDISCH_TAC `SND (h:A#B) = SND (p:A#B)` THEN
    MESON_TAC[PAIR];
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXISTS_TAC [`CONS (h:A#B) xs1`; `xs2:(A#B)list`; `xs3:(A#B)list`;
      `x:B`; `y1:A`; `y2:A`] THEN REWRITE_TAC[APPEND]]);;

(* HOL4 line 13505 *)
let IN_all_vs_HD = prove
 (`!x refs xs. x IN all_vs refs (CONS x xs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN
  REPEAT DISJ2_TAC THEN CASES_ON `x:data_v` THEN
  REWRITE_TAC[v_all_vs_def; MEM; MEM_APPEND]);;

(* HOL4 line 13511 *)
let IN_all_vs_TL = prove
 (`!x refs xs y. x IN all_vs refs xs ==> x IN all_vs refs (CONS y xs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT DISJ2_TAC THEN ASM_MESON_TAC[MEM_v_all_vs_extend_hd]);;

(* HOL4 line 13523 *)
let get_lowerbits_shift_length = prove
 (`!w1 (w2:A word) n.
     word_ushr w2 n = word 0 ==> word_ushr (word_or w1 w2) n = word_ushr w1 n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC MP5AUX_BIT_RULES THEN
  DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV) [BIT_GUARD] THEN REWRITE_TAC[]);;

(* HOL4 line 13530 *)
let shift_shift = prove
 (`!n1 l. n1 * 2 EXP l < dimword (:A) ==>
          word_ushr (word_shl (word n1) l) l = word n1:A word`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SHL_WORD] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC[VAL_WORD_USHR] THEN
  REWRITE_TAC[VAL_WORD; GSYM dimword_def] THEN
  SUBGOAL_THEN `2 EXP l * n1 < dimword (:A)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_RULE `~(2 = 0)`] THEN
  MATCH_MP_TAC(GSYM MOD_LT) THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `n1 * 2 EXP l` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `l:num` ZERO_LT_TWOEXP) THEN
  REWRITE_TAC[ARITH_RULE `0 < k <=> 1 <= k`] THEN
  DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `n = n * 1`] THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL]);;

(* HOL4 line 13543 *)
let word_addr_Data_NE_get_addr = prove
 (`!c a1 n a2. good_dimindex (:A) ==>
     ~(word_addr c (gc_shared_Data a1) = wl_Word (get_addr c n a2:A word))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CASES_ON `a1:A word_loc` THEN
  REWRITE_TAC[word_addr_def; injectivity "word_loc"; distinctness "word_loc"] THEN
  DISCH_THEN(MP_TAC o AP_TERM `bit 0:A word->bool`) THEN
  REWRITE_TAC[get_addr_0] THEN REWRITE_TAC MP5AUX_BIT_RULES THEN
  CONV_TAC(DEPTH_CONV MP5AUX_NUMBIT_CONV) THEN MESON_TAC[]);;

(* Local helper (MP5AUX_): the heap address of a pointer word *)
let MP5AUX_get_addr_11 = prove
 (`!c p1 u1 p2 u2.
     p1 * 2 EXP shift_length c < dimword (:A) /\ p1 < dimword (:A) /\
     p2 * 2 EXP shift_length c < dimword (:A) /\ p2 < dimword (:A) /\
     get_addr c p1 u1 = (get_addr c p2 u2:A word) ==> p1 = p2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\w:A word. word_ushr w (shift_length c)`) THEN
  REWRITE_TAC[get_addr_def] THEN
  SIMP_TAC[get_lowerbits_shift_length; get_lowerbits_LSL_shift_length] THEN
  ASM_SIMP_TAC[shift_shift; n2w_11; MOD_LT]);;

(* HOL4 line 13558 *)
let memory_rel_Block_ptr_eq = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) (dm:A word->bool) t1 a1 b1 x t2
    a2 b2 rest.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Block t1 a1 b1,x) (CONS (data_Block t2 a2 b2,x) rest)) /\
     good_dimindex (:A) ==>
     data_Block t1 a1 b1 = data_Block t2 a2 b2`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP5AUX_memory_rel_HD2) THEN
  SUBGOAL_THEN `h1:((A)word_loc)heap_address = h2` SUBST_ALL_TAC THENL
   [MP5AUX_UNDISCH_HEAD "v_inv" THEN MP5AUX_UNDISCH_HEAD "v_inv" THEN
        REWRITE_TAC[v_inv_def] THEN
        ASM_CASES_TAC `b1:data_v list = []` THEN ASM_REWRITE_TAC[] THENL
     [ASM_CASES_TAC `b2:data_v list = []` THEN ASM_REWRITE_TAC[] THEN
            REPEAT STRIP_TAC THEN
            MP5AUX_SUBST_VAR_TAC "h1" THEN MP5AUX_SUBST_VAR_TAC "h2" THEN
            RULE_ASSUM_TAC(REWRITE_RULE[word_addr_def; MP4AUX_BlockNil_and]) THENL
       [MP5AUX_SUBST_VAR_TAC "x" THEN RULE_ASSUM_TAC(REWRITE_RULE[injectivity "word_loc"]) THEN
          ASM_REWRITE_TAC[];
        MP5AUX_SUBST_VAR_TAC "x" THEN RULE_ASSUM_TAC(REWRITE_RULE[injectivity "word_loc"]) THEN
          FIRST_X_ASSUM(MP_TAC o AP_TERM `bit 0:A word->bool` o check (fun th ->
            is_eq (concl th) && type_of (lhs (concl th)) = `:A word`)) THEN
          REWRITE_TAC[get_addr_0; MP5AUX_bit0_BlockNil]];
      ASM_CASES_TAC `b2:data_v list = []` THEN ASM_REWRITE_TAC[] THEN
            REPEAT STRIP_TAC THEN
            MP5AUX_SUBST_VAR_TAC "h1" THEN MP5AUX_SUBST_VAR_TAC "h2" THEN
            RULE_ASSUM_TAC(REWRITE_RULE[word_addr_def; MP4AUX_BlockNil_and]) THENL
       [MP5AUX_SUBST_VAR_TAC "x" THEN RULE_ASSUM_TAC(REWRITE_RULE[injectivity "word_loc"]) THEN
          FIRST_X_ASSUM(MP_TAC o AP_TERM `bit 0:A word->bool` o check (fun th ->
            is_eq (concl th) && type_of (lhs (concl th)) = `:A word`)) THEN
          REWRITE_TAC[get_addr_0; MP5AUX_bit0_BlockNil];
        MP5AUX_SUBST_VAR_TAC "x" THEN RULE_ASSUM_TAC(REWRITE_RULE[injectivity "word_loc"]) THEN
          SUBGOAL_THEN `ptr':num = ptr` SUBST_ALL_TAC THENL
           [MATCH_MP_TAC MP5AUX_get_addr_11 THEN
            MAP_EVERY EXISTS_TAC [`c:data_to_word_config`;
              `wl_Word (ptr_bits c a2
                 (LENGTH (xs':(((A)word_loc)heap_address)list))):A word_loc`;
              `wl_Word (ptr_bits c a1
                 (LENGTH (xs:(((A)word_loc)heap_address)list))):A word_loc`] THEN
            ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MP5AUX_heap_lookup_BOUND];
            ALL_TAC] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[BlockRep_def]) THEN
          SUBGOAL_THEN `a1:num = a2 /\ xs:(((A)word_loc)heap_address)list = xs'`
            (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
           [FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
              mp5aux_head_is "heap_lookup" (lhs (concl th))
              then RULE_ASSUM_TAC(REWRITE_RULE[th]) else failwith "") THEN
            RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; injectivity "heap_element"; PAIR_EQ;
              injectivity "data_to_word_memoryProof_tag"]) THEN
            ASM_REWRITE_TAC[];
            REWRITE_TAC[]]]];
    MP5AUX_UNDISCH_HEAD "v_inv" THEN MP5AUX_UNDISCH_HEAD "v_inv" THEN
      REWRITE_TAC[v_inv_def] THEN
      ASM_CASES_TAC `b1:data_v list = []` THEN ASM_REWRITE_TAC[] THENL
     [ASM_CASES_TAC `b2:data_v list = []` THEN ASM_REWRITE_TAC[] THEN
          REPEAT STRIP_TAC THEN MP5AUX_SUBST_VAR_TAC "h2" THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[injectivity "heap_address"; distinctness "heap_address";
             GSYM (distinctness "heap_address"); injectivity "word_loc"]) THEN
          ASM_REWRITE_TAC[injectivity "data_v"] THEN
          FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
              mp5aux_head_is "BlockNil" (lhs (concl th)))) THEN
          REWRITE_TAC[BlockNil_def; WORD_SHL_WORD; word_add_n2w; n2w_11] THEN
          SUBGOAL_THEN `2 EXP 4 * a1 + 2 < dimword(:A) /\ 2 EXP 4 * a2 + 2 < dimword(:A)`
              STRIP_ASSUME_TAC THENL
             [CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THEN
              MATCH_MP_TAC data_to_word_memoryProof_LESS_DIV_16_IMP THEN ASM_REWRITE_TAC[];
              ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC];
        RULE_ASSUM_TAC(REWRITE_RULE[distinctness "heap_address";
             GSYM (distinctness "heap_address")]) THEN FIRST_ASSUM CONTR_TAC];
      ASM_CASES_TAC `b2:data_v list = []` THEN ASM_REWRITE_TAC[] THEN
        REPEAT STRIP_TAC THEN MP5AUX_SUBST_VAR_TAC "h2" THEN
        RULE_ASSUM_TAC(REWRITE_RULE[injectivity "heap_address"; distinctness "heap_address";
           GSYM (distinctness "heap_address"); injectivity "word_loc"]) THENL
       [FIRST_ASSUM CONTR_TAC;
        FIRST_X_ASSUM(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC o check (fun th ->
            is_conj (concl th) && is_eq (lhand (concl th)) &&
            is_var (lhs (lhand (concl th))) && fst(dest_var(lhs(lhand(concl th)))) = "ptr'")) THEN
          SUBGOAL_THEN `t1 IN FDOM (tf:(num,num)fmap) /\ FAPPLY tf t1 = ptr /\
                        t2 IN FDOM tf /\ FAPPLY tf t2 = ptr` STRIP_ASSUME_TAC THENL
           [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
              mp5aux_head_is "FLOOKUP" (lhs (concl th))))) THEN
            REWRITE_TAC[FLOOKUP_DEF] THEN REPEAT COND_CASES_TAC THEN
            REWRITE_TAC[option_INJ; option_DISTINCT] THEN SIMP_TAC[];
            ALL_TAC] THEN
          SUBGOAL_THEN `t1:num = t2` SUBST_ALL_TAC THENL
           [UNDISCH_TAC `INJ (FAPPLY (tf:(num,num)fmap)) (FDOM tf)
               {a | isSomeDataElement (heap_lookup a (heap:(((A)word_loc,
                  data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list))}` THEN
            REWRITE_TAC[INJ] THEN DISCH_THEN(MP_TAC o SPECL [`t1:num`; `t2:num`] o CONJUNCT2) THEN
            ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[blocks_unique_def] o check (fun th ->
            mp5aux_head_is "blocks_unique" (concl th))) THEN
          DISCH_THEN(MP_TAC o SPECL [`t2:num`; `a1:num`; `b1:data_v list`; `a2:num`;
            `b2:data_v list`]) THEN
          ASM_REWRITE_TAC[IN_all_vs_HD] THEN
          ANTS_TAC THENL [MATCH_MP_TAC IN_all_vs_TL THEN REWRITE_TAC[IN_all_vs_HD]; ALL_TAC] THEN
          SIMP_TAC[]]]]);;

(* HOL4 line 13620 *)
let elements_list_all_blocks = prove
 (`!xs. elements_list xs /\ ~(xs = []) /\ (?t a b. HD xs = data_Block t a b) ==>
        ALL (\x. ?t a b. x = data_Block t a b) xs /\
        SORTED (\x y. vb_size x < vb_size y) xs`,
  MATCH_MP_TAC elements_list_ind THEN
  REWRITE_TAC[elements_list_def; ALL; SORTED_DEF; HD; NOT_CONS_NIL] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    is_var (lhs (concl th)) && fst(dest_var(lhs(concl th))) = "w")) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  SIMP_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[vb_size_def; MAP_APPEND; SUM_APPEND; MAP; SUM; LENGTH_APPEND; LENGTH] THEN
  ARITH_TAC);;

(* HOL4 line 13631 *)
let memory_rel_elements_list_distinct_lemma = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) (dm:A word->bool) vs vars tag a b.
     memory_rel c be ts refs sp st m dm vars /\
     elements_list vs /\ vs = MAP FST vars /\
     good_dimindex (:A) /\
     ~(vs = []) /\
     HD vs = data_Block tag a b
     ==>
     ALL_DISTINCT (MAP SND vars)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP not_all_distinct_map_snd) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`xs1:(data_v#A word_loc)list`; `xs2:(data_v#A word_loc)list`;
    `xs3:(data_v#A word_loc)list`; `x:A word_loc`; `y1:data_v`; `y2:data_v`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `memory_rel c be ts refs sp st (m:A word -> A word_loc) dm
                  [(y1:data_v,x:A word_loc); (y2,x)]` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (mp5aux_head_is "memory_rel" o concl)) THEN
    MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM; MEM_APPEND] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `vs:data_v list` elements_list_all_blocks) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    is_var (lhs (concl th)) && fst(dest_var(lhs(concl th))) = "vs")) THEN
  REWRITE_TAC[MAP_APPEND; MAP; ALL_APPEND; ALL; GSYM APPEND_ASSOC; APPEND] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `transitive (\x y:data_v. vb_size x < vb_size y)` ASSUME_TAC THENL
   [REWRITE_TAC[transitive_DEF] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SORTED_APPEND; SORTED_EQ] THEN REWRITE_TAC[MEM; MEM_APPEND] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `y2:data_v` (find (fun c -> is_forall (concl c) &&
    can (find_term ((=) `y1:data_v`)) (concl c)) (CONJUNCTS th)))) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `t1:num` (X_CHOOSE_THEN `a1:num`
         (X_CHOOSE_THEN `b1:data_v list` SUBST_ALL_TAC)))
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `t2:num` (X_CHOOSE_THEN `a2:num`
           (X_CHOOSE_THEN `b2:data_v list` SUBST_ALL_TAC)))
        (K ALL_TAC))))) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_Block_ptr_eq) o
    check (fun th -> mp5aux_head_is "memory_rel" (concl th) &&
      can (find_term ((=) `[]:(data_v#A word_loc)list`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> mp5aux_head_is "<" (concl th))) THEN
  ARITH_TAC);;

(* HOL4 line 13666.  DEVIATION: HOL4's TL [] = [] (HOL Light's TL [] is   *)
(* unspecified), so the hypothesis ~(vars = []) is added; its use (line     *)
(* 13840) has a non-empty vars                                              *)
let memory_rel_elements_list_distinct = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) (dm:A word->bool) vs vars.
     memory_rel c be ts refs sp st m dm vars /\
     elements_list vs /\ vs = MAP FST vars /\
     good_dimindex (:A) /\ ~(vars = [])
     ==>
     ALL_DISTINCT (MAP SND (TL vars))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `vars:(data_v#A word_loc)list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; TL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tl) THEN
  ASM_CASES_TAC `t:(data_v#A word_loc)list = []` THEN
  ASM_REWRITE_TAC[MAP; ALL_DISTINCT] THEN
  MATCH_MP_TAC memory_rel_elements_list_distinct_lemma THEN
  MAP_EVERY EXISTS_TAC [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
    `m:A word -> A word_loc`; `dm:A word->bool`; `MAP FST (t:(data_v#A word_loc)list)`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    is_var (lhs (concl th)) && fst(dest_var(lhs(concl th))) = "vs")) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (mp5aux_head_is "elements_list" o concl)) THEN
  MP_TAC(ISPEC `t:(data_v#A word_loc)list` list_CASES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAP; elements_list_def; HD; NOT_CONS_NIL] THEN MESON_TAC[]);;

(* HOL4 line 13683 *)
let memory_rel_elements_list_words = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) (dm:A word->bool) vs vars.
     memory_rel c be ts refs sp st m dm vars /\
     elements_list vs /\ vs = MAP FST vars /\
     good_dimindex(:A)
     ==> ~(vars = []) ==> ALL isWord (TL (MAP SND vars))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!vs (vars:(data_v#A word_loc)list).
     memory_rel c be ts refs sp st (m:A word -> A word_loc) (dm:A word->bool) vars /\
     elements_list vs /\ vs = MAP FST vars /\ good_dimindex(:A)
     ==> ~(vars = []) ==> ALL isWord (TL (MAP SND vars))`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC elements_list_ind THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[EQ_SYM_EQ; MAP_EQ_NIL] THEN MESON_TAC[];
    GEN_TAC THEN X_GEN_TAC `vars:(data_v#A word_loc)list` THEN
    STRUCT_CASES_TAC(ISPEC `vars:(data_v#A word_loc)list` list_CASES) THEN
    REWRITE_TAC[MAP; TL; NOT_CONS_NIL; CONS_11] THEN
    STRUCT_CASES_TAC(ISPEC `t:(data_v#A word_loc)list` list_CASES) THEN
    REWRITE_TAC[MAP; TL; ALL; NOT_CONS_NIL; CONS_11];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:data_v`; `w:data_v`; `rest:data_v list`] THEN
  DISCH_TAC THEN X_GEN_TAC `vars:(data_v#A word_loc)list` THEN
  STRUCT_CASES_TAC(ISPEC `vars:(data_v#A word_loc)list` list_CASES) THEN
  REWRITE_TAC[MAP; TL; NOT_CONS_NIL; CONS_11] THEN
  STRUCT_CASES_TAC(ISPEC `t:(data_v#A word_loc)list` list_CASES) THEN
  REWRITE_TAC[MAP; TL; NOT_CONS_NIL; CONS_11; GSYM CONJ_ASSOC] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tl) THEN
  FIRST_X_ASSUM(MP_TAC o check (mp5aux_head_is "elements_list" o concl)) THEN
  REWRITE_TAC[elements_list_def] THEN STRIP_TAC THEN
  REWRITE_TAC[ALL] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
      `sp:num`; `st:(store_name,(A)word_loc)fmap`; `m:A word -> A word_loc`;
      `dm:A word->bool`; `ts':num`; `t:num`;
      `APPEND (APPEND ls1 [v:data_v]) ls2`; `SND (h':data_v#A word_loc)`;
      `t':(data_v#A word_loc)list`] memory_rel_Block_IMP) THEN
    SUBGOAL_THEN `(data_Block ts' t (APPEND (APPEND ls1 [v]) ls2),
                   SND (h':data_v#A word_loc)) = h'` SUBST1_TAC THENL
     [ASM_MESON_TAC[PAIR]; ASM_REWRITE_TAC[]] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[isWord_def];
    FIRST_X_ASSUM(MP_TAC o SPEC `CONS (h':data_v#A word_loc) t'`) THEN
    ASM_REWRITE_TAC[MAP; TL; NOT_CONS_NIL]]);;

(* HOL4 line 13703 *)
let memory_rel_depth_size_limit = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm v w vars.
     memory_rel c be ts refs sp st m dm (CONS (v,w:A word_loc) vars) /\
     good_dimindex (:A)
     ==>
     vb_size v <= dimword(:A) EXP (v_depth v + 1)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!v (w:A word_loc) vars.
     memory_rel c be ts refs sp st (m:A word -> A word_loc) dm (CONS (v,w) vars) /\
     good_dimindex (:A)
     ==> vb_size v <= dimword(:A) EXP (v_depth v + 1)`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC data_to_word_memoryProof_v_ind THEN BETA_TAC THEN
  REPEAT CONJ_TAC THEN TRY
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[vb_size_def; v_depth_def; ADD_CLAUSES; EXP_1] THEN
    MP_TAC(INST_TYPE [`:A`,`:N`] ONE_LT_dimword) THEN ARITH_TAC) THEN
  MAP_EVERY X_GEN_TAC [`bts:num`; `n:num`; `l:data_v list`] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[vb_size_def; v_depth_def] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_Block_IMP)) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `l:data_v list = []` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[NULL; MAP; SUM; LENGTH; MAX_LIST; ADD_CLAUSES; EXP_1] THEN
    STRIP_TAC THEN MP_TAC(SPECL [`dimword(:A)`; `16`] DIVISION) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[NULL_EQ] THEN
  ABBREV_TAC `kk = dimword(:A) EXP (MAX_LIST (MAP v_depth l) + 1)` THEN
  SUBGOAL_THEN `dimword(:A) EXP ((1 + MAX_LIST (MAP v_depth l)) + 1) = dimword(:A) * kk`
    SUBST1_TAC THENL
   [EXPAND_TAC "kk" THEN REWRITE_TAC[ARITH_RULE `(1 + x) + 1 = SUC (x + 1)`; EXP];
    ALL_TAC] THEN
  MATCH_MP_TAC MP5AUX_depth_arith THEN EXISTS_TAC `dimword(:A) DIV 16` THEN
  SUBGOAL_THEN `16 * (dimword(:A) DIV 16) <= dimword(:A) /\ 16 <= dimword(:A) /\
                2 EXP (dimindex (:A) - 4) = dimword(:A) DIV 16`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC memory_rel_tag_limit THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    MATCH_MP_TAC MP5AUX_SUM_MAP_BOUND THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    X_GEN_TAC `e:data_v` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[MEM_EXISTS_EL]) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
      `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,(A)word_loc)fmap`;
      `m:A word -> A word_loc`; `dm:A word->bool`; `bts:num`; `n:num`;
      `l:data_v list`; `w:A word_loc`; `vars:(data_v#A word_loc)list`; `i:num`]
      memory_rel_Block_MEM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `EL i (l:data_v list)` o REWRITE_RULE[GSYM ALL_MEM] o
      check (fun th -> mp5aux_head_is "ALL" (concl th))) THEN
    ASM_REWRITE_TAC[MEM_EL] THEN
    DISCH_THEN(fun ih -> FIRST_ASSUM(MP_TAC o MATCH_MP ih)) THEN
    MATCH_MP_TAC(ARITH_RULE `y <= z ==> x <= y ==> x <= z`) THEN EXPAND_TAC "kk" THEN
    REWRITE_TAC[LE_EXP] THEN MP_TAC(INST_TYPE [`:A`,`:N`] ONE_LT_dimword) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP
      (ARITH_RULE `1 < x ==> ~(x = 0) /\ ~(x = 1)`) th]) THEN
    REWRITE_TAC[LE_ADD_RCANCEL] THEN MATCH_MP_TAC MAX_LIST_PROPERTY THEN
    REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `EL i (l:data_v list)` THEN
    ASM_SIMP_TAC[MEM_EL];
    EXPAND_TAC "kk" THEN GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
    REWRITE_TAC[LE_EXP] THEN MP_TAC(INST_TYPE [`:A`,`:N`] ONE_LT_dimword) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP
      (ARITH_RULE `1 < x ==> ~(x = 0) /\ ~(x = 1)`) th]) THEN ARITH_TAC]);;

