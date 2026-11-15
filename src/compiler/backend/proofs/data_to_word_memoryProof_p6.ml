(* ========================================================================= *)
(* data_to_word_memoryProof_p6: part 6 of 7 (HOL4 lines 13774-16495) of the  *)
(* port of HOL4 compiler/backend/proofs/data_to_word_memoryProofScript.sml   *)
(* (CakeML v3479).  Part of the correctness proof for data_to_word.          *)
(* The parts _p1 ... _p7 are loaded one after the other (each needs the     *)
(* previous one); data_to_word_memoryProof.ml needs the last.                *)
(* MP6AUX_ names are local helpers of this part.                            *)
(* ========================================================================= *)

needs "compiler/backend/proofs/data_to_word_memoryProof_p5.ml";;

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Local helpers (MP6AUX_): bits of numerals, words of width 32 or 64.       *)
(* ------------------------------------------------------------------------- *)

(* numbit i n for a numeral n and a non-numeral i: the disjunction of the   *)
(* positions of the set bits of n                                            *)
let MP6AUX_NUMBIT_CONV tm =
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
      if k = 0 then prove(goal,REWRITE_TAC[numbit; DIV_0; ODD]) else
      let kt = mk_small_numeral k in
      let ilt = mk_comb(mk_comb(`(<):num->num->bool`,i),kt) in
      let enum = prove(mk_imp(mk_comb(mk_comb(`(<):num->num->bool`,`x:num`),kt),
                         list_mk_disj (map (fun j -> mk_eq(`x:num`,mk_small_numeral j))
                                           (0--(k-1)))), ARITH_TAC) in
      prove(goal,
        ASM_CASES_TAC ilt THENL
         [FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP enum th)) THEN
          DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
          REWRITE_TAC[numbit] THEN CONV_TAC NUM_REDUCE_CONV;
          MATCH_MP_TAC(TAUT `~a /\ ~b ==> (a <=> b)`) THEN CONJ_TAC THENL
           [MATCH_MP_TAC NOT_BIT_GT_TWOEXP THEN
            MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC (mk_comb(`(EXP) 2`,kt)) THEN
            CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV;
              REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
            ASM_ARITH_TAC]])
  | _ -> failwith "MP6AUX_NUMBIT_CONV";;

let MP6AUX_BIT_WORD = prove
 (`!i n. bit i (word n:N word) <=> i < dimindex(:N) /\ numbit i n`,
  REWRITE_TAC[BIT_WORD; numbit]);;

let MP6AUX_BIT_RULES =
  [BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_XOR; BIT_WORD_SHL; BIT_WORD_USHR;
   BIT_WORD_NOT; BIT_WORD_0; BIT_WORD_1; MP6AUX_BIT_WORD];;

(* a word equation as bits: !i. i < dimindex(:N) ==> (bit i v <=> ..)      *)
let MP6AUX_WORD_BITS_TAC =
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC MP6AUX_BIT_RULES THEN CONV_TAC(DEPTH_CONV MP6AUX_NUMBIT_CONV);;

(* arithmetic from the arithmetic assumptions only (relations on num)       *)
let MP6AUX_IS_ARITH_ASM =
  let num_ty = `:num` in
  let rec ok t =
    if is_neg t then ok (dest_neg t) else
    if is_conj t || is_disj t then ok (lhand t) && ok (rand t) else
    match t with
      Comb(Comb(Const(("<"|"<="|">"|">="),_),a),_) -> type_of a = num_ty
    | Comb(Comb(Const("=",_),a),_) -> type_of a = num_ty
    | _ -> false in
  ok;;

(* each conjunct of the goal by ARITH_TAC from the arithmetic assumptions   *)
(* that share a variable with it (all of them if that fails)                *)
let MP6AUX_ASM_ARITH_TAC =
  let arith1 (asl,w as g) =
    let fv = frees w in
    let rel th = MP6AUX_IS_ARITH_ASM (concl th) &&
                 not (intersect (frees (concl th)) fv = []) in
    FIRST [REPEAT(FIRST_X_ASSUM(MP_TAC o check rel)) THEN ARITH_TAC;
           REPEAT(FIRST_X_ASSUM(MP_TAC o check (MP6AUX_IS_ARITH_ASM o concl))) THEN
           ARITH_TAC] g in
  REPEAT CONJ_TAC THEN arith1;;

(* decide the conditionals of the goal one by one (by arithmetic from the   *)
(* assumptions where possible, else by a case split), then finish: EL of    *)
(* equal indices, or contradictory arithmetic                               *)
let MP6AUX_COND_DECIDE_TAC (asl,w as g) =
  let tm = find_term is_cond w in
  let c = fst(dest_cond tm) in
  FIRST [SUBGOAL_THEN c (fun th -> REWRITE_TAC[th]) THENL
           [MP6AUX_ASM_ARITH_TAC; ALL_TAC];
         SUBGOAL_THEN (mk_neg c) (fun th -> REWRITE_TAC[th]) THENL
           [MP6AUX_ASM_ARITH_TAC; ALL_TAC];
         ASM_CASES_TAC c THEN ASM_REWRITE_TAC[]] g;;

let MP6AUX_COND_ARITH_TAC =
  REPEAT MP6AUX_COND_DECIDE_TAC THEN
  FIRST [REFL_TAC;
         MATCH_MP_TAC(TAUT `F ==> p`) THEN MP6AUX_ASM_ARITH_TAC;
         AP_THM_TAC THEN AP_TERM_TAC THEN MP6AUX_ASM_ARITH_TAC];;

(* AC normalisation for STAR (HOL4 star_ss) *)
let MP6AUX_STAR_AC = prove
 (`!p q r:(A->bool)->bool.
     p STAR q = q STAR p /\ (p STAR q) STAR r = p STAR (q STAR r) /\
     p STAR (q STAR r) = q STAR (p STAR r)`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_ACCEPT_TAC STAR_COMM;
    REWRITE_TAC[STAR_ASSOC];
    REWRITE_TAC[STAR_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_ACCEPT_TAC STAR_COMM]);;

let MP6AUX_STAR_AC_CONV = EQT_INTRO o AC MP6AUX_STAR_AC;;

(* conditions to the front of a STAR product *)
let MP6AUX_COND_PULL = prove
 (`!c p q:(A->bool)->bool.
     (p STAR cond c = cond c STAR p) /\
     (p STAR (cond c STAR q) = cond c STAR (p STAR q)) /\
     ((cond c STAR p) STAR q = cond c STAR (p STAR q))`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN CONV_TAC MP6AUX_STAR_AC_CONV);;

(* goal ?frame. (P STAR frame) s, an assumption Q s with P a factor of the *)
(* STAR product Q: frame is the product of the other factors (HOL4 SEP_F) *)
let MP6AUX_SEP_FRAME_TAC (asl,w as g) =
  let rec leaves t = match t with
      Comb(Comb(Const("STAR",_),a),b) -> leaves a @ leaves b
    | _ -> [t] in
  let body = snd(dest_exists w) in
  let pst,s = dest_comb body in
  let starc = rator(rator pst) in
  let p = lhand pst in
  let th = find (fun th -> let c = concl th in is_comb c && rand c = s &&
                   exists (aconv p) (leaves (rator c))) (map snd asl) in
  let ls = leaves (rator(concl th)) in
  let rec remove1 l = match l with
      [] -> [] | h::t -> if aconv h p then t else h :: remove1 t in
  let rest = remove1 ls in
  let frame = end_itlist (fun a b -> mk_comb(mk_comb(starc,a),b)) rest in
  (EXISTS_TAC frame THEN MP_TAC th THEN
   MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN AP_THM_TAC THEN
   CONV_TAC MP6AUX_STAR_AC_CONV) g;;

(* from th: Q s and a factor p of the STAR product Q, the theorem          *)
(* (p STAR frame) s with frame the product of the other factors            *)
let MP6AUX_SEP_FACTOR p th =
  let rec leaves t = match t with
      Comb(Comb(Const("STAR",_),a),b) -> leaves a @ leaves b
    | _ -> [t] in
  let q,s = dest_comb(concl th) in
  let starc = rator(rator q) in
  let rec remove1 l = match l with
      [] -> failwith "MP6AUX_SEP_FACTOR" | h::t -> if aconv h p then t else h :: remove1 t in
  let rest = remove1 (leaves q) in
  let frame = end_itlist (fun a b -> mk_comb(mk_comb(starc,a),b)) rest in
  let eq = AC MP6AUX_STAR_AC (mk_eq(q,mk_comb(mk_comb(starc,p),frame))) in
  EQ_MP (AP_THM eq s) th;;

(* ===== PART 6: HOL4 lines 13774-16495 ===== *)

(* HOL4 line 13774.  Defined by a match (the clause form, whose catch-all *)
(* clauses complete to 30 clauses, makes the recursion package very slow); *)
(* vb_eq_size_def below is HOL4's theorem: the clauses as TFL completes    *)
(* them                                                                      *)
let vb_eq_size_DEF = cake_def_wf
  `measure (\x:(A bvl_ref)spt#data_v#data_v + (A bvl_ref)spt#(data_v list)#(data_v list).
              sum_CASE x (\p. data_v_size (FST (SND p)))
                         (\p. list_size data_v_size (FST (SND p))))`
  TERM_TAC
  `(vb_eq_size (refs:(A bvl_ref)spt) v1 v2 =
      match (v1,v2) with
        (data_Block _ t1 l1,data_Block _ t2 l2) ->
          if data_isClos t1 l1 \/ data_isClos t2 l2
          then if data_isClos t1 l1 /\ data_isClos t2 l2 then SOME (1,T) else NONE
          else if t1 = t2 /\ LENGTH l1 = LENGTH l2
               then OPTION_MAP (\(n,b). (n + 1,b)) (vb_eq_size_list refs l1 l2)
               else SOME (1,F)
      | (data_RefPtr b1 n1,data_RefPtr b2 n2) ->
          if b1 /\ b2 then
            (match (lookup n1 refs, lookup n2 refs) with
               (SOME (bvl_ByteArray T bs1), SOME (bvl_ByteArray T bs2)) ->
                 SOME (1,(bs1 = bs2))
             | (SOME (bvl_ByteArray T bs1), _) -> NONE
             | (_, SOME (bvl_ByteArray T bs2)) -> NONE
             | _ -> SOME (1,(n1 = n2)))
          else NONE
      | (data_Number i1,data_Number i2) -> SOME (1,(i1 = i2))
      | (data_Word64 w1,data_Word64 w2) -> SOME (1,(w1 = w2))
      | _ -> NONE) /\
   (vb_eq_size_list refs vs1 vs2 =
      match (vs1,vs2) with
        ([],[]) -> SOME (0,T)
      | ([],_) -> SOME (0,F)
      | (_,[]) -> SOME (0,F)
      | (CONS x1 xs1,CONS x2 xs2) ->
          match vb_eq_size refs x1 x2 with
            NONE -> NONE
          | SOME (n,F) -> SOME (n + 1,F)
          | SOME (n,T) ->
              (match vb_eq_size_list refs xs1 xs2 with
                 NONE -> NONE
               | SOME (m,b) -> SOME (m + n + 1,b)))`;;
let vb_eq_size_ind = cake_ind "vb_eq_size";;

let vb_eq_size_def = prove
 (CASE_TERM
  `(!(refs:(A bvl_ref)spt) ts1 t1 l1 ts2 t2 l2.
      vb_eq_size refs (data_Block ts1 t1 l1) (data_Block ts2 t2 l2) =
      if data_isClos t1 l1 \/ data_isClos t2 l2
      then if data_isClos t1 l1 /\ data_isClos t2 l2 then SOME (1,T) else NONE
      else if t1 = t2 /\ LENGTH l1 = LENGTH l2
           then OPTION_MAP (\(n,b). (n + 1,b)) (vb_eq_size_list refs l1 l2)
           else SOME (1,F)) /\
   (!(refs:(A bvl_ref)spt) b1 n1 b2 n2.
      vb_eq_size refs (data_RefPtr b1 n1) (data_RefPtr b2 n2) =
      if b1 /\ b2 then
        (match (lookup n1 refs, lookup n2 refs) with
           (SOME (bvl_ByteArray T bs1), SOME (bvl_ByteArray T bs2)) ->
             SOME (1,(bs1 = bs2))
         | (SOME (bvl_ByteArray T bs1), _) -> NONE
         | (_, SOME (bvl_ByteArray T bs2)) -> NONE
         | _ -> SOME (1,(n1 = n2)))
      else NONE) /\
   (!(refs:(A bvl_ref)spt) n1 n2.
      vb_eq_size refs (data_Number n1) (data_Number n2) = SOME (1,(n1 = n2))) /\
   (!(refs:(A bvl_ref)spt) w1 w2.
      vb_eq_size refs (data_Word64 w1) (data_Word64 w2) = SOME (1,(w1 = w2))) /\
   (!(refs:(A bvl_ref)spt) i1 w2. vb_eq_size refs (data_Number i1) (data_Word64 w2) = NONE) /\
   (!(refs:(A bvl_ref)spt) i1 ts2 t2 l2. vb_eq_size refs (data_Number i1) (data_Block ts2 t2 l2) = NONE) /\
   (!(refs:(A bvl_ref)spt) i1 c2. vb_eq_size refs (data_Number i1) (data_CodePtr c2) = NONE) /\
   (!(refs:(A bvl_ref)spt) i1 b2 p2. vb_eq_size refs (data_Number i1) (data_RefPtr b2 p2) = NONE) /\
   (!(refs:(A bvl_ref)spt) w1 i2. vb_eq_size refs (data_Word64 w1) (data_Number i2) = NONE) /\
   (!(refs:(A bvl_ref)spt) w1 ts2 t2 l2. vb_eq_size refs (data_Word64 w1) (data_Block ts2 t2 l2) = NONE) /\
   (!(refs:(A bvl_ref)spt) w1 c2. vb_eq_size refs (data_Word64 w1) (data_CodePtr c2) = NONE) /\
   (!(refs:(A bvl_ref)spt) w1 b2 p2. vb_eq_size refs (data_Word64 w1) (data_RefPtr b2 p2) = NONE) /\
   (!(refs:(A bvl_ref)spt) ts1 t1 l1 i2. vb_eq_size refs (data_Block ts1 t1 l1) (data_Number i2) = NONE) /\
   (!(refs:(A bvl_ref)spt) ts1 t1 l1 w2. vb_eq_size refs (data_Block ts1 t1 l1) (data_Word64 w2) = NONE) /\
   (!(refs:(A bvl_ref)spt) ts1 t1 l1 c2. vb_eq_size refs (data_Block ts1 t1 l1) (data_CodePtr c2) = NONE) /\
   (!(refs:(A bvl_ref)spt) ts1 t1 l1 b2 p2. vb_eq_size refs (data_Block ts1 t1 l1) (data_RefPtr b2 p2) = NONE) /\
   (!(refs:(A bvl_ref)spt) c1 i2. vb_eq_size refs (data_CodePtr c1) (data_Number i2) = NONE) /\
   (!(refs:(A bvl_ref)spt) c1 w2. vb_eq_size refs (data_CodePtr c1) (data_Word64 w2) = NONE) /\
   (!(refs:(A bvl_ref)spt) c1 ts2 t2 l2. vb_eq_size refs (data_CodePtr c1) (data_Block ts2 t2 l2) = NONE) /\
   (!(refs:(A bvl_ref)spt) c1 c2. vb_eq_size refs (data_CodePtr c1) (data_CodePtr c2) = NONE) /\
   (!(refs:(A bvl_ref)spt) c1 b2 p2. vb_eq_size refs (data_CodePtr c1) (data_RefPtr b2 p2) = NONE) /\
   (!(refs:(A bvl_ref)spt) b1 p1 i2. vb_eq_size refs (data_RefPtr b1 p1) (data_Number i2) = NONE) /\
   (!(refs:(A bvl_ref)spt) b1 p1 w2. vb_eq_size refs (data_RefPtr b1 p1) (data_Word64 w2) = NONE) /\
   (!(refs:(A bvl_ref)spt) b1 p1 ts2 t2 l2. vb_eq_size refs (data_RefPtr b1 p1) (data_Block ts2 t2 l2) = NONE) /\
   (!(refs:(A bvl_ref)spt) b1 p1 c2. vb_eq_size refs (data_RefPtr b1 p1) (data_CodePtr c2) = NONE) /\
   (!(refs:(A bvl_ref)spt). vb_eq_size_list refs [] [] = SOME (0,T)) /\
   (!(refs:(A bvl_ref)spt) v vs. vb_eq_size_list refs [] (CONS v vs) = SOME (0,F)) /\
   (!(refs:(A bvl_ref)spt) v vs. vb_eq_size_list refs (CONS v vs) [] = SOME (0,F)) /\
   (!(refs:(A bvl_ref)spt) v1 vs1 v2 vs2.
      vb_eq_size_list refs (CONS v1 vs1) (CONS v2 vs2) =
      match vb_eq_size refs v1 v2 with
        NONE -> NONE
      | SOME (n,F) -> SOME (n + 1,F)
      | SOME (n,T) ->
          (match vb_eq_size_list refs vs1 vs2 with
             NONE -> NONE
           | SOME (m,b) -> SOME (m + n + 1,b)))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [vb_eq_size_DEF] THEN SIMP[]);;

let MP6AUX_OPTION_MAP_SUC = prove
 (`!(x:(num#bool)option) n b.
     OPTION_MAP (\(n,b). (n + 1,b)) x = SOME (n,b) <=> ?m. x = SOME (m,b) /\ n = m + 1`,
  REWRITE_TAC[FORALL_OPTION_THM; OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 13805 *)
let vb_eq_size_IMP_vb_size = prove
 (`(!(refs:(A bvl_ref)spt) v1 v2 n b.
      vb_eq_size refs v1 v2 = SOME (n,b) ==> n <= vb_size v1) /\
   (!(refs:(A bvl_ref)spt) v1 v2 n b.
      vb_eq_size_list refs v1 v2 = SOME (n,b) ==>
      n <= SUM (MAP vb_size v1) + LENGTH v1)`,
  MATCH_MP_TAC vb_eq_size_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [CASES_ON `v1:data_v` THEN CASES_ON `v2:data_v` THEN
    REWRITE_TAC[vb_eq_size_def; vb_size_def; option_DISTINCT] THEN REPEAT GEN_TAC THEN
    EVERY_CASE_TAC THEN
    REWRITE_TAC[option_INJ; PAIR_EQ; option_DISTINCT; MP6AUX_OPTION_MAP_SUC] THEN
    TRY ARITH_TAC THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`a0:num`; `a0':num`; `a1':num`;
      `a2:data_v list`; `a2':data_v list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`m:num`; `b:bool`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    CASES_ON `vs1:data_v list` THEN CASES_ON `vs2:data_v list` THEN
    REWRITE_TAC[vb_eq_size_def; MAP; SUM; LENGTH; option_INJ; PAIR_EQ] THEN
    TRY ARITH_TAC THEN FS[] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC(option_DISTINCT :: option_INJ :: PAIR_EQ :: all_case_eqs()) THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `y:bool`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `y:bool`]) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    TRY(FIRST_X_ASSUM(MP_TAC o SPECL [`x':num`; `b:bool`]) THEN ASM_REWRITE_TAC[]) THEN
    (ASM_ARITH_TAC ORELSE ASM_MESON_TAC[])]);;

let MP6AUX_DIMWORD_GE_4 = prove
 (`good_dimindex(:A) ==> 4 <= dimword(:A)`,
  REWRITE_TAC[good_dimindex_def; dimword_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let MP6AUX_MT_LIMIT = prove
 (`!n k. good_dimindex(:A) /\ k <= dimword(:A) /\ n <= dimword(:A) EXP (k + 1)
         ==> n * dimword(:A) < MustTerminate_limit(:A) - dimword(:A)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP6AUX_DIMWORD_GE_4) THEN
  REWRITE_TAC[MustTerminate_limit_def] THEN
  ABBREV_TAC `d = dimword(:A)` THEN
  SUBGOAL_THEN `d + 2 <= d EXP d` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS `d EXP 2` THEN CONJ_TAC THENL
     [REWRITE_TAC[EXP_2] THEN
      SUBGOAL_THEN `4 * d <= d * d` MP_TAC THENL
       [ASM_SIMP_TAC[LE_MULT_RCANCEL]; ASM_ARITH_TAC];
      REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `n * d <= d EXP (d EXP d)` MP_TAC THENL
   [TRANS_TAC LE_TRANS `d EXP (k + 1) * d` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
    REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(* HOL4 line 13818 (the unused bound variables v w of HOL4 are left out) *)
let memory_rel_limit = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm v1 w1 v2 w2 vars n b.
     memory_rel c be ts refs sp st m dm
       (CONS (v1,w1:A word_loc) (CONS (v2,w2:A word_loc) vars)) /\
     vb_eq_size refs v1 v2 = SOME (n,b) /\
     good_dimindex (:A)
     ==>
     n * dimword (:A) < MustTerminate_limit (:A) - dimword (:A)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n <= dimword(:A) EXP (v_depth v1 + 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `vb_size v1` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[vb_eq_size_IMP_vb_size];
      MATCH_MP_TAC memory_rel_depth_size_limit THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `memory_rel c be ts refs sp st (m:A word -> A word_loc) dm
                  [(v1,w1:A word_loc)]` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (can (find_term (fun t -> t = `vars:(data_v#A word_loc)list`)) o concl)) THEN
    MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,A word_loc)fmap`;
    `m:A word -> A word_loc`; `dm:A word->bool`; `v1:data_v`; `w1:A word_loc`;
    `[]:(data_v#A word_loc)list`] memory_rel_depth_limit) THEN
  ASM_REWRITE_TAC[MAP; elements_list_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `ls:(data_v#A word_loc)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `LENGTH (ls:(data_v#A word_loc)list) <= dimword(:A)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
      `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,A word_loc)fmap`;
      `m:A word -> A word_loc`; `dm:A word->bool`;
      `APPEND (MAP FST (ls:(data_v#A word_loc)list)) [v1:data_v]`;
      `APPEND ls [(v1:data_v,w1:A word_loc)]`] memory_rel_elements_list_distinct) THEN
    MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
      `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,A word_loc)fmap`;
      `m:A word -> A word_loc`; `dm:A word->bool`;
      `APPEND (MAP FST (ls:(data_v#A word_loc)list)) [v1:data_v]`;
      `APPEND ls [(v1:data_v,w1:A word_loc)]`] memory_rel_elements_list_words) THEN
    ASM_REWRITE_TAC[MAP_APPEND; MAP; APPEND_EQ_NIL; NOT_CONS_NIL] THEN
    SIMP_TAC[MAP_TL; APPEND_EQ_NIL; NOT_CONS_NIL; MAP_APPEND; MAP] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `TL (APPEND (MAP SND (ls:(data_v#A word_loc)list)) [w1:A word_loc])`
      word_list_limit) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[LENGTH_TL; APPEND_EQ_NIL; NOT_CONS_NIL; LENGTH_APPEND; LENGTH_MAP; LENGTH] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MP6AUX_MT_LIMIT THEN
  EXISTS_TAC `LENGTH (ls:(data_v#A word_loc)list)` THEN ASM_MESON_TAC[]);;

(* HOL4 line 13871 *)
let memory_rel_ptr_eq = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm v1 x1 v2 vars b.
     memory_rel c be ts refs sp st m dm
       (CONS (v1,x1) (CONS (v2,x1:A word_loc) vars)) /\
     data_do_eq refs v1 v2 = Eq_val b /\
     good_dimindex (:A) ==> b`,
  MESON_TAC[memory_rel_pointer_eq]);;

(* HOL4 line 13880 *)
let memory_rel_Block_Block_small_eq = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm ts1 t1 v1 w1 ts2 t2 v2 w2 vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Block ts1 t1 v1,wl_Word (w1:A word))
             (CONS (data_Block ts2 t2 v2,wl_Word w2) vars)) /\
     good_dimindex (:A) /\ ~(w1 = w2) /\ ~bit 0 w1 ==>
     ~(LENGTH v1 = LENGTH v2) \/ ~(t1 = t2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Block_IMP
    (CONJ (MATCH_MP memory_rel_tail th) (ASSUME `good_dimindex(:A)`)))) THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Block_IMP
    (CONJ th (ASSUME `good_dimindex(:A)`)))) THEN
  REWRITE_TAC[injectivity "word_loc"; UNWIND_THM1] THEN
  ASM_CASES_TAC `v1:data_v list = []` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `v2:data_v list = []` THEN ASM_REWRITE_TAC[LENGTH] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[LENGTH_EQ_NIL]);;

let MP6AUX_GET_ADDR_BIT0 = prove
 (`!c n (w:A word_loc). bit 0 (get_addr c n w:A word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[get_addr_def; BIT_WORD_OR] THEN
  STRUCT_CASES_TAC(ISPEC `w:A word_loc` (cases "word_loc")) THEN
  REWRITE_TAC[get_lowerbits_def; BIT_WORD_OR; BIT_WORD_1] THEN
  REWRITE_TAC[DIMINDEX_GT_0]);;

(* HOL4 line 13894 *)
let memory_rel_simple_eq = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm v1 x1 v2 x2 vars b.
     memory_rel c be ts refs sp st m dm (CONS (v1,x1) (CONS (v2,x2) vars)) /\
     data_do_eq refs v1 v2 = Eq_val b /\
     good_dimindex (:A) ==>
     ?w1 w2:A word.
       x1 = wl_Word w1 /\ x2 = wl_Word w2 /\
       (~bit 0 w1 \/ ~bit 0 w2 ==> ((w1 = w2) <=> b))`,
  REPEAT GEN_TAC THEN CASES_ON `v1:data_v` THEN CASES_ON `v2:data_v` THEN
  REWRITE_TAC[data_do_eq_def; distinctness "eq_result"; injectivity "eq_result"] THENL
   [(* Number, Number *)
    STRIP_TAC THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Number_cmp
      (CONJ th (ASSUME `good_dimindex(:A)`)))) THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Number_cmp
      (CONJ (MATCH_MP memory_rel_swap th) (ASSUME `good_dimindex(:A)`)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `u2:A word` (X_CHOOSE_THEN `u1:A word`
      STRIP_ASSUME_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `w1:A word` (X_CHOOSE_THEN `w2:A word`
      STRIP_ASSUME_TAC)) THEN
    RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[injectivity "word_loc"]) THEN
    RVEQ_TAC THEN
    REWRITE_TAC[injectivity "word_loc"; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    ASM_CASES_TAC `bit 0 (u1:A word)` THEN ASM_CASES_TAC `bit 0 (u2:A word)` THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[];
    (* Word64, Word64 *)
    STRIP_TAC THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Word64_IMP
      (CONJ th (ASSUME `good_dimindex(:A)`)))) THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Word64_IMP
      (CONJ (MATCH_MP memory_rel_tail th) (ASSUME `good_dimindex(:A)`)))) THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[injectivity "word_loc"; RIGHT_EXISTS_AND_THM; UNWIND_THM1;
                MP6AUX_GET_ADDR_BIT0];
    (* Block, Block *)
    STRIP_TAC THEN
    SUBGOAL_THEN `data_do_eq (refs:(data_v bvl_ref)spt) (data_Block a0 a1 a2)
                    (data_Block a0' a1' a2') = Eq_val b` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[data_do_eq_def]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Block_IMP
      (CONJ th (ASSUME `good_dimindex(:A)`)))) THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Block_IMP
      (CONJ (MATCH_MP memory_rel_tail th) (ASSUME `good_dimindex(:A)`)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `w2:A word` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `w1:A word` STRIP_ASSUME_TAC) THEN
    RVEQ_TAC THEN
    REWRITE_TAC[injectivity "word_loc"; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    ASM_CASES_TAC `w1:A word = w2` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN
      MATCH_MP_TAC memory_rel_ptr_eq THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(data_isClos a1 (a2:data_v list)) /\
                  ~(data_isClos a1' (a2':data_v list))` STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `data_isClos a1 (a2:data_v list)` THEN
      ASM_CASES_TAC `data_isClos a1' (a2':data_v list)` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
                                              is_cond(lhs(concl th)))) THEN
      ASM_REWRITE_TAC[distinctness "eq_result"] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~((a2:data_v list) = []) /\ ~((a2':data_v list) = [])`
        STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[data_isClos_def]; ALL_TAC] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl))) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
                                            is_cond(lhs(concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(LENGTH (a2:data_v list) = LENGTH (a2':data_v list)) \/
                  ~(a1:num = a1')` MP_TAC THENL
     [ASM_CASES_TAC `bit 0 (w1:A word)` THENL
       [SUBGOAL_THEN `~bit 0 (w2:A word)` ASSUME_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Block_Block_small_eq
          (end_itlist CONJ [MATCH_MP memory_rel_swap th;
             ASSUME `good_dimindex(:A)`;
             ONCE_REWRITE_RULE[EQ_SYM_EQ] (ASSUME `~(w1:A word = w2)`);
             ASSUME `~bit 0 (w2:A word)`]))) THEN
        MESON_TAC[];
        FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Block_Block_small_eq
          (end_itlist CONJ [th; ASSUME `good_dimindex(:A)`;
             ASSUME `~(w1:A word = w2)`; ASSUME `~bit 0 (w1:A word)`]))) THEN
        REWRITE_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[injectivity "eq_result"];
    (* RefPtr, RefPtr *)
    ASM_CASES_TAC `a0:bool` THEN ASM_CASES_TAC `a0':bool` THEN
    ASM_REWRITE_TAC[distinctness "eq_result"] THEN
    STRIP_TAC THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_RefPtr_T_IMP
      (CONJ th (ASSUME `good_dimindex(:A)`)))) THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_RefPtr_T_IMP
      (CONJ (MATCH_MP memory_rel_tail th) (ASSUME `good_dimindex(:A)`)))) THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[injectivity "word_loc"; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 13947 *)
let word_header_def = cake_def
  `word_header c st (a:A word) dm (m:A word -> A word_loc) =
     match get_real_addr c st a with
       NONE -> NONE
     | SOME a1 ->
         if ~(a1 IN dm) then NONE else
           match m a1 with wl_Word x1 -> SOME (a1,x1) | _ -> NONE`;;

(* HOL4 line 13956: fix_clock *)
let data_to_word_memoryProof_fix_clock_def = cake_def
  `(data_to_word_memoryProof_fix_clock ck l (NONE:(A#num#num)option) = NONE) /\
   (data_to_word_memoryProof_fix_clock ck (l:num) (SOME (y,l1:num,ck1:num)) =
      let new_ck = if ck < ck1 then ck else ck1
      and new_l = if l < l1 then l else l1 in
      SOME (y,new_l,new_ck))`;;

(* HOL4 stores an induction theorem for the (non-recursive) fix_clock too;  *)
(* cake_ind needs a recursive definition, so it is proved here              *)
let data_to_word_memoryProof_fix_clock_ind = prove
 (`!P:num->num->(A#num#num)option->bool.
     (!ck l. P ck l NONE) /\
     (!ck l y l1 ck1. P ck l (SOME (y,l1,ck1)))
     ==> !v v1 v2. P v v1 v2`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 13964 (proved here: the termination proof of word_eq uses it) *)
let data_to_word_memoryProof_fix_clock_IMP = prove
 (`!ck l (x:(A#num#num)option) w l1 ck1.
     data_to_word_memoryProof_fix_clock ck l x = SOME (w,l1,ck1) ==>
     ck1 <= ck /\ l1 <= l`,
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM;
              data_to_word_memoryProof_fix_clock_def; LET_DEF; LET_END_DEF;
              option_DISTINCT; option_INJ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 13970 *)
let word_is_clos_def = cake_def
  `word_is_clos c (h:A word) <=>
     word_and h (word_or (tag_mask c) (word 2)) = word (16 * closure_tag + 2) \/
     word_and h (word_or (tag_mask c) (word 2)) = word (16 * partial_app_tag + 2)`;;

(* HOL4 line 13982 *)
let word_eq_def = cake_def_wf
  `measure (\x:data_to_word_config#(store_name,A word_loc)fmap#(A word->bool)#
                (A word->A word_loc)#num#num#A word#A word +
               data_to_word_config#(store_name,A word_loc)fmap#(A word->bool)#
                (A word->A word_loc)#num#num#A word#A word#A word.
              sum_CASE x (\p. FST (SND (SND (SND (SND p)))))
                         (\p. FST (SND (SND (SND (SND p))))))`
  (REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
   REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
   TRY(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP
         data_to_word_memoryProof_fix_clock_IMP)) THEN
   TERM_TAC)
  `(word_eq c st dm m l ck w1 (w2:A word) =
      if w1 = w2 then SOME (word 1:A word,l,ck) else
      if ~(bit 0 w1 /\ bit 0 w2) then SOME (word 0,l,ck) else
        match (word_header c st w1 dm m, word_header c st w2 dm m) with
          (SOME (a1,h1), SOME (a2,h2)) ->
            if word_and h1 (word 12) = word 0 then
              if word_is_clos c h1 then SOME (word 1,l,ck) else
              if ~(h1 = h2) then SOME (word 0,l,ck) else
              if l = 0 then NONE else
                word_eq_list c st dm m (l - 1) ck (decode_length c h1)
                  (word_add a1 bytes_in_word) (word_add a2 bytes_in_word) else
            if ~(h1 = h2) then SOME (word 0,l,ck) else
            if ~bit 2 h1 then SOME (word 0,l,ck) else
            if ~bit 3 h1 /\ bit 4 h1 then SOME (word 0,l,ck)
            else
              (if l <= val (decode_length c h1)
               then NONE else
               match word_cmp_loop (decode_length c h1)
                       (word_add a1 (word_mul bytes_in_word (decode_length c h1)))
                       (word_add a2 (word_mul bytes_in_word (decode_length c h1)))
                       dm m with
                 NONE -> NONE
               | SOME res -> SOME (res,l - 1 - val (decode_length c h1),ck))
        | _ -> NONE) /\
   (word_eq_list c st dm m l ck w a1 a2 =
      if w = word 0:A word then SOME (word 1,l,ck) else
      if ~(a1 IN dm) \/ ~(a2 IN dm) \/ l = 0 \/ ck = 0 then NONE else
        match (m a1,m a2) with
          (wl_Word w1, wl_Word w2) ->
            (match data_to_word_memoryProof_fix_clock (ck - 1) (l - 1)
                     (word_eq c st dm m (l - 1) (ck - 1) w1 w2) with
               NONE -> NONE
             | SOME (x,l,ck') ->
                 if ~(x = word 1) then SOME (x,l,ck) else
                 if l = 0 then NONE else
                   word_eq_list c st dm m (l - 1) ck (word_sub w (word 1))
                     (word_add a1 bytes_in_word) (word_add a2 bytes_in_word))
        | _ -> NONE)`;;

(* HOL4 line 14027 (val) *)
let word_eq_ind = cake_ind "word_eq";;

(* HOL4 line 14029 *)
let word_eq_LESS_EQ = prove
 (`(!c st dm m l ck w1 (w2:A word) x0 l1 ck1.
      word_eq c st dm m l ck w1 w2 = SOME (x0,l1,ck1) ==> l1 <= l /\ ck1 <= ck) /\
   (!c st dm m l ck w a1 (a2:A word) x0 l1 ck1.
      word_eq_list c st dm m l ck w a1 a2 = SOME (x0,l1,ck1) ==>
      l1 <= l /\ ck1 <= ck)`,
  MATCH_MP_TAC word_eq_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[word_eq_def] THEN
  REWRITE_TAC(option_DISTINCT :: option_INJ :: PAIR_EQ :: all_case_eqs()) THEN
  STRIP_TAC THEN RVEQ_TAC THEN TRY ARITH_TAC THEN
  TRY(FIRST_ASSUM(STRIP_ASSUME_TAC o
        MATCH_MP data_to_word_memoryProof_fix_clock_IMP)) THEN
  TRY ASM_ARITH_TAC THEN
  ASM_MESON_TAC[ARITH_RULE `!a b. a <= b - 1 ==> a <= b`;
                ARITH_RULE `!a b c. a <= b - 1 /\ b <= c ==> a <= c`; LE_REFL]);;

(* HOL4 line 14047 *)
let fix_clock_word_eq = prove
 (`!ck l c st dm m w1 (w2:A word).
     data_to_word_memoryProof_fix_clock ck l (word_eq c st dm m l ck w1 w2) =
     word_eq c st dm m l ck w1 w2`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `st:(store_name,A word_loc)fmap`;
    `dm:A word->bool`; `m:A word->A word_loc`; `l:num`; `ck:num`; `w1:A word`;
    `w2:A word`] (CONJUNCT1 word_eq_LESS_EQ)) THEN
  SPEC_TAC(`word_eq c st dm m l ck (w1:A word) w2`,`x:(A word#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; data_to_word_memoryProof_fix_clock_def;
              LET_DEF; LET_END_DEF; option_INJ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`p1:A word`; `p1':num`; `p2:num`]) THEN
  REWRITE_TAC[] THEN ARITH_TAC);;

(* HOL4 lines 14055 and 14058 (allow_rebind) *)
let word_eq_def = REWRITE_RULE [fix_clock_word_eq] word_eq_def;;
let word_eq_ind = REWRITE_RULE [fix_clock_word_eq] word_eq_ind;;

(* HOL4 line 14061 *)
let bit_pattern_1100 = prove
 (`!x1:A word. good_dimindex (:A) ==>
     (word_and (word 12) x1 = word 0 <=> ~bit 2 x1 /\ ~bit 3 x1)`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0; MP6AUX_BIT_WORD] THEN
  CONV_TAC(DEPTH_CONV MP6AUX_NUMBIT_CONV) THEN ASM_REWRITE_TAC[] THEN
  (EQ_TAC THENL
    [DISCH_THEN(fun th -> MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th)) THEN
     CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[];
     MESON_TAC[]]));;
let _ = cake_add_simps [bit_pattern_1100];;

(* HOL4 line 14070 *)
let word_eq_add_clock = prove
 (`(!c st dm m l ck (a1:A word) a2 res l' ck1 n.
      word_eq c st dm m l ck a1 a2 = SOME (res,l',ck1) ==>
      word_eq c st dm m l (ck + n) a1 a2 = SOME (res,l',ck1 + n)) /\
   (!c st dm m l ck w (a1:A word) a2 res l' ck1 n.
      word_eq_list c st dm m l ck w a1 a2 = SOME (res,l',ck1) ==>
      word_eq_list c st dm m l (ck + n) w a1 a2 = SOME (res,l',ck1 + n))`,
  MATCH_MP_TAC word_eq_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [word_eq_def] THEN
  REWRITE_TAC(option_DISTINCT :: option_INJ :: PAIR_EQ :: DE_MORGAN_THM ::
              all_case_eqs()) THEN
  STRIP_TAC THEN RVEQ_TAC THEN GVS[] THEN
  ONCE_REWRITE_TAC[word_eq_def] THEN
  ASM_SIMP_TAC[ADD_EQ_0; ARITH_RULE `!k n. ~(k = 0) ==> (k + n) - 1 = (k - 1) + n`] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 14092 *)
let word_eq_max_clock = prove
 (`(!c st dm m l ck (a1:A word) a2 res l' ck1 n.
      word_eq c st dm m l ck a1 a2 = SOME (res,l',ck1) ==>
      word_eq c st dm m l (MAX ck n) a1 a2 = SOME (res,l',ck1 + (n - ck))) /\
   (!c st dm m l ck w (a1:A word) a2 res l' ck1 n.
      word_eq_list c st dm m l ck w a1 a2 = SOME (res,l',ck1) ==>
      word_eq_list c st dm m l (MAX ck n) w a1 a2 = SOME (res,l',ck1 + (n - ck)))`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MAX] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[ARITH_RULE `~(ck <= n) ==> n - ck = 0`; ADD_CLAUSES] THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n - ck` o MATCH_MP (CONJUNCT1 word_eq_add_clock));
    FIRST_X_ASSUM(MP_TAC o SPEC `n - ck` o MATCH_MP (CONJUNCT2 word_eq_add_clock))] THEN
  ASM_SIMP_TAC[ARITH_RULE `ck <= n ==> ck + (n - ck) = n`]);;

(* HOL4 line 14107 *)
let word_eq_min_max_clock = prove
 (`!c st dm m l a b (a1:A word) a2 res l' ck1 w.
     (!x y. word_eq c st dm m l (MIN a b) a1 a2 = SOME (res,l',ck1) ==>
            ?ck1'. word_eq c st dm m l (MIN (MAX a x) (MAX b y)) a1 a2 =
                   SOME (res,l',ck1')) /\
     (!x y. word_eq_list c st dm m l (MIN a b) w a1 a2 = SOME (res,l',ck1) ==>
            ?ck1'. word_eq_list c st dm m l (MIN (MAX a x) (MAX b y)) w a1 a2 =
                   SOME (res,l',ck1'))`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  (SUBGOAL_THEN `?d. MIN (MAX a x) (MAX b y) = MIN a b + d` (CHOOSE_THEN SUBST1_TAC) THENL
    [EXISTS_TAC `MIN (MAX a x) (MAX b y) - MIN a b` THEN REWRITE_TAC[MIN; MAX] THEN
     ARITH_TAC;
     ALL_TAC]) THEN
  (FIRST_X_ASSUM(MP_TAC o SPEC `d:num` o MATCH_MP (CONJUNCT1 word_eq_add_clock)) ORELSE
   FIRST_X_ASSUM(MP_TAC o SPEC `d:num` o MATCH_MP (CONJUNCT2 word_eq_add_clock))) THEN
  MESON_TAC[]);;

let MP6AUX_DIMWORD_GE_2EXP32 = prove
 (`good_dimindex(:A) ==> 4294967296 <= dimword(:A)`,
  REWRITE_TAC[good_dimindex_def; dimword_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let MP6AUX_WORD_EQ_SMALL = prove
 (`!n k. n < dimword(:A) /\ k < dimword(:A) ==>
         (word n:A word = word k <=> n = k)`,
  SIMP_TAC[GSYM VAL_EQ; VAL_WORD; GSYM dimword_def; MOD_LT]);;

(* HOL4 line 14122 *)
let memory_rel_isClos = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm ts1 t1 v1 w1 vars a' x'.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Block ts1 t1 v1,wl_Word (w1:A word)) vars) /\
     bit 0 w1 /\
     get_real_addr c st w1 = SOME a' /\ m a' = wl_Word x' /\ good_dimindex (:A) ==>
     (data_isClos t1 v1 <=> word_is_clos c x')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Block_IMP
    (CONJ th (ASSUME `good_dimindex(:A)`)))) THEN
  REWRITE_TAC[injectivity "word_loc"; UNWIND_THM1] THEN
  ASM_CASES_TAC `v1:data_v list = []` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A word` (X_CHOOSE_THEN `x:A word` STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN RVEQ_TAC THEN
  SUBGOAL_THEN `wl_Word (x':A word) = wl_Word x` MP_TAC THENL
   [ASM_MESON_TAC[];
    REWRITE_TAC[injectivity "word_loc"] THEN DISCH_THEN SUBST_ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP encode_header_tag_mask o
    C CONJ (ASSUME `good_dimindex(:A)`) o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "encode_header"))
        (concl th))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[word_is_clos_def; data_isClos_def] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP6AUX_DIMWORD_GE_2EXP32) THEN
  SUBGOAL_THEN `16 * t1 + 2 < dimword(:A) /\ 16 * closure_tag + 2 < dimword(:A) /\
                16 * partial_app_tag + 2 < dimword(:A)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[closure_tag_def; partial_app_tag_def] THEN
    MP_TAC(SPECL [`dimword(:A)`; `16`] DIVISION) THEN MP6AUX_ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MP6AUX_WORD_EQ_SMALL] THEN ARITH_TAC);;

(* HOL4 line 14141 *)
let eq_assum_def = cake_def
  `(eq_assum (a:A word) (m:A word -> A word_loc) dm ([]:B list) <=> T) /\
   (eq_assum a m dm (CONS v vs) <=>
      a IN dm /\ eq_assum (word_add a bytes_in_word) m dm vs)`;;

(* HOL4 line 14147 (dm is unused: its type is a type variable, as in HOL4) *)
let eq_explode_def = cake_def
  `(eq_explode (a:A word) (m:A word -> A word_loc) (dm:C) ([]:B list) = []) /\
   (eq_explode a m dm (CONS v vs) =
      CONS (v,m a) (eq_explode (word_add a bytes_in_word) m dm vs))`;;

(* HOL4 line 14152 *)
let eq_explode_APPEND = prove
 (`!(m:A word -> A word_loc) (dm:C) (xs:B list) ys a.
     eq_explode a m dm (APPEND xs ys) =
     APPEND (eq_explode a m dm xs)
            (eq_explode (word_add a (word_mul (word (LENGTH xs)) bytes_in_word))
               m dm ys)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[eq_explode_def; APPEND; LENGTH] THEN REPEAT GEN_TAC THENL
   [AP_THM_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[ADD1; WORD_ADD] THEN CONV_TAC WORD_RULE]);;

(* HOL4 line 14162 *)
let eq_assum_APPEND = prove
 (`!(m:A word -> A word_loc) dm (xs:B list) ys a.
     eq_assum a m dm (APPEND xs ys) <=>
     eq_assum a m dm xs /\
     eq_assum (word_add a (word_mul (word (LENGTH xs)) bytes_in_word)) m dm ys`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[eq_assum_def; APPEND; LENGTH] THEN REPEAT GEN_TAC THENL
   [AP_THM_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[ADD1; WORD_ADD] THEN CONV_TAC WORD_RULE]);;

(* the address of the payload element i of a block *)
let MP6AUX_REAL_OFFSET_SMALLNUM = prove
 (`!i y. good_dimindex(:A) /\ get_real_offset (Smallnum (&i):A word) = SOME y ==>
         y = word_add bytes_in_word (word_mul (word i) bytes_in_word)`,
  REWRITE_TAC[good_dimindex_def; get_real_offset_def; data_to_word_Smallnum_def] THEN
  REWRITE_TAC[INT_OF_NUM_LT; CONJUNCT1 LT; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[option_INJ; bytes_in_word_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[WORD_MUL_LSL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM WORD_MUL; GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC);;

(* HOL4 line 14173 *)
let memory_rel_Block_explode_lemma = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm ts1 t1 v1 w1 vars a n.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Block ts1 t1 v1,wl_Word w1) vars) /\
     bit 0 w1 /\ get_real_addr c st w1 = SOME a /\ good_dimindex (:A) ==>
     memory_rel c be ts refs sp st m dm
       (APPEND (eq_explode (word_add a bytes_in_word) m dm (TAKE n v1))
               (CONS (data_Block ts1 t1 v1,wl_Word (w1:A word)) vars)) /\
     eq_assum (word_add a bytes_in_word) m dm (TAKE n v1)`,
  REPLICATE_TAC 14 GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[TAKE; eq_explode_def; eq_assum_def; APPEND] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `n < LENGTH (v1:data_v list)` THENL
   [ALL_TAC;
    SUBGOAL_THEN `TAKE (SUC n) v1 = TAKE n (v1:data_v list)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[TAKE_LENGTH_TOO_LONG; ARITH_RULE `~(n < l) ==> l <= n /\ l <= SUC n`];
      ASM_REWRITE_TAC[]]] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP SNOC_EL_TAKE) THEN
  REWRITE_TAC[SNOC_APPEND; eq_explode_APPEND; eq_assum_APPEND; eq_explode_def;
              eq_assum_def] THEN
  ASM_SIMP_TAC[LENGTH_TAKE; LT_IMP_LE] THEN
  SUBGOAL_THEN `memory_rel c be ts refs sp st (m:A word -> A word_loc) dm
      (CONS (data_Block ts1 t1 v1,wl_Word w1)
        (APPEND (eq_explode (word_add a bytes_in_word) m dm (TAKE n v1)) vars))`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `APPEND:(data_v#A word_loc)list->(data_v#A word_loc)list->(data_v#A word_loc)list`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "memory_rel")) (concl th))) THEN
    MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,A word_loc)fmap`;
    `m:A word -> A word_loc`; `dm:A word->bool`; `ts1:num`; `t1:num`;
    `v1:data_v list`; `wl_Word (w1:A word)`;
    `APPEND (eq_explode (word_add a bytes_in_word) (m:A word -> A word_loc) (dm:A word->bool)
       (TAKE n (v1:data_v list))) vars`; `n:num`] memory_rel_Block_MEM) THEN
  ASM_REWRITE_TAC[injectivity "word_loc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `w':A word` (X_CHOOSE_THEN `a':A word`
    (X_CHOOSE_THEN `y:A word` STRIP_ASSUME_TAC))) THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `a':A word = a` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `get_real_addr c st w' = SOME (a':A word)` THEN
    ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MP6AUX_REAL_OFFSET_SMALLNUM o
    CONJ (ASSUME `good_dimindex(:A)`) o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "get_real_offset"))
        (concl th))) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_ASSOC]) THEN ASM_REWRITE_TAC[WORD_ADD_ASSOC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match []
    `memory_rel c be ts refs sp st m dm (CONS (x:data_v#A word_loc) (CONS y z))`) (concl th))) THEN
  MATCH_MP_TAC memory_rel_rearrange THEN
  REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]);;

(* HOL4 line 14206 *)
let memory_rel_Block_explode = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm ts1 t1 v1 w1 vars a.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Block ts1 t1 v1,wl_Word w1) vars) /\
     bit 0 w1 /\ get_real_addr c st w1 = SOME a /\ good_dimindex (:A) ==>
     memory_rel c be ts refs sp st m dm
       (APPEND (eq_explode (word_add a bytes_in_word:A word) m dm v1) vars) /\
     eq_assum (word_add a bytes_in_word) m dm v1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,A word_loc)fmap`;
    `m:A word -> A word_loc`; `dm:A word->bool`; `ts1:num`; `t1:num`;
    `v1:data_v list`; `w1:A word`; `vars:(data_v#A word_loc)list`; `a:A word`;
    `LENGTH (v1:data_v list)`] memory_rel_Block_explode_lemma) THEN
  ASM_REWRITE_TAC[TAKE_LENGTH_TOO_LONG; LE_REFL] THEN
  SIMP_TAC[TAKE_LENGTH_TOO_LONG; LE_REFL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
    fst(dest_const t) = "eq_explode")) (concl th) && not (is_conj (concl th)))) THEN
  MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]);;

(* HOL4 line 14220 *)
let memory_rel_Loc = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm v1 n k vars.
     memory_rel c be ts refs sp st m dm (CONS (v1,wl_Loc n k) vars) /\
     (!ptr. ~(v1 = data_RefPtr F ptr)) ==>
     v1 = data_CodePtr n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[memory_rel_def; word_ml_inv_def; abs_ml_inv_def; bc_stack_ref_inv_def;
              MAP] THEN
  REWRITE_TAC[LIST_REL_CONS2] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL2]) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_comb(lhs(concl th)) &&
    fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_addr")) THEN
  CASES_ON `h':(A word_loc)heap_address` THEN
  REWRITE_TAC[word_addr_def; distinctness "word_loc"] THEN
  TRY(CASES_ON `a':A word_loc` THEN
      REWRITE_TAC[word_addr_def; distinctness "word_loc"; injectivity "word_loc"]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o check (is_conj o concl)) THEN
  CASES_ON `v1:data_v` THEN REWRITE_TAC[v_inv_def] THEN FS[] THEN RW[] THEN FS[] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 14231 *)
let memory_rel_ByteArray_words_IMP = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl p w vars fl vals a.
     memory_rel c be ts refs sp st m dm
       (CONS (data_RefPtr bl p,wl_Word (w:A word)) vars) /\
     lookup p refs = SOME (bvl_ByteArray fl vals) /\
     good_dimindex(:A) /\
     get_real_addr c st w = SOME a ==>
     ?x frame.
       m a = wl_Word x /\
       (misc_word_list (word_add a bytes_in_word)
          (MAP wl_Word (write_bytes vals (REPLICATE (val (decode_length c x)) (word 0))
                          be))
        STAR frame) (fun2set (m,dm)) /\
       val (decode_length c x) < dimword(:A) /\
       val (decode_length c x) = LENGTH vals DIV (dimindex(:A) DIV 8) + 1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[memory_rel_def; word_ml_inv_def; abs_ml_inv_def; bc_stack_ref_inv_def;
              MAP] THEN
  REWRITE_TAC[LIST_REL_CONS2] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL2]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl) o
    check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "v_inv")) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "v_inv")) (concl th) && not (is_forall (concl th)) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "ALL2"))
        (concl th)))) THEN
  ASM_REWRITE_TAC[v_inv_def; option_INJ; distinctness "bvl_ref"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "bc_ref_inv"))
      (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[reachable_refs_def] THEN
    EXISTS_TAC `data_RefPtr bl p` THEN EXISTS_TAC `p:num` THEN
    REWRITE_TAC[MEM; get_refs_def; RTC_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN DISCH_TAC THEN
  UNDISCH_TAC `word_addr c (Pointer (FAPPLY (f:(num,num)fmap) p)
      (ref_ptr_annot c (SOME (bvl_ByteArray fl (vals:byte list):data_v bvl_ref)))) =
      wl_Word (w:A word)` THEN
  REWRITE_TAC[word_addr_def; injectivity "word_loc"] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `heap_in_memory_store heap a' sp' sp1 gens c st
     (m:A word -> A word_loc) dm limit` THEN
  REWRITE_TAC[heap_in_memory_store_def] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
      heap_element)list`; `c:data_to_word_config`; `FAPPLY (f:(num,num)fmap) p`;
    `Bytes be fl vals (REPLICATE (LENGTH vals DIV (dimindex (:A) DIV 8) + 1)
       (word 0:A word))`; `st:(store_name,A word_loc)fmap`; `curr:A word`;
    `ref_ptr_annot c (SOME (bvl_ByteArray fl (vals:byte list):data_v bvl_ref)):A word_loc`]
    get_real_addr_get_addr) THEN
  ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP heap_lookup_SPLIT o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "heap_lookup"))
      (concl th) && is_eq (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "Bytes")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ha:((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list` (X_CHOOSE_THEN `hb:((A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
      STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `(word_heap curr heap c STAR word_heap other (heap_expand limit) c)
      (fun2set ((m:A word->A word_loc),dm))` THEN
  ASM_REWRITE_TAC[word_heap_APPEND; word_heap_def; data_to_word_memoryProof_Bytes_def;
    LET_DEF; LET_END_DEF; word_el_def] THEN
  REWRITE_TAC[word_payload_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[misc_word_list_def; LENGTH_MAP; LENGTH_write_bytes; LENGTH_REPLICATE] THEN
  REWRITE_TAC[MP6AUX_COND_PULL; cond_STAR] THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_mul (word (heap_length (ha:((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list))) bytes_in_word =
      word_mul bytes_in_word (word (heap_length ha)):A word` SUBST1_TAC THENL
   [MATCH_ACCEPT_TAC WORD_MUL_SYM; ALL_TAC] THEN
  ABBREV_TAC `addr = word_add curr (word_mul bytes_in_word
    (word (heap_length (ha:((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list)))):A word` THEN
  EXISTS_TAC `make_byte_header c fl (LENGTH (vals:byte list)):A word` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (vals:byte list) DIV (dimindex (:A) DIV 8) + 1 < dimword(:A)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `2 EXP (dimindex (:A) - 4)` THEN ASM_REWRITE_TAC[dimword_def; LE_EXP] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD; GSYM dimword_def; MOD_LT] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP read_fun2set (MP6AUX_SEP_FACTOR
      `set_sep_one (addr:A word,
        wl_Word (make_byte_header c fl (LENGTH (vals:byte list)):A word))`
      th))) THEN SIMP_TAC[];
    MP6AUX_SEP_FRAME_TAC]);;

(* HOL4 line 14269 *)
let poly_inj_lemma = prove
 (`!a b a' c c'. a < b /\ a' < b /\ a + b * c = a' + b * c' ==> a = a' /\ c = c'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a' + b * c'`; `b:num`; `c:num`; `a:num`] DIVMOD_UNIQ) THEN
  MP_TAC(SPECL [`a' + b * c'`; `b:num`; `c':num`; `a':num`] DIVMOD_UNIQ) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN ASM_MESON_TAC[]);;

(* HOL4 line 14280 *)
let mw2n_inj = prove
 (`!x y. LENGTH x = LENGTH y ==> (mw2n (x:(A word)list) = mw2n y <=> x = y)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[mw2n_def; LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; CONS_11] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `t':(A word)list`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [`val (h:A word)`; `dimword(:A)`; `val (h':A word)`;
      `mw2n (t:(A word)list)`; `mw2n (t':(A word)list)`] poly_inj_lemma) THEN
    ASM_REWRITE_TAC[dimword_def; VAL_BOUND; VAL_EQ] THEN
    ASM_REWRITE_TAC[GSYM dimword_def];
    SIMP_TAC[]]);;

let MP6AUX_WB_ARITH = prove
 (`!L n k. 0 < k /\ L <= SUC n * k /\ SUC n <= L DIV k + 1 ==>
           L - k <= n * k /\ n <= (L - k) DIV k + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `L <= SUC n * k` THEN REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `k * n <= L` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM LE_RDIV_EQ; ARITH_RULE `0 < k ==> ~(k = 0)`] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[LE_0] THEN
  MATCH_MP_TAC(ARITH_RULE `n - 1 <= x ==> n <= x + 1`) THEN
  ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `0 < k ==> ~(k = 0)`; LEFT_SUB_DISTRIB; MULT_CLAUSES] THEN
  ASM_ARITH_TAC);;

let MP6AUX_TAKE_EQ_EL = prove
 (`!k (bs1:A list) bs2.
     LENGTH bs1 = LENGTH bs2 /\
     (!i. i < k /\ i < LENGTH bs1 ==> EL i bs1 = EL i bs2) ==>
     TAKE k bs1 = TAKE k bs2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_TAKE_EQ] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `n < k /\ n < LENGTH (bs2:A list)` STRIP_ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_TAKE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 14291 *)
let write_bytes_inj = prove
 (`!be. good_dimindex(:A) ==>
     !ws bs1 bs2.
       LENGTH bs1 = LENGTH bs2 /\
       LENGTH bs1 <= LENGTH ws * (dimindex(:A) DIV 8) /\
       LENGTH ws <= LENGTH bs1 DIV (dimindex(:A) DIV 8) + 1 ==>
       (write_bytes bs1 (ws:(A word)list) be = write_bytes bs2 ws be <=> bs1 = bs2)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?kk. 2 EXP kk = dimindex(:A) DIV 8 /\ 0 < dimindex(:A) DIV 8`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THENL [EXISTS_TAC `2`; EXISTS_TAC `3`] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[write_bytes_def; LENGTH; MULT_CLAUSES; LE] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[LENGTH_EQ_NIL];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REWRITE_TAC[write_bytes_def; LET_DEF; LET_END_DEF; CONS_11] THEN STRIP_TAC THEN
  SUBGOAL_THEN `DROP (dimindex(:A) DIV 8) bs1 = DROP (dimindex(:A) DIV 8) (bs2:byte list)`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`DROP (dimindex(:A) DIV 8) bs1:byte list`;
                                  `DROP (dimindex(:A) DIV 8) bs2:byte list`]) THEN
    ASM_REWRITE_TAC[LENGTH_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC MP6AUX_WB_ARITH THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `TAKE (dimindex(:A) DIV 8) bs1 = TAKE (dimindex(:A) DIV 8) (bs2:byte list)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC MP6AUX_TAKE_EQ_EL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`i:num`; `kk:num`; `be:bool`; `bs1:byte list`; `h:A word`]
      get_byte_bytes_to_word) THEN
    MP_TAC(ISPECL [`i:num`; `kk:num`; `be:bool`; `bs2:byte list`; `h:A word`]
      get_byte_bytes_to_word) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `i < LENGTH (bs2:byte list)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`dimindex(:A) DIV 8`; `bs1:byte list`] TAKE_DROP) THEN
  MP_TAC(ISPECL [`dimindex(:A) DIV 8`; `bs2:byte list`] TAKE_DROP) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4 line 14381: MIN_ADD *)
let data_to_word_memoryProof_MIN_ADD = prove
 (`!a b c. MIN a b + c = MIN (a + c) (b + c)`,
  REWRITE_TAC[MIN] THEN ARITH_TAC);;

(* HOL4 line 14387: MIN_SUB *)
let data_to_word_memoryProof_MIN_SUB = prove
 (`!a b c. MIN a b - c = MIN (a - c) (b - c)`,
  REWRITE_TAC[MIN] THEN ARITH_TAC);;

(* HOL4 line 14393 *)
let MAX_ADD = prove
 (`!a b c. MAX a b + c = MAX (a + c) (b + c)`,
  REWRITE_TAC[MAX] THEN ARITH_TAC);;

(* HOL4 line 14399 *)
let MAX_SUB = prove
 (`!a b c. MAX a b - c = MAX (a - c) (b - c)`,
  REWRITE_TAC[MAX] THEN ARITH_TAC);;

(* HOL4 line 14405 *)
let do_eq_IFF_vb_eq_size = prove
 (`(!(refs:(A bvl_ref)spt) v1 v2 b.
      data_do_eq refs v1 v2 = Eq_val b <=>
      ?n. vb_eq_size refs v1 v2 = SOME (n,b)) /\
   (!(refs:(A bvl_ref)spt) v1 v2 b.
      data_do_eq_list refs v1 v2 = Eq_val b <=>
      ?n. vb_eq_size_list refs v1 v2 = SOME (n,b))`,
  MATCH_MP_TAC data_do_eq_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN REWRITE_TAC[data_do_eq_def; vb_eq_size_def] THEN
  SIMP[MP6AUX_OPTION_MAP_SUC] THENL
   [(* CodePtr against an arbitrary value *)
    CASES_ON `x'':data_v` THEN REWRITE_TAC[vb_eq_size_def; option_DISTINCT];
    (* RefPtr, RefPtr *)
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; distinctness "eq_result"] THEN
    EVERY_CASE_TAC THEN
    REWRITE_TAC[UNWIND_THM1; option_DISTINCT; distinctness "eq_result";
                injectivity "eq_result"; option_INJ; PAIR_EQ];
    (* Block, Block *)
    GEN_TAC THEN COND_CASES_TAC THENL
     [REWRITE_TAC[] THEN COND_CASES_TAC THEN
      REWRITE_TAC[UNWIND_THM1; option_DISTINCT; distinctness "eq_result";
                  injectivity "eq_result"; option_INJ; PAIR_EQ];
      REWRITE_TAC[] THEN COND_CASES_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[MP6AUX_OPTION_MAP_SUC] THEN MESON_TAC[];
        REWRITE_TAC[UNWIND_THM1; option_DISTINCT; distinctness "eq_result";
                    injectivity "eq_result"; option_INJ; PAIR_EQ]]];
    (* CONS, CONS *)
    GEN_TAC THEN FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
    ASM_CASES_TAC `?n0 b0. vb_eq_size (refs:(A bvl_ref)spt) v1 v2 = SOME (n0,b0)` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `b0:bool` ASSUME_TAC)) THEN
      SUBGOAL_THEN `data_do_eq (refs:(A bvl_ref)spt) v1 v2 = Eq_val b0` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      ASM_CASES_TAC `b0:bool` THEN ASM_REWRITE_TAC[] THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `b0:bool` o check (fun th ->
          is_forall(concl th) && is_imp(snd(dest_forall(concl th))))) THEN
        ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
                        DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
        REWRITE_TAC(option_DISTINCT :: option_INJ :: PAIR_EQ :: all_case_eqs()) THEN
        MESON_TAC[];
        REWRITE_TAC[injectivity "eq_result"; option_INJ; PAIR_EQ] THEN MESON_TAC[]];
      SUBGOAL_THEN `vb_eq_size (refs:(A bvl_ref)spt) v1 v2 = NONE` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
        SPEC_TAC(`vb_eq_size (refs:(A bvl_ref)spt) v1 v2`, `x:(num#bool)option`) THEN
        REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; option_DISTINCT; option_INJ;
                    PAIR_EQ] THEN MESON_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT] THEN
      CASES_ON `data_do_eq (refs:(A bvl_ref)spt) v1 v2` THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `a:bool` o check (fun th ->
          is_forall(concl th) && is_iff(snd(dest_forall(concl th))))) THEN
        ASM_REWRITE_TAC[option_DISTINCT];
        CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "eq_result"]]]]);;

(* HOL4 line 14424 *)
let do_eq_IMP_vb_eq_size = prove
 (`!(refs:(A bvl_ref)spt) v1 v2 b.
     data_do_eq refs v1 v2 = Eq_val b ==> ?n. vb_eq_size refs v1 v2 = SOME (n,b)`,
  REWRITE_TAC[do_eq_IFF_vb_eq_size]);;

(* HOL4 line 14431 *)
let vb_eq_size_IMP_do_eq = prove
 (`!(refs:(A bvl_ref)spt) v1 v2 n b.
     vb_eq_size refs v1 v2 = SOME (n,b) ==> data_do_eq refs v1 v2 = Eq_val b`,
  MESON_TAC[do_eq_IFF_vb_eq_size]);;

(* HOL4 line 14438 *)
let memory_rel_ptr_vb_eq = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm v1 x1 v2 vars n b.
     memory_rel c be ts refs sp st m dm
       (CONS (v1,x1) (CONS (v2,x1:A word_loc) vars)) /\
     vb_eq_size refs v1 v2 = SOME (n,b) /\
     good_dimindex (:A) ==> b`,
  MESON_TAC[vb_eq_size_IMP_do_eq; memory_rel_ptr_eq]);;

let MP6AUX_MEMREL_LEN_SIZE = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars.
     memory_rel c be ts refs sp st m dm vars ==>
     data_to_word_config_len_size c + 2 < dimindex (:A)`,
  REWRITE_TAC[memory_rel_def; heap_in_memory_store_def] THEN REPEAT STRIP_TAC THEN
  MP6AUX_ASM_ARITH_TAC);;

let MP6AUX_WORD64_SPLIT32 = prove
 (`dimindex(:A) = 32 ==>
   !i j:int64. (word_extract 63 32 i:A word = word_extract 63 32 j /\
                word_extract 31 0 i:A word = word_extract 31 0 j) <=> i = j`,
  DISCH_TAC THEN REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_EXTRACT; DIMINDEX_64] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hi") (LABEL_TAC "lo")) THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `k < 32` THENL
   [REMOVE_THEN "lo" (MP_TAC o SPEC `k:num`) THEN
    ASM_SIMP_TAC[ADD_CLAUSES; ARITH_RULE `k < 32 ==> k <= 31`];
    REMOVE_THEN "hi" (MP_TAC o SPEC `k - 32`) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(k < 32) /\ k < 64 ==>
      k - 32 < 32 /\ (k - 32) + 32 <= 63 /\ (k - 32) + 32 = k`]]);;

let MP6AUX_WORD64_EQ64 = prove
 (`dimindex(:A) = 64 ==>
   !i j:int64. (word_extract 63 0 i:A word = word_extract 63 0 j) <=> i = j`,
  DISCH_TAC THEN REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_EXTRACT; DIMINDEX_64; ADD_CLAUSES] THEN
  MESON_TAC[ARITH_RULE `k < 64 ==> k <= 63`]);;

let MP6AUX_WORD_HEADER_SOME = prove
 (`!c st (w:A word) dm (m:A word -> A word_loc) a x.
     get_real_addr c st w = SOME a /\ a IN dm /\ m a = wl_Word x ==>
     word_header c st w dm m = SOME (a,x)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[word_header_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let MP6AUX_WORD_01 = prove
 (`good_dimindex(:A) ==> ~(word 0:A word = word 1) /\ ~(word 2:A word = word 1)`,
  DISCH_THEN(MP_TAC o MATCH_MP MP6AUX_DIMWORD_GE_2EXP32) THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; GSYM dimword_def] THEN DISCH_TAC THEN
  SUBGOAL_THEN `0 MOD dimword(:A) = 0 /\ 1 MOD dimword(:A) = 1 /\ 2 MOD dimword(:A) = 2`
    (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ARITH_TAC]);;

let MP6AUX_WORD_CMP_RES_1 = prove
 (`good_dimindex(:A) ==> !i j. (word_cmp_res i j = word 1:A word <=> i = j)`,
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MP6AUX_WORD_01) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[word_cmp_res_def] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let MP6AUX_NUM_BIG_HDR = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i w vars a x.
     memory_rel c be ts refs sp st m dm (CONS (data_Number i,wl_Word w) vars) /\
     good_dimindex(:A) /\ bit 0 w /\ get_real_addr c st w = SOME a /\ m a = wl_Word x ==>
     bit 2 x /\ bit 3 x /\ a IN dm /\ val (decode_length c x) < dimword(:A)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~small_int (:A) i` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_any_Number_IMP o
      CONJ (ASSUME `good_dimindex(:A)`)) THEN
    REWRITE_TAC[injectivity "word_loc"; UNWIND_THM1] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Number_bignum_IMP_ALT o
    (fun th -> end_itlist CONJ [th; ASSUME `~small_int (:A) i`;
                                ASSUME `good_dimindex(:A)`])) THEN
  REWRITE_TAC[injectivity "word_loc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:((A word#A word_loc)->bool)->bool`
    (X_CHOOSE_THEN `w':A word` (X_CHOOSE_THEN `x':A word`
      (X_CHOOSE_THEN `a':A word` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `a':A word = a` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
  SUBGOAL_THEN `x':A word = x` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[injectivity "word_loc"]; ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD; GSYM dimword_def; MOD_LT]);;

let MP6AUX_NUM_CMP_BB = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i1 i2 w1 w2 vars a1 x1 a2 x2.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number i1,wl_Word w1) (CONS (data_Number i2,wl_Word w2) vars)) /\
     good_dimindex(:A) /\ bit 0 w1 /\ bit 0 w2 /\
     get_real_addr c st w1 = SOME a1 /\ m a1 = wl_Word x1 /\
     get_real_addr c st w2 = SOME a2 /\ m a2 = wl_Word x2 ==>
     (~(x1 = x2) ==> ~(i1 = i2)) /\
     (x1 = x2 ==>
      ?r. word_cmp_loop (decode_length c x1)
            (word_add a1 (word_mul bytes_in_word (decode_length c x1)))
            (word_add a2 (word_mul bytes_in_word (decode_length c x1))) dm m = SOME r /\
          (r = word 1 <=> i1 = i2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MP6AUX_WORD_CMP_RES_1 (ASSUME `good_dimindex(:A)`)) THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP MP6AUX_WORD_01 (ASSUME `good_dimindex(:A)`)) THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Number_cmp
    (CONJ th (ASSUME `good_dimindex(:A)`)))) THEN
  REWRITE_TAC[injectivity "word_loc"; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Number_cmp
    (CONJ (MATCH_MP memory_rel_swap th) (ASSUME `good_dimindex(:A)`)))) THEN
  REWRITE_TAC[injectivity "word_loc"; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond (concl th) &&
      fst(dest_cond(concl th)) = `x1:A word = x2`)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\r:A word. r = word 1`) THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl))) THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `word_and x2 (word 16) = word 0:A word` THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
     [EXISTS_TAC `word_cmp_res i1 i2:A word`; EXISTS_TAC `word_cmp_res i2 i1:A word`] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

let MP6AUX_NUM_BIG_ADDR = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i w vars.
     memory_rel c be ts refs sp st m dm (CONS (data_Number i,wl_Word w) vars) /\
     good_dimindex(:A) /\ bit 0 w ==>
     ?a x. get_real_addr c st w = SOME a /\ m a = wl_Word x /\ a IN dm`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~small_int (:A) i` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_any_Number_IMP o
      CONJ (ASSUME `good_dimindex(:A)`)) THEN
    REWRITE_TAC[injectivity "word_loc"; UNWIND_THM1] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Number_bignum_IMP_ALT o
    (fun th -> end_itlist CONJ [th; ASSUME `~small_int (:A) i`;
                                ASSUME `good_dimindex(:A)`])) THEN
  REWRITE_TAC[injectivity "word_loc"] THEN STRIP_TAC THEN ASM_MESON_TAC[]);;

let MP6AUX_WEQ_NUM = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars i1 i2 l ck w1 w2.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number i1,wl_Word w1) (CONS (data_Number i2,wl_Word w2) vars)) /\
     dimword(:A) < l /\ good_dimindex(:A) ==>
     ?res l1 ck1. word_eq c st dm m l ck w1 w2 = SOME (res,l1,ck1) /\
                  ((i1 = i2) <=> res = word 1) /\ l <= l1 + dimword(:A)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MP6AUX_WORD_01 (ASSUME `good_dimindex(:A)`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `data_do_eq (refs:(data_v bvl_ref)spt) (data_Number i1) (data_Number i2) =
                Eq_val (i1 = i2)` ASSUME_TAC THENL [REWRITE_TAC[data_do_eq_def]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[word_eq_def] THEN
  ASM_CASES_TAC `w1:A word = w2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`word 1:A word`; `l:num`; `ck:num`] THEN REWRITE_TAC[LE_ADD] THEN
    MATCH_MP_TAC memory_rel_pointer_eq THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `bit 0 (w1:A word) /\ bit 0 (w2:A word)` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`word 0:A word`; `l:num`; `ck:num`] THEN
    ASM_REWRITE_TAC[LE_ADD] THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Number_cmp
      (CONJ th (ASSUME `good_dimindex(:A)`)))) THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Number_cmp
      (CONJ (MATCH_MP memory_rel_swap th) (ASSUME `good_dimindex(:A)`)))) THEN
    REWRITE_TAC[injectivity "word_loc"; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    ASM_CASES_TAC `bit 0 (w1:A word)` THEN ASM_CASES_TAC `bit 0 (w2:A word)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MP6AUX_NUM_BIG_ADDR o
    (fun th -> end_itlist CONJ [th; ASSUME `good_dimindex(:A)`; ASSUME `bit 0 (w1:A word)`])) THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:A word` (X_CHOOSE_THEN `x1:A word` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MP6AUX_NUM_BIG_ADDR o
    (fun th -> end_itlist CONJ [MATCH_MP memory_rel_tl th; ASSUME `good_dimindex(:A)`;
                                ASSUME `bit 0 (w2:A word)`])) THEN
  DISCH_THEN(X_CHOOSE_THEN `a2:A word` (X_CHOOSE_THEN `x2:A word` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `word_header c st (w1:A word) dm m = SOME (a1,x1) /\
                word_header c st (w2:A word) dm m = SOME (a2,x2)`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MP6AUX_WORD_HEADER_SOME THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MP6AUX_NUM_BIG_HDR o
    (fun th -> end_itlist CONJ [th; ASSUME `good_dimindex(:A)`; ASSUME `bit 0 (w1:A word)`;
       ASSUME `get_real_addr c st (w1:A word) = SOME a1`; ASSUME `(m:A word -> A word_loc) a1 = wl_Word x1`])) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(word_and x1 (word 12) = word 0:A word)` (fun th -> REWRITE_TAC[th]) THENL
   [ONCE_REWRITE_TAC[WORD_AND_SYM] THEN ASM_SIMP_TAC[bit_pattern_1100]; ALL_TAC] THEN
  MP_TAC(SPEC_ALL MP6AUX_NUM_CMP_BB) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `x1:A word = x2` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`word 0:A word`; `l:num`; `ck:num`] THEN
    ASM_SIMP_TAC[LE_ADD]] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_exists o concl)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:A word` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(l <= val (decode_length c (x1:A word)))` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`r:A word`; `l - 1 - val (decode_length c (x1:A word))`; `ck:num`] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MP6AUX_WORD_NE0 = prove
 (`good_dimindex(:A) ==> ~(word 1:A word = word 0) /\ ~(word 2:A word = word 0)`,
  DISCH_THEN(MP_TAC o MATCH_MP MP6AUX_DIMWORD_GE_2EXP32) THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; GSYM dimword_def] THEN DISCH_TAC THEN
  SUBGOAL_THEN `0 MOD dimword(:A) = 0 /\ 1 MOD dimword(:A) = 1 /\ 2 MOD dimword(:A) = 2`
    (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ARITH_TAC]);;

let MP6AUX_CMP_LOOP1 = prove
 (`!(m:A word -> A word_loc) dm x1 x2 u1 u2.
     good_dimindex(:A) /\
     word_add x1 bytes_in_word IN dm /\ word_add x2 bytes_in_word IN dm /\
     m (word_add x1 bytes_in_word) = wl_Word u1 /\
     m (word_add x2 bytes_in_word) = wl_Word u2 ==>
     ?r. word_cmp_loop (word 1) (word_add x1 (word_mul bytes_in_word (word 1)))
           (word_add x2 (word_mul bytes_in_word (word 1))) dm m = SOME r /\
         (r = word 1 <=> u1 = u2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP6AUX_WORD_NE0) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP6AUX_WORD_01) THEN
  REWRITE_TAC[WORD_RULE `word_mul (b:A word) (word 1) = b`] THEN
  ONCE_REWRITE_TAC[word_cmp_loop_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_SUB_REFL] THEN ONCE_REWRITE_TAC[word_cmp_loop_def] THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ; UNWIND_THM1] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ; UNWIND_THM1]);;
let MP6AUX_CMP_LOOP2 = prove
 (`!(m:A word -> A word_loc) dm x1 x2 u1 u2 v1 v2.
     good_dimindex(:A) /\
     word_add x1 bytes_in_word IN dm /\ word_add x2 bytes_in_word IN dm /\
     word_add x1 (word_shl bytes_in_word 1) IN dm /\
     word_add x2 (word_shl bytes_in_word 1) IN dm /\
     m (word_add x1 bytes_in_word) = wl_Word u1 /\
     m (word_add x2 bytes_in_word) = wl_Word u2 /\
     m (word_add x1 (word_shl bytes_in_word 1)) = wl_Word v1 /\
     m (word_add x2 (word_shl bytes_in_word 1)) = wl_Word v2 ==>
     ?r. word_cmp_loop (word 2) (word_add x1 (word_mul bytes_in_word (word 2)))
           (word_add x2 (word_mul bytes_in_word (word 2))) dm m = SOME r /\
         (r = word 1 <=> u1 = u2 /\ v1 = v2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP6AUX_WORD_NE0) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP6AUX_WORD_01) THEN
  SUBGOAL_THEN `!b:A word. word_mul b (word 2) = word_shl b 1` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[LSL_ONE] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ONCE_REWRITE_TAC[word_cmp_loop_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word 2) (word 1):A word = word 1`;
              WORD_RULE `word_sub (word_add (x:A word) (word_shl b 1)) b = word_add x b`] THEN
  ONCE_REWRITE_TAC[word_cmp_loop_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_SUB_REFL] THEN ONCE_REWRITE_TAC[word_cmp_loop_def] THEN
  REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ; UNWIND_THM1]));;

let MP6AUX_WEQ_W64 = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars i1 i2 l ck w1 w2.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Word64 i1,wl_Word w1) (CONS (data_Word64 i2,wl_Word w2) vars)) /\
     dimword(:A) < l /\ good_dimindex(:A) ==>
     ?res l1 ck1. word_eq c st dm m l ck w1 w2 = SOME (res,l1,ck1) /\
                  ((i1 = i2) <=> res = word 1) /\ l <= l1 + dimword(:A)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `data_do_eq (refs:(data_v bvl_ref)spt) (data_Word64 i1) (data_Word64 i2) =
                Eq_val (i1 = i2)` ASSUME_TAC THENL [REWRITE_TAC[data_do_eq_def]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[word_eq_def] THEN
  ASM_CASES_TAC `w1:A word = w2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`word 1:A word`; `l:num`; `ck:num`] THEN REWRITE_TAC[LE_ADD] THEN
    MATCH_MP_TAC memory_rel_pointer_eq THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Word64_IMP
    (CONJ th (ASSUME `good_dimindex(:A)`)))) THEN
  REWRITE_TAC[injectivity "word_loc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:num` (X_CHOOSE_THEN `y1:A word`
    (X_CHOOSE_THEN `h1:A word` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Word64_IMP
    (CONJ (MATCH_MP memory_rel_tail th) (ASSUME `good_dimindex(:A)`)))) THEN
  REWRITE_TAC[injectivity "word_loc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:num` (X_CHOOSE_THEN `y2:A word`
    (X_CHOOSE_THEN `h2:A word` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `bit 0 (w1:A word) /\ bit 0 (w2:A word)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[MP6AUX_GET_ADDR_BIT0]; ALL_TAC] THEN
  SUBGOAL_THEN `word_header c st (w1:A word) dm m = SOME (y1,h1) /\
                word_header c st (w2:A word) dm m = SOME (y2,h2)`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MP6AUX_WORD_HEADER_SOME THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(word_and h1 (word 12) = word 0:A word)` (fun th -> REWRITE_TAC[th]) THENL
   [ONCE_REWRITE_TAC[WORD_AND_SYM] THEN ASM_SIMP_TAC[bit_pattern_1100]; ALL_TAC] THEN
  SUBGOAL_THEN `dimindex(:A) = 32 \/ dimindex(:A) = 64` MP_TAC THENL
   [ASM_MESON_TAC[good_dimindex_def]; ALL_TAC] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl))) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  (SUBGOAL_THEN `h2:A word = h1` SUBST_ALL_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`m:A word -> A word_loc`; `dm:A word->bool`; `y1:A word`; `y2:A word`;
      `word_extract 63 32 (i1:int64):A word`; `word_extract 63 32 (i2:int64):A word`;
      `word_extract 31 0 (i1:int64):A word`; `word_extract 31 0 (i2:int64):A word`]
      MP6AUX_CMP_LOOP2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:A word` STRIP_ASSUME_TAC) THEN
    MP_TAC(MATCH_MP MP6AUX_DIMWORD_GE_2EXP32 (ASSUME `good_dimindex(:A)`)) THEN DISCH_TAC THEN
    SUBGOAL_THEN `val (word 2:A word) = 2` SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD; GSYM dimword_def] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(l <= 2)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`r:A word`; `l - 1 - 2`; `ck:num`] THEN
    ASM_REWRITE_TAC[GSYM(MATCH_MP MP6AUX_WORD64_SPLIT32 (ASSUME `dimindex(:A) = 32`))] THEN
    ASM_ARITH_TAC;
    MP_TAC(SPECL [`m:A word -> A word_loc`; `dm:A word->bool`; `y1:A word`; `y2:A word`;
      `word_extract 63 0 (i1:int64):A word`; `word_extract 63 0 (i2:int64):A word`]
      MP6AUX_CMP_LOOP1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:A word` STRIP_ASSUME_TAC) THEN
    MP_TAC(MATCH_MP MP6AUX_DIMWORD_GE_2EXP32 (ASSUME `good_dimindex(:A)`)) THEN DISCH_TAC THEN
    REWRITE_TAC[VAL_WORD_1] THEN
    SUBGOAL_THEN `~(l <= 1)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`r:A word`; `l - 1 - 1`; `ck:num`] THEN
    ASM_REWRITE_TAC[GSYM(MATCH_MP MP6AUX_WORD64_EQ64 (ASSUME `dimindex(:A) = 64`))] THEN
    ASM_ARITH_TAC]);;
let MP6AUX_REF_CLASS = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm p w vars a x.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr T p,wl_Word w) vars) /\
     good_dimindex(:A) /\ get_real_addr c st w = SOME a /\ m a = wl_Word x ==>
     ((bit 2 x /\ ~bit 4 x) <=> ?bs. lookup p refs = SOME (bvl_ByteArray T bs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_RefPtr_IMP_lemma) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:data_v bvl_ref` ASSUME_TAC) THEN
  ASM_REWRITE_TAC[option_INJ] THEN POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:data_v bvl_ref` (cases "bvl_ref")) THEN
  REWRITE_TAC[distinctness "bvl_ref"; injectivity "bvl_ref"; RIGHT_EXISTS_AND_THM;
              EXISTS_REFL] THEN
  DISCH_TAC THENL
   [FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun lk -> MP_TAC(MATCH_MP memory_rel_ValueArray_IMP
      (end_itlist CONJ [mr; lk; ASSUME `good_dimindex(:A)`]))));
    FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun lk -> MP_TAC(MATCH_MP memory_rel_ByteArray_IMP
      (end_itlist CONJ [mr; lk; ASSUME `good_dimindex(:A)`]))));
    FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun lk -> MP_TAC(MATCH_MP memory_rel_Thunk_IMP
      (end_itlist CONJ [mr; lk; ASSUME `good_dimindex(:A)`])))) THEN
    REWRITE_TAC[];
    FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun lk -> MP_TAC(MATCH_MP memory_rel_MutBlock_IMP_F
      (CONJ mr lk)))) THEN REWRITE_TAC[]] THEN
  REWRITE_TAC[injectivity "word_loc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `w':A word` (X_CHOOSE_THEN `a':A word`
    (X_CHOOSE_THEN `x':A word` STRIP_ASSUME_TAC))) THEN
  (SUBGOAL_THEN `x':A word = x` SUBST_ALL_TAC THENL
    [ASM_MESON_TAC[option_INJ; injectivity "word_loc"]; ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MP6AUX_BA_HDR = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl p w vars fl bs a x.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl p,wl_Word w) vars) /\
     lookup p refs = SOME (bvl_ByteArray fl bs) /\ good_dimindex(:A) /\
     get_real_addr c st w = SOME a /\ m a = wl_Word x ==>
     x = make_byte_header c fl (LENGTH bs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun lk -> MP_TAC(MATCH_MP memory_rel_ByteArray_IMP
    (end_itlist CONJ [mr; lk; ASSUME `good_dimindex(:A)`])))) THEN
  REWRITE_TAC[injectivity "word_loc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `w':A word` (X_CHOOSE_THEN `a':A word`
    (X_CHOOSE_THEN `x':A word` STRIP_ASSUME_TAC))) THEN
  ASM_MESON_TAC[option_INJ; injectivity "word_loc"]);;

let MP6AUX_REF_CASES_TAC (asl,w as g) =
  let v = find (fun v -> type_of v = `:data_v bvl_ref`) (frees w) in
  STRUCT_CASES_TAC(ISPEC v (cases "bvl_ref")) g;;

let MP6AUX_VB_REF = prove
 (`!(refs:(data_v bvl_ref)spt) p1 p2 n b.
     vb_eq_size refs (data_RefPtr T p1) (data_RefPtr T p2) = SOME (n,b) ==>
     n = 1 /\
     ((?bs1. lookup p1 refs = SOME (bvl_ByteArray T bs1)) <=>
      (?bs2. lookup p2 refs = SOME (bvl_ByteArray T bs2))) /\
     (!bs1 bs2. lookup p1 refs = SOME (bvl_ByteArray T bs1) /\
                lookup p2 refs = SOME (bvl_ByteArray T bs2) ==> (b <=> bs1 = bs2)) /\
     ((!bs1. ~(lookup p1 refs = SOME (bvl_ByteArray T bs1))) ==> (b <=> p1 = p2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vb_eq_size_def] THEN
  CASES_ON `lookup p1 (refs:(data_v bvl_ref)spt)` THEN
  CASES_ON `lookup p2 (refs:(data_v bvl_ref)spt)` THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  REPEAT MP6AUX_REF_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  REWRITE_TAC[distinctness "bvl_ref"; injectivity "bvl_ref"] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  MESON_TAC[]);;

let MP6AUX_BYTE_LEN = prove
 (`good_dimindex(:A) ==> !n. byte_len (:A) n = n DIV (dimindex(:A) DIV 8) + 1`,
  REWRITE_TAC[good_dimindex_def; byte_len_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let MP6AUX_BYTE_LEN_LE = prove
 (`good_dimindex(:A) ==> !n. n <= (n DIV (dimindex(:A) DIV 8) + 1) * (dimindex(:A) DIV 8)`,
  REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let MP6AUX_BA_USHR = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl p w vars fl bs a x.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl p,wl_Word w) vars) /\
     lookup p refs = SOME (bvl_ByteArray fl bs) /\ good_dimindex(:A) /\
     get_real_addr c st w = SOME a /\ m a = wl_Word x ==>
     LENGTH bs + 8 < dimword(:A) /\
     word_ushr x (dimindex(:A) - data_to_word_config_len_size c -
                  (if dimindex(:A) = 32 then 2 else 3)) =
     word (LENGTH bs + (if dimindex(:A) = 32 then 4 else 8))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun lk -> MP_TAC(MATCH_MP memory_rel_ByteArray_IMP
    (end_itlist CONJ [mr; lk; ASSUME `good_dimindex(:A)`])))) THEN
  REWRITE_TAC[injectivity "word_loc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `w':A word` (X_CHOOSE_THEN `a':A word`
    (X_CHOOSE_THEN `x':A word` STRIP_ASSUME_TAC))) THEN
  (SUBGOAL_THEN `x':A word = x` SUBST_ALL_TAC THENL
    [ASM_MESON_TAC[option_INJ; injectivity "word_loc"]; ALL_TAC]) THEN
  SUBGOAL_THEN `dimindex(:A) = 32 \/ dimindex(:A) = 64` MP_TAC THENL
   [ASM_MESON_TAC[good_dimindex_def]; ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[dimword_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MP6AUX_BA_CMP = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm p1 p2 w1 w2 vars bs1 bs2 a1 a2 h.
     memory_rel c be ts refs sp st m dm
       (CONS (data_RefPtr T p1,wl_Word w1) (CONS (data_RefPtr T p2,wl_Word w2) vars)) /\
     lookup p1 refs = SOME (bvl_ByteArray T bs1) /\
     lookup p2 refs = SOME (bvl_ByteArray T bs2) /\ good_dimindex(:A) /\
     get_real_addr c st w1 = SOME a1 /\ m a1 = wl_Word h /\
     get_real_addr c st w2 = SOME a2 /\ m a2 = wl_Word h ==>
     val (decode_length c h) < dimword(:A) /\
     ?r. word_cmp_loop (decode_length c h)
           (word_add a1 (word_mul bytes_in_word (decode_length c h)))
           (word_add a2 (word_mul bytes_in_word (decode_length c h))) dm m = SOME r /\
         (r = word 1 <=> bs1 = bs2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun mr -> MP_TAC(MATCH_MP memory_rel_ByteArray_words_IMP (end_itlist CONJ
    [mr; ASSUME `lookup p1 (refs:(data_v bvl_ref)spt) = SOME (bvl_ByteArray T bs1)`;
     ASSUME `good_dimindex(:A)`; ASSUME `get_real_addr c st (w1:A word) = SOME a1`]))) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:A word` (X_CHOOSE_THEN `f1:((A word#A word_loc)->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(fun mr -> MP_TAC(MATCH_MP memory_rel_ByteArray_words_IMP (end_itlist CONJ
    [MATCH_MP memory_rel_tail mr;
     ASSUME `lookup p2 (refs:(data_v bvl_ref)spt) = SOME (bvl_ByteArray T bs2)`;
     ASSUME `good_dimindex(:A)`; ASSUME `get_real_addr c st (w2:A word) = SOME a2`]))) THEN
  DISCH_THEN(X_CHOOSE_THEN `x2:A word` (X_CHOOSE_THEN `f2:((A word#A word_loc)->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `x1:A word = h /\ x2:A word = h` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [ASM_MESON_TAC[injectivity "word_loc"]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (bs1:byte list) = LENGTH (bs2:byte list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
      `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`; `dm:A word->bool`;
      `T`; `p1:num`; `w1:A word`; `CONS (data_RefPtr T p2,wl_Word (w2:A word)) vars`;
      `T`; `bs1:byte list`; `a1:A word`; `h:A word`] MP6AUX_BA_USHR) THEN
    MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
      `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`; `dm:A word->bool`;
      `T`; `p2:num`; `w2:A word`; `vars:(data_v#A word_loc)list`;
      `T`; `bs2:byte list`; `a2:A word`; `h:A word`] MP6AUX_BA_USHR) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP memory_rel_tail); ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      (try fst(dest_const(rator(lhs(concl th)))) = "word" with Failure _ -> false))) THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; GSYM dimword_def] THEN
    SUBGOAL_THEN `(LENGTH (bs1:byte list) + (if dimindex(:A) = 32 then 4 else 8)) MOD
                  dimword(:A) = LENGTH bs1 + (if dimindex(:A) = 32 then 4 else 8) /\
                  (LENGTH (bs2:byte list) + (if dimindex(:A) = 32 then 4 else 8)) MOD
                  dimword(:A) = LENGTH bs2 + (if dimindex(:A) = 32 then 4 else 8)`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN COND_CASES_TAC THEN ASM_ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:A word -> A word_loc`; `dm:A word->bool`;
    `write_bytes bs1 (REPLICATE (val (decode_length c (h:A word))) (word 0:A word)) be`;
    `write_bytes bs2 (REPLICATE (val (decode_length c (h:A word))) (word 0:A word)) be`;
    `f1:((A word#A word_loc)->bool)->bool`; `f2:((A word#A word_loc)->bool)->bool`;
    `a1:A word`; `a2:A word`] word_cmp_loop_thm) THEN
  REWRITE_TAC[LENGTH_write_bytes; LENGTH_REPLICATE; WORD_VAL] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[option_INJ; UNWIND_THM1] THEN
  MP_TAC(MATCH_MP MP6AUX_WORD_01 (ASSUME `good_dimindex(:A)`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `write_bytes bs1 (REPLICATE (val (decode_length c (h:A word))) (word 0:A word)) be =
                write_bytes bs2 (REPLICATE (val (decode_length c h)) (word 0)) be <=>
                bs1 = bs2` ASSUME_TAC THENL
   [MATCH_MP_TAC(MATCH_MP (SPEC `be:bool` write_bytes_inj) (ASSUME `good_dimindex(:A)`)) THEN
    ASM_REWRITE_TAC[LENGTH_REPLICATE; LE_REFL] THEN
    MATCH_ACCEPT_TAC(MATCH_MP MP6AUX_BYTE_LEN_LE (ASSUME `good_dimindex(:A)`));
    ALL_TAC] THEN
  MP_TAC(ISPECL
    [`write_bytes bs1 (REPLICATE (val (decode_length c (h:A word))) (word 0:A word)) be`;
     `write_bytes bs2 (REPLICATE (val (decode_length c (h:A word))) (word 0:A word)) be`]
    mw_cmp_thm) THEN
  REWRITE_TAC[LENGTH_write_bytes; LENGTH_REPLICATE] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
    [`write_bytes bs1 (REPLICATE (val (decode_length c (h:A word))) (word 0:A word)) be`;
     `write_bytes bs2 (REPLICATE (val (decode_length c (h:A word))) (word 0:A word)) be`]
    mw2n_inj) THEN
  REWRITE_TAC[LENGTH_write_bytes; LENGTH_REPLICATE] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;
let MP6AUX_WEQ_REF = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars p1 p2 l ck w1 w2 n b.
     memory_rel c be ts refs sp st m dm
       (CONS (data_RefPtr T p1,wl_Word w1) (CONS (data_RefPtr T p2,wl_Word w2) vars)) /\
     vb_eq_size refs (data_RefPtr T p1) (data_RefPtr T p2) = SOME (n,b) /\
     n * dimword(:A) < l /\ good_dimindex(:A) ==>
     ?res l1 ck1. word_eq c st dm m l ck w1 w2 = SOME (res,l1,ck1) /\
                  (b <=> res = word 1) /\ l <= l1 + n * dimword(:A)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP6AUX_VB_REF) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `n = 1`)) THEN
  REWRITE_TAC[MULT_CLAUSES] THEN RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
  MP_TAC(MATCH_MP MP6AUX_WORD_01 (ASSUME `good_dimindex(:A)`)) THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[word_eq_def] THEN
  ASM_CASES_TAC `w1:A word = w2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`word 1:A word`; `l:num`; `ck:num`] THEN REWRITE_TAC[LE_ADD] THEN
    FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun vb -> ACCEPT_TAC(MATCH_MP memory_rel_ptr_vb_eq
      (end_itlist CONJ [mr; vb; ASSUME `good_dimindex(:A)`]))));
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `~(p1:num = p2)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_RefPtr_EQ
      (CONJ th (ASSUME `good_dimindex(:A)`)))) THEN
    REWRITE_TAC[injectivity "word_loc"; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_RefPtr_T_IMP
    (CONJ th (ASSUME `good_dimindex(:A)`)))) THEN
  REWRITE_TAC[injectivity "word_loc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:A word` (X_CHOOSE_THEN `y1:A word`
    (X_CHOOSE_THEN `h1:A word` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `w1:A word = u1`)) THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_RefPtr_T_IMP
    (CONJ (MATCH_MP memory_rel_tail th) (ASSUME `good_dimindex(:A)`)))) THEN
  REWRITE_TAC[injectivity "word_loc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `u2:A word` (X_CHOOSE_THEN `y2:A word`
    (X_CHOOSE_THEN `h2:A word` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `w2:A word = u2`)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `word_header c st (w1:A word) dm m = SOME (y1,h1) /\
                word_header c st (w2:A word) dm m = SOME (y2,h2)`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MP6AUX_WORD_HEADER_SOME THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(word_and h1 (word 12) = word 0:A word)` (fun th -> REWRITE_TAC[th]) THENL
   [ONCE_REWRITE_TAC[WORD_AND_SYM] THEN ASM_SIMP_TAC[bit_pattern_1100] THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `bit 3 (h1:A word) <=> ~bit 2 h1`)) THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`; `dm:A word->bool`;
    `p1:num`; `w1:A word`; `CONS (data_RefPtr T p2,wl_Word (w2:A word)) vars`;
    `y1:A word`; `h1:A word`] MP6AUX_REF_CLASS) THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`; `dm:A word->bool`;
    `p2:num`; `w2:A word`; `vars:(data_v#A word_loc)list`;
    `y2:A word`; `h2:A word`] MP6AUX_REF_CLASS) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP memory_rel_tail); DISCH_TAC] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `?bs2. lookup p2 (refs:(data_v bvl_ref)spt) = SOME (bvl_ByteArray T bs2)` THENL
   [ALL_TAC;
    (* neither is a compare-by-contents byte array: different pointers *)
    SUBGOAL_THEN `~b` ASSUME_TAC THENL
     [SUBGOAL_THEN `!bs1. ~(lookup p1 (refs:(data_v bvl_ref)spt) = SOME (bvl_ByteArray T bs1))`
        (fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o check (is_imp o concl))) THENL
       [REWRITE_TAC[GSYM NOT_EXISTS_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(bit 2 (h1:A word) /\ ~bit 4 h1)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`word 0:A word`; `l:num`; `ck:num`] THEN ASM_REWRITE_TAC[LE_ADD] THEN
    ASM_CASES_TAC `h1:A word = h2` THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `h1:A word = h2`)) THEN
    REWRITE_TAC[] THEN
    ASM_CASES_TAC `bit 2 (h1:A word)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `bit 4 (h1:A word)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(CONJ (ASSUME `bit 2 (h1:A word)`) (ASSUME `~bit 4 (h1:A word)`)) THEN
    ASM_REWRITE_TAC[]] THEN
  (* both are compare-by-contents byte arrays *)
  FIRST_X_ASSUM(X_CHOOSE_TAC `bs2:byte list`) THEN
  SUBGOAL_THEN `?bs1. lookup p1 (refs:(data_v bvl_ref)spt) = SOME (bvl_ByteArray T bs1)`
    (X_CHOOSE_TAC `bs1:byte list`) THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `bs2:byte list` THEN REFL_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(b <=> bs1 = bs2:byte list)` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(bit 2 (h1:A word) /\ ~bit 4 h1) /\ (bit 2 (h2:A word) /\ ~bit 4 h2)`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN EXISTS_TAC `bs2:byte list` THEN REFL_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `h1:A word = h2` THENL
   [ALL_TAC;
    (* different headers: different arrays *)
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`word 0:A word`; `l:num`; `ck:num`] THEN
    ASM_REWRITE_TAC[LE_ADD] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(h1:A word = h2)` THEN
    MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
      `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`; `dm:A word->bool`;
      `T`; `p1:num`; `w1:A word`; `CONS (data_RefPtr T p2,wl_Word (w2:A word)) vars`;
      `T`; `bs2:byte list`; `y1:A word`; `h1:A word`] MP6AUX_BA_HDR) THEN
    MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
      `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`; `dm:A word->bool`;
      `T`; `p2:num`; `w2:A word`; `vars:(data_v#A word_loc)list`;
      `T`; `bs2:byte list`; `y2:A word`; `h2:A word`] MP6AUX_BA_HDR) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP memory_rel_tail); ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]] THEN
  (* same header: compare the bytes *)
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `h1:A word = h2`)) THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`; `dm:A word->bool`;
    `p1:num`; `p2:num`; `w1:A word`; `w2:A word`; `vars:(data_v#A word_loc)list`;
    `bs1:byte list`; `bs2:byte list`; `y1:A word`; `y2:A word`; `h1:A word`] MP6AUX_BA_CMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r:A word` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(l <= val (decode_length c (h1:A word)))` (fun th -> REWRITE_TAC[th]) THENL
   [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`r:A word`; `l - 1 - val (decode_length c (h1:A word))`; `ck:num`] THEN
  ASM_REWRITE_TAC[] THEN MP6AUX_ASM_ARITH_TAC);;

let MP6AUX_VB_BLOCK = prove
 (`!(refs:(data_v bvl_ref)spt) ts1 t1 vs1 ts2 t2 vs2 n b.
     vb_eq_size refs (data_Block ts1 t1 vs1) (data_Block ts2 t2 vs2) = SOME (n,b) ==>
     (data_isClos t1 vs1 \/ data_isClos t2 vs2 ==>
      data_isClos t1 vs1 /\ data_isClos t2 vs2 /\ n = 1 /\ b) /\
     (~(data_isClos t1 vs1 \/ data_isClos t2 vs2) /\ ~(t1 = t2 /\ LENGTH vs1 = LENGTH vs2)
      ==> n = 1 /\ ~b) /\
     (~(data_isClos t1 vs1 \/ data_isClos t2 vs2) /\ t1 = t2 /\ LENGTH vs1 = LENGTH vs2
      ==> ?k. vb_eq_size_list refs vs1 vs2 = SOME (k,b) /\ n = k + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vb_eq_size_def] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; PAIR_EQ; option_DISTINCT; MP6AUX_OPTION_MAP_SUC] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MP6AUX_BLOCK_PTR = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm ts1 t1 vs1 w vars.
     memory_rel c be ts refs sp st m dm (CONS (data_Block ts1 t1 vs1,wl_Word w) vars) /\
     good_dimindex(:A) ==>
     (~(vs1 = []) <=> bit 0 w) /\
     (bit 0 w ==>
      ?a x. get_real_addr c st w = SOME a /\ m a = wl_Word x /\ a IN dm /\
            ~bit 3 x /\ ~bit 2 x /\ decode_length c x = word (LENGTH vs1) /\
            LENGTH vs1 < dimword(:A) /\ encode_header c (4 * t1) (LENGTH vs1) = SOME x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Block_IMP
    (CONJ th (ASSUME `good_dimindex(:A)`)))) THEN
  REWRITE_TAC[injectivity "word_loc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `w':A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
  ASM_CASES_TAC `vs1:data_v list = []` THEN ASM_REWRITE_TAC[] THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `a:A word` (X_CHOOSE_THEN `x:A word` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`a:A word`; `x:A word`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `2 EXP (dimindex(:A) - 4)` THEN
    ASM_REWRITE_TAC[dimword_def; LE_EXP] THEN ARITH_TAC]);;
let MP6AUX_CLOS_BIT0 = prove
 (`!(vs:data_v list) t (w:A word).
     (~(vs = []) <=> bit 0 w) /\ data_isClos t vs ==> bit 0 w`,
  REWRITE_TAC[data_isClos_def] THEN MESON_TAC[]);;

let MP6AUX_EX3_TAC (asl,w as g) =
  let vs,bod = strip_exists w in
  let eq = fst(dest_conj bod) in
  let tr = rand(lhs eq) in
  let x,yz = dest_pair tr in let y,z = dest_pair yz in
  (EXISTS_TAC x THEN EXISTS_TAC y THEN EXISTS_TAC z THEN REWRITE_TAC[]) g;;

let MP6AUX_WEQ_BLOCK = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars ts1 t1 vs1 ts2 t2 vs2.
     (~(data_isClos t1 vs1 \/ data_isClos t2 vs2) /\ t1 = t2 /\ LENGTH vs1 = LENGTH vs2 ==>
      !l ck b w1 w2 n.
        memory_rel c be ts refs sp st m dm
          (APPEND (APPEND (eq_explode w1 m dm vs1) (eq_explode w2 m dm vs2)) vars) /\
        LENGTH vs2 = LENGTH vs1 /\ LENGTH vs1 < dimword (:A) /\
        eq_assum w1 m dm vs1 /\ eq_assum w2 m dm vs2 /\
        vb_eq_size_list refs vs1 vs2 = SOME (n,b) /\
        ck = MIN (vs_depth_list vs1) (vs_depth_list vs2) /\
        n * dimword (:A) < l /\ good_dimindex (:A) ==>
        ?res l1 ck1.
          word_eq_list c st dm m l ck (word (LENGTH vs1)) w1 w2 = SOME (res,l1,ck1) /\
          (b <=> res = word 1) /\ l <= l1 + n * dimword (:A)) ==>
     !l ck b w1 w2 n.
       memory_rel c be ts refs sp st m dm
         (CONS (data_Block ts1 t1 vs1,wl_Word w1)
           (CONS (data_Block ts2 t2 vs2,wl_Word w2) vars)) /\
       vb_eq_size refs (data_Block ts1 t1 vs1) (data_Block ts2 t2 vs2) = SOME (n,b) /\
       ck = MIN (vs_depth_list vs1) (vs_depth_list vs2) /\
       n * dimword (:A) < l /\ good_dimindex (:A) ==>
       ?res l1 ck1. word_eq c st dm m l ck w1 w2 = SOME (res,l1,ck1) /\
                    (b <=> res = word 1) /\ l <= l1 + n * dimword (:A)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MP6AUX_WORD_01 (ASSUME `good_dimindex(:A)`)) THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP6AUX_VB_BLOCK) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MP6AUX_BLOCK_PTR o
    (fun th -> CONJ th (ASSUME `good_dimindex(:A)`))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MP6AUX_BLOCK_PTR o
    (fun th -> CONJ (MATCH_MP memory_rel_tail th) (ASSUME `good_dimindex(:A)`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p2")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p1")) THEN
  ONCE_REWRITE_TAC[word_eq_def] THEN
  ASM_CASES_TAC `w1:A word = w2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`word 1:A word`; `l:num`; `ck:num`] THEN REWRITE_TAC[LE_ADD] THEN
    FIRST_ASSUM(fun mr -> FIRST_ASSUM(fun vb -> ACCEPT_TAC(MATCH_MP memory_rel_ptr_vb_eq
      (end_itlist CONJ [mr; vb; ASSUME `good_dimindex(:A)`]))));
    ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `data_isClos t1 (vs1:data_v list) \/ data_isClos t2 (vs2:data_v list)` THENL
   [(* two closures: equal by definition *)
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `data_isClos t1 (vs1:data_v list) \/
                                               data_isClos t2 (vs2:data_v list)`) o
      check (fun th -> is_imp(concl th) && is_disj(lhand(concl th)))) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `n = 1`)) THEN
    SUBGOAL_THEN `bit 0 (w1:A word) /\ bit 0 (w2:A word)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MP6AUX_CLOS_BIT0 THENL
       [EXISTS_TAC `vs1:data_v list` THEN EXISTS_TAC `t1:num`;
        EXISTS_TAC `vs2:data_v list` THEN EXISTS_TAC `t2:num`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "p1" (MP_TAC o C MP (ASSUME `bit 0 (w1:A word)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `a1:A word` (X_CHOOSE_THEN `x1:A word` STRIP_ASSUME_TAC)) THEN
    REMOVE_THEN "p2" (MP_TAC o C MP (ASSUME `bit 0 (w2:A word)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `a2:A word` (X_CHOOSE_THEN `x2:A word` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `word_header c st (w1:A word) dm m = SOME (a1,x1) /\
                  word_header c st (w2:A word) dm m = SOME (a2,x2)`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC MP6AUX_WORD_HEADER_SOME THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    SUBGOAL_THEN `word_and x1 (word 12) = word 0:A word` (fun th -> REWRITE_TAC[th]) THENL
     [ONCE_REWRITE_TAC[WORD_AND_SYM] THEN ASM_SIMP_TAC[bit_pattern_1100]; ALL_TAC] THEN
    SUBGOAL_THEN `word_is_clos c (x1:A word)` (fun th -> REWRITE_TAC[th]) THENL
     [FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_isClos (end_itlist CONJ
        [th; ASSUME `bit 0 (w1:A word)`; ASSUME `get_real_addr c st (w1:A word) = SOME a1`;
         ASSUME `(m:A word -> A word_loc) a1 = wl_Word x1`; ASSUME `good_dimindex(:A)`]))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP6AUX_EX3_TAC THEN ASM_REWRITE_TAC[LE_ADD; MULT_CLAUSES];
    ALL_TAC] THEN
  ASM_CASES_TAC `bit 0 (w1:A word) /\ bit 0 (w2:A word)` THENL
   [ALL_TAC;
    (* a small block: different words, different values *)
    SUBGOAL_THEN `~(t1:num = t2 /\ LENGTH (vs1:data_v list) = LENGTH (vs2:data_v list))`
      ASSUME_TAC THENL
     [ASM_CASES_TAC `bit 0 (w1:A word)` THENL
       [SUBGOAL_THEN `~bit 0 (w2:A word)` ASSUME_TAC THENL
         [UNDISCH_TAC `~(bit 0 (w1:A word) /\ bit 0 (w2:A word))` THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Block_Block_small_eq
          (end_itlist CONJ [MATCH_MP memory_rel_swap th; ASSUME `good_dimindex(:A)`;
             ONCE_REWRITE_RULE[EQ_SYM_EQ] (ASSUME `~(w1:A word = w2)`);
             ASSUME `~bit 0 (w2:A word)`]))) THEN
        MESON_TAC[];
        FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Block_Block_small_eq
          (end_itlist CONJ [th; ASSUME `good_dimindex(:A)`;
             ASSUME `~(w1:A word = w2)`; ASSUME `~bit 0 (w1:A word)`]))) THEN
        MESON_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      is_conj (lhand (concl th)) && is_neg (rand (lhand (concl th))))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP6AUX_EX3_TAC THEN ASM_REWRITE_TAC[LE_ADD]] THEN
  (* two pointers: compare the headers *)
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> concl th =
    `bit 0 (w1:A word) /\ bit 0 (w2:A word)`)) THEN
  ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "p1" (MP_TAC o C MP (ASSUME `bit 0 (w1:A word)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:A word` (X_CHOOSE_THEN `x1:A word` STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "p2" (MP_TAC o C MP (ASSUME `bit 0 (w2:A word)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `a2:A word` (X_CHOOSE_THEN `x2:A word` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `word_header c st (w1:A word) dm m = SOME (a1,x1) /\
                word_header c st (w2:A word) dm m = SOME (a2,x2)`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MP6AUX_WORD_HEADER_SOME THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `word_and x1 (word 12) = word 0:A word` (fun th -> REWRITE_TAC[th]) THENL
   [ONCE_REWRITE_TAC[WORD_AND_SYM] THEN ASM_SIMP_TAC[bit_pattern_1100]; ALL_TAC] THEN
  SUBGOAL_THEN `~word_is_clos c (x1:A word)` (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_isClos (end_itlist CONJ
      [th; ASSUME `bit 0 (w1:A word)`; ASSUME `get_real_addr c st (w1:A word) = SOME a1`;
       ASSUME `(m:A word -> A word_loc) a1 = wl_Word x1`; ASSUME `good_dimindex(:A)`]))) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `~(data_isClos t1 (vs1:data_v list) \/ data_isClos t2 (vs2:data_v list))` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `x1:A word = x2` THENL
   [ALL_TAC;
    SUBGOAL_THEN `~(t1:num = t2 /\ LENGTH (vs1:data_v list) = LENGTH (vs2:data_v list))`
      ASSUME_TAC THENL
     [STRIP_TAC THEN UNDISCH_TAC `~(x1:A word = x2)` THEN
      UNDISCH_TAC `encode_header c (4 * t1) (LENGTH (vs1:data_v list)) = SOME (x1:A word)` THEN
      UNDISCH_TAC `encode_header c (4 * t2) (LENGTH (vs2:data_v list)) = SOME (x2:A word)` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_INJ] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      is_conj (lhand (concl th)) && is_neg (rand (lhand (concl th))))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP6AUX_EX3_TAC THEN ASM_REWRITE_TAC[LE_ADD]] THEN
  (* equal headers: equal tags and lengths, compare the elements *)
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `x1:A word = x2`)) THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `4 * t1`; `LENGTH (vs1:data_v list)`; `4 * t2`;
    `LENGTH (vs2:data_v list)`; `x1:A word`; `x1:A word`] encode_header_EQ) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MP6AUX_MEMREL_LEN_SIZE); ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `4 * a = 4 * b <=> a = b`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `t1:num = t2`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) && is_exists (rand (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  MP_TAC(MATCH_MP MP6AUX_DIMWORD_GE_2EXP32 (ASSUME `good_dimindex(:A)`)) THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(l = 0)` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `(k + 1) * dimword(:A) < l` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `memory_rel c be ts refs sp st (m:A word -> A word_loc) dm
      (APPEND (APPEND (eq_explode (word_add a1 bytes_in_word) m dm vs1)
                      (eq_explode (word_add a2 bytes_in_word) m dm vs2)) vars) /\
      eq_assum (word_add a1 bytes_in_word) m dm vs1 /\
      eq_assum (word_add a2 bytes_in_word) m dm (vs2:data_v list)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Block_explode o (fun th -> end_itlist CONJ
      [th; ASSUME `bit 0 (w1:A word)`; ASSUME `get_real_addr c st (w1:A word) = SOME a1`;
       ASSUME `good_dimindex(:A)`])) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `memory_rel c be ts refs sp st (m:A word -> A word_loc) dm
        (CONS (data_Block ts2 t1 vs2,wl_Word w2)
          (APPEND (eq_explode (word_add a1 bytes_in_word) m dm vs1) vars))` MP_TAC THENL
     [FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC memory_rel_rearrange) THEN
      REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP memory_rel_Block_explode o (fun th -> end_itlist CONJ
      [th; ASSUME `bit 0 (w2:A word)`; ASSUME `get_real_addr c st (w2:A word) = SOME a2`;
       ASSUME `good_dimindex(:A)`])) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC memory_rel_rearrange) THEN
    REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) && is_forall (rand (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`l - 1`; `MIN (vs_depth_list vs1) (vs_depth_list (vs2:data_v list))`;
    `b:bool`; `word_add a1 bytes_in_word:A word`; `word_add a2 bytes_in_word:A word`; `k:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `(k + 1) * dimword(:A) < l` THEN
                  UNDISCH_TAC `4294967296 <= dimword(:A)` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `res:A word` (X_CHOOSE_THEN `l1:num`
    (X_CHOOSE_THEN `ck1:num` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`res:A word`; `l1:num`; `ck1:num`] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `l - 1 <= l1 + k * dimword(:A)` THEN
  UNDISCH_TAC `4294967296 <= dimword(:A)` THEN ARITH_TAC);;

let MP6AUX_VB_NOT_LOC = prove
 (`!(refs:(data_v bvl_ref)spt) v1 v2 x.
     vb_eq_size refs v1 v2 = SOME x ==>
     (!ptr. ~(v1 = data_RefPtr F ptr)) /\ (!n. ~(v1 = data_CodePtr n)) /\
     (!ptr. ~(v2 = data_RefPtr F ptr)) /\ (!n. ~(v2 = data_CodePtr n))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `v1:data_v` (CONJUNCT1 (cases "data_v"))) THEN
  STRUCT_CASES_TAC(SPEC `v2:data_v` (CONJUNCT1 (cases "data_v"))) THEN
  REWRITE_TAC[vb_eq_size_def; option_DISTINCT; distinctness "data_v"; injectivity "data_v"] THEN
  TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]);;

let MP6AUX_VB_LIST_CONS = prove
 (`!(refs:(data_v bvl_ref)spt) h1 t1 h2 t2 n b.
     vb_eq_size_list refs (CONS h1 t1) (CONS h2 t2) = SOME (n,b) ==>
     ?n0. (vb_eq_size refs h1 h2 = SOME (n0,F) /\ n = n0 + 1 /\ ~b) \/
          (vb_eq_size refs h1 h2 = SOME (n0,T) /\
           ?m0. vb_eq_size_list refs t1 t2 = SOME (m0,b) /\ n = m0 + n0 + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vb_eq_size_def] THEN
  SPEC_TAC(`vb_eq_size_list (refs:(data_v bvl_ref)spt) t1 t2`,`r2:(num#bool)option`) THEN
  SPEC_TAC(`vb_eq_size (refs:(data_v bvl_ref)spt) h1 h2`,`r1:(num#bool)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  REWRITE_TAC[option_INJ; PAIR_EQ; FORALL_BOOL_THM] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN MESON_TAC[]);;

let MP6AUX_MINMAX_CK = prove
 (`!a x b y. MIN (MAX (1 + a) x) (MAX (1 + b) y) - 1 = MIN (MAX a (x - 1)) (MAX b (y - 1)) /\
             MIN (MAX x (a + 1)) (MAX y (b + 1)) = MIN (MAX (1 + a) x) (MAX (1 + b) y)`,
  REWRITE_TAC[MIN; MAX] THEN REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let MP6AUX_NOT_LOC_WORD = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm v x vars.
     memory_rel c be ts refs sp st m dm (CONS (v,x) vars) /\
     (!ptr. ~(v = data_RefPtr F ptr)) /\ (!n. ~(v = data_CodePtr n)) ==>
     ?c. x = wl_Word c`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `x:A word_loc` (cases "word_loc")) THEN
  REWRITE_TAC[injectivity "word_loc"; distinctness "word_loc"; EXISTS_REFL] THEN
  STRIP_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_Loc o
    (fun th -> CONJ th (ASSUME `!ptr. ~(v = data_RefPtr F ptr)`))) THEN
  ASM_REWRITE_TAC[]);;

let MP6AUX_CK_POS = prove
 (`!a x b y. ~(MIN (MAX (1 + a) x) (MAX (1 + b) y) = 0)`,
  REWRITE_TAC[MIN; MAX] THEN REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let MP6AUX_WEQ_CONS = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars h1 t1 h2 t2.
  (!l ck b w1 w2 n.
     memory_rel c be ts refs sp st m dm
       (CONS (h1,wl_Word w1) (CONS (h2,wl_Word w2:A word_loc) vars)) /\
     vb_eq_size refs h1 h2 = SOME (n,b) /\ ck = MIN (vs_depth h1) (vs_depth h2) /\
     n * dimword(:A) < l /\ good_dimindex(:A) ==>
     ?res l1 ck1. word_eq c st dm m l ck w1 w2 = SOME (res,l1,ck1) /\
                  (b <=> res = word 1) /\ l <= l1 + n * dimword(:A)) /\
  (!n0. vb_eq_size refs h1 h2 = SOME (n0,T) ==>
     !l ck b w1 w2 n.
       memory_rel c be ts refs sp st m dm
         (APPEND (APPEND (eq_explode w1 m dm t1) (eq_explode w2 m dm t2)) vars) /\
       LENGTH t2 = LENGTH t1 /\ LENGTH t1 < dimword (:A) /\
       eq_assum w1 m dm t1 /\ eq_assum w2 m dm t2 /\
       vb_eq_size_list refs t1 t2 = SOME (n,b) /\
       ck = MIN (vs_depth_list t1) (vs_depth_list t2) /\
       n * dimword (:A) < l /\ good_dimindex (:A) ==>
       ?res l1 ck1. word_eq_list c st dm m l ck (word (LENGTH t1)) w1 w2 = SOME (res,l1,ck1) /\
                    (b <=> res = word 1) /\ l <= l1 + n * dimword (:A)) ==>
  !l ck b w1 w2 n.
    memory_rel c be ts refs sp st m dm
      (APPEND (APPEND (eq_explode w1 m dm (CONS h1 t1)) (eq_explode w2 m dm (CONS h2 t2))) vars) /\
    LENGTH (CONS h2 t2) = LENGTH (CONS h1 t1) /\ LENGTH (CONS h1 t1) < dimword (:A) /\
    eq_assum w1 m dm (CONS h1 t1) /\ eq_assum w2 m dm (CONS h2 t2) /\
    vb_eq_size_list refs (CONS h1 t1) (CONS h2 t2) = SOME (n,b) /\
    ck = MIN (vs_depth_list (CONS h1 t1)) (vs_depth_list (CONS h2 t2)) /\
    n * dimword (:A) < l /\ good_dimindex (:A) ==>
    ?res l1 ck1.
      word_eq_list c st dm m l ck (word (LENGTH (CONS h1 t1))) w1 w2 = SOME (res,l1,ck1) /\
      (b <=> res = word 1) /\ l <= l1 + n * dimword (:A)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hd") (LABEL_TAC "tl")) THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[eq_explode_def; eq_assum_def; LENGTH; APPEND; vs_depth_def; SUC_INJ] THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP MP6AUX_DIMWORD_GE_2EXP32 (ASSUME `good_dimindex(:A)`)) THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MP6AUX_VB_LIST_CONS) THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:num` (LABEL_TAC "vb")) THEN
  SUBGOAL_THEN `?y. vb_eq_size (refs:(data_v bvl_ref)spt) h1 h2 = SOME (n0,y)`
    (X_CHOOSE_THEN `y:bool` ASSUME_TAC) THENL
   [REMOVE_THEN "vb" (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC `F`; EXISTS_TAC `T`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `n0 + 1 <= n` ASSUME_TAC THENL
   [USE_THEN "vb" (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP6AUX_VB_NOT_LOC o check (fun th ->
    concl th = `vb_eq_size (refs:(data_v bvl_ref)spt) h1 h2 = SOME (n0,y)`)) THEN
  FIRST_ASSUM(fun mr -> MP_TAC(MATCH_MP MP6AUX_NOT_LOC_WORD (end_itlist CONJ
    [mr; ASSUME `!ptr. ~(h1 = data_RefPtr F ptr)`; ASSUME `!n. ~(h1 = data_CodePtr n)`]))) THEN
  DISCH_THEN(X_CHOOSE_TAC `c1:A word`) THEN
  SUBGOAL_THEN `memory_rel c be ts refs sp st (m:A word -> A word_loc) dm
      (CONS (h2,m w2) vars)` MP_TAC THENL
   [FIRST_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC memory_rel_rearrange) THEN
    REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun mr -> MP_TAC(MATCH_MP MP6AUX_NOT_LOC_WORD (end_itlist CONJ
    [mr; ASSUME `!ptr. ~(h2 = data_RefPtr F ptr)`; ASSUME `!n. ~(h2 = data_CodePtr n)`]))) THEN
  DISCH_THEN(X_CHOOSE_TAC `c2:A word`) THEN
  SUBGOAL_THEN `memory_rel c be ts refs sp st (m:A word -> A word_loc) dm
      (CONS (h1,wl_Word c1) (CONS (h2,wl_Word c2) vars))` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC memory_rel_rearrange) THEN
    ASM_REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(word (SUC (LENGTH (t1:data_v list))) = word 0:A word)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_0; GSYM dimword_def] THEN
    ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[CONJUNCT2 word_eq_def] THEN
  ASM_REWRITE_TAC[MP6AUX_CK_POS] THEN
  SUBGOAL_THEN `~(l = 0)` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `n * dimword(:A) < l` THEN ARITH_TAC; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[MP6AUX_MINMAX_CK] THEN
  SUBGOAL_THEN `(~y ==> n = n0 + 1 /\ ~b) /\
                (y ==> ?m0. vb_eq_size_list (refs:(data_v bvl_ref)spt) t1 t2 = SOME (m0,b) /\
                            n = m0 + n0 + 1)` STRIP_ASSUME_TAC THENL
   [REMOVE_THEN "vb" (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
      `vb_eq_size (refs:(data_v bvl_ref)spt) h1 h2 = SOME (n0,y)`)) THEN
    ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY(EXISTS_TAC `m0:num` THEN ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(n0 + 1) * dimword(:A) <= n * dimword(:A)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ALL_TAC] THEN
  REMOVE_THEN "hd" (MP_TAC o SPECL [`l - 1`; `MIN (vs_depth h1) (vs_depth h2)`; `y:bool`;
    `c1:A word`; `c2:A word`; `n0:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(n0 + 1) * dimword(:A) <= n * dimword(:A)` THEN
    UNDISCH_TAC `n * dimword(:A) < l` THEN UNDISCH_TAC `4294967296 <= dimword(:A)` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:A word` (X_CHOOSE_THEN `l1:num`
    (X_CHOOSE_THEN `k1:num` STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `st:(store_name,A word_loc)fmap`; `dm:A word->bool`;
    `m:A word -> A word_loc`; `l - 1`; `vs_depth h1`; `vs_depth h2`; `c1:A word`; `c2:A word`;
    `r0:A word`; `l1:num`; `k1:num`; `word 0:A word`] word_eq_min_max_clock) THEN
  DISCH_THEN(MP_TAC o SPECL [`vs_depth_list t1 - 1`; `vs_depth_list t2 - 1`] o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k1':num`) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r0:A word = word 1` THENL
   [ALL_TAC;
    SUBGOAL_THEN `~y` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `~y`) o
      check (fun th -> is_imp (concl th) && is_neg (lhand (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN MP6AUX_EX3_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `l - 1 <= l1 + n0 * dimword(:A)` THEN
    UNDISCH_TAC `4294967296 <= dimword(:A)` THEN ARITH_TAC] THEN
  SUBGOAL_THEN `y:bool` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m0:num` STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `y:bool`) o
    check (fun th -> is_imp (concl th) && is_var (lhand (concl th)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `n = m0 + n0 + 1`)) THEN
  SUBGOAL_THEN `~(l1 = 0) /\ m0 * dimword(:A) < l1 - 1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `l - 1 <= l1 + n0 * dimword(:A)` THEN
    UNDISCH_TAC `(m0 + n0 + 1) * dimword(:A) < l` THEN
    UNDISCH_TAC `4294967296 <= dimword(:A)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD1; WORD_ADD; WORD_ADD_SUB] THEN
  SUBGOAL_THEN `memory_rel c be ts refs sp st (m:A word -> A word_loc) dm
      (APPEND (APPEND (eq_explode (word_add w1 bytes_in_word) m dm t1)
                      (eq_explode (word_add w2 bytes_in_word) m dm t2)) vars)` ASSUME_TAC THENL
   [FIRST_ASSUM((fun th -> MP_TAC th THEN MATCH_MP_TAC memory_rel_rearrange) o
      check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "eq_explode"))
        (concl th))) THEN
    REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `vb_eq_size (refs:(data_v bvl_ref)spt) h1 h2 = SOME (n0,T)` ASSUME_TAC THENL
   [UNDISCH_TAC `vb_eq_size (refs:(data_v bvl_ref)spt) h1 h2 = SOME (n0,y)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "tl" (MP_TAC o SPEC `n0:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`l1 - 1`; `MIN (vs_depth_list t1) (vs_depth_list (t2:data_v list))`;
    `b:bool`; `word_add w1 bytes_in_word:A word`; `word_add w2 bytes_in_word:A word`;
    `m0:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `SUC (LENGTH (t1:data_v list)) < dimword(:A)` THEN ARITH_TAC;
                  ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:A word` (X_CHOOSE_THEN `l2:num`
    (X_CHOOSE_THEN `k2:num` STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `st:(store_name,A word_loc)fmap`; `dm:A word->bool`;
    `m:A word -> A word_loc`; `l1 - 1`; `vs_depth_list t1`; `vs_depth_list (t2:data_v list)`;
    `word_add w1 bytes_in_word:A word`; `word_add w2 bytes_in_word:A word`;
    `r2:A word`; `l2:num`; `k2:num`; `word (LENGTH (t1:data_v list)):A word`]
    word_eq_min_max_clock) THEN
  DISCH_THEN(MP_TAC o SPECL [`vs_depth h1 + 1`; `vs_depth h2 + 1`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[MP6AUX_MINMAX_CK] THEN DISCH_THEN(X_CHOOSE_TAC `k2':num`) THEN
  MAP_EVERY EXISTS_TAC [`r2:A word`; `l2:num`; `k2':num`] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `l - 1 <= l1 + n0 * dimword(:A)` THEN
  UNDISCH_TAC `l1 - 1 <= l2 + m0 * dimword(:A)` THEN
  UNDISCH_TAC `4294967296 <= dimword(:A)` THEN ARITH_TAC);;

(* HOL4 line 14448 (the unused bound variables t1 t2 of HOL4 are left out) *)
let word_eq_thm0 = prove
 (`!c be ts sp st (m:A word -> A word_loc) dm vars.
   (!refs v1 v2 l ck b w1 w2 n.
      memory_rel c be ts refs sp st m dm
        (CONS (v1,wl_Word w1) (CONS (v2,wl_Word w2:A word_loc) vars)) /\
      vb_eq_size refs v1 v2 = SOME (n,b) /\
      ck = MIN (vs_depth v1) (vs_depth v2) /\
      n * dimword (:A) < l /\
      good_dimindex (:A) ==>
      ?res l1 ck1. word_eq c st dm m l ck w1 w2 = SOME (res,l1,ck1) /\
                   (b <=> res = word 1) /\
                   l <= l1 + n * dimword (:A)) /\
   (!refs v1 v2 l ck b w1 w2 n.
      memory_rel c be ts refs sp st m dm
        (APPEND (APPEND (eq_explode w1 m dm v1) (eq_explode w2 m dm v2)) vars) /\
      LENGTH v2 = LENGTH v1 /\ LENGTH v1 < dimword (:A) /\
      eq_assum w1 m dm v1 /\ eq_assum w2 m dm v2 /\
      vb_eq_size_list refs v1 v2 = SOME (n,b) /\
      ck = MIN (vs_depth_list v1) (vs_depth_list v2) /\
      n * dimword (:A) < l /\
      good_dimindex (:A) ==>
      ?res l1 ck1.
        word_eq_list c st dm m l ck (word (LENGTH v1)) w1 w2 = SOME (res,l1,ck1) /\
        (b <=> res = word 1) /\
        l <= l1 + n * dimword (:A))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC vb_eq_size_ind THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`refs:(data_v bvl_ref)spt`; `v1:data_v`; `v2:data_v`] THEN
    STRUCT_CASES_TAC(SPEC `v1:data_v` (CONJUNCT1 (cases "data_v"))) THEN
    STRUCT_CASES_TAC(SPEC `v2:data_v` (CONJUNCT1 (cases "data_v"))) THEN
    REWRITE_TAC[vb_eq_size_def; option_DISTINCT; distinctness "data_v"; injectivity "data_v"] THENL
     [REWRITE_TAC[option_INJ; PAIR_EQ] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `1 = n`)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
        rhs (concl th) = `b:bool`)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN REWRITE_TAC[MULT_CLAUSES] THEN
      MATCH_MP_TAC MP6AUX_WEQ_NUM THEN
      MAP_EVERY EXISTS_TAC [`be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`; `sp:num`;
        `vars:(data_v#A word_loc)list`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[option_INJ; PAIR_EQ] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `1 = n`)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
        rhs (concl th) = `b:bool`)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN REWRITE_TAC[MULT_CLAUSES] THEN
      MATCH_MP_TAC MP6AUX_WEQ_W64 THEN
      MAP_EVERY EXISTS_TAC [`be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`; `sp:num`;
        `vars:(data_v#A word_loc)list`] THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN REWRITE_TAC[vs_depth_def] THEN
      MATCH_MP_TAC(REWRITE_RULE[vb_eq_size_def] MP6AUX_WEQ_BLOCK) THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`a0:num`; `a0':num`; `a1:num`] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      REPEAT GEN_TAC THEN ASM_CASES_TAC `a0:bool` THEN ASM_CASES_TAC `a0':bool` THEN
      ASM_REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
      MATCH_MP_TAC MP6AUX_WEQ_REF THEN
      MAP_EVERY EXISTS_TAC [`be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`; `sp:num`;
        `vars:(data_v#A word_loc)list`; `a1:num`; `a1':num`] THEN
      ASM_REWRITE_TAC[vb_eq_size_def]];
    MAP_EVERY X_GEN_TAC [`refs:(data_v bvl_ref)spt`; `vs1:data_v list`; `vs2:data_v list`] THEN
    STRUCT_CASES_TAC(SPEC `vs1:data_v list` (CONJUNCT2 (cases "data_v"))) THEN
    STRUCT_CASES_TAC(SPEC `vs2:data_v list` (CONJUNCT2 (cases "data_v"))) THEN
    REWRITE_TAC[NOT_CONS_NIL; CONS_11; LENGTH; NOT_SUC; ARITH_RULE `~(0 = SUC n)`] THENL
     [TRY DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[vb_eq_size_def; option_INJ; PAIR_EQ] THEN
      STRIP_TAC THEN ONCE_REWRITE_TAC[CONJUNCT2 word_eq_def] THEN REWRITE_TAC[] THEN
      MP6AUX_EX3_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `0 = n`)) THEN
      ASM_REWRITE_TAC[LE_ADD; MULT_CLAUSES; ADD_CLAUSES; LE_REFL];
      STRIP_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[NOT_CONS_NIL; CONS_11; LENGTH; NOT_SUC] MP6AUX_WEQ_CONS) THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`a1:data_v list`; `a1':data_v list`; `a0:data_v`;
          `a0':data_v`]) THEN REWRITE_TAC[];
        GEN_TAC THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`a0:data_v`; `a0':data_v`; `n0:num`; `T`;
          `a1:data_v list`; `a1':data_v list`]) THEN ASM_REWRITE_TAC[]]]]);;

(* HOL4 line 14788 *)
let word_eq_thm = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm v1 w1 v2 w2 vars b.
     memory_rel c be ts refs sp st m dm
       (CONS (v1,wl_Word w1) (CONS (v2,wl_Word w2:A word_loc) vars)) /\
     data_do_eq refs v1 v2 = Eq_val b /\ good_dimindex (:A) ==>
     ?res l1 ck1.
       word_eq c st dm m (MustTerminate_limit (:A) - 1)
         (MIN (vs_depth v1) (vs_depth v2)) w1 w2 = SOME (res,l1,ck1) /\
       (b <=> res = word 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `n:num` o MATCH_MP do_eq_IMP_vb_eq_size) THEN
  FIRST_ASSUM(fun mr -> MP_TAC(MATCH_MP memory_rel_limit (end_itlist CONJ
    [mr; ASSUME `vb_eq_size (refs:(data_v bvl_ref)spt) v1 v2 = SOME (n,b)`;
     ASSUME `good_dimindex(:A)`]))) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`refs:(data_v bvl_ref)spt`; `v1:data_v`; `v2:data_v`;
    `MustTerminate_limit (:A) - 1`; `MIN (vs_depth v1) (vs_depth v2)`; `b:bool`;
    `w1:A word`; `w2:A word`; `n:num`]
    (CONJUNCT1 (SPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `sp:num`;
      `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`; `dm:A word->bool`;
      `vars:(data_v#A word_loc)list`] word_eq_thm0))) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [MP_TAC(MATCH_MP MP6AUX_DIMWORD_GE_2EXP32 (ASSUME `good_dimindex(:A)`)) THEN
    UNDISCH_TAC `n * dimword(:A) < MustTerminate_limit (:A) - dimword(:A)` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `res:A word` (X_CHOOSE_THEN `l1:num`
    (X_CHOOSE_THEN `ck1:num` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`res:A word`; `l1:num`; `ck1:num`] THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 14807 *)
let word_mem_eq_def = cake_def
  `(word_mem_eq (a:A word) [] dm (m:A word -> A word_loc) = SOME T) /\
   (word_mem_eq a (CONS x xs) dm m =
      if ~(a IN dm) then NONE else
      if ~isWord (m a) then NONE else
      if ~(m a = wl_Word x) then SOME F else
        word_mem_eq (word_add a bytes_in_word) xs dm m)`;;

(* HOL4 line 14816 *)
let word_mem_eq_thm = prove
 (`!(m:A word -> A word_loc) dm xs ys a ff.
     (misc_word_list a (MAP wl_Word xs) STAR ff) (fun2set (m,dm)) /\
     LENGTH xs = LENGTH ys ==>
     word_mem_eq a ys dm m = SOME (xs = ys)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; word_mem_eq_def; MAP;
              misc_word_list_def; CONS_11] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP read_fun2set o REWRITE_RULE[GSYM STAR_ASSOC]) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[isWord_def; injectivity "word_loc"] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t':(A word)list`; `word_add a bytes_in_word:A word`;
    `set_sep_one (a:A word,wl_Word (h:A word)) STAR ff`] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "word_mem_eq"))
        (concl th) && is_forall (concl th) &&
      can (find_term (fun t -> t = `t:(A word)list`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
    fst(dest_const t) = "fun2set")) (concl th))) THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN AP_THM_TAC THEN
  CONV_TAC MP6AUX_STAR_AC_CONV);;

(* HOL4 line 14831 *)
let bignum_words_def = cake_def
  `bignum_words c i =
     let (sign,payload) = (i2mw i:bool#(A word)list) in
     match encode_header c (if sign then 7 else 3) (LENGTH payload):(A word)option with
       NONE -> NONE
     | SOME h -> SOME (CONS h payload)`;;

let MP6AUX_SIGN_TAG_WORD = prove
 (`!b. word_or (word_shl (b2w b) 2) (word 3):A word = word (if b then 7 else 3)`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[b2w_def] THEN
  MP6AUX_WORD_BITS_TAC THEN ARITH_TAC);;

let MP6AUX_SIGN_TAG = prove
 (`good_dimindex(:A) ==>
   !b. val (word_or (word_shl (b2w b) 2) (word 3):A word) = if b then 7 else 3`,
  DISCH_THEN(MP_TAC o MATCH_MP MP6AUX_DIMWORD_GE_2EXP32) THEN
  DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[MP6AUX_SIGN_TAG_WORD] THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[GSYM dimword_def] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

let MP6AUX_INT_SIGN_ABS = prove
 (`!i j:int. (i < &0 <=> j < &0) /\ num_of_int (abs i) = num_of_int (abs j) <=> i = j`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (MP_TAC o AP_TERM `int_of_num`)) THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN INT_ARITH_TAC);;

let MP6AUX_BIGNUM_PAYLOAD = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i w vars a.
     memory_rel c be ts refs sp st m dm (CONS (data_Number i,wl_Word w) vars) /\
     ~small_int (:A) i /\ good_dimindex (:A) /\ get_real_addr c st w = SOME a ==>
     a IN dm /\
     ?ff. (misc_word_list (word_add a bytes_in_word)
             (MAP wl_Word (n2mw (num_of_int (abs i)):(A word)list)) STAR ff)
          (fun2set (m,dm))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Number_bignum_IMP_ALT
     (end_itlist CONJ [th; ASSUME `~small_int (:A) i`; ASSUME `good_dimindex(:A)`]))) THEN
  REWRITE_TAC[injectivity "word_loc"] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "word_loc"]) THEN
  ASM_MESON_TAC[option_INJ]);;

(* HOL4 line 14839 *)
let memory_rel_Number_const_test = prove
 (CASE_TERM
  `!c be ts refs sp st (m:A word -> A word_loc) dm i w vars j.
     memory_rel c be ts refs sp st m dm (CONS (data_Number i,wl_Word (w:A word)) vars) /\
     good_dimindex (:A) ==>
     if small_int (:A) j then
       (Smallnum j = w <=> i = j)
     else
       match bignum_words c j with
         NONE -> ~(i = j)
       | SOME words ->
           if ~bit 0 w then ~(i = j) else
             ?a. get_real_addr c st w = SOME a /\
                 word_mem_eq a words dm m = SOME (i = j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `bit 0 (w:A word) <=> ~small_int (:A) i` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_any_Number_IMP o
      CONJ (ASSUME `good_dimindex(:A)`)) THEN
    REWRITE_TAC[injectivity "word_loc"] THEN MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [(* small_int j *)
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP IMP_memory_rel_Number
      (end_itlist CONJ [ASSUME `good_dimindex(:A)`; ASSUME `small_int (:A) j`; th]))) THEN
    DISCH_THEN(fun th -> MP_TAC(MATCH_MP memory_rel_Number_EQ
      (end_itlist CONJ [th; DISJ1 (ASSUME `small_int (:A) j`) `small_int (:A) i`;
                        ASSUME `good_dimindex(:A)`]))) THEN
    REWRITE_TAC[injectivity "word_loc"; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `small_int (:A) i` THENL
   [(* i small, j not: different *)
    SUBGOAL_THEN `~(i:int = j)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~bit 0 (w:A word)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    CASES_ON `bignum_words c j:((A word)list)option` THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  (* both bignums: compare the headers, then the payloads *)
  SUBGOAL_THEN `bit 0 (w:A word)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Number_bignum_header
    (end_itlist CONJ [th; ASSUME `~small_int (:A) i`; ASSUME `good_dimindex(:A)`]))) THEN
  REWRITE_TAC[injectivity "word_loc"; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A word` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP MP6AUX_SIGN_TAG (ASSUME `good_dimindex(:A)`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP6AUX_SIGN_TAG_WORD]) THEN
  SUBGOAL_THEN `encode_header c (if i < &0 then 7 else 3)
     (LENGTH (n2mw (num_of_int (abs i)):(A word)list)) =
     SOME (make_header c (word (if i < &0 then 7 else 3))
       (LENGTH (n2mw (num_of_int (abs i)):(A word)list)):A word)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(rator(concl th))) = "IS_SOME" with Failure _ -> false)) THEN
    REWRITE_TAC[encode_header_def] THEN COND_CASES_TAC THEN REWRITE_TAC[IS_SOME_DEF];
    ALL_TAC] THEN
  REWRITE_TAC[bignum_words_def; i2mw_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `encode_header c (if j < &0 then 7 else 3)
     (LENGTH (n2mw (num_of_int (abs j)):(A word)list)):(A word)option` THEN
  CASE_REWRITE_TAC[] THENL
   [(* no header for j: then i <> j *)
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try rhs(concl th) = `NONE:(A word)option` with Failure _ -> false)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `a:A word` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(MATCH_MP MP6AUX_BIGNUM_PAYLOAD (end_itlist CONJ
    [ASSUME `memory_rel c be ts refs sp st (m:A word -> A word_loc) dm
               (CONS (data_Number i,wl_Word w) vars)`;
     ASSUME `~small_int (:A) i`; ASSUME `good_dimindex(:A)`;
     ASSUME `get_real_addr c st (w:A word) = SOME a`])) THEN STRIP_TAC THEN
  REWRITE_TAC[word_mem_eq_def] THEN ASM_REWRITE_TAC[isWord_def; injectivity "word_loc"] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `if (i:int) < &0 then 7 else 3`;
     `LENGTH (n2mw (num_of_int (abs (i:int))):(A word)list)`; `if (j:int) < &0 then 7 else 3`;
     `LENGTH (n2mw (num_of_int (abs (j:int))):(A word)list)`;
     `make_header (c:data_to_word_config) (word (if (i:int) < &0 then 7 else 3))
        (LENGTH (n2mw (num_of_int (abs i)):(A word)list)):A word`; `a':A word`]
     encode_header_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MP6AUX_MEMREL_LEN_SIZE);
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `((if (i:int) < &0 then 7 else 3) = (if (j:int) < &0 then 7 else 3)) <=>
                (i < &0 <=> j < &0)` SUBST1_TAC THENL
   [REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `((i:int) < &0 <=> (j:int) < &0) /\
     LENGTH (n2mw (num_of_int (abs i)):(A word)list) =
     LENGTH (n2mw (num_of_int (abs j)):(A word)list)` THEN ASM_REWRITE_TAC[] THENL
   [POP_ASSUM STRIP_ASSUME_TAC THEN
    SUBGOAL_THEN `(i:int = j) <=> (n2mw (num_of_int (abs i)):(A word)list =
                                   n2mw (num_of_int (abs j)))` SUBST1_TAC THENL
     [REWRITE_TAC[n2mw_11; GSYM MP6AUX_INT_SIGN_ABS] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC word_mem_eq_thm THEN ASM_MESON_TAC[]];
    REWRITE_TAC[option_INJ] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[]]);;

let MP6AUX_WORD64_HEADER = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm w64 v vars.
     memory_rel c be ts refs sp st m dm (CONS (data_Word64 w64,v) vars) ==>
     IS_SOME (encode_header c 3 (if dimindex(:A) < 64 then 2 else 1):(A word)option)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[memory_rel_def; word_ml_inv_def; abs_ml_inv_def; bc_stack_ref_inv_def;
              MAP] THEN
  REWRITE_TAC[LIST_REL_CONS2] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL2]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl) o
    check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "v_inv")) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "v_inv")) (concl th) && not (is_forall (concl th)) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "ALL2"))
        (concl th)))) THEN
  REWRITE_TAC[v_inv_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "heap_in_memory_store")) (concl th))) THEN
  REWRITE_TAC[heap_in_memory_store_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP heap_lookup_SPLIT o check (fun th -> is_eq (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "Word64Rep")) (concl th))) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "word_heap")) (concl th))) THEN
  ASM_REWRITE_TAC[word_heap_APPEND; word_heap_def; Word64Rep_def] THEN
  ASM_CASES_TAC `dimindex(:A) < 64` THEN
  ASM_REWRITE_TAC[word_el_def; word_payload_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[MP6AUX_COND_PULL; cond_STAR] THEN SIMP_TAC[]);;

(* HOL4 line 14901 *)
let memory_rel_Word64_const_test = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i v vars j.
     memory_rel c be ts refs sp st m dm (CONS (data_Word64 i,v) vars) /\
     good_dimindex (:A) ==>
     ?(w:A word) a words h.
       v = wl_Word w /\ get_real_addr c st w = SOME a /\
       word_mem_eq (word_add a bytes_in_word) words dm m = SOME (i = j) /\
       encode_header c 3 (LENGTH words) = SOME (h:A word) /\
       if dimindex (:A) < 64 then
         words = [word_extract 63 32 j; word_extract 31 0 j]
       else
         words = [word_extract 63 0 j]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP6AUX_WORD64_HEADER) THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Word64_IMP
    (CONJ th (ASSUME `good_dimindex(:A)`)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr:num` (X_CHOOSE_THEN `x:A word`
    (X_CHOOSE_THEN `hw:A word` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `get_addr c ptr (wl_Word (word 0)):A word` THEN EXISTS_TAC `x:A word` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `dimindex(:A) = 32 \/ dimindex(:A) = 64` MP_TAC THENL
   [ASM_MESON_TAC[good_dimindex_def]; ALL_TAC] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl))) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[cases "option"; IS_SOME_DEF]
    `IS_SOME (x:(A word)option) ==> ?h. x = SOME h`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `h:A word`) THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1; LEFT_EXISTS_AND_THM] THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  UNDISCH_TAC `encode_header c 3 (if dimindex(:A) < 64 then 2 else 1) = SOME (h:A word)` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THENL
   [(* 32 bits: two payload words *)
    EXISTS_TAC `[word_extract 63 32 (j:int64); word_extract 31 0 j]:(A word)list` THEN
    REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[word_mem_eq_def; GSYM WORD_ADD_ASSOC; GSYM LSL_ONE] THEN
    ASM_REWRITE_TAC[isWord_def; injectivity "word_loc"] THEN
    REWRITE_TAC[GSYM(MATCH_MP MP6AUX_WORD64_SPLIT32 (ASSUME `dimindex(:A) = 32`))] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ];
    (* 64 bits: one payload word *)
    EXISTS_TAC `[word_extract 63 0 (j:int64)]:(A word)list` THEN
    REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[word_mem_eq_def] THEN
    ASM_REWRITE_TAC[isWord_def; injectivity "word_loc"] THEN
    REWRITE_TAC[GSYM(MATCH_MP MP6AUX_WORD64_EQ64 (ASSUME `dimindex(:A) = 64`))] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ]]);;

(* HOL4 line 14943 *)
let or_seven_eq = prove
 (`!w v:A word k.
     ~(word_shl w k = word_shl v k) /\ 2 < k ==>
     ~(word_or (word_shl w k) (word 7) = word_or (word_shl v k) (word 7))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR; BIT_WORD_SHL; MP6AUX_BIT_WORD] THEN
  CONV_TAC(DEPTH_CONV MP6AUX_NUMBIT_CONV) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN STRIP_TAC THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  ASM_CASES_TAC `k <= i:num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(i = 0) /\ ~(i = 1) /\ ~(i = 2)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let MP6AUX_SHL_INJ = prove
 (`!x y k. x * 2 EXP k < 2 EXP dimindex(:A) /\ y * 2 EXP k < 2 EXP dimindex(:A) ==>
           (word_shl (word x) k = word_shl (word y) k:A word <=> x = y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD] THEN
  SUBGOAL_THEN `!z. z <= z * 2 EXP k` ASSUME_TAC THENL
   [GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `z = z * 1`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL; ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `x < 2 EXP dimindex(:A) /\ y < 2 EXP dimindex(:A)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LET_TRANS]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_LT] THEN
  REWRITE_TAC[EQ_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ]);;

let MP6AUX_DIV_BOUND = prove
 (`!m j L K. m DIV (2 EXP j) + 1 < 2 EXP L ==>
             (m + 2 EXP j) * 2 EXP K < 2 EXP (L + j + K)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `m + 2 EXP j < 2 EXP L * 2 EXP j` ASSUME_TAC THENL
   [MP_TAC(SPECL [`m:num`; `2 EXP j`] DIVISION) THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN `(m DIV 2 EXP j + 2) * 2 EXP j <= 2 EXP L * 2 EXP j` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM ADD_ASSOC; EXP_ADD; MULT_ASSOC] THEN
  ASM_REWRITE_TAC[LT_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ]);;

(* HOL4 line 14954 *)
let make_byte_header_eq = prove
 (`!c m n.
     byte_len (:A) m < 2 EXP data_to_word_config_len_size c /\
     byte_len (:A) m < 2 EXP (dimindex (:A) - 4) /\
     byte_len (:A) n < 2 EXP data_to_word_config_len_size c /\
     byte_len (:A) n < 2 EXP (dimindex (:A) - 4) /\
     good_dimindex (:A) /\
     2 < dimindex (:A) - (if dimindex (:A) = 32 then 2 else 3) -
         data_to_word_config_len_size c ==>
     (make_byte_header c T m = make_byte_header c T n:A word <=> m = n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def; byte_len_def] THEN
  REWRITE_TAC[make_byte_header_def; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && lhs(concl th) = `dimindex(:A)`
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th else failwith "") THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  EQ_TAC THEN SIMP_TAC[] THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC or_seven_eq THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`m:num`; `2`; `data_to_word_config_len_size c`;
      `30 - data_to_word_config_len_size c`] MP6AUX_DIV_BOUND) THEN
    MP_TAC(SPECL [`n:num`; `2`; `data_to_word_config_len_size c`;
      `30 - data_to_word_config_len_size c`] MP6AUX_DIV_BOUND);
    MP_TAC(SPECL [`m:num`; `3`; `data_to_word_config_len_size c`;
      `61 - data_to_word_config_len_size c`] MP6AUX_DIV_BOUND) THEN
    MP_TAC(SPECL [`n:num`; `3`; `data_to_word_config_len_size c`;
      `61 - data_to_word_config_len_size c`] MP6AUX_DIV_BOUND)] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `2 < 30 - l ==> l + 2 + 30 - l = 32`;
               ARITH_RULE `2 < 61 - l ==> l + 3 + 61 - l = 64`] THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`m + 4`; `n + 4`; `30 - data_to_word_config_len_size c`]
    MP6AUX_SHL_INJ) THEN
  MP_TAC(ISPECL [`m + 8`; `n + 8`; `61 - data_to_word_config_len_size c`]
    MP6AUX_SHL_INJ) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[EQ_ADD_RCANCEL]);;

let MP6AUX_MEMREL_LEN_SIZE7 = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars.
     memory_rel c be ts refs sp st m dm vars ==>
     data_to_word_config_len_size c + 7 < dimindex (:A)`,
  REWRITE_TAC[memory_rel_def; heap_in_memory_store_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let MP6AUX_MEMREL_BE = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars.
     memory_rel c be ts refs sp st m dm vars ==> data_to_word_config_be c = be`,
  REWRITE_TAC[memory_rel_def; word_ml_inv_def; abs_ml_inv_def; bc_stack_ref_inv_def;
              be_ok_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MP6AUX_USHR_EQ_BOUND = prove
 (`!(x:A word) s n. s <= dimindex(:A) /\ n < dimword(:A) /\ word_ushr x s = word n ==>
                    n < 2 EXP (dimindex(:A) - s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n = val(word_ushr (x:A word) s)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD; GSYM dimword_def; MOD_LT]; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_USHR] THEN SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[GSYM EXP_ADD] THEN
  ASM_SIMP_TAC[ARITH_RULE `s <= d ==> s + d - s = d`; VAL_BOUND]);;

let MP6AUX_BYTEARRAY_BOUNDS = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl p v vars fl vals.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl p,v:A word_loc) vars) /\
     lookup p refs = SOME (bvl_ByteArray fl vals) /\ good_dimindex (:A) ==>
     byte_len (:A) (LENGTH vals) < 2 EXP (dimindex(:A) - 4) /\
     byte_len (:A) (LENGTH vals) < 2 EXP (data_to_word_config_len_size c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP6AUX_MEMREL_LEN_SIZE7) THEN
  MP_TAC(SPEC_ALL memory_rel_ByteArray_IMP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word` (X_CHOOSE_THEN `a:A word`
    (X_CHOOSE_THEN `x:A word` (MP_TAC o last o CONJUNCTS)))) THEN
  SUBGOAL_THEN `dimindex(:A) = 32 \/ dimindex(:A) = 64` MP_TAC THENL
   [ASM_MESON_TAC[good_dimindex_def]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[byte_len_def] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THENL
   [MP_TAC(ISPECL [`x:A word`; `dimindex(:A) - data_to_word_config_len_size c - 2`;
                   `LENGTH (vals:byte list) + 4`] MP6AUX_USHR_EQ_BOUND);
    MP_TAC(ISPECL [`x:A word`; `dimindex(:A) - data_to_word_config_len_size c - 3`;
                   `LENGTH (vals:byte list) + 8`] MP6AUX_USHR_EQ_BOUND)] THEN
  ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THENL
   [SUBGOAL_THEN `32 - (32 - data_to_word_config_len_size c - 2) =
                  data_to_word_config_len_size c + 2` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC];
    SUBGOAL_THEN `64 - (64 - data_to_word_config_len_size c - 3) =
                  data_to_word_config_len_size c + 3` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC]] THEN
  REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let MP6AUX_CHR_VAL_WORD_ORD = prove
 (`!c. CHR (val (word (ORD c):byte)) = c`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT; ORD_BOUND; CHR_ORD]);;

let MP6AUX_WORD_ORD_CHR_VAL = prove
 (`!b:byte. word (ORD (CHR (val b))) = b`,
  GEN_TAC THEN MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[ORD_CHR_RWT; WORD_VAL]);;

let MP6AUX_BYTES_STR = prove
 (`!(other:byte list) s.
     other = MAP (word o ORD) (explode s) <=> s = implode (MAP (CHR o val) other)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM MAP_o; explode_implode] THEN
  REWRITE_TAC[o_DEF; MP6AUX_CHR_VAL_WORD_ORD; MP6AUX_WORD_ORD_CHR_VAL; MAP_ID;
              implode_explode]);;

let MP6AUX_MAP_GET_WORD = prove
 (`!l:(A word)list. MAP (get_Word o SND) (MAP (\w. (F,wl_Word w)) l) = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; o_THM; SND; get_Word_def]);;

(* HOL4 line 14987 *)
let memory_rel_String_const_test = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl i v vars other s.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl i,v) vars) /\
     lookup i refs = SOME (bvl_ByteArray T other) /\
     good_dimindex (:A) ==>
     let t = implode (MAP (CHR o val) other) in
     (part_to_words c LN (clos_Str s) (word 0:A word) = NONE ==> ~(s = t)) /\
     !x res.
       part_to_words c LN (clos_Str s) (word 0) = SOME (x,res) ==>
       ?(w:A word) a.
         v = wl_Word w /\ get_real_addr c st w = SOME a /\
         word_mem_eq a (MAP (get_Word o SND) res) dm m = SOME (s = t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(MATCH_MP MP6AUX_BYTEARRAY_BOUNDS (end_itlist CONJ
    [ASSUME `memory_rel c be ts refs sp st (m:A word -> A word_loc) dm
               (CONS (data_RefPtr bl i,v) vars)`;
     ASSUME `lookup i (refs:(data_v bvl_ref)spt) = SOME (bvl_ByteArray T other)`;
     ASSUME `good_dimindex(:A)`])) THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP6AUX_MEMREL_LEN_SIZE7) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP6AUX_MEMREL_BE) THEN
  REWRITE_TAC[part_to_words_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[LENGTH_MAP; LENGTH_explode] THEN
  ASM_CASES_TAC `byte_len (:A) (strlen s) < 2 EXP (dimindex (:A) - 4) /\
                 byte_len (:A) (strlen s) < 2 EXP data_to_word_config_len_size c` THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THENL
   [ALL_TAC;
    (* no encoding: the string is longer than the byte array *)
    DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    ASM_REWRITE_TAC[strlen_def; LENGTH_MAP]] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[MP6AUX_MAP_GET_WORD] THEN
  MP_TAC(MATCH_MP memory_rel_ByteArray_IMP (end_itlist CONJ
    [ASSUME `memory_rel c be ts refs sp st (m:A word -> A word_loc) dm
               (CONS (data_RefPtr bl i,v) vars)`;
     ASSUME `lookup i (refs:(data_v bvl_ref)spt) = SOME (bvl_ByteArray T other)`;
     ASSUME `good_dimindex(:A)`])) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word` (X_CHOOSE_THEN `a:A word`
    (X_CHOOSE_THEN `hx:A word` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `hx:A word`)) THEN
  EXISTS_TAC `w:A word` THEN EXISTS_TAC `a:A word` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[word_mem_eq_def] THEN ASM_REWRITE_TAC[isWord_def; injectivity "word_loc"] THEN
  (* compare the headers *)
  MP_TAC(ISPECL [`c:data_to_word_config`; `LENGTH (other:byte list)`; `strlen s`]
    make_byte_header_eq) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
                  DISCH_THEN SUBST1_TAC] THEN
  ASM_CASES_TAC `LENGTH (other:byte list) = strlen s` THEN ASM_REWRITE_TAC[option_INJ] THENL
   [ALL_TAC;
    DISCH_THEN SUBST_ALL_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[strlen_def; LENGTH_MAP]] THEN
  (* same length: compare the payloads *)
  UNDISCH_TAC `v = wl_Word (w:A word)` THEN DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(MATCH_MP memory_rel_ByteArray_words_IMP (end_itlist CONJ
    [ASSUME `memory_rel c be ts refs sp st (m:A word -> A word_loc) dm
               (CONS (data_RefPtr bl i,wl_Word w) vars)`;
     ASSUME `lookup i (refs:(data_v bvl_ref)spt) = SOME (bvl_ByteArray T other)`;
     ASSUME `good_dimindex(:A)`; ASSUME `get_real_addr c st (w:A word) = SOME a`])) THEN
  DISCH_THEN(X_CHOOSE_THEN `hy:A word`
    (X_CHOOSE_THEN `frame:((A word#A word_loc)->bool)->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `byte_len (:A) (strlen s) = val (decode_length c (hy:A word))` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[MATCH_MP MP6AUX_BYTE_LEN (ASSUME `good_dimindex(:A)`)]; ALL_TAC] THEN
  MP_TAC(SPECL [`REPLICATE (val (decode_length c (hy:A word))) (word 0:A word)`;
                `other:byte list`; `MAP (word o ORD) (explode s):byte list`]
    (MATCH_MP (SPEC `be:bool` write_bytes_inj) (ASSUME `good_dimindex(:A)`))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_explode; LENGTH_REPLICATE; LE_REFL] THEN
    MATCH_ACCEPT_TAC(MATCH_MP MP6AUX_BYTE_LEN_LE (ASSUME `good_dimindex(:A)`));
    ALL_TAC] THEN
  REWRITE_TAC[MP6AUX_BYTES_STR] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC word_mem_eq_thm THEN EXISTS_TAC `frame:((A word#A word_loc)->bool)->bool` THEN
  ASM_REWRITE_TAC[LENGTH_write_bytes]);;

(* HOL4 line 15099 *)
let word_1_and_eq_0 = prove
 (`!w:A word. (word_and (word 1) w = word 0) <=> ~bit 0 w`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0; BIT_WORD_1] THEN
  MESON_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> 0 < n`]);;

let MP6AUX_SINGLE_MUL_HI0 = prove
 (`!(x:A word) (y:A word).
     word ((val x * val y + val (word 0:A word)) DIV dimword(:A)) = word 0:A word <=>
     val x * val y < dimword(:A)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES] THEN
  SUBGOAL_THEN `~(dimword(:A) = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[dimword_def; EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `(val (x:A word) * val (y:A word)) DIV dimword(:A) < dimword(:A)`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ] THEN MATCH_MP_TAC LT_MULT2 THEN
    REWRITE_TAC[dimword_def; VAL_BOUND];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0] THEN
  ASM_SIMP_TAC[VAL_WORD; GSYM dimword_def; MOD_LT; DIV_EQ_0]);;

let MP6AUX_AND1_EQ0 = prove
 (`!(w1:A word) (w2:A word). word_and (word_or w1 w2) (word 1) = word 0 <=> ~bit 0 w1 /\ ~bit 0 w2`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_1; BIT_WORD_0] THEN
  MESON_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= d ==> 0 < d`]);;

let MP6AUX_SMALLNUM_0 = prove
 (`Smallnum (&0):A word = word 0`,
  REWRITE_TAC[data_to_word_Smallnum_def; INT_LT_REFL; INT_MUL_RZERO; NUM_OF_INT_OF_NUM]);;

let MP6AUX_SMALLNUM_NUM = prove
 (`!n. Smallnum (&n):A word = word (4 * n)`,
  REWRITE_TAC[data_to_word_Smallnum_def; INT_ARITH `~(&n:int < &0)`; INT_OF_NUM_MUL;
              NUM_OF_INT_OF_NUM]);;

let MP6AUX_DIMWORD_DIV = prove
 (`good_dimindex(:A) ==>
   4 * (dimword(:A) DIV 4) = dimword(:A) /\ 2 * (dimword(:A) DIV 2) = dimword(:A) /\
   8 <= dimword(:A) DIV 2`,
  REWRITE_TAC[good_dimindex_def; dimword_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let MP6AUX_VAL_SMALLNUM_GE = prove
 (`!i. good_dimindex(:A) /\ small_int (:A) i /\ ~(i = &0) ==>
       4 <= val (Smallnum i:A word) /\
       (i < &0 ==> dimword(:A) DIV 2 <= val (Smallnum i:A word))`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP6AUX_DIMWORD_DIV) THEN
  DISJ_CASES_TAC(SPEC `i:int` INT_IMAGE) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_NEG_EQ_0; INT_OF_NUM_EQ]) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
    fst(dest_const t) = "small_int")) (concl th))) THEN
  REWRITE_TAC[small_int_def; INT_LE_NEG2; INT_OF_NUM_LE; INT_OF_NUM_LT;
              INT_ARITH `~(&n:int < &0)`] THEN STRIP_TAC THENL
   [REWRITE_TAC[MP6AUX_SMALLNUM_NUM] THEN
    SUBGOAL_THEN `val (word (4 * n):A word) = 4 * n` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[GSYM dimword_def] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    REWRITE_TAC[data_to_word_Smallnum_def; INT_ARITH `-- &n:int < &0 <=> ~(&n:int = &0)`;
                INT_OF_NUM_EQ] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&4 * (&0 - -- &n):int = &(4 * n)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NUM_OF_INT_OF_NUM; WORD_SUB_LZERO; VAL_WORD_NEG_CASES] THEN
    SUBGOAL_THEN `val (word (4 * n):A word) = 4 * n` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[GSYM dimword_def] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM dimword_def] THEN ASM_ARITH_TAC]);;

let MP6AUX_SMALL_MUL_NONNEG = prove
 (`!i1 i2. good_dimindex(:A) /\ small_int (:A) i1 /\ small_int (:A) i2 /\
           ~(i1 = &0) /\ ~(i2 = &0) /\
           val (Smallnum i1:A word) * val (word_ushr (Smallnum i2:A word) 1) < dimword(:A)
           ==> &0 <= i1 /\ &0 <= i2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP6AUX_DIMWORD_DIV) THEN
  MP_TAC(SPEC `i1:int` MP6AUX_VAL_SMALLNUM_GE) THEN
  MP_TAC(SPEC `i2:int` MP6AUX_VAL_SMALLNUM_GE) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_USHR; EXP_1]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT] THEN DISCH_TAC THEN
  RES_TAC THENL
   [SUBGOAL_THEN `(dimword(:A) DIV 2) * 2 <=
                  val (Smallnum i1:A word) * (val (Smallnum i2:A word) DIV 2)` MP_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    SUBGOAL_THEN `4 * (dimword(:A) DIV 4) <=
                  val (Smallnum i1:A word) * (val (Smallnum i2:A word) DIV 2)` MP_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

let MP6AUX_SMALL_INT_NUM = prove
 (`!n. small_int (:A) (&n) <=> n < dimword(:A) DIV 8`,
  REWRITE_TAC[small_int_def; INT_OF_NUM_LT; INT_ARITH `--(&a:int) <= &n`]);;

let MP6AUX_SMALL_MUL_POS = prove
 (`!n1 n2. good_dimindex(:A) /\ small_int (:A) (&n1) /\ small_int (:A) (&n2) /\
           val (Smallnum (&n1):A word) * val (word_ushr (Smallnum (&n2):A word) 1) <
           dimword(:A) ==>
           word_ushr (word_mul (Smallnum (&n1)) (word_ushr (Smallnum (&n2)) 1)) 1 =
           word_shl (word (n1 * n2)) 2:A word /\
           n1 * n2 < 2 EXP (dimindex(:A) - 3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MP6AUX_SMALL_INT_NUM; MP6AUX_SMALLNUM_NUM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!k. k < dimword(:A) ==> val (word k:A word) = k` ASSUME_TAC THENL
   [SIMP_TAC[VAL_WORD; GSYM dimword_def; MOD_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `word_ushr (word (4 * n2)) 1 = word (2 * n2):A word` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; EXP_1] THEN
    SUBGOAL_THEN `4 * n2 < dimword(:A) /\ 2 * n2 < dimword(:A)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `val (word (4 * n1):A word) = 4 * n1 /\ val (word (2 * n2):A word) = 2 * n2`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM WORD_MUL; WORD_SHL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `4 * n1 * n2 < dimword(:A) /\ 8 * n1 * n2 < dimword(:A)`
    STRIP_ASSUME_TAC THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; EXP_1] THEN ASM_SIMP_TAC[] THEN ARITH_TAC;
    UNDISCH_TAC `8 * n1 * n2 < dimword(:A)` THEN
    UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

(* HOL4 line 15105 *)
let memory_rel_Number_single_mul = prove
 (CASE_TERM
  `!c be ts refs sp st (m:A word -> A word_loc) dm i1 w1 i2 w2 vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number i1,wl_Word (w1:A word))
             (CONS (data_Number i2,wl_Word w2) vars)) /\
     good_dimindex(:A) ==>
     let (lw,hw) = single_mul w1 (word_ushr w2 1) (word 0) in
     word_or hw (word_and (word_or w1 w2) (word 1)) = word 0 ==>
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number (i1 * i2),wl_Word (word_ushr lw 1)) vars)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[single_mul_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ADD_0; WORD_OR_EQ_0; MP6AUX_SINGLE_MUL_HI0; MP6AUX_AND1_EQ0] THEN
  STRIP_TAC THEN
  (* both arguments are small numbers *)
  SUBGOAL_THEN `small_int (:A) i1 /\ small_int (:A) i2` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_any_Number_IMP o
      CONJ (ASSUME `good_dimindex(:A)`)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_any_Number_IMP o
      CONJ (ASSUME `good_dimindex(:A)`) o MATCH_MP memory_rel_tl) THEN
    REWRITE_TAC[injectivity "word_loc"; UNWIND_THM1] THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `w1 = Smallnum i1:A word /\ w2 = Smallnum i2:A word`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Number_IMP o
        (fun th -> end_itlist CONJ [ASSUME `good_dimindex(:A)`;
                                    ASSUME `small_int (:A) i1`; th]));
      FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Number_IMP o
        (fun th -> end_itlist CONJ [ASSUME `good_dimindex(:A)`;
                                    ASSUME `small_int (:A) i2`; MATCH_MP memory_rel_tl th]))] THEN
    REWRITE_TAC[injectivity "word_loc"];
    ALL_TAC] THEN
  ASM_CASES_TAC `i2:int = &0` THENL
   [(* times zero: the second argument itself *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[MP6AUX_SMALLNUM_0; WORD_USHR_0; WORD_MUL_0; INT_MUL_RZERO] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC memory_rel_rearrange) THEN
    REWRITE_TAC[MEM; MP6AUX_SMALLNUM_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `i1:int = &0` THENL
   [(* zero times: the first argument itself *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[MP6AUX_SMALLNUM_0; WORD_USHR_0; WORD_MUL_0; INT_MUL_LZERO] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC memory_rel_rearrange) THEN
    REWRITE_TAC[MEM; MP6AUX_SMALLNUM_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* no overflow: both are non-negative *)
  MP_TAC(ISPECL [`i1:int`; `i2:int`] MP6AUX_SMALL_MUL_NONNEG) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?n1 n2. (i1:int) = &n1 /\ (i2:int) = &n2`
    (X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `n2:num` (CONJUNCTS_THEN SUBST_ALL_TAC))) THENL
   [MAP_EVERY EXISTS_TAC [`num_of_int i1`; `num_of_int i2`] THEN
    ASM_SIMP_TAC[INT_OF_NUM_OF_INT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n1:num`; `n2:num`] MP6AUX_SMALL_MUL_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[INT_OF_NUM_MUL] THEN
  MATCH_MP_TAC IMP_memory_rel_Number_num3 THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> ACCEPT_TAC(MATCH_MP memory_rel_tl (MATCH_MP memory_rel_tl th))));;

let MP6AUX_ROR2_VAL = prove
 (`good_dimindex(:A) ==>
   !w:A word. val (word_ror w 2) = (dimword(:A) DIV 4) * (val w MOD 4) + val w DIV 4`,
  DISCH_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN `2 <= dimindex(:A) /\ 2 EXP (dimindex(:A) - 2) = dimword(:A) DIV 4`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD_ROR] THEN CONV_TAC NUM_REDUCE_CONV);;

let MP6AUX_VAL_SMALLNUM_NEG = prove
 (`!k. good_dimindex(:A) /\ ~(k = 0) /\ k <= dimword(:A) DIV 8 ==>
       val (Smallnum (-- &k):A word) = dimword(:A) - 4 * k`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP6AUX_DIMWORD_DIV) THEN
  REWRITE_TAC[data_to_word_Smallnum_def; INT_ARITH `-- &n:int < &0 <=> ~(&n:int = &0)`;
              INT_OF_NUM_EQ] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&4 * (&0 - -- &k):int = &(4 * k)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM; WORD_SUB_LZERO; VAL_WORD_NEG_CASES] THEN
  SUBGOAL_THEN `val (word (4 * k):A word) = 4 * k` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[GSYM dimword_def] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM dimword_def] THEN ASM_ARITH_TAC);;

let MP6AUX_ODD_MOD4 = prove
 (`!v. ODD v ==> 1 <= v MOD 4`,
  GEN_TAC THEN REWRITE_TAC[ODD_MOD] THEN
  MP_TAC(SPECL [`v:num`; `2`; `2`] MOD_MOD) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_CASES_TAC `v MOD 4 = 0` THEN ASM_REWRITE_TAC[MOD_0] THEN ARITH_TAC);;

(* HOL4 line 15213 *)
let memory_rel_bounds_check = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm i1 w1 vars n.
     memory_rel c be ts refs sp st m dm (CONS (data_Number i1,wl_Word (w1:A word)) vars) /\
     small_int (:A) (&n) /\ good_dimindex (:A) ==>
     (word_ult (word_ror w1 2) (word n) <=> &0 <= i1 /\ i1 < &n) /\
     (word_ule (word_ror w1 2) (word n) <=> &0 <= i1 /\ i1 <= &n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP6AUX_DIMWORD_DIV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP6AUX_SMALL_INT_NUM]) THEN
  SUBGOAL_THEN `val (word n:A word) = n` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[GSYM dimword_def] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[WORD_ULT; WORD_ULE;
                  MATCH_MP MP6AUX_ROR2_VAL (ASSUME `good_dimindex(:A)`)] THEN
  ASM_CASES_TAC `small_int (:A) i1` THENL
   [(* a small number: the tagged value shifted back *)
    SUBGOAL_THEN `w1 = Smallnum i1:A word` SUBST_ALL_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Number_IMP o
        (fun th -> end_itlist CONJ [ASSUME `good_dimindex(:A)`;
                                    ASSUME `small_int (:A) i1`; th])) THEN
      REWRITE_TAC[injectivity "word_loc"];
      ALL_TAC] THEN
    ASM_CASES_TAC `&0 <= (i1:int)` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o
        REWRITE_RULE[GSYM INT_OF_NUM_EXISTS]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MP6AUX_SMALL_INT_NUM]) THEN
      REWRITE_TAC[MP6AUX_SMALLNUM_NUM] THEN
      SUBGOAL_THEN `val (word (4 * k):A word) = 4 * k` SUBST1_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[GSYM dimword_def] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[MOD_MULT; MULT_CLAUSES; ADD_CLAUSES] THEN SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
      REWRITE_TAC[INT_POS; INT_OF_NUM_LT; INT_OF_NUM_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `?k. i1 = --(&k:int) /\ ~(k = 0)`
      (X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THENL
     [EXISTS_TAC `num_of_int (--i1)` THEN
      SUBGOAL_THEN `&(num_of_int (--i1)) = --(i1:int)` ASSUME_TAC THENL
       [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[INT_NEG_NEG] THEN DISCH_TAC THEN
      UNDISCH_TAC `&(num_of_int (--i1)) = --(i1:int)` THEN ASM_REWRITE_TAC[] THEN
      ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `k <= dimword(:A) DIV 8` ASSUME_TAC THENL
     [UNDISCH_TAC `small_int (:A) (-- &k)` THEN
      REWRITE_TAC[small_int_def; INT_LE_NEG2; INT_OF_NUM_LE] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPEC `k:num` MP6AUX_VAL_SMALLNUM_NEG) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `dimword(:A) - 4 * k = 4 * (dimword(:A) DIV 4 - k)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MOD_MULT; MULT_CLAUSES; ADD_CLAUSES] THEN SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
    ASM_SIMP_TAC[INT_ARITH `~(&k:int = &0) ==> ~(&0 <= --(&k:int))`; INT_OF_NUM_EQ;
                 ARITH_RULE `n < d DIV 8 /\ k <= d DIV 8 ==>
                             ~(d DIV 4 - k < n) /\ ~(d DIV 4 - k <= n)`];
    ALL_TAC] THEN
  (* a bignum pointer: bit 0 set, rotated to the top *)
  SUBGOAL_THEN `bit 0 (w1:A word)` MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_any_Number_IMP o
      CONJ (ASSUME `good_dimindex(:A)`)) THEN
    REWRITE_TAC[injectivity "word_loc"; UNWIND_THM1] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[BIT_VAL; EXP; DIV_1] THEN DISCH_THEN(ASSUME_TAC o MATCH_MP MP6AUX_ODD_MOD4) THEN
  SUBGOAL_THEN `dimword(:A) DIV 4 <= dimword(:A) DIV 4 * (val (w1:A word) MOD 4)`
    ASSUME_TAC THENL
   [MP_TAC(SPECL [`dimword(:A) DIV 4`; `1`; `val (w1:A word) MOD 4`] LE_MULT_LCANCEL) THEN
    REWRITE_TAC[MULT_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&0 <= (i1:int) /\ i1 <= &n)` ASSUME_TAC THENL
   [UNDISCH_TAC `~small_int (:A) i1` THEN REWRITE_TAC[small_int_def] THEN
    UNDISCH_TAC `n < dimword(:A) DIV 8` THEN REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
    MP_TAC(SPEC `dimword(:A) DIV 8` INT_POS) THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&0 <= (i1:int) /\ i1 < &n)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[INT_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* HOL4 line 15279 *)
let memory_rel_ByteArray_IMP_store = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl p w vars fl vals a i b.
     memory_rel c be ts refs sp st m dm
       (CONS (data_RefPtr bl p,wl_Word (w:A word)) vars) /\
     lookup p refs = SOME (bvl_ByteArray fl vals) /\ good_dimindex (:A) /\
     get_real_addr c st w = SOME a /\ i < LENGTH vals ==>
     ?m1. mem_store_byte_aux m dm be (word_add (word_add a bytes_in_word) (word i)) b =
            SOME m1 /\
          memory_rel c be ts (insert p (bvl_ByteArray fl (LUPDATE b i vals)) refs)
            sp st m1 dm (CONS (data_RefPtr bl p,wl_Word (w:A word)) vars)`,
  REPEAT STRIP_TAC THEN DRULE_ALL memory_rel_ByteArray_IMP THEN
  REWRITE_TAC[injectivity "word_loc"] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `a':A word = a` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `get_real_addr c st w' = SOME (a':A word)` THEN
    ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `b:byte`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  ASM_REWRITE_TAC[mem_load_byte_aux_def; mem_store_byte_aux_def; LET_DEF; LET_END_DEF] THEN
  CASES_ON `(m:A word->A word_loc)
              (byte_align (word_add (word_add a bytes_in_word) (word i)))` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT; theWord_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

(* the termination condition of word_copy_fwd and word_copy_bwd *)
let SKELAUX_VAL_WORD_SUB_4_LT = prove
 (`!n:A word.
     ~(dimword (:A) <= 4) /\ ~(word_ult n (word 4)) ==>
     val (word_sub n (word 4)) < val n`,
  GEN_TAC THEN REWRITE_TAC[WORD_ULT; NOT_LT; dimword_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word 4:A word) = 4` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES] THEN ASM_REWRITE_TAC[] THEN
  TRY COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 15295 *)
let word_copy_fwd_def = cake_def_wf
  `measure (\p:bool#A word#A word#A word#(A word->A word_loc)#(A word->bool).
              val (FST (SND p)))`
  (REWRITE_TAC[measure_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SKELAUX_VAL_WORD_SUB_4_LT THEN ASM_REWRITE_TAC[])
  `word_copy_fwd be (n:A word) a b (m:A word -> A word_loc) dm =
     if dimword (:A) <= 4 then NONE else
     if word_ult n (word 4) then
       if word_ult n (word 2) then
         if n = word 0 then SOME m else
           OPTION_BIND (mem_load_byte_aux m dm be a)
                       (\w. mem_store_byte_aux m dm be b w)
       else
         OPTION_BIND (mem_load_byte_aux m dm be a) (\w1.
         OPTION_BIND (mem_load_byte_aux m dm be (word_add a (word 1))) (\w2.
           if n = word 2 then
             OPTION_BIND (mem_store_byte_aux m dm be b w1) (\m.
             OPTION_BIND (mem_store_byte_aux m dm be (word_add b (word 1)) w2)
               (\m. SOME m))
           else
             OPTION_BIND (mem_load_byte_aux m dm be (word_add a (word 2))) (\w3.
             OPTION_BIND (mem_store_byte_aux m dm be b w1) (\m.
             OPTION_BIND (mem_store_byte_aux m dm be (word_add b (word 1)) w2) (\m.
             OPTION_BIND (mem_store_byte_aux m dm be (word_add b (word 2)) w3)
               (\m. SOME m))))))
     else
       OPTION_BIND (mem_load_byte_aux m dm be a) (\w1.
       OPTION_BIND (mem_load_byte_aux m dm be (word_add a (word 1))) (\w2.
       OPTION_BIND (mem_load_byte_aux m dm be (word_add a (word 2))) (\w3.
       OPTION_BIND (mem_load_byte_aux m dm be (word_add a (word 3))) (\w4.
       OPTION_BIND (mem_store_byte_aux m dm be b w1) (\m.
       OPTION_BIND (mem_store_byte_aux m dm be (word_add b (word 1)) w2) (\m.
       OPTION_BIND (mem_store_byte_aux m dm be (word_add b (word 2)) w3) (\m.
       OPTION_BIND (mem_store_byte_aux m dm be (word_add b (word 3)) w4) (\m.
         word_copy_fwd be (word_sub n (word 4)) (word_add a (word 4))
           (word_add b (word 4)) m dm))))))))`;;
let word_copy_fwd_ind = cake_ind "word_copy_fwd";;

(* HOL4 line 15331 *)
let list_copy_fwd_def = cake_def_wf
  `measure (\p:num#num#A list#num#A list. FST p)` TERM_TAC
  `list_copy_fwd n xp (xs:A list) yp ys =
     if xp + n <= LENGTH xs /\ yp + n <= LENGTH ys then
       if n = 0 then SOME ys else
       if n = 1 then SOME (LUPDATE (EL xp xs) yp ys) else
       if n = 2 then SOME ((LUPDATE (EL (xp + 1) xs) (yp + 1) o
                            LUPDATE (EL (xp + 0) xs) (yp + 0)) ys) else
       if n = 3 then SOME ((LUPDATE (EL (xp + 2) xs) (yp + 2) o
                            LUPDATE (EL (xp + 1) xs) (yp + 1) o
                            LUPDATE (EL (xp + 0) xs) (yp + 0)) ys) else
         list_copy_fwd (n - 4) (xp + 4) xs (yp + 4)
                          ((LUPDATE (EL (xp + 3) xs) (yp + 3) o
                            LUPDATE (EL (xp + 2) xs) (yp + 2) o
                            LUPDATE (EL (xp + 1) xs) (yp + 1) o
                            LUPDATE (EL (xp + 0) xs) (yp + 0)) ys)
     else NONE`;;
let list_copy_fwd_ind = cake_ind "list_copy_fwd";;

(* HOL4 line 15349 *)
let list_copy_fwd_alias_def = cake_def_wf
  `measure (\p:num#num#num#A list. FST p)` TERM_TAC
  `list_copy_fwd_alias n xp yp (ys:A list) =
     if xp + n <= LENGTH ys /\ yp + n <= LENGTH ys then
       if n = 0 then SOME ys else
       if n = 1 then SOME (LUPDATE (EL xp ys) yp ys) else
       if n = 2 then SOME ((LUPDATE (EL (xp + 1) ys) (yp + 1) o
                            LUPDATE (EL (xp + 0) ys) (yp + 0)) ys) else
       if n = 3 then SOME ((LUPDATE (EL (xp + 2) ys) (yp + 2) o
                            LUPDATE (EL (xp + 1) ys) (yp + 1) o
                            LUPDATE (EL (xp + 0) ys) (yp + 0)) ys) else
         list_copy_fwd_alias (n - 4) (xp + 4) (yp + 4)
                          ((LUPDATE (EL (xp + 3) ys) (yp + 3) o
                            LUPDATE (EL (xp + 2) ys) (yp + 2) o
                            LUPDATE (EL (xp + 1) ys) (yp + 1) o
                            LUPDATE (EL (xp + 0) ys) (yp + 0)) ys)
     else NONE`;;
let list_copy_fwd_alias_ind = cake_ind "list_copy_fwd_alias";;

(* small words: comparisons and equations as on the numbers *)
let MP6AUX_DIMWORD_GE_256 = prove
 (`good_dimindex(:A) ==> 256 <= dimword(:A)`,
  REWRITE_TAC[good_dimindex_def; dimword_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let MP6AUX_WORD_ULT_SMALL = prove
 (`!n k. n < dimword(:A) /\ k < dimword(:A) ==>
         (word_ult (word n:A word) (word k) <=> n < k)`,
  SIMP_TAC[WORD_ULT; VAL_WORD; GSYM dimword_def; MOD_LT]);;

let MP6AUX_WORD_ADD_ADD = prove
 (`!(a:A word) x k. word_add (word_add a (word x)) (word k) = word_add a (word (x + k))`,
  REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;

(* a store into the second of two byte arrays (HOL4 does this step inline) *)
let MP6AUX_STORE_SECOND = prove
 (`!c be ts p2 fl_ys ys refs sp st (m:A word -> A word_loc) dm bl1 p1 v1 bl2 w2 vars
    a2 k b.
     memory_rel c be ts (insert p2 (bvl_ByteArray fl_ys ys) refs) sp st m dm
       (CONS (data_RefPtr bl1 p1,v1) (CONS (data_RefPtr bl2 p2,wl_Word w2) vars)) /\
     good_dimindex(:A) /\ get_real_addr c st w2 = SOME a2 /\ k < LENGTH ys ==>
     ?m1. mem_store_byte_aux m dm be (word_add (word_add a2 bytes_in_word) (word k)) b =
            SOME m1 /\
          memory_rel c be ts (insert p2 (bvl_ByteArray fl_ys (LUPDATE b k ys)) refs)
            sp st m1 dm
            (CONS (data_RefPtr bl1 p1,v1) (CONS (data_RefPtr bl2 p2,wl_Word w2) vars))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_swap) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `insert p2 (bvl_ByteArray fl_ys ys) (refs:(data_v bvl_ref)spt)`; `sp:num`;
    `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`; `dm:A word->bool`;
    `bl2:bool`; `p2:num`; `w2:A word`;
    `CONS (data_RefPtr bl1 p1,v1:A word_loc) vars`; `fl_ys:bool`; `ys:byte list`;
    `a2:A word`; `k:num`; `b:byte`] memory_rel_ByteArray_IMP_store) THEN
  ASM_REWRITE_TAC[lookup_insert; insert_shadow] THEN
  STRIP_TAC THEN EXISTS_TAC `m1:A word -> A word_loc` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_swap) THEN REWRITE_TAC[]);;

let MP6AUX_STORE_SECOND' = prove
 (`!c be ts p2 fl_ys ys refs sp st (m:A word -> A word_loc) dm bl1 p1 v1 bl2 w2 vars.
     memory_rel c be ts (insert p2 (bvl_ByteArray fl_ys ys) refs) sp st m dm
       (CONS (data_RefPtr bl1 p1,v1) (CONS (data_RefPtr bl2 p2,wl_Word w2) vars)) ==>
     good_dimindex(:A) ==>
     !a2. get_real_addr c st w2 = SOME a2 ==>
     !k b. k < LENGTH ys ==>
     ?m1. mem_store_byte_aux m dm be (word_add (word_add a2 bytes_in_word) (word k)) b =
            SOME m1 /\
          memory_rel c be ts (insert p2 (bvl_ByteArray fl_ys (LUPDATE b k ys)) refs)
            sp st m1 dm
            (CONS (data_RefPtr bl1 p1,v1) (CONS (data_RefPtr bl2 p2,wl_Word w2) vars))`,
  MESON_TAC[MP6AUX_STORE_SECOND]);;

(* one store into the second array: the memory_rel assumption is replaced *)
let MP6AUX_STORE_TAC a2 k b =
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MP6AUX_STORE_SECOND') THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC a2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [k; b]) THEN
  ANTS_TAC THENL [REWRITE_TAC[LENGTH_LUPDATE] THEN MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
  (fun (asl,w as g) ->
     let avoid = itlist (union o frees o concl o snd) asl (frees w) in
     let mm = variant avoid `mm:A word->A word_loc` in
     DISCH_THEN(X_CHOOSE_THEN mm STRIP_ASSUME_TAC) g) THEN
  ASM_REWRITE_TAC[OPTION_BIND_DEF];;

(* HOL4 line 15367 *)
let word_copy_fwd_thm = prove
 (`!c be ts p2 fl_ys refs sp st dm bl1 p1 v1 bl2 v2 vars fl_xs xs.
   !n xp yp ys ys1 (m:A word -> A word_loc).
     memory_rel c be ts (insert p2 (bvl_ByteArray fl_ys ys) refs)
       sp st m dm (CONS (data_RefPtr bl1 p1,v1) (CONS (data_RefPtr bl2 p2,v2) vars)) /\
     lookup p1 refs = SOME (bvl_ByteArray fl_xs xs) /\
     list_copy_fwd n xp xs yp ys = SOME ys1 /\
     good_dimindex (:A) /\ n < dimword (:A) /\ ~(p1 = p2) ==>
     ?w1 (w2:A word) a1 a2 m1.
       v1 = wl_Word w1 /\ v2 = wl_Word w2 /\
       get_real_addr c st w1 = SOME a1 /\
       get_real_addr c st w2 = SOME a2 /\
       word_copy_fwd be (word n) (word_add (word_add a1 bytes_in_word) (word xp))
         (word_add (word_add a2 bytes_in_word) (word yp)) m dm = SOME m1 /\
       memory_rel c be ts (insert p2 (bvl_ByteArray fl_ys ys1) refs)
         sp st m1 dm (CONS (data_RefPtr bl1 p1,v1) (CONS (data_RefPtr bl2 p2,v2) vars))`,
  REPLICATE_TAC 17 GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP6AUX_DIMWORD_GE_256) THEN
  SUBGOAL_THEN `lookup p1 (insert p2 (bvl_ByteArray fl_ys (ys:byte list))
                  (refs:(data_v bvl_ref)spt)) = SOME (bvl_ByteArray fl_xs (xs:byte list))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[lookup_insert]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `insert p2 (bvl_ByteArray fl_ys ys) (refs:(data_v bvl_ref)spt)`; `sp:num`;
    `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`; `dm:A word->bool`;
    `bl1:bool`; `p1:num`; `v1:A word_loc`;
    `CONS (data_RefPtr bl2 p2,v2:A word_loc) vars`; `fl_xs:bool`; `xs:byte list`]
    memory_rel_ByteArray_IMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word` (X_CHOOSE_THEN `a1:A word`
    (X_CHOOSE_THEN `x1:A word` (fun th -> let l = CONJUNCTS th in
       MAP_EVERY (fun i -> ASSUME_TAC (el i l)) [0;7;10])))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_swap) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `insert p2 (bvl_ByteArray fl_ys ys) (refs:(data_v bvl_ref)spt)`; `sp:num`;
    `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`; `dm:A word->bool`;
    `bl2:bool`; `p2:num`; `v2:A word_loc`;
    `CONS (data_RefPtr bl1 p1,v1:A word_loc) vars`; `fl_ys:bool`; `ys:byte list`]
    memory_rel_ByteArray_IMP) THEN
  ASM_REWRITE_TAC[lookup_insert] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:A word` (X_CHOOSE_THEN `a2:A word`
    (X_CHOOSE_THEN `x2:A word` (fun th -> let l = CONJUNCTS th in
       MAP_EVERY (fun i -> ASSUME_TAC (el i l)) [0;7])))) THEN
  FIRST_X_ASSUM(K ALL_TAC o MATCH_MP memory_rel_swap) THEN
  RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`w1:A word`; `w2:A word`; `a1:A word`; `a2:A word`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `xp + n <= LENGTH (xs:byte list) /\ yp + n <= LENGTH (ys:byte list) /\
                4 < dimword(:A) /\ 2 < dimword(:A) /\ 1 < dimword(:A) /\
                0 < dimword(:A)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `list_copy_fwd n xp xs yp ys = SOME (ys1:byte list)` THEN
    ONCE_REWRITE_TAC[list_copy_fwd_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
    MP6AUX_ASM_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `list_copy_fwd n xp xs yp ys = SOME (ys1:byte list)` THEN
  ONCE_REWRITE_TAC[list_copy_fwd_def] THEN ONCE_REWRITE_TAC[word_copy_fwd_def] THEN
  ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  SIMP_TAC[ASSUME `n < dimword(:A)`; ASSUME `4 < dimword(:A)`; ASSUME `2 < dimword(:A)`;
           ASSUME `0 < dimword(:A)`; MP6AUX_WORD_ULT_SMALL; MP6AUX_WORD_EQ_SMALL] THEN
  ASM_CASES_TAC `n = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXISTS_TAC `m:A word->A word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `xp < LENGTH (xs:byte list)` ASSUME_TAC THENL
     [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[OPTION_BIND_DEF] THEN
    MP6AUX_STORE_TAC `a2:A word` `yp:num` `EL xp (xs:byte list)` THEN
    EXISTS_TAC `mm:A word->A word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[option_INJ; o_THM; ADD_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `xp < LENGTH (xs:byte list) /\ xp + 1 < LENGTH xs` STRIP_ASSUME_TAC THENL
     [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[OPTION_BIND_DEF; MP6AUX_WORD_ADD_ADD] THEN
    MP6AUX_STORE_TAC `a2:A word` `yp:num` `EL xp (xs:byte list)` THEN
    MP6AUX_STORE_TAC `a2:A word` `yp + 1` `EL (xp + 1) (xs:byte list)` THEN
    EXISTS_TAC `mm':A word->A word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 3` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[option_INJ; o_THM; ADD_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `xp < LENGTH (xs:byte list) /\ xp + 1 < LENGTH xs /\ xp + 2 < LENGTH xs`
      STRIP_ASSUME_TAC THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[OPTION_BIND_DEF; MP6AUX_WORD_ADD_ADD] THEN
    MP6AUX_STORE_TAC `a2:A word` `yp:num` `EL xp (xs:byte list)` THEN
    MP6AUX_STORE_TAC `a2:A word` `yp + 1` `EL (xp + 1) (xs:byte list)` THEN
    MP6AUX_STORE_TAC `a2:A word` `yp + 2` `EL (xp + 2) (xs:byte list)` THEN
    EXISTS_TAC `mm'':A word->A word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `xp < LENGTH (xs:byte list) /\ xp + 1 < LENGTH xs /\ xp + 2 < LENGTH xs /\
                xp + 3 < LENGTH xs /\ 4 <= n /\ n - 4 < n /\ n - 4 < dimword(:A)`
    STRIP_ASSUME_TAC THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[OPTION_BIND_DEF; MP6AUX_WORD_ADD_ADD; ADD_CLAUSES] THEN
  MP6AUX_STORE_TAC `a2:A word` `yp:num` `EL xp (xs:byte list)` THEN
  MP6AUX_STORE_TAC `a2:A word` `yp + 1` `EL (xp + 1) (xs:byte list)` THEN
  MP6AUX_STORE_TAC `a2:A word` `yp + 2` `EL (xp + 2) (xs:byte list)` THEN
  MP6AUX_STORE_TAC `a2:A word` `yp + 3` `EL (xp + 3) (xs:byte list)` THEN
  ASM_REWRITE_TAC[GSYM NOT_LE] THEN
  SUBGOAL_THEN `word_sub (word n) (word 4):A word = word (n - 4)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[WORD_SUB]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_THM; ADD_CLAUSES]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 4` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "list_copy_fwd"))
      (concl th) && is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`xp + 4`; `yp + 4`;
    `LUPDATE (EL (xp + 3) xs) (yp + 3) (LUPDATE (EL (xp + 2) xs) (yp + 2)
      (LUPDATE (EL (xp + 1) xs) (yp + 1) (LUPDATE (EL xp xs) yp (ys:byte list))))`;
    `ys1:byte list`; `mm''':A word->A word_loc`]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "word_loc"] THEN
  CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN ASM_REWRITE_TAC[option_INJ] THEN
  CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[]);;

(* a store into a byte array (the single-array version of the above) *)
let MP6AUX_STORE_ONE = prove
 (`!c be ts p2 fl_ys ys refs sp st (m:A word -> A word_loc) dm bl w2 vars.
     memory_rel c be ts (insert p2 (bvl_ByteArray fl_ys ys) refs) sp st m dm
       (CONS (data_RefPtr bl p2,wl_Word w2) vars) ==>
     good_dimindex(:A) ==>
     !a2. get_real_addr c st w2 = SOME a2 ==>
     !k b. k < LENGTH ys ==>
     ?m1. mem_store_byte_aux m dm be (word_add (word_add a2 bytes_in_word) (word k)) b =
            SOME m1 /\
          memory_rel c be ts (insert p2 (bvl_ByteArray fl_ys (LUPDATE b k ys)) refs)
            sp st m1 dm (CONS (data_RefPtr bl p2,wl_Word w2) vars)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `insert p2 (bvl_ByteArray fl_ys ys) (refs:(data_v bvl_ref)spt)`; `sp:num`;
    `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`; `dm:A word->bool`;
    `bl:bool`; `p2:num`; `w2:A word`; `vars:(data_v#A word_loc)list`;
    `fl_ys:bool`; `ys:byte list`; `a2:A word`; `k:num`; `b:byte`]
    memory_rel_ByteArray_IMP_store) THEN
  ASM_REWRITE_TAC[lookup_insert; insert_shadow]);;

let MP6AUX_STORE_ONE_TAC a2 k b =
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MP6AUX_STORE_ONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC a2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [k; b]) THEN
  ANTS_TAC THENL [REWRITE_TAC[LENGTH_LUPDATE] THEN MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
  (fun (asl,w as g) ->
     let avoid = itlist (union o frees o concl o snd) asl (frees w) in
     let mm = variant avoid `mm:A word->A word_loc` in
     DISCH_THEN(X_CHOOSE_THEN mm STRIP_ASSUME_TAC) g) THEN
  ASM_REWRITE_TAC[OPTION_BIND_DEF];;

(* HOL4 line 15460 *)
let word_copy_fwd_alias_thm = prove
 (`!c be ts p2 fl_ys refs sp st dm bl v2 vars.
   !n xp yp ys ys1 (m:A word -> A word_loc).
     memory_rel c be ts (insert p2 (bvl_ByteArray fl_ys ys) refs)
       sp st m dm (CONS (data_RefPtr bl p2,v2) vars) /\
     list_copy_fwd_alias n xp yp ys = SOME ys1 /\
     good_dimindex (:A) /\ n < dimword (:A) ==>
     ?(w2:A word) a2 m1.
       v2 = wl_Word w2 /\
       get_real_addr c st w2 = SOME a2 /\
       word_copy_fwd be (word n) (word_add (word_add a2 bytes_in_word) (word xp))
         (word_add (word_add a2 bytes_in_word) (word yp)) m dm = SOME m1 /\
       memory_rel c be ts (insert p2 (bvl_ByteArray fl_ys ys1) refs)
         sp st m1 dm (CONS (data_RefPtr bl p2,v2) vars)`,
  REPLICATE_TAC 12 GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP6AUX_DIMWORD_GE_256) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `insert p2 (bvl_ByteArray fl_ys ys) (refs:(data_v bvl_ref)spt)`; `sp:num`;
    `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`; `dm:A word->bool`;
    `bl:bool`; `p2:num`; `v2:A word_loc`; `vars:(data_v#A word_loc)list`;
    `fl_ys:bool`; `ys:byte list`] memory_rel_ByteArray_IMP) THEN
  ASM_REWRITE_TAC[lookup_insert] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:A word` (X_CHOOSE_THEN `a2:A word`
    (X_CHOOSE_THEN `x2:A word` (fun th -> let l = CONJUNCTS th in
       MAP_EVERY (fun i -> ASSUME_TAC (el i l)) [0;7;10])))) THEN
  RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`w2:A word`; `a2:A word`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `xp + n <= LENGTH (ys:byte list) /\ yp + n <= LENGTH (ys:byte list) /\
                4 < dimword(:A) /\ 2 < dimword(:A) /\ 1 < dimword(:A) /\
                0 < dimword(:A)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `list_copy_fwd_alias n xp yp ys = SOME (ys1:byte list)` THEN
    ONCE_REWRITE_TAC[list_copy_fwd_alias_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
    MP6AUX_ASM_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `list_copy_fwd_alias n xp yp ys = SOME (ys1:byte list)` THEN
  ONCE_REWRITE_TAC[list_copy_fwd_alias_def] THEN ONCE_REWRITE_TAC[word_copy_fwd_def] THEN
  ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  SIMP_TAC[ASSUME `n < dimword(:A)`; ASSUME `4 < dimword(:A)`; ASSUME `2 < dimword(:A)`;
           ASSUME `0 < dimword(:A)`; MP6AUX_WORD_ULT_SMALL; MP6AUX_WORD_EQ_SMALL] THEN
  ASM_CASES_TAC `n = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXISTS_TAC `m:A word->A word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `xp < LENGTH (ys:byte list)` ASSUME_TAC THENL
     [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[OPTION_BIND_DEF] THEN
    MP6AUX_STORE_ONE_TAC `a2:A word` `yp:num` `EL xp (ys:byte list)` THEN
    EXISTS_TAC `mm:A word->A word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[option_INJ; o_THM; ADD_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `xp < LENGTH (ys:byte list) /\ xp + 1 < LENGTH ys` STRIP_ASSUME_TAC THENL
     [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[OPTION_BIND_DEF; MP6AUX_WORD_ADD_ADD] THEN
    MP6AUX_STORE_ONE_TAC `a2:A word` `yp:num` `EL xp (ys:byte list)` THEN
    MP6AUX_STORE_ONE_TAC `a2:A word` `yp + 1` `EL (xp + 1) (ys:byte list)` THEN
    EXISTS_TAC `mm':A word->A word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 3` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[option_INJ; o_THM; ADD_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `xp < LENGTH (ys:byte list) /\ xp + 1 < LENGTH ys /\ xp + 2 < LENGTH ys`
      STRIP_ASSUME_TAC THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[OPTION_BIND_DEF; MP6AUX_WORD_ADD_ADD] THEN
    MP6AUX_STORE_ONE_TAC `a2:A word` `yp:num` `EL xp (ys:byte list)` THEN
    MP6AUX_STORE_ONE_TAC `a2:A word` `yp + 1` `EL (xp + 1) (ys:byte list)` THEN
    MP6AUX_STORE_ONE_TAC `a2:A word` `yp + 2` `EL (xp + 2) (ys:byte list)` THEN
    EXISTS_TAC `mm'':A word->A word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `xp < LENGTH (ys:byte list) /\ xp + 1 < LENGTH ys /\ xp + 2 < LENGTH ys /\
                xp + 3 < LENGTH ys /\ 4 <= n /\ n - 4 < n /\ n - 4 < dimword(:A)`
    STRIP_ASSUME_TAC THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[OPTION_BIND_DEF; MP6AUX_WORD_ADD_ADD; ADD_CLAUSES] THEN
  MP6AUX_STORE_ONE_TAC `a2:A word` `yp:num` `EL xp (ys:byte list)` THEN
  MP6AUX_STORE_ONE_TAC `a2:A word` `yp + 1` `EL (xp + 1) (ys:byte list)` THEN
  MP6AUX_STORE_ONE_TAC `a2:A word` `yp + 2` `EL (xp + 2) (ys:byte list)` THEN
  MP6AUX_STORE_ONE_TAC `a2:A word` `yp + 3` `EL (xp + 3) (ys:byte list)` THEN
  ASM_REWRITE_TAC[GSYM NOT_LE] THEN
  SUBGOAL_THEN `word_sub (word n) (word 4):A word = word (n - 4)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[WORD_SUB]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_THM; ADD_CLAUSES]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 4` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "list_copy_fwd_alias"))
      (concl th) && is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`xp + 4`; `yp + 4`;
    `LUPDATE (EL (xp + 3) ys) (yp + 3) (LUPDATE (EL (xp + 2) ys) (yp + 2)
      (LUPDATE (EL (xp + 1) ys) (yp + 1) (LUPDATE (EL xp ys) yp (ys:byte list))))`;
    `ys1:byte list`; `mm''':A word->A word_loc`]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "word_loc"] THEN
  CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN ASM_REWRITE_TAC[option_INJ] THEN
  CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[]);;

(* HOL4 line 15540 *)
let word_copy_bwd_def = cake_def_wf
  `measure (\p:bool#A word#A word#A word#(A word->A word_loc)#(A word->bool).
              val (FST (SND p)))`
  (REWRITE_TAC[measure_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SKELAUX_VAL_WORD_SUB_4_LT THEN ASM_REWRITE_TAC[])
  `word_copy_bwd be (n:A word) a b (m:A word -> A word_loc) dm =
     if dimword (:A) <= 4 then NONE else
     if word_ult n (word 4) then
       if word_ult n (word 2) then
         if n = word 0 then SOME m else
           OPTION_BIND (mem_load_byte_aux m dm be a)
                       (\w. mem_store_byte_aux m dm be b w)
       else
         OPTION_BIND (mem_load_byte_aux m dm be a) (\w1.
         OPTION_BIND (mem_load_byte_aux m dm be (word_sub a (word 1))) (\w2.
           if n = word 2 then
             OPTION_BIND (mem_store_byte_aux m dm be b w1) (\m.
             OPTION_BIND (mem_store_byte_aux m dm be (word_sub b (word 1)) w2)
               (\m. SOME m))
           else
             OPTION_BIND (mem_load_byte_aux m dm be (word_sub a (word 2))) (\w3.
             OPTION_BIND (mem_store_byte_aux m dm be b w1) (\m.
             OPTION_BIND (mem_store_byte_aux m dm be (word_sub b (word 1)) w2) (\m.
             OPTION_BIND (mem_store_byte_aux m dm be (word_sub b (word 2)) w3)
               (\m. SOME m))))))
     else
       OPTION_BIND (mem_load_byte_aux m dm be a) (\w1.
       OPTION_BIND (mem_load_byte_aux m dm be (word_sub a (word 1))) (\w2.
       OPTION_BIND (mem_load_byte_aux m dm be (word_sub a (word 2))) (\w3.
       OPTION_BIND (mem_load_byte_aux m dm be (word_sub a (word 3))) (\w4.
       OPTION_BIND (mem_store_byte_aux m dm be b w1) (\m.
       OPTION_BIND (mem_store_byte_aux m dm be (word_sub b (word 1)) w2) (\m.
       OPTION_BIND (mem_store_byte_aux m dm be (word_sub b (word 2)) w3) (\m.
       OPTION_BIND (mem_store_byte_aux m dm be (word_sub b (word 3)) w4) (\m.
         word_copy_bwd be (word_sub n (word 4)) (word_sub a (word 4))
           (word_sub b (word 4)) m dm))))))))`;;
let word_copy_bwd_ind = cake_ind "word_copy_bwd";;

(* HOL4 line 15576 *)
let minus_def = cake_def
  `minus m n = m - n:num`;;

(* HOL4 line 15580 *)
let list_copy_bwd_def = cake_def_wf
  `measure (\p:num#num#A list#num#A list. FST p)` TERM_TAC
  `list_copy_bwd (n:num) xp (xs:A list) yp ys =
     if n <= xp + 1 /\ xp < LENGTH xs /\ n <= yp + 1 /\ yp < LENGTH ys then
       if n = 0 then SOME ys else
       if n = 1 then SOME (LUPDATE (EL xp xs) yp ys) else
       if n = 2 then SOME ((LUPDATE (EL (minus xp 1) xs) (minus yp 1) o
                            LUPDATE (EL (minus xp 0) xs) (minus yp 0)) ys) else
       if n = 3 then SOME ((LUPDATE (EL (minus xp 2) xs) (minus yp 2) o
                            LUPDATE (EL (minus xp 1) xs) (minus yp 1) o
                            LUPDATE (EL (minus xp 0) xs) (minus yp 0)) ys) else
         list_copy_bwd (n - 4) (minus xp 4) xs (minus yp 4)
                          ((LUPDATE (EL (minus xp 3) xs) (minus yp 3) o
                            LUPDATE (EL (minus xp 2) xs) (minus yp 2) o
                            LUPDATE (EL (minus xp 1) xs) (minus yp 1) o
                            LUPDATE (EL (minus xp 0) xs) (minus yp 0)) ys)
     else NONE`;;
let list_copy_bwd_ind = cake_ind "list_copy_bwd";;

(* HOL4 line 15598 (val) *)
let list_copy_bwd_def = REWRITE_RULE [minus_def] list_copy_bwd_def;;

(* HOL4 line 15600 *)
let list_copy_bwd_alias_def = cake_def_wf
  `measure (\p:num#num#num#A list. FST p)` TERM_TAC
  `list_copy_bwd_alias n xp yp (ys:A list) =
     if n <= xp + 1 /\ xp < LENGTH ys /\ n <= yp + 1 /\ yp < LENGTH ys then
       if n = 0 then SOME ys else
       if n = 1 then SOME (LUPDATE (EL xp ys) yp ys) else
       if n = 2 then SOME ((LUPDATE (EL (minus xp 1) ys) (minus yp 1) o
                            LUPDATE (EL (minus xp 0) ys) (minus yp 0)) ys) else
       if n = 3 then SOME ((LUPDATE (EL (minus xp 2) ys) (minus yp 2) o
                            LUPDATE (EL (minus xp 1) ys) (minus yp 1) o
                            LUPDATE (EL (minus xp 0) ys) (minus yp 0)) ys) else
         list_copy_bwd_alias (n - 4) (minus xp 4) (minus yp 4)
                          ((LUPDATE (EL (minus xp 3) ys) (minus yp 3) o
                            LUPDATE (EL (minus xp 2) ys) (minus yp 2) o
                            LUPDATE (EL (minus xp 1) ys) (minus yp 1) o
                            LUPDATE (EL (minus xp 0) ys) (minus yp 0)) ys)
     else NONE`;;
let list_copy_bwd_alias_ind = cake_ind "list_copy_bwd_alias";;

(* HOL4 line 15617 (val) *)
let list_copy_bwd_alias_def = REWRITE_RULE [minus_def] list_copy_bwd_alias_def;;

let MP6AUX_WORD_COPY_BWD_0 = prove
 (`!be a1 a2 (m:A word -> A word_loc) dm.
     good_dimindex (:A) ==> word_copy_bwd be (word 0:A word) a1 a2 m dm = SOME m`,
  REWRITE_TAC[good_dimindex_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[word_copy_bwd_def] THEN
  ASM_REWRITE_TAC[WORD_ULT; VAL_WORD_0; VAL_WORD; dimword_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MP6AUX_WORD_ADD_SUB = prove
 (`!(a:A word) x k. k <= x ==>
     word_sub (word_add a (word x)) (word k) = word_add a (word (x - k))`,
  SIMP_TAC[WORD_SUB] THEN REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

(* HOL4 line 15620 *)
let word_copy_bwd_thm = prove
 (`!c be ts p2 fl_ys refs sp st dm bl1 p1 v1 bl2 v2 vars fl_xs xs.
   !n xp yp ys ys1 (m:A word -> A word_loc).
     memory_rel c be ts (insert p2 (bvl_ByteArray fl_ys ys) refs)
       sp st m dm (CONS (data_RefPtr bl1 p1,v1) (CONS (data_RefPtr bl2 p2,v2) vars)) /\
     lookup p1 refs = SOME (bvl_ByteArray fl_xs xs) /\
     list_copy_bwd n xp xs yp ys = SOME ys1 /\
     good_dimindex (:A) /\ n < dimword (:A) /\ ~(p1 = p2) ==>
     ?w1 (w2:A word) a1 a2 m1.
       v1 = wl_Word w1 /\ v2 = wl_Word w2 /\
       get_real_addr c st w1 = SOME a1 /\
       get_real_addr c st w2 = SOME a2 /\
       word_copy_bwd be (word n) (word_add (word_add a1 bytes_in_word) (word xp))
         (word_add (word_add a2 bytes_in_word) (word yp)) m dm = SOME m1 /\
       memory_rel c be ts (insert p2 (bvl_ByteArray fl_ys ys1) refs)
         sp st m1 dm (CONS (data_RefPtr bl1 p1,v1) (CONS (data_RefPtr bl2 p2,v2) vars))`,
  REPLICATE_TAC 17 GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP6AUX_DIMWORD_GE_256) THEN
  SUBGOAL_THEN `lookup p1 (insert p2 (bvl_ByteArray fl_ys (ys:byte list))
                  (refs:(data_v bvl_ref)spt)) = SOME (bvl_ByteArray fl_xs (xs:byte list))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[lookup_insert]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `insert p2 (bvl_ByteArray fl_ys ys) (refs:(data_v bvl_ref)spt)`; `sp:num`;
    `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`; `dm:A word->bool`;
    `bl1:bool`; `p1:num`; `v1:A word_loc`;
    `CONS (data_RefPtr bl2 p2,v2:A word_loc) vars`; `fl_xs:bool`; `xs:byte list`]
    memory_rel_ByteArray_IMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word` (X_CHOOSE_THEN `a1:A word`
    (X_CHOOSE_THEN `x1:A word` (fun th -> let l = CONJUNCTS th in
       MAP_EVERY (fun i -> ASSUME_TAC (el i l)) [0;7;10])))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_swap) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `insert p2 (bvl_ByteArray fl_ys ys) (refs:(data_v bvl_ref)spt)`; `sp:num`;
    `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`; `dm:A word->bool`;
    `bl2:bool`; `p2:num`; `v2:A word_loc`;
    `CONS (data_RefPtr bl1 p1,v1:A word_loc) vars`; `fl_ys:bool`; `ys:byte list`]
    memory_rel_ByteArray_IMP) THEN
  ASM_REWRITE_TAC[lookup_insert] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:A word` (X_CHOOSE_THEN `a2:A word`
    (X_CHOOSE_THEN `x2:A word` (fun th -> let l = CONJUNCTS th in
       MAP_EVERY (fun i -> ASSUME_TAC (el i l)) [0;7])))) THEN
  FIRST_X_ASSUM(K ALL_TAC o MATCH_MP memory_rel_swap) THEN
  RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`w1:A word`; `w2:A word`; `a1:A word`; `a2:A word`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n <= xp + 1 /\ xp < LENGTH (xs:byte list) /\ n <= yp + 1 /\
                yp < LENGTH (ys:byte list) /\
                4 < dimword(:A) /\ 2 < dimword(:A) /\ 1 < dimword(:A) /\
                0 < dimword(:A)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `list_copy_bwd n xp xs yp ys = SOME (ys1:byte list)` THEN
    ONCE_REWRITE_TAC[list_copy_bwd_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
    MP6AUX_ASM_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `list_copy_bwd n xp xs yp ys = SOME (ys1:byte list)` THEN
  ONCE_REWRITE_TAC[list_copy_bwd_def] THEN ONCE_REWRITE_TAC[word_copy_bwd_def] THEN
  ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  SIMP_TAC[ASSUME `n < dimword(:A)`; ASSUME `4 < dimword(:A)`; ASSUME `2 < dimword(:A)`;
           ASSUME `0 < dimword(:A)`; MP6AUX_WORD_ULT_SMALL; MP6AUX_WORD_EQ_SMALL] THEN
  ASM_CASES_TAC `n = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXISTS_TAC `m:A word->A word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[OPTION_BIND_DEF] THEN
    MP6AUX_STORE_TAC `a2:A word` `yp:num` `EL xp (xs:byte list)` THEN
    EXISTS_TAC `mm:A word->A word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[option_INJ; o_THM; SUB_0] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `xp - 1 < LENGTH (xs:byte list) /\ 1 <= xp /\ 1 <= yp`
      STRIP_ASSUME_TAC THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[OPTION_BIND_DEF; MP6AUX_WORD_ADD_SUB] THEN
    MP6AUX_STORE_TAC `a2:A word` `yp:num` `EL xp (xs:byte list)` THEN
    MP6AUX_STORE_TAC `a2:A word` `yp - 1` `EL (xp - 1) (xs:byte list)` THEN
    EXISTS_TAC `mm':A word->A word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 3` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[option_INJ; o_THM; SUB_0] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `xp - 1 < LENGTH (xs:byte list) /\ xp - 2 < LENGTH xs /\
                  1 <= xp /\ 2 <= xp /\ 1 <= yp /\ 2 <= yp`
      STRIP_ASSUME_TAC THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[OPTION_BIND_DEF; MP6AUX_WORD_ADD_SUB] THEN
    MP6AUX_STORE_TAC `a2:A word` `yp:num` `EL xp (xs:byte list)` THEN
    MP6AUX_STORE_TAC `a2:A word` `yp - 1` `EL (xp - 1) (xs:byte list)` THEN
    MP6AUX_STORE_TAC `a2:A word` `yp - 2` `EL (xp - 2) (xs:byte list)` THEN
    EXISTS_TAC `mm'':A word->A word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `xp - 1 < LENGTH (xs:byte list) /\ xp - 2 < LENGTH xs /\
                xp - 3 < LENGTH xs /\ 1 <= xp /\ 2 <= xp /\ 3 <= xp /\
                1 <= yp /\ 2 <= yp /\ 3 <= yp /\ 4 <= n /\ n - 4 < n /\
                n - 4 < dimword(:A)`
    STRIP_ASSUME_TAC THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[OPTION_BIND_DEF; MP6AUX_WORD_ADD_SUB; SUB_0] THEN
  MP6AUX_STORE_TAC `a2:A word` `yp:num` `EL xp (xs:byte list)` THEN
  MP6AUX_STORE_TAC `a2:A word` `yp - 1` `EL (xp - 1) (xs:byte list)` THEN
  MP6AUX_STORE_TAC `a2:A word` `yp - 2` `EL (xp - 2) (xs:byte list)` THEN
  MP6AUX_STORE_TAC `a2:A word` `yp - 3` `EL (xp - 3) (xs:byte list)` THEN
  ASM_REWRITE_TAC[GSYM NOT_LE] THEN
  SUBGOAL_THEN `word_sub (word n) (word 4):A word = word (n - 4)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[WORD_SUB]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_THM; SUB_0]) THEN
  ASM_CASES_TAC `n = 4` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MP6AUX_WORD_COPY_BWD_0] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "list_copy_bwd"))
        (concl th) && not (is_forall (concl th)))) THEN
    ONCE_REWRITE_TAC[list_copy_bwd_def] THEN
    REWRITE_TAC[LENGTH_LUPDATE] THEN
    SUBGOAL_THEN `0 <= (xp - 4) + 1 /\ xp - 4 < LENGTH (xs:byte list) /\
                  0 <= (yp - 4) + 1 /\ yp - 4 < LENGTH (ys:byte list)`
      (fun th -> REWRITE_TAC[th]) THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXISTS_TAC `mm''':A word->A word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `4 <= xp /\ 4 <= yp` STRIP_ASSUME_TAC THENL
   [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MP6AUX_WORD_ADD_SUB] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 4` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "list_copy_bwd"))
      (concl th) && is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`xp - 4`; `yp - 4`;
    `LUPDATE (EL (xp - 3) xs) (yp - 3) (LUPDATE (EL (xp - 2) xs) (yp - 2)
      (LUPDATE (EL (xp - 1) xs) (yp - 1) (LUPDATE (EL xp xs) yp (ys:byte list))))`;
    `ys1:byte list`; `mm''':A word->A word_loc`]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "word_loc"] THEN
  CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN ASM_REWRITE_TAC[option_INJ] THEN
  CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[]);;

(* HOL4 line 15729 *)
let word_copy_bwd_alias_thm = prove
 (`!c be ts p2 fl_ys refs sp st dm bl v2 vars.
   !n xp yp ys ys1 (m:A word -> A word_loc).
     memory_rel c be ts (insert p2 (bvl_ByteArray fl_ys ys) refs)
       sp st m dm (CONS (data_RefPtr bl p2,v2) vars) /\
     list_copy_bwd_alias n xp yp ys = SOME ys1 /\
     good_dimindex (:A) /\ n < dimword (:A) ==>
     ?(w2:A word) a2 m1.
       v2 = wl_Word w2 /\
       get_real_addr c st w2 = SOME a2 /\
       word_copy_bwd be (word n) (word_add (word_add a2 bytes_in_word) (word xp))
         (word_add (word_add a2 bytes_in_word) (word yp)) m dm = SOME m1 /\
       memory_rel c be ts (insert p2 (bvl_ByteArray fl_ys ys1) refs)
         sp st m1 dm (CONS (data_RefPtr bl p2,v2) vars)`,
  REPLICATE_TAC 12 GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP6AUX_DIMWORD_GE_256) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `insert p2 (bvl_ByteArray fl_ys ys) (refs:(data_v bvl_ref)spt)`; `sp:num`;
    `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`; `dm:A word->bool`;
    `bl:bool`; `p2:num`; `v2:A word_loc`; `vars:(data_v#A word_loc)list`;
    `fl_ys:bool`; `ys:byte list`] memory_rel_ByteArray_IMP) THEN
  ASM_REWRITE_TAC[lookup_insert] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:A word` (X_CHOOSE_THEN `a2:A word`
    (X_CHOOSE_THEN `x2:A word` (fun th -> let l = CONJUNCTS th in
       MAP_EVERY (fun i -> ASSUME_TAC (el i l)) [0;7;10])))) THEN
  RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`w2:A word`; `a2:A word`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n <= xp + 1 /\ xp < LENGTH (ys:byte list) /\ n <= yp + 1 /\
                yp < LENGTH (ys:byte list) /\
                4 < dimword(:A) /\ 2 < dimword(:A) /\ 1 < dimword(:A) /\
                0 < dimword(:A)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `list_copy_bwd_alias n xp yp ys = SOME (ys1:byte list)` THEN
    ONCE_REWRITE_TAC[list_copy_bwd_alias_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
    MP6AUX_ASM_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `list_copy_bwd_alias n xp yp ys = SOME (ys1:byte list)` THEN
  ONCE_REWRITE_TAC[list_copy_bwd_alias_def] THEN ONCE_REWRITE_TAC[word_copy_bwd_def] THEN
  ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  SIMP_TAC[ASSUME `n < dimword(:A)`; ASSUME `4 < dimword(:A)`; ASSUME `2 < dimword(:A)`;
           ASSUME `0 < dimword(:A)`; MP6AUX_WORD_ULT_SMALL; MP6AUX_WORD_EQ_SMALL] THEN
  ASM_CASES_TAC `n = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXISTS_TAC `m:A word->A word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[OPTION_BIND_DEF] THEN
    MP6AUX_STORE_ONE_TAC `a2:A word` `yp:num` `EL xp (ys:byte list)` THEN
    EXISTS_TAC `mm:A word->A word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[option_INJ; o_THM; SUB_0] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `xp - 1 < LENGTH (ys:byte list) /\ 1 <= xp /\ 1 <= yp`
      STRIP_ASSUME_TAC THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[OPTION_BIND_DEF; MP6AUX_WORD_ADD_SUB] THEN
    MP6AUX_STORE_ONE_TAC `a2:A word` `yp:num` `EL xp (ys:byte list)` THEN
    MP6AUX_STORE_ONE_TAC `a2:A word` `yp - 1` `EL (xp - 1) (ys:byte list)` THEN
    EXISTS_TAC `mm':A word->A word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 3` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[option_INJ; o_THM; SUB_0] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `xp - 1 < LENGTH (ys:byte list) /\ xp - 2 < LENGTH ys /\
                  1 <= xp /\ 2 <= xp /\ 1 <= yp /\ 2 <= yp`
      STRIP_ASSUME_TAC THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[OPTION_BIND_DEF; MP6AUX_WORD_ADD_SUB] THEN
    MP6AUX_STORE_ONE_TAC `a2:A word` `yp:num` `EL xp (ys:byte list)` THEN
    MP6AUX_STORE_ONE_TAC `a2:A word` `yp - 1` `EL (xp - 1) (ys:byte list)` THEN
    MP6AUX_STORE_ONE_TAC `a2:A word` `yp - 2` `EL (xp - 2) (ys:byte list)` THEN
    EXISTS_TAC `mm'':A word->A word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `xp - 1 < LENGTH (ys:byte list) /\ xp - 2 < LENGTH ys /\
                xp - 3 < LENGTH ys /\ 1 <= xp /\ 2 <= xp /\ 3 <= xp /\
                1 <= yp /\ 2 <= yp /\ 3 <= yp /\ 4 <= n /\ n - 4 < n /\
                n - 4 < dimword(:A)`
    STRIP_ASSUME_TAC THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[OPTION_BIND_DEF; MP6AUX_WORD_ADD_SUB; SUB_0] THEN
  MP6AUX_STORE_ONE_TAC `a2:A word` `yp:num` `EL xp (ys:byte list)` THEN
  MP6AUX_STORE_ONE_TAC `a2:A word` `yp - 1` `EL (xp - 1) (ys:byte list)` THEN
  MP6AUX_STORE_ONE_TAC `a2:A word` `yp - 2` `EL (xp - 2) (ys:byte list)` THEN
  MP6AUX_STORE_ONE_TAC `a2:A word` `yp - 3` `EL (xp - 3) (ys:byte list)` THEN
  ASM_REWRITE_TAC[GSYM NOT_LE] THEN
  SUBGOAL_THEN `word_sub (word n) (word 4):A word = word (n - 4)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[WORD_SUB]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_THM; SUB_0]) THEN
  ASM_CASES_TAC `n = 4` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MP6AUX_WORD_COPY_BWD_0] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "list_copy_bwd_alias"))
        (concl th) && not (is_forall (concl th)))) THEN
    ONCE_REWRITE_TAC[list_copy_bwd_alias_def] THEN
    REWRITE_TAC[LENGTH_LUPDATE] THEN
    SUBGOAL_THEN `0 <= (xp - 4) + 1 /\ xp - 4 < LENGTH (ys:byte list) /\
                  0 <= (yp - 4) + 1 /\ yp - 4 < LENGTH (ys:byte list)`
      (fun th -> REWRITE_TAC[th]) THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXISTS_TAC `mm''':A word->A word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `4 <= xp /\ 4 <= yp` STRIP_ASSUME_TAC THENL
   [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MP6AUX_WORD_ADD_SUB] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 4` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "list_copy_bwd_alias"))
      (concl th) && is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`xp - 4`; `yp - 4`;
    `LUPDATE (EL (xp - 3) ys) (yp - 3) (LUPDATE (EL (xp - 2) ys) (yp - 2)
      (LUPDATE (EL (xp - 1) ys) (yp - 1) (LUPDATE (EL xp ys) yp (ys:byte list))))`;
    `ys1:byte list`; `mm''':A word->A word_loc`]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "word_loc"] THEN
  CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN ASM_REWRITE_TAC[option_INJ] THEN
  CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[]);;

(* HOL4 line 15827 *)
let list_copy_def = cake_def
  `list_copy n xp (xs:A list) yp ys =
     if yp <= xp \/ n + xp = 0
     then list_copy_fwd n xp xs yp ys
     else list_copy_bwd n ((xp + n) - 1) xs ((yp + n) - 1) ys`;;

(* HOL4 line 15834 *)
let list_copy_alias_def = cake_def
  `list_copy_alias n xp yp (ys:A list) =
     if yp <= xp \/ n + xp = 0
     then list_copy_fwd_alias n xp yp ys
     else list_copy_bwd_alias n ((xp + n) - 1) ((yp + n) - 1) ys`;;

(* the copy of n elements of xs from xp into ys at yp, elementwise *)
let MP6AUX_LENGTH_COPY = prove
 (`!n xp (xs:A list) yp ys.
     xp + n <= LENGTH xs /\ yp + n <= LENGTH ys ==>
     LENGTH (APPEND (APPEND (TAKE yp ys) (TAKE n (DROP xp xs))) (DROP (n + yp) ys)) =
     LENGTH ys`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LENGTH_APPEND; LENGTH_DROP] THEN
  SUBGOAL_THEN `LENGTH (TAKE yp (ys:A list)) = yp /\
                LENGTH (TAKE n (DROP xp (xs:A list))) = n`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC LENGTH_TAKE THEN REWRITE_TAC[LENGTH_DROP] THEN
    ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let MP6AUX_EL_COPY = prove
 (`!n xp (xs:A list) yp ys i.
     xp + n <= LENGTH xs /\ yp + n <= LENGTH ys /\ i < LENGTH ys ==>
     EL i (APPEND (APPEND (TAKE yp ys) (TAKE n (DROP xp xs))) (DROP (n + yp) ys)) =
     if i < yp then EL i ys else if i < yp + n then EL (xp + (i - yp)) xs
     else EL i ys`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (TAKE yp (ys:A list)) = yp /\
                LENGTH (TAKE n (DROP xp (xs:A list))) = n`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LENGTH_TAKE THEN REWRITE_TAC[LENGTH_DROP] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[EL_APPEND_EQN; LENGTH_APPEND] THEN
  ASM_CASES_TAC `i < yp:num` THEN ASM_SIMP_TAC[EL_TAKE] THEN
  ASM_CASES_TAC `i < yp + n:num` THEN ASM_REWRITE_TAC[] THENL
   [ASM_ARITH_TAC;
    ASM_SIMP_TAC[ARITH_RULE `~(i < yp) /\ i < yp + n ==> i - yp < n`; EL_TAKE] THEN
    SUBGOAL_THEN `EL (i - yp) (DROP xp (xs:A list)) = EL ((i - yp) + xp) xs`
      SUBST1_TAC THENL
     [MATCH_MP_TAC EL_DROP THEN ASM_ARITH_TAC;
      AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC];
    SUBGOAL_THEN `EL (i - (yp + n)) (DROP (n + yp) (ys:A list)) =
                  EL ((i - (yp + n)) + (n + yp)) ys` SUBST1_TAC THENL
     [MATCH_MP_TAC EL_DROP THEN ASM_ARITH_TAC;
      AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]]);;

(* rewrite one EL of a copy term with MP6AUX_EL_COPY, proving its side    *)
(* conditions by arithmetic                                                 *)
let MP6AUX_EL_COPY_TAC (asl,w as g) =
  let pat = lhand(rand(snd(strip_forall(concl MP6AUX_EL_COPY)))) in
  let t = find_term (fun t -> can (term_match [] pat) t) w in
  let ith = PART_MATCH (lhand o rand) MP6AUX_EL_COPY t in
  (MP_TAC ith THEN ANTS_TAC THENL
    [ASM_SIMP_TAC[MP6AUX_LENGTH_COPY] THEN MP6AUX_ASM_ARITH_TAC;
     DISCH_THEN SUBST1_TAC]) g;;

let MP6AUX_COPY_CHAIN4 = prove
 (`!xp (xs:A list) yp ys.
     xp + 4 <= LENGTH xs /\ yp + 4 <= LENGTH ys ==>
     (LUPDATE (EL (xp + 3) xs) (yp + 3) o LUPDATE (EL (xp + 2) xs) (yp + 2) o
      LUPDATE (EL (xp + 1) xs) (yp + 1) o LUPDATE (EL (xp + 0) xs) (yp + 0)) ys =
     APPEND (APPEND (TAKE yp ys) (TAKE 4 (DROP xp xs))) (DROP (4 + yp) ys)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM; LIST_EQ] THEN
  ASM_SIMP_TAC[MP6AUX_LENGTH_COPY; LENGTH_LUPDATE] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MP6AUX_EL_COPY; EL_LUPDATE; LENGTH_LUPDATE] THEN
  MP6AUX_COND_ARITH_TAC);;

let MP6AUX_COPY_SPLIT = prove
 (`!n xp (xs:A list) yp ys.
     4 <= n /\ xp + n <= LENGTH xs /\ yp + n <= LENGTH ys ==>
     APPEND (APPEND (TAKE (yp + 4)
       (APPEND (APPEND (TAKE yp ys) (TAKE 4 (DROP xp xs))) (DROP (4 + yp) ys)))
       (TAKE (n - 4) (DROP (xp + 4) xs)))
       (DROP (n - 4 + yp + 4)
         (APPEND (APPEND (TAKE yp ys) (TAKE 4 (DROP xp xs))) (DROP (4 + yp) ys))) =
     APPEND (APPEND (TAKE yp ys) (TAKE n (DROP xp xs))) (DROP (n + yp) ys)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `xp + 4 <= LENGTH (xs:A list) /\ yp + 4 <= LENGTH (ys:A list) /\
                (xp + 4) + (n - 4) <= LENGTH xs /\ (yp + 4) + (n - 4) <= LENGTH ys`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LIST_EQ] THEN ASM_SIMP_TAC[MP6AUX_LENGTH_COPY] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MP6AUX_EL_COPY; MP6AUX_LENGTH_COPY] THEN
  MP6AUX_COND_ARITH_TAC);;

let MP6AUX_COPY_SPLIT_ALIAS = prove
 (`!n xp yp (ys:A list).
     yp <= xp /\ 4 <= n /\ xp + n <= LENGTH ys /\ yp + n <= LENGTH ys ==>
     APPEND (APPEND (TAKE (yp + 4)
       (APPEND (APPEND (TAKE yp ys) (TAKE 4 (DROP xp ys))) (DROP (4 + yp) ys)))
       (TAKE (n - 4) (DROP (xp + 4)
          (APPEND (APPEND (TAKE yp ys) (TAKE 4 (DROP xp ys))) (DROP (4 + yp) ys)))))
       (DROP (n - 4 + yp + 4)
         (APPEND (APPEND (TAKE yp ys) (TAKE 4 (DROP xp ys))) (DROP (4 + yp) ys))) =
     APPEND (APPEND (TAKE yp ys) (TAKE n (DROP xp ys))) (DROP (n + yp) ys)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `xp + 4 <= LENGTH (ys:A list) /\ yp + 4 <= LENGTH ys /\
                (xp + 4) + (n - 4) <= LENGTH ys /\ (yp + 4) + (n - 4) <= LENGTH ys`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LIST_EQ] THEN ASM_SIMP_TAC[MP6AUX_LENGTH_COPY] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MP6AUX_LENGTH_COPY] THEN
  REPEAT(MP6AUX_EL_COPY_TAC ORELSE MP6AUX_COND_DECIDE_TAC) THEN
  FIRST [REFL_TAC;
         MATCH_MP_TAC(TAUT `F ==> p`) THEN MP6AUX_ASM_ARITH_TAC;
         AP_THM_TAC THEN AP_TERM_TAC THEN MP6AUX_ASM_ARITH_TAC]);;

(* HOL4 line 15841 *)
let list_copy_fwd_eq = prove
 (`!n xp (xs:A list) yp ys.
     xp + n <= LENGTH xs /\
     yp + n <= LENGTH ys ==>
     list_copy_fwd n xp xs yp ys =
     SOME (APPEND (APPEND (TAKE yp ys) (TAKE n (DROP xp xs))) (DROP (n + yp) ys))`,
  MATCH_MP_TAC list_copy_fwd_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[list_copy_fwd_def] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[option_INJ; TAKE_0; APPEND_NIL; ADD_CLAUSES; TAKE_DROP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun k -> ASM_CASES_TAC (mk_eq(`n:num`,mk_small_numeral k)) THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[option_INJ; LIST_EQ; o_THM] THEN
     ASM_SIMP_TAC[MP6AUX_LENGTH_COPY; LENGTH_LUPDATE] THEN
     REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MP6AUX_EL_COPY; EL_LUPDATE; LENGTH_LUPDATE] THEN
     MP6AUX_COND_ARITH_TAC;
     ASM_REWRITE_TAC[]]) [1;2;3] THEN
  SUBGOAL_THEN `(xp + 4) + (n - 4) <= LENGTH (xs:A list) /\
                (yp + 4) + (n - 4) <= LENGTH (ys:A list) /\ 4 <= n /\
                xp + 4 <= LENGTH xs /\ yp + 4 <= LENGTH ys`
    STRIP_ASSUME_TAC THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MP6AUX_COPY_CHAIN4] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_SIMP_TAC[MP6AUX_COPY_CHAIN4; MP6AUX_LENGTH_COPY] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[MP6AUX_COPY_SPLIT]);;

(* the backward copy of n elements ending at xp into ys ending at yp       *)
let MP6AUX_LENGTH_COPY_BWD = prove
 (`!n xp (xs:A list) yp ys.
     n <= xp + 1 /\ xp < LENGTH xs /\ n <= yp + 1 /\ yp < LENGTH ys ==>
     LENGTH (APPEND (APPEND (TAKE ((yp + 1) - n) ys) (TAKE n (DROP ((xp + 1) - n) xs)))
               (DROP (yp + 1) ys)) = LENGTH ys`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `(xp + 1) - n`; `xs:A list`; `(yp + 1) - n`; `ys:A list`]
    MP6AUX_LENGTH_COPY) THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= yp + 1 ==> n + (yp + 1) - n = yp + 1`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let MP6AUX_EL_COPY_BWD = prove
 (`!n xp (xs:A list) yp ys i.
     n <= xp + 1 /\ xp < LENGTH xs /\ n <= yp + 1 /\ yp < LENGTH ys /\ i < LENGTH ys ==>
     EL i (APPEND (APPEND (TAKE ((yp + 1) - n) ys) (TAKE n (DROP ((xp + 1) - n) xs)))
             (DROP (yp + 1) ys)) =
     if i + n <= yp then EL i ys else if i <= yp then EL ((xp + i) - yp) xs
     else EL i ys`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `(xp + 1) - n`; `xs:A list`; `(yp + 1) - n`; `ys:A list`;
    `i:num`] MP6AUX_EL_COPY) THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= yp + 1 ==> n + (yp + 1) - n = yp + 1`] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP6AUX_COND_ARITH_TAC);;

let MP6AUX_EL_COPY_BWD_TAC (asl,w as g) =
  let pat = lhand(rand(snd(strip_forall(concl MP6AUX_EL_COPY_BWD)))) in
  let t = find_term (fun t -> can (term_match [] pat) t) w in
  let ith = PART_MATCH (lhand o rand) MP6AUX_EL_COPY_BWD t in
  (MP_TAC ith THEN ANTS_TAC THENL
    [ASM_SIMP_TAC[MP6AUX_LENGTH_COPY_BWD] THEN MP6AUX_ASM_ARITH_TAC;
     DISCH_THEN SUBST1_TAC]) g;;

let MP6AUX_COPY_BWD_FINISH_TAC =
  REPEAT(MP6AUX_EL_COPY_BWD_TAC ORELSE MP6AUX_COND_DECIDE_TAC) THEN
  FIRST [REFL_TAC;
         MATCH_MP_TAC(TAUT `F ==> p`) THEN MP6AUX_ASM_ARITH_TAC;
         AP_THM_TAC THEN AP_TERM_TAC THEN MP6AUX_ASM_ARITH_TAC];;

let MP6AUX_COPY_BWD_CHAIN4 = prove
 (`!xp (xs:A list) yp ys.
     3 <= xp /\ xp < LENGTH xs /\ 3 <= yp /\ yp < LENGTH ys ==>
     (LUPDATE (EL (xp - 3) xs) (yp - 3) o LUPDATE (EL (xp - 2) xs) (yp - 2) o
      LUPDATE (EL (xp - 1) xs) (yp - 1) o LUPDATE (EL (xp - 0) xs) (yp - 0)) ys =
     APPEND (APPEND (TAKE ((yp + 1) - 4) ys) (TAKE 4 (DROP ((xp + 1) - 4) xs)))
       (DROP (yp + 1) ys)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM; LIST_EQ] THEN
  SUBGOAL_THEN `4 <= xp + 1 /\ 4 <= yp + 1` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MP6AUX_LENGTH_COPY_BWD; LENGTH_LUPDATE] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_LUPDATE; LENGTH_LUPDATE] THEN
  MP6AUX_COPY_BWD_FINISH_TAC);;

let MP6AUX_COPY_BWD_SPLIT = prove
 (`!n xp (xs:A list) yp ys.
     4 <= n /\ n <= xp + 1 /\ xp < LENGTH xs /\ n <= yp + 1 /\ yp < LENGTH ys ==>
     APPEND (APPEND (TAKE (((yp - 4) + 1) - (n - 4))
       (APPEND (APPEND (TAKE ((yp + 1) - 4) ys) (TAKE 4 (DROP ((xp + 1) - 4) xs)))
          (DROP (yp + 1) ys)))
       (TAKE (n - 4) (DROP (((xp - 4) + 1) - (n - 4)) xs)))
       (DROP ((yp - 4) + 1)
         (APPEND (APPEND (TAKE ((yp + 1) - 4) ys) (TAKE 4 (DROP ((xp + 1) - 4) xs)))
            (DROP (yp + 1) ys))) =
     APPEND (APPEND (TAKE ((yp + 1) - n) ys) (TAKE n (DROP ((xp + 1) - n) xs)))
       (DROP (yp + 1) ys)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `4 <= xp + 1 /\ 4 <= yp + 1 /\ n - 4 <= (xp - 4) + 1 /\
                xp - 4 < LENGTH (xs:A list) /\ n - 4 <= (yp - 4) + 1 /\
                yp - 4 < LENGTH (ys:A list)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LIST_EQ] THEN ASM_SIMP_TAC[MP6AUX_LENGTH_COPY_BWD] THEN
  REPEAT STRIP_TAC THEN MP6AUX_COPY_BWD_FINISH_TAC);;

let MP6AUX_COPY_BWD_SPLIT_ALIAS = prove
 (`!n xp yp (ys:A list).
     xp <= yp /\ 4 <= n /\ n <= xp + 1 /\ xp < LENGTH ys /\ n <= yp + 1 /\
     yp < LENGTH ys ==>
     APPEND (APPEND (TAKE (((yp - 4) + 1) - (n - 4))
       (APPEND (APPEND (TAKE ((yp + 1) - 4) ys) (TAKE 4 (DROP ((xp + 1) - 4) ys)))
          (DROP (yp + 1) ys)))
       (TAKE (n - 4) (DROP (((xp - 4) + 1) - (n - 4))
         (APPEND (APPEND (TAKE ((yp + 1) - 4) ys) (TAKE 4 (DROP ((xp + 1) - 4) ys)))
            (DROP (yp + 1) ys)))))
       (DROP ((yp - 4) + 1)
         (APPEND (APPEND (TAKE ((yp + 1) - 4) ys) (TAKE 4 (DROP ((xp + 1) - 4) ys)))
            (DROP (yp + 1) ys))) =
     APPEND (APPEND (TAKE ((yp + 1) - n) ys) (TAKE n (DROP ((xp + 1) - n) ys)))
       (DROP (yp + 1) ys)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `4 <= xp + 1 /\ 4 <= yp + 1 /\ n - 4 <= (xp - 4) + 1 /\
                xp - 4 < LENGTH (ys:A list) /\ n - 4 <= (yp - 4) + 1 /\
                yp - 4 < LENGTH ys`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LIST_EQ] THEN ASM_SIMP_TAC[MP6AUX_LENGTH_COPY_BWD] THEN
  REPEAT STRIP_TAC THEN MP6AUX_COPY_BWD_FINISH_TAC);;

(* HOL4 line 15862 *)
let list_copy_bwd_eq = prove
 (`!n xp (xs:A list) yp ys.
     n <= xp + 1 /\ xp < LENGTH xs /\
     n <= yp + 1 /\ yp < LENGTH ys ==>
     list_copy_bwd n xp xs yp ys =
     SOME (APPEND (APPEND (TAKE ((yp + 1) - n) ys) (TAKE n (DROP ((xp + 1) - n) xs)))
                  (DROP (yp + 1) ys))`,
  MATCH_MP_TAC list_copy_bwd_ind THEN REWRITE_TAC[minus_def] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[list_copy_bwd_def] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[option_INJ; TAKE_0; APPEND_NIL; SUB_0; TAKE_DROP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun k -> ASM_CASES_TAC (mk_eq(`n:num`,mk_small_numeral k)) THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN
     REWRITE_TAC[option_INJ; LIST_EQ; o_THM] THEN
     ASM_SIMP_TAC[MP6AUX_LENGTH_COPY_BWD; LENGTH_LUPDATE] THEN
     REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_LUPDATE; LENGTH_LUPDATE] THEN
     MP6AUX_COPY_BWD_FINISH_TAC;
     ASM_REWRITE_TAC[]]) [1;2;3] THEN
  SUBGOAL_THEN `n - 4 <= (xp - 4) + 1 /\ xp - 4 < LENGTH (xs:A list) /\
                n - 4 <= (yp - 4) + 1 /\ yp - 4 < LENGTH (ys:A list) /\
                4 <= n /\ 3 <= xp /\ 3 <= yp`
    STRIP_ASSUME_TAC THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MP6AUX_COPY_BWD_CHAIN4] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_SIMP_TAC[MP6AUX_COPY_BWD_CHAIN4; MP6AUX_LENGTH_COPY_BWD;
               ARITH_RULE `3 <= x ==> 4 <= x + 1`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th; option_INJ]) THEN
  MATCH_MP_TAC MP6AUX_COPY_BWD_SPLIT THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 15906 *)
let list_copy_thm = prove
 (`!(xs:A list) ys xp yp n ys1.
     copy_array (xs,&xp) (&n) (SOME (ys,&yp)) = SOME ys1 ==>
     list_copy n xp xs yp ys = SOME ys1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[copy_array_def; I_THM; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_ABS_NUM; NUM_OF_INT_OF_NUM; INT_OF_NUM_LT;
              CONJUNCT1 LT; NOT_LT] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT; DE_MORGAN_THM]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[list_copy_def] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[list_copy_fwd_eq] THEN REWRITE_TAC[ADD_SYM];
    MP_TAC(SPECL [`n:num`; `(xp + n) - 1`; `xs:A list`; `(yp + n) - 1`; `ys:A list`]
      list_copy_bwd_eq) THEN
    ANTS_TAC THENL [MP6AUX_ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[option_INJ] THEN
    SUBGOAL_THEN `((yp + n) - 1 + 1) - n = yp /\ ((xp + n) - 1 + 1) - n = xp /\
                  (yp + n) - 1 + 1 = yp + n` (fun th -> REWRITE_TAC[th]) THEN
    MP6AUX_ASM_ARITH_TAC]);;

(* HOL4 line 15928 *)
let list_copy_fwd_alias_eq = prove
 (`!n xp yp (ys:A list).
     yp <= xp /\
     xp + n <= LENGTH ys /\
     yp + n <= LENGTH ys ==>
     list_copy_fwd_alias n xp yp ys =
     SOME (APPEND (APPEND (TAKE yp ys) (TAKE n (DROP xp ys))) (DROP (n + yp) ys))`,
  MATCH_MP_TAC list_copy_fwd_alias_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[list_copy_fwd_alias_def] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[option_INJ; TAKE_0; APPEND_NIL; ADD_CLAUSES; TAKE_DROP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun k -> ASM_CASES_TAC (mk_eq(`n:num`,mk_small_numeral k)) THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[option_INJ; LIST_EQ; o_THM] THEN
     ASM_SIMP_TAC[MP6AUX_LENGTH_COPY; LENGTH_LUPDATE] THEN
     REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MP6AUX_EL_COPY; EL_LUPDATE; LENGTH_LUPDATE] THEN
     MP6AUX_COND_ARITH_TAC;
     ASM_REWRITE_TAC[]]) [1;2;3] THEN
  SUBGOAL_THEN `(xp + 4) + (n - 4) <= LENGTH (ys:A list) /\
                (yp + 4) + (n - 4) <= LENGTH ys /\ 4 <= n /\ yp + 4 <= xp + 4 /\
                xp + 4 <= LENGTH ys /\ yp + 4 <= LENGTH ys`
    STRIP_ASSUME_TAC THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MP6AUX_COPY_CHAIN4] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_SIMP_TAC[MP6AUX_COPY_CHAIN4; MP6AUX_LENGTH_COPY] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[MP6AUX_COPY_SPLIT_ALIAS]);;

(* HOL4 line 15950 *)
let list_copy_bwd_alias_eq = prove
 (`!n xp yp (ys:A list).
     xp <= yp /\
     n <= xp + 1 /\ xp < LENGTH ys /\
     n <= yp + 1 /\ yp < LENGTH ys ==>
     list_copy_bwd_alias n xp yp ys =
     SOME (APPEND (APPEND (TAKE ((yp + 1) - n) ys) (TAKE n (DROP ((xp + 1) - n) ys)))
                  (DROP (yp + 1) ys))`,
  MATCH_MP_TAC list_copy_bwd_alias_ind THEN REWRITE_TAC[minus_def] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[list_copy_bwd_alias_def] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[option_INJ; TAKE_0; APPEND_NIL; SUB_0; TAKE_DROP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun k -> ASM_CASES_TAC (mk_eq(`n:num`,mk_small_numeral k)) THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN
     REWRITE_TAC[option_INJ; LIST_EQ; o_THM] THEN
     ASM_SIMP_TAC[MP6AUX_LENGTH_COPY_BWD; LENGTH_LUPDATE] THEN
     REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_LUPDATE; LENGTH_LUPDATE] THEN
     MP6AUX_COPY_BWD_FINISH_TAC;
     ASM_REWRITE_TAC[]]) [1;2;3] THEN
  SUBGOAL_THEN `n - 4 <= (xp - 4) + 1 /\ xp - 4 < LENGTH (ys:A list) /\
                n - 4 <= (yp - 4) + 1 /\ yp - 4 < LENGTH (ys:A list) /\
                4 <= n /\ 3 <= xp /\ 3 <= yp /\ xp - 4 <= yp - 4`
    STRIP_ASSUME_TAC THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MP6AUX_COPY_BWD_CHAIN4] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_SIMP_TAC[MP6AUX_COPY_BWD_CHAIN4; MP6AUX_LENGTH_COPY_BWD;
               ARITH_RULE `3 <= x ==> 4 <= x + 1`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th; option_INJ]) THEN
  MATCH_MP_TAC MP6AUX_COPY_BWD_SPLIT_ALIAS THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 15995 *)
let list_copy_alias_thm = prove
 (`!(ys:A list) xp yp n ys1.
     copy_array (ys,&xp) (&n) (SOME (ys,&yp)) = SOME ys1 ==>
     list_copy_alias n xp yp ys = SOME ys1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[copy_array_def; I_THM; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_ABS_NUM; NUM_OF_INT_OF_NUM; INT_OF_NUM_LT;
              CONJUNCT1 LT; NOT_LT] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT; DE_MORGAN_THM]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[list_copy_alias_def] THEN
  COND_CASES_TAC THENL
   [ASM_CASES_TAC `yp <= xp:num` THENL
     [ASM_SIMP_TAC[list_copy_fwd_alias_eq] THEN REWRITE_TAC[ADD_SYM];
      SUBGOAL_THEN `n = 0 /\ xp = 0 /\ yp <= LENGTH (ys:A list)` STRIP_ASSUME_TAC THENL
       [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[list_copy_fwd_alias_def] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; TAKE_0; APPEND_NIL; TAKE_DROP; LE_0]];
    MP_TAC(SPECL [`n:num`; `(xp + n) - 1`; `(yp + n) - 1`; `ys:A list`]
      list_copy_bwd_alias_eq) THEN
    ANTS_TAC THENL [MP6AUX_ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[option_INJ] THEN
    SUBGOAL_THEN `((yp + n) - 1 + 1) - n = yp /\ ((xp + n) - 1 + 1) - n = xp /\
                  (yp + n) - 1 + 1 = yp + n` (fun th -> REWRITE_TAC[th]) THEN
    MP6AUX_ASM_ARITH_TAC]);;

(* HOL4 line 16013 *)
let copy_array_NONE_IMP = prove
 (`!(xs:(A word)list) ys xp n.
     copy_array (xs,&xp) (&n) NONE = SOME ys ==>
     list_copy_fwd n xp xs 0 (REPLICATE n (word 0)) = SOME ys`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[copy_array_def; I_THM; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_ABS_NUM; NUM_OF_INT_OF_NUM; INT_OF_NUM_LT;
              CONJUNCT1 LT; NOT_LT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT; DE_MORGAN_THM]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`n:num`; `xp:num`; `xs:(A word)list`; `0`;
    `REPLICATE n (word 0:A word)`] list_copy_fwd_eq) THEN
  ASM_REWRITE_TAC[LENGTH_REPLICATE; ADD_CLAUSES; LE_REFL] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[TAKE_0; APPEND; option_INJ] THEN
  MP_TAC(ISPEC `REPLICATE n (word 0:A word)` DROP_LENGTH_NIL) THEN
  REWRITE_TAC[LENGTH_REPLICATE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[APPEND_NIL]);;

(* HOL4 lines 16026-16041: ML tests of list_copy_alias_thm, not ported *)

(* HOL4 line 16045 *)
let word_copy_array_def = cake_def
  `word_copy_array be (n:A word) a a1 b b1 (m:A word -> A word_loc) dm =
     if word_ule b1 a1 then
       word_copy_fwd be n (word_add a a1) (word_add b b1) m dm
     else
       word_copy_bwd be n (word_sub (word_add (word_add a a1) n) (word 1))
         (word_sub (word_add (word_add b b1) n) (word 1)) m dm`;;

(* HOL4 line 16053 *)
let word_copy_bwd_0 = prove
 (`!be a1 a2 (m:A word -> A word_loc) dm.
     good_dimindex (:A) ==> word_copy_bwd be (word 0:A word) a1 a2 m dm = SOME m`,
  MATCH_ACCEPT_TAC MP6AUX_WORD_COPY_BWD_0);;

(* a byte array in memory_rel is shorter than dimword *)
let MP6AUX_BYTEARRAY_LENGTH = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl p v vars fl vals.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl p,v:A word_loc) vars) /\
     lookup p refs = SOME (bvl_ByteArray fl vals) /\ good_dimindex (:A) ==>
     LENGTH vals < dimword(:A)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_ByteArray_IMP) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word` (X_CHOOSE_THEN `a:A word`
    (X_CHOOSE_THEN `x:A word` (fun th -> MP_TAC(el 12 (CONJUNCTS th)))))) THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[good_dimindex_def; dimword_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* copy_array of a source array into a target array: the bounds *)
let MP6AUX_COPY_ARRAY_BOUNDS = prove
 (`!(xs:A list) ys xp yp n ys1.
     copy_array (xs,&xp) (&n) (SOME (ys,&yp)) = SOME ys1 ==>
     n + xp <= LENGTH xs /\ n + yp <= LENGTH ys`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[copy_array_def; I_THM; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_ABS_NUM; NUM_OF_INT_OF_NUM; INT_OF_NUM_LT;
              CONJUNCT1 LT; NOT_LT] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT; DE_MORGAN_THM]) THEN DISCH_TAC THEN
  MP6AUX_ASM_ARITH_TAC);;

(* HOL4 line 16061 *)
let word_copy_array_thm = prove
 (`!c be ts refs sp st dm bl1 p1 v1 bl2 p2 v2 vars fl_xs fl_ys.
   !n xp yp xs ys ys1 (m:A word -> A word_loc).
     memory_rel c be ts refs sp st m dm
       (CONS (data_RefPtr bl1 p1,v1) (CONS (data_RefPtr bl2 p2,v2) vars)) /\
     lookup p1 refs = SOME (bvl_ByteArray fl_xs xs) /\
     lookup p2 refs = SOME (bvl_ByteArray fl_ys ys) /\
     copy_array (xs,&xp) (&n) (SOME (ys,&yp)) = SOME ys1 /\
     good_dimindex (:A) /\ ~(p1 = p2) ==>
     ?w1 (w2:A word) a1 a2 m1.
       v1 = wl_Word w1 /\ v2 = wl_Word w2 /\
       get_real_addr c st w1 = SOME a1 /\
       get_real_addr c st w2 = SOME a2 /\
       word_copy_array be (word n) (word_add a1 bytes_in_word) (word xp)
         (word_add a2 bytes_in_word) (word yp) m dm = SOME m1 /\
       memory_rel c be ts (insert p2 (bvl_ByteArray fl_ys ys1) refs)
         sp st m1 dm (CONS (data_RefPtr bl1 p1,v1) (CONS (data_RefPtr bl2 p2,v2) vars))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP list_copy_thm) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP6AUX_COPY_ARRAY_BOUNDS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP6AUX_DIMWORD_GE_256) THEN
  SUBGOAL_THEN `LENGTH (xs:byte list) < dimword(:A) /\
                LENGTH (ys:byte list) < dimword(:A)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP MP6AUX_BYTEARRAY_LENGTH (CONJ th
        (CONJ (ASSUME `lookup p1 (refs:(data_v bvl_ref)spt) =
                       SOME (bvl_ByteArray fl_xs (xs:byte list))`)
              (ASSUME `good_dimindex(:A)`)))));
      FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP MP6AUX_BYTEARRAY_LENGTH
        (CONJ (MATCH_MP memory_rel_swap th)
        (CONJ (ASSUME `lookup p2 (refs:(data_v bvl_ref)spt) =
                       SOME (bvl_ByteArray fl_ys (ys:byte list))`)
              (ASSUME `good_dimindex(:A)`)))))] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `insert p2 (bvl_ByteArray fl_ys ys) refs = (refs:(data_v bvl_ref)spt)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC insert_unchanged THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `n < dimword(:A) /\ xp < dimword(:A) /\ yp < dimword(:A)`
    STRIP_ASSUME_TAC THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `list_copy n xp xs yp ys = SOME (ys1:byte list)` THEN
  REWRITE_TAC[list_copy_def] THEN COND_CASES_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `p2:num`; `fl_ys:bool`;
      `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,A word_loc)fmap`;
      `dm:A word->bool`; `bl1:bool`; `p1:num`; `v1:A word_loc`; `bl2:bool`;
      `v2:A word_loc`; `vars:(data_v#A word_loc)list`; `fl_xs:bool`; `xs:byte list`;
      `n:num`; `xp:num`; `yp:num`; `ys:byte list`; `ys1:byte list`;
      `m:A word->A word_loc`] word_copy_fwd_thm) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w1:A word` (X_CHOOSE_THEN `w2:A word`
      (X_CHOOSE_THEN `a1:A word` (X_CHOOSE_THEN `a2:A word`
      (X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC))))) THEN
    RVEQ_TAC THEN MAP_EVERY EXISTS_TAC [`w1:A word`; `w2:A word`; `a1:A word`; `a2:A word`] THEN
    ASM_REWRITE_TAC[word_copy_array_def; WORD_ULE; VAL_WORD; GSYM dimword_def] THEN
    ASM_SIMP_TAC[MOD_LT] THEN COND_CASES_TAC THENL
     [EXISTS_TAC `m1:A word->A word_loc` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `n = 0` SUBST_ALL_TAC THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[word_copy_bwd_0] THEN
    UNDISCH_TAC `word_copy_fwd be (word 0)
       (word_add (word_add a1 bytes_in_word) (word xp))
       (word_add (word_add a2 bytes_in_word) (word yp)) m dm = SOME (m1:A word->A word_loc)` THEN
    ONCE_REWRITE_TAC[word_copy_fwd_def] THEN
    ASM_SIMP_TAC[ARITH_RULE `256 <= n ==> ~(n <= 4)`; MP6AUX_WORD_ULT_SMALL;
                 ARITH_RULE `256 <= n ==> 4 < n /\ 2 < n /\ 0 < n`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[option_INJ] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[UNWIND_THM1] THEN
    ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
    MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `p2:num`; `fl_ys:bool`;
      `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,A word_loc)fmap`;
      `dm:A word->bool`; `bl1:bool`; `p1:num`; `v1:A word_loc`; `bl2:bool`;
      `v2:A word_loc`; `vars:(data_v#A word_loc)list`; `fl_xs:bool`; `xs:byte list`;
      `n:num`; `(xp + n) - 1`; `(yp + n) - 1`; `ys:byte list`; `ys1:byte list`;
      `m:A word->A word_loc`] word_copy_bwd_thm) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w1:A word` (X_CHOOSE_THEN `w2:A word`
      (X_CHOOSE_THEN `a1:A word` (X_CHOOSE_THEN `a2:A word`
      (X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC))))) THEN
    RVEQ_TAC THEN MAP_EVERY EXISTS_TAC [`w1:A word`; `w2:A word`; `a1:A word`; `a2:A word`;
                          `m1:A word->A word_loc`] THEN
    ASM_REWRITE_TAC[word_copy_array_def; WORD_ULE; VAL_WORD; GSYM dimword_def] THEN
    ASM_SIMP_TAC[MOD_LT] THEN
    SUBGOAL_THEN `1 <= xp + n /\ 1 <= yp + n` STRIP_ASSUME_TAC THENL
     [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MP6AUX_WORD_ADD_ADD; MP6AUX_WORD_ADD_SUB]]);;

(* HOL4 line 16110 *)
let word_copy_array_alias_thm = prove
 (`!c be ts refs sp st dm bl p2 v2 vars fl_ys.
   !n xp yp ys ys1 (m:A word -> A word_loc).
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl p2,v2) vars) /\
     lookup p2 refs = SOME (bvl_ByteArray fl_ys ys) /\
     copy_array (ys,&xp) (&n) (SOME (ys,&yp)) = SOME ys1 /\
     good_dimindex (:A) ==>
     ?(w2:A word) a2 m1.
       v2 = wl_Word w2 /\
       get_real_addr c st w2 = SOME a2 /\
       word_copy_array be (word n) (word_add a2 bytes_in_word) (word xp)
         (word_add a2 bytes_in_word) (word yp) m dm = SOME m1 /\
       memory_rel c be ts (insert p2 (bvl_ByteArray fl_ys ys1) refs)
         sp st m1 dm (CONS (data_RefPtr bl p2,v2) vars)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP list_copy_alias_thm) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP6AUX_COPY_ARRAY_BOUNDS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP6AUX_DIMWORD_GE_256) THEN
  SUBGOAL_THEN `LENGTH (ys:byte list) < dimword(:A)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP MP6AUX_BYTEARRAY_LENGTH (CONJ th
      (CONJ (ASSUME `lookup p2 (refs:(data_v bvl_ref)spt) =
                     SOME (bvl_ByteArray fl_ys (ys:byte list))`)
            (ASSUME `good_dimindex(:A)`))))) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `insert p2 (bvl_ByteArray fl_ys ys) refs = (refs:(data_v bvl_ref)spt)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC insert_unchanged THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `n < dimword(:A) /\ xp < dimword(:A) /\ yp < dimword(:A)`
    STRIP_ASSUME_TAC THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `list_copy_alias n xp yp ys = SOME (ys1:byte list)` THEN
  REWRITE_TAC[list_copy_alias_def] THEN COND_CASES_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `p2:num`; `fl_ys:bool`;
      `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,A word_loc)fmap`;
      `dm:A word->bool`; `bl:bool`; `v2:A word_loc`; `vars:(data_v#A word_loc)list`;
      `n:num`; `xp:num`; `yp:num`; `ys:byte list`; `ys1:byte list`;
      `m:A word->A word_loc`] word_copy_fwd_alias_thm) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w2:A word` (X_CHOOSE_THEN `a2:A word`
      (X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC))) THEN
    RVEQ_TAC THEN MAP_EVERY EXISTS_TAC [`w2:A word`; `a2:A word`] THEN
    ASM_REWRITE_TAC[word_copy_array_def; WORD_ULE; VAL_WORD; GSYM dimword_def] THEN
    ASM_SIMP_TAC[MOD_LT] THEN COND_CASES_TAC THENL
     [EXISTS_TAC `m1:A word->A word_loc` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `n = 0` SUBST_ALL_TAC THENL [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[word_copy_bwd_0] THEN
    UNDISCH_TAC `word_copy_fwd be (word 0)
       (word_add (word_add a2 bytes_in_word) (word xp))
       (word_add (word_add a2 bytes_in_word) (word yp)) m dm = SOME (m1:A word->A word_loc)` THEN
    ONCE_REWRITE_TAC[word_copy_fwd_def] THEN
    ASM_SIMP_TAC[ARITH_RULE `256 <= n ==> ~(n <= 4)`; MP6AUX_WORD_ULT_SMALL;
                 ARITH_RULE `256 <= n ==> 4 < n /\ 2 < n /\ 0 < n`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[option_INJ] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[UNWIND_THM1] THEN
    ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
    MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `p2:num`; `fl_ys:bool`;
      `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,A word_loc)fmap`;
      `dm:A word->bool`; `bl:bool`; `v2:A word_loc`; `vars:(data_v#A word_loc)list`;
      `n:num`; `(xp + n) - 1`; `(yp + n) - 1`; `ys:byte list`; `ys1:byte list`;
      `m:A word->A word_loc`] word_copy_bwd_alias_thm) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w2:A word` (X_CHOOSE_THEN `a2:A word`
      (X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC))) THEN
    RVEQ_TAC THEN MAP_EVERY EXISTS_TAC [`w2:A word`; `a2:A word`;
                                        `m1:A word->A word_loc`] THEN
    ASM_REWRITE_TAC[word_copy_array_def; WORD_ULE; VAL_WORD; GSYM dimword_def] THEN
    ASM_SIMP_TAC[MOD_LT] THEN
    SUBGOAL_THEN `1 <= xp + n /\ 1 <= yp + n` STRIP_ASSUME_TAC THENL
     [MP6AUX_ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MP6AUX_WORD_ADD_ADD; MP6AUX_WORD_ADD_SUB]]);;

(* HOL4 line 16156 *)
let word_of_byte_0 = prove
 (`word_of_byte (word 0) = word 0:A word`,
  REWRITE_TAC[word_of_byte_def; LET_DEF; LET_END_DEF; WORD_SHL_0; WORD_OR_0; COND_ID]);;

let MP6AUX_SET_BYTE_0 = prove
 (`!(a:A word) be. set_byte a (word 0) (word 0:A word) be = word 0`,
  REWRITE_TAC[set_byte_def; LET_DEF; LET_END_DEF; WORD_ZX_0; WORD_SHL_0; WORD_OR_0] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR; BIT_WORD_SLICE_ALT;
    BIT_WORD_0]);;

(* HOL4 line 16162 *)
let last_bytes_0 = prove
 (`!be nb a. last_bytes nb (word 0) a (word 0:A word) be = word 0`,
  GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[last_bytes_def] THEN
  ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; MP6AUX_SET_BYTE_0]);;

(* HOL4 line 16172 *)
let LUPDATE_REPLICATE = prove
 (`!(x:A) n a. LUPDATE x a (REPLICATE n x) = REPLICATE n x`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[REPLICATE; LUPDATE_def] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[LUPDATE_def]);;
let _ = cake_add_simps [LUPDATE_REPLICATE];;

(* HOL4 line 16179 (val: memory_rel_RefByte_alt for w = 0w, simplified) *)
let memory_rel_copy_array_NONE_lemma = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars new n fl.
     memory_rel c be ts refs sp st m dm vars /\
     ~(new IN domain refs) /\ byte_len (:A) n < sp /\
     byte_len (:A) n < 2 EXP (dimindex (:A) - 4) /\
     byte_len (:A) n < 2 EXP data_to_word_config_len_size c /\
     good_dimindex (:A) ==>
     ?free curr m1.
       FLOOKUP st NextFree = SOME (wl_Word free) /\
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       data_to_word_memoryProof_store_list free
         (CONS (wl_Word (make_byte_header c fl n))
               (REPLICATE (byte_len (:A) n) (wl_Word (word 0)))) m dm = SOME m1 /\
       memory_rel c be ts (insert new (bvl_ByteArray fl (REPLICATE n (word 0))) refs)
         (sp - (byte_len (:A) n + 1))
         (st |+ (NextFree,
                 wl_Word (word_add free
                            (word_mul bytes_in_word (word (byte_len (:A) n + 1))))))
         m1 dm
         (CONS (data_RefPtr T new,make_ptr c (word_sub free curr) (word 0:A word)
                                    (byte_len (:A) n)) vars)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,A word_loc)fmap`;
    `m:A word->A word_loc`; `dm:A word->bool`; `vars:(data_v#A word_loc)list`;
    `new:num`; `n:num`; `word 0:byte`; `fl:bool`] memory_rel_RefByte_alt) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; WORD_ZX_0; word_of_byte_0; last_bytes_0;
                  LUPDATE_REPLICATE]);;

let MP6AUX_GET_REAL_ADDR_NEXTFREE = prove
 (`!c st x (w:A word).
     get_real_addr c (st |+ (NextFree,x)) w = get_real_addr c st w`,
  REWRITE_TAC[get_real_addr_def; FLOOKUP_UPDATE; distinctness "store_name"]);;

(* HOL4 line 16185 *)
let memory_rel_copy_array_NONE = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl p1 v1 vars new fl_xs xs xp n
    ys fl.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl p1,v1:A word_loc) vars) /\
     ~(new IN domain refs) /\
     lookup p1 refs = SOME (bvl_ByteArray fl_xs xs) /\
     copy_array (xs,&xp) (&n) NONE = SOME ys /\
     byte_len (:A) n < sp /\ byte_len (:A) n < 2 EXP (dimindex (:A) - 4) /\
     byte_len (:A) n < 2 EXP data_to_word_config_len_size c /\ good_dimindex (:A) ==>
     ?free curr a1 a2 m1 m2 w1 w2.
       v1 = wl_Word w1 /\
       get_real_addr c st w1 = SOME a1 /\
       make_ptr c (word_sub free curr) (word 0:A word) (byte_len (:A) n) = wl_Word w2 /\
       get_real_addr c st w2 = SOME a2 /\
       FLOOKUP st NextFree = SOME (wl_Word free) /\
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       data_to_word_memoryProof_store_list free
         (CONS (wl_Word (make_byte_header c fl n))
               (REPLICATE (byte_len (:A) n) (wl_Word (word 0)))) m dm = SOME m1 /\
       word_copy_fwd be (word n) (word_add (word_add a1 bytes_in_word) (word xp))
         (word_add a2 bytes_in_word) m1 dm = SOME m2 /\
       memory_rel c be ts (insert new (bvl_ByteArray fl ys) refs)
         (sp - (byte_len (:A) n + 1))
         (st |+ (NextFree,
                 wl_Word (word_add free
                            (word_mul bytes_in_word (word (byte_len (:A) n + 1))))))
         m2 dm
         (CONS (data_RefPtr T new,wl_Word w2) vars)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,A word_loc)fmap`;
    `m:A word->A word_loc`; `dm:A word->bool`;
    `CONS (data_RefPtr bl p1,v1:A word_loc) vars`; `new:num`; `n:num`; `fl:bool`]
    memory_rel_copy_array_NONE_lemma) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `free:A word` (X_CHOOSE_THEN `curr:A word`
    (X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_swap) THEN
  REWRITE_TAC[make_ptr_def] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP copy_array_NONE_IMP) THEN
  SUBGOAL_THEN `~(p1 = new:num)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(new IN domain (refs:(data_v bvl_ref)spt))` THEN
    ASM_REWRITE_TAC[domain_lookup] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `n < dimword(:A)` ASSUME_TAC THENL
   [UNDISCH_TAC `byte_len (:A) n < 2 EXP (dimindex (:A) - 4)` THEN
    MP_TAC(SPECL [`n:num`; `4`] DIVISION) THEN MP_TAC(SPECL [`n:num`; `8`] DIVISION) THEN
    UNDISCH_TAC `good_dimindex(:A)` THEN
    REWRITE_TAC[good_dimindex_def; byte_len_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `new:num`; `fl:bool`;
    `refs:(data_v bvl_ref)spt`; `sp - (byte_len (:A) n + 1)`;
    `st |+ (NextFree, wl_Word (word_add free
       (word_mul bytes_in_word (word (byte_len (:A) n + 1))):A word))`;
    `dm:A word->bool`; `bl:bool`; `p1:num`; `v1:A word_loc`; `T`;
    `wl_Word (word_or (word_shl (word_sub free curr)
       (shift_length c - backend_common_word_shift (:A))) (word 1):A word)`; `vars:(data_v#A word_loc)list`; `fl_xs:bool`;
    `xs:byte list`; `n:num`; `xp:num`; `0`; `REPLICATE n (word 0:byte)`;
    `ys:byte list`; `m1:A word->A word_loc`] word_copy_fwd_thm) THEN
  ASM_REWRITE_TAC[MP6AUX_GET_REAL_ADDR_NEXTFREE; WORD_ADD_0] THEN
  REWRITE_TAC[injectivity "word_loc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word` (X_CHOOSE_THEN `w2':A word`
    (X_CHOOSE_THEN `a1:A word` (X_CHOOSE_THEN `a2:A word`
    (X_CHOOSE_THEN `m2:A word->A word_loc` STRIP_ASSUME_TAC))))) THEN
  RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`free:A word`; `curr:A word`; `a1:A word`; `a2:A word`;
    `m1:A word->A word_loc`; `m2:A word->A word_loc`; `w1:A word`;
    `(word_or (word_shl (word_sub free curr)
       (shift_length c - backend_common_word_shift (:A))) (word 1):A word)`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_tl) THEN REWRITE_TAC[]);;

(* HOL4 line 16226 *)
let write_bytearray_isWord = prove
 (`!dm be ls (a:A word) m x.
     isWord (m x) ==> isWord (write_bytearray a ls m dm be x)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[write_bytearray_def] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`word_add a (word 1):A word`; `m:A word->A word_loc`;
                                `x:A word`]) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`write_bytearray (word_add (a:A word) (word 1)) t m dm be`,
           `m':A word->A word_loc`) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[mem_store_byte_aux_def] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[APPLY_UPDATE_THM] THEN
  TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[isWord_def]);;

(* HOL4 line 16238 *)
let write_bytearray_append = prove
 (`!xs ys (a:A word) m dm be.
     (!i. i < LENGTH xs + LENGTH ys ==>
          ?b. mem_load_byte_aux m dm be (word_add a (word i)) = SOME b) ==>
     write_bytearray a (APPEND xs ys) m dm be =
     write_bytearray a xs (write_bytearray (word_add a (word (LENGTH xs))) ys m dm be)
       dm be`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; LENGTH; write_bytearray_def; WORD_ADD_0] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `write_bytearray (word_add a (word 1)) (APPEND t ys) m dm be =
    write_bytearray (word_add a (word 1)) t
      (write_bytearray (word_add (a:A word) (word (SUC (LENGTH (t:byte list)))))
         ys m dm be) dm be`
   SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`ys:byte list`; `word_add (a:A word) (word 1)`;
      `m:A word->A word_loc`; `dm:A word->bool`; `be:bool`]) THEN
    ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i + 1`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[WORD_ADD; WORD_ADD_AC];
      DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      AP_THM_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[ADD1; WORD_ADD; WORD_ADD_AC]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
  REWRITE_TAC[ARITH_RULE `0 < SUC n + p`; WORD_ADD_0; mem_load_byte_aux_def] THEN
  CASES_ON `(m:A word->A word_loc) (byte_align a)` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?w. write_bytearray (word_add a (word 1)) t
          (write_bytearray (word_add (a:A word) (word (SUC (LENGTH (t:byte list)))))
             ys m dm be) dm be (byte_align a) = wl_Word w`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM isWord_exists] THEN MATCH_MP_TAC write_bytearray_isWord THEN
    MATCH_MP_TAC write_bytearray_isWord THEN ASM_REWRITE_TAC[isWord_def];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[mem_store_byte_aux_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 16260 *)
let memory_rel_write_bytearray_lemma = prove
 (`!c be stm sp st dm b n w vs a rest bytes bytes0 (m:A word -> A word_loc) refs.
     memory_rel c be stm refs sp st m dm
       (CONS (data_RefPtr b n,wl_Word (w:A word)) vs) /\
     lookup n refs = SOME (bvl_ByteArray F (APPEND bytes0 rest)) /\
     LENGTH bytes = LENGTH bytes0 /\
     get_real_simple_addr c st w = SOME a /\ good_dimindex (:A) ==>
     memory_rel c be stm (insert n (bvl_ByteArray F (APPEND bytes rest)) refs) sp st
       (write_bytearray (word_add a bytes_in_word) bytes m dm be)
       dm (CONS (data_RefPtr b n,wl_Word w) vs)`,
  REPLICATE_TAC 11 GEN_TAC THEN
  SUBGOAL_THEN
   `!bytes rest bytes0 (m:A word -> A word_loc) refs.
     memory_rel c be stm refs sp st m dm
       (CONS (data_RefPtr b n,wl_Word (w:A word)) vs) /\
     lookup n refs = SOME (bvl_ByteArray F (APPEND bytes0 rest)) /\
     LENGTH (bytes:byte list) = LENGTH bytes0 /\
     get_real_simple_addr c st w = SOME a /\ good_dimindex (:A) ==>
     memory_rel c be stm (insert n (bvl_ByteArray F (APPEND bytes rest)) refs) sp st
       (write_bytearray (word_add a bytes_in_word) bytes m dm be)
       dm (CONS (data_RefPtr b n,wl_Word w) vs)`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC SNOC_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `bytes0:byte list = []` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[LENGTH_EQ_NIL; LENGTH]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND]) THEN
    ASM_SIMP_TAC[APPEND; write_bytearray_def; insert_unchanged];
    ALL_TAC] THEN
  X_GEN_TAC `bytes:byte list` THEN DISCH_TAC THEN X_GEN_TAC `new_b:byte` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `bytes0:byte list` SNOC_CASES) THEN STRIP_TAC THENL
   [UNDISCH_TAC `LENGTH (SNOC (new_b:byte) bytes) = LENGTH (bytes0:byte list)` THEN
    ASM_REWRITE_TAC[LENGTH_SNOC; LENGTH; NOT_SUC];
    ALL_TAC] THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_SNOC; SUC_INJ]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SNOC_APPEND; GSYM APPEND_ASSOC; APPEND]) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `stm:num`;
    `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,A word_loc)fmap`;
    `m:A word -> A word_loc`; `dm:A word->bool`; `b:bool`; `n:num`;
    `wl_Word (w:A word)`; `vs:(data_v#A word_loc)list`; `F`;
    `APPEND (l':byte list) (CONS (x:byte) rest)`] memory_rel_ByteArray_IMP) THEN
  ASM_REWRITE_TAC[injectivity "word_loc"; UNWIND_THM1] THEN
  DISCH_THEN(X_CHOOSE_THEN `w':A word` (X_CHOOSE_THEN `a':A word`
    (X_CHOOSE_THEN `x1:A word` (fun th -> let l = CONJUNCTS th in
       MAP_EVERY (fun i -> ASSUME_TAC (el i l)) [0;6;10;11])))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `w:A word = w'`)) THEN
  SUBGOAL_THEN `a':A word = a` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `get_real_simple_addr c st w = SOME (a':A word)` THEN
    ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`LENGTH (bytes:byte list)`; `new_b:byte`] o check
    (fun th -> is_forall(concl th) && is_forall(snd(dest_forall(concl th))))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[LUPDATE_LENGTH] THEN
  ABBREV_TAC `addr = word_add (word_add a bytes_in_word)
                       (word (LENGTH (l':byte list))):A word` THEN
  ABBREV_TAC `m' = (byte_align addr =+ wl_Word (set_byte addr new_b
                     (theWord ((m:A word->A word_loc) (byte_align addr))) be)) m` THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (new_b:byte) rest`; `l':byte list`;
    `m':A word->A word_loc`;
    `insert n (bvl_ByteArray F (APPEND l' (CONS (new_b:byte) rest)))
       (refs:(data_v bvl_ref)spt)`] o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[lookup_insert; insert_shadow] THEN
  SUBGOAL_THEN `write_bytearray (word_add (a:A word) bytes_in_word) (SNOC new_b bytes)
                  (m:A word->A word_loc) dm be =
                write_bytearray (word_add a bytes_in_word) bytes
                  (m':A word->A word_loc) dm be`
    SUBST1_TAC THENL
   [REWRITE_TAC[SNOC_APPEND] THEN
    MP_TAC(ISPECL [`bytes:byte list`; `[new_b:byte]`; `word_add a bytes_in_word:A word`;
      `m:A word->A word_loc`; `dm:A word->bool`; `be:bool`] write_bytearray_append) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[LENGTH] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
        not (is_forall(snd(dest_forall(concl th)))))) THEN
      ANTS_TAC THENL [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC;
                      MESON_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH (bytes:byte list)` o check (fun th ->
      is_forall(concl th) && not (is_forall(snd(dest_forall(concl th)))))) THEN
    ANTS_TAC THENL [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[write_bytearray_def; mem_load_byte_aux_def;
                    mem_store_byte_aux_def] THEN
    EXPAND_TAC "m'" THEN
    CASES_ON `(m:A word->A word_loc) (byte_align addr)` THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_DISTINCT; theWord_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN CASE_REWRITE_TAC[];
    REWRITE_TAC[SNOC_APPEND; GSYM APPEND_ASSOC; APPEND]]);;

(* HOL4 line 16298 *)
let memory_rel_write_bytearray = prove
 (`!c be stm sp st dm b n w vs a bytes bytes0 (m:A word -> A word_loc) refs.
     memory_rel c be stm refs sp st m dm
       (CONS (data_RefPtr b n,wl_Word (w:A word)) vs) /\
     lookup n refs = SOME (bvl_ByteArray F bytes0) /\
     LENGTH bytes = LENGTH bytes0 /\
     get_real_simple_addr c st w = SOME a /\ good_dimindex (:A) ==>
     memory_rel c be stm (insert n (bvl_ByteArray F bytes) refs) sp st
       (write_bytearray (word_add a bytes_in_word) bytes m dm be)
       dm (CONS (data_RefPtr b n,wl_Word w) vs)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `be:bool`; `stm:num`; `sp:num`;
    `st:(store_name,A word_loc)fmap`; `dm:A word->bool`; `b:bool`; `n:num`; `w:A word`;
    `vs:(data_v#A word_loc)list`; `a:A word`; `[]:byte list`; `bytes:byte list`;
    `bytes0:byte list`; `m:A word->A word_loc`; `refs:(data_v bvl_ref)spt`]
    memory_rel_write_bytearray_lemma) THEN
  ASM_REWRITE_TAC[APPEND_NIL]);;

(* HOL4 line 16301 *)
let memory_rel_space_max = prove
 (`!c be ts refs old_sp st (m:A word -> A word_loc) dm vars.
     memory_rel c be ts refs old_sp st m dm vars ==>
     ?next_free trig_gc sp.
       FLOOKUP st NextFree = SOME (wl_Word next_free) /\
       FLOOKUP st TriggerGC = SOME (wl_Word trig_gc) /\
       word_sub trig_gc next_free = word_mul bytes_in_word (word sp):A word /\
       old_sp <= sp /\
       memory_rel c be ts refs sp st m dm vars /\
       (good_dimindex (:A) ==> (dimindex (:A) DIV 8) * sp < dimword (:A))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[memory_rel_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[heap_in_memory_store_def] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "heap_in_memory_store"))
      (concl th))) THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`word_add curr (word_mul bytes_in_word (word a)):A word`;
    `word_add curr (word_mul bytes_in_word (word (a + sp))):A word`; `sp:num`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE;
    MAP_EVERY EXISTS_TAC [`heap:((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list`; `limit:num`; `a:num`; `sp:num`; `sp1:num`] THEN
    EXISTS_TAC `gens:gen_state` THEN ASM_REWRITE_TAC[LE_REFL];
    DISCH_TAC THEN
    UNDISCH_TAC `word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
                   (vars:(data_v#A word_loc)list)` THEN
    REWRITE_TAC[word_ml_inv_def; abs_ml_inv_def; unused_space_inv_def; heap_ok_def] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `sp * (dimindex(:A) DIV 8) <= limit * (dimindex(:A) DIV 8)` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(limit + 3) * dimindex (:A) DIV 8 + 1 < dimword (:A)` THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN ARITH_TAC]);;

let MP6AUX_MAXOUT_BITS_GE = prove
 (`!n r k i. bit i (maxout_bits n r k:A word) ==> k <= i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[maxout_bits_def; all_ones_def] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[BIT_WORD_SHL; BIT_WORD_0; BIT_WORD_SLICE] THEN ARITH_TAC);;

(* HOL4 line 16325 *)
let get_lowerbits_ptrbits = prove
 (`!c x y. get_lowerbits c (wl_Word (ptr_bits c x y)) =
           word_or (ptr_bits c x y) (word 1):A word`,
  REPEAT GEN_TAC THEN REWRITE_TAC[get_lowerbits_def] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_BITS; ADD_CLAUSES] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `bit i (ptr_bits c x y:A word)` THEN
  REWRITE_TAC[ptr_bits_def; BIT_WORD_OR; small_shift_length_def] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP maxout_bits_IMP
    (CONJ (ASSUME `i < dimindex(:A)`) th))) THEN ARITH_TAC);;

(* HOL4 line 16335 *)
let append_writes_def = cake_def
  `(append_writes c (ptr:A word) (hdr:A word) [] (l:A word_loc) = ARB) /\
   (append_writes c ptr (hdr:A word) (CONS x xs) l =
      CONS (wl_Word hdr) (CONS x
        (if xs = [] then [l] else
           let ptr = word_add ptr (word_shl (word 3) (shift_length c)) in
           CONS (wl_Word ptr) (append_writes c ptr hdr xs l))))`;;

(* HOL4 line 16345 *)
let append_writes_LENGTH = prove
 (`!c hdr l xs (ptr:A word).
     ~(xs = []) ==> LENGTH (append_writes c ptr hdr xs l) = 3 * LENGTH xs`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN GEN_TAC THEN
  REWRITE_TAC[append_writes_def; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[LENGTH] THEN ARITH_TAC);;

(* HOL4 line 16352 *)
let ptr_bits_or_1_add_1 = prove
 (`!c tag len.
     word_or (ptr_bits c tag len) (word 1) = word_add (ptr_bits c tag len) (word 1):A word`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_ADD_OR THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_1; BIT_WORD_0] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ptr_bits_def; BIT_WORD_OR] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP MP6AUX_MAXOUT_BITS_GE) THEN ARITH_TAC);;

(* HOL4 line 16363 *)
let all_ones_n2w = prove
 (`!l b. all_ones (l + b) b = word_shl (word (2 EXP l - 1)) b:A word`,
  REPEAT GEN_TAC THEN REWRITE_TAC[all_ones_def] THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `l = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_SHL_0];
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SLICE; BIT_WORD_SHL; BIT_WORD_NOT;
                BIT_WORD_0; MP6AUX_BIT_WORD; BIT_EXP_SUB1] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* HOL4 line 16373 *)
let ptr_bits_lemma = prove
 (`!(w:A word) conf.
     word_or (word_shl w (shift_length conf))
             (word_or (ptr_bits conf 0 2) (word 1)) =
     word_add (word_add (word_shl w (shift_length conf)) (ptr_bits conf 0 2)) (word 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM ptr_bits_or_1_add_1] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_ADD_OR THEN
  SUBGOAL_THEN `!i. i < dimindex(:A) /\
                    bit i (word_or (ptr_bits conf 0 2) (word 1):A word)
                    ==> i < shift_length conf` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN REWRITE_TAC[BIT_WORD_OR; BIT_WORD_1; ptr_bits_def] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP maxout_bits_IMP
        (CONJ (ASSUME `i < dimindex(:A)`) th)));
      FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP maxout_bits_IMP
        (CONJ (ASSUME `i < dimindex(:A)`) th)));
      ALL_TAC] THEN
    ASM_REWRITE_TAC[shift_length_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_SHL; BIT_WORD_0] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* HOL4 line 16387 *)
let encode_header_lemma = prove
 (`!c. 1 < data_to_word_config_len_size c /\
       data_to_word_config_len_size c + 5 < dimindex (:A) /\
       good_dimindex (:A)
       ==>
       decode_length c (make_header c (word 0) 2) = (word 2:A word) /\
       encode_header c 0 2 = SOME (make_header c (word 0:A word) 2)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `encode_header c 0 2 = SOME (make_header c (word 0:A word) 2)`
    ASSUME_TAC THENL
   [REWRITE_TAC[encode_header_def] THEN
    SUBGOAL_THEN `2 < 2 EXP data_to_word_config_len_size c` ASSUME_TAC THENL
     [MP_TAC(SPECL [`1`; `data_to_word_config_len_size c`] WORDSAUX_EXP2_LT) THEN
      ASM_REWRITE_TAC[EXP_1];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[LT_NZ; EXP_EQ_0; ARITH_EQ] THEN
    UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `0`; `2`; `make_header c (word 0:A word) 2`]
    encode_header_IMP) THEN
  ASM_SIMP_TAC[]);;

let MP6AUX_CONS_PTR = prove
 (`!c offset. good_dimindex(:A) /\ backend_common_word_shift (:A) <= shift_length c ==>
     make_cons_ptr c (word_mul bytes_in_word (word offset):A word) 0 2 =
     wl_Word (word_add (word_add (word_shl (word offset) (shift_length c))
                                 (ptr_bits c 0 2)) (word 1))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[make_cons_ptr_thm; bytes_in_word_mul_eq_shift] THEN
  REWRITE_TAC[WORD_SHL_COMPOSE; injectivity "word_loc"] THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= l ==> k + (l - k) = l`] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [WORD_OR_SYM] THEN
  REWRITE_TAC[ptr_bits_lemma]);;

let MP6AUX_GET_ADDR_PTR = prove
 (`!c n. get_addr c n (wl_Word (ptr_bits c 0 2)) =
         word_add (word_add (word_shl (word n) (shift_length c)) (ptr_bits c 0 2))
           (word 1):A word`,
  REWRITE_TAC[get_addr_def; get_lowerbits_ptrbits; ptr_bits_lemma]);;

(* HOL4 line 16400 *)
let append_writes_list_to_BlockReps = prove
 (`!c curr v.
   !xs ws x w offset init_ptr.
     LENGTH xs = LENGTH ws /\
     good_dimindex (:A) /\
     1 < data_to_word_config_len_size c /\
     data_to_word_config_len_size c + 5 < dimindex (:A) /\
     backend_common_word_shift (:A) <= shift_length c /\
     ALL2 (\v w. word_addr c v = w) (CONS x xs) (CONS w ws) /\
     wl_Word init_ptr = make_cons_ptr c (word_mul bytes_in_word (word offset:A word)) 0 2
     ==>
     misc_word_list (word_add curr (word_mul bytes_in_word (word offset:A word)))
       (append_writes c init_ptr (make_header c (word 0) 2) (CONS w ws)
          (word_addr c v)) =
     word_heap (word_add curr (word_mul bytes_in_word (word offset:A word)))
       (list_to_BlockReps c v offset (CONS x xs)) c`,
  REPLICATE_TAC 3 GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[LENGTH_EQ_NIL] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL2]) THEN
    MP_TAC(SPEC `c:data_to_word_config` encode_header_lemma) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[append_writes_def; list_to_BlockReps_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[BlockRep_def; word_heap_def; word_el_def; word_payload_def;
      cons_tag_def; WORD_SHL_0; LENGTH; MAP; LET_DEF; LET_END_DEF] THEN
    CASE_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `2 < 2 EXP (dimindex (:A) - 4)` ASSUME_TAC THENL
     [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; misc_word_list_def; SEP_CLAUSES];
    X_GEN_TAC `ws:(A word_loc)list` THEN REPEAT GEN_TAC THEN
    MP_TAC(ISPEC `ws:(A word_loc)list` list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `h':A word_loc` (X_CHOOSE_THEN `t':(A word_loc)list`
        SUBST1_TAC))) THEN
    REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; ALL2] THEN STRIP_TAC THEN
    MP_TAC(SPEC `c:data_to_word_config` encode_header_lemma) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `2 < 2 EXP (dimindex (:A) - 4)` ASSUME_TAC THENL
     [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    UNDISCH_TAC `wl_Word init_ptr =
      make_cons_ptr c (word_mul bytes_in_word (word offset)) 0 2:A word_loc` THEN
    ASM_SIMP_TAC[MP6AUX_CONS_PTR; injectivity "word_loc"] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `word_add (word_add (word_add (word_shl (word offset:A word)
         (shift_length c)) (ptr_bits c 0 2)) (word 1)) (word_shl (word 3) (shift_length c)) =
       word_add (word_add (word_shl (word (offset + 3)) (shift_length c))
         (ptr_bits c 0 2)) (word 1)` ASSUME_TAC THENL
     [REWRITE_TAC[WORD_MUL_LSL; WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t':(A word_loc)list`; `h:(A word_loc)heap_address`;
      `h':A word_loc`; `offset + 3`;
      `word_add (word_add (word_shl (word (offset + 3)) (shift_length c))
         (ptr_bits c 0 2)) (word 1):A word`] o check (is_forall o concl)) THEN
    ASM_SIMP_TAC[MP6AUX_CONS_PTR; ALL2] THEN DISCH_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [append_writes_def] THEN
    REWRITE_TAC[NOT_CONS_NIL; LET_DEF; LET_END_DEF] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [list_to_BlockReps_def] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[misc_word_list_def; word_heap_def; BlockRep_def; el_length_def;
      word_el_def; word_payload_def; MAP; LET_DEF; LET_END_DEF; cons_tag_def;
      WORD_SHL_0; word_addr_def; MP6AUX_GET_ADDR_PTR] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; SEP_CLAUSES] THEN
    SUBGOAL_THEN `word_add (word_add (word_add (word_add (curr:A word)
         (word_mul bytes_in_word (word offset))) bytes_in_word) bytes_in_word)
         bytes_in_word = word_add curr (word_mul bytes_in_word (word (offset + 3))) /\
       word_add (word_add curr (word_mul bytes_in_word (word offset)))
         (word_mul bytes_in_word (word 3)) =
       (word_add curr (word_mul bytes_in_word (word (offset + 3))):A word)`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[misc_word_list_def; SEP_CLAUSES] THEN
    CONV_TAC MP6AUX_STAR_AC_CONV]);;

(* HOL4 line 16441 *)
let bind_each_eq_tf = prove
 (`!k tf ts n i x.
     (!t. t IN FDOM tf ==> t < ts) /\ x < ts
     ==> FAPPLY (bind_each tf ts n i k) x = FAPPLY tf x`,
  INDUCT_TAC THEN REWRITE_TAC[bind_each_def; FAPPLY_FUPDATE_THM] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[ARITH_RULE `t < ts ==> t < ts + 1`]]);;

(* HOL4 line 16453 *)
let bind_each_FDOM = prove
 (`!n tf ts k i.
     FDOM (bind_each tf ts k i n) = FDOM tf UNION {x | ts <= x /\ x < ts + n}`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[bind_each_def; FDOM_FUPDATE] THEN
  REWRITE_TAC[EXTENSION; IN_INSERT; IN_UNION; IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(x:num) IN FDOM (tf:(num,num)fmap)` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* HOL4 line 16465 *)
let bind_each_eq_tf_FDOM = prove
 (`!k tf ts n i x.
     (!t. t IN FDOM tf ==> t < ts) /\ x < ts /\ x IN FDOM (bind_each tf ts n i k)
     ==> x IN FDOM tf`,
  REWRITE_TAC[bind_each_FDOM; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[ARITH_RULE `x < ts ==> ~(ts <= x)`]);;

(* HOL4 line 16473 *)
let bind_each_eq_lt_FAPPLY = prove
 (`!n tf ts k i x.
     FAPPLY (bind_each tf ts k i n) x < k
     ==> FAPPLY (bind_each tf ts k i n) x = FAPPLY tf x`,
  INDUCT_TAC THEN REWRITE_TAC[bind_each_def; FAPPLY_FUPDATE_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ARITH_TAC;
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* HOL4 line 16484 *)
let bind_each_eq_lt_FDOM = prove
 (`!n tf ts k i x.
     x IN FDOM (bind_each tf ts k i n) /\
     FAPPLY (bind_each tf ts k i n) x < k
     ==> x IN FDOM tf`,
  INDUCT_TAC THEN
  REWRITE_TAC[bind_each_def; FAPPLY_FUPDATE_THM; FDOM_FUPDATE; IN_INSERT] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ARITH_TAC;
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`tf:(num,num)fmap`; `ts + 1`; `k + i:num`;
                                  `i:num`; `x:num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;


