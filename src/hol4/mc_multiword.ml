(* ========================================================================= *)
(* mc_multiword: port of HOL4 examples/machine-code/multiword/              *)
(* mc_multiwordScript.sml (HOL4 library used by CakeML v3479): functions    *)
(* that resemble machine code (tail-recursive, over words and word lists)   *)
(* implementing the bignum operations of multiword.ml, and their            *)
(* correctness, up to the top-level entry point mc_iop_thm.                  *)
(*                                                                           *)
(* Vocabulary (as in multiword.ml): n2w = word, w2n = val, a + b and a - b  *)
(* on words = word_add, word_sub, && = word_and, ?? = word_xor, ~ = word_not, *)
(* <+ = word_ult, < on words = word_ilt, >>> = word_ushr, << = word_shl,    *)
(* w ' i = bit i w, ++ = APPEND, FRONT = BUTLAST, dimword(:N) as in words4.  *)
(* The constructors Add Sub Mul Div Mod Lt Dec of HOL4's mw_op are          *)
(* multiword_Add .. multiword_Dec (Eq is kept), see multiword.ml.           *)
(*                                                                           *)
(* Rendering of the definitions:                                             *)
(* - HOL4's tailrec_define NAME step (mc_tailrecLib) is LBIGAUX_tailrec_define *)
(*   below: NAME and NAME_pre are SHORT_TAILREC step and SHORT_TAILREC_PRE   *)
(*   step of tailrec.ml (bound as OCaml values NAME and NAME_pre), and the   *)
(*   theorems NAME_def and NAME_pre_def are HOL4's equations (details in    *)
(*   the comment before the tool).  HOL4's ML rebindings such as            *)
(*   val mc_add_loop_def = LIST_CONJ [...] are not reproduced: each NAME_def *)
(*   is the equation of NAME alone.                                          *)
(* - HOL4's let (a,b) = e in t is written match e with (a,b) -> t (CASE_TERM). *)
(*   When e is an explicit tuple (the swaps let (xs,ys) = (ys,xs)) CASE_TERM  *)
(*   substitutes it, so those equations show the swapped variables directly. *)
(* - The condition variable cond of HOL4 is cnd (cond is a set_sep constant), *)
(*   and l <> 0n is ~(l = 0).                                               *)
(* - mc_fac and mc_fac_pre (HOL4 tDefine, not tail-recursive) are cake_def_wf *)
(*   definitions with the measure FST, as in HOL4 (WF_REL_TAC, measure FST). *)
(* Theorems: the HOL4 theorems are proved under their HOL4 names in the     *)
(* final form HOL4 gives them (after its SPECL / SIMP_RULE post-processing); *)
(* where HOL4 first proves a general statement (extra prefix lists) that    *)
(* statement is LBIGAUX_NAME.  HOL4's mod is md (mod is a HOL Light        *)
(* constant).  Vacuous quantifiers of HOL4's statements are dropped         *)
(* (mc_div_sub_aux_thm: z_af' .. z_zf'; mc_div_loop_thm: ys1 c r1 r12).     *)
(* HOL4's local theorems single_mul_add_thm and single_mul_thm (whose names *)
(* are taken by multiword.ml) are LBIGAUX_SINGLE_MUL_ADD_00; mc_icmp_res and *)
(* mc_full_cmp (not used by mc_iop) and the decimal printing (commented out *)
(* in HOL4) are not ported.  Helper lemmas are named LBIGAUX_.               *)
(* ========================================================================= *)

needs "hol4/multiword.ml";;
needs "hol4/tailrec.ml";;

prioritize_num();;
type_invention_error := true;;
(* ------------------------------------------------------------------------- *)
(* HOL4's mc_tailrecLib.tailrec_define, as used by this file: for a step     *)
(* function  step : A -> (A + B) # bool  it defines NAME = SHORT_TAILREC     *)
(* step and NAME_pre = SHORT_TAILREC_PRE step (bound as OCaml values NAME    *)
(* and NAME_pre, as HOL4 stores them) and proves HOL4's equations NAME_def   *)
(* and NAME_pre_def: the body of the step with INL x leaves replaced by      *)
(* NAME x and INR y leaves by y (the cond lets removed), and for the         *)
(* precondition the leaves (INL x,c) replaced by NAME_pre x /\ c and         *)
(* (INR y,c) by c, the cond lets kept, the outermost cond being T.          *)
(* HOL4 names the condition variable cond; here it is cnd (cond is a        *)
(* constant of set_sep).                                                    *)
(* HOL4's let (a,b) = e in t is written match e with (a,b) -> t.             *)
(* ------------------------------------------------------------------------- *)

type lbig_ftree =
    Lbif of term * lbig_ftree * lbig_ftree
  | Lblet of term * term * lbig_ftree
  | Lbcase of term * term * term * lbig_ftree
  | Lbcond of term * lbig_ftree
  | Lbval of term;;

let lbig_cond_var = `cnd:bool`;;

let lbig_is_pair_case tm =
  is_comb tm && is_comb (rator tm) && is_const (rator (rator tm)) &&
  fst (dest_const (rator (rator tm))) = "pair_CASE" &&
  is_abs (rand tm) && is_abs (body (rand tm));;

let rec lbig_tm2ftree tm =
  if is_cond tm then
    let b,(x,y) = dest_cond tm in Lbif(b,lbig_tm2ftree x,lbig_tm2ftree y)
  else if is_let tm then
    (match dest_let tm with
       [v,e],t ->
         let t' = lbig_tm2ftree t in
         if v = lbig_cond_var then
           let c = try let l,r = dest_conj e in
                       if l = lbig_cond_var then r else e
                   with Failure _ -> e in
           Lbcond(c,t')
         else Lblet(v,e,t')
     | _ -> failwith "lbig_tm2ftree: let")
  else if lbig_is_pair_case tm then
    let e = rand (rator tm) and f = rand tm in
    let a,b1 = dest_abs f in
    let b,t = dest_abs b1 in
    Lbcase(e,a,b,lbig_tm2ftree t)
  else Lbval tm;;

let rec lbig_ftree2tm t =
  match t with
    Lbval tm -> tm
  | Lbif(b,x,y) -> mk_cond(b,lbig_ftree2tm x,lbig_ftree2tm y)
  | Lblet(v,e,x) -> mk_let([v,e],lbig_ftree2tm x)
  | Lbcase(e,a,b,x) ->
      mk_icomb(mk_icomb(mk_const("pair_CASE",[]),e),
               mk_abs(a,mk_abs(b,lbig_ftree2tm x)))
  | Lbcond(c,x) ->
      mk_let([lbig_cond_var,mk_conj(lbig_cond_var,c)],lbig_ftree2tm x);;

let rec lbig_leaves t f =
  match t with
    Lbval tm -> Lbval (f tm)
  | Lbif(b,x,y) -> Lbif(b,lbig_leaves x f,lbig_leaves y f)
  | Lblet(v,e,x) -> Lblet(v,e,lbig_leaves x f)
  | Lbcase(e,a,b,x) -> Lbcase(e,a,b,lbig_leaves x f)
  | Lbcond(c,x) -> Lbcond(c,lbig_leaves x f);;

let rec lbig_rm_conds t =
  match t with
    Lbcond(c,x) -> lbig_rm_conds x
  | Lbif(b,x,y) -> Lbif(b,lbig_rm_conds x,lbig_rm_conds y)
  | Lblet(v,e,x) -> Lblet(v,e,lbig_rm_conds x)
  | Lbcase(e,a,b,x) -> Lbcase(e,a,b,lbig_rm_conds x)
  | Lbval tm -> Lbval tm;;

let lbig_is_inl s =
  is_comb s && is_const (rator s) && fst (dest_const (rator s)) = "INL";;

(* split the conditionals and pair cases of the right hand side of the goal, *)
(* outermost first (only those whose subject has no bound variable), then   *)
(* simplify the sum injections and projections                              *)

let lbig_split_candidate fvs tm =
  let ok t = subset (frees t) fvs in
  if is_cond tm then
    let b = fst(dest_cond tm) in if ok b then Some(true,b) else None
  else if lbig_is_pair_case tm then
    let e = rand(rator tm) in
    if ok e && not (is_pair e) then Some(false,e) else None
  else None;;

let rec lbig_find_split fvs tm =
  match lbig_split_candidate fvs tm with
    Some x -> Some x
  | None ->
      if is_comb tm then
        (match lbig_find_split fvs (rator tm) with
           Some x -> Some x
         | None -> lbig_find_split fvs (rand tm))
      else if is_abs tm then lbig_find_split fvs (body tm)
      else None;;

let LBIG_SPLIT_TAC : tactic =
  fun (asl,w as gl) ->
    let fvs = itlist (union o frees o concl o snd) asl (frees w) in
    match lbig_find_split fvs (rand w) with
      Some(true,b) -> (ASM_CASES_TAC b THEN ASM_REWRITE_TAC[]) gl
    | Some(false,e) ->
        (MP_TAC(ISPEC e PAIR_SURJECTIVE) THEN
         REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
         let ty1,ty2 = match dest_type (type_of e) with
             "prod",[a;b] -> a,b | _ -> failwith "LBIG_SPLIT_TAC" in
         let v1 = variant fvs (mk_var("p1",ty1)) in
         let v2 = variant (v1::fvs) (mk_var("p2",ty2)) in
         MAP_EVERY X_GEN_TAC [v1;v2] THEN
         DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
         CASE_REWRITE_TAC[]) gl
    | None -> failwith "LBIG_SPLIT_TAC: nothing to split";;

let LBIG_TAILREC_FINISH_TAC =
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  REPEAT LBIG_SPLIT_TAC THEN
  ASM_REWRITE_TAC[ISL; OUTL; OUTR; FST; SND] THEN
  TRY (CONV_TAC TAUT);;

let LBIGAUX_tailrec_equations def_thm pre_thm step =
  let pat,bod = dest_gabs step in
  let f = lhs(concl def_thm) and fp = lhs(concl pre_thm) in
  let tr = lbig_tm2ftree bod in
  let def_body = lbig_ftree2tm (lbig_leaves (lbig_rm_conds tr)
    (fun tm -> let s,_ = dest_pair tm in
               if lbig_is_inl s then mk_comb(f,rand s) else rand s)) in
  let pre_body0 = lbig_ftree2tm (lbig_leaves tr
    (fun tm -> let s,c = dest_pair tm in
               if lbig_is_inl s then mk_conj(mk_comb(fp,rand s),c) else c)) in
  let pre_body1 = vsubst [`T`,lbig_cond_var] pre_body0 in
  let pre_body = rand(concl((REWRITE_CONV[GSYM CONJ_ASSOC] THENC
                             REWRITE_CONV[]) pre_body1)) in
  let def_goal = mk_eq(mk_comb(f,pat),def_body) in
  let pre_goal = mk_eq(mk_comb(fp,pat),pre_body) in
  let thm1 = ISPECL [step; pat] SHORT_TAILREC_THM in
  let def_res = prove(def_goal,
    GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [def_thm] THEN
    GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 thm1] THEN
    REWRITE_TAC[GSYM def_thm] THEN
    CONV_TAC(LAND_CONV(TOP_DEPTH_CONV GEN_BETA_CONV)) THEN
    LBIG_TAILREC_FINISH_TAC) in
  let pre_res = prove(pre_goal,
    GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [pre_thm] THEN
    GEN_REWRITE_TAC LAND_CONV [CONJUNCT2 thm1] THEN
    REWRITE_TAC[GSYM pre_thm; GSYM def_thm] THEN
    CONV_TAC(LAND_CONV(TOP_DEPTH_CONV GEN_BETA_CONV)) THEN
    LBIG_TAILREC_FINISH_TAC) in
  let rec pvars p =
    if is_pair p then let a,b = dest_pair p in pvars a @ pvars b else [p] in
  let vs = pvars pat in
  GENL vs def_res,GENL vs pre_res;;

let LBIGAUX_tailrec_define name step =
  let st = mk_icomb(mk_const("SHORT_TAILREC",[]),step) in
  let sp = mk_icomb(mk_const("SHORT_TAILREC_PRE",[]),step) in
  let def_thm = new_definition(mk_eq(mk_var(name,type_of st),st)) in
  let pre_thm = new_definition(mk_eq(mk_var(name ^ "_pre",type_of sp),sp)) in
  let def_res,pre_res = LBIGAUX_tailrec_equations def_thm pre_thm step in
  def_thm,pre_thm,def_res,pre_res;;
(* ------------------------------------------------------------------------- *)
(* compare                                                                   *)
(* ------------------------------------------------------------------------- *)

let mc_cmp,mc_cmp_pre,mc_cmp_def,mc_cmp_pre_def = LBIGAUX_tailrec_define "mc_cmp"
  `((\(l,r10,xs,ys).
      if r10 = word 0 then (INR (l,r10,xs,ys),T)
      else
        (let r10 = word_sub r10 (word 1) in
         let cnd = val r10 < LENGTH xs in
         let r8 = EL (val r10) xs in
         let cnd = (cnd /\ val r10 < LENGTH ys) in
         let r9 = EL (val r10) ys in
           if r8 = r9 then (INL (l - 1,r10,xs,ys),(cnd /\ ~(l = 0)))
           else if word_ult r8 r9
           then (let r10 = word 1 in (INR (l,r10,xs,ys),cnd))
           else (let r10 = word 2 in (INR (l,r10,xs,ys),cnd))))
   :num#N word#(N word)list#(N word)list ->
    ((num#N word#(N word)list#(N word)list) +
     (num#N word#(N word)list#(N word)list))#bool)`;;

let mc_compare,mc_compare_pre,mc_compare_def,mc_compare_pre_def =
  LBIGAUX_tailrec_define "mc_compare" (CASE_TERM
  `((\(l,r10,r11,xs,ys).
      if word_ult r10 r11 then (let r10 = word 1 in (INR (l,r10,xs,ys),T))
      else if word_ult r11 r10 then (let r10 = word 2 in (INR (l,r10,xs,ys),T))
      else
        (let cnd = (mc_cmp_pre (l - 1,r10,xs,ys) /\ ~(l = 0)) in
         match mc_cmp (l - 1,r10,xs,ys) with (l,r10,xs,ys) ->
           (INR (l,r10,xs,ys),cnd)))
   :num#N word#N word#(N word)list#(N word)list ->
    ((num#N word#N word#(N word)list#(N word)list) +
     (num#N word#(N word)list#(N word)list))#bool)`);;

let mc_header_def = new_definition
  `mc_header (s,xs:(N word)list) =
     word_add (word (LENGTH xs * 2)) (if s then word 1 else word 0):N word`;;

let mc_icompare,mc_icompare_pre,mc_icompare_def,mc_icompare_pre_def =
  LBIGAUX_tailrec_define "mc_icompare" (CASE_TERM
  `((\(l,r10,r11,xs,ys).
      if word_and r10 (word 1) = word 0 then
        if word_and r11 (word 1) = word 0 then
          (let r10 = word_ushr r10 1 in
           let r11 = word_ushr r11 1 in
           let cnd = mc_compare_pre (l,r10,r11,xs,ys) in
           match mc_compare (l,r10,r11,xs,ys) with (l,r10,xs,ys) ->
             (INR (l,r10,xs,ys),cnd))
        else (let r10 = word 2 in (INR (l,r10,xs,ys),T))
      else if word_and r11 (word 1) = word 0 then
        (let r10 = word 1 in (INR (l,r10,xs,ys),T))
      else
        (let r10 = word_ushr r10 1 in
         let r11 = word_ushr r11 1 in
         let cnd = mc_compare_pre (l,r10,r11,xs,ys) in
         match mc_compare (l,r10,r11,xs,ys) with (l,r10,xs,ys) ->
           if r10 = word 0 then (INR (l,r10,xs,ys),cnd)
           else (let r10 = word_xor r10 (word 3) in (INR (l,r10,xs,ys),cnd))))
   :num#N word#N word#(N word)list#(N word)list ->
    ((num#N word#N word#(N word)list#(N word)list) +
     (num#N word#(N word)list#(N word)list))#bool)`);;

let cmp2w_def = cake_def
  `(cmp2w NONE = word 0:N word) /\
   (cmp2w (SOME T) = word 1) /\
   (cmp2w (SOME F) = word 2)`;;
(* small helpers *)

let LBIGAUX_EL_LENGTH_CONS = prove
 (`!xs (x:A) ys. EL (LENGTH xs) (APPEND xs (CONS x ys)) = x`,
  SIMP_TAC[EL_LENGTH_APPEND; NULL; HD]);;

let LBIGAUX_VAL_WORD_LT = prove
 (`!n. n < dimword(:N) ==> val (word n:N word) = n`,
  SIMP_TAC[w2n_n2w; MOD_LT]);;

let LBIGAUX_WORD_SUC_NZ = prove
 (`!n. SUC n < dimword(:N) ==> ~(word (SUC n):N word = word 0)`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0] THEN SIMP_TAC[LBIGAUX_VAL_WORD_LT] THEN
  ARITH_TAC);;

let LBIGAUX_MW_CMP_SNOC = prove
 (`!(x:N word) y xs ys.
     mw_cmp (SNOC x xs) (SNOC y ys) =
     if x = y then mw_cmp xs ys else SOME (word_ult x y)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [mw_cmp_def] THEN
  REWRITE_TAC[NOT_SNOC_NIL; LAST_SNOC; FRONT_SNOC]);;

let LBIGAUX_MC_CMP = prove
 (`!xs ys xs1 ys1 l.
     LENGTH ys = LENGTH xs /\ LENGTH (xs:(N word)list) < dimword(:N) /\
     LENGTH xs <= l
     ==> mc_cmp_pre (l,word (LENGTH xs),APPEND xs xs1,APPEND ys ys1) /\
         ?l2. mc_cmp (l,word (LENGTH xs),APPEND xs xs1,APPEND ys ys1) =
                (l2,cmp2w (mw_cmp xs ys),APPEND xs xs1,APPEND ys ys1) /\
              l <= l2 + LENGTH xs`,
  MATCH_MP_TAC SNOC_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[mc_cmp_def; mc_cmp_pre_def] THEN
    ONCE_REWRITE_TAC[mw_cmp_def] THEN REWRITE_TAC[cmp2w_def; APPEND] THEN
    EXISTS_TAC `l:num` THEN REWRITE_TAC[ADD_CLAUSES; LE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `xs:(N word)list` THEN DISCH_TAC THEN X_GEN_TAC `x:N word` THEN
  X_GEN_TAC `zs:(N word)list` THEN
  MP_TAC(ISPEC `zs:(N word)list` SNOC_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_SNOC; LENGTH; ARITH_RULE `~(0 = SUC n)`; SUC_INJ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[mc_cmp_def; mc_cmp_pre_def] THEN
  ASM_SIMP_TAC[LBIGAUX_WORD_SUC_NZ; LBIGAUX_WORD_SUC_SUB1; LET_DEF; LET_END_DEF] THEN
  ASM_SIMP_TAC[LBIGAUX_VAL_WORD_LT; ARITH_RULE `SUC n < d ==> n < d`] THEN
  REWRITE_TAC[LBIGAUX_MW_CMP_SNOC] THEN
  REWRITE_TAC[SNOC_APPEND; GSYM APPEND_ASSOC; APPEND] THEN
  SUBGOAL_THEN `EL (LENGTH (xs:(N word)list)) (APPEND l' (CONS (x':N word) ys1)) = x'`
  SUBST1_TAC THENL
   [UNDISCH_TAC `LENGTH (l':(N word)list) = LENGTH (xs:(N word)list)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LBIGAUX_EL_LENGTH_CONS]; ALL_TAC] THEN
  REWRITE_TAC[LBIGAUX_EL_LENGTH_CONS; LENGTH_APPEND; LENGTH] THEN
  UNDISCH_TAC `LENGTH (l':(N word)list) = LENGTH (xs:(N word)list)` THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
  REWRITE_TAC[ARITH_RULE `n < n + SUC m`] THEN
  ASM_CASES_TAC `x:N word = x'` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    COND_CASES_TAC THEN ASM_REWRITE_TAC[cmp2w_def; ARITH_RULE `~(SUC n = 0)`] THEN
    EXISTS_TAC `l:num` THEN ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l':(N word)list`; `CONS (x':N word) xs1`;
    `CONS (x':N word) ys1`; `l - 1`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `l2:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let mc_cmp_thm = prove
 (`!xs ys l.
     LENGTH ys = LENGTH xs /\ LENGTH (xs:(N word)list) < dimword(:N) /\
     LENGTH xs <= l
     ==> mc_cmp_pre (l,word (LENGTH xs),xs,ys) /\
         ?l2. mc_cmp (l,word (LENGTH xs),xs,ys) = (l2,cmp2w (mw_cmp xs ys),xs,ys) /\
              l <= l2 + LENGTH xs`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`xs:(N word)list`; `ys:(N word)list`; `[]:(N word)list`;
                `[]:(N word)list`; `l:num`] LBIGAUX_MC_CMP) THEN
  ASM_REWRITE_TAC[APPEND_NIL]);;

let mc_compare_thm = prove
 (`!xs ys:(N word)list l.
     LENGTH xs < dimword(:N) /\ LENGTH ys < dimword(:N) /\ LENGTH xs + 1 <= l
     ==> ?l2. mc_compare_pre (l,word (LENGTH xs),word (LENGTH ys),xs,ys) /\
              mc_compare (l,word (LENGTH xs),word (LENGTH ys),xs,ys) =
                (l2,cmp2w (mw_compare xs ys),xs,ys) /\
              l <= l2 + LENGTH xs + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mc_compare_def; mc_compare_pre_def; LET_DEF; LET_END_DEF] THEN
  ASM_SIMP_TAC[word_lo_n2w; MOD_LT; mw_compare_def] THEN
  ASM_CASES_TAC `LENGTH (xs:(N word)list) < LENGTH (ys:(N word)list)` THEN
  ASM_REWRITE_TAC[] THENL
   [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[cmp2w_def] THEN
    EXISTS_TAC `l:num` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH (ys:(N word)list) < LENGTH (xs:(N word)list)` THEN
  ASM_REWRITE_TAC[] THENL
   [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[cmp2w_def] THEN
    EXISTS_TAC `l:num` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (ys:(N word)list) = LENGTH (xs:(N word)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`xs:(N word)list`; `ys:(N word)list`; `l - 1`] mc_cmp_thm) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `l2:num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  EXISTS_TAC `l2:num` THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let b2w_eq = prove
 (`!b. ((b2w b:N word = word 0) <=> ~b) /\ ((b2w b:N word = word 1) <=> b)`,
  GEN_TAC THEN REWRITE_TAC[multiword_b2w_def] THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[BITVAL_CLAUSES; LBIGAUX_WORD_NOT_ZERO_ONE] THEN
  MESON_TAC[LBIGAUX_WORD_NOT_ZERO_ONE]);;

let mc_header_AND_1 = prove
 (`!s xs:(N word)list. word_and (mc_header (s,xs)) (word 1) = b2w s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mc_header_def; WORD_AND_1_BITVAL; multiword_b2w_def] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD; BIT_LSB_WORD; ODD_ADD; ODD_MULT;
                  ARITH]);;

let mc_header_sign = prove
 (`!s xs:(N word)list. (word_and (mc_header (s,xs)) (word 1) = word 0) <=> ~s`,
  REWRITE_TAC[mc_header_AND_1; b2w_eq]);;

let dim63_IMP_dim64 = prove
 (`!n. n < dimword(:N) DIV 2 ==> n < dimword(:N)`,
  GEN_TAC THEN MP_TAC(SPECL [`dimword(:N)`; `2`] DIV_LE) THEN ARITH_TAC);;

let mc_length = prove
 (`!s xs:(N word)list.
     LENGTH xs < dimword(:N) DIV 2 ==> word_ushr (mc_header (s,xs)) 1 = word (LENGTH xs)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; EXP_1] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP dim63_IMP_dim64) THEN
  ASM_SIMP_TAC[LBIGAUX_VAL_WORD_LT] THEN
  REWRITE_TAC[mc_header_def] THEN
  SUBGOAL_THEN `LENGTH (xs:(N word)list) * 2 + 1 < dimword(:N)` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (xs:(N word)list) < dimword(:N) DIV 2` THEN
    REWRITE_TAC[LBIGAUX_DIMWORD_HALF] THEN SIMP_TAC[DIV_MULT; ARITH_RULE `~(2 = 0)`] THEN
    ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[LBIGAUX_VAL_WORD_LT; ARITH_RULE `n * 2 + 1 < d ==> n * 2 < d`] THEN
  MATCH_MP_TAC DIV_UNIQ THENL
   [EXISTS_TAC `1`; EXISTS_TAC `0`] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* addition                                                                  *)
(* ------------------------------------------------------------------------- *)

let single_add_word_def = cake_def
  `single_add_word (w1:N word) (w2:N word) (c:N word) =
     match single_add w1 w2 (~(c = word 0)) with (z,c) -> (z:N word, b2w c:N word)`;;

let single_add_word_thm = prove
 (`!(w1:N word) w2 c.
     single_add_word w1 w2 c =
     (FST (single_add w1 w2 (~(c = word 0))),
      b2w (SND (single_add w1 w2 (~(c = word 0)))):N word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[single_add_word_def] THEN
  PAIRARG_TAC THEN REWRITE_TAC[FST; SND]);;

let mc_add_loop2,mc_add_loop2_pre,mc_add_loop2_def,mc_add_loop2_pre_def =
  LBIGAUX_tailrec_define "mc_add_loop2" (CASE_TERM
  `((\(l,r1,r3,r8,r9,r10,xs,zs).
      if r1 = word 1 then
        (let r1 = word 0 in (INR (l,r1,r3,r8,r9,r10,xs,zs),T))
      else
        (let r1 = word_sub r1 (word 1) in
         let cnd = val r10 < LENGTH xs in
         let r8 = EL (val r10) xs in
         let cnd = (cnd /\ (~(r3 = word 0) ==> r3 = word 1)) in
         match single_add_word r8 r9 r3 with (r8,r3) ->
         let cnd = (cnd /\ val r10 < LENGTH zs) in
         let zs = LUPDATE r8 (val r10) zs in
         let r10 = word_add r10 (word 1) in
           (INL (l - 1,r1,r3,r8,r9,r10,xs,zs),(cnd /\ ~(l = 0)))))
   :num#N word#N word#N word#N word#N word#(N word)list#(N word)list ->
    ((num#N word#N word#N word#N word#N word#(N word)list#(N word)list) +
     (num#N word#N word#N word#N word#N word#(N word)list#(N word)list))#bool)`);;

let mc_add_loop1,mc_add_loop1_pre,mc_add_loop1_def,mc_add_loop1_pre_def =
  LBIGAUX_tailrec_define "mc_add_loop1" (CASE_TERM
  `((\(l,r1,r3,r8,r9,r10,xs,ys,zs).
      if r1 = word 1 then
        (let r1 = word 0 in (INR (l,r1,r3,r8,r9,r10,xs,ys,zs),T))
      else
        (let r1 = word_sub r1 (word 1) in
         let cnd = val r10 < LENGTH xs in
         let r8 = EL (val r10) xs in
         let cnd = (cnd /\ val r10 < LENGTH ys) in
         let r9 = EL (val r10) ys in
         let cnd = (cnd /\ (~(r3 = word 0) ==> r3 = word 1)) in
         match single_add_word r8 r9 r3 with (r8,r3) ->
         let cnd = (cnd /\ val r10 < LENGTH zs) in
         let zs = LUPDATE r8 (val r10) zs in
         let r10 = word_add r10 (word 1) in
           (INL (l - 1,r1,r3,r8,r9,r10,xs,ys,zs),(cnd /\ ~(l = 0)))))
   :num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list ->
    ((num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list) +
     (num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list))
    #bool)`);;
let mc_add_loop,mc_add_loop_pre,mc_add_loop_def,mc_add_loop_pre_def =
  LBIGAUX_tailrec_define "mc_add_loop" (CASE_TERM
  `((\(l,r1,r2,r8,r9,r10,xs,ys,zs).
      (let r1 = word_add r1 (word 1) in
       let r2 = word_add r2 (word 1) in
       let r3 = word 0 in
       let cnd = (mc_add_loop1_pre (l - 1,r1,r3,r8,r9,r10,xs,ys,zs) /\ ~(l = 0)) in
       match mc_add_loop1 (l - 1,r1,r3,r8,r9,r10,xs,ys,zs) with
         (l,r1,r3,r8,r9,r10,xs,ys,zs) ->
       let r1 = r2 in
       let r9 = word 0 in
       let cnd = (cnd /\ mc_add_loop2_pre (l - 1,r1,r3,r8,r9,r10,xs,zs) /\ ~(l = 0)) in
       match mc_add_loop2 (l - 1,r1,r3,r8,r9,r10,xs,zs) with
         (l,r1,r3,r8,r9,r10,xs,zs) ->
         if r3 = word 0 then
           (INR (l,r1,r2,r8,r9,r10,xs,ys,zs),cnd)
         else
           (let r8 = word 1 in
            let cnd = (cnd /\ val r10 < LENGTH zs) in
            let zs = LUPDATE r8 (val r10) zs in
            let r10 = word_add r10 (word 1) in
              (INR (l,r1,r2,r8,r9,r10,xs,ys,zs),cnd))))
   :num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list ->
    ((num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list) +
     (num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list))
    #bool)`);;

let mc_add,mc_add_pre,mc_add_def,mc_add_pre_def =
  LBIGAUX_tailrec_define "mc_add" (CASE_TERM
  `((\(l,r1,r2,r8,r9,r10,xs,ys,zs).
      (let r2 = word_sub r2 r1 in
       let cnd = mc_add_loop_pre (l,r1,r2,r8,r9,r10,xs,ys,zs) in
       match mc_add_loop (l,r1,r2,r8,r9,r10,xs,ys,zs) with
         (l,r1,r2,r8,r9,r10,xs,ys,zs) ->
         (INR (l,r1,r2,r8,r9,r10,xs,ys,zs),cnd)))
   :num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list ->
    ((num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list) +
     (num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list))
    #bool)`);;
let LBIGAUX_WORD_EQ_LT = prove
 (`!m n. m < dimword(:N) /\ n < dimword(:N) ==> (word m:N word = word n <=> m = n)`,
  SIMP_TAC[n2w_11; MOD_LT]);;

let LBIGAUX_WORD_ADD1_SUB1 = prove
 (`!n. word_sub (word (n + 1)) (word 1):N word = word n`,
  REWRITE_TAC[GSYM word_add_n2w; WORD_ADD_SUB]);;

let LBIGAUX_B2W_NZ = prove
 (`!c. ~(b2w c:N word = word 0) <=> c`,
  REWRITE_TAC[b2w_eq]);;

let LBIGAUX_B2W_01 = prove
 (`!c. ~(b2w c:N word = word 0) ==> b2w c:N word = word 1`,
  REWRITE_TAC[b2w_eq]);;

let LBIGAUX_SINGLE_ADD_WORD_B2W = prove
 (`!(x:N word) y c.
     single_add_word x y (b2w c) =
     (FST (single_add x y c), b2w (SND (single_add x y c)):N word)`,
  REWRITE_TAC[single_add_word_thm; LBIGAUX_B2W_NZ]);;

let LBIGAUX_MW_ADD_CONS = prove
 (`!(x:N word) xs y ys c.
     mw_add (CONS x xs) (CONS y ys) c =
     (CONS (FST (single_add x y c)) (FST (mw_add xs ys (SND (single_add x y c)))),
      SND (mw_add xs ys (SND (single_add x y c))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mw_add_def; HD; TL] THEN
  REPEAT PAIRARG_TAC THEN ASM_REWRITE_TAC[FST; SND]);;

let LBIG_CONS_CASES_TAC v h t =
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN h (X_CHOOSE_THEN t SUBST_ALL_TAC))
    (ISPEC v list_CASES);;

let mc_add_loop1_thm = prove
 (`!(xs:(N word)list) (ys:(N word)list) (zs:(N word)list) (xs1:(N word)list)
    (ys1:(N word)list) (zs1:(N word)list) (xs2:(N word)list) (ys2:(N word)list)
    (zs2:(N word)list) (r8:N word) (r9:N word) c l.
      LENGTH ys1 = LENGTH xs1 /\ LENGTH zs1 = LENGTH xs1 /\
      LENGTH ys = LENGTH xs /\ LENGTH zs = LENGTH xs /\
      LENGTH (APPEND xs1 xs) + 1 < dimword(:N) /\
      LENGTH xs <= l
      ==> ?r8' r9' l2.
        mc_add_loop1_pre (l,word (LENGTH xs + 1),b2w c,r8,r9,word (LENGTH xs1),
          APPEND (APPEND xs1 xs) xs2,APPEND (APPEND ys1 ys) ys2,
          APPEND (APPEND zs1 zs) zs2) /\
        mc_add_loop1 (l,word (LENGTH xs + 1),b2w c,r8,r9,word (LENGTH xs1),
          APPEND (APPEND xs1 xs) xs2,APPEND (APPEND ys1 ys) ys2,
          APPEND (APPEND zs1 zs) zs2) =
          (l2,word 0,b2w (SND (mw_add xs ys c)),r8',r9',
           word (LENGTH (APPEND xs1 xs)),
           APPEND (APPEND xs1 xs) xs2,APPEND (APPEND ys1 ys) ys2,
           APPEND (APPEND zs1 (FST (mw_add xs ys c))) zs2) /\
        l <= l2 + LENGTH xs`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[mc_add_loop1_def; mc_add_loop1_pre_def] THEN
    REWRITE_TAC[mw_add_def; APPEND_NIL; ADD_CLAUSES; LET_DEF; LET_END_DEF] THEN
    MAP_EVERY EXISTS_TAC [`r8:N word`; `r9:N word`; `l:num`] THEN REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `ys:(N word)list` THEN X_GEN_TAC `zs:(N word)list` THEN
  LBIG_CONS_CASES_TAC `ys:(N word)list` `y:N word` `ys':(N word)list` THEN
  LBIG_CONS_CASES_TAC `zs:(N word)list` `z:N word` `zs':(N word)list` THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH]) THEN
  SUBGOAL_THEN `SUC (SUC (LENGTH (t:(N word)list))) < dimword(:N) /\
                LENGTH (xs1:(N word)list) < dimword(:N)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(word (SUC (SUC (LENGTH (t:(N word)list)))):N word = word 1) /\
                val (word (LENGTH (xs1:(N word)list)):N word) = LENGTH xs1`
   STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LBIGAUX_WORD_EQ_LT; LBIGAUX_VAL_WORD_LT; ONE_LT_dimword] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(!(a:N word) b. EL (LENGTH (xs1:(N word)list)) (APPEND ys1 (CONS a b)) = a) /\
                (!(a:N word) b c. LUPDATE a (LENGTH (xs1:(N word)list)) (APPEND zs1 (CONS c b)) =
                                  APPEND zs1 (CONS a b))`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `LENGTH (ys1:(N word)list) = LENGTH (xs1:(N word)list)`;
      UNDISCH_TAC `LENGTH (zs1:(N word)list) = LENGTH (xs1:(N word)list)`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[LBIGAUX_EL_LENGTH_CONS; LUPDATE_LENGTH];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; LENGTH; GSYM ADD1] THEN
  ONCE_REWRITE_TAC[mc_add_loop1_def; mc_add_loop1_pre_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; LBIGAUX_WORD_SUC_SUB1; LBIGAUX_EL_LENGTH_CONS] THEN
  REWRITE_TAC[LBIGAUX_SINGLE_ADD_WORD_B2W] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[b2w_eq; LBIGAUX_B2W_01; word_add_n2w; GSYM ADD1; LBIGAUX_MW_ADD_CONS] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ys':(N word)list`; `zs':(N word)list`;
    `SNOC (h:N word) xs1`; `SNOC (y:N word) ys1`;
    `SNOC (FST (single_add (h:N word) y c)) zs1`; `xs2:(N word)list`;
    `ys2:(N word)list`; `zs2:(N word)list`; `FST (single_add (h:N word) y c)`;
    `y:N word`; `SND (single_add (h:N word) y c)`; `l - 1`]) THEN
  REWRITE_TAC[LENGTH_SNOC; SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH;
              GSYM ADD1; ADD_CLAUSES] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`r8':N word`; `r9':N word`; `l2:num`] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN ASM_ARITH_TAC);;

let mc_add_loop2_thm = prove
 (`!(xs:(N word)list) (zs:(N word)list) (xs1:(N word)list) (zs1:(N word)list)
    (xs2:(N word)list) (zs2:(N word)list) (r8:N word) c l.
      LENGTH zs1 = LENGTH xs1 /\ LENGTH zs = LENGTH xs /\
      LENGTH (APPEND xs1 xs) + 1 < dimword(:N) /\
      LENGTH xs <= l
      ==> ?r8' r9' l2.
        mc_add_loop2_pre (l,word (LENGTH xs + 1),b2w c,r8,word 0,word (LENGTH xs1),
          APPEND (APPEND xs1 xs) xs2,APPEND (APPEND zs1 zs) zs2) /\
        mc_add_loop2 (l,word (LENGTH xs + 1),b2w c,r8,word 0,word (LENGTH xs1),
          APPEND (APPEND xs1 xs) xs2,APPEND (APPEND zs1 zs) zs2) =
          (l2,word 0,b2w (SND (mw_add xs (MAP (\x. word 0) xs) c)),r8',r9',
           word (LENGTH (APPEND xs1 xs)),APPEND (APPEND xs1 xs) xs2,
           APPEND (APPEND zs1 (FST (mw_add xs (MAP (\x. word 0) xs) c))) zs2) /\
        l <= l2 + LENGTH xs`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[mc_add_loop2_def; mc_add_loop2_pre_def] THEN
    REWRITE_TAC[mw_add_def; MAP; APPEND_NIL; ADD_CLAUSES; LET_DEF; LET_END_DEF] THEN
    MAP_EVERY EXISTS_TAC [`r8:N word`; `word 0:N word`; `l:num`] THEN REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `zs:(N word)list` THEN
  LBIG_CONS_CASES_TAC `zs:(N word)list` `z:N word` `zs':(N word)list` THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH]) THEN
  SUBGOAL_THEN `SUC (SUC (LENGTH (t:(N word)list))) < dimword(:N) /\
                LENGTH (xs1:(N word)list) < dimword(:N)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(word (SUC (SUC (LENGTH (t:(N word)list)))):N word = word 1) /\
                val (word (LENGTH (xs1:(N word)list)):N word) = LENGTH xs1`
   STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LBIGAUX_WORD_EQ_LT; LBIGAUX_VAL_WORD_LT; ONE_LT_dimword] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!(a:N word) b c. LUPDATE a (LENGTH (xs1:(N word)list)) (APPEND zs1 (CONS c b)) =
                                 APPEND zs1 (CONS a b)`
   ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (zs1:(N word)list) = LENGTH (xs1:(N word)list)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LUPDATE_LENGTH];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; LENGTH; GSYM ADD1] THEN
  ONCE_REWRITE_TAC[mc_add_loop2_def; mc_add_loop2_pre_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; LBIGAUX_WORD_SUC_SUB1; LBIGAUX_EL_LENGTH_CONS] THEN
  REWRITE_TAC[LBIGAUX_SINGLE_ADD_WORD_B2W] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[b2w_eq; LBIGAUX_B2W_01; word_add_n2w; GSYM ADD1; LBIGAUX_MW_ADD_CONS; MAP] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`zs':(N word)list`;
    `SNOC (h:N word) xs1`; `SNOC (FST (single_add (h:N word) (word 0) c)) zs1`;
    `xs2:(N word)list`; `zs2:(N word)list`; `FST (single_add (h:N word) (word 0) c)`;
    `SND (single_add (h:N word) (word 0) c)`; `l - 1`]) THEN
  REWRITE_TAC[LENGTH_SNOC; SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH;
              GSYM ADD1; ADD_CLAUSES] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`r8':N word`; `r9':N word`; `l2:num`] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN ASM_ARITH_TAC);;

let LBIGAUX_WORD_ADD_SUB_L = prove
 (`!m n. word_sub (word (m + n)) (word m):N word = word n`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[GSYM word_add_n2w; WORD_ADD_SUB]);;

let LBIG_PAIR_TAC tm v1 v2 =
  MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [v1; v2] THEN DISCH_TAC;;

let mc_add_thm = prove
 (`!(xs:(N word)list) (ys:(N word)list) (zs:(N word)list) (zs2:(N word)list) l.
      LENGTH ys <= LENGTH xs /\ LENGTH zs = LENGTH (mw_addv xs ys F) /\
      LENGTH xs + 1 < dimword(:N) /\ LENGTH xs + 2 <= l
      ==> ?r1' r2' r8' r9' (r10':N word) l2.
            mc_add_pre (l,word (LENGTH ys),word (LENGTH xs),word 0,word 0,word 0,xs,ys,
                        APPEND zs zs2) /\
            mc_add (l,word (LENGTH ys),word (LENGTH xs),word 0,word 0,word 0,xs,ys,
                    APPEND zs zs2) =
              (l2,r1',r2',r8',r9',word (LENGTH (mw_addv xs ys F)),xs,ys,
               APPEND (mw_addv xs ys F) zs2) /\
            l <= l2 + LENGTH xs + 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP multiword_LESS_EQ_LENGTH) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`xs1:(N word)list`; `xs2:(N word)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  UNDISCH_TAC `LENGTH (zs:(N word)list) = LENGTH (mw_addv (APPEND xs1 xs2) (ys:(N word)list) F)` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP mw_addv_EQ_mw_add (SYM th)]) THEN
  LBIG_PAIR_TAC `mw_add (xs1:(N word)list) (ys:(N word)list) F` `qs1:(N word)list` `c1:bool` THEN
  LBIG_PAIR_TAC `mw_add (xs2:(N word)list) (MAP (\x. word 0:N word) xs2) c1`
    `qs2:(N word)list` `c2:bool` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH (qs1:(N word)list) = LENGTH (xs1:(N word)list) /\
                LENGTH (qs2:(N word)list) = LENGTH (xs2:(N word)list)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_mw_add]; ALL_TAC] THEN
  MP_TAC(ISPECL [`zs:(N word)list`; `LENGTH (xs1:(N word)list)`] multiword_LESS_EQ_LENGTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`zs1:(N word)list`; `zs5:(N word)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  MP_TAC(ISPECL [`zs5:(N word)list`; `LENGTH (xs2:(N word)list)`] multiword_LESS_EQ_LENGTH) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `LENGTH (APPEND zs1 zs5:(N word)list) =
       LENGTH (APPEND (APPEND qs1 qs2) (if c2 then [word 1:N word] else []))` THEN
    ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`zs3:(N word)list`; `zs4:(N word)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  UNDISCH_TAC `LENGTH (xs1:(N word)list) = LENGTH (ys:(N word)list)` THEN
  DISCH_THEN(fun th -> SUBST_ALL_TAC(SYM th) THEN ASSUME_TAC th) THEN
  REWRITE_TAC[mc_add_def; mc_add_pre_def; mc_add_loop_def; mc_add_loop_pre_def;
              LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[LENGTH_APPEND; LBIGAUX_WORD_ADD_SUB_L; word_add_n2w] THEN
  MP_TAC(SPECL [`xs1:(N word)list`; `ys:(N word)list`; `zs1:(N word)list`;
    `[]:(N word)list`; `[]:(N word)list`; `[]:(N word)list`; `xs2:(N word)list`;
    `[]:(N word)list`; `APPEND zs3 (APPEND zs4 zs2):(N word)list`; `word 0:N word`;
    `word 0:N word`; `F`; `l - 1`] mc_add_loop1_thm) THEN
  REWRITE_TAC[APPEND; APPEND_NIL; LENGTH; multiword_b2w_def; BITVAL_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r8a:N word` (X_CHOOSE_THEN `r9a:N word`
    (X_CHOOSE_THEN `l2a:num` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`xs2:(N word)list`; `zs3:(N word)list`; `xs1:(N word)list`;
    `qs1:(N word)list`; `[]:(N word)list`; `APPEND zs4 zs2:(N word)list`; `r8a:N word`;
    `c1:bool`; `l2a - 1`] mc_add_loop2_thm) THEN
  REWRITE_TAC[APPEND; APPEND_NIL; LENGTH; multiword_b2w_def; GSYM APPEND_ASSOC] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r8b:N word` (X_CHOOSE_THEN `r9b:N word`
    (X_CHOOSE_THEN `l2b:num` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (zs4:(N word)list) = (if c2 then 1 else 0)` MP_TAC THENL
   [UNDISCH_TAC `LENGTH (APPEND zs1 (APPEND zs3 zs4):(N word)list) =
       LENGTH (APPEND (APPEND qs1 qs2) (if c2 then [word 1:N word] else []))` THEN
    ASM_REWRITE_TAC[LENGTH_APPEND] THEN COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN
    ARITH_TAC; ALL_TAC] THEN
  LBIG_CONS_CASES_TAC `zs4:(N word)list` `z4:N word` `zs6:(N word)list` THEN
  ASM_CASES_TAC `c2:bool` THEN
  ASM_REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; ARITH_RULE `SUC n = 1 <=> n = 0`;
                  ARITH_RULE `~(0 = 1)`; LENGTH_EQ_NIL; BITVAL_CLAUSES;
                  LBIGAUX_WORD_NOT_ZERO_ONE; GSYM LBIGAUX_WORD_NOT_ZERO_ONE] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[APPEND] THEN CASE_REWRITE_TAC[] THENL
   [MAP_EVERY EXISTS_TAC [`word 0:N word`; `word (LENGTH (xs2:(N word)list) + 1):N word`;
      `r8b:N word`; `r9b:N word`; `l2b:num`] THEN
    REWRITE_TAC[LENGTH_APPEND; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val (word (LENGTH (APPEND (xs1:(N word)list) xs2)):N word) =
                LENGTH (APPEND (qs1:(N word)list) qs2)` SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `LENGTH (APPEND (xs1:(N word)list) xs2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[LENGTH_APPEND]]; ALL_TAC] THEN
  REWRITE_TAC[APPEND_ASSOC; LUPDATE_LENGTH] THEN
  MAP_EVERY EXISTS_TAC [`word 0:N word`; `word (LENGTH (xs2:(N word)list) + 1):N word`;
    `word 1:N word`; `r9b:N word`; `l2b:num`] THEN
  REWRITE_TAC[word_add_n2w; LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ADD1] THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* subtraction                                                               *)
(* ------------------------------------------------------------------------- *)

let single_sub_word_def = cake_def
  `single_sub_word (w1:N word) (w2:N word) (c:N word) =
     match single_sub w1 w2 (~(c = word 0)) with (z,c) -> (z:N word, b2w c:N word)`;;

let single_sub_word_thm = prove
 (`!(w1:N word) w2 c.
     single_sub_word w1 w2 c =
     (FST (single_sub w1 w2 (~(c = word 0))),
      b2w (SND (single_sub w1 w2 (~(c = word 0)))):N word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[single_sub_word_def] THEN
  PAIRARG_TAC THEN REWRITE_TAC[FST; SND]);;

let mc_sub_loop2,mc_sub_loop2_pre,mc_sub_loop2_def,mc_sub_loop2_pre_def =
  LBIGAUX_tailrec_define "mc_sub_loop2" (CASE_TERM
  `((\(l,r1,r3,r8,r9,r10,xs,zs).
      if r1 = word 1 then
        (let r1 = word 0 in (INR (l,r1,r3,r8,r9,r10,xs,zs),T))
      else
        (let r1 = word_sub r1 (word 1) in
         let cnd = val r10 < LENGTH xs in
         let r8 = EL (val r10) xs in
         let cnd = (cnd /\ (~(r3 = word 0) ==> r3 = word 1)) in
         match single_sub_word r8 r9 r3 with (r8,r3) ->
         let cnd = (cnd /\ val r10 < LENGTH zs) in
         let zs = LUPDATE r8 (val r10) zs in
         let r10 = word_add r10 (word 1) in
           (INL (l - 1,r1,r3,r8,r9,r10,xs,zs),(cnd /\ ~(l = 0)))))
   :num#N word#N word#N word#N word#N word#(N word)list#(N word)list ->
    ((num#N word#N word#N word#N word#N word#(N word)list#(N word)list) +
     (num#N word#N word#N word#N word#N word#(N word)list#(N word)list))#bool)`);;

let mc_sub_loop1,mc_sub_loop1_pre,mc_sub_loop1_def,mc_sub_loop1_pre_def =
  LBIGAUX_tailrec_define "mc_sub_loop1" (CASE_TERM
  `((\(l,r1,r3,r8,r9,r10,xs,ys,zs).
      if r1 = word 1 then
        (let r1 = word 0 in (INR (l,r1,r3,r8,r9,r10,xs,ys,zs),T))
      else
        (let r1 = word_sub r1 (word 1) in
         let cnd = val r10 < LENGTH xs in
         let r8 = EL (val r10) xs in
         let cnd = (cnd /\ val r10 < LENGTH ys) in
         let r9 = EL (val r10) ys in
         let cnd = (cnd /\ (~(r3 = word 0) ==> r3 = word 1)) in
         match single_sub_word r8 r9 r3 with (r8,r3) ->
         let cnd = (cnd /\ val r10 < LENGTH zs) in
         let zs = LUPDATE r8 (val r10) zs in
         let r10 = word_add r10 (word 1) in
           (INL (l - 1,r1,r3,r8,r9,r10,xs,ys,zs),(cnd /\ ~(l = 0)))))
   :num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list ->
    ((num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list) +
     (num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list))
    #bool)`);;

let mc_sub_loop,mc_sub_loop_pre,mc_sub_loop_def,mc_sub_loop_pre_def =
  LBIGAUX_tailrec_define "mc_sub_loop" (CASE_TERM
  `((\(l,r1,r2,r8,r9,r10,xs,ys,zs).
      (let r1 = word_add r1 (word 1) in
       let r2 = word_add r2 (word 1) in
       let r3 = word 1 in
       let r8 = word_sub r8 (word 0) in
       let cnd = (mc_sub_loop1_pre (l - 1,r1,r3,r8,r9,r10,xs,ys,zs) /\ ~(l = 0)) in
       match mc_sub_loop1 (l - 1,r1,r3,r8,r9,r10,xs,ys,zs) with
         (l,r1,r3,r8,r9,r10,xs,ys,zs) ->
       let r1 = r2 in
       let r9 = word 0 in
       let cnd = (cnd /\ mc_sub_loop2_pre (l - 1,r1,r3,r8,r9,r10,xs,zs) /\ ~(l = 0)) in
       match mc_sub_loop2 (l - 1,r1,r3,r8,r9,r10,xs,zs) with
         (l,r1,r3,r8,r9,r10,xs,zs) ->
         (INR (l,r1,r2,r8,r9,r10,xs,ys,zs),cnd)))
   :num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list ->
    ((num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list) +
     (num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list))
    #bool)`);;

let mc_fix,mc_fix_pre,mc_fix_def,mc_fix_pre_def =
  LBIGAUX_tailrec_define "mc_fix"
  `((\(l,r8,r10,zs).
      if r10 = word 0 then (INR (l,r8,r10,zs),T)
      else
        (let r10 = word_sub r10 (word 1) in
         let cnd = val r10 < LENGTH zs in
         let r8 = EL (val r10) zs in
           if r8 = word 0 then (INL (l - 1,r8,r10,zs),(cnd /\ ~(l = 0)))
           else (let r10 = word_add r10 (word 1) in (INR (l,r8,r10,zs),cnd))))
   :num#N word#N word#(N word)list ->
    ((num#N word#N word#(N word)list) + (num#N word#N word#(N word)list))#bool)`;;

let mc_sub,mc_sub_pre,mc_sub_def,mc_sub_pre_def =
  LBIGAUX_tailrec_define "mc_sub" (CASE_TERM
  `((\(l,r1,r2,r8,r9,r10,xs,ys,zs).
      (let r2 = word_sub r2 r1 in
       let cnd = mc_sub_loop_pre (l,r1,r2,r8,r9,r10,xs,ys,zs) in
       match mc_sub_loop (l,r1,r2,r8,r9,r10,xs,ys,zs) with
         (l,r1,r2,r8,r9,r10,xs,ys,zs) ->
       let cnd = (cnd /\ mc_fix_pre (l - 1,r8,r10,zs) /\ ~(l = 0)) in
       match mc_fix (l - 1,r8,r10,zs) with
         (l,r8,r10,zs) ->
         (INR (l,r1,r2,r8,r9,r10,xs,ys,zs),cnd)))
   :num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list ->
    ((num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list) +
     (num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list))
    #bool)`);;

let mw_fix_SNOC = prove
 (`!xs:(N word)list. mw_fix (SNOC (word 0) xs) = mw_fix xs`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [mw_fix_def] THEN
  REWRITE_TAC[NOT_SNOC_NIL; LAST_SNOC; FRONT_SNOC]);;

let LBIGAUX_MW_FIX_SNOC_NZ = prove
 (`!(x:N word) xs. ~(x = word 0) ==> mw_fix (SNOC x xs) = SNOC x xs`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [mw_fix_def] THEN
  ASM_REWRITE_TAC[NOT_SNOC_NIL; LAST_SNOC]);;

let mc_fix_thm = prove
 (`!(zs:(N word)list) (zs1:(N word)list) (r8:N word) l.
     LENGTH zs < dimword(:N) /\ LENGTH zs <= l
     ==> ?r8' l2.
           mc_fix_pre (l,r8,word (LENGTH zs),APPEND zs zs1) /\
           mc_fix (l,r8,word (LENGTH zs),APPEND zs zs1) =
             (l2,r8',word (LENGTH (mw_fix zs)),
              APPEND (APPEND (mw_fix zs) (REPLICATE (LENGTH zs - LENGTH (mw_fix zs)) (word 0)))
                     zs1) /\
           l <= l2 + LENGTH zs`,
  MATCH_MP_TAC SNOC_INDUCT THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[mc_fix_def; mc_fix_pre_def] THEN
    ONCE_REWRITE_TAC[mw_fix_def] THEN
    REWRITE_TAC[LENGTH; APPEND; SUB_REFL; REPLICATE] THEN
    MAP_EVERY EXISTS_TAC [`r8:N word`; `l:num`] THEN REWRITE_TAC[ADD_CLAUSES; LE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `zs:(N word)list` THEN DISCH_TAC THEN X_GEN_TAC `x:N word` THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH_SNOC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(word (SUC (LENGTH (zs:(N word)list))):N word = word 0) /\
                val (word (LENGTH (zs:(N word)list)):N word) = LENGTH zs`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LBIGAUX_WORD_SUC_NZ] THEN MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[mc_fix_def; mc_fix_pre_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; LBIGAUX_WORD_SUC_SUB1] THEN
  REWRITE_TAC[SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LBIGAUX_EL_LENGTH_CONS] THEN
  ASM_CASES_TAC `x:N word = word 0` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    ASM_SIMP_TAC[GSYM SNOC_APPEND; LBIGAUX_MW_FIX_SNOC_NZ; LENGTH_SNOC; SUB_REFL; REPLICATE;
                 APPEND_NIL; word_add_n2w; ADD1] THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH; SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; ADD1] THEN
    MAP_EVERY EXISTS_TAC [`x:N word`; `l:num`] THEN ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (word 0:N word) zs1`; `word 0:N word`; `l - 1`]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r8a:N word` (X_CHOOSE_THEN `l2:num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[GSYM SNOC_APPEND; mw_fix_SNOC] THEN
  MAP_EVERY EXISTS_TAC [`r8a:N word`; `l2:num`] THEN
  SUBGOAL_THEN `SUC (LENGTH (zs:(N word)list)) - LENGTH (mw_fix zs) =
                SUC (LENGTH zs - LENGTH (mw_fix zs))` SUBST1_TAC THENL
   [MP_TAC(SPEC `zs:(N word)list` LENGTH_mw_fix) THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REPLICATE_SNOC; SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND;
              LENGTH] THEN
  ASM_ARITH_TAC);;

let LBIGAUX_SINGLE_SUB_WORD_B2W = prove
 (`!(x:N word) y c.
     single_sub_word x y (b2w c) =
     (FST (single_sub x y c), b2w (SND (single_sub x y c)):N word)`,
  REWRITE_TAC[single_sub_word_thm; LBIGAUX_B2W_NZ]);;

let LBIGAUX_MW_SUB_CONS = prove
 (`!(x:N word) xs y ys c.
     mw_sub (CONS x xs) (CONS y ys) c =
     (CONS (FST (single_sub x y c)) (FST (mw_sub xs ys (SND (single_sub x y c)))),
      SND (mw_sub xs ys (SND (single_sub x y c))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mw_sub_def] THEN
  REPEAT PAIRARG_TAC THEN ASM_REWRITE_TAC[FST; SND]);;

let LBIGAUX_MW_SUB_CONS_NIL = prove
 (`!(x:N word) xs c.
     mw_sub (CONS x xs) [] c =
     (CONS (FST (single_sub x (word 0) c)) (FST (mw_sub xs [] (SND (single_sub x (word 0) c)))),
      SND (mw_sub xs [] (SND (single_sub x (word 0) c))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mw_sub_def] THEN
  REPEAT PAIRARG_TAC THEN ASM_REWRITE_TAC[FST; SND]);;

let mc_sub_loop1_thm = prove
 (`!(xs:(N word)list) (ys:(N word)list) (zs:(N word)list) (xs1:(N word)list)
    (ys1:(N word)list) (zs1:(N word)list) (xs2:(N word)list) (ys2:(N word)list)
    (zs2:(N word)list) (r8:N word) (r9:N word) c l.
      LENGTH ys1 = LENGTH xs1 /\ LENGTH zs1 = LENGTH xs1 /\
      LENGTH ys = LENGTH xs /\ LENGTH zs = LENGTH xs /\
      LENGTH (APPEND xs1 xs) + 1 < dimword(:N) /\
      LENGTH xs <= l
      ==> ?r8' r9' l2.
        mc_sub_loop1_pre (l,word (LENGTH xs + 1),b2w c,r8,r9,word (LENGTH xs1),
          APPEND (APPEND xs1 xs) xs2,APPEND (APPEND ys1 ys) ys2,
          APPEND (APPEND zs1 zs) zs2) /\
        mc_sub_loop1 (l,word (LENGTH xs + 1),b2w c,r8,r9,word (LENGTH xs1),
          APPEND (APPEND xs1 xs) xs2,APPEND (APPEND ys1 ys) ys2,
          APPEND (APPEND zs1 zs) zs2) =
          (l2,word 0,b2w (SND (mw_sub xs ys c)),r8',r9',
           word (LENGTH (APPEND xs1 xs)),
           APPEND (APPEND xs1 xs) xs2,APPEND (APPEND ys1 ys) ys2,
           APPEND (APPEND zs1 (FST (mw_sub xs ys c))) zs2) /\
        l <= l2 + LENGTH xs`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[mc_sub_loop1_def; mc_sub_loop1_pre_def] THEN
    REWRITE_TAC[mw_sub_def; APPEND_NIL; ADD_CLAUSES; LET_DEF; LET_END_DEF] THEN
    MAP_EVERY EXISTS_TAC [`r8:N word`; `r9:N word`; `l:num`] THEN REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `ys:(N word)list` THEN X_GEN_TAC `zs:(N word)list` THEN
  LBIG_CONS_CASES_TAC `ys:(N word)list` `y:N word` `ys':(N word)list` THEN
  LBIG_CONS_CASES_TAC `zs:(N word)list` `z:N word` `zs':(N word)list` THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH]) THEN
  SUBGOAL_THEN `SUC (SUC (LENGTH (t:(N word)list))) < dimword(:N) /\
                LENGTH (xs1:(N word)list) < dimword(:N)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(word (SUC (SUC (LENGTH (t:(N word)list)))):N word = word 1) /\
                val (word (LENGTH (xs1:(N word)list)):N word) = LENGTH xs1`
   STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LBIGAUX_WORD_EQ_LT; LBIGAUX_VAL_WORD_LT; ONE_LT_dimword] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(!(a:N word) b. EL (LENGTH (xs1:(N word)list)) (APPEND ys1 (CONS a b)) = a) /\
                (!(a:N word) b c. LUPDATE a (LENGTH (xs1:(N word)list)) (APPEND zs1 (CONS c b)) =
                                  APPEND zs1 (CONS a b))`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `LENGTH (ys1:(N word)list) = LENGTH (xs1:(N word)list)`;
      UNDISCH_TAC `LENGTH (zs1:(N word)list) = LENGTH (xs1:(N word)list)`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[LBIGAUX_EL_LENGTH_CONS; LUPDATE_LENGTH];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; LENGTH; GSYM ADD1] THEN
  ONCE_REWRITE_TAC[mc_sub_loop1_def; mc_sub_loop1_pre_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; LBIGAUX_WORD_SUC_SUB1; LBIGAUX_EL_LENGTH_CONS] THEN
  REWRITE_TAC[LBIGAUX_SINGLE_SUB_WORD_B2W] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[b2w_eq; LBIGAUX_B2W_01; word_add_n2w; GSYM ADD1; LBIGAUX_MW_SUB_CONS] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ys':(N word)list`; `zs':(N word)list`;
    `SNOC (h:N word) xs1`; `SNOC (y:N word) ys1`;
    `SNOC (FST (single_sub (h:N word) y c)) zs1`; `xs2:(N word)list`;
    `ys2:(N word)list`; `zs2:(N word)list`; `FST (single_sub (h:N word) y c)`;
    `y:N word`; `SND (single_sub (h:N word) y c)`; `l - 1`]) THEN
  REWRITE_TAC[LENGTH_SNOC; SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH;
              GSYM ADD1; ADD_CLAUSES] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`r8':N word`; `r9':N word`; `l2:num`] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN ASM_ARITH_TAC);;

let mc_sub_loop2_thm = prove
 (`!(xs:(N word)list) (zs:(N word)list) (xs1:(N word)list) (zs1:(N word)list)
    (xs2:(N word)list) (zs2:(N word)list) (r8:N word) c l.
      LENGTH zs1 = LENGTH xs1 /\ LENGTH zs = LENGTH xs /\
      LENGTH (APPEND xs1 xs) + 1 < dimword(:N) /\
      LENGTH xs <= l
      ==> ?r8' r9' l2.
        mc_sub_loop2_pre (l,word (LENGTH xs + 1),b2w c,r8,word 0,word (LENGTH xs1),
          APPEND (APPEND xs1 xs) xs2,APPEND (APPEND zs1 zs) zs2) /\
        mc_sub_loop2 (l,word (LENGTH xs + 1),b2w c,r8,word 0,word (LENGTH xs1),
          APPEND (APPEND xs1 xs) xs2,APPEND (APPEND zs1 zs) zs2) =
          (l2,word 0,b2w (SND (mw_sub xs [] c)),r8',r9',
           word (LENGTH (APPEND xs1 xs)),APPEND (APPEND xs1 xs) xs2,
           APPEND (APPEND zs1 (FST (mw_sub xs [] c))) zs2) /\
        l <= l2 + LENGTH xs`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[mc_sub_loop2_def; mc_sub_loop2_pre_def] THEN
    REWRITE_TAC[mw_sub_def; MAP; APPEND_NIL; ADD_CLAUSES; LET_DEF; LET_END_DEF] THEN
    MAP_EVERY EXISTS_TAC [`r8:N word`; `word 0:N word`; `l:num`] THEN REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `zs:(N word)list` THEN
  LBIG_CONS_CASES_TAC `zs:(N word)list` `z:N word` `zs':(N word)list` THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH]) THEN
  SUBGOAL_THEN `SUC (SUC (LENGTH (t:(N word)list))) < dimword(:N) /\
                LENGTH (xs1:(N word)list) < dimword(:N)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(word (SUC (SUC (LENGTH (t:(N word)list)))):N word = word 1) /\
                val (word (LENGTH (xs1:(N word)list)):N word) = LENGTH xs1`
   STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LBIGAUX_WORD_EQ_LT; LBIGAUX_VAL_WORD_LT; ONE_LT_dimword] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!(a:N word) b c. LUPDATE a (LENGTH (xs1:(N word)list)) (APPEND zs1 (CONS c b)) =
                                 APPEND zs1 (CONS a b)`
   ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (zs1:(N word)list) = LENGTH (xs1:(N word)list)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LUPDATE_LENGTH];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; LENGTH; GSYM ADD1] THEN
  ONCE_REWRITE_TAC[mc_sub_loop2_def; mc_sub_loop2_pre_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; LBIGAUX_WORD_SUC_SUB1; LBIGAUX_EL_LENGTH_CONS] THEN
  REWRITE_TAC[LBIGAUX_SINGLE_SUB_WORD_B2W] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[b2w_eq; LBIGAUX_B2W_01; word_add_n2w; GSYM ADD1; LBIGAUX_MW_SUB_CONS_NIL] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`zs':(N word)list`;
    `SNOC (h:N word) xs1`; `SNOC (FST (single_sub (h:N word) (word 0) c)) zs1`;
    `xs2:(N word)list`; `zs2:(N word)list`; `FST (single_sub (h:N word) (word 0) c)`;
    `SND (single_sub (h:N word) (word 0) c)`; `l - 1`]) THEN
  REWRITE_TAC[LENGTH_SNOC; SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH;
              GSYM ADD1; ADD_CLAUSES] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`r8':N word`; `r9':N word`; `l2:num`] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN ASM_ARITH_TAC);;

let mc_sub_thm = prove
 (`!(xs:(N word)list) (ys:(N word)list) (zs:(N word)list) (zs2:(N word)list) l.
      LENGTH ys <= LENGTH xs /\ LENGTH zs = LENGTH xs /\
      LENGTH xs + 1 < dimword(:N) /\ LENGTH xs + LENGTH xs + 3 <= l
      ==> ?r1' r2' r8' r9' (r10':N word) l2.
            mc_sub_pre (l,word (LENGTH ys),word (LENGTH xs),word 0,word 0,word 0,xs,ys,
                        APPEND zs zs2) /\
            mc_sub (l,word (LENGTH ys),word (LENGTH xs),word 0,word 0,word 0,xs,ys,
                    APPEND zs zs2) =
              (l2,r1',r2',r8',r9',word (LENGTH (mw_subv xs ys)),xs,ys,
               APPEND (APPEND (mw_subv xs ys)
                 (REPLICATE (LENGTH xs - LENGTH (mw_subv xs ys)) (word 0))) zs2) /\
            l <= l2 + LENGTH xs + LENGTH xs + 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP multiword_LESS_EQ_LENGTH) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`xs1:(N word)list`; `xs2:(N word)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  REWRITE_TAC[mw_subv_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP mw_sub_APPEND th]) THEN
  LBIG_PAIR_TAC `mw_sub (xs1:(N word)list) (ys:(N word)list) T` `qs1:(N word)list` `c1:bool` THEN
  LBIG_PAIR_TAC `mw_sub (xs2:(N word)list) [] c1` `qs2:(N word)list` `c2:bool` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (qs1:(N word)list) = LENGTH (xs1:(N word)list) /\
                LENGTH (qs2:(N word)list) = LENGTH (xs2:(N word)list)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_mw_sub]; ALL_TAC] THEN
  MP_TAC(ISPECL [`zs:(N word)list`; `LENGTH (xs1:(N word)list)`] multiword_LESS_EQ_LENGTH) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `LENGTH (zs:(N word)list) = LENGTH (APPEND (xs1:(N word)list) xs2)` THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`zs1:(N word)list`; `zs3:(N word)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `LENGTH (zs3:(N word)list) = LENGTH (xs2:(N word)list)` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (APPEND zs1 zs3:(N word)list) = LENGTH (APPEND (xs1:(N word)list) xs2)` THEN
    ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `LENGTH (xs1:(N word)list) = LENGTH (ys:(N word)list)` THEN
  DISCH_THEN(fun th -> SUBST_ALL_TAC(SYM th) THEN ASSUME_TAC(SYM th)) THEN
  REWRITE_TAC[mc_sub_def; mc_sub_pre_def; mc_sub_loop_def; mc_sub_loop_pre_def;
              LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[LENGTH_APPEND; LBIGAUX_WORD_ADD_SUB_L; word_add_n2w; WORD_SUB_0] THEN
  MP_TAC(SPECL [`xs1:(N word)list`; `ys:(N word)list`; `zs1:(N word)list`;
    `[]:(N word)list`; `[]:(N word)list`; `[]:(N word)list`; `xs2:(N word)list`;
    `[]:(N word)list`; `APPEND zs3 zs2:(N word)list`; `word 0:N word`;
    `word 0:N word`; `T`; `l - 1`] mc_sub_loop1_thm) THEN
  REWRITE_TAC[APPEND; APPEND_NIL; LENGTH; multiword_b2w_def; BITVAL_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r8a:N word` (X_CHOOSE_THEN `r9a:N word`
    (X_CHOOSE_THEN `l2a:num` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`xs2:(N word)list`; `zs3:(N word)list`; `xs1:(N word)list`;
    `qs1:(N word)list`; `[]:(N word)list`; `zs2:(N word)list`; `r8a:N word`;
    `c1:bool`; `l2a - 1`] mc_sub_loop2_thm) THEN
  REWRITE_TAC[APPEND; APPEND_NIL; LENGTH; multiword_b2w_def; GSYM APPEND_ASSOC] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r8b:N word` (X_CHOOSE_THEN `r9b:N word`
    (X_CHOOSE_THEN `l2b:num` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`APPEND (qs1:(N word)list) qs2`; `zs2:(N word)list`; `r8b:N word`;
    `l2b - 1`] mc_fix_thm) THEN
  REWRITE_TAC[LENGTH_APPEND; GSYM APPEND_ASSOC] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r8c:N word` (X_CHOOSE_THEN `l2c:num` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`word 0:N word`; `word (LENGTH (xs2:(N word)list) + 1):N word`;
    `r8c:N word`; `r9b:N word`; `l2c:num`] THEN
  REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* integer addition                                                          *)
(* ------------------------------------------------------------------------- *)

let mc_iadd1,mc_iadd1_pre,mc_iadd1_def,mc_iadd1_pre_def =
  LBIGAUX_tailrec_define "mc_iadd1" (CASE_TERM
  `((\(r1,r2,xs,ys).
      (let r0 = word 0 in
         if word_ult r1 r2 then
           (match (ys,xs) with (xs,ys) ->
            let r0 = word 1 in
              (INR (r1,r2,r0,xs,ys),T))
         else
           (let r8 = r1 in
            let r1 = r2 in
            let r2 = r8 in
              (INR (r1,r2,r0,xs,ys),T))))
   :N word#N word#(N word)list#(N word)list ->
    ((N word#N word#(N word)list#(N word)list) +
     (N word#N word#N word#(N word)list#(N word)list))#bool)`);;

let mc_iadd2,mc_iadd2_pre,mc_iadd2_def,mc_iadd2_pre_def =
  LBIGAUX_tailrec_define "mc_iadd2" (CASE_TERM
  `((\(r1,r2,r10,r12,xs,ys).
      (let r0 = word 0 in
         if r10 = word 1 then
           (match (ys,xs) with (xs,ys) ->
            let r12 = word_xor r12 (word 1) in
            let r0 = word 1 in
              (INR (r1,r2,r0,r12,xs,ys),T))
         else
           (let r8 = r1 in
            let r1 = r2 in
            let r2 = r8 in
              (INR (r1,r2,r0,r12,xs,ys),T))))
   :N word#N word#N word#N word#(N word)list#(N word)list ->
    ((N word#N word#N word#N word#(N word)list#(N word)list) +
     (N word#N word#N word#N word#(N word)list#(N word)list))#bool)`);;

let mc_iadd3,mc_iadd3_pre,mc_iadd3_def,mc_iadd3_pre_def =
  LBIGAUX_tailrec_define "mc_iadd3" (CASE_TERM
  `((\(r0,xs,ys).
      if r0 = word 0 then (INR (xs,ys),T)
      else (match (ys,xs) with (xs,ys) -> (INR (xs,ys),T)))
   :N word#(N word)list#(N word)list ->
    ((N word#(N word)list#(N word)list) + ((N word)list#(N word)list))#bool)`);;

let mc_iadd,mc_iadd_pre,mc_iadd_def,mc_iadd_pre_def =
  LBIGAUX_tailrec_define "mc_iadd" (CASE_TERM
  `((\(l,r1,r2,xs,ys,zs).
      (let r10 = r1 in
       let r10 = word_and r10 (word 1) in
       let r11 = r2 in
       let r11 = word_and r11 (word 1) in
         if r10 = r11 then
           (let r1 = word_ushr r1 1 in
            let r2 = word_ushr r2 1 in
            match mc_iadd1 (r1,r2,xs,ys) with (r1,r2,r0,xs,ys) ->
            let r8 = word 0 in
            let r9 = r8 in
            let r10 = r8 in
            let cnd = mc_add_pre (l,r1,r2,r8,r9,r10,xs,ys,zs) in
            match mc_add (l,r1,r2,r8,r9,r10,xs,ys,zs) with
              (l,r1,r2,r8,r9,r10,xs,ys,zs) ->
            match mc_iadd3 (r0,xs,ys) with (xs,ys) ->
            let r10 = word_shl r10 1 in
            let r10 = word_add r10 r11 in
              (INR (l,r10,xs,ys,zs),cnd))
         else
           (let r12 = r10 in
            let r10 = r1 in
            let r10 = word_ushr r10 1 in
            let r11 = r2 in
            let r11 = word_ushr r11 1 in
            let cnd = mc_compare_pre (l,r10,r11,xs,ys) in
            match mc_compare (l,r10,r11,xs,ys) with (l,r10,xs,ys) ->
              if r10 = word 0 then (INR (l,r10,xs,ys,zs),cnd)
              else
                (match mc_iadd2 (r1,r2,r10,r12,xs,ys) with (r1,r2,r0,r12,xs,ys) ->
                 let r8 = word 0 in
                 let r9 = r8 in
                 let r10 = r8 in
                 let r1 = word_ushr r1 1 in
                 let r2 = word_ushr r2 1 in
                 let cnd = (cnd /\ mc_sub_pre (l,r1,r2,r8,r9,r10,xs,ys,zs)) in
                 match mc_sub (l,r1,r2,r8,r9,r10,xs,ys,zs) with
                   (l,r1,r2,r8,r9,r10,xs,ys,zs) ->
                 match mc_iadd3 (r0,xs,ys) with (xs,ys) ->
                 let r10 = word_shl r10 1 in
                 let r10 = word_add r10 r12 in
                   (INR (l,r10,xs,ys,zs),cnd)))))
   :num#N word#N word#(N word)list#(N word)list#(N word)list ->
    ((num#N word#N word#(N word)list#(N word)list#(N word)list) +
     (num#N word#(N word)list#(N word)list#(N word)list))#bool)`);;

let mc_header_EQ = prove
 (`!s t xs ys:(N word)list.
     (word_and (mc_header (s,xs)) (word 1) = word_and (mc_header (t,ys)) (word 1)) <=>
     (s <=> t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mc_header_AND_1; multiword_b2w_def] THEN
  BOOL_CASES_TAC `s:bool` THEN BOOL_CASES_TAC `t:bool` THEN
  REWRITE_TAC[BITVAL_CLAUSES; LBIGAUX_WORD_NOT_ZERO_ONE; GSYM LBIGAUX_WORD_NOT_ZERO_ONE]);;

let b2w_NOT = prove
 (`!s. word_xor (b2w s) (word 1) = b2w (~s):N word`,
  GEN_TAC THEN REWRITE_TAC[multiword_b2w_def] THEN BOOL_CASES_TAC `s:bool` THEN
  REWRITE_TAC[BITVAL_CLAUSES; WORD_XOR_REFL; WORD_XOR_0]);;

let LBIGAUX_SHL1_ADD_B2W = prove
 (`!n s (xs:(N word)list).
     LENGTH xs = n ==> word_add (word_shl (word n) 1) (b2w s) = mc_header (s,xs)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[mc_header_def; WORD_MUL_LSL; word_mul_n2w; EXP_1; multiword_b2w_def] THEN
  BOOL_CASES_TAC `s:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  REWRITE_TAC[MULT_SYM]);;

let LBIGAUX_IADD_ADD = prove
 (`!(xs:(N word)list) (ys:(N word)list) (zs:(N word)list) l.
     LENGTH ys <= LENGTH xs /\ LENGTH xs + LENGTH ys <= LENGTH zs /\
     LENGTH xs + 1 < dimword(:N) /\ LENGTH xs + 2 <= l
     ==> ?zs1 r1 r2 r8 r9 l2.
           mc_add_pre (l,word (LENGTH ys),word (LENGTH xs),word 0,word 0,word 0,xs,ys,zs) /\
           mc_add (l,word (LENGTH ys),word (LENGTH xs),word 0,word 0,word 0,xs,ys,zs) =
             (l2,r1,r2,r8,r9,word (LENGTH (mw_addv xs ys F)),xs,ys,
              APPEND (mw_addv xs ys F) zs1) /\
           LENGTH (APPEND (mw_addv xs ys F) zs1) = LENGTH zs /\
           l <= l2 + LENGTH xs + 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`zs:(N word)list`; `LENGTH (mw_addv (xs:(N word)list) ys F)`]
    multiword_LESS_EQ_LENGTH) THEN
  ANTS_TAC THENL
   [MP_TAC(SPECL [`xs:(N word)list`; `ys:(N word)list`] LENGTH_mw_addv) THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`zs0:(N word)list`; `zs2:(N word)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  MP_TAC(SPECL [`xs:(N word)list`; `ys:(N word)list`; `zs0:(N word)list`;
    `zs2:(N word)list`; `l:num`] mc_add_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`zs2:(N word)list`; `r1':N word`; `r2':N word`; `r8':N word`;
    `r9':N word`; `l2:num`] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND]);;

let LBIGAUX_IADD_SUB = prove
 (`!(xs:(N word)list) (ys:(N word)list) (zs:(N word)list) l.
     LENGTH ys <= LENGTH xs /\ LENGTH xs <= LENGTH zs /\
     LENGTH xs + 1 < dimword(:N) /\ LENGTH xs + LENGTH xs + 3 <= l
     ==> ?zs1 r1 r2 r8 r9 l2.
           mc_sub_pre (l,word (LENGTH ys),word (LENGTH xs),word 0,word 0,word 0,xs,ys,zs) /\
           mc_sub (l,word (LENGTH ys),word (LENGTH xs),word 0,word 0,word 0,xs,ys,zs) =
             (l2,r1,r2,r8,r9,word (LENGTH (mw_subv xs ys)),xs,ys,
              APPEND (mw_subv xs ys) zs1) /\
           LENGTH (APPEND (mw_subv xs ys) zs1) = LENGTH zs /\
           l <= l2 + LENGTH xs + LENGTH xs + 3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`zs:(N word)list`; `LENGTH (xs:(N word)list)`]
    multiword_LESS_EQ_LENGTH) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`zs0:(N word)list`; `zs2:(N word)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  MP_TAC(SPECL [`xs:(N word)list`; `ys:(N word)list`; `zs0:(N word)list`;
    `zs2:(N word)list`; `l:num`] mc_sub_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`APPEND (REPLICATE (LENGTH (xs:(N word)list) - LENGTH (mw_subv xs ys)) (word 0:N word))
       zs2`;
    `r1':N word`; `r2':N word`; `r8':N word`; `r9':N word`; `l2:num`] THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC; LENGTH_APPEND; LENGTH_REPLICATE] THEN
  MP_TAC(SPECL [`xs:(N word)list`; `ys:(N word)list`] LENGTH_mw_subv) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let LBIGAUX_DIV2_LT = prove
 (`!n. n < dimword(:N) DIV 2 ==> n + 1 < dimword(:N)`,
  GEN_TAC THEN REWRITE_TAC[LBIGAUX_DIMWORD_HALF] THEN
  SIMP_TAC[DIV_MULT; ARITH_RULE `~(2 = 0)`] THEN ARITH_TAC);;

let LBIGAUX_SHL1_HEADER = prove
 (`!s (xs:(N word)list).
     word_add (word_shl (word (LENGTH xs)) 1) (b2w s) = mc_header (s,xs)`,
  MESON_TAC[LBIGAUX_SHL1_ADD_B2W]);;

let LBIGAUX_WORD_2_NE_1 = prove
 (`~(word 2:N word = word 1)`,
  REWRITE_TAC[n2w_11] THEN MP_TAC ONE_LT_dimword THEN
  SIMP_TAC[MOD_LT] THEN DISCH_TAC THEN
  ASM_CASES_TAC `dimword(:N) = 2` THEN ASM_REWRITE_TAC[] THENL
   [CONV_TAC NUM_REDUCE_CONV;
    SUBGOAL_THEN `2 < dimword(:N)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT]] THEN ARITH_TAC]);;

let LBIGAUX_WORD_2_NZ = prove
 (`2 < dimword(:N) ==> ~(word 2:N word = word 0)`,
  SIMP_TAC[n2w_11; MOD_LT; ZERO_LT_dimword] THEN ARITH_TAC);;


let mc_iadd_thm = prove
 (`!s t (xs:(N word)list) (ys:(N word)list) (zs:(N word)list) l.
     LENGTH xs < dimword (:N) DIV 2 /\ LENGTH ys < dimword (:N) DIV 2 /\
     LENGTH xs + LENGTH ys <= LENGTH zs /\ mw_ok xs /\ mw_ok ys /\
     4 * LENGTH xs + 4 * LENGTH ys + 4 <= l
     ==> ?zs1 l2.
           mc_iadd_pre (l,mc_header (s,xs),mc_header (t,ys),xs,ys,zs) /\
           mc_iadd (l,mc_header (s,xs),mc_header (t,ys),xs,ys,zs) =
             (l2,mc_header (mwi_add (s,xs) (t,ys)),xs,ys,
              APPEND (SND (mwi_add (s,xs) (t,ys))) zs1) /\
           LENGTH (APPEND (SND (mwi_add (s,xs) (t,ys))) zs1) = LENGTH zs /\
           l <= l2 + 4 * LENGTH xs + 4 * LENGTH ys + 4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mc_iadd_def; mc_iadd_pre_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[mc_header_EQ; mwi_add_def] THEN ASM_SIMP_TAC[mc_length] THEN
  ASM_CASES_TAC `s <=> (t:bool)` THEN ASM_REWRITE_TAC[] THENL
   [(SUBGOAL_THEN `LENGTH (xs:(N word)list) < dimword(:N) /\ LENGTH (ys:(N word)list) < dimword(:N)`
        STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[dim63_IMP_dim64]; ALL_TAC] THEN
      REWRITE_TAC[mc_iadd1_def; LET_DEF; LET_END_DEF; word_lo_n2w] THEN ASM_SIMP_TAC[MOD_LT] THEN
      ASM_CASES_TAC `LENGTH (ys:(N word)list) <= LENGTH (xs:(N word)list)` THEN
      ASM_REWRITE_TAC[GSYM NOT_LE] THEN CASE_REWRITE_TAC[]) THENL
    [(MP_TAC(SPECL [`xs:(N word)list`; `ys:(N word)list`; `zs:(N word)list`; `l:num`]
         LBIGAUX_IADD_ADD) THEN
       ANTS_TAC THENL
        [ASM_SIMP_TAC[LBIGAUX_DIV2_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
       REWRITE_TAC[mc_iadd3_def; mc_header_AND_1] THEN CASE_REWRITE_TAC[] THEN
       EXISTS_TAC `zs1:(N word)list` THEN EXISTS_TAC `l2:num` THEN
       ASM_REWRITE_TAC[LBIGAUX_SHL1_HEADER] THEN ASM_ARITH_TAC);
     (MP_TAC(SPECL [`ys:(N word)list`; `xs:(N word)list`; `zs:(N word)list`; `l:num`]
         LBIGAUX_IADD_ADD) THEN
       ANTS_TAC THENL
        [ASM_SIMP_TAC[LBIGAUX_DIV2_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
       REWRITE_TAC[mc_iadd3_def; mc_header_AND_1; GSYM LBIGAUX_WORD_NOT_ZERO_ONE] THEN
       CASE_REWRITE_TAC[] THEN
       EXISTS_TAC `zs1:(N word)list` THEN EXISTS_TAC `l2:num` THEN
       ASM_REWRITE_TAC[LBIGAUX_SHL1_HEADER] THEN ASM_ARITH_TAC)];
    (SUBGOAL_THEN `LENGTH (xs:(N word)list) < dimword(:N) /\ LENGTH (ys:(N word)list) < dimword(:N)`
        STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[dim63_IMP_dim64]; ALL_TAC] THEN
      MP_TAC(SPECL [`xs:(N word)list`; `ys:(N word)list`; `l:num`] mc_compare_thm) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `l1:num` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[mw_compare_thm] THEN
      ASM_CASES_TAC `mw2n (xs:(N word)list) = mw2n (ys:(N word)list)` THEN
      ASM_REWRITE_TAC[cmp2w_def] THENL
       [EXISTS_TAC `zs:(N word)list` THEN EXISTS_TAC `l1:num` THEN
        REWRITE_TAC[mc_header_def; LENGTH; MULT_CLAUSES; WORD_ADD_0; APPEND] THEN
        ASM_ARITH_TAC; ALL_TAC]) THEN
    (ASM_CASES_TAC `mw2n (xs:(N word)list) < mw2n (ys:(N word)list)` THEN
      ASM_REWRITE_TAC[cmp2w_def; GSYM LBIGAUX_WORD_NOT_ZERO_ONE] THEN
      REWRITE_TAC[mc_iadd2_def; LET_DEF; LET_END_DEF; mc_header_AND_1] THEN
      ASM_REWRITE_TAC[LBIGAUX_WORD_2_NE_1; GSYM NOT_LT]) THENL
    [(CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[mc_length] THEN
       SUBGOAL_THEN `LENGTH (xs:(N word)list) <= LENGTH (ys:(N word)list)` ASSUME_TAC THENL
        [ASM_MESON_TAC[mw2n_LESS; LT_IMP_LE]; ALL_TAC] THEN
       MP_TAC(SPECL [`ys:(N word)list`; `xs:(N word)list`; `zs:(N word)list`; `l1:num`]
         LBIGAUX_IADD_SUB) THEN
       ANTS_TAC THENL
        [ASM_SIMP_TAC[LBIGAUX_DIV2_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
       REWRITE_TAC[mc_iadd3_def; GSYM LBIGAUX_WORD_NOT_ZERO_ONE] THEN
       CASE_REWRITE_TAC[] THEN
       EXISTS_TAC `zs1:(N word)list` THEN EXISTS_TAC `l2:num` THEN
       ASM_REWRITE_TAC[b2w_NOT; LBIGAUX_SHL1_HEADER] THEN ASM_ARITH_TAC);
     (SUBGOAL_THEN `~(word 2:N word = word 0)` (fun th -> REWRITE_TAC[th]) THENL
        [MATCH_MP_TAC LBIGAUX_WORD_2_NZ THEN
         SUBGOAL_THEN `~(xs:(N word)list = [])` MP_TAC THENL
          [DISCH_TAC THEN UNDISCH_TAC `~(mw2n (xs:(N word)list) < mw2n (ys:(N word)list))` THEN
           UNDISCH_TAC `~(mw2n (xs:(N word)list) = mw2n (ys:(N word)list))` THEN
           ASM_REWRITE_TAC[mw2n_def] THEN ARITH_TAC; ALL_TAC] THEN
         REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
         UNDISCH_TAC `LENGTH (xs:(N word)list) < dimword (:N) DIV 2` THEN
         REWRITE_TAC[LBIGAUX_DIMWORD_HALF] THEN SIMP_TAC[DIV_MULT; ARITH_RULE `~(2 = 0)`] THEN
         ARITH_TAC; ALL_TAC] THEN
       CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[mc_length] THEN
       SUBGOAL_THEN `LENGTH (ys:(N word)list) <= LENGTH (xs:(N word)list)` ASSUME_TAC THENL
        [MATCH_MP_TAC mw2n_LESS THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
       MP_TAC(SPECL [`xs:(N word)list`; `ys:(N word)list`; `zs:(N word)list`; `l1:num`]
         LBIGAUX_IADD_SUB) THEN
       ANTS_TAC THENL
        [ASM_SIMP_TAC[LBIGAUX_DIV2_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
       REWRITE_TAC[mc_iadd3_def] THEN
       CASE_REWRITE_TAC[] THEN
       EXISTS_TAC `zs1:(N word)list` THEN EXISTS_TAC `l2:num` THEN
       ASM_REWRITE_TAC[LBIGAUX_SHL1_HEADER] THEN ASM_ARITH_TAC)]]);;

(* ------------------------------------------------------------------------- *)
(* multiplication                                                            *)
(* ------------------------------------------------------------------------- *)

let mc_single_mul_add,mc_single_mul_add_pre,mc_single_mul_add_def,mc_single_mul_add_pre_def =
  LBIGAUX_tailrec_define "mc_single_mul_add" (CASE_TERM
  `((\(r0,r1,r2,r3).
      (let cnd = T in
       match single_mul r0 r2 (word 0) with (r0,r2) ->
       match single_add_word r0 r1 (word 0) with (r0,r4) ->
       match single_add_word r2 (word 0) r4 with (r2,r4) ->
       match single_add_word r0 r3 (word 0) with (r0,r4) ->
       match single_add_word r2 (word 0) r4 with (r2,r4) ->
         (INR (r0,r1,r2,r3),cnd)))
   :N word#N word#N word#N word ->
    ((N word#N word#N word#N word) + (N word#N word#N word#N word))#bool)`);;

let LBIGAUX_DIGITS_UNIQUE = prove
 (`!(a:N word) (b:N word) (c:N word) (d:N word).
     val a + dimword(:N) * val b = val c + dimword(:N) * val d ==> a = c /\ b = d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(SPECL [`a:N word`; `val (b:N word)`] LBIGAUX_VAL_DIVMOD) THEN
  MP_TAC(SPECL [`c:N word`; `val (d:N word)`] LBIGAUX_VAL_DIVMOD) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let LBIGAUX_SINGLE_ADD_WORD_0 = prove
 (`!(x:N word) y.
     single_add_word x y (word 0) =
     (FST (single_add x y F), b2w (SND (single_add x y F)):N word)`,
  REWRITE_TAC[single_add_word_thm]);;

let LBIG_MULW_TAC v w =
  FIRST_X_ASSUM(MP_TAC o AP_TERM `( * ) (dimword(:N))` o
    check (fun th -> free_in v (concl th) && not (free_in w (concl th)))) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN DISCH_TAC;;

let mc_single_mul_add_thm = prove
 (CASE_TERM
  `!(p:N word) k q s.
     mc_single_mul_add_pre (p,k,q,s) /\
     mc_single_mul_add (p,k,q,s) =
       (match single_mul_add p q k s with (x1,x2) -> (x1,k,x2,s))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mc_single_mul_add_def; mc_single_mul_add_pre_def; LET_DEF; LET_END_DEF] THEN
  LBIG_PAIR_TAC `single_mul (p:N word) q (word 0)` `r0a:N word` `r2a:N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LBIGAUX_SINGLE_ADD_WORD_0] THEN
  LBIG_PAIR_TAC `single_add (r0a:N word) k F` `r0b:N word` `c1:bool` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LBIGAUX_SINGLE_ADD_WORD_B2W] THEN
  LBIG_PAIR_TAC `single_add (r2a:N word) (word 0) c1` `r2b:N word` `c2:bool` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LBIGAUX_SINGLE_ADD_WORD_0] THEN
  LBIG_PAIR_TAC `single_add (r0b:N word) s F` `r0c:N word` `c3:bool` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LBIGAUX_SINGLE_ADD_WORD_B2W] THEN
  LBIG_PAIR_TAC `single_add (r2b:N word) (word 0) c3` `r2c:N word` `c4:bool` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  LBIG_PAIR_TAC `single_mul_add (p:N word) q k s` `x1:N word` `x2:N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  MATCH_MP_TAC LBIGAUX_DIGITS_UNIQUE THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    let th' = tryfind (fun r -> MATCH_MP r th)
      [single_mul_thm; single_add_thm; single_mul_add_thm] in
    MP_TAC th')) THEN
  REWRITE_TAC[VAL_WORD_0; BITVAL_CLAUSES; ADD_CLAUSES] THEN
  MP_TAC(SPECL [`p:N word`; `q:N word`; `k:N word`; `s:N word`] LBIGAUX_MUL_ADD_BOUND) THEN
  BOOL_CASES_TAC `c2:bool` THEN BOOL_CASES_TAC `c4:bool` THEN
  REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES; ADD_CLAUSES] THEN
  REPEAT DISCH_TAC THEN
  LBIG_MULW_TAC `r2c:N word` `r0c:N word` THEN
  LBIG_MULW_TAC `r2b:N word` `r2c:N word` THEN
  REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC);;

let mc_mul_pass,mc_mul_pass_pre,mc_mul_pass_def,mc_mul_pass_pre_def =
  LBIGAUX_tailrec_define "mc_mul_pass" (CASE_TERM
  `((\(l,r1,r8,r9,r10,r11,ys,zs).
      if r9 = r11 then
        (let cnd = val r10 < LENGTH zs in
         let zs = LUPDATE r1 (val r10) zs in
         let r10 = word_add r10 (word 1) in
           (INR (l,r1,r9,r10,ys,zs),cnd))
      else
        (let cnd = val r10 < LENGTH zs in
         let r3 = EL (val r10) zs in
         let cnd = (cnd /\ val r11 < LENGTH ys) in
         let r2 = EL (val r11) ys in
         let r0 = r8 in
         let cnd = (cnd /\ mc_single_mul_add_pre (r0,r1,r2,r3)) in
         match mc_single_mul_add (r0,r1,r2,r3) with (r0,r1,r2,r3) ->
         let zs = LUPDATE r0 (val r10) zs in
         let r1 = r2 in
         let r10 = word_add r10 (word 1) in
         let r11 = word_add r11 (word 1) in
           (INL (l - 1,r1,r8,r9,r10,r11,ys,zs),(cnd /\ ~(l = 0)))))
   :num#N word#N word#N word#N word#N word#(N word)list#(N word)list ->
    ((num#N word#N word#N word#N word#N word#(N word)list#(N word)list) +
     (num#N word#N word#N word#(N word)list#(N word)list))#bool)`);;

let mc_mul,mc_mul_pre,mc_mul_def,mc_mul_pre_def =
  LBIGAUX_tailrec_define "mc_mul" (CASE_TERM
  `((\(l,r7,r9,r10,r12,xs,ys,zs).
      if r7 = word 0 then (let r10 = word_add r10 r9 in (INR (l,r10,xs,ys,zs),T))
      else
        (let r7 = word_sub r7 (word 1) in
         let cnd = val r12 < LENGTH xs in
         let r8 = EL (val r12) xs in
         let r12 = word_add r12 (word 1) in
         let r11 = word 0 in
         let r1 = r11 in
         let cnd = (cnd /\ mc_mul_pass_pre (l - 1,r1,r8,r9,r10,r11,ys,zs) /\ ~(l = 0)) in
         match mc_mul_pass (l - 1,r1,r8,r9,r10,r11,ys,zs) with (l,r1,r9,r10,ys,zs) ->
         let r10 = word_sub r10 r9 in
           (INL (l - 1,r7,r9,r10,r12,xs,ys,zs),(cnd /\ ~(l = 0)))))
   :num#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list ->
    ((num#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list) +
     (num#N word#(N word)list#(N word)list#(N word)list))#bool)`);;

let mc_mul_zero,mc_mul_zero_pre,mc_mul_zero_def,mc_mul_zero_pre_def =
  LBIGAUX_tailrec_define "mc_mul_zero"
  `((\(l,r0,r10,zs).
      if r10 = word 0 then (INR (l,r10,zs),T)
      else
        (let r10 = word_sub r10 (word 1) in
         let cnd = val r10 < LENGTH zs in
         let zs = LUPDATE r0 (val r10) zs in
           (INL (l - 1,r0,r10,zs),(cnd /\ ~(l = 0)))))
   :num#N word#N word#(N word)list ->
    ((num#N word#N word#(N word)list) + (num#N word#(N word)list))#bool)`;;

let mc_imul1,mc_imul1_pre,mc_imul1_def,mc_imul1_pre_def =
  LBIGAUX_tailrec_define "mc_imul1"
  `((\(r10,r11).
      if r10 = r11
      then (let r13 = word 0 in (INR (r10,r11,r13),T))
      else (let r13 = word 1 in (INR (r10,r11,r13),T)))
   :N word#N word -> ((N word#N word) + (N word#N word#N word))#bool)`;;

let mc_imul,mc_imul_pre,mc_imul_def,mc_imul_pre_def =
  LBIGAUX_tailrec_define "mc_imul" (CASE_TERM
  `((\(l,r1,r2,xs,ys,zs).
      (let r10 = word 0 in
         if r1 = word 0 then (INR (l,r10,xs,ys,zs),T)
         else if r2 = word 0 then (INR (l,r10,xs,ys,zs),T)
         else
           (let r0 = word 0 in
            let r10 = r2 in
            let r10 = word_ushr r10 1 in
            let cnd = (mc_mul_zero_pre (l - 1,r0,r10,zs) /\ ~(l = 0)) in
            match mc_mul_zero (l - 1,r0,r10,zs) with (l,r10,zs) ->
            let r10 = r1 in
            let r10 = word_and r10 (word 1) in
            let r11 = r2 in
            let r11 = word_and r11 (word 1) in
            match mc_imul1 (r10,r11) with (r10,r11,r13) ->
            let r7 = r1 in
            let r7 = word_ushr r7 1 in
            let r9 = r2 in
            let r9 = word_ushr r9 1 in
            let r10 = word 0 in
            let r12 = word 0 in
            let cnd = (cnd /\ mc_mul_pre (l - 1,r7,r9,r10,r12,xs,ys,zs) /\ ~(l = 0)) in
            match mc_mul (l - 1,r7,r9,r10,r12,xs,ys,zs) with (l,r10,xs,ys,zs) ->
            let r8 = word 0 in
            let cnd = (cnd /\ mc_fix_pre (l - 1,r8,r10,zs) /\ ~(l = 0)) in
            match mc_fix (l - 1,r8,r10,zs) with (l,r8,r10,zs) ->
            let r10 = word_shl r10 1 in
            let r10 = word_add r10 r13 in
              (INR (l,r10,xs,ys,zs),cnd))))
   :num#N word#N word#(N word)list#(N word)list#(N word)list ->
    ((num#N word#N word#(N word)list#(N word)list#(N word)list) +
     (num#N word#(N word)list#(N word)list#(N word)list))#bool)`);;

let LBIGAUX_MC_MUL_PASS = prove
 (`!(ys:(N word)list) (ys1:(N word)list) (x:N word) (zs:(N word)list) (k:N word)
     (zs1:(N word)list) (zs2:(N word)list) (z2:N word) l.
     LENGTH (APPEND ys1 ys) < dimword(:N) /\ LENGTH zs = LENGTH ys /\
     LENGTH (APPEND zs1 zs) < dimword(:N) /\ LENGTH ys <= l
     ==> ?r1 l2.
           mc_mul_pass_pre (l,k,x,word (LENGTH (APPEND ys1 ys)),word (LENGTH zs1),
             word (LENGTH ys1),APPEND ys1 ys,APPEND zs1 (APPEND zs (CONS z2 zs2))) /\
           mc_mul_pass (l,k,x,word (LENGTH (APPEND ys1 ys)),word (LENGTH zs1),
             word (LENGTH ys1),APPEND ys1 ys,APPEND zs1 (APPEND zs (CONS z2 zs2))) =
             (l2,r1,word (LENGTH (APPEND ys1 ys)),word (LENGTH (APPEND zs1 zs) + 1),
              APPEND ys1 ys,APPEND zs1 (APPEND (mw_mul_pass x ys zs k) zs2)) /\
           l <= l2 + LENGTH ys`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ONCE_REWRITE_TAC[mc_mul_pass_def; mc_mul_pass_pre_def] THEN
    REWRITE_TAC[APPEND_NIL; APPEND; mw_mul_pass_def; LET_DEF; LET_END_DEF] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL]) THEN
    SUBGOAL_THEN `val (word (LENGTH (zs1:(N word)list)):N word) = LENGTH zs1` SUBST1_TAC THENL
     [MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LUPDATE_LENGTH; LENGTH_APPEND; LENGTH; word_add_n2w] THEN
    MAP_EVERY EXISTS_TAC [`k:N word`; `l:num`] THEN REWRITE_TAC[ADD_CLAUSES; LE_REFL] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `ys1:(N word)list` THEN X_GEN_TAC `x:N word` THEN X_GEN_TAC `zs:(N word)list` THEN
  LBIG_CONS_CASES_TAC `zs:(N word)list` `z:N word` `zs':(N word)list` THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH]) THEN
  SUBGOAL_THEN `~(word (LENGTH (ys1:(N word)list) + SUC (LENGTH (t:(N word)list))):N word =
                  word (LENGTH ys1)) /\
                val (word (LENGTH (ys1:(N word)list)):N word) = LENGTH ys1 /\
                val (word (LENGTH (zs1:(N word)list)):N word) = LENGTH zs1`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [W(fun (_,w) -> MP_TAC(SPECL [rand(lhs(rand w)); rand(rhs(rand w))]
         (INST_TYPE [`:N`,`:N`] LBIGAUX_WORD_EQ_LT))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ARITH_TAC];
      MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; APPEND] THEN
  ONCE_REWRITE_TAC[mc_mul_pass_def; mc_mul_pass_pre_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; LBIGAUX_EL_LENGTH_CONS; mc_single_mul_add_thm] THEN
  LBIG_PAIR_TAC `single_mul_add (x:N word) h k z` `x1:N word` `x2:N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LUPDATE_LENGTH; word_add_n2w; mw_mul_pass_def; HD; TL] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`SNOC (h:N word) ys1`; `x:N word`; `zs':(N word)list`;
    `x2:N word`; `SNOC (x1:N word) zs1`; `zs2:(N word)list`; `z2:N word`; `l - 1`]) THEN
  REWRITE_TAC[LENGTH_SNOC; SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH;
              GSYM ADD1; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:N word` (X_CHOOSE_THEN `l2:num` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r1:N word`; `l2:num`] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN ASM_ARITH_TAC);;

let mc_mul_pass_thm = prove
 (`!(ys:(N word)list) (x:N word) (zs:(N word)list) (k:N word)
     (zs1:(N word)list) (zs2:(N word)list) (z2:N word) l.
     LENGTH ys < dimword(:N) /\ LENGTH zs = LENGTH ys /\
     LENGTH (APPEND zs1 zs) < dimword(:N) /\ LENGTH ys <= l
     ==> ?r1 l2.
           mc_mul_pass_pre (l,k,x,word (LENGTH ys),word (LENGTH zs1),word 0,ys,
             APPEND zs1 (APPEND zs (CONS z2 zs2))) /\
           mc_mul_pass (l,k,x,word (LENGTH ys),word (LENGTH zs1),word 0,ys,
             APPEND zs1 (APPEND zs (CONS z2 zs2))) =
             (l2,r1,word (LENGTH ys),word (LENGTH (APPEND zs1 zs) + 1),ys,
              APPEND zs1 (APPEND (mw_mul_pass x ys zs k) zs2)) /\
           l <= l2 + LENGTH ys`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`ys:(N word)list`; `[]:(N word)list`] LBIGAUX_MC_MUL_PASS) THEN
  REWRITE_TAC[APPEND; LENGTH] THEN DISCH_THEN MATCH_ACCEPT_TAC);;

let LBIGAUX_WORD_SUB_MID2 = prove
 (`!a b. word_sub (word ((a + b) + 1)) (word b):N word = word (a + 1)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ARITH_RULE `(a + b) + 1 = b + a + 1`] THEN
  REWRITE_TAC[LBIGAUX_WORD_ADD_SUB_L]);;

let LBIGAUX_MC_MUL = prove
 (`!(xs:(N word)list) (ys:(N word)list) (zs:(N word)list) (xs1:(N word)list)
     (zs1:(N word)list) (zs2:(N word)list) l.
     LENGTH (APPEND xs1 xs) < dimword(:N) /\ LENGTH ys < dimword(:N) /\
     LENGTH zs = LENGTH ys /\ LENGTH (APPEND zs1 (APPEND zs zs2)) < dimword(:N) /\
     LENGTH xs <= LENGTH zs2 /\ ~(ys = []) /\
     2 * LENGTH xs + LENGTH xs * LENGTH ys <= l
     ==> ?zs3 l2.
           mc_mul_pre (l,word (LENGTH xs),word (LENGTH ys),word (LENGTH zs1),
             word (LENGTH xs1),APPEND xs1 xs,ys,APPEND zs1 (APPEND zs zs2)) /\
           mc_mul (l,word (LENGTH xs),word (LENGTH ys),word (LENGTH zs1),
             word (LENGTH xs1),APPEND xs1 xs,ys,APPEND zs1 (APPEND zs zs2)) =
             (l2,word (LENGTH (APPEND zs1 (mw_mul xs ys zs))),APPEND xs1 xs,ys,
              APPEND zs1 (APPEND (mw_mul xs ys zs) zs3)) /\
           LENGTH (APPEND zs1 (APPEND zs zs2)) =
             LENGTH (APPEND zs1 (APPEND (mw_mul xs ys zs) zs3)) /\
           l <= l2 + 2 * LENGTH xs + LENGTH xs * LENGTH ys`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[mc_mul_def; mc_mul_pre_def] THEN
    REWRITE_TAC[APPEND_NIL; mw_mul_def; LET_DEF; LET_END_DEF; word_add_n2w] THEN
    MAP_EVERY EXISTS_TAC [`zs2:(N word)list`; `l:num`] THEN
    ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `ys:(N word)list` THEN X_GEN_TAC `zs:(N word)list` THEN
  X_GEN_TAC `xs1:(N word)list` THEN X_GEN_TAC `zs1:(N word)list` THEN
  X_GEN_TAC `zs2:(N word)list` THEN
  LBIG_CONS_CASES_TAC `zs2:(N word)list` `z2:N word` `zs2':(N word)list` THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC n <= 0)`; LE_SUC] THEN
  X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH]) THEN
  SUBGOAL_THEN `~(word (SUC (LENGTH (t:(N word)list))):N word = word 0) /\
                val (word (LENGTH (xs1:(N word)list)):N word) = LENGTH xs1`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LBIGAUX_WORD_SUC_NZ; MATCH_MP_TAC LBIGAUX_VAL_WORD_LT] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[mc_mul_def; mc_mul_pre_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; LBIGAUX_WORD_SUC_SUB1; LBIGAUX_EL_LENGTH_CONS] THEN
  MP_TAC(SPECL [`ys:(N word)list`; `h:N word`; `zs:(N word)list`; `word 0:N word`;
    `zs1:(N word)list`; `zs2':(N word)list`; `z2:N word`; `l - 1`] mc_mul_pass_thm) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND] THEN
    SUBGOAL_THEN `1 <= LENGTH (ys:(N word)list)` MP_TAC THENL
     [UNDISCH_TAC `~(ys:(N word)list = [])` THEN REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `2 * SUC (LENGTH (t:(N word)list)) + SUC (LENGTH t) * LENGTH (ys:(N word)list) <= l` THEN
    REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:N word` (X_CHOOSE_THEN `l2:num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LBIGAUX_WORD_SUB_MID2] THEN
  SUBGOAL_THEN `?p ps. mw_mul_pass (h:N word) ys zs (word 0) = CONS p ps /\
                       LENGTH (ps:(N word)list) = LENGTH (ys:(N word)list)`
   STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ys:(N word)list`; `zs:(N word)list`; `h:N word`; `word 0:N word`]
      LENGTH_mw_mul_pass) THEN
    STRUCT_CASES_TAC(ISPEC `mw_mul_pass (h:N word) ys zs (word 0)` list_CASES) THEN
    REWRITE_TAC[LENGTH; CONS_11; GSYM ADD1; SUC_INJ; NOT_SUC; GSYM NOT_SUC] THEN
    MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[mw_mul_def; LET_DEF; LET_END_DEF; HD; TL] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ys:(N word)list`; `ps:(N word)list`;
    `SNOC (h:N word) xs1`; `SNOC (p:N word) zs1`; `zs2':(N word)list`; `l2 - 1`]) THEN
  REWRITE_TAC[LENGTH_SNOC; SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH;
              GSYM ADD1; ADD_CLAUSES; word_add_n2w] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `2 * SUC (LENGTH (t:(N word)list)) + SUC (LENGTH t) * LENGTH (ys:(N word)list) <= l` THEN
    REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `zs3:(N word)list` (X_CHOOSE_THEN `l3:num` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`zs3:(N word)list`; `l3:num`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `2 * SUC (LENGTH (t:(N word)list)) + SUC (LENGTH t) * LENGTH (ys:(N word)list) <= l` THEN
  REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC);;

let mc_mul_thm = prove
 (`!(xs:(N word)list) (ys:(N word)list) (zs:(N word)list) (zs2:(N word)list) l.
     LENGTH xs < dimword(:N) /\ LENGTH ys < dimword(:N) /\
     LENGTH zs = LENGTH ys /\ LENGTH (APPEND zs zs2) < dimword(:N) /\
     LENGTH xs <= LENGTH zs2 /\ ~(ys = []) /\
     2 * LENGTH xs + LENGTH xs * LENGTH ys <= l
     ==> ?zs3 l2.
           mc_mul_pre (l,word (LENGTH xs),word (LENGTH ys),word 0,word 0,xs,ys,
                       APPEND zs zs2) /\
           mc_mul (l,word (LENGTH xs),word (LENGTH ys),word 0,word 0,xs,ys,
                   APPEND zs zs2) =
             (l2,word (LENGTH (mw_mul xs ys zs)),xs,ys,APPEND (mw_mul xs ys zs) zs3) /\
           LENGTH (APPEND zs zs2) = LENGTH (APPEND (mw_mul xs ys zs) zs3) /\
           l <= l2 + 2 * LENGTH xs + LENGTH xs * LENGTH ys`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`xs:(N word)list`; `ys:(N word)list`; `zs:(N word)list`;
    `[]:(N word)list`; `[]:(N word)list`; `zs2:(N word)list`; `l:num`] LBIGAUX_MC_MUL) THEN
  REWRITE_TAC[APPEND; LENGTH]);;

let mc_mul_zero_thm = prove
 (`!(zs:(N word)list) (zs1:(N word)list) l.
     LENGTH zs < dimword(:N) /\ LENGTH zs <= l
     ==> mc_mul_zero_pre (l,word 0:N word,word (LENGTH zs),APPEND zs zs1) /\
         mc_mul_zero (l,word 0,word (LENGTH zs),APPEND zs zs1) =
           (l - LENGTH zs,word 0,APPEND (MAP (\x. word 0) zs) zs1)`,
  MATCH_MP_TAC SNOC_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[mc_mul_zero_def; mc_mul_zero_pre_def] THEN
    REWRITE_TAC[LENGTH; APPEND; MAP; SUB_0];
    ALL_TAC] THEN
  X_GEN_TAC `zs:(N word)list` THEN DISCH_TAC THEN X_GEN_TAC `x:N word` THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH_SNOC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(word (SUC (LENGTH (zs:(N word)list))):N word = word 0) /\
                val (word (LENGTH (zs:(N word)list)):N word) = LENGTH zs`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LBIGAUX_WORD_SUC_NZ] THEN MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[mc_mul_zero_def; mc_mul_zero_pre_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; LBIGAUX_WORD_SUC_SUB1] THEN
  REWRITE_TAC[SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LUPDATE_LENGTH] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (word 0:N word) zs1`; `l - 1`]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[MAP_APPEND; MAP; GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; PAIR_EQ] THEN ASM_ARITH_TAC);;

let MAP_EQ_MAP_EQ = prove
 (`!(xs:A list) (ys:B list).
     MAP (\x. word 0:N word) xs = MAP (\x. word 0) ys <=> LENGTH xs = LENGTH ys`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; LENGTH; NOT_CONS_NIL; NOT_SUC; GSYM NOT_SUC; CONS_11; SUC_INJ]);;

let mc_imul1_thm = prove
 (`!r10 r11:N word.
     mc_imul1_pre (r10,r11) /\
     mc_imul1 (r10,r11) = (r10,r11,if r10 = r11 then word 0 else word 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mc_imul1_def; mc_imul1_pre_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let LBIGAUX_B2W_EQ_COND = prove
 (`!s t. (if b2w s:N word = b2w t then word 0 else word 1) = b2w (~(s <=> t)):N word`,
  REPEAT GEN_TAC THEN REWRITE_TAC[multiword_b2w_def] THEN
  BOOL_CASES_TAC `s:bool` THEN BOOL_CASES_TAC `t:bool` THEN
  REWRITE_TAC[BITVAL_CLAUSES; LBIGAUX_WORD_NOT_ZERO_ONE; GSYM LBIGAUX_WORD_NOT_ZERO_ONE]);;

let mc_imul_thm = prove
 (`!s t (xs:(N word)list) (ys:(N word)list) (zs:(N word)list) l.
     ((mc_header (s,xs) = word 0) <=> (xs = [])) /\
     ((mc_header (t,ys) = word 0) <=> (ys = [])) /\
     LENGTH xs < dimword (:N) DIV 2 /\ LENGTH ys < dimword (:N) DIV 2 /\
     LENGTH xs + LENGTH ys <= LENGTH zs /\ LENGTH zs < dimword (:N) DIV 2 /\
     3 * LENGTH xs + 3 * LENGTH ys + LENGTH xs * LENGTH ys + 3 <= l
     ==> ?zs1 l2.
           mc_imul_pre (l,mc_header (s,xs),mc_header (t,ys),xs,ys,zs) /\
           mc_imul (l,mc_header (s,xs),mc_header (t,ys),xs,ys,zs) =
             (l2,mc_header (mwi_mul (s,xs) (t,ys)),xs,ys,
              APPEND (SND (mwi_mul (s,xs) (t,ys))) zs1) /\
           LENGTH (APPEND (SND (mwi_mul (s,xs) (t,ys))) zs1) = LENGTH zs /\
           l <= l2 + 3 * LENGTH xs + 3 * LENGTH ys + LENGTH xs * LENGTH ys + 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mc_imul_def; mc_imul_pre_def; LET_DEF; LET_END_DEF; mwi_mul_def] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `xs:(N word)list = []` THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `zs:(N word)list` THEN EXISTS_TAC `l:num` THEN
    REWRITE_TAC[mc_header_def; LENGTH; MULT_CLAUSES; WORD_ADD_0; APPEND] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `ys:(N word)list = []` THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `zs:(N word)list` THEN EXISTS_TAC `l:num` THEN
    REWRITE_TAC[mc_header_def; LENGTH; MULT_CLAUSES; WORD_ADD_0; APPEND] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (xs:(N word)list) < dimword(:N) /\ LENGTH (ys:(N word)list) < dimword(:N) /\
                LENGTH (zs:(N word)list) < dimword(:N)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[dim63_IMP_dim64]; ALL_TAC] THEN
  ASM_SIMP_TAC[mc_length; mc_header_AND_1; mc_imul1_thm] THEN
  MP_TAC(ISPECL [`zs:(N word)list`; `LENGTH (ys:(N word)list)`] multiword_LESS_EQ_LENGTH) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`qs1:(N word)list`; `qs2:(N word)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  MP_TAC(SPECL [`qs1:(N word)list`; `qs2:(N word)list`; `l - 1`] mc_mul_zero_thm) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `MAP (\x. word 0:N word) (qs1:(N word)list) = MAP (\x. word 0) (ys:(N word)list)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[MAP_EQ_MAP_EQ]; ALL_TAC] THEN
  MP_TAC(SPECL [`xs:(N word)list`; `ys:(N word)list`; `MAP (\x. word 0:N word) (ys:(N word)list)`;
    `qs2:(N word)list`; `l - 1 - LENGTH (ys:(N word)list) - 1`] mc_mul_thm) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_APPEND] THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `zs3:(N word)list` (X_CHOOSE_THEN `l2:num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (mw_mul (xs:(N word)list) ys (MAP (\x. word 0) ys)) =
                LENGTH xs + LENGTH ys` ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_mw_mul THEN REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  MP_TAC(SPECL [`mw_mul (xs:(N word)list) ys (MAP (\x. word 0) ys)`; `zs3:(N word)list`;
    `word 0:N word`; `l2 - 1`] mc_fix_thm) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r8a:N word` (X_CHOOSE_THEN `l3:num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LBIGAUX_B2W_EQ_COND; LBIGAUX_SHL1_HEADER] THEN
  EXISTS_TAC `APPEND (REPLICATE (LENGTH (mw_mul (xs:(N word)list) ys (MAP (\x. word 0) ys)) -
     LENGTH (mw_fix (mw_mul xs ys (MAP (\x. word 0) ys)))) (word 0:N word)) zs3` THEN
  EXISTS_TAC `l3:num` THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH_MAP]) THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE] THEN
  MP_TAC(SPEC `mw_mul (xs:(N word)list) ys (MAP (\x. word 0) ys)` LENGTH_mw_fix) THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* simple division, calc_d                                                   *)
(* ------------------------------------------------------------------------- *)

let single_div_pre_def = new_definition
  `single_div_pre (r2:N word) (r0:N word) (r9:N word) <=>
     ~(r9 = word 0) /\ (val r2 * dimword(:N) + val r0) DIV val r9 < dimword(:N)`;;

let mc_single_div,mc_single_div_pre,mc_single_div_def,mc_single_div_pre_def =
  LBIGAUX_tailrec_define "mc_single_div" (CASE_TERM
  `((\(r0,r2,r9).
      (let cnd = single_div_pre r2 r0 r9 in
       match single_div r2 r0 r9 with (r0,r2) ->
         (INR (r0,r2,r9),cnd)))
   :N word#N word#N word -> ((N word#N word#N word) + (N word#N word#N word))#bool)`);;

let mc_single_div_thm = prove
 (CASE_TERM
  `!(x2:N word) x1 y.
     (mc_single_div_pre (x2,x1,y) <=> word_ult x1 y) /\
     mc_single_div (x2,x1,y) = (match single_div x1 x2 y with (q,r) -> (q,r,y))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mc_single_div_def; mc_single_div_pre_def; LET_DEF; LET_END_DEF] THEN
  LBIG_PAIR_TAC `single_div (x1:N word) x2 y` `q:N word` `r:N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[single_div_pre_def; WORD_ULT] THEN
  ASM_CASES_TAC `y:N word = word 0` THEN ASM_REWRITE_TAC[VAL_WORD_0; CONJUNCT1 LT] THEN
  SUBGOAL_THEN `~(val (y:N word) = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[RDIV_LT_EQ] THEN
  ASSUME_TAC(ISPEC `x2:N word` w2n_lt) THEN
  EQ_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `val (y:N word) * dimword(:N) <= val (x1:N word) * dimword(:N)` MP_TAC THENL
     [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ALL_TAC] THEN
    UNDISCH_TAC `val (x1:N word) * dimword(:N) + val (x2:N word) < val (y:N word) * dimword(:N)` THEN
    ARITH_TAC;
    SUBGOAL_THEN `(val (x1:N word) + 1) * dimword(:N) <= val (y:N word) * dimword(:N)` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN
    UNDISCH_TAC `(val (x1:N word) + 1) * dimword(:N) <= val (y:N word) * dimword(:N)` THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    UNDISCH_TAC `val (x2:N word) < dimword(:N)` THEN ARITH_TAC]);;

let mc_simple_div,mc_simple_div_pre,mc_simple_div_def,mc_simple_div_pre_def =
  LBIGAUX_tailrec_define "mc_simple_div" (CASE_TERM
  `((\(l,r2,r9,r10,xs,zs).
      if r10 = word 0 then (INR (l,r2,r9,r10,xs,zs),T)
      else
        (let r10 = word_sub r10 (word 1) in
         let cnd = val r10 < LENGTH xs in
         let r0 = EL (val r10) xs in
         let cnd = (cnd /\ mc_single_div_pre (r0,r2,r9)) in
         match mc_single_div (r0,r2,r9) with (r0,r2,r9) ->
         let cnd = (cnd /\ val r10 < LENGTH zs) in
         let zs = LUPDATE r0 (val r10) zs in
           (INL (l - 1,r2,r9,r10,xs,zs),(cnd /\ ~(l = 0)))))
   :num#N word#N word#N word#(N word)list#(N word)list ->
    ((num#N word#N word#N word#(N word)list#(N word)list) +
     (num#N word#N word#N word#(N word)list#(N word)list))#bool)`);;

let mc_simple_div1,mc_simple_div1_pre,mc_simple_div1_def,mc_simple_div1_pre_def =
  LBIGAUX_tailrec_define "mc_simple_div1" (CASE_TERM
  `((\(l,r2,r9,r10,zs).
      if r10 = word 0 then (INR (l,r2,r9,r10,zs),T)
      else
        (let r10 = word_sub r10 (word 1) in
         let cnd = val r10 < LENGTH zs in
         let r0 = EL (val r10) zs in
         let cnd = (cnd /\ mc_single_div_pre (r0,r2,r9)) in
         match mc_single_div (r0,r2,r9) with (r0,r2,r9) ->
         let zs = LUPDATE r0 (val r10) zs in
           (INL (l - 1,r2,r9,r10,zs),(cnd /\ ~(l = 0)))))
   :num#N word#N word#N word#(N word)list ->
    ((num#N word#N word#N word#(N word)list) +
     (num#N word#N word#N word#(N word)list))#bool)`);;

let LBIGAUX_MW_SIMPLE_DIV_SNOC = prove
 (`!(r2:N word) x xs r9 qs r.
     mw_simple_div r2 (REVERSE (SNOC x xs)) r9 = (qs,r,T) <=>
     word_ult r2 r9 /\
     ?qs'. qs = CONS (FST (single_div r2 x r9)) qs' /\
           mw_simple_div (SND (single_div r2 x r9)) (REVERSE xs) r9 = (qs',r,T)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REVERSE_SNOC; mw_simple_div_def; LET_DEF; LET_END_DEF] THEN
  LBIG_PAIR_TAC `single_div (r2:N word) x r9` `q:N word` `r':N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `mw_simple_div (r':N word) (REVERSE xs) r9` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`qs1:(N word)list`; `p:N word#bool`] THEN
  MP_TAC(ISPEC `p:N word#bool` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`r1:N word`; `c1:bool`] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; FST; SND] THEN MESON_TAC[]);;

let mc_simple_div_thm = prove
 (`!(xs:(N word)list) (xs1:(N word)list) (zs:(N word)list) (zs1:(N word)list)
     (r2:N word) r9 qs r l.
     LENGTH xs < dimword(:N) /\ LENGTH zs = LENGTH xs /\ LENGTH xs <= l /\
     mw_simple_div r2 (REVERSE xs) r9 = (qs,r,T)
     ==> mc_simple_div_pre (l,r2,r9,word (LENGTH xs),APPEND xs xs1,APPEND zs zs1) /\
         mc_simple_div (l,r2,r9,word (LENGTH xs),APPEND xs xs1,APPEND zs zs1) =
           (l - LENGTH xs,r,r9,word 0,APPEND xs xs1,APPEND (REVERSE qs) zs1)`,
  MATCH_MP_TAC SNOC_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH; LENGTH_EQ_NIL; REVERSE; mw_simple_div_def;
      PAIR_EQ] THEN
    STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN
    ONCE_REWRITE_TAC[mc_simple_div_def; mc_simple_div_pre_def] THEN
    REWRITE_TAC[LENGTH; APPEND; REVERSE; SUB_0];
    ALL_TAC] THEN
  X_GEN_TAC `xs:(N word)list` THEN DISCH_TAC THEN X_GEN_TAC `x:N word` THEN
  X_GEN_TAC `xs1:(N word)list` THEN X_GEN_TAC `zs:(N word)list` THEN
  MP_TAC(ISPEC `zs:(N word)list` SNOC_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `z:N word` (X_CHOOSE_THEN `zs':(N word)list` SUBST1_TAC))) THEN
  REWRITE_TAC[LENGTH; LENGTH_SNOC; GSYM NOT_SUC; SUC_INJ; LBIGAUX_MW_SIMPLE_DIV_SNOC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(word (SUC (LENGTH (xs:(N word)list))):N word = word 0) /\
                val (word (LENGTH (xs:(N word)list)):N word) = LENGTH xs`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LBIGAUX_WORD_SUC_NZ] THEN MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[mc_simple_div_def; mc_simple_div_pre_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; LBIGAUX_WORD_SUC_SUB1] THEN
  REWRITE_TAC[SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LBIGAUX_EL_LENGTH_CONS] THEN
  ASM_REWRITE_TAC[mc_single_div_thm] THEN
  LBIG_PAIR_TAC `single_div (r2:N word) x r9` `q:N word` `r':N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  UNDISCH_TAC `single_div (r2:N word) x r9 = q,r'` THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; FST; SND]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `LUPDATE (q:N word) (LENGTH (xs:(N word)list)) (APPEND zs' (CONS z zs1)) =
                APPEND zs' (CONS q zs1)` SUBST1_TAC THENL
   [UNDISCH_TAC `LENGTH (zs':(N word)list) = LENGTH (xs:(N word)list)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LUPDATE_LENGTH]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (x:N word) xs1`; `zs':(N word)list`;
    `CONS (q:N word) zs1`; `r':N word`; `r9:N word`; `qs':(N word)list`; `r:N word`;
    `l - 1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REVERSE; GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; PAIR_EQ] THEN ASM_ARITH_TAC);;

let mc_simple_div1_thm = prove
 (`!(zs:(N word)list) (zs1:(N word)list) (r2:N word) r9 qs r l.
     LENGTH zs < dimword(:N) /\ LENGTH zs <= l /\
     mw_simple_div r2 (REVERSE zs) r9 = (qs,r,T)
     ==> mc_simple_div1_pre (l,r2,r9,word (LENGTH zs),APPEND zs zs1) /\
         mc_simple_div1 (l,r2,r9,word (LENGTH zs),APPEND zs zs1) =
           (l - LENGTH zs,r,r9,word 0,APPEND (REVERSE qs) zs1)`,
  MATCH_MP_TAC SNOC_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH; REVERSE; mw_simple_div_def; PAIR_EQ] THEN
    STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN
    ONCE_REWRITE_TAC[mc_simple_div1_def; mc_simple_div1_pre_def] THEN
    REWRITE_TAC[LENGTH; APPEND; REVERSE; SUB_0];
    ALL_TAC] THEN
  X_GEN_TAC `zs:(N word)list` THEN DISCH_TAC THEN X_GEN_TAC `x:N word` THEN
  REWRITE_TAC[LENGTH_SNOC; LBIGAUX_MW_SIMPLE_DIV_SNOC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(word (SUC (LENGTH (zs:(N word)list))):N word = word 0) /\
                val (word (LENGTH (zs:(N word)list)):N word) = LENGTH zs`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LBIGAUX_WORD_SUC_NZ] THEN MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[mc_simple_div1_def; mc_simple_div1_pre_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; LBIGAUX_WORD_SUC_SUB1] THEN
  REWRITE_TAC[SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LBIGAUX_EL_LENGTH_CONS] THEN
  ASM_REWRITE_TAC[mc_single_div_thm] THEN
  LBIG_PAIR_TAC `single_div (r2:N word) x r9` `q:N word` `r':N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  UNDISCH_TAC `single_div (r2:N word) x r9 = q,r'` THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; FST; SND]) THEN ASSUME_TAC th) THEN
  REWRITE_TAC[LUPDATE_LENGTH] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (q:N word) zs1`; `r':N word`; `r9:N word`;
    `qs':(N word)list`; `r:N word`; `l - 1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REVERSE; GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; PAIR_EQ] THEN ASM_ARITH_TAC);;

let mc_calc_d,mc_calc_d_pre,mc_calc_d_def,mc_calc_d_pre_def =
  LBIGAUX_tailrec_define "mc_calc_d"
  `((\(l,r1,r2).
      (if word_ilt r1 (word 0) then (INR (l,r2),T) else
         (let r1 = word_add r1 r1 in let r2 = word_add r2 r2 in
            (INL (l - 1,r1,r2),~(l = 0)))))
   :num#N word#N word -> ((num#N word#N word) + (num#N word))#bool)`;;

let LBIGAUX_MC_CALC_D = prove
 (`!n (v1:N word) d l.
     ~(v1 = word 0) /\ dimword(:N) <= val v1 * 2 EXP n /\ n <= l
     ==> ?l2. mc_calc_d_pre (l,v1,d) /\ mc_calc_d (l,v1,d) = (l2,calc_d (v1,d)) /\
              l <= l2 + n`,
  INDUCT_TAC THENL
   [REWRITE_TAC[EXP; MULT_CLAUSES] THEN MESON_TAC[w2n_lt; NOT_LE]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[mc_calc_d_def; mc_calc_d_pre_def] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [calc_d_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; GSYM word_msb_neg] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `word_msb (v1:N word)` THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `l:num` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_add (x:N word) x = word_mul x (word 2)`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`word_mul (v1:N word) (word 2)`; `word_mul (d:N word) (word 2)`;
    `l - 1`]) THEN
  SUBGOAL_THEN `val (word_mul (v1:N word) (word 2)) = 2 * val v1` ASSUME_TAC THENL
   [MATCH_MP_TAC LBIGAUX_VAL_DOUBLE THEN ASM_MESON_TAC[d_word_msb; NOT_LE]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_0] THEN
    UNDISCH_TAC `~(v1:N word = word 0)` THEN REWRITE_TAC[GSYM VAL_EQ_0] THEN
    UNDISCH_TAC `dimword(:N) <= val (v1:N word) * 2 EXP SUC n` THEN
    REWRITE_TAC[EXP; MULT_AC] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `l2:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let mc_calc_d_thm = prove
 (`!(v1:N word) d l.
     ~(v1 = word 0) /\ dimindex(:N) <= l
     ==> ?l2. mc_calc_d_pre (l,v1,d) /\ mc_calc_d (l,v1,d) = (l2,calc_d (v1,d)) /\
              l <= l2 + dimindex(:N)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LBIGAUX_MC_CALC_D THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM dimword_def] THEN
  UNDISCH_TAC `~(v1:N word = word 0)` THEN REWRITE_TAC[GSYM VAL_EQ_0] THEN
  DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `d = 1 * d`] THEN
  REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* division: the quotient digit guess                                        *)
(* ------------------------------------------------------------------------- *)

let mc_single_mul,mc_single_mul_pre,mc_single_mul_def,mc_single_mul_pre_def =
  LBIGAUX_tailrec_define "mc_single_mul" (CASE_TERM
  `((\(r0,r1,r2).
      (let cnd = T in
       match single_mul r0 r2 (word 0) with (r0,r2) ->
       match single_add_word r0 r1 (word 0) with (r0,r4) ->
       match single_add_word r2 (word 0) r4 with (r2,r4) ->
         (INR (r0,r1,r2),cnd)))
   :N word#N word#N word -> ((N word#N word#N word) + (N word#N word#N word))#bool)`);;

let mc_single_mul_thm = prove
 (CASE_TERM
  `!(p:N word) k q.
     mc_single_mul_pre (p,k,q) /\
     mc_single_mul (p,k,q) =
       (match single_mul_add p q k (word 0) with (x1,x2) -> (x1,k,x2))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mc_single_mul_def; mc_single_mul_pre_def; LET_DEF; LET_END_DEF] THEN
  LBIG_PAIR_TAC `single_mul (p:N word) q (word 0)` `r0a:N word` `r2a:N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LBIGAUX_SINGLE_ADD_WORD_0] THEN
  LBIG_PAIR_TAC `single_add (r0a:N word) k F` `r0b:N word` `c1:bool` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LBIGAUX_SINGLE_ADD_WORD_B2W] THEN
  LBIG_PAIR_TAC `single_add (r2a:N word) (word 0) c1` `r2b:N word` `c2:bool` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  LBIG_PAIR_TAC `single_mul_add (p:N word) q k (word 0)` `x1:N word` `x2:N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  MATCH_MP_TAC LBIGAUX_DIGITS_UNIQUE THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    let th' = tryfind (fun r -> MATCH_MP r th)
      [single_mul_thm; single_add_thm; single_mul_add_thm] in
    MP_TAC th')) THEN
  REWRITE_TAC[VAL_WORD_0; BITVAL_CLAUSES; ADD_CLAUSES] THEN
  MP_TAC(SPECL [`p:N word`; `q:N word`; `k:N word`; `word 0:N word`] LBIGAUX_MUL_ADD_BOUND) THEN
  REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES] THEN
  BOOL_CASES_TAC `c2:bool` THEN
  REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES; ADD_CLAUSES] THEN
  REPEAT DISCH_TAC THEN
  LBIG_MULW_TAC `r2b:N word` `r0b:N word` THEN
  REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC);;

let mc_mul_by_single2,mc_mul_by_single2_pre,mc_mul_by_single2_def,mc_mul_by_single2_pre_def =
  LBIGAUX_tailrec_define "mc_mul_by_single2" (CASE_TERM
  `((\(r6,r7,r8).
      (let r0 = r6 in
       let r1 = word 0 in
       let r2 = r7 in
       let cnd = mc_single_mul_pre (r0,r1,r2) in
       match mc_single_mul (r0,r1,r2) with (r0,r1,r2) ->
       let r12 = r0 in
       let r0 = r6 in
       let r1 = r2 in
       let r2 = r8 in
       let cnd = (cnd /\ mc_single_mul_pre (r0,r1,r2)) in
       match mc_single_mul (r0,r1,r2) with (r0,r1,r2) ->
       let r3 = r2 in
       let r2 = r0 in
       let r1 = r12 in
         (INR (r1,r2,r3,r6,r7,r8),cnd)))
   :N word#N word#N word ->
    ((N word#N word#N word) + (N word#N word#N word#N word#N word#N word))#bool)`);;

let mc_mul_by_single2_thm = prove
 (`!r6 r7 r8:N word.
     ?r1 r2 r3.
       mc_mul_by_single2_pre (r6,r7,r8) /\
       mc_mul_by_single2 (r6,r7,r8) = (r1,r2,r3,r6,r7,r8) /\
       mw_mul_by_single r6 [r7; r8] = [r1; r2; r3]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mc_mul_by_single2_def; mc_mul_by_single2_pre_def; LET_DEF; LET_END_DEF;
              mc_single_mul_thm] THEN
  REWRITE_TAC[mw_mul_by_single_def; LENGTH; k2mw_def; DIV_0; mw_mul_pass_def; HD; TL;
              ARITH_RULE `2 = SUC (SUC 0)`] THEN
  LBIG_PAIR_TAC `single_mul_add (r6:N word) r7 (word 0) (word 0)` `y1:N word` `k1:N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  LBIG_PAIR_TAC `single_mul_add (r6:N word) r8 k1 (word 0)` `y2:N word` `k2:N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MESON_TAC[]);;

let mc_cmp3,mc_cmp3_pre,mc_cmp3_def,mc_cmp3_pre_def =
  LBIGAUX_tailrec_define "mc_cmp3"
  `((\(r1,r2,r3,r9,r10,r11).
      (let r0 = word 1 in
         if r3 = r11 then
           if r2 = r10 then
             if r1 = r9 then
               (let r0 = word 0 in (INR (r0,r1,r2,r3,r9,r10,r11),T))
             else if word_ult r9 r1 then (INR (r0,r1,r2,r3,r9,r10,r11),T)
             else (let r0 = word 0 in (INR (r0,r1,r2,r3,r9,r10,r11),T))
           else if word_ult r10 r2 then (INR (r0,r1,r2,r3,r9,r10,r11),T)
           else (let r0 = word 0 in (INR (r0,r1,r2,r3,r9,r10,r11),T))
         else if word_ult r11 r3 then (INR (r0,r1,r2,r3,r9,r10,r11),T)
         else (let r0 = word 0 in (INR (r0,r1,r2,r3,r9,r10,r11),T))))
   :N word#N word#N word#N word#N word#N word ->
    ((N word#N word#N word#N word#N word#N word) +
     (N word#N word#N word#N word#N word#N word#N word))#bool)`;;

let LBIGAUX_MW_CMP_2 = prove
 (`!a1 a2 b1 b2:N word.
     mw_cmp [a1;a2] [b1;b2] =
     if a2 = b2 then (if a1 = b1 then NONE else SOME (word_ult a1 b1))
     else SOME (word_ult a2 b2)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[mw_cmp_def] THEN REWRITE_TAC[NOT_CONS_NIL; LAST; BUTLAST] THEN
  ONCE_REWRITE_TAC[mw_cmp_def] THEN REWRITE_TAC[NOT_CONS_NIL; LAST; BUTLAST] THEN
  ONCE_REWRITE_TAC[mw_cmp_def] THEN REWRITE_TAC[NOT_CONS_NIL; LAST; BUTLAST]);;

let LBIGAUX_MW_CMP_3 = prove
 (`!a1 a2 a3 b1 b2 b3:N word.
     mw_cmp [a1;a2;a3] [b1;b2;b3] =
     if a3 = b3 then mw_cmp [a1;a2] [b1;b2] else SOME (word_ult a3 b3)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [mw_cmp_def] THEN REWRITE_TAC[NOT_CONS_NIL; LAST; BUTLAST]);;

let mc_cmp3_thm = prove
 (`!r1 r2 r3 r9 r10 r11:N word.
     mc_cmp3_pre (r1,r2,r3,r9,r10,r11) /\
     mc_cmp3 (r1,r2,r3,r9,r10,r11) =
       ((if mw_cmp [r9;r10;r11] [r1;r2;r3] = SOME T then word 1 else word 0),
        r1,r2,r3,r9,r10,r11)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mc_cmp3_def; mc_cmp3_pre_def; LET_DEF; LET_END_DEF; COND_ID] THEN
  REWRITE_TAC[LBIGAUX_MW_CMP_3; LBIGAUX_MW_CMP_2] THEN
  ASM_CASES_TAC `r11:N word = r3` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r10:N word = r2` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r9:N word = r1` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let mc_cmp_mul2,mc_cmp_mul2_pre,mc_cmp_mul2_def,mc_cmp_mul2_pre_def =
  LBIGAUX_tailrec_define "mc_cmp_mul2" (CASE_TERM
  `((\(r6,r7,r8,r9,r10,r11).
      (let cnd = mc_mul_by_single2_pre (r6,r7,r8) in
       match mc_mul_by_single2 (r6,r7,r8) with (r1,r2,r3,r6,r7,r8) ->
       match mc_cmp3 (r1,r2,r3,r9,r10,r11) with (r0,r1,r2,r3,r9,r10,r11) ->
         (INR (r0,r6,r7,r8,r9,r10,r11),cnd)))
   :N word#N word#N word#N word#N word#N word ->
    ((N word#N word#N word#N word#N word#N word) +
     (N word#N word#N word#N word#N word#N word#N word))#bool)`);;

let mc_cmp_mul2_thm = prove
 (`!r6 r7 r8 r9 r10 r11:N word.
     mc_cmp_mul2_pre (r6,r7,r8,r9,r10,r11) /\
     mc_cmp_mul2 (r6,r7,r8,r9,r10,r11) =
       ((if mw_cmp [r9;r10;r11] (mw_mul_by_single r6 [r7; r8]) = SOME T
         then word 1 else word 0),r6,r7,r8,r9,r10,r11)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mc_cmp_mul2_def; mc_cmp_mul2_pre_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(SPECL [`r6:N word`; `r7:N word`; `r8:N word`] mc_mul_by_single2_thm) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[mc_cmp3_thm] THEN CASE_REWRITE_TAC[]);;

let mc_sub1,mc_sub1_pre,mc_sub1_def,mc_sub1_pre_def =
  LBIGAUX_tailrec_define "mc_sub1"
  `((\r6. if r6 = word 0 then (INR r6,T)
          else (let r6 = word_sub r6 (word 1) in (INR r6,T)))
   :N word -> ((N word) + (N word))#bool)`;;

let mc_sub1_thm = prove
 (`!r6:N word. mc_sub1_pre r6 /\ mc_sub1 r6 = word (val r6 - 1)`,
  GEN_TAC THEN REWRITE_TAC[mc_sub1_def; mc_sub1_pre_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0; SUB_0] THEN
  SUBGOAL_THEN `1 <= val (r6:N word)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(r6:N word = word 0)` THEN REWRITE_TAC[GSYM VAL_EQ_0] THEN ARITH_TAC;
    ASM_SIMP_TAC[WORD_SUB; WORD_VAL]]);;

let mc_cmp2,mc_cmp2_pre,mc_cmp2_def,mc_cmp2_pre_def =
  LBIGAUX_tailrec_define "mc_cmp2"
  `((\(r0,r2,r10,r11).
      (let r1 = word 1 in
         if r2 = r11 then
           if r0 = r10 then (let r1 = word 0 in (INR (r0,r1,r2,r10,r11),T))
           else if word_ult r10 r0 then (INR (r0,r1,r2,r10,r11),T)
           else (let r1 = word 0 in (INR (r0,r1,r2,r10,r11),T))
         else if word_ult r11 r2 then (INR (r0,r1,r2,r10,r11),T)
         else (let r1 = word 0 in (INR (r0,r1,r2,r10,r11),T))))
   :N word#N word#N word#N word ->
    ((N word#N word#N word#N word) + (N word#N word#N word#N word#N word))#bool)`;;

let mc_cmp2_thm = prove
 (`!r0 r2 r10 r11:N word.
     mc_cmp2_pre (r0,r2,r10,r11) /\
     mc_cmp2 (r0,r2,r10,r11) =
       (r0,(if mw_cmp [r10;r11] [r0;r2] = SOME T then word 1 else word 0),r2,r10,r11)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mc_cmp2_def; mc_cmp2_pre_def; LET_DEF; LET_END_DEF; COND_ID] THEN
  REWRITE_TAC[LBIGAUX_MW_CMP_2] THEN
  ASM_CASES_TAC `r11:N word = r2` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r10:N word = r0` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let mc_div_test,mc_div_test_pre,mc_div_test_def,mc_div_test_pre_def =
  LBIGAUX_tailrec_define "mc_div_test" (CASE_TERM
  `((\(l,r6,r7,r8,r9,r10,r11).
      (let cnd = mc_cmp_mul2_pre (r6,r7,r8,r9,r10,r11) in
       match mc_cmp_mul2 (r6,r7,r8,r9,r10,r11) with (r0,r6,r7,r8,r9,r10,r11) ->
         if r0 = word 0 then (INR (l,r6,r7,r8,r9,r10,r11),cnd)
         else
           (let r6 = mc_sub1 r6 in
            let r0 = r6 in
            let r1 = word 0 in
            let r2 = r8 in
            let r3 = r1 in
            let cnd = (cnd /\ mc_single_mul_add_pre (r0,r1,r2,r3)) in
            match mc_single_mul_add (r0,r1,r2,r3) with (r0,r1,r2,r3) ->
            let r2 = word_add r2 (word 1) in
            match mc_cmp2 (r0,r2,r10,r11) with (r0,r1,r2,r10,r11) ->
              if r1 = word 0 then (INR (l,r6,r7,r8,r9,r10,r11),cnd)
              else (INL (l - 1,r6,r7,r8,r9,r10,r11),(cnd /\ ~(l = 0))))))
   :num#N word#N word#N word#N word#N word#N word ->
    ((num#N word#N word#N word#N word#N word#N word) +
     (num#N word#N word#N word#N word#N word#N word))#bool)`);;

let LBIGAUX_SINGLE_MUL_ADD_00 = prove
 (`!x y:N word. single_mul_add x y (word 0) (word 0) = single_mul x y (word 0)`,
  REPEAT GEN_TAC THEN
  LBIG_PAIR_TAC `single_mul_add (x:N word) y (word 0) (word 0)` `a:N word` `b:N word` THEN
  LBIG_PAIR_TAC `single_mul (x:N word) y (word 0)` `c:N word` `d:N word` THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN MATCH_MP_TAC LBIGAUX_DIGITS_UNIQUE THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP single_mul_thm) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP single_mul_add_thm) THEN
  REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES] THEN ARITH_TAC);;

let LBIGAUX_MW_ADD_0_1 = prove
 (`!r0 r2:N word. FST (mw_add [r0;r2] [word 0;word 1] F) = [r0; word_add r2 (word 1)]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LBIGAUX_MW_ADD_CONS; mw_add_def; FST; SND] THEN
  REWRITE_TAC[single_add_def; multiword_b2w_def; BITVAL_CLAUSES; WORD_ADD_0; VAL_WORD_0;
              ADD_CLAUSES; GSYM NOT_LT; w2n_lt; FST; SND; CONS_11]);;

let mc_div_test_lemma = prove
 (`!(q:N word) u1 u2 u3 v1 v2 l.
     val q <= l
     ==> ?l2. mc_div_test_pre (l,q,v2,v1,u3,u2,u1) /\
              mc_div_test (l,q,v2,v1,u3,u2,u1) =
                (l2,mw_div_test q u1 u2 u3 v1 v2,v2,v1,u3,u2,u1) /\
              l <= l2 + val q`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; GSYM RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC (REWRITE_RULE[RIGHT_FORALL_IMP_THM] mw_div_test_ind) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN X_GEN_TAC `l:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[mc_div_test_def; mc_div_test_pre_def] THEN
  ONCE_REWRITE_TAC[mw_div_test_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; mc_cmp_mul2_thm] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `mw_cmp [u3:N word;u2;u1] (mw_mul_by_single (q:N word) [v2;v1]) = SOME T` THEN
  ASM_REWRITE_TAC[GSYM LBIGAUX_WORD_NOT_ZERO_ONE] THENL
   [ALL_TAC; EXISTS_TAC `l:num` THEN ARITH_TAC] THEN
  SUBGOAL_THEN `1 <= val (q:N word)` ASSUME_TAC THENL
   [UNDISCH_TAC `mw_cmp [u3:N word;u2;u1] (mw_mul_by_single (q:N word) [v2;v1]) = SOME T` THEN
    SUBGOAL_THEN `LENGTH [u3:N word;u2;u1] = LENGTH (mw_mul_by_single (q:N word) [v2;v1])`
      (fun th -> REWRITE_TAC[MATCH_MP LBIGAUX_MW_CMP_SOME_T th]) THENL
     [REWRITE_TAC[LENGTH_mw_mul_by_single; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[mw_mul_by_single_lemma] THEN
    ASM_CASES_TAC `val (q:N word) = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; LT] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mc_sub1_thm; mc_single_mul_add_thm; GSYM LBIGAUX_SINGLE_MUL_ADD_00] THEN
  LBIG_PAIR_TAC `single_mul_add (word (val (q:N word) - 1):N word) v1 (word 0) (word 0)`
    `x1:N word` `x2:N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[mc_cmp2_thm; FST; SND; LBIGAUX_MW_ADD_0_1] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `mw_cmp [u2:N word;u1] [x1; word_add x2 (word 1)] = SOME T` THEN
  ASM_REWRITE_TAC[GSYM LBIGAUX_WORD_NOT_ZERO_ONE] THENL
   [ALL_TAC; EXISTS_TAC `l:num` THEN ARITH_TAC] THEN
  SUBGOAL_THEN `val (word (val (q:N word) - 1):N word) = val q - 1` ASSUME_TAC THENL
   [MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN MP_TAC(ISPEC `q:N word` w2n_lt) THEN ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`word (val (q:N word) - 1):N word`;
    `single_mul (word (val (q:N word) - 1):N word) v1 (word 0)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM LBIGAUX_SINGLE_MUL_ADD_00; FST; SND; LBIGAUX_MW_ADD_0_1];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `l - 1`) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `l2:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let mc_div_test_thm = prove
 (`!(q:N word) u1 u2 u3 v1 v2 l.
     dimword(:N) <= l
     ==> ?l2. mc_div_test_pre (l,q,v2,v1,u3,u2,u1) /\
              mc_div_test (l,q,v2,v1,u3,u2,u1) =
                (l2,mw_div_test q u1 u2 u3 v1 v2,v2,v1,u3,u2,u1) /\
              l <= l2 + dimword(:N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`q:N word`; `u1:N word`; `u2:N word`; `u3:N word`; `v1:N word`; `v2:N word`;
    `l:num`] mc_div_test_lemma) THEN
  ANTS_TAC THENL [MP_TAC(ISPEC `q:N word` w2n_lt) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `l2:num` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `q:N word` w2n_lt) THEN ASM_ARITH_TAC);;

let LBIGAUX_WORD_NOT_0 = prove
 (`word_not (word 0):N word = word (dimword(:N) - 1)`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_NOT; VAL_WORD_0; SUB_0; dimword_def] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  MP_TAC ZERO_LT_dimword THEN REWRITE_TAC[dimword_def] THEN ARITH_TAC);;

let LBIGAUX_SINGLE_DIV_PRE = prove
 (`!(x1:N word) x2 y. single_div_pre x1 x2 y <=> word_ult x1 y`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`x2:N word`; `x1:N word`; `y:N word`] mc_single_div_thm) THEN
  REWRITE_TAC[mc_single_div_pre_def; LET_DEF; LET_END_DEF] THEN
  LBIG_PAIR_TAC `single_div (x1:N word) x2 y` `q:N word` `r:N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN SIMP_TAC[]);;

let mc_div_r1,mc_div_r1_pre,mc_div_r1_def,mc_div_r1_pre_def =
  LBIGAUX_tailrec_define "mc_div_r1" (CASE_TERM
  `((\(r0,r1,r2).
      if word_ult r2 r1 then
        (let cnd = single_div_pre r2 r0 r1 in
         match single_div r2 r0 r1 with (r0,r2) -> (INR (r0,r1,r2),cnd))
      else (let r0 = word 0 in let r0 = word_not r0 in (INR (r0,r1,r2),T)))
   :N word#N word#N word -> ((N word#N word#N word) + (N word#N word#N word))#bool)`);;

let mc_div_r1_thm = prove
 (`!r0 r1 r2:N word.
     mc_div_r1 (r0,r1,r2) =
       if word_ult r2 r1 then
         (FST (single_div r2 r0 r1),r1,SND (single_div r2 r0 r1))
       else (word_not (word 0),r1,r2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mc_div_r1_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  LBIG_PAIR_TAC `single_div (r2:N word) r0 r1` `q:N word` `r:N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[FST; SND]);;

let mc_div_guess,mc_div_guess_pre,mc_div_guess_def,mc_div_guess_pre_def =
  LBIGAUX_tailrec_define "mc_div_guess" (CASE_TERM
  `((\(l,r7,r8,r9,r10,r11).
      (let r0 = r10 in
       let r1 = r8 in
       let r2 = r11 in
       let cnd = mc_div_r1_pre (r0,r1,r2) in
       match mc_div_r1 (r0,r1,r2) with (r0,r1,r2) ->
       let r6 = r0 in
       let cnd = (cnd /\ mc_div_test_pre (l - 1,r6,r7,r8,r9,r10,r11) /\ ~(l = 0)) in
       match mc_div_test (l - 1,r6,r7,r8,r9,r10,r11) with (l,r6,r7,r8,r9,r10,r11) ->
         (INR (l,r6,r7,r8,r9,r10,r11),cnd)))
   :num#N word#N word#N word#N word#N word ->
    ((num#N word#N word#N word#N word#N word) +
     (num#N word#N word#N word#N word#N word#N word))#bool)`);;

let mc_div_guess_thm = prove
 (`!(u1:N word) u2 u3 v1 v2 (us:(N word)list) (vs:(N word)list) l.
     dimword(:N) + 1 <= l
     ==> ?l2. (mc_div_guess_pre (l,v2,v1,u3,u2,u1) <=> (word_ult u1 v1 ==> ~(v1 = word 0))) /\
              mc_div_guess (l,v2,v1,u3,u2,u1) =
                (l2,mw_div_guess (CONS u1 (CONS u2 (CONS u3 us))) (CONS v1 (CONS v2 vs)),
                 v2,v1,u3,u2,u1) /\
              l <= l2 + dimword(:N) + 1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mc_div_guess_def; mc_div_guess_pre_def; LET_DEF; LET_END_DEF; mc_div_r1_thm;
              mc_div_r1_pre_def] THEN
  REWRITE_TAC[mw_div_guess_def; LET_DEF; LET_END_DEF; HD; TL; GSYM WORD_ULT;
              LBIGAUX_WORD_NOT_0] THEN
  ASM_CASES_TAC `word_ult (u1:N word) v1` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LBIGAUX_SINGLE_DIV_PRE] THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`FST (single_div (u1:N word) u2 v1)`; `u1:N word`; `u2:N word`; `u3:N word`;
      `v1:N word`; `v2:N word`; `l - 1`] mc_div_test_thm);
    MP_TAC(SPECL [`word (dimword(:N) - 1):N word`; `u1:N word`; `u2:N word`; `u3:N word`;
      `v1:N word`; `v2:N word`; `l - 1`] mc_div_test_thm)] THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   EXISTS_TAC `l2:num` THEN REWRITE_TAC[] THEN
   CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC]) THEN
  TRY(LBIG_PAIR_TAC `single_div (u1:N word) u2 v1` `q0:N word` `rr0:N word` THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THEN
  (SUBGOAL_THEN `~(l = 0) /\ (word_ult (u1:N word) v1 ==> ~(v1 = word 0))` MP_TAC THENL
    [CONJ_TAC THENL
      [ASM_ARITH_TAC; REWRITE_TAC[WORD_ULT; GSYM VAL_EQ_0; VAL_WORD_0] THEN ARITH_TAC];
     ASM_MESON_TAC[]]));;

(* ------------------------------------------------------------------------- *)
(* division: adjusting the guess and subtracting                            *)
(* ------------------------------------------------------------------------- *)

let mc_adj_cmp,mc_adj_cmp_pre,mc_adj_cmp_def,mc_adj_cmp_pre_def =
  LBIGAUX_tailrec_define "mc_adj_cmp"
  `((\(r0,r3,r8).
      if r0 = r3 then (INR (r0,r3,r8),T)
      else
        (let r8 = word 1 in
           if word_ult r3 r0 then (INR (r0,r3,r8),T)
           else (let r8 = word 0 in (INR (r0,r3,r8),T))))
   :N word#N word#N word -> ((N word#N word#N word) + (N word#N word#N word))#bool)`;;

let mc_adjust_aux,mc_adjust_aux_pre,mc_adjust_aux_def,mc_adjust_aux_pre_def =
  LBIGAUX_tailrec_define "mc_adjust_aux" (CASE_TERM
  `((\(l,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs).
      if r9 = r11 then
        (let r0 = r12 in
         let cnd = val r10 < LENGTH zs in
         let r3 = EL (val r10) zs in
         let r10 = word_add r10 (word 1) in
         match mc_adj_cmp (r0,r3,r8) with (r0,r3,r8) ->
           (INR (l,r6,r7,r8,r9,r10,r11,ys,zs),cnd))
      else
        (let r0 = r6 in
         let cnd = val r11 < LENGTH ys in
         let r2 = EL (val r11) ys in
         let cnd = (cnd /\ mc_single_mul_pre (r0,r1,r2)) in
         match mc_single_mul (r0,r1,r2) with (r0,r1,r2) ->
         let r1 = r12 in
         let r12 = r2 in
         let r2 = r0 in
         let r0 = r7 in
         let cnd = (cnd /\ mc_single_mul_pre (r0,r1,r2)) in
         match mc_single_mul (r0,r1,r2) with (r0,r1,r2) ->
         let r1 = r12 in
         let r12 = r2 in
         let cnd = (cnd /\ val r10 < LENGTH zs) in
         let r3 = EL (val r10) zs in
         match mc_adj_cmp (r0,r3,r8) with (r0,r3,r8) ->
         let r11 = word_add r11 (word 1) in
         let r10 = word_add r10 (word 1) in
           (INL (l - 1,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs),(cnd /\ ~(l = 0)))))
   :num#N word#N word#N word#N word#N word#N word#N word#N word#(N word)list#(N word)list ->
    ((num#N word#N word#N word#N word#N word#N word#N word#N word#(N word)list#(N word)list) +
     (num#N word#N word#N word#N word#N word#N word#(N word)list#(N word)list))#bool)`);;

let mc_div_adjust,mc_div_adjust_pre,mc_div_adjust_def,mc_div_adjust_pre_def =
  LBIGAUX_tailrec_define "mc_div_adjust" (CASE_TERM
  `((\(l,r6,r7,r9,r10,ys,zs).
      (let r1 = word 0 in
       let r8 = r1 in
       let r11 = r1 in
       let r12 = r1 in
       let cnd = (mc_adjust_aux_pre (l - 1,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs) /\ ~(l = 0)) in
       match mc_adjust_aux (l - 1,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs) with
         (l,r6,r7,r8,r9,r10,r11,ys,zs) ->
         if r7 = word 0 then (INR (l,r6,r7,r9,r10,r11,ys,zs),cnd)
         else if r8 = word 0 then (INR (l,r6,r7,r9,r10,r11,ys,zs),cnd)
         else (let r7 = word_sub r7 (word 1) in (INR (l,r6,r7,r9,r10,r11,ys,zs),cnd))))
   :num#N word#N word#N word#N word#(N word)list#(N word)list ->
    ((num#N word#N word#N word#N word#(N word)list#(N word)list) +
     (num#N word#N word#N word#N word#N word#(N word)list#(N word)list))#bool)`);;

let mc_div_sub,mc_div_sub_pre,mc_div_sub_def,mc_div_sub_pre_def =
  LBIGAUX_tailrec_define "mc_div_sub" (CASE_TERM
  `((\(r0,r3,r8).
      (let cnd = (~(r8 = word 0) ==> r8 = word 1) in
       match single_sub_word r3 r0 r8 with (r3,r8) ->
         (INR (r0,r3,r8),cnd)))
   :N word#N word#N word -> ((N word#N word#N word) + (N word#N word#N word))#bool)`);;

let mc_div_sub_loop,mc_div_sub_loop_pre,mc_div_sub_loop_def,mc_div_sub_loop_pre_def =
  LBIGAUX_tailrec_define "mc_div_sub_loop" (CASE_TERM
  `((\(l,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs).
      if r9 = r11 then
        (let r0 = r12 in
         let cnd = val r10 < LENGTH zs in
         let r3 = EL (val r10) zs in
         let cnd = (cnd /\ mc_div_sub_pre (r0,r3,r8)) in
         match mc_div_sub (r0,r3,r8) with (r0,r3,r8) ->
         let r1 = r3 in
         let zs = LUPDATE r1 (val r10) zs in
         let r10 = word_add r10 (word 1) in
           (INR (l,r6,r7,r9,r10,r11,ys,zs),cnd))
      else
        (let r0 = r6 in
         let cnd = val r11 < LENGTH ys in
         let r2 = EL (val r11) ys in
         let cnd = (cnd /\ mc_single_mul_pre (r0,r1,r2)) in
         match mc_single_mul (r0,r1,r2) with (r0,r1,r2) ->
         let r1 = r12 in
         let r12 = r2 in
         let r2 = r0 in
         let r0 = r7 in
         let cnd = (cnd /\ mc_single_mul_pre (r0,r1,r2)) in
         match mc_single_mul (r0,r1,r2) with (r0,r1,r2) ->
         let r1 = r12 in
         let r12 = r2 in
         let cnd = (cnd /\ val r10 < LENGTH zs) in
         let r3 = EL (val r10) zs in
         let cnd = (cnd /\ mc_div_sub_pre (r0,r3,r8)) in
         match mc_div_sub (r0,r3,r8) with (r0,r3,r8) ->
         let r0 = r1 in
         let r1 = r3 in
         let zs = LUPDATE r1 (val r10) zs in
         let r1 = r0 in
         let r11 = word_add r11 (word 1) in
         let r10 = word_add r10 (word 1) in
           (INL (l - 1,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs),(cnd /\ ~(l = 0)))))
   :num#N word#N word#N word#N word#N word#N word#N word#N word#(N word)list#(N word)list ->
    ((num#N word#N word#N word#N word#N word#N word#N word#N word#(N word)list#(N word)list) +
     (num#N word#N word#N word#N word#N word#(N word)list#(N word)list))#bool)`);;

let mc_adj_cmp_thm = prove
 (`!(r1:N word) h anything res.
     mc_adj_cmp_pre (r1,h,anything) /\
     mc_adj_cmp (r1,h,(if res = SOME T then word 1 else word 0)) =
       (r1,h,(if mw_cmp_alt [h] [r1] res = SOME T then word 1 else word 0))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mc_adj_cmp_def; mc_adj_cmp_pre_def; mw_cmp_alt_def; HD; TL; LET_DEF;
              LET_END_DEF; COND_ID] THEN
  ASM_CASES_TAC `(r1:N word) = h` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "option"; injectivity "option"]);;

let mc_div_sub_thm = prove
 (CASE_TERM
  `!(r0:N word) r3 c.
     mc_div_sub_pre (r0,r3,b2w c) /\
     mc_div_sub (r0,r3,b2w c) = (match single_sub r3 r0 c with (r3,c) -> (r0,r3,b2w c))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mc_div_sub_def; mc_div_sub_pre_def; LET_DEF; LET_END_DEF;
              LBIGAUX_SINGLE_SUB_WORD_B2W; LBIGAUX_B2W_01] THEN
  CASE_REWRITE_TAC[] THEN
  LBIG_PAIR_TAC `single_sub (r3:N word) r0 c` `a:N word` `b:bool` THEN
  ASM_REWRITE_TAC[FST; SND] THEN CASE_REWRITE_TAC[]);;

let LBIGAUX_MW_CMP_ALT_CONS = prove
 (`!(z:N word) zs q qs res.
     mw_cmp_alt (CONS z zs) (CONS q qs) res = mw_cmp_alt zs qs (mw_cmp_alt [z] [q] res)`,
  REWRITE_TAC[mw_cmp_alt_def; HD; TL]);;

let LBIGAUX_MC_ADJUST_AUX = prove
 (`!(ys:(N word)list) (zs:(N word)list) (ys1:(N word)list) (zs1:(N word)list)
     (zs2:(N word)list) res (r1:N word) (r12:N word) l.
     LENGTH zs = LENGTH ys + 1 /\ LENGTH (APPEND ys1 ys) < dimword(:N) /\
     LENGTH (APPEND zs1 zs) < dimword(:N) /\ LENGTH ys <= l
     ==> ?l2.
       mc_adjust_aux_pre (l,r1,r6,r7,(if res = SOME T then word 1 else word 0),
         word (LENGTH (APPEND ys1 ys)),word (LENGTH zs1),word (LENGTH ys1),
         r12,APPEND ys1 ys,APPEND zs1 (APPEND zs zs2)) /\
       mc_adjust_aux (l,r1,r6,r7,(if res = SOME T then word 1 else word 0),
         word (LENGTH (APPEND ys1 ys)),word (LENGTH zs1),word (LENGTH ys1),
         r12,APPEND ys1 ys,APPEND zs1 (APPEND zs zs2)) =
         (l2,r6,r7,
          (if mw_cmp_alt zs (mw_mul_by_single2 r6 r7 ys r1 r12) res = SOME T
           then word 1 else word 0),
          word (LENGTH (APPEND ys1 ys)),word (LENGTH (APPEND zs1 zs)),
          word (LENGTH (APPEND ys1 ys)),APPEND ys1 ys,APPEND zs1 (APPEND zs zs2)) /\
       l <= l2 + LENGTH ys`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `zs:(N word)list` THEN
  LBIG_CONS_CASES_TAC `zs:(N word)list` `z:N word` `zs':(N word)list` THEN
  REWRITE_TAC[LENGTH; ADD_CLAUSES; NOT_SUC; GSYM NOT_SUC; SUC_INJ; LENGTH_EQ_NIL;
              ARITH_RULE `~(0 = 1)`; ARITH_RULE `SUC n = 1 <=> n = 0`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH; APPEND_NIL]) THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[APPEND_NIL; APPEND; LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
    ONCE_REWRITE_TAC[mc_adjust_aux_def; mc_adjust_aux_pre_def] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    SUBGOAL_THEN `val (word (LENGTH (zs1:(N word)list)):N word) = LENGTH zs1` SUBST1_TAC THENL
     [MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LBIGAUX_EL_LENGTH_CONS; mc_adj_cmp_thm; mw_mul_by_single2_def] THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[word_add_n2w; LENGTH_APPEND; LENGTH; GSYM ADD1] THEN
    EXISTS_TAC `l:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(word (LENGTH (ys1:(N word)list) + SUC (LENGTH (t:(N word)list))):N word =
                  word (LENGTH ys1)) /\
                val (word (LENGTH (ys1:(N word)list)):N word) = LENGTH ys1 /\
                val (word (LENGTH (zs1:(N word)list)):N word) = LENGTH zs1`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [W(fun (_,w) -> MP_TAC(SPECL [rand(lhs(rand w)); rand(rhs(rand w))]
         (INST_TYPE [`:N`,`:N`] LBIGAUX_WORD_EQ_LT))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ARITH_TAC];
      MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; APPEND] THEN
  ONCE_REWRITE_TAC[mc_adjust_aux_def; mc_adjust_aux_pre_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; LBIGAUX_EL_LENGTH_CONS] THEN
  REWRITE_TAC[mc_single_mul_thm] THEN
  LBIG_PAIR_TAC `single_mul_add (r6:N word) h r1 (word 0)` `q1:N word` `q2:N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  LBIG_PAIR_TAC `single_mul_add (r7:N word) q1 r12 (word 0)` `q3:N word` `q4:N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[mc_adj_cmp_thm] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[word_add_n2w; mw_mul_by_single2_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ISPECL [`z:N word`; `zs':(N word)list`; `q3:N word`;
    `mw_mul_by_single2 (r6:N word) r7 t q2 q4`; `res:bool option`] LBIGAUX_MW_CMP_ALT_CONS] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`zs':(N word)list`; `SNOC (h:N word) ys1`;
    `SNOC (z:N word) zs1`; `zs2:(N word)list`; `mw_cmp_alt [z:N word] [q3] res`;
    `q2:N word`; `q4:N word`; `l - 1`]) THEN
  REWRITE_TAC[LENGTH_SNOC; SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH;
              GSYM ADD1; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[GSYM ADD1] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l3:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `l3:num` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN ASM_ARITH_TAC);;

let mc_adjust_aux_thm = prove
 (`!(ys:(N word)list) (zs:(N word)list) (zs1:(N word)list) (zs2:(N word)list) l.
     LENGTH zs = LENGTH ys + 1 /\ LENGTH ys < dimword(:N) /\
     LENGTH (APPEND zs1 zs) < dimword(:N) /\ LENGTH ys <= l
     ==> ?l2.
       mc_adjust_aux_pre (l,word 0,r6,r7,word 0,word (LENGTH ys),word (LENGTH zs1),word 0,
         word 0,ys,APPEND zs1 (APPEND zs zs2)) /\
       mc_adjust_aux (l,word 0,r6,r7,word 0,word (LENGTH ys),word (LENGTH zs1),word 0,
         word 0,ys,APPEND zs1 (APPEND zs zs2)) =
         (l2,r6,r7,
          (if mw_cmp_alt zs (mw_mul_by_single2 r6 r7 ys (word 0) (word 0)) NONE = SOME T
           then word 1 else word 0),
          word (LENGTH ys),word (LENGTH (APPEND zs1 zs)),word (LENGTH ys),ys,
          APPEND zs1 (APPEND zs zs2)) /\
       l <= l2 + LENGTH ys`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`ys:(N word)list`; `zs:(N word)list`; `[]:(N word)list`; `zs1:(N word)list`;
    `zs2:(N word)list`; `NONE:bool option`; `word 0:N word`; `word 0:N word`; `l:num`]
    LBIGAUX_MC_ADJUST_AUX) THEN
  REWRITE_TAC[APPEND; LENGTH; distinctness "option"]);;

let LBIGAUX_WORD_SUB1_VAL = prove
 (`!w:N word. ~(w = word 0) ==> word_sub w (word 1) = word (val w - 1)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN `1 <= val (w:N word)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_SUB; WORD_VAL]);;

let mc_div_adjust_thm = prove
 (`!(ys:(N word)list) (zs:(N word)list) (zs1:(N word)list) (zs2:(N word)list) r6 r7 l.
     LENGTH zs = LENGTH ys + 1 /\ LENGTH ys < dimword(:N) /\
     LENGTH (APPEND zs1 zs) < dimword(:N) /\ LENGTH ys + 1 <= l
     ==> ?l2.
       mc_div_adjust_pre (l,r6,r7,word (LENGTH ys),word (LENGTH zs1),ys,
         APPEND zs1 (APPEND zs zs2)) /\
       mc_div_adjust (l,r6,r7,word (LENGTH ys),word (LENGTH zs1),ys,
         APPEND zs1 (APPEND zs zs2)) =
         (l2,r6,mw_div_adjust r7 zs (BUTLAST (mw_mul_by_single r6 ys)),
          word (LENGTH ys),word (LENGTH (APPEND zs1 zs)),word (LENGTH ys),ys,
          APPEND zs1 (APPEND zs zs2)) /\
       l <= l2 + LENGTH ys + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mc_div_adjust_def; mc_div_adjust_pre_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(SPECL [`ys:(N word)list`; `zs:(N word)list`; `zs1:(N word)list`; `zs2:(N word)list`;
    `l - 1`] mc_adjust_aux_thm) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mw_cmp_alt (zs:(N word)list) (mw_mul_by_single2 r6 r7 ys (word 0) (word 0)) NONE =
                mw_cmp zs (mw_mul_by_single r7 (BUTLAST (mw_mul_by_single r6 ys)))`
    SUBST1_TAC THENL
   [REWRITE_TAC[mw_mul_by_single2_thm] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC mw_cmp_alt_thm THEN
    ASM_REWRITE_TAC[LENGTH_mw_mul_by_single] THEN
    SUBGOAL_THEN `~(mw_mul_by_single (r6:N word) ys = [])` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_mw_mul_by_single] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LENGTH_FRONT; LENGTH_mw_mul_by_single] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[mw_div_adjust_def] THEN
  EXISTS_TAC `l2:num` THEN
  ASM_CASES_TAC `r7:N word = word 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[VAL_WORD_0; SUB_0; COND_ID] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `mw_cmp (zs:(N word)list)
    (mw_mul_by_single r7 (BUTLAST (mw_mul_by_single (r6:N word) ys))) = SOME T` THEN
  ASM_REWRITE_TAC[GSYM LBIGAUX_WORD_NOT_ZERO_ONE] THEN
  ASM_SIMP_TAC[LBIGAUX_WORD_SUB1_VAL] THEN ASM_ARITH_TAC);;

let LBIGAUX_MC_DIV_SUB_LOOP = prove
 (`!(ys:(N word)list) (zs:(N word)list) (ys1:(N word)list) (zs1:(N word)list)
     (zs2:(N word)list) c (r1:N word) (r12:N word) l.
     LENGTH zs = LENGTH ys + 1 /\ LENGTH (APPEND ys1 ys) < dimword(:N) /\
     LENGTH (APPEND zs1 zs) < dimword(:N) /\ LENGTH ys <= l
     ==> ?l2.
       mc_div_sub_loop_pre (l,r1,r6,r7,b2w c,
         word (LENGTH (APPEND ys1 ys)),word (LENGTH zs1),word (LENGTH ys1),
         r12,APPEND ys1 ys,APPEND zs1 (APPEND zs zs2)) /\
       mc_div_sub_loop (l,r1,r6,r7,b2w c,
         word (LENGTH (APPEND ys1 ys)),word (LENGTH zs1),word (LENGTH ys1),
         r12,APPEND ys1 ys,APPEND zs1 (APPEND zs zs2)) =
         (l2,r6,r7,word (LENGTH (APPEND ys1 ys)),word (LENGTH (APPEND zs1 zs)),
          word (LENGTH (APPEND ys1 ys)),APPEND ys1 ys,
          APPEND zs1 (APPEND (FST (mw_sub zs (mw_mul_by_single2 r6 r7 ys r1 r12) c)) zs2)) /\
       l <= l2 + LENGTH ys`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `zs:(N word)list` THEN
  LBIG_CONS_CASES_TAC `zs:(N word)list` `z:N word` `zs':(N word)list` THEN
  REWRITE_TAC[LENGTH; ADD_CLAUSES; NOT_SUC; GSYM NOT_SUC; SUC_INJ; LENGTH_EQ_NIL;
              ARITH_RULE `~(0 = 1)`; ARITH_RULE `SUC n = 1 <=> n = 0`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH; APPEND_NIL]) THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[APPEND_NIL; APPEND; LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
    ONCE_REWRITE_TAC[mc_div_sub_loop_def; mc_div_sub_loop_pre_def] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    SUBGOAL_THEN `val (word (LENGTH (zs1:(N word)list)):N word) = LENGTH zs1` SUBST1_TAC THENL
     [MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LBIGAUX_EL_LENGTH_CONS; mc_div_sub_thm; mw_mul_by_single2_def] THEN
    LBIG_PAIR_TAC `single_sub (z:N word) r12 c` `d:N word` `c1:bool` THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[LUPDATE_LENGTH; mw_sub_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[word_add_n2w; LENGTH_APPEND; LENGTH; GSYM ADD1; APPEND; FST] THEN
    EXISTS_TAC `l:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(word (LENGTH (ys1:(N word)list) + SUC (LENGTH (t:(N word)list))):N word =
                  word (LENGTH ys1)) /\
                val (word (LENGTH (ys1:(N word)list)):N word) = LENGTH ys1 /\
                val (word (LENGTH (zs1:(N word)list)):N word) = LENGTH zs1`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [W(fun (_,w) -> MP_TAC(SPECL [rand(lhs(rand w)); rand(rhs(rand w))]
         (INST_TYPE [`:N`,`:N`] LBIGAUX_WORD_EQ_LT))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ARITH_TAC];
      MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; APPEND] THEN
  ONCE_REWRITE_TAC[mc_div_sub_loop_def; mc_div_sub_loop_pre_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; LBIGAUX_EL_LENGTH_CONS] THEN
  REWRITE_TAC[mc_single_mul_thm] THEN
  LBIG_PAIR_TAC `single_mul_add (r6:N word) h r1 (word 0)` `q1:N word` `q2:N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  LBIG_PAIR_TAC `single_mul_add (r7:N word) q1 r12 (word 0)` `q3:N word` `q4:N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[mc_div_sub_thm] THEN
  LBIG_PAIR_TAC `single_sub (z:N word) q3 c` `d:N word` `c1:bool` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LUPDATE_LENGTH; word_add_n2w; mw_mul_by_single2_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[LBIGAUX_MW_SUB_CONS; FST; SND] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`zs':(N word)list`; `SNOC (h:N word) ys1`;
    `SNOC (d:N word) zs1`; `zs2:(N word)list`; `c1:bool`;
    `q2:N word`; `q4:N word`; `l - 1`]) THEN
  REWRITE_TAC[LENGTH_SNOC; SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH;
              GSYM ADD1; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[GSYM ADD1] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l3:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `l3:num` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN ASM_ARITH_TAC);;

let mc_div_sub_loop_thm = prove
 (`!(ys:(N word)list) (zs:(N word)list) (zs1:(N word)list) (zs2:(N word)list) l.
     LENGTH zs = LENGTH ys + 1 /\ LENGTH ys < dimword(:N) /\
     LENGTH (APPEND zs1 zs) < dimword(:N) /\ LENGTH ys <= l
     ==> ?l2.
       mc_div_sub_loop_pre (l,word 0,r6,r7,word 1,word (LENGTH ys),word (LENGTH zs1),
         word 0,word 0,ys,APPEND zs1 (APPEND zs zs2)) /\
       mc_div_sub_loop (l,word 0,r6,r7,word 1,word (LENGTH ys),word (LENGTH zs1),
         word 0,word 0,ys,APPEND zs1 (APPEND zs zs2)) =
         (l2,r6,r7,word (LENGTH ys),word (LENGTH (APPEND zs1 zs)),word (LENGTH ys),ys,
          APPEND zs1 (APPEND (FST (mw_sub zs (mw_mul_by_single2 r6 r7 ys (word 0) (word 0)) T))
            zs2)) /\
       l <= l2 + LENGTH ys`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`ys:(N word)list`; `zs:(N word)list`; `[]:(N word)list`; `zs1:(N word)list`;
    `zs2:(N word)list`; `T`; `word 0:N word`; `word 0:N word`; `l:num`]
    LBIGAUX_MC_DIV_SUB_LOOP) THEN
  REWRITE_TAC[APPEND; LENGTH; multiword_b2w_def; BITVAL_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* division: the main loop (mw_div_aux)                                      *)
(* ------------------------------------------------------------------------- *)

let mc_div_loop,mc_div_loop_pre,mc_div_loop_def,mc_div_loop_pre_def =
  LBIGAUX_tailrec_define "mc_div_loop" (CASE_TERM
  `((\(l,r7,r9,r10,r11,r14,r15,ys,zs).
      if r10 = word 0 then (INR (l,r7,r9,r10,r11,r14,r15,ys,zs),T)
      else
        (let r6 = r14 in
         let r3 = r15 in
         let r14 = r7 in
         let r15 = r9 in
         let r16 = r10 in
         let r10 = word_add r10 r9 in
         let r10 = word_sub r10 (word 1) in
         let cnd = val r10 < LENGTH zs in
         let r0 = EL (val r10) zs in
         let r10 = word_sub r10 (word 1) in
         let cnd = (cnd /\ val r10 < LENGTH zs) in
         let r1 = EL (val r10) zs in
         let r10 = word_sub r10 (word 1) in
         let cnd = (cnd /\ val r10 < LENGTH zs) in
         let r2 = EL (val r10) zs in
         let r11 = r0 in
         let r10 = r1 in
         let r9 = r2 in
         let r7 = r3 in
         let r8 = r6 in
         let cnd = (cnd /\ mc_div_guess_pre (l,r7,r8,r9,r10,r11)) in
         match mc_div_guess (l,r7,r8,r9,r10,r11) with (l,r6,r7,r8,r9,r10,r11) ->
         let r0 = r6 in
         let r6 = r14 in
         let r9 = r15 in
         let r10 = r16 in
         let r10 = word_sub r10 (word 1) in
         let r15 = r7 in
         let r14 = r8 in
         let r7 = r0 in
         let cnd = (cnd /\ mc_div_adjust_pre (l,r6,r7,r9,r10,ys,zs)) in
         match mc_div_adjust (l,r6,r7,r9,r10,ys,zs) with (l,r6,r7,r9,r10,r11,ys,zs) ->
         let r10 = word_sub r10 r9 in
         let r10 = word_sub r10 (word 1) in
         let r1 = word 0 in
         let r8 = r1 in
         let r8 = word 1 in
         let r11 = r1 in
         let r12 = r1 in
         let cnd = (cnd /\ mc_div_sub_loop_pre (l - 1,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs) /\
                    ~(l = 0)) in
         match mc_div_sub_loop (l - 1,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs) with
           (l,r6,r7,r9,r10,r11,ys,zs) ->
         let r10 = word_sub r10 (word 1) in
         let cnd = (cnd /\ val r10 < LENGTH zs) in
         let zs = LUPDATE r7 (val r10) zs in
         let r10 = word_sub r10 r9 in
         let r7 = r6 in
           (INL (l - 1,r7,r9,r10,r11,r14,r15,ys,zs),(cnd /\ ~(l = 0)))))
   :num#N word#N word#N word#N word#N word#N word#(N word)list#(N word)list ->
    ((num#N word#N word#N word#N word#N word#N word#(N word)list#(N word)list) +
     (num#N word#N word#N word#N word#N word#N word#(N word)list#(N word)list))#bool)`);;

let LBIGAUX_WORD_SUB_EQ = prove
 (`!a b c. b + c = a ==> word_sub (word a) (word b):N word = word c`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[LBIGAUX_WORD_ADD_SUB_L]);;


let LBIGAUX_MW_DIV_AUX_SNOC = prove
 (CASE_TERM
  `!(x:N word) zs1 zs ys.
     mw_div_aux (SNOC x zs1) zs ys =
     (let q = mw_div_adjust (mw_div_guess (REVERSE (CONS x zs)) (REVERSE ys)) (CONS x zs) ys in
      match mw_div_aux zs1 (BUTLAST (FST (mw_sub (CONS x zs) (mw_mul_by_single q ys) T))) ys
      with (qs,rs) -> (CONS q qs,rs))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [mw_div_aux_def] THEN
  REWRITE_TAC[NOT_SNOC_NIL; LAST_SNOC; FRONT_SNOC; LET_DEF; LET_END_DEF]);;

let LBIGAUX_LAST3 = prove
 (`!w:A list. 3 <= LENGTH w ==> ?w0 a3 a2 a1. w = APPEND w0 [a3;a2;a1]`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP LESS_EQ_LENGTH_ALT) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`w0:A list`; `t:A list`] THEN
  REWRITE_TAC[ARITH_RULE `3 = SUC (SUC (SUC 0))`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN MESON_TAC[]);;

let LBIGAUX_LAST2 = prove
 (`!w:A list. 2 <= LENGTH w ==> ?w0 a2 a1. w = APPEND w0 [a2;a1]`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP LESS_EQ_LENGTH_ALT) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`w0:A list`; `t:A list`] THEN
  REWRITE_TAC[ARITH_RULE `2 = SUC (SUC 0)`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN MESON_TAC[]);;

let LBIGAUX_APPEND2_SNOC = prove
 (`!(w0:A list) a2 a1. APPEND w0 [a2;a1] = SNOC a1 (SNOC a2 w0)`,
  REWRITE_TAC[SNOC_APPEND; GSYM APPEND_ASSOC; APPEND]);;

let LBIGAUX_LAST_APPEND2 = prove
 (`!(w0:A list) a2 a1. LAST (APPEND w0 [a2;a1]) = a1 /\
                       LAST (BUTLAST (APPEND w0 [a2;a1])) = a2 /\
                       REVERSE (APPEND w0 [a2;a1]) = CONS a1 (CONS a2 (REVERSE w0))`,
  REWRITE_TAC[LBIGAUX_APPEND2_SNOC; LAST_SNOC; FRONT_SNOC; REVERSE_SNOC]);;

let LBIGAUX_APPEND3_SNOC = prove
 (`!(w0:A list) a3 a2 a1. APPEND w0 [a3;a2;a1] = SNOC a1 (SNOC a2 (SNOC a3 w0))`,
  REWRITE_TAC[SNOC_APPEND; GSYM APPEND_ASSOC; APPEND]);;

let LBIGAUX_EL_APPEND_CONS3 = prove
 (`!(p:A list) a b c r.
     EL (LENGTH p) (APPEND p (CONS a (CONS b (CONS c r)))) = a /\
     EL (LENGTH p + 1) (APPEND p (CONS a (CONS b (CONS c r)))) = b /\
     EL (LENGTH p + 2) (APPEND p (CONS a (CONS b (CONS c r)))) = c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EL_APPEND] THEN
  REWRITE_TAC[LT_REFL; ARITH_RULE `~(n + 1 < n) /\ ~(n + 2 < n)`; ADD_SUB2; SUB_REFL] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0 /\ 2 = SUC (SUC 0)`; EL; HD; TL]);;

let LBIGAUX_MC_DIV_LOOP = prove
 ((CASE_TERM `!(ys1:(N word)list).
     ys1 = BUTLAST (mw_mul_by_single d ys)
     ==> !(zs1:(N word)list) (zs:(N word)list) (zs2:(N word)list) l.
       LENGTH zs = LENGTH ys /\ LENGTH (APPEND zs1 (APPEND zs zs2)) < dimword(:N) /\
       1 < LENGTH ys /\ ~(LAST ys1 = word 0) /\
       LENGTH zs1 * (dimword(:N) + 2 * LENGTH ys + 4) <= l
       ==> ?l2.
         mc_div_loop_pre (l,d,word (LENGTH ys),word (LENGTH zs1),word (LENGTH ys),
           LAST ys1,LAST (BUTLAST ys1),ys,APPEND zs1 (APPEND zs zs2)) /\
         mc_div_loop (l,d,word (LENGTH ys),word (LENGTH zs1),word (LENGTH ys),
           LAST ys1,LAST (BUTLAST ys1),ys,APPEND zs1 (APPEND zs zs2)) =
           (l2,d,word (LENGTH ys),word 0,word (LENGTH ys),LAST ys1,LAST (BUTLAST ys1),ys,
            (match mw_div_aux zs1 zs ys1 with (qs,rs) -> APPEND rs (APPEND (REVERSE qs) zs2))) /\
         l <= l2 + LENGTH zs1 * (dimword(:N) + 2 * LENGTH ys + 4)`),
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SNOC_INDUCT THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[mc_div_loop_def; mc_div_loop_pre_def] THEN
    GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV o LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
      [mw_div_aux_def] THEN
    REWRITE_TAC[LENGTH; APPEND; REVERSE; MULT_CLAUSES; ADD_CLAUSES] THEN
    EXISTS_TAC `l:num` THEN REWRITE_TAC[LE_REFL] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[APPEND; REVERSE];
    ALL_TAC] THEN
  X_GEN_TAC `zs1:(N word)list` THEN DISCH_THEN(LABEL_TAC "ih") THEN
  X_GEN_TAC `x:N word` THEN
  MAP_EVERY X_GEN_TAC [`zs:(N word)list`; `zs2:(N word)list`; `l:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (ys1:(N word)list) = LENGTH (ys:(N word)list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(mw_mul_by_single (d:N word) ys = [])` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_mw_mul_by_single] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LENGTH_FRONT; LENGTH_mw_mul_by_single] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `ys1:(N word)list` LBIGAUX_LAST2) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`y0:(N word)list`; `b2:N word`; `b1:N word`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `LAST (ys1:(N word)list) = b1 /\ LAST (BUTLAST ys1) = b2 /\
                REVERSE ys1 = CONS b1 (CONS b2 (REVERSE y0))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ys1:(N word)list = APPEND y0 [b2;b1]` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LBIGAUX_LAST_APPEND2]; ALL_TAC] THEN
  MP_TAC(ISPEC `CONS (x:N word) zs` LBIGAUX_LAST3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`w0:(N word)list`; `a3:N word`; `a2:N word`; `a1:N word`] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `ys1:(N word)list = APPEND y0 [b2;b1]` THEN DISCH_THEN(K ALL_TAC) THEN
  UNDISCH_TAC `ys1 = BUTLAST (mw_mul_by_single (d:N word) ys)` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  UNDISCH_TAC `CONS (x:N word) zs = APPEND w0 [a3;a2;a1]` THEN
  DISCH_THEN(LABEL_TAC "win") THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_SNOC; LENGTH_APPEND; LENGTH]) THEN
  SUBGOAL_THEN `LENGTH (w0:(N word)list) + 2 = LENGTH (ys:(N word)list)` ASSUME_TAC THENL
   [USE_THEN "win" (MP_TAC o AP_TERM `LENGTH:(N word)list->num`) THEN
    REWRITE_TAC[LENGTH; LENGTH_APPEND] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. APPEND (zs1:(N word)list) (CONS x (APPEND zs t)) =
        APPEND (APPEND zs1 w0) (CONS a3 (CONS a2 (CONS a1 t)))`
   ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM APPEND] THEN USE_THEN "win" SUBST1_TAC THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
  REWRITE_TAC[LBIGAUX_MW_DIV_AUX_SNOC; LENGTH_SNOC] THEN
  REWRITE_TAC[SNOC_APPEND; GSYM APPEND_ASSOC; APPEND] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall (concl th) &&
    free_in `a3:N word` (concl th))) THEN
  REMOVE_THEN "win" (K ALL_TAC) THEN
  SUBGOAL_THEN
   `EL (LENGTH (zs1:(N word)list) + LENGTH (ys:(N word)list) - 2)
       (APPEND zs1 (APPEND w0 (CONS (a3:N word) (CONS a2 (CONS a1 zs2))))) = a3 /\
    EL (LENGTH (zs1:(N word)list) + LENGTH (ys:(N word)list) - 1)
       (APPEND zs1 (APPEND w0 (CONS (a3:N word) (CONS a2 (CONS a1 zs2))))) = a2 /\
    EL (LENGTH (zs1:(N word)list) + LENGTH (ys:(N word)list))
       (APPEND zs1 (APPEND w0 (CONS (a3:N word) (CONS a2 (CONS a1 zs2))))) = a1`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[APPEND_ASSOC] THEN
    SUBGOAL_THEN `LENGTH (zs1:(N word)list) + LENGTH (ys:(N word)list) - 2 =
                  LENGTH (APPEND zs1 (w0:(N word)list)) /\
                  LENGTH (zs1:(N word)list) + LENGTH (ys:(N word)list) - 1 =
                  LENGTH (APPEND zs1 (w0:(N word)list)) + 1 /\
                  LENGTH (zs1:(N word)list) + LENGTH (ys:(N word)list) =
                  LENGTH (APPEND zs1 (w0:(N word)list)) + 2`
      (fun th -> REWRITE_TAC[th; LBIGAUX_EL_APPEND_CONS3]) THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `SUC (LENGTH (zs1:(N word)list)) + LENGTH (ys:(N word)list) +
                LENGTH (zs2:(N word)list) < dimword(:N)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(word (SUC (LENGTH (zs1:(N word)list))):N word = word 0) /\
    word_sub (word_add (word (SUC (LENGTH zs1))) (word (LENGTH (ys:(N word)list)))) (word 1):N word =
      word (LENGTH zs1 + LENGTH ys) /\
    word_sub (word (LENGTH zs1 + LENGTH ys)) (word 1):N word =
      word (LENGTH zs1 + LENGTH ys - 1) /\
    word_sub (word (LENGTH zs1 + LENGTH ys - 1)) (word 1):N word =
      word (LENGTH zs1 + LENGTH ys - 2) /\
    val (word (LENGTH zs1 + LENGTH ys):N word) = LENGTH zs1 + LENGTH ys /\
    val (word (LENGTH zs1 + LENGTH ys - 1):N word) = LENGTH zs1 + LENGTH ys - 1 /\
    val (word (LENGTH zs1 + LENGTH ys - 2):N word) = LENGTH zs1 + LENGTH ys - 2 /\
    word_sub (word (SUC (LENGTH zs1))) (word 1):N word = word (LENGTH zs1) /\
    word_sub (word_sub (word (LENGTH zs1 + LENGTH ys + 1)) (word (LENGTH ys))) (word 1):N word =
      word (LENGTH zs1) /\
    word_sub (word (LENGTH zs1 + LENGTH ys + 1)) (word 1):N word =
      word (LENGTH zs1 + LENGTH ys) /\
    word_sub (word (LENGTH zs1 + LENGTH ys)) (word (LENGTH ys)):N word = word (LENGTH zs1)`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[word_add_n2w; LBIGAUX_WORD_SUC_SUB1] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC LBIGAUX_WORD_SUC_NZ THEN ASM_ARITH_TAC) THEN
    TRY(MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_ARITH_TAC) THEN
    TRY(MATCH_MP_TAC LBIGAUX_WORD_SUB_EQ THEN ASM_ARITH_TAC) THEN
    SUBGOAL_THEN `word_sub (word (LENGTH (zs1:(N word)list) + LENGTH (ys:(N word)list) + 1))
                   (word (LENGTH ys)):N word = word (LENGTH zs1 + 1)` SUBST1_TAC THENL
     [MATCH_MP_TAC LBIGAUX_WORD_SUB_EQ THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LBIGAUX_WORD_ADD1_SUB1];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[mc_div_loop_def; mc_div_loop_pre_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  MP_TAC(SPECL [`a1:N word`; `a2:N word`; `a3:N word`; `b1:N word`; `b2:N word`;
    `REVERSE (w0:(N word)list)`; `REVERSE (y0:(N word)list)`; `l:num`] mc_div_guess_thm) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `SUC (LENGTH (zs1:(N word)list)) * (dimword(:N) + 2 * LENGTH (ys:(N word)list) + 4) <= l` THEN
    REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `REVERSE (APPEND w0 [a3;a2;a1]) =
                CONS (a1:N word) (CONS a2 (CONS a3 (REVERSE w0)))` SUBST1_TAC THENL
   [REWRITE_TAC[LBIGAUX_APPEND3_SNOC; REVERSE_SNOC]; ALL_TAC] THEN
  ABBREV_TAC `q0 = mw_div_guess (CONS (a1:N word) (CONS a2 (CONS a3 (REVERSE w0))))
                                (CONS b1 (CONS b2 (REVERSE y0)))` THEN
  ABBREV_TAC `q1 = mw_div_adjust (q0:N word) (APPEND w0 [a3;a2;a1]) ys1` THEN
  SUBGOAL_THEN `LENGTH (APPEND (zs1:(N word)list) (APPEND w0 [a3;a2;a1:N word])) =
                LENGTH zs1 + LENGTH (ys:(N word)list) + 1` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`ys:(N word)list`; `APPEND w0 [a3;a2;a1:N word]`; `zs1:(N word)list`;
    `zs2:(N word)list`; `d:N word`; `q0:N word`; `l2:num`] mc_div_adjust_thm) THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
    UNDISCH_TAC `SUC (LENGTH (zs1:(N word)list)) * (dimword(:N) + 2 * LENGTH (ys:(N word)list) + 4) <= l` THEN
    REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l3:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(INST [`d:N word`,`r6:N word`; `q1:N word`,`r7:N word`]
   (SPECL [`ys:(N word)list`; `APPEND w0 [a3;a2;a1:N word]`; `zs1:(N word)list`;
    `zs2:(N word)list`; `l3 - 1`] mc_div_sub_loop_thm)) THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; mw_mul_by_single2_thm] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
    UNDISCH_TAC `SUC (LENGTH (zs1:(N word)list)) * (dimword(:N) + 2 * LENGTH (ys:(N word)list) + 4) <= l` THEN
    REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l4:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?s sub0. FST (mw_sub (APPEND w0 [a3;a2;a1]) (mw_mul_by_single (q1:N word) ys1) T) =
                         SNOC s sub0 /\ LENGTH (sub0:(N word)list) = LENGTH (ys:(N word)list)`
   STRIP_ASSUME_TAC THENL
   [LBIG_PAIR_TAC `mw_sub (APPEND w0 [a3;a2;a1:N word]) (mw_mul_by_single (q1:N word) ys1) T`
      `sb:(N word)list` `cb:bool` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LENGTH_mw_sub) THEN ASM_REWRITE_TAC[FST] THEN
    MP_TAC(ISPEC `sb:(N word)list` SNOC_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `s:N word` (X_CHOOSE_THEN `sub0:(N word)list` SUBST1_TAC))) THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH; LENGTH_SNOC] THENL
     [ARITH_TAC; DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`s:N word`; `sub0:(N word)list`] THEN
      ASM_ARITH_TAC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FRONT_SNOC] THEN
  SUBGOAL_THEN `LUPDATE (q1:N word) (LENGTH (zs1:(N word)list) + LENGTH (ys:(N word)list))
                  (APPEND zs1 (APPEND (SNOC s sub0) zs2)) = APPEND zs1 (APPEND sub0 (CONS q1 zs2))`
    SUBST1_TAC THENL
   [REWRITE_TAC[SNOC_APPEND; GSYM APPEND_ASSOC; APPEND] THEN
    ONCE_REWRITE_TAC[APPEND_ASSOC] THEN
    SUBGOAL_THEN `LENGTH (zs1:(N word)list) + LENGTH (ys:(N word)list) =
                  LENGTH (APPEND zs1 (sub0:(N word)list))` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_APPEND]; ALL_TAC] THEN
    REWRITE_TAC[LUPDATE_LENGTH]; ALL_TAC] THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`sub0:(N word)list`; `CONS (q1:N word) zs2`; `l4 - 1`]) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
    UNDISCH_TAC `SUC (LENGTH (zs1:(N word)list)) * (dimword(:N) + 2 * LENGTH (ys:(N word)list) + 4) <= l` THEN
    REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l5:num` STRIP_ASSUME_TAC) THEN
  LBIG_PAIR_TAC `mw_div_aux (zs1:(N word)list) sub0 ys1` `qs0:(N word)list` `rs0:(N word)list` THEN
  UNDISCH_TAC `mw_div_aux (zs1:(N word)list) sub0 ys1 = qs0,rs0` THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o REWRITE_RULE[th]) THEN
                       ASSUME_TAC th) THEN
  SUBGOAL_THEN `~(b1:N word = word 0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  EXISTS_TAC `l5:num` THEN ASM_REWRITE_TAC[REVERSE; GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; LENGTH_SNOC] THEN
  UNDISCH_TAC `SUC (LENGTH (zs1:(N word)list)) * (dimword(:N) + 2 * LENGTH (ys:(N word)list) + 4) <= l` THEN
  REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC);;

let mc_div_loop_thm = prove
 (CASE_TERM
  `!(zs1:(N word)list) (zs:(N word)list) (zs2:(N word)list) l.
     LENGTH zs = LENGTH ys /\ LENGTH (APPEND zs1 (APPEND zs zs2)) < dimword(:N) /\
     1 < LENGTH ys /\ ~(LAST (BUTLAST (mw_mul_by_single d ys)) = word 0) /\
     LENGTH zs1 * (dimword(:N) + 2 * LENGTH ys + 4) <= l
     ==> ?l2.
       let ys1 = BUTLAST (mw_mul_by_single d ys) in
         mc_div_loop_pre (l,d,word (LENGTH ys),word (LENGTH zs1),word (LENGTH ys),
           LAST ys1,LAST (BUTLAST ys1),ys,APPEND zs1 (APPEND zs zs2)) /\
         mc_div_loop (l,d,word (LENGTH ys),word (LENGTH zs1),word (LENGTH ys),
           LAST ys1,LAST (BUTLAST ys1),ys,APPEND zs1 (APPEND zs zs2)) =
           (l2,d,word (LENGTH ys),word 0,word (LENGTH ys),LAST ys1,LAST (BUTLAST ys1),ys,
            (match mw_div_aux zs1 zs ys1 with (qs,rs) -> APPEND rs (APPEND (REVERSE qs) zs2))) /\
         l <= l2 + LENGTH zs1 * (dimword(:N) + 2 * LENGTH ys + 4)`,
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  MP_TAC(SPEC `BUTLAST (mw_mul_by_single (d:N word) ys)` LBIGAUX_MC_DIV_LOOP) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* division: multiplying by d, the top two digits, copying, and mc_div       *)
(* ------------------------------------------------------------------------- *)

let mc_mul_by_single,mc_mul_by_single_pre,mc_mul_by_single_def,mc_mul_by_single_pre_def =
  LBIGAUX_tailrec_define "mc_mul_by_single" (CASE_TERM
  `((\(l,r1,r8,r9,r10,r11,xs,zs).
      if r9 = r11 then
        (let cnd = val r10 < LENGTH zs in
         let zs = LUPDATE r1 (val r10) zs in
         let r10 = word_add r10 (word 1) in
           (INR (l,r1,r8,r9,r10,xs,zs),cnd))
      else
        (let cnd = val r11 < LENGTH xs in
         let r2 = EL (val r11) xs in
         let r0 = r8 in
         let r3 = word 0 in
         let cnd = (cnd /\ mc_single_mul_add_pre (r0,r1,r2,r3)) in
         match mc_single_mul_add (r0,r1,r2,r3) with (r0,r1,r2,r3) ->
         let cnd = (cnd /\ val r10 < LENGTH zs) in
         let zs = LUPDATE r0 (val r10) zs in
         let r1 = r2 in
         let r10 = word_add r10 (word 1) in
         let r11 = word_add r11 (word 1) in
           (INL (l - 1,r1,r8,r9,r10,r11,xs,zs),(cnd /\ ~(l = 0)))))
   :num#N word#N word#N word#N word#N word#(N word)list#(N word)list ->
    ((num#N word#N word#N word#N word#N word#(N word)list#(N word)list) +
     (num#N word#N word#N word#N word#(N word)list#(N word)list))#bool)`);;

let mc_top_two,mc_top_two_pre,mc_top_two_def,mc_top_two_pre_def =
  LBIGAUX_tailrec_define "mc_top_two" (CASE_TERM
  `((\(l,r0,r1,r3,r8,r9,r11,ys).
      if r9 = r11 then (let r1 = r3 in (INR (l,r0,r1,r8,r9,r11,ys),T))
      else
        (let r3 = r0 in
         let cnd = val r11 < LENGTH ys in
         let r2 = EL (val r11) ys in
         let r0 = r8 in
         let cnd = (cnd /\ mc_single_mul_pre (r0,r1,r2)) in
         match mc_single_mul (r0,r1,r2) with (r0,r1,r2) ->
         let r1 = r2 in
         let r11 = word_add r11 (word 1) in
           (INL (l - 1,r0,r1,r3,r8,r9,r11,ys),(cnd /\ ~(l = 0)))))
   :num#N word#N word#N word#N word#N word#N word#(N word)list ->
    ((num#N word#N word#N word#N word#N word#N word#(N word)list) +
     (num#N word#N word#N word#N word#N word#(N word)list))#bool)`);;

let mc_copy_down,mc_copy_down_pre,mc_copy_down_def,mc_copy_down_pre_def =
  LBIGAUX_tailrec_define "mc_copy_down"
  `((\(l,r8,r10,r11,zs).
      if r8 = word 0 then (INR (l,zs),T)
      else
        (let cnd = val r10 < LENGTH zs in
         let r0 = EL (val r10) zs in
         let r8 = word_sub r8 (word 1) in
         let r10 = word_add r10 (word 1) in
         let cnd = (cnd /\ val r11 < LENGTH zs) in
         let zs = LUPDATE r0 (val r11) zs in
         let r11 = word_add r11 (word 1) in
           (INL (l - 1,r8,r10,r11,zs),(cnd /\ ~(l = 0)))))
   :num#N word#N word#N word#(N word)list ->
    ((num#N word#N word#N word#(N word)list) + (num#(N word)list))#bool)`;;

let mc_copy_over,mc_copy_over_pre,mc_copy_over_def,mc_copy_over_pre_def =
  LBIGAUX_tailrec_define "mc_copy_over"
  `((\(l,r10,xs,zs).
      if r10 = word 0 then (INR (l,xs,zs),T)
      else
        (let r10 = word_sub r10 (word 1) in
         let cnd = val r10 < LENGTH xs in
         let r0 = EL (val r10) xs in
         let cnd = (cnd /\ val r10 < LENGTH zs) in
         let zs = LUPDATE r0 (val r10) zs in
           (INL (l - 1,r10,xs,zs),(cnd /\ ~(l = 0)))))
   :num#N word#(N word)list#(N word)list ->
    ((num#N word#(N word)list#(N word)list) + (num#(N word)list#(N word)list))#bool)`;;

let mc_div0,mc_div0_pre,mc_div0_def,mc_div0_pre_def =
  LBIGAUX_tailrec_define "mc_div0" (CASE_TERM
  `((\(l,r0,r1,r3,xs,ys,zs).
      (let r6 = r0 in
         if r3 = word 0 then
           (let r0 = word 0 in (INR (l,r0,r3,r6,xs,ys,zs),T))
         else
           (let r11 = r0 in
            let r10 = r1 in
            let r0 = word 0 in
            let cnd = (mc_mul_zero_pre (l - 1,r0,r10,zs) /\ ~(l = 0)) in
            match mc_mul_zero (l - 1,r0,r10,zs) with (l,r10,zs) ->
            let r10 = r11 in
            let cnd = (cnd /\ mc_copy_over_pre (l - 1,r10,xs,zs) /\ ~(l = 0)) in
            match mc_copy_over (l - 1,r10,xs,zs) with (l,xs,zs) ->
            let r0 = r1 in
              (INR (l,r0,r3,r6,xs,ys,zs),cnd))))
   :num#N word#N word#N word#(N word)list#(N word)list#(N word)list ->
    ((num#N word#N word#N word#(N word)list#(N word)list#(N word)list) +
     (num#N word#N word#N word#(N word)list#(N word)list#(N word)list))#bool)`);;

let mc_div1,mc_div1_pre,mc_div1_def,mc_div1_pre_def =
  LBIGAUX_tailrec_define "mc_div1" (CASE_TERM
  `((\(l,r0,r1,r3,xs,ys,zs).
      (let r14 = r3 in
       let r2 = word 0 in
       let r10 = r2 in
       let cnd = val r10 < LENGTH ys in
       let r9 = EL (val r10) ys in
       let r10 = r0 in
       let r8 = r0 in
       let cnd = (cnd /\ mc_simple_div_pre (l - 1,r2,r9,r10,xs,zs) /\ ~(l = 0)) in
       match mc_simple_div (l - 1,r2,r9,r10,xs,zs) with (l,r2,r9,r10,xs,zs) ->
       let r6 = word 0 in
       let r0 = r8 in
       let r3 = r14 in
         if r3 = word 0 then
           if r2 = word 0 then (INR (l,r0,r3,r6,xs,ys,zs),cnd)
           else (let r6 = word 1 in (INR (l,r0,r3,r6,xs,ys,zs),cnd))
         else
           (let r0 = word 1 in
            let r10 = word 0:N word in
            let cnd = (cnd /\ val r10 < LENGTH zs) in
            let zs = LUPDATE r2 (val r10) zs in
              if r2 = word 0 then (INR (l,r0,r3,r6,xs,ys,zs),cnd)
              else (let r6 = word 1 in (INR (l,r0,r3,r6,xs,ys,zs),cnd)))))
   :num#N word#N word#N word#(N word)list#(N word)list#(N word)list ->
    ((num#N word#N word#N word#(N word)list#(N word)list#(N word)list) +
     (num#N word#N word#N word#(N word)list#(N word)list#(N word)list))#bool)`);;

let mc_div2,mc_div2_pre,mc_div2_def,mc_div2_pre_def =
  LBIGAUX_tailrec_define "mc_div2" (CASE_TERM
  `((\(l,r7,r8,r10,r11,r18,xs,ys,zs).
      (let r9 = r7 in
       let r2 = word 0 in
       let cnd = (mc_simple_div1_pre (l - 1,r2,r9,r10,zs) /\ ~(l = 0)) in
       match mc_simple_div1 (l - 1,r2,r9,r10,zs) with (l,r2,r9,r10,zs) ->
       let r9 = r11 in
       let r10 = r9 in
       let r7 = r8 in
       let cnd = (cnd /\ mc_fix_pre (l - 1,r8,r10,zs) /\ ~(l = 0)) in
       match mc_fix (l - 1,r8,r10,zs) with (l,r8,r10,zs) ->
       let r6 = r10 in
       let r10 = r9 in
       let r3 = r18 in
       let r8 = r7 in
         if r3 = word 0 then
           (let r11 = word 0 in
            let cnd = (cnd /\ mc_copy_down_pre (l - 1,r8,r10,r11,zs) /\ ~(l = 0)) in
            match mc_copy_down (l - 1,r8,r10,r11,zs) with (l,zs) ->
            let r0 = r7 in
              (INR (l,r0,r3,r6,xs,ys,zs),cnd))
         else (let r0 = r9 in (INR (l,r0,r3,r6,xs,ys,zs),cnd))))
   :num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list ->
    ((num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list) +
     (num#N word#N word#N word#(N word)list#(N word)list#(N word)list))#bool)`);;

let mc_div3,mc_div3_pre,mc_div3_def,mc_div3_pre_def =
  LBIGAUX_tailrec_define "mc_div3" (CASE_TERM
  `((\(l,r2,r7,r9,r18,r19,xs,ys,zs).
      (let r1 = word 0 in
       let r8 = r2 in
       let r10 = r1 in
       let r11 = r1 in
       let cnd = (mc_mul_by_single_pre (l - 1,r1,r8,r9,r10,r11,xs,zs) /\ ~(l = 0)) in
       match mc_mul_by_single (l - 1,r1,r8,r9,r10,r11,xs,zs) with (l,r1,r8,r9,r10,xs,zs) ->
       let r1 = word 0 in
       let cnd = (cnd /\ val r10 < LENGTH zs) in
       let zs = LUPDATE r1 (val r10) zs in
       let r0 = word 0 in
       let r1 = r0 in
       let r3 = r0 in
       let r11 = r0 in
       let r9 = r7 in
       let cnd = (cnd /\ mc_top_two_pre (l - 1,r0,r1,r3,r8,r9,r11,ys) /\ ~(l = 0)) in
       match mc_top_two (l - 1,r0,r1,r3,r8,r9,r11,ys) with (l,r0,r1,r8,r9,r11,ys) ->
       let r7 = r8 in
       let r11 = r9 in
       let r10 = r19 in
       let r10 = word_sub r10 r9 in
       let r10 = word_add r10 (word 2) in
       let r14 = r0 in
       let r15 = r1 in
       let r17 = r10 in
       let cnd = (cnd /\ mc_div_loop_pre (l - 1,r7,r9,r10,r11,r14,r15,ys,zs) /\ ~(l = 0)) in
       match mc_div_loop (l - 1,r7,r9,r10,r11,r14,r15,ys,zs) with
         (l,r7,r9,r10,r11,r14,r15,ys,zs) ->
       let r8 = r17 in
       let r11 = r9 in
       let r10 = r9 in
       let cnd = (cnd /\ mc_div2_pre (l,r7,r8,r10,r11,r18,xs,ys,zs)) in
       match mc_div2 (l,r7,r8,r10,r11,r18,xs,ys,zs) with (l,r0,r3,r6,xs,ys,zs) ->
         (INR (l,r0,r3,r6,xs,ys,zs),cnd)))
   :num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list ->
    ((num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list) +
     (num#N word#N word#N word#(N word)list#(N word)list#(N word)list))#bool)`);;

let mc_div,mc_div_pre,mc_div_def,mc_div_pre_def =
  LBIGAUX_tailrec_define "mc_div" (CASE_TERM
  `((\(l,r0,r1,r3,xs,ys,zs).
      if word_ult r0 r1 then
        (let cnd = mc_div0_pre (l,r0,r1,r3,xs,ys,zs) in
         match mc_div0 (l,r0,r1,r3,xs,ys,zs) with (l,r0,r3,r6,xs,ys,zs) ->
           (INR (l,r0,r3,r6,xs,ys,zs),cnd))
      else if r1 = word 1 then
        (let cnd = mc_div1_pre (l,r0,r1,r3,xs,ys,zs) in
         match mc_div1 (l,r0,r1,r3,xs,ys,zs) with (l,r0,r3,r6,xs,ys,zs) ->
           (INR (l,r0,r3,r6,xs,ys,zs),cnd))
      else
        (let r18 = r3 in
         let r19 = r0 in
         let r7 = r1 in
         let r9 = r0 in
         let r10 = r1 in
         let r10 = word_sub r10 (word 1) in
         let cnd = val r10 < LENGTH ys in
         let r1 = EL (val r10) ys in
         let r2 = word 1 in
         let cnd = (cnd /\ mc_calc_d_pre (l - 1,r1,r2) /\ ~(l = 0)) in
         match mc_calc_d (l - 1,r1,r2) with (l,r2) ->
         let cnd = (cnd /\ mc_div3_pre (l,r2,r7,r9,r18,r19,xs,ys,zs)) in
         match mc_div3 (l,r2,r7,r9,r18,r19,xs,ys,zs) with (l,r0,r3,r6,xs,ys,zs) ->
           (INR (l,r0,r3,r6,xs,ys,zs),cnd)))
   :num#N word#N word#N word#(N word)list#(N word)list#(N word)list ->
    ((num#N word#N word#N word#(N word)list#(N word)list#(N word)list) +
     (num#N word#N word#N word#(N word)list#(N word)list#(N word)list))#bool)`);;

let LBIGAUX_MC_MUL_BY_SINGLE = prove
 (`!(ys:(N word)list) (ys1:(N word)list) (x:N word) (zs:(N word)list) (k:N word)
     (zs1:(N word)list) (zs2:(N word)list) (z2:N word) l.
     LENGTH (APPEND ys1 ys) < dimword(:N) /\ LENGTH zs = LENGTH ys /\
     LENGTH (APPEND zs1 zs) < dimword(:N) /\ LENGTH ys <= l
     ==> ?r1 l2.
           mc_mul_by_single_pre (l,k,x,word (LENGTH (APPEND ys1 ys)),word (LENGTH zs1),
             word (LENGTH ys1),APPEND ys1 ys,APPEND zs1 (APPEND zs (CONS z2 zs2))) /\
           mc_mul_by_single (l,k,x,word (LENGTH (APPEND ys1 ys)),word (LENGTH zs1),
             word (LENGTH ys1),APPEND ys1 ys,APPEND zs1 (APPEND zs (CONS z2 zs2))) =
             (l2,r1,x,word (LENGTH (APPEND ys1 ys)),word (LENGTH (APPEND zs1 zs) + 1),
              APPEND ys1 ys,
              APPEND zs1 (APPEND (mw_mul_pass x ys (MAP (K (word 0)) ys) k) zs2)) /\
           l <= l2 + LENGTH ys`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ONCE_REWRITE_TAC[mc_mul_by_single_def; mc_mul_by_single_pre_def] THEN
    REWRITE_TAC[APPEND_NIL; APPEND; mw_mul_pass_def; MAP; LET_DEF; LET_END_DEF] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL]) THEN
    SUBGOAL_THEN `val (word (LENGTH (zs1:(N word)list)):N word) = LENGTH zs1` SUBST1_TAC THENL
     [MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LUPDATE_LENGTH; LENGTH_APPEND; LENGTH; word_add_n2w] THEN
    MAP_EVERY EXISTS_TAC [`k:N word`; `l:num`] THEN REWRITE_TAC[ADD_CLAUSES; LE_REFL] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `ys1:(N word)list` THEN X_GEN_TAC `x:N word` THEN X_GEN_TAC `zs:(N word)list` THEN
  LBIG_CONS_CASES_TAC `zs:(N word)list` `z:N word` `zs':(N word)list` THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH]) THEN
  SUBGOAL_THEN `~(word (LENGTH (ys1:(N word)list) + SUC (LENGTH (t:(N word)list))):N word =
                  word (LENGTH ys1)) /\
                val (word (LENGTH (ys1:(N word)list)):N word) = LENGTH ys1 /\
                val (word (LENGTH (zs1:(N word)list)):N word) = LENGTH zs1`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [W(fun (_,w) -> MP_TAC(SPECL [rand(lhs(rand w)); rand(rhs(rand w))]
         (INST_TYPE [`:N`,`:N`] LBIGAUX_WORD_EQ_LT))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ARITH_TAC];
      MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; APPEND] THEN
  ONCE_REWRITE_TAC[mc_mul_by_single_def; mc_mul_by_single_pre_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; LBIGAUX_EL_LENGTH_CONS; mc_single_mul_add_thm] THEN
  LBIG_PAIR_TAC `single_mul_add (x:N word) h k (word 0)` `x1:N word` `x2:N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LUPDATE_LENGTH; word_add_n2w; mw_mul_pass_def; MAP; K_THM; HD; TL] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`SNOC (h:N word) ys1`; `x:N word`; `zs':(N word)list`;
    `x2:N word`; `SNOC (x1:N word) zs1`; `zs2:(N word)list`; `z2:N word`; `l - 1`]) THEN
  REWRITE_TAC[LENGTH_SNOC; SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH;
              GSYM ADD1; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:N word` (X_CHOOSE_THEN `l2:num` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r1:N word`; `l2:num`] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN ASM_ARITH_TAC);;


let mc_mul_by_single_thm = prove
 (`!(xs:(N word)list) (x:N word) (zs:(N word)list) (zs2:(N word)list) (z2:N word) l.
     LENGTH xs < dimword(:N) /\ LENGTH zs = LENGTH xs /\ LENGTH zs < dimword(:N) /\
     LENGTH xs <= l
     ==> ?r1 l2.
       mc_mul_by_single_pre (l,word 0,x,word (LENGTH xs),word 0,word 0,xs,
         APPEND zs (CONS z2 zs2)) /\
       mc_mul_by_single (l,word 0,x,word (LENGTH xs),word 0,word 0,xs,
         APPEND zs (CONS z2 zs2)) =
         (l2,r1,x,word (LENGTH xs),word (LENGTH zs + 1),xs,
          APPEND (mw_mul_by_single x xs) zs2) /\
       l <= l2 + LENGTH xs`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`xs:(N word)list`; `[]:(N word)list`; `x:N word`; `zs:(N word)list`;
    `word 0:N word`; `[]:(N word)list`; `zs2:(N word)list`; `z2:N word`; `l:num`]
    LBIGAUX_MC_MUL_BY_SINGLE) THEN
  REWRITE_TAC[APPEND; LENGTH; mw_mul_by_single_def; k2mw_LENGTH_0]);;

let LBIGAUX_MC_TOP_TWO = prove
 (`!(ys:(N word)list) (x:N word) k1 k2 k3 (ys1:(N word)list) l.
     LENGTH (APPEND ys1 ys) < dimword(:N) /\ LENGTH ys <= l
     ==> ?l2.
       mc_top_two_pre (l,k2,k1,k3,x,word (LENGTH (APPEND ys1 ys)),word (LENGTH ys1),
         APPEND ys1 ys) /\
       mc_top_two (l,k2,k1,k3,x,word (LENGTH (APPEND ys1 ys)),word (LENGTH ys1),
         APPEND ys1 ys) =
         (l2,FST (SND (mw_mul_pass_top x ys (k1,k2,k3))),
          SND (SND (mw_mul_pass_top x ys (k1,k2,k3))),x,
          word (LENGTH (APPEND ys1 ys)),word (LENGTH (APPEND ys1 ys)),APPEND ys1 ys) /\
       l <= l2 + LENGTH ys`,
  LIST_INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[mc_top_two_def; mc_top_two_pre_def] THEN
    REWRITE_TAC[APPEND_NIL; mw_mul_pass_top_def; LET_DEF; LET_END_DEF; FST; SND] THEN
    EXISTS_TAC `l:num` THEN REWRITE_TAC[LENGTH; ADD_CLAUSES; LE_REFL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH]) THEN
  SUBGOAL_THEN `~(word (LENGTH (ys1:(N word)list) + SUC (LENGTH (t:(N word)list))):N word =
                  word (LENGTH ys1)) /\
                val (word (LENGTH (ys1:(N word)list)):N word) = LENGTH ys1`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [W(fun (_,w) -> MP_TAC(SPECL [rand(lhs(rand w)); rand(rhs(rand w))]
         (INST_TYPE [`:N`,`:N`] LBIGAUX_WORD_EQ_LT))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ARITH_TAC];
      MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
  ONCE_REWRITE_TAC[mc_top_two_def; mc_top_two_pre_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; LBIGAUX_EL_LENGTH_CONS; mc_single_mul_thm] THEN
  LBIG_PAIR_TAC `single_mul_add (x:N word) h k1 (word 0)` `y1:N word` `k':N word` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[word_add_n2w; mw_mul_pass_top_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:N word`; `k':N word`; `y1:N word`; `k2:N word`;
    `SNOC (h:N word) ys1`; `l - 1`]) THEN
  REWRITE_TAC[LENGTH_SNOC; SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH;
              GSYM ADD1; ADD_CLAUSES] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `l2:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let mc_top_two_thm = prove
 (`!(ys:(N word)list) (x:N word) l.
     1 < LENGTH ys /\ LENGTH ys < dimword(:N) /\ LENGTH ys <= l
     ==> ?l2.
       mc_top_two_pre (l,word 0,word 0,word 0,x,word (LENGTH ys),word 0,ys) /\
       mc_top_two (l,word 0,word 0,word 0,x,word (LENGTH ys),word 0,ys) =
         (l2,LAST (BUTLAST (mw_mul_by_single x ys)),
          LAST (BUTLAST (BUTLAST (mw_mul_by_single x ys))),x,
          word (LENGTH ys),word (LENGTH ys),ys) /\
       l <= l2 + LENGTH ys`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ys:(N word)list`; `x:N word`; `word 0:N word`; `word 0:N word`;
    `word 0:N word`; `[]:(N word)list`; `l:num`] LBIGAUX_MC_TOP_TWO) THEN
  ASM_SIMP_TAC[APPEND; LENGTH; mw_mul_pass_top_thm; FST; SND]);;

let LBIGAUX_MC_COPY_DOWN = prove
 (`!(zs2:(N word)list) (zs0:(N word)list) (zs1:(N word)list) (zs3:(N word)list) l.
     LENGTH (APPEND zs0 (APPEND zs1 zs2)) < dimword(:N) /\ ~(zs1 = []) /\ LENGTH zs2 <= l
     ==> ?zs4 l2.
       mc_copy_down_pre (l,word (LENGTH zs2),word (LENGTH (APPEND zs0 zs1)),
         word (LENGTH zs0),APPEND zs0 (APPEND zs1 (APPEND zs2 zs3))) /\
       mc_copy_down (l,word (LENGTH zs2),word (LENGTH (APPEND zs0 zs1)),
         word (LENGTH zs0),APPEND zs0 (APPEND zs1 (APPEND zs2 zs3))) =
         (l2,APPEND zs0 (APPEND zs2 zs4)) /\
       LENGTH zs4 = LENGTH zs1 + LENGTH zs3 /\
       l <= l2 + LENGTH zs2`,
  LIST_INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[mc_copy_down_def; mc_copy_down_pre_def] THEN
    REWRITE_TAC[LENGTH; APPEND] THEN
    MAP_EVERY EXISTS_TAC [`APPEND (zs1:(N word)list) zs3`; `l:num`] THEN
    REWRITE_TAC[LENGTH_APPEND; ADD_CLAUSES; LE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `zs0:(N word)list` THEN X_GEN_TAC `zs1:(N word)list` THEN
  LBIG_CONS_CASES_TAC `zs1:(N word)list` `z:N word` `zs':(N word)list` THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH]) THEN
  SUBGOAL_THEN `~(word (SUC (LENGTH (t:(N word)list))):N word = word 0) /\
                val (word (LENGTH (zs0:(N word)list) + SUC (LENGTH (zs':(N word)list))):N word) =
                  LENGTH zs0 + SUC (LENGTH zs') /\
                val (word (LENGTH (zs0:(N word)list)):N word) = LENGTH zs0`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LBIGAUX_WORD_SUC_NZ; MATCH_MP_TAC LBIGAUX_VAL_WORD_LT;
      MATCH_MP_TAC LBIGAUX_VAL_WORD_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
  ONCE_REWRITE_TAC[mc_copy_down_def; mc_copy_down_pre_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; LBIGAUX_WORD_SUC_SUB1] THEN
  SUBGOAL_THEN `EL (LENGTH (zs0:(N word)list) + SUC (LENGTH (zs':(N word)list)))
                  (APPEND zs0 (APPEND (CONS z zs') (APPEND (CONS h t) zs3))) = h`
    SUBST1_TAC THENL
   [SUBGOAL_THEN `APPEND (zs0:(N word)list) (APPEND (CONS z zs') (APPEND (CONS h t) zs3)) =
                  APPEND (APPEND zs0 (CONS z zs')) (CONS h (APPEND t zs3))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (zs0:(N word)list) + SUC (LENGTH (zs':(N word)list)) =
                  LENGTH (APPEND zs0 (CONS (z:N word) zs'))` SUBST1_TAC THENL
     [REWRITE_TAC[LENGTH_APPEND; LENGTH]; ALL_TAC] THEN
    REWRITE_TAC[LBIGAUX_EL_LENGTH_CONS]; ALL_TAC] THEN
  REWRITE_TAC[APPEND; LUPDATE_LENGTH; word_add_n2w] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`SNOC (h:N word) zs0`; `SNOC (h:N word) zs'`;
    `zs3:(N word)list`; `l - 1`]) THEN
  REWRITE_TAC[LENGTH_SNOC; SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH;
              GSYM ADD1; ADD_CLAUSES; NOT_CONS_NIL; APPEND_EQ_NIL] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `zs4:(N word)list` (X_CHOOSE_THEN `l2:num` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`zs4:(N word)list`; `l2:num`] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let mc_copy_down_thm = prove
 (`!(zs1:(N word)list) (zs2:(N word)list) (zs3:(N word)list) l.
     LENGTH (APPEND zs1 zs2) < dimword(:N) /\ ~(zs1 = []) /\ LENGTH zs2 <= l
     ==> ?zs4 l2.
       mc_copy_down_pre (l,word (LENGTH zs2),word (LENGTH zs1),word 0,
         APPEND zs1 (APPEND zs2 zs3)) /\
       mc_copy_down (l,word (LENGTH zs2),word (LENGTH zs1),word 0,
         APPEND zs1 (APPEND zs2 zs3)) = (l2,APPEND zs2 zs4) /\
       LENGTH zs4 = LENGTH zs1 + LENGTH zs3 /\
       l <= l2 + LENGTH zs2`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`zs2:(N word)list`; `[]:(N word)list`; `zs1:(N word)list`; `zs3:(N word)list`;
    `l:num`] LBIGAUX_MC_COPY_DOWN) THEN
  REWRITE_TAC[APPEND; LENGTH]);;

let mc_copy_over_thm = prove
 (`!(xs0:(N word)list) (zs0:(N word)list) (xs:(N word)list) (zs:(N word)list) l.
     LENGTH zs0 = LENGTH xs0 /\ LENGTH (APPEND zs0 zs) < dimword(:N) /\ LENGTH xs0 <= l
     ==> ?l2.
       mc_copy_over_pre (l,word (LENGTH xs0),APPEND xs0 xs,APPEND zs0 zs) /\
       mc_copy_over (l,word (LENGTH xs0),APPEND xs0 xs,APPEND zs0 zs) =
         (l2,APPEND xs0 xs,APPEND xs0 zs) /\
       l <= l2 + LENGTH xs0`,
  MATCH_MP_TAC SNOC_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[mc_copy_over_def; mc_copy_over_pre_def] THEN
    REWRITE_TAC[APPEND] THEN EXISTS_TAC `l:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `xs0:(N word)list` THEN DISCH_TAC THEN X_GEN_TAC `x:N word` THEN
  X_GEN_TAC `zs0:(N word)list` THEN
  MP_TAC(ISPEC `zs0:(N word)list` SNOC_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `z:N word` (X_CHOOSE_THEN `zs0':(N word)list` SUBST1_TAC))) THEN
  REWRITE_TAC[LENGTH; LENGTH_SNOC; GSYM NOT_SUC; SUC_INJ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH_SNOC]) THEN
  SUBGOAL_THEN `~(word (SUC (LENGTH (xs0:(N word)list))):N word = word 0) /\
                val (word (LENGTH (xs0:(N word)list)):N word) = LENGTH xs0`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LBIGAUX_WORD_SUC_NZ; MATCH_MP_TAC LBIGAUX_VAL_WORD_LT] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[mc_copy_over_def; mc_copy_over_pre_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; LBIGAUX_WORD_SUC_SUB1] THEN
  REWRITE_TAC[SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LBIGAUX_EL_LENGTH_CONS] THEN
  SUBGOAL_THEN `LUPDATE (x:N word) (LENGTH (xs0:(N word)list)) (APPEND zs0' (CONS z zs)) =
                APPEND zs0' (CONS x zs)` SUBST1_TAC THENL
   [UNDISCH_TAC `LENGTH (zs0':(N word)list) = LENGTH (xs0:(N word)list)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LUPDATE_LENGTH]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`zs0':(N word)list`; `CONS (x:N word) xs`;
    `CONS (x:N word) zs`; `l - 1`]) THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `l2:num` THEN ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* division: correctness of mc_div                                           *)
(* ------------------------------------------------------------------------- *)

let mw_fix_REPLICATE = prove
 (`!n xs:(N word)list. mw_fix (APPEND xs (REPLICATE n (word 0))) = mw_fix xs`,
  INDUCT_TAC THEN REWRITE_TAC[REPLICATE; APPEND_NIL] THEN
  REWRITE_TAC[GSYM REPLICATE; REPLICATE_SNOC; APPEND_SNOC; mw_fix_SNOC] THEN
  ASM_REWRITE_TAC[]);;

let MAP_K_0 = prove
 (`!xs:A list. MAP (\x. word 0:N word) xs = REPLICATE (LENGTH xs) (word 0)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; LENGTH; REPLICATE]);;

let mc_div_max_def = new_definition
  `mc_div_max (xs:(N word)list) (ys:(N word)list) (zs:(N word)list) =
     2 * LENGTH ys + 2 * LENGTH zs + 5 + dimindex(:N) +
     LENGTH xs * (dimword(:N) + 2 * LENGTH ys + 4)`;;

let LBIGAUX_BUTLASTN_LENGTH_APPEND = prove
 (`!(l2:A list) l1. BUTLASTN (LENGTH l2) (APPEND l1 l2) = l1`,
  REWRITE_TAC[BUTLASTN_DEF; REVERSE_APPEND] THEN
  ONCE_REWRITE_TAC[GSYM LENGTH_REVERSE] THEN
  REWRITE_TAC[DROP_LENGTH_APPEND; REVERSE_REVERSE]);;

let LBIGAUX_MC_DIV_A = prove
 (`!(xs:(N word)list) (ys:(N word)list) (zs:(N word)list) res md (r3:N word) l.
     ~(ys = []) /\ mw_ok xs /\ mw_ok ys /\ LENGTH xs + LENGTH ys <= LENGTH zs /\
     LENGTH zs < dimword(:N) /\ (res,md,T) = mw_div xs ys /\ mc_div_max xs ys zs <= l /\
     LENGTH xs < LENGTH ys
     ==> ?zs2 l2.
       mc_div_pre (l,word (LENGTH xs),word (LENGTH ys),r3,xs,ys,zs) /\
       mc_div (l,word (LENGTH xs),word (LENGTH ys),r3,xs,ys,zs) =
         (l2,word (LENGTH (if r3 = word 0 then res else md)),r3,word (LENGTH (mw_fix md)),
          xs,ys,APPEND (if r3 = word 0 then res else md) zs2) /\
       LENGTH zs = LENGTH (APPEND (if r3 = word 0 then res else md) zs2) /\
       (r3 = word 0 ==> ~(LENGTH zs2 = 0)) /\ LENGTH (mw_fix md) < dimword(:N) /\
       l <= l2 + mc_div_max xs ys zs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `res = []:(N word)list /\
                md = APPEND (xs:(N word)list) (REPLICATE (LENGTH (ys:(N word)list) - LENGTH xs) (word 0))`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(res:(N word)list,md:(N word)list,T) = mw_div xs ys` THEN
    ASM_SIMP_TAC[mw_div_def; mw_ok_mw_fix_ID; LET_DEF; LET_END_DEF; PAIR_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (xs:(N word)list) < dimword(:N) /\ LENGTH (ys:(N word)list) < dimword(:N)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[mw_fix_REPLICATE; mw_ok_mw_fix_ID] THEN
  REWRITE_TAC[mc_div_def; mc_div_pre_def; LET_DEF; LET_END_DEF] THEN
  ASM_SIMP_TAC[word_lo_n2w; MOD_LT] THEN
  REWRITE_TAC[mc_div0_def; mc_div0_pre_def; LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `r3:N word = word 0` THEN ASM_REWRITE_TAC[] THENL
   [(CASE_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`zs:(N word)list`; `l:num`] THEN
      REWRITE_TAC[LENGTH; APPEND] THEN
      UNDISCH_TAC `~(ys:(N word)list = [])` THEN REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
      ASM_ARITH_TAC);
    (MP_TAC(ISPECL [`zs:(N word)list`; `LENGTH (ys:(N word)list)`] multiword_LESS_EQ_LENGTH) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`zs1:(N word)list`; `zs5:(N word)list`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
      MP_TAC(ISPECL [`zs1:(N word)list`; `LENGTH (xs:(N word)list)`] multiword_LESS_EQ_LENGTH) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`zs3:(N word)list`; `zs4:(N word)list`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
      MP_TAC(SPECL [`APPEND zs3 zs4:(N word)list`; `zs5:(N word)list`; `l - 1`] mc_mul_zero_thm) THEN
      ASM_REWRITE_TAC[LENGTH_APPEND] THEN
      ANTS_TAC THENL [UNDISCH_TAC `mc_div_max xs ys (APPEND (APPEND zs3 zs4) zs5:(N word)list) <= l` THEN
        REWRITE_TAC[mc_div_max_def; LENGTH_APPEND] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`xs:(N word)list`; `MAP (\x. word 0:N word) (zs3:(N word)list)`;
        `[]:(N word)list`; `APPEND (MAP (\x. word 0:N word) (zs4:(N word)list)) zs5`;
        `l - 1 - (LENGTH (zs3:(N word)list) + LENGTH (zs4:(N word)list)) - 1`] mc_copy_over_thm) THEN
      ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_APPEND; APPEND_NIL; MAP_APPEND; GSYM APPEND_ASSOC] THEN
      ANTS_TAC THENL [UNDISCH_TAC `mc_div_max xs ys (APPEND (APPEND zs3 zs4) zs5:(N word)list) <= l` THEN
        REWRITE_TAC[mc_div_max_def; LENGTH_APPEND] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`zs5:(N word)list`; `l2:num`] THEN
      ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE; GSYM APPEND_ASSOC; MAP_K_0] THEN
      SUBGOAL_THEN `LENGTH (xs:(N word)list) + LENGTH (ys:(N word)list) - LENGTH xs = LENGTH ys /\
                    LENGTH (zs4:(N word)list) = LENGTH ys - LENGTH xs`
        (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `mc_div_max xs ys (APPEND (APPEND zs3 zs4) zs5:(N word)list) <= l` THEN
      REWRITE_TAC[mc_div_max_def; LENGTH_APPEND] THEN ASM_ARITH_TAC)]);;

let LBIGAUX_MW_FIX_SING = prove
 (`!r:N word. mw_fix [r] = if r = word 0 then [] else [r]`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [mw_fix_def] THEN
  REWRITE_TAC[NOT_CONS_NIL; LAST; BUTLAST] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[mw_fix_def] THEN REWRITE_TAC[]);;

let LBIGAUX_MC_DIV_B = prove
 (`!(xs:(N word)list) (ys:(N word)list) (zs:(N word)list) res md (r3:N word) l.
     ~(ys = []) /\ mw_ok xs /\ mw_ok ys /\ LENGTH xs + LENGTH ys <= LENGTH zs /\
     LENGTH zs < dimword(:N) /\ (res,md,T) = mw_div xs ys /\ mc_div_max xs ys zs <= l /\
     ~(LENGTH xs < LENGTH ys) /\ LENGTH ys = 1
     ==> ?zs2 l2.
       mc_div_pre (l,word (LENGTH xs),word (LENGTH ys),r3,xs,ys,zs) /\
       mc_div (l,word (LENGTH xs),word (LENGTH ys),r3,xs,ys,zs) =
         (l2,word (LENGTH (if r3 = word 0 then res else md)),r3,word (LENGTH (mw_fix md)),
          xs,ys,APPEND (if r3 = word 0 then res else md) zs2) /\
       LENGTH zs = LENGTH (APPEND (if r3 = word 0 then res else md) zs2) /\
       (r3 = word 0 ==> ~(LENGTH zs2 = 0)) /\ LENGTH (mw_fix md) < dimword(:N) /\
       l <= l2 + mc_div_max xs ys zs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?qs r. mw_simple_div (word 0) (REVERSE xs) (HD ys) = (qs,r,T) /\
                       res = REVERSE qs /\ md = [r:N word]`
    STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(LENGTH (xs:(N word)list) < 1)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(res:(N word)list,md:(N word)list,T) = mw_div xs ys` THEN
    ASM_SIMP_TAC[mw_div_def; mw_ok_mw_fix_ID; LET_DEF; LET_END_DEF] THEN
    MP_TAC(ISPEC `mw_simple_div (word 0) (REVERSE xs) (HD ys:N word)` PAIR_SURJECTIVE) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`qs:(N word)list`; `p:N word#bool`] THEN
    MP_TAC(ISPEC `p:N word#bool` PAIR_SURJECTIVE) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`r:N word`; `c:bool`] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`qs:(N word)list`; `r:N word`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (qs:(N word)list) = LENGTH (xs:(N word)list)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP LENGTH_mw_simple_div) THEN REWRITE_TAC[LENGTH_REVERSE] THEN
    MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (xs:(N word)list) < dimword(:N) /\ LENGTH (ys:(N word)list) < dimword(:N)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`zs:(N word)list`; `LENGTH (xs:(N word)list)`] multiword_LESS_EQ_LENGTH) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`zs1:(N word)list`; `zs5:(N word)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mc_div_def; mc_div_pre_def; LET_DEF; LET_END_DEF] THEN
  ASM_SIMP_TAC[word_lo_n2w; MOD_LT; ONE_LT_dimword] THEN
  REWRITE_TAC[mc_div1_def; mc_div1_pre_def; LET_DEF; LET_END_DEF; VAL_WORD_0] THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < 1`; EL; ARITH_RULE `0 = 0`] THEN
  MP_TAC(SPECL [`xs:(N word)list`; `[]:(N word)list`; `zs1:(N word)list`; `zs5:(N word)list`;
    `word 0:N word`; `HD (ys:(N word)list)`; `qs:(N word)list`; `r:N word`; `l - 1`]
    mc_simple_div_thm) THEN
  ASM_REWRITE_TAC[APPEND_NIL] THEN
  ANTS_TAC THENL [UNDISCH_TAC `mc_div_max xs ys (APPEND zs1 zs5:(N word)list) <= l` THEN
    REWRITE_TAC[mc_div_max_def; LENGTH_APPEND] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r3:N word = word 0` THEN ASM_REWRITE_TAC[] THENL
   [(ASM_CASES_TAC `r:N word = word 0` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`zs5:(N word)list`; `l - 1 - LENGTH (xs:(N word)list)`] THEN
      ASM_REWRITE_TAC[LBIGAUX_MW_FIX_SING; LENGTH_REVERSE; LENGTH_APPEND; LENGTH] THEN
      UNDISCH_TAC `mc_div_max xs ys (APPEND zs1 zs5:(N word)list) <= l` THEN
      REWRITE_TAC[mc_div_max_def; LENGTH_APPEND] THEN
      MP_TAC ONE_LT_dimword THEN ASM_ARITH_TAC);
    (SUBGOAL_THEN `?h t. REVERSE (qs:(N word)list) = CONS h t` STRIP_ASSUME_TAC THENL
       [MP_TAC(ISPEC `REVERSE (qs:(N word)list)` list_CASES) THEN STRIP_TAC THENL
         [UNDISCH_TAC `REVERSE (qs:(N word)list) = []` THEN
          REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_REVERSE] THEN ASM_ARITH_TAC;
          ASM_MESON_TAC[]]; ALL_TAC] THEN
      ASM_REWRITE_TAC[APPEND; LUPDATE_DEF] THEN
      ASM_CASES_TAC `r:N word = word 0` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`APPEND t zs5:(N word)list`; `l - 1 - LENGTH (xs:(N word)list)`] THEN
      ASM_REWRITE_TAC[LBIGAUX_MW_FIX_SING; LENGTH_APPEND; LENGTH; APPEND] THEN
      (SUBGOAL_THEN `LENGTH (t:(N word)list) + 1 = LENGTH (xs:(N word)list)` ASSUME_TAC THENL
        [UNDISCH_TAC `REVERSE (qs:(N word)list) = CONS h t` THEN
         DISCH_THEN(MP_TAC o AP_TERM `LENGTH:(N word)list->num`) THEN
         ASM_REWRITE_TAC[LENGTH_REVERSE; LENGTH] THEN ARITH_TAC; ALL_TAC]) THEN
      UNDISCH_TAC `mc_div_max xs ys (APPEND zs1 zs5:(N word)list) <= l` THEN
      REWRITE_TAC[mc_div_max_def; LENGTH_APPEND] THEN
      MP_TAC ONE_LT_dimword THEN ASM_ARITH_TAC)]);;

let LBIGAUX_DIV_ARITH = prove
 (`!l l1 l2 l3 l4 l6 l7 n m t z2 di p q.
     2 <= m /\ m <= n /\ t + m = n + 2 /\ p <= q /\
     2 * m + 2 * (n + SUC (SUC z2)) + 5 + di + q <= l /\
     l - 1 <= l1 + di /\ l1 - 1 <= l2 + n /\ l2 - 1 <= l3 + m /\
     l3 - 1 <= l4 + p /\ l4 - 1 - m - 1 <= l6 + m /\ l6 - 1 <= l7 + t
     ==> ~(l = 0) /\ ~(l1 = 0) /\ ~(l2 = 0) /\ ~(l3 = 0) /\ ~(l4 = 0) /\
         ~(l4 - 1 - m = 0) /\ ~(l6 = 0) /\
         l <= l7 + 2 * m + 2 * (n + SUC (SUC z2)) + 5 + di + q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN ASM_ARITH_TAC);;

let LBIGAUX_MC_DIV_C = prove
 (`!(xs:(N word)list) (ys:(N word)list) (zs:(N word)list) res md (r3:N word) l.
     ~(ys = []) /\ mw_ok xs /\ mw_ok ys /\ LENGTH xs + LENGTH ys <= LENGTH zs /\
     LENGTH zs < dimword(:N) /\ (res,md,T) = mw_div xs ys /\ mc_div_max xs ys zs <= l /\
     ~(LENGTH xs < LENGTH ys) /\ ~(LENGTH ys = 1)
     ==> ?zs2 l2.
       mc_div_pre (l,word (LENGTH xs),word (LENGTH ys),r3,xs,ys,zs) /\
       mc_div (l,word (LENGTH xs),word (LENGTH ys),r3,xs,ys,zs) =
         (l2,word (LENGTH (if r3 = word 0 then res else md)),r3,word (LENGTH (mw_fix md)),
          xs,ys,APPEND (if r3 = word 0 then res else md) zs2) /\
       LENGTH zs = LENGTH (APPEND (if r3 = word 0 then res else md) zs2) /\
       (r3 = word 0 ==> ~(LENGTH zs2 = 0)) /\ LENGTH (mw_fix md) < dimword(:N) /\
       l <= l2 + mc_div_max xs ys zs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `d = calc_d (LAST ys,word 1:N word)` THEN
  SUBGOAL_THEN `2 <= LENGTH (ys:(N word)list) /\ LENGTH ys <= LENGTH (xs:(N word)list)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(ys:(N word)list = [])` THEN REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`APPEND (mw_mul_by_single (d:N word) xs) [word 0]`; `LENGTH (ys:(N word)list)`]
    LESS_EQ_LENGTH_ALT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH_mw_mul_by_single; LENGTH] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`ts1:(N word)list`; `ts2:(N word)list`] THEN STRIP_TAC THEN
  LBIG_PAIR_TAC `mw_div_aux ts1 ts2 (BUTLAST (mw_mul_by_single (d:N word) ys))`
    `qs1:(N word)list` `rs1:(N word)list` THEN
  LBIG_PAIR_TAC `mw_simple_div (word 0) (REVERSE rs1) (d:N word)` `x1:(N word)list`
    `p:N word#bool` THEN
  MP_TAC(ISPEC `p:N word#bool` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`x2:N word`; `x3:bool`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `res = REVERSE (qs1:(N word)list) /\ md = REVERSE (x1:(N word)list) /\ x3`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(res:(N word)list,md:(N word)list,T) = mw_div xs ys` THEN
    ASM_SIMP_TAC[mw_div_def; mw_ok_mw_fix_ID; LET_DEF; LET_END_DEF] THEN
    UNDISCH_TAC `LENGTH (ts2:(N word)list) = LENGTH (ys:(N word)list)` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[SYM th] THEN ASSUME_TAC th) THEN
    ASM_REWRITE_TAC[LBIGAUX_BUTLASTN_LENGTH_APPEND; LASTN_LENGTH_APPEND] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `res = REVERSE (qs1:(N word)list)` THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `md = REVERSE (x1:(N word)list)` THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `x3:bool` THEN DISCH_THEN(SUBST_ALL_TAC o EQT_INTRO) THEN
  SUBGOAL_THEN `LENGTH (BUTLAST (mw_mul_by_single (d:N word) ys)) = LENGTH (ys:(N word)list)`
    ASSUME_TAC THENL
   [SUBGOAL_THEN `~(mw_mul_by_single (d:N word) ys = [])` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_mw_mul_by_single] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LENGTH_FRONT; LENGTH_mw_mul_by_single] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (rs1:(N word)list) = LENGTH (ys:(N word)list) /\
                LENGTH (qs1:(N word)list) = LENGTH (ts1:(N word)list)` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`ts1:(N word)list`; `ts2:(N word)list`;
      `BUTLAST (mw_mul_by_single (d:N word) ys)`; `qs1:(N word)list`; `rs1:(N word)list`]
      LENGTH_mw_div_aux) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (x1:(N word)list) = LENGTH (ys:(N word)list)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP LENGTH_mw_simple_div o
      check (fun th -> free_in `x1:(N word)list` (concl th) && is_eq (concl th))) THEN
    ASM_REWRITE_TAC[LENGTH_REVERSE] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (ts1:(N word)list) + LENGTH (ys:(N word)list) = LENGTH (xs:(N word)list) + 2`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:(N word)list->num` o
      check (fun th -> free_in `ts1:(N word)list` (concl th) && is_eq (concl th) &&
                       free_in `ts2:(N word)list` (concl th))) THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_mw_mul_by_single; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(REVERSE qs1,REVERSE x1,T) = mw_div (xs:(N word)list) ys` THEN
  DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `LENGTH (xs:(N word)list) < dimword(:N) /\ LENGTH (ys:(N word)list) < dimword(:N) /\
                2 < dimword(:N)` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(LAST (ys:(N word)list) = word 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mw_ok_def]; ALL_TAC] THEN
  SUBGOAL_THEN `~(LAST (BUTLAST (mw_mul_by_single (d:N word) ys)) = word 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `calc_d (LAST ys,word 1) = (d:N word)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC LAST_FRONT_mw_mul_by_single_NOT_ZERO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `EL (LENGTH (ys:(N word)list) - 1) ys = LAST ys` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LAST_EL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`zs:(N word)list`; `LENGTH (xs:(N word)list)`] multiword_LESS_EQ_LENGTH) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`zs1:(N word)list`; `zs5:(N word)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
  SUBGOAL_THEN `?z1 z2 zs2. zs5 = CONS (z1:N word) (CONS z2 zs2)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `zs5:(N word)list` list_CASES) THEN STRIP_TAC THENL
     [UNDISCH_TAC `zs5:(N word)list = []` THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `t:(N word)list` list_CASES) THEN STRIP_TAC THENL
     [UNDISCH_TAC `t:(N word)list = []` THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `zs5 = CONS (h:N word) []` THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `zs5 = CONS (z1:N word) (CONS z2 zs2)` THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
  SUBGOAL_THEN `~word_ult (word (LENGTH (xs:(N word)list)):N word) (word (LENGTH (ys:(N word)list)))`
    ASSUME_TAC THENL [ASM_SIMP_TAC[word_lo_n2w; MOD_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `~(word (LENGTH (ys:(N word)list)):N word = word 1)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LBIGAUX_WORD_EQ_LT; ONE_LT_dimword]; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (LENGTH (ys:(N word)list))) (word 1):N word = word (LENGTH ys - 1)`
    ASSUME_TAC THENL [MATCH_MP_TAC LBIGAUX_WORD_SUB_EQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word (LENGTH (ys:(N word)list) - 1):N word) = LENGTH ys - 1`
    ASSUME_TAC THENL [MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mc_div_def; mc_div_pre_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`LAST (ys:(N word)list)`; `word 1:N word`; `l - 1`] mc_calc_d_thm) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `mc_div_max xs ys (APPEND zs1 (CONS z1 (CONS z2 zs2)):(N word)list) <= l` THEN
    REWRITE_TAC[mc_div_max_def; LENGTH_APPEND; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[mc_div3_def; mc_div3_pre_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(SPECL [`xs:(N word)list`; `d:N word`; `zs1:(N word)list`; `CONS (z2:N word) zs2`;
    `z1:N word`; `l1 - 1`] mc_mul_by_single_thm) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `mc_div_max xs ys (APPEND zs1 (CONS z1 (CONS z2 zs2)):(N word)list) <= l` THEN
    REWRITE_TAC[mc_div_max_def; LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1a:N word` (X_CHOOSE_THEN `l2:num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val (word (LENGTH (xs:(N word)list) + 1):N word) = LENGTH xs + 1 /\
                LUPDATE (word 0) (LENGTH xs + 1)
                  (APPEND (mw_mul_by_single (d:N word) xs) (CONS z2 zs2)) =
                APPEND ts1 (APPEND ts2 zs2)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (xs:(N word)list) + 1 = LENGTH (mw_mul_by_single (d:N word) xs)`
      SUBST1_TAC THENL [REWRITE_TAC[LENGTH_mw_mul_by_single]; ALL_TAC] THEN
    REWRITE_TAC[LUPDATE_LENGTH; APPEND_ASSOC] THEN
    UNDISCH_TAC `APPEND (mw_mul_by_single (d:N word) xs) [word 0] = APPEND ts1 ts2` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`ys:(N word)list`; `d:N word`; `l2 - 1`] mc_top_two_thm) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `mc_div_max xs ys (APPEND zs1 (CONS z1 (CONS z2 zs2)):(N word)list) <= l` THEN
    REWRITE_TAC[mc_div_max_def; LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l3:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `word_add (word_sub (word (LENGTH (xs:(N word)list))) (word (LENGTH (ys:(N word)list))))
                  (word 2):N word = word (LENGTH (ts1:(N word)list))` SUBST1_TAC THENL
   [SUBGOAL_THEN `word_sub (word (LENGTH (xs:(N word)list))) (word (LENGTH (ys:(N word)list))):N word =
                  word (LENGTH xs - LENGTH ys)` SUBST1_TAC THENL
     [MATCH_MP_TAC LBIGAUX_WORD_SUB_EQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[word_add_n2w] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (ts1:(N word)list) * (dimword(:N) + 2 * LENGTH (ys:(N word)list) + 4) <=
                LENGTH (xs:(N word)list) * (dimword(:N) + 2 * LENGTH ys + 4)` ASSUME_TAC THENL
   [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(CONV_RULE (TOP_DEPTH_CONV let_CONV)
   (INST [`d:N word`,`d:N word`; `ys:(N word)list`,`ys:(N word)list`]
    (SPECL [`ts1:(N word)list`; `ts2:(N word)list`; `zs2:(N word)list`; `l3 - 1`]
      mc_div_loop_thm))) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND] THEN
    UNDISCH_TAC `mc_div_max xs ys (APPEND zs1 (CONS z1 (CONS z2 zs2)):(N word)list) <= l` THEN
    REWRITE_TAC[mc_div_max_def; LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l4:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[mc_div2_def; mc_div2_pre_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(SPECL [`rs1:(N word)list`; `APPEND (REVERSE qs1) zs2:(N word)list`; `word 0:N word`;
    `d:N word`; `x1:(N word)list`; `x2:N word`; `l4 - 1`] mc_simple_div1_thm) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `mc_div_max xs ys (APPEND zs1 (CONS z1 (CONS z2 zs2)):(N word)list) <= l` THEN
    REWRITE_TAC[mc_div_max_def; LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`REVERSE x1:(N word)list`; `APPEND (REVERSE qs1) zs2:(N word)list`;
    `word (LENGTH (ts1:(N word)list)):N word`; `l4 - 1 - LENGTH (ys:(N word)list) - 1`]
    mc_fix_thm) THEN
  REWRITE_TAC[mw_fix_thm] THEN ASM_REWRITE_TAC[LENGTH_REVERSE] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `mc_div_max xs ys (APPEND zs1 (CONS z1 (CONS z2 zs2)):(N word)list) <= l` THEN
    REWRITE_TAC[mc_div_max_def; LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r8a:N word` (X_CHOOSE_THEN `l6:num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r3:N word = word 0` THEN ASM_REWRITE_TAC[] THENL
   [(MP_TAC(SPECL [`REVERSE x1:(N word)list`; `REVERSE qs1:(N word)list`; `zs2:(N word)list`;
        `l6 - 1`] mc_copy_down_thm) THEN
      ASM_REWRITE_TAC[LENGTH_REVERSE; LENGTH_APPEND] THEN
      ANTS_TAC THENL
       [REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_REVERSE] THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `mc_div_max xs ys (APPEND zs1 (CONS z1 (CONS z2 zs2)):(N word)list) <= l` THEN
        REWRITE_TAC[mc_div_max_def; LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `zs4:(N word)list` (X_CHOOSE_THEN `l7:num` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`zs4:(N word)list`; `l7:num`] THEN
      ASM_REWRITE_TAC[LENGTH_REVERSE; LENGTH_APPEND; LENGTH] THEN
    MP_TAC(ISPEC `REVERSE x1:(N word)list` LENGTH_mw_fix) THEN
      REWRITE_TAC[LENGTH_REVERSE; LENGTH_mw_mul_by_single] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `mc_div_max xs ys (APPEND zs1 (CONS z1 (CONS z2 zs2)):(N word)list) <= l` THEN
      REWRITE_TAC[mc_div_max_def; LENGTH_APPEND; LENGTH] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`l:num`; `l1:num`; `l2:num`; `l3:num`; `l4:num`; `l6:num`; `l7:num`;
        `LENGTH (xs:(N word)list)`; `LENGTH (ys:(N word)list)`; `LENGTH (ts1:(N word)list)`;
        `LENGTH (zs2:(N word)list)`; `dimindex(:N)`;
        `LENGTH (ts1:(N word)list) * (dimword(:N) + 2 * LENGTH (ys:(N word)list) + 4)`;
        `LENGTH (xs:(N word)list) * (dimword(:N) + 2 * LENGTH (ys:(N word)list) + 4)`]
        LBIGAUX_DIV_ARITH) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY (fun t -> UNDISCH_TAC t)
       [`2 <= LENGTH (ys:(N word)list)`;
        `LENGTH (ts1:(N word)list) + LENGTH (ys:(N word)list) = LENGTH (xs:(N word)list) + 2`;
        `LENGTH (mw_fix (REVERSE (x1:(N word)list))) <= LENGTH (ys:(N word)list)`;
        `LENGTH (ys:(N word)list) < dimword(:N)`] THEN
      ARITH_TAC);
    (CASE_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`APPEND (REVERSE qs1) zs2:(N word)list`; `l6:num`] THEN
      ASM_REWRITE_TAC[LENGTH_REVERSE; LENGTH_APPEND; LENGTH] THEN
      MP_TAC(ISPEC `REVERSE x1:(N word)list` LENGTH_mw_fix) THEN
      REWRITE_TAC[LENGTH_REVERSE; LENGTH_mw_mul_by_single] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `mc_div_max xs ys (APPEND zs1 (CONS z1 (CONS z2 zs2)):(N word)list) <= l` THEN
      REWRITE_TAC[mc_div_max_def; LENGTH_APPEND; LENGTH] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`l:num`; `l1:num`; `l2:num`; `l3:num`; `l4:num`; `l6:num`; `l6:num`;
        `LENGTH (xs:(N word)list)`; `LENGTH (ys:(N word)list)`; `LENGTH (ts1:(N word)list)`;
        `LENGTH (zs2:(N word)list)`; `dimindex(:N)`;
        `LENGTH (ts1:(N word)list) * (dimword(:N) + 2 * LENGTH (ys:(N word)list) + 4)`;
        `LENGTH (xs:(N word)list) * (dimword(:N) + 2 * LENGTH (ys:(N word)list) + 4)`]
        LBIGAUX_DIV_ARITH) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY (fun t -> UNDISCH_TAC t)
       [`2 <= LENGTH (ys:(N word)list)`;
        `LENGTH (ts1:(N word)list) + LENGTH (ys:(N word)list) = LENGTH (xs:(N word)list) + 2`;
        `LENGTH (mw_fix (REVERSE (x1:(N word)list))) <= LENGTH (ys:(N word)list)`;
        `LENGTH (ys:(N word)list) < dimword(:N)`] THEN
      ARITH_TAC)]);;

let mc_div_thm = prove
 (`!(xs:(N word)list) (ys:(N word)list) (zs:(N word)list) res md (r3:N word) l.
     ~(ys = []) /\ mw_ok xs /\ mw_ok ys /\ LENGTH xs + LENGTH ys <= LENGTH zs /\
     LENGTH zs < dimword(:N) /\ (res,md,T) = mw_div xs ys /\ mc_div_max xs ys zs <= l
     ==> ?zs2 l2.
       mc_div_pre (l,word (LENGTH xs),word (LENGTH ys),r3,xs,ys,zs) /\
       mc_div (l,word (LENGTH xs),word (LENGTH ys),r3,xs,ys,zs) =
         (l2,word (LENGTH (if r3 = word 0 then res else md)),r3,word (LENGTH (mw_fix md)),
          xs,ys,APPEND (if r3 = word 0 then res else md) zs2) /\
       LENGTH zs = LENGTH (APPEND (if r3 = word 0 then res else md) zs2) /\
       (r3 = word 0 ==> ~(LENGTH zs2 = 0)) /\ LENGTH (mw_fix md) < dimword(:N) /\
       l <= l2 + mc_div_max xs ys zs`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `LENGTH (xs:(N word)list) < LENGTH (ys:(N word)list)` THENL
   [MATCH_MP_TAC LBIGAUX_MC_DIV_A THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH (ys:(N word)list) = 1` THENL
   [MATCH_MP_TAC LBIGAUX_MC_DIV_B; MATCH_MP_TAC LBIGAUX_MC_DIV_C] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* integer division                                                          *)
(* ------------------------------------------------------------------------- *)

let mc_add1,mc_add1_pre,mc_add1_def,mc_add1_pre_def =
  LBIGAUX_tailrec_define "mc_add1"
  `((\(l,r2,r10,r11,zs).
      if r10 = r11 then
        (let r0 = word 1 in
         let cnd = val r10 < LENGTH zs in
         let zs = LUPDATE r0 (val r10) zs in
         let r11 = word_add r11 (word 1) in
           (INR (l,r11,zs),cnd))
      else
        (let cnd = val r10 < LENGTH zs in
         let r0 = EL (val r10) zs in
           if r0 = r2 then
             (let r0 = word 0 in
              let zs = LUPDATE r0 (val r10) zs in
              let r10 = word_add r10 (word 1) in
                (INL (l - 1,r2,r10,r11,zs),(cnd /\ ~(l = 0))))
           else
             (let r0 = word_add r0 (word 1) in
              let zs = LUPDATE r0 (val r10) zs in
                (INR (l,r11,zs),cnd))))
   :num#N word#N word#N word#(N word)list ->
    ((num#N word#N word#N word#(N word)list) + (num#N word#(N word)list))#bool)`;;

let mc_add1_call,mc_add1_call_pre,mc_add1_call_def,mc_add1_call_pre_def =
  LBIGAUX_tailrec_define "mc_add1_call" (CASE_TERM
  `((\(l,r2,r6,r11,zs).
      if r2 = word 0 then (INR (l,r11,zs),T)
      else if r6 = word 0 then (INR (l,r11,zs),T)
      else
        (let r2 = word 0 in
         let r10 = r2 in
         let r2 = word_not r2 in
         let cnd = (mc_add1_pre (l - 1,r2,r10,r11,zs) /\ ~(l = 0)) in
         match mc_add1 (l - 1,r2,r10,r11,zs) with (l,r11,zs) ->
           (INR (l,r11,zs),cnd)))
   :num#N word#N word#N word#(N word)list ->
    ((num#N word#N word#N word#(N word)list) + (num#N word#(N word)list))#bool)`);;

let mc_div_sub_aux1,mc_div_sub_aux1_pre,mc_div_sub_aux1_def,mc_div_sub_aux1_pre_def =
  LBIGAUX_tailrec_define "mc_div_sub_aux1" (CASE_TERM
  `((\(l,r1,r4,r8,r9,r10,ys,zs).
      if r1 = word 1 then
        (let r1 = word 0 in (INR (l,r1,r4,r8,r9,r10,ys,zs),T))
      else
        (let r1 = word_sub r1 (word 1) in
         let cnd = val r10 < LENGTH ys in
         let r8 = EL (val r10) ys in
         let cnd = (cnd /\ val r10 < LENGTH zs) in
         let r9 = EL (val r10) zs in
         let cnd = (cnd /\ (~(r4 = word 0) ==> r4 = word 1)) in
         match single_sub_word r8 r9 r4 with (r8,r4) ->
         let zs = LUPDATE r8 (val r10) zs in
         let r10 = word_add r10 (word 1) in
           (INL (l - 1,r1,r4,r8,r9,r10,ys,zs),(cnd /\ ~(l = 0)))))
   :num#N word#N word#N word#N word#N word#(N word)list#(N word)list ->
    ((num#N word#N word#N word#N word#N word#(N word)list#(N word)list) +
     (num#N word#N word#N word#N word#N word#(N word)list#(N word)list))#bool)`);;

let mc_div_sub_aux,mc_div_sub_aux_pre,mc_div_sub_aux_def,mc_div_sub_aux_pre_def =
  LBIGAUX_tailrec_define "mc_div_sub_aux" (CASE_TERM
  `((\(l,r1,r8,r9,ys,zs).
      (let r10 = word 0 in
       let r1 = word_add r1 (word 1) in
       let r4 = word 1 in
       let cnd = (mc_div_sub_aux1_pre (l - 1,r1,r4,r8,r9,r10,ys,zs) /\ ~(l = 0)) in
       match mc_div_sub_aux1 (l - 1,r1,r4,r8,r9,r10,ys,zs) with
         (l,r1,r4,r8,r9,r10,ys,zs) ->
         (INR (l,r1,r4,r8,r9,r10,ys,zs),cnd)))
   :num#N word#N word#N word#(N word)list#(N word)list ->
    ((num#N word#N word#N word#(N word)list#(N word)list) +
     (num#N word#N word#N word#N word#N word#(N word)list#(N word)list))#bool)`);;

let mc_div_sub1,mc_div_sub1_pre,mc_div_sub1_def,mc_div_sub1_pre_def =
  LBIGAUX_tailrec_define "mc_div_sub1" (CASE_TERM
  `((\(l,r1,r8,r9,ys,zs).
      (let cnd = mc_div_sub_aux_pre (l,r1,r8,r9,ys,zs) in
       match mc_div_sub_aux (l,r1,r8,r9,ys,zs) with (l,r1,r4,r8,r9,r10,ys,zs) ->
         (INR (l,r1,r8,r9,r10,ys,zs),cnd)))
   :num#N word#N word#N word#(N word)list#(N word)list ->
    ((num#N word#N word#N word#(N word)list#(N word)list) +
     (num#N word#N word#N word#N word#(N word)list#(N word)list))#bool)`);;

let mc_div_sub_call,mc_div_sub_call_pre,mc_div_sub_call_def,mc_div_sub_call_pre_def =
  LBIGAUX_tailrec_define "mc_div_sub_call" (CASE_TERM
  `((\(l,r1,r2,r6,ys,zs).
      if r2 = word 0 then (INR (l,r6,ys,zs),T)
      else if r6 = word 0 then (INR (l,r6,ys,zs),T)
      else
        (let r8 = r6 in
         let r9 = r6 in
         let r3 = r1 in
         let cnd = mc_div_sub1_pre (l,r1,r8,r9,ys,zs) in
         match mc_div_sub1 (l,r1,r8,r9,ys,zs) with (l,r1,r8,r9,r10,ys,zs) ->
         let r10 = r3 in
         let cnd = (cnd /\ mc_fix_pre (l - 1,r8,r10,zs) /\ ~(l = 0)) in
         match mc_fix (l - 1,r8,r10,zs) with (l,r8,r10,zs) ->
         let r6 = r10 in
           (INR (l,r6,ys,zs),cnd)))
   :num#N word#N word#N word#(N word)list#(N word)list ->
    ((num#N word#N word#N word#(N word)list#(N word)list) +
     (num#N word#(N word)list#(N word)list))#bool)`);;

let mc_idiv_mod_header,mc_idiv_mod_header_pre,mc_idiv_mod_header_def,
    mc_idiv_mod_header_pre_def =
  LBIGAUX_tailrec_define "mc_idiv_mod_header"
  `((\(r6,r11).
      if r6 = word 0 then (INR r6,T)
      else
        (let r6 = word_shl r6 1 in
           if word_and r11 (word 1) = word 0 then (INR r6,T)
           else (let r6 = word_add r6 (word 1) in (INR r6,T))))
   :N word#N word -> ((N word#N word) + N word)#bool)`;;

let mc_idiv0,mc_idiv0_pre,mc_idiv0_def,mc_idiv0_pre_def =
  LBIGAUX_tailrec_define "mc_idiv0" (CASE_TERM
  `((\(l,r0,r3,r6,r11,r20,xs,ys,zs).
      if r3 = word 0 then
        (let r10 = r0 in
         let r8 = r10 in
         let cnd = (mc_fix_pre (l - 1,r8,r10,zs) /\ ~(l = 0)) in
         match mc_fix (l - 1,r8,r10,zs) with (l,r8,r10,zs) ->
         let r11 = r10 in
         let r2 = r20 in
         let r3 = r2 in
         let cnd = (cnd /\ mc_add1_call_pre (l,r2,r6,r11,zs)) in
         match mc_add1_call (l,r2,r6,r11,zs) with (l,r11,zs) ->
           if r11 = word 0 then (INR (l,r11,xs,ys,zs),cnd)
           else
             (let r11 = word_shl r11 1 in
              let r11 = word_add r11 r3 in
                (INR (l,r11,xs,ys,zs),cnd)))
      else
        (let r2 = r20 in
         let r1 = r11 in
         let r1 = word_ushr r1 1 in
         let cnd = mc_div_sub_call_pre (l,r1,r2,r6,ys,zs) in
         match mc_div_sub_call (l,r1,r2,r6,ys,zs) with (l,r6,ys,zs) ->
         let r6 = mc_idiv_mod_header (r6,r11) in
         let r11 = r6 in
           (INR (l,r11,xs,ys,zs),cnd)))
   :num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list ->
    ((num#N word#N word#N word#N word#N word#(N word)list#(N word)list#(N word)list) +
     (num#N word#(N word)list#(N word)list#(N word)list))#bool)`);;

let mc_idiv,mc_idiv_pre,mc_idiv_def,mc_idiv_pre_def =
  LBIGAUX_tailrec_define "mc_idiv" (CASE_TERM
  `((\(l,r3,r10,r11,xs,ys,zs).
      (let r0 = word_ushr r10 1 in
       let r1 = word_ushr r11 1 in
       let r10 = word_xor r10 r11 in
       let r10 = word_and r10 (word 1) in
       let r20 = r10 in
       let r21 = r11 in
       let cnd = mc_div_pre (l,r0,r1,r3,xs,ys,zs) in
       match mc_div (l,r0,r1,r3,xs,ys,zs) with (l,r0,r3,r6,xs,ys,zs) ->
       let r11 = r21 in
       let cnd = (cnd /\ mc_idiv0_pre (l,r0,r3,r6,r11,r20,xs,ys,zs)) in
       match mc_idiv0 (l,r0,r3,r6,r11,r20,xs,ys,zs) with (l,r11,xs,ys,zs) ->
         (INR (l,r11,xs,ys,zs),cnd)))
   :num#N word#N word#N word#(N word)list#(N word)list#(N word)list ->
    ((num#N word#N word#N word#(N word)list#(N word)list#(N word)list) +
     (num#N word#(N word)list#(N word)list#(N word)list))#bool)`);;

let LBIGAUX_MC_ADD1 = prove
 (`!(zs:(N word)list) (zs1:(N word)list) (zs2:(N word)list) l.
     LENGTH (APPEND zs1 zs) + 1 < dimword(:N) /\ ~(zs2 = []) /\ LENGTH zs <= l
     ==> ?rest l2.
       mc_add1_pre (l,word_not (word 0),word (LENGTH zs1),word (LENGTH (APPEND zs1 zs)),
         APPEND zs1 (APPEND zs zs2)) /\
       mc_add1 (l,word_not (word 0),word (LENGTH zs1),word (LENGTH (APPEND zs1 zs)),
         APPEND zs1 (APPEND zs zs2)) =
         (l2,word (LENGTH (APPEND zs1 (mw_addv zs [] T))),
          APPEND zs1 (APPEND (mw_addv zs [] T) rest)) /\
       LENGTH (APPEND zs1 (mw_addv zs [] T)) < dimword(:N) /\
       LENGTH (APPEND zs1 (APPEND (mw_addv zs [] T) rest)) =
         LENGTH (APPEND zs1 (APPEND zs zs2)) /\
       l <= l2 + LENGTH zs`,
  LIST_INDUCT_TAC THENL
   [X_GEN_TAC `zs1:(N word)list` THEN X_GEN_TAC `zs2:(N word)list` THEN
    LBIG_CONS_CASES_TAC `zs2:(N word)list` `z:N word` `zs3:(N word)list` THEN
    REWRITE_TAC[NOT_CONS_NIL] THEN REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL; LENGTH]) THEN
    SUBGOAL_THEN `val (word (LENGTH (zs1:(N word)list)):N word) = LENGTH zs1` ASSUME_TAC THENL
     [MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[mc_add1_def; mc_add1_pre_def] THEN
    ASM_REWRITE_TAC[APPEND_NIL; APPEND; LET_DEF; LET_END_DEF; LUPDATE_LENGTH; mw_addv_def;
                    word_add_n2w] THEN
    MAP_EVERY EXISTS_TAC [`zs3:(N word)list`; `l:num`] THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH; APPEND] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `zs1:(N word)list` THEN X_GEN_TAC `zs2:(N word)list` THEN X_GEN_TAC `l:num` THEN
  STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH]) THEN
  SUBGOAL_THEN `~(word (LENGTH (zs1:(N word)list)):N word =
                  word (LENGTH zs1 + SUC (LENGTH (t:(N word)list)))) /\
                val (word (LENGTH (zs1:(N word)list)):N word) = LENGTH zs1`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [W(fun (_,w) -> MP_TAC(SPECL [rand(lhs(rand w)); rand(rhs(rand w))]
         (INST_TYPE [`:N`,`:N`] LBIGAUX_WORD_EQ_LT))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ARITH_TAC];
      MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; APPEND] THEN
  ONCE_REWRITE_TAC[mc_add1_def; mc_add1_pre_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; LBIGAUX_EL_LENGTH_CONS; LUPDATE_LENGTH;
                  LBIGAUX_MW_ADDV_CONS_NIL_T] THEN
  ASM_CASES_TAC `h = word_not (word 0):N word` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`zs2:(N word)list`; `l:num`] THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH; APPEND] THEN ASM_ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`SNOC (word 0:N word) zs1`; `zs2:(N word)list`; `l - 1`]) THEN
  REWRITE_TAC[LENGTH_SNOC; SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH;
              word_add_n2w; GSYM ADD1; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rest:(N word)list` (X_CHOOSE_THEN `l2:num` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`rest:(N word)list`; `l2:num`] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let mc_add1_thm = prove
 (`!(zs:(N word)list) (zs2:(N word)list) l.
     LENGTH zs + 1 < dimword(:N) /\ ~(zs2 = []) /\ LENGTH zs <= l
     ==> ?rest l2.
       mc_add1_pre (l,word_not (word 0),word 0,word (LENGTH zs),APPEND zs zs2) /\
       mc_add1 (l,word_not (word 0),word 0,word (LENGTH zs),APPEND zs zs2) =
         (l2,word (LENGTH (mw_addv zs [] T)),APPEND (mw_addv zs [] T) rest) /\
       LENGTH (mw_addv zs [] T) < dimword(:N) /\
       LENGTH (APPEND (mw_addv zs [] T) rest) = LENGTH (APPEND zs zs2) /\
       l <= l2 + LENGTH zs`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`zs:(N word)list`; `[]:(N word)list`; `zs2:(N word)list`; `l:num`]
    LBIGAUX_MC_ADD1) THEN
  REWRITE_TAC[APPEND; LENGTH]);;

let LBIGAUX_MC_DIV_SUB_AUX = prove
 (`!(ys:(N word)list) (zs:(N word)list) (ys1:(N word)list) (zs1:(N word)list)
    (ys2:(N word)list) (zs2:(N word)list) c (r8:N word) (r9:N word) l.
      LENGTH zs1 = LENGTH ys1 /\ LENGTH zs = LENGTH ys /\
      LENGTH (APPEND zs1 zs) + 1 < dimword(:N) /\ LENGTH ys <= l
      ==> ?r8' r9' l2.
        mc_div_sub_aux1_pre (l,word (LENGTH zs + 1),b2w c,r8,r9,word (LENGTH zs1),
          APPEND (APPEND ys1 ys) ys2,APPEND (APPEND zs1 zs) zs2) /\
        mc_div_sub_aux1 (l,word (LENGTH zs + 1),b2w c,r8,r9,word (LENGTH zs1),
          APPEND (APPEND ys1 ys) ys2,APPEND (APPEND zs1 zs) zs2) =
          (l2,word 0,b2w (SND (mw_sub ys zs c)),r8',r9',word (LENGTH (APPEND zs1 zs)),
           APPEND (APPEND ys1 ys) ys2,APPEND (APPEND zs1 (FST (mw_sub ys zs c))) zs2) /\
        l <= l2 + LENGTH ys`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[mc_div_sub_aux1_def; mc_div_sub_aux1_pre_def] THEN
    REWRITE_TAC[mw_sub_def; APPEND_NIL; LENGTH; ADD_CLAUSES; LET_DEF; LET_END_DEF] THEN
    MAP_EVERY EXISTS_TAC [`r8:N word`; `r9:N word`; `l:num`] THEN
    ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `zs:(N word)list` THEN
  LBIG_CONS_CASES_TAC `zs:(N word)list` `z:N word` `zs':(N word)list` THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH]) THEN
  SUBGOAL_THEN `~(word (SUC (LENGTH (zs':(N word)list)) + 1):N word = word 1) /\
                val (word (LENGTH (zs1:(N word)list)):N word) = LENGTH zs1`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [W(fun (_,w) -> MP_TAC(SPECL [rand(lhs(rand w)); rand(rhs(rand w))]
         (INST_TYPE [`:N`,`:N`] LBIGAUX_WORD_EQ_LT))) THEN
      REWRITE_TAC[ONE_LT_dimword] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ARITH_TAC];
      MATCH_MP_TAC LBIGAUX_VAL_WORD_LT THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!(a:N word) b. EL (LENGTH (zs1:(N word)list)) (APPEND ys1 (CONS a b)) = a`
   ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (zs1:(N word)list) = LENGTH (ys1:(N word)list)` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LBIGAUX_EL_LENGTH_CONS]; ALL_TAC] THEN
  UNDISCH_TAC `LENGTH (zs1:(N word)list) = LENGTH (ys1:(N word)list)` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; LENGTH] THEN
  ONCE_REWRITE_TAC[mc_div_sub_aux1_def; mc_div_sub_aux1_pre_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; LBIGAUX_WORD_ADD1_SUB1; LBIGAUX_EL_LENGTH_CONS] THEN
  REWRITE_TAC[LBIGAUX_SINGLE_SUB_WORD_B2W] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[b2w_eq; LBIGAUX_B2W_01; word_add_n2w; LUPDATE_LENGTH; LBIGAUX_MW_SUB_CONS] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`zs':(N word)list`;
    `SNOC (h:N word) ys1`; `SNOC (FST (single_sub (h:N word) z c)) zs1`; `ys2:(N word)list`;
    `zs2:(N word)list`; `SND (single_sub (h:N word) z c)`; `FST (single_sub (h:N word) z c)`;
    `z:N word`; `l - 1`]) THEN
  REWRITE_TAC[LENGTH_SNOC; SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH;
              GSYM ADD1; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`r8':N word`; `r9':N word`; `l2:num`] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN ASM_ARITH_TAC);;

let mc_div_sub_aux_thm = prove
 (`!(ys:(N word)list) (zs:(N word)list) (ys2:(N word)list) (zs2:(N word)list)
    (r8:N word) (r9:N word) l.
      LENGTH zs = LENGTH ys /\ LENGTH zs + 1 < dimword(:N) /\ LENGTH ys <= l
      ==> ?r8' r9' l2.
        mc_div_sub_aux1_pre (l,word (LENGTH zs + 1),word 1,r8,r9,word 0,
          APPEND ys ys2,APPEND zs zs2) /\
        mc_div_sub_aux1 (l,word (LENGTH zs + 1),word 1,r8,r9,word 0,
          APPEND ys ys2,APPEND zs zs2) =
          (l2,word 0,b2w (SND (mw_sub ys zs T)),r8',r9',word (LENGTH zs),
           APPEND ys ys2,APPEND (FST (mw_sub ys zs T)) zs2) /\
        l <= l2 + LENGTH ys`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`ys:(N word)list`; `zs:(N word)list`; `[]:(N word)list`; `[]:(N word)list`;
    `ys2:(N word)list`; `zs2:(N word)list`; `T`; `r8:N word`; `r9:N word`; `l:num`]
    LBIGAUX_MC_DIV_SUB_AUX) THEN
  REWRITE_TAC[APPEND; LENGTH; multiword_b2w_def; BITVAL_CLAUSES]);;

let mc_div_sub1_thm = prove
 (`!(ys:(N word)list) (zs:(N word)list) (ys2:(N word)list) (zs2:(N word)list)
    (r8:N word) (r9:N word) l.
      LENGTH zs = LENGTH ys /\ LENGTH zs + 1 < dimword(:N) /\ LENGTH ys + 1 <= l
      ==> ?r8' r9' l2.
        mc_div_sub1_pre (l,word (LENGTH ys),r8,r9,APPEND ys ys2,APPEND zs zs2) /\
        mc_div_sub1 (l,word (LENGTH ys),r8,r9,APPEND ys ys2,APPEND zs zs2) =
          (l2,word 0,r8',r9',word (LENGTH ys),APPEND ys ys2,
           APPEND (FST (mw_sub ys zs T)) zs2) /\
        l <= l2 + LENGTH ys + 1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mc_div_sub1_def; mc_div_sub1_pre_def; mc_div_sub_aux_def; mc_div_sub_aux_pre_def;
              LET_DEF; LET_END_DEF; word_add_n2w] THEN
  MP_TAC(SPECL [`ys:(N word)list`; `zs:(N word)list`; `ys2:(N word)list`; `zs2:(N word)list`;
    `r8:N word`; `r9:N word`; `l - 1`] mc_div_sub_aux_thm) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r8a:N word` (X_CHOOSE_THEN `r9a:N word`
    (X_CHOOSE_THEN `l2:num` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`r8a:N word`; `r9a:N word`; `l2:num`] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let LBIGAUX_BIT0_HEADER = prove
 (`!s (xs:(N word)list). bit 0 (mc_header (s,xs)) <=> s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mc_header_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD; BIT_LSB_WORD; ODD_ADD; ODD_MULT; ARITH]);;

let mc_header_XOR = prove
 (`!s t (xs:(N word)list) (ys:(N word)list).
     word_and (word_xor (mc_header (s,xs)) (mc_header (t,ys))) (word 1) =
     b2w (~(s <=> t)):N word`,
  REWRITE_TAC[WORD_AND_1_BITVAL; BIT_WORD_XOR_ALT; LBIGAUX_BIT0_HEADER; multiword_b2w_def]);;

let b2w_EQ_0w = prove
 (`!b. (b2w b = word 0:N word) <=> ~b`,
  REWRITE_TAC[b2w_eq]);;

let mwi_divmod_alt_def = new_definition
  `mwi_divmod_alt (w:N word) (s_xs:bool#(N word)list) (t_ys:bool#(N word)list) =
     if w = word 0 then mwi_div s_xs t_ys else mwi_mod s_xs t_ys`;;

let LBIGAUX_SHL1_WORD = prove
 (`!n. word_shl (word n) 1:N word = word (n * 2)`,
  REWRITE_TAC[WORD_MUL_LSL; word_mul_n2w; EXP_1] THEN REWRITE_TAC[MULT_SYM]);;

let mc_idiv_mod_header_thm = prove
 (`!(xs:(N word)list) t (ys:(N word)list).
     LENGTH xs < dimword(:N)
     ==> mc_idiv_mod_header (word (LENGTH xs),mc_header (t,ys)) =
         mc_header ((~(xs = []) /\ t),xs)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mc_idiv_mod_header_def; LET_DEF; LET_END_DEF; mc_header_sign] THEN
  SUBGOAL_THEN `(word (LENGTH (xs:(N word)list)):N word = word 0) <=> xs = []`
    SUBST1_TAC THENL
   [ASM_SIMP_TAC[LBIGAUX_WORD_EQ_LT; ZERO_LT_dimword; LENGTH_EQ_NIL]; ALL_TAC] THEN
  ASM_CASES_TAC `xs:(N word)list = []` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[mc_header_def; LENGTH; MULT_CLAUSES; WORD_ADD_0]; ALL_TAC] THEN
  REWRITE_TAC[mc_header_def; LBIGAUX_SHL1_WORD] THEN
  BOOL_CASES_TAC `t:bool` THEN REWRITE_TAC[WORD_ADD_0]);;

let LBIGAUX_HEADER_NIL = prove
 (`!s. mc_header (s,[]:(N word)list) = b2w s`,
  GEN_TAC THEN REWRITE_TAC[mc_header_def; LENGTH; MULT_CLAUSES; WORD_ADD_0; multiword_b2w_def] THEN
  BOOL_CASES_TAC `s:bool` THEN REWRITE_TAC[BITVAL_CLAUSES]);;

let LBIGAUX_B2W_TF = prove
 (`b2w F = word 0:N word /\ b2w T = word 1:N word`,
  REWRITE_TAC[multiword_b2w_def; BITVAL_CLAUSES]);;

let LBIGAUX_WORD_LENGTH_EQ_0 = prove
 (`!xs:(N word)list. LENGTH xs < dimword(:N) ==> ((word (LENGTH xs):N word = word 0) <=> xs = [])`,
  SIMP_TAC[LBIGAUX_WORD_EQ_LT; ZERO_LT_dimword; LENGTH_EQ_NIL]);;

let LBIGAUX_MW_ADDV_T_NZ = prove
 (`!xs:(N word)list. ~(mw_addv xs [] T = [])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[mw_addv_def; NOT_CONS_NIL; LBIGAUX_MW_ADDV_CONS_NIL_T] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NOT_CONS_NIL]);;

let LBIGAUX_MW_FIX_APPEND = prove
 (`!(md:(N word)list) zs2.
     APPEND md zs2 =
     APPEND (mw_fix md) (APPEND (REPLICATE (LENGTH md - LENGTH (mw_fix md)) (word 0)) zs2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[APPEND_ASSOC; mw_fix_thm]);;

let mc_idiv_thm = prove
 ((CASE_TERM `!(xs:(N word)list) (ys:(N word)list) (zs:(N word)list) s t (r3:N word) l.
     LENGTH xs + LENGTH ys <= LENGTH zs /\ LENGTH zs < dimword(:N) DIV 2 /\
     mw_ok xs /\ mw_ok ys /\ ~(ys = []) /\
     mc_div_max xs ys zs + 2 * LENGTH zs + 2 <= l
     ==> ?zs1 l2.
       mc_idiv_pre (l,r3,mc_header (s,xs),mc_header (t,ys),xs,ys,zs) /\
       mc_idiv (l,r3,mc_header (s,xs),mc_header (t,ys),xs,ys,zs) =
         (l2,mc_header (mwi_divmod_alt r3 (s,xs) (t,ys)),xs,ys,
          APPEND (SND (mwi_divmod_alt r3 (s,xs) (t,ys))) zs1) /\
       LENGTH (APPEND (SND (mwi_divmod_alt r3 (s,xs) (t,ys))) zs1) = LENGTH zs /\
       l <= l2 + mc_div_max xs ys zs + 2 * LENGTH zs + 2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (xs:(N word)list) < dimword(:N) DIV 2 /\
                LENGTH (ys:(N word)list) < dimword(:N) DIV 2 /\
                LENGTH (zs:(N word)list) < dimword(:N)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC dim63_IMP_dim64 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(mw2n (ys:(N word)list) = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM mw_fix_NIL] THEN ASM_SIMP_TAC[mw_ok_mw_fix_ID]; ALL_TAC] THEN
  LBIG_PAIR_TAC `mw_div (xs:(N word)list) ys` `res:(N word)list` `p:(N word)list#bool` THEN
  MP_TAC(ISPEC `p:(N word)list#bool` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`md:(N word)list`; `c:bool`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`xs:(N word)list`; `ys:(N word)list`; `md:(N word)list`; `res:(N word)list`;
    `c:bool`] mw_div_thm) THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[mw_ok_mw_fix_ID] THEN STRIP_TAC THEN
  UNDISCH_TAC `c:bool` THEN DISCH_THEN(fun th -> SUBST_ALL_TAC(EQT_INTRO th)) THEN
  REWRITE_TAC[mc_idiv_def; mc_idiv_pre_def; LET_DEF; LET_END_DEF] THEN
  ASM_SIMP_TAC[mc_length; mc_header_XOR] THEN
  MP_TAC(SPECL [`xs:(N word)list`; `ys:(N word)list`; `zs:(N word)list`; `res:(N word)list`;
    `md:(N word)list`; `r3:N word`; `l:num`] mc_div_thm) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `zs2:(N word)list` (X_CHOOSE_THEN `l1:num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[mwi_divmod_alt_def; mwi_div_def; mwi_mod_def; mwi_divmod_def; LET_DEF;
              LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[mc_idiv0_def; mc_idiv0_pre_def; LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `r3:N word = word 0` THEN ASM_REWRITE_TAC[FST; SND] THENL
   [((SUBGOAL_THEN `LENGTH (res:(N word)list) < dimword(:N) /\ ~(LENGTH (zs2:(N word)list) = 0)`
        STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [UNDISCH_TAC `LENGTH (zs:(N word)list) = LENGTH (APPEND (if (r3:N word) = word 0 then (res:(N word)list) else md) zs2)` THEN
          ASM_REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC; ASM_MESON_TAC[]]; ALL_TAC] THEN
      MP_TAC(SPECL [`res:(N word)list`; `zs2:(N word)list`; `word (LENGTH (res:(N word)list)):N word`;
        `l1 - 1`] mc_fix_thm) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `mc_div_max xs ys (zs:(N word)list) + 2 * LENGTH zs + 2 <= l` THEN
        UNDISCH_TAC `l <= l1 + mc_div_max xs ys (zs:(N word)list)` THEN
        UNDISCH_TAC `LENGTH (zs:(N word)list) = LENGTH (APPEND (if (r3:N word) = word 0 then (res:(N word)list) else md) zs2)` THEN
        ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r8a:N word` (X_CHOOSE_THEN `l2:num` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[mc_add1_call_def; mc_add1_call_pre_def; LET_DEF; LET_END_DEF; b2w_EQ_0w] THEN
      ASM_CASES_TAC `s <=> (t:bool)` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THENL
    [(SUBGOAL_THEN `LENGTH (mw_fix (res:(N word)list)) < dimword(:N)` ASSUME_TAC THENL
        [MP_TAC(ISPEC `res:(N word)list` LENGTH_mw_fix) THEN ASM_ARITH_TAC; ALL_TAC] THEN
       ASM_SIMP_TAC[LBIGAUX_WORD_LENGTH_EQ_0] THEN
       ASM_CASES_TAC `mw_fix (res:(N word)list) = []` THEN ASM_REWRITE_TAC[] THEN
       CASE_REWRITE_TAC[] THEN
       EXISTS_TAC `APPEND (REPLICATE (LENGTH (res:(N word)list) - LENGTH (mw_fix res)) (word 0:N word)) zs2` THEN
       EXISTS_TAC `l2:num` THEN
       REWRITE_TAC[LBIGAUX_HEADER_NIL; LBIGAUX_SHL1_HEADER; LBIGAUX_B2W_TF] THEN
       REWRITE_TAC[GSYM APPEND_ASSOC] THEN
       ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE; LENGTH] THEN
       MP_TAC(ISPEC `res:(N word)list` LENGTH_mw_fix) THEN
       UNDISCH_TAC `mc_div_max xs ys (zs:(N word)list) + 2 * LENGTH zs + 2 <= l` THEN
       UNDISCH_TAC `l <= l1 + mc_div_max xs ys (zs:(N word)list)` THEN
       UNDISCH_TAC `LENGTH (zs:(N word)list) = LENGTH (APPEND (if (r3:N word) = word 0 then (res:(N word)list) else md) zs2)` THEN
       UNDISCH_TAC `l1 - 1 <= l2 + LENGTH (res:(N word)list)` THEN
       ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC);
     (SUBGOAL_THEN `LENGTH (mw_fix (res:(N word)list)) < dimword(:N)` ASSUME_TAC THENL
        [MP_TAC(ISPEC `res:(N word)list` LENGTH_mw_fix) THEN ASM_ARITH_TAC; ALL_TAC] THEN
       ASM_SIMP_TAC[LBIGAUX_WORD_LENGTH_EQ_0] THEN
       ASM_CASES_TAC `mw_fix (md:(N word)list) = []` THEN ASM_REWRITE_TAC[] THEN
       CASE_REWRITE_TAC[] THENL
        [ASM_SIMP_TAC[LBIGAUX_WORD_LENGTH_EQ_0] THEN
         ASM_CASES_TAC `mw_fix (res:(N word)list) = []` THEN ASM_REWRITE_TAC[] THEN
         CASE_REWRITE_TAC[] THEN
         EXISTS_TAC `APPEND (REPLICATE (LENGTH (res:(N word)list) - LENGTH (mw_fix res)) (word 0:N word)) zs2` THEN
         EXISTS_TAC `l2:num` THEN
         REWRITE_TAC[LBIGAUX_HEADER_NIL; LBIGAUX_SHL1_HEADER; LBIGAUX_B2W_TF] THEN
         REWRITE_TAC[GSYM APPEND_ASSOC] THEN
         ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE; LENGTH] THEN
         MP_TAC(ISPEC `res:(N word)list` LENGTH_mw_fix) THEN
         UNDISCH_TAC `mc_div_max xs ys (zs:(N word)list) + 2 * LENGTH zs + 2 <= l` THEN
         UNDISCH_TAC `l <= l1 + mc_div_max xs ys (zs:(N word)list)` THEN
         UNDISCH_TAC `LENGTH (zs:(N word)list) = LENGTH (APPEND (if (r3:N word) = word 0 then (res:(N word)list) else md) zs2)` THEN
         UNDISCH_TAC `l1 - 1 <= l2 + LENGTH (res:(N word)list)` THEN
         ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
         ALL_TAC] THEN
     REWRITE_TAC[GSYM APPEND_ASSOC] THEN
       MP_TAC(SPECL [`mw_fix (res:(N word)list)`;
         `APPEND (REPLICATE (LENGTH (res:(N word)list) - LENGTH (mw_fix res)) (word 0:N word)) zs2`;
         `l2 - 1`] mc_add1_thm) THEN
       ANTS_TAC THENL
        [REWRITE_TAC[APPEND_EQ_NIL] THEN
         SUBGOAL_THEN `~(zs2:(N word)list = [])` (fun th -> REWRITE_TAC[th]) THENL
          [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
         MP_TAC(ISPEC `res:(N word)list` LENGTH_mw_fix) THEN
         UNDISCH_TAC `mc_div_max xs ys (zs:(N word)list) + 2 * LENGTH zs + 2 <= l` THEN
         UNDISCH_TAC `l <= l1 + mc_div_max xs ys (zs:(N word)list)` THEN
         UNDISCH_TAC `LENGTH (zs:(N word)list) = LENGTH (APPEND (if (r3:N word) = word 0 then (res:(N word)list) else md) zs2)` THEN
         UNDISCH_TAC `l1 - 1 <= l2 + LENGTH (res:(N word)list)` THEN
         UNDISCH_TAC `LENGTH (zs:(N word)list) < dimword(:N)` THEN
         UNDISCH_TAC `~(LENGTH (zs2:(N word)list) = 0)` THEN
         ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
       DISCH_THEN(X_CHOOSE_THEN `rest:(N word)list` (X_CHOOSE_THEN `l3:num` STRIP_ASSUME_TAC)) THEN
       ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
       ASM_SIMP_TAC[LBIGAUX_WORD_LENGTH_EQ_0; LBIGAUX_MW_ADDV_T_NZ] THEN
       CASE_REWRITE_TAC[] THEN
       MAP_EVERY EXISTS_TAC [`rest:(N word)list`; `l3:num`] THEN
       ASM_REWRITE_TAC[LBIGAUX_SHL1_HEADER] THEN
       MP_TAC(ISPEC `res:(N word)list` LENGTH_mw_fix) THEN
       UNDISCH_TAC `mc_div_max xs ys (zs:(N word)list) + 2 * LENGTH zs + 2 <= l` THEN
       UNDISCH_TAC `l <= l1 + mc_div_max xs ys (zs:(N word)list)` THEN
       UNDISCH_TAC `LENGTH (zs:(N word)list) = LENGTH (APPEND (if (r3:N word) = word 0 then (res:(N word)list) else md) zs2)` THEN
       UNDISCH_TAC `l1 - 1 <= l2 + LENGTH (res:(N word)list)` THEN
       UNDISCH_TAC `l2 - 1 <= l3 + LENGTH (mw_fix (res:(N word)list))` THEN
       UNDISCH_TAC `LENGTH (APPEND (mw_addv (mw_fix (res:(N word)list)) [] T) rest) =
                    LENGTH (APPEND (mw_fix res)
                      (APPEND (REPLICATE (LENGTH res - LENGTH (mw_fix res)) (word 0)) zs2))` THEN
       ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE] THEN ARITH_TAC)]);
    (ASM_SIMP_TAC[mc_length] THEN
      REWRITE_TAC[mc_div_sub_call_def; mc_div_sub_call_pre_def; LET_DEF; LET_END_DEF; b2w_EQ_0w] THEN
      ASM_SIMP_TAC[LBIGAUX_WORD_LENGTH_EQ_0] THEN
      ASM_CASES_TAC `s <=> (t:bool)` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
       [ASM_SIMP_TAC[mc_idiv_mod_header_thm] THEN
        EXISTS_TAC `APPEND (REPLICATE (LENGTH (md:(N word)list) - LENGTH (mw_fix md)) (word 0:N word)) zs2` THEN
        EXISTS_TAC `l1:num` THEN
        REWRITE_TAC[GSYM LBIGAUX_MW_FIX_APPEND] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `mc_div_max xs ys (zs:(N word)list) + 2 * LENGTH zs + 2 <= l` THEN
        UNDISCH_TAC `l <= l1 + mc_div_max xs ys (zs:(N word)list)` THEN ARITH_TAC;
        ALL_TAC] THEN
    ASM_CASES_TAC `mw_fix (md:(N word)list) = []` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
       [ASM_SIMP_TAC[mc_idiv_mod_header_thm; LENGTH; ZERO_LT_dimword] THEN
        MAP_EVERY EXISTS_TAC [`APPEND (md:(N word)list) zs2`; `l1:num`] THEN
        REWRITE_TAC[APPEND] THEN
        UNDISCH_TAC `mc_div_max xs ys (zs:(N word)list) + 2 * LENGTH zs + 2 <= l` THEN
        UNDISCH_TAC `l <= l1 + mc_div_max xs ys (zs:(N word)list)` THEN ARITH_TAC;
        ALL_TAC] THEN
    MP_TAC(SPEC `LENGTH (ys:(N word)list)` LBIGAUX_DIV2_LT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`ys:(N word)list`; `md:(N word)list`; `[]:(N word)list`; `zs2:(N word)list`;
        `word (LENGTH (mw_fix (md:(N word)list))):N word`;
        `word (LENGTH (mw_fix (md:(N word)list))):N word`; `l1:num`] mc_div_sub1_thm) THEN
      REWRITE_TAC[APPEND_NIL] THEN ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `mc_div_max xs ys (zs:(N word)list) + 2 * LENGTH zs + 2 <= l` THEN
        UNDISCH_TAC `l <= l1 + mc_div_max xs ys (zs:(N word)list)` THEN
        UNDISCH_TAC `LENGTH (zs:(N word)list) = LENGTH (APPEND (if (r3:N word) = word 0 then (res:(N word)list) else md) zs2)` THEN
        UNDISCH_TAC `LENGTH (zs:(N word)list) < dimword(:N)` THEN
        UNDISCH_TAC `LENGTH (ys:(N word)list) + 1 < dimword(:N)` THEN
        ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r8a:N word` (X_CHOOSE_THEN `r9a:N word`
        (X_CHOOSE_THEN `l2:num` STRIP_ASSUME_TAC))) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      LBIG_PAIR_TAC `mw_sub (ys:(N word)list) md T` `sb:(N word)list` `cb:bool` THEN
      FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP LENGTH_mw_sub) THEN
      ASM_REWRITE_TAC[FST] THEN
      MP_TAC(SPECL [`sb:(N word)list`; `zs2:(N word)list`; `r8a:N word`; `l2 - 1`] mc_fix_thm) THEN
      ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `mc_div_max xs ys (zs:(N word)list) + 2 * LENGTH zs + 2 <= l` THEN
        UNDISCH_TAC `l <= l1 + mc_div_max xs ys (zs:(N word)list)` THEN
        UNDISCH_TAC `l1 <= l2 + LENGTH (ys:(N word)list) + 1` THEN
        UNDISCH_TAC `LENGTH (zs:(N word)list) = LENGTH (APPEND (if (r3:N word) = word 0 then (res:(N word)list) else md) zs2)` THEN
        UNDISCH_TAC `LENGTH (zs:(N word)list) < dimword(:N)` THEN
        ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r8b:N word` (X_CHOOSE_THEN `l3:num` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      SUBGOAL_THEN `mw_subv ys (mw_fix (md:(N word)list)) = mw_fix (sb:(N word)list)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[mw_subv_def; mw_sub_mw_fix]; ALL_TAC] THEN
      SUBGOAL_THEN `LENGTH (mw_fix (sb:(N word)list)) < dimword(:N)` ASSUME_TAC THENL
       [MP_TAC(ISPEC `sb:(N word)list` LENGTH_mw_fix) THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[mc_idiv_mod_header_thm] THEN
      EXISTS_TAC `APPEND (REPLICATE (LENGTH (sb:(N word)list) - LENGTH (mw_fix sb)) (word 0:N word)) zs2` THEN
      EXISTS_TAC `l3:num` THEN
      REWRITE_TAC[GSYM APPEND_ASSOC] THEN
      REWRITE_TAC[TAUT `(if p then F else t) <=> ~p /\ t`] THEN
      ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE] THEN
      MP_TAC(ISPEC `sb:(N word)list` LENGTH_mw_fix) THEN
      UNDISCH_TAC `mc_div_max xs ys (zs:(N word)list) + 2 * LENGTH zs + 2 <= l` THEN
      UNDISCH_TAC `l <= l1 + mc_div_max xs ys (zs:(N word)list)` THEN
      UNDISCH_TAC `l1 <= l2 + LENGTH (ys:(N word)list) + 1` THEN
      UNDISCH_TAC `l2 - 1 <= l3 + LENGTH (ys:(N word)list)` THEN
      UNDISCH_TAC `LENGTH (zs:(N word)list) = LENGTH (APPEND (if (r3:N word) = word 0 then (res:(N word)list) else md) zs2)` THEN
      ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC)]);;

(* ------------------------------------------------------------------------- *)
(* the top-level entry point                                                 *)
(* ------------------------------------------------------------------------- *)

let xor_one_add_one = prove
 (`!w:N word. ~bit 0 w ==> word_xor w (word 1) = word_add w (word 1)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_ADD_XOR THEN
  ASM_REWRITE_TAC[WORD_AND_1_BITVAL; BITVAL_CLAUSES]);;

let add_one_xor_one = prove
 (`!w:N word. ~bit 0 w ==> word_xor (word_add w (word 1)) (word 1) = w`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM xor_one_add_one] THEN
  CONV_TAC WORD_RULE);;

let mc_header_XOR_1 = prove
 (`!s (xs:(N word)list). word_xor (mc_header (s,xs)) (word 1) = mc_header (~s,xs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mc_header_def] THEN
  SUBGOAL_THEN `~bit 0 (word (LENGTH (xs:(N word)list) * 2):N word)` ASSUME_TAC THENL
   [REWRITE_TAC[BIT_LSB_WORD; ODD_MULT; ARITH]; ALL_TAC] THEN
  BOOL_CASES_TAC `s:bool` THEN REWRITE_TAC[WORD_ADD_0] THEN
  ASM_SIMP_TAC[xor_one_add_one; add_one_xor_one]);;

let int_op_rep_def = cake_def
  `(int_op_rep multiword_Add = word 0:N word) /\
   (int_op_rep multiword_Sub = word 1) /\
   (int_op_rep multiword_Lt = word 2) /\
   (int_op_rep Eq = word 3) /\
   (int_op_rep multiword_Mul = word 4) /\
   (int_op_rep multiword_Div = word 5) /\
   (int_op_rep multiword_Mod = word 6) /\
   (int_op_rep multiword_Dec = word 7)`;;

let mc_isub_flip,mc_isub_flip_pre,mc_isub_flip_def,mc_isub_flip_pre_def =
  LBIGAUX_tailrec_define "mc_isub_flip"
  `((\(r1,r3).
      if r3 = word 0 then (INR (r1,r3),T)
      else (let r1 = word_xor r1 (word 1) in (INR (r1,r3),T)))
   :N word#N word -> ((N word#N word) + (N word#N word))#bool)`;;

let mc_iop,mc_iop_pre,mc_iop_def,mc_iop_pre_def =
  LBIGAUX_tailrec_define "mc_iop" (CASE_TERM
  `((\(l,r0,r1,r3,xs,ys,zs).
      if word_ult r3 (word 2) then
        (match mc_isub_flip (r1,r3) with (r1,r3) ->
         let r2 = r1 in
         let r1 = r0 in
         let cnd = mc_iadd_pre (l,r1,r2,xs,ys,zs) in
         match mc_iadd (l,r1,r2,xs,ys,zs) with (l,r10,xs,ys,zs) ->
           (INR (l,r10,xs,ys,zs),cnd))
      else if r3 = word 4 then
        (let r2 = r1 in
         let r1 = r0 in
         let cnd = mc_imul_pre (l,r1,r2,xs,ys,zs) in
         match mc_imul (l,r1,r2,xs,ys,zs) with (l,r10,xs,ys,zs) ->
           (INR (l,r10,xs,ys,zs),cnd))
      else
        (let r3 = word_sub r3 (word 5) in
         let r10 = r0 in
         let r11 = r1 in
         let cnd = mc_idiv_pre (l,r3,r10,r11,xs,ys,zs) in
         match mc_idiv (l,r3,r10,r11,xs,ys,zs) with (l,r11,xs,ys,zs) ->
         let r10 = r11 in
           (INR (l,r10,xs,ys,zs),cnd)))
   :num#N word#N word#N word#(N word)list#(N word)list#(N word)list ->
    ((num#N word#N word#N word#(N word)list#(N word)list#(N word)list) +
     (num#N word#(N word)list#(N word)list#(N word)list))#bool)`);;

let LBIG_IOP_BOUND_TAC =
  UNDISCH_TAC `mc_div_max xs ys (zs:(N word)list) + 2 * LENGTH zs + 2 <= l` THEN
  UNDISCH_TAC `LENGTH (xs:(N word)list) + LENGTH (ys:(N word)list) < LENGTH (zs:(N word)list)` THEN
  REWRITE_TAC[mc_div_max_def] THEN ARITH_TAC;;

let LBIG_IOP_IADD_TAC t =
  MP_TAC(SPECL [`s:bool`; t; `xs:(N word)list`; `ys:(N word)list`; `zs:(N word)list`; `l:num`]
    mc_iadd_thm) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN LBIG_IOP_BOUND_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `zs1:(N word)list` (X_CHOOSE_THEN `l2:num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`zs1:(N word)list`; `l2:num`] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `l <= l2 + 4 * LENGTH (xs:(N word)list) + 4 * LENGTH (ys:(N word)list) + 4` THEN
  LBIG_IOP_BOUND_TAC;;

let LBIG_IOP_IDIV_TAC w =
  MP_TAC(SPECL [`xs:(N word)list`; `ys:(N word)list`; `zs:(N word)list`; `s:bool`; `t:bool`;
    w; `l:num`] mc_idiv_thm) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mwi_divmod_alt_def; GSYM LBIGAUX_WORD_NOT_ZERO_ONE] THEN
  DISCH_THEN(X_CHOOSE_THEN `zs1:(N word)list` (X_CHOOSE_THEN `l2:num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`zs1:(N word)list`; `l2:num`] THEN ASM_REWRITE_TAC[];;

let mc_iop_thm = prove
 (`!(xs:(N word)list) (ys:(N word)list) (zs:(N word)list) s t iop l.
     3 < dimindex(:N)
     ==> (mc_header (s,xs) = word 0 <=> xs = []) /\ mw_ok xs /\
         (mc_header (t,ys) = word 0 <=> ys = []) /\ mw_ok ys /\
         LENGTH xs + LENGTH ys < LENGTH zs /\ LENGTH zs < dimword(:N) DIV 2 /\
         ~(iop = multiword_Lt) /\ ~(iop = Eq) /\ ~(iop = multiword_Dec) /\
         ((iop = multiword_Div \/ iop = multiword_Mod) ==> ~(ys = [])) /\
         mc_div_max xs ys zs + 2 * LENGTH zs + 2 <= l
         ==> ?zs1 l2.
               mc_iop_pre (l,mc_header (s,xs),mc_header (t,ys),int_op_rep iop,xs,ys,zs) /\
               mc_iop (l,mc_header (s,xs),mc_header (t,ys),int_op_rep iop,xs,ys,zs) =
                 (l2,mc_header (mwi_op iop (s,xs) (t,ys)),xs,ys,
                  APPEND (SND (mwi_op iop (s,xs) (t,ys))) zs1) /\
               LENGTH (APPEND (SND (mwi_op iop (s,xs) (t,ys))) zs1) = LENGTH zs /\
               l <= l2 + mc_div_max xs ys zs + 2 * LENGTH zs + 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `16 <= dimword(:N)` ASSUME_TAC THENL
   [REWRITE_TAC[dimword_def] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP 4` THEN CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV; REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b. a < 16 /\ b < 16 ==> ((word a:N word = word b) <=> a = b) /\
                                            (word_ult (word a:N word) (word b) <=> a < b)`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `a < dimword(:N) /\ b < dimword(:N)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LBIGAUX_WORD_EQ_LT; word_lo_n2w; MOD_LT]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (xs:(N word)list) < dimword(:N) DIV 2 /\
                LENGTH (ys:(N word)list) < dimword(:N) DIV 2 /\
                LENGTH (xs:(N word)list) + LENGTH (ys:(N word)list) <= LENGTH (zs:(N word)list)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(cases "mw_op") THEN DISCH_THEN(MP_TAC o SPEC `iop:mw_op`) THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "mw_op"]) THEN
  ASM_REWRITE_TAC[int_op_rep_def; mwi_op_def; distinctness "mw_op"] THEN
  REWRITE_TAC[mc_iop_def; mc_iop_pre_def; LET_DEF; LET_END_DEF] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < 16 /\ 1 < 16 /\ 2 < 16 /\ 4 < 16 /\ 5 < 16 /\ 6 < 16`] THEN
  CONV_TAC NUM_REDUCE_CONV THENL
   [(TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
       REWRITE_TAC[mc_isub_flip_def; LET_DEF; LET_END_DEF] THEN
       ASM_SIMP_TAC[ARITH_RULE `0 < 16 /\ 1 < 16`; WORD_SUB_REFL] THEN CONV_TAC NUM_REDUCE_CONV THEN
       CASE_REWRITE_TAC[] THEN LBIG_IOP_IADD_TAC `t:bool`);
    (TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
       REWRITE_TAC[mc_isub_flip_def; LET_DEF; LET_END_DEF] THEN
       ASM_SIMP_TAC[ARITH_RULE `0 < 16 /\ 1 < 16`; WORD_SUB_REFL] THEN CONV_TAC NUM_REDUCE_CONV THEN
       CASE_REWRITE_TAC[] THEN REWRITE_TAC[mc_header_XOR_1; mwi_sub_def] THEN
       LBIG_IOP_IADD_TAC `~t:bool`);
    (MP_TAC(SPECL [`s:bool`; `t:bool`; `xs:(N word)list`; `ys:(N word)list`; `zs:(N word)list`;
         `l:num`] mc_imul_thm) THEN
       ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN LBIG_IOP_BOUND_TAC; ALL_TAC] THEN
       DISCH_THEN(X_CHOOSE_THEN `zs1:(N word)list` (X_CHOOSE_THEN `l2:num` STRIP_ASSUME_TAC)) THEN
       ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
       MAP_EVERY EXISTS_TAC [`zs1:(N word)list`; `l2:num`] THEN ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `l <= l2 + 3 * LENGTH (xs:(N word)list) + 3 * LENGTH (ys:(N word)list) +
                      LENGTH xs * LENGTH ys + 3` THEN
       LBIG_IOP_BOUND_TAC);
    (REWRITE_TAC[WORD_SUB_REFL] THEN LBIG_IOP_IDIV_TAC `word 0:N word`);
    (SUBGOAL_THEN `word_sub (word 6) (word 5):N word = word 1` SUBST1_TAC THENL
        [MATCH_MP_TAC LBIGAUX_WORD_SUB_EQ THEN ARITH_TAC; ALL_TAC] THEN
       LBIG_IOP_IDIV_TAC `word 1:N word`);
    (FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`)));
    (FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`)));
    (FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`)))]);;

(* ------------------------------------------------------------------------- *)
(* an example with non-tail recursion (HOL4's tDefine of mc_fac and         *)
(* mc_fac_pre is rendered with cake_def_wf and the measure FST)             *)
(* ------------------------------------------------------------------------- *)

let mc_fac_init,mc_fac_init_pre,mc_fac_init_def,mc_fac_init_pre_def =
  LBIGAUX_tailrec_define "mc_fac_init"
  `((\(l,r1).
      if word_ult r1 (word 2) then
        (let r0 = word 0 in
         let r2 = word 0 in
         let r3 = word 0 in
         let cnd = T in
           (INR (l,r0,r1,r2,r3),cnd))
      else
        (let r0 = word 1 in
         let r2 = word_sub r1 (word 1) in
         let r3 = word_sub r1 (word 2) in
         let cnd = T in
           (INR (l,r0,r1,r2,r3),cnd)))
   :num#N word -> ((num#N word) + (num#N word#N word#N word#N word))#bool)`;;

let mc_fac_final,mc_fac_final_pre,mc_fac_final_def,mc_fac_final_pre_def =
  LBIGAUX_tailrec_define "mc_fac_final"
  `((\(l,r1,r2).
      (let r1 = word_add r1 r2 in
       let cnd = T in
         (INR (l,r1),cnd)))
   :num#N word#N word -> ((num#N word#N word) + (num#N word))#bool)`;;

let mc_fac_def = cake_def_wf `measure (FST:num#N word->num)`
  (REWRITE_TAC WF_REL_THMS THEN REWRITE_TAC[FST] THEN REPEAT STRIP_TAC THEN
   REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> not (is_forall (concl th))))) THEN
   REWRITE_TAC[MIN] THEN ARITH_TAC)
  `mc_fac (l:num,r1:N word) =
     let l0 = l in
     match mc_fac_init (l,r1) with (l,r0,r1,r2,r3) ->
     let l = MIN l l0 in
       if r0 = word 0 then (l,r1) else
       let r1 = r2 in
       if l = 0 then (l,r1) else
       match ((r2,r3),mc_fac (l - 1,r1)) with ((r2,r3),(l,r1)) ->
       let l = MIN l l0 in
       let r2 = r1 in
       let r1 = r3 in
       if l = 0 then (l,r1) else
       match (r2,mc_fac (l - 1,r1)) with (r2,(l,r1)) ->
       match mc_fac_final (l,r1,r2) with (l,r1) ->
         (l,r1)`;;

let mc_fac_pre_def = cake_def_wf `measure (FST:num#N word->num)`
  (REWRITE_TAC WF_REL_THMS THEN REWRITE_TAC[FST] THEN REPEAT STRIP_TAC THEN
   REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> not (is_forall (concl th))))) THEN
   REWRITE_TAC[MIN] THEN ARITH_TAC)
  `mc_fac_pre (l:num,r1:N word) <=>
     let l0 = l in
     let cnd = mc_fac_init_pre (l,r1) in
     match mc_fac_init (l,r1) with (l,r0,r1,r2,r3) ->
     let l = MIN l l0 in
       if r0 = word 0 then F else
       let r1 = r2 in
       if l = 0 then F else
       let cnd = (mc_fac_pre (l - 1,r1) /\ cnd) in
       match ((r2,r3),mc_fac (l - 1,r1)) with ((r2,r3),(l,r1)) ->
       let l = MIN l l0 in
       let r2 = r1 in
       let r1 = r3 in
       if l = 0 then F else
       let cnd = (mc_fac_pre (l - 1,r1) /\ cnd) in
       let cnd = (mc_fac_final_pre (l,r1,r2) /\ cnd) in
       match mc_fac_final (l,r1,r2) with (l,r1) ->
         cnd`;;

let mc_use_fac,mc_use_fac_pre,mc_use_fac_def,mc_use_fac_pre_def =
  LBIGAUX_tailrec_define "mc_use_fac" (CASE_TERM
  `((\(l,r1).
      (let cnd = (mc_fac_pre (l - 1,r1) /\ ~(l = 0)) in
       match mc_fac (l - 1,r1) with (l,r1) ->
       let r0 = r1 in
         (INR (l,r0),cnd)))
   :num#N word -> ((num#N word) + (num#N word))#bool)`);;
