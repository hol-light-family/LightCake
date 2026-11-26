(* ========================================================================= *)
(* crep_arith: port of HOL4 pancake/crep_arithScript.sml (CakeML v3479).     *)
(* Simplification of arithmetic in crepLang.                                 *)
(*                                                                           *)
(* Notes on the rendering: 0w is word 0, 1w is word 1, n2w is word, && is    *)
(* word_and, word_lsr is word_ushr, word_lsl is word_shl, * on words is      *)
(* word_mul; HOL4 Mul, Lsl are crep_Mul, Lsl.                               *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "pancake/crepLang.ml";;

prioritize_num();;
type_invention_error := true;;

let dest_const_def = cake_def
  `(dest_const (crep_Const (w:A word)) = SOME w) /\
   (dest_const _ = NONE)`;;

(* termination: the word shifted right by one is smaller (it is not 0) *)

let dest_2exp_def = cake_def_wf
  `MEASURE (\(n:num,w:A word). val w)`
  (REWRITE_TAC[measure_THM; FORALL_PAIR_THM] THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `val(word_ushr (w:A word) 1) < val w` MP_TAC THENL
    [REWRITE_TAC[VAL_WORD_USHR; EXP_1] THEN
     MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> n DIV 2 < n`) THEN
     ASM_REWRITE_TAC[VAL_EQ_0];
     DECIDE_TAC])
  `dest_2exp n (w:A word) =
     if w = word 0 then NONE
     else if w = word 1 then SOME n
     else if ~(word_and w (word 1) = word 0) then NONE
     else dest_2exp (n + 1) (word_ushr w 1)`;;

let dest_2exp_ind = cake_ind "dest_2exp";;

(* HOL4: [local] *)

let dest_2exp_lemma = prove
 (`!i (w:A word) n. dest_2exp i w = SOME n ==>
     i <= n /\ w = word_shl (word 1) (n - i)`,
  REC_IND_TAC dest_2exp_ind THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RW[ONCE dest_2exp_def] THEN RFS[WORD_SHL_ZERO] THEN TRY DECIDE_TAC THEN
  QSUFF_TAC "alignment_aligned 1 w" THENL
   [RW[aligned_def] THEN
    FIRST_X_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    ASM_REWRITE_TAC[align_shift; WORD_SHL_COMPOSE] THEN
    AP_TERM_TAC THEN DECIDE_TAC;
    REWRITE_TAC[aligned_bitwise_and] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[]]);;

let dest_2exp_thm = prove
 (`dest_2exp 0 (w:A word) = SOME n2 ==> w = word_shl (word 1) n2`,
  RW[] THEN IMP_RES_TAC dest_2exp_lemma THEN FS[SUB_0]);;

let mul_const_def = cake_def
  `mul_const exp (c:A word) =
     if c = word 0 then crep_Const (word 0)
     else if c = word 1 then exp
     else match dest_2exp 0 c with
            NONE -> Crepop crep_Mul [exp; crep_Const c]
          | SOME i -> crep_Shift Lsl exp (crep_Const (word i))`;;

(* the let is kept for the recursion analysis (HOL4's LET_CONG), so that   *)
(* simp_exp_ind has HOL4's case for Crepop: MEM y exps ==> P y              *)

cake_let_cong := true;;

let simp_exp_def = cake_def_wf
  `MEASURE (crep_exp_size (combin_K 0):(A)crep_exp->num)`
  TERM_TAC
  `(simp_exp (Crepop op exps:(A)crep_exp) =
      let exps = MAP simp_exp exps in
      match (op,exps) with
        (crep_Mul,[exp1; exp2]) ->
          (match (dest_const exp1,dest_const exp2) with
             (SOME c,SOME c2) -> crep_Const (word_mul c c2)
           | (SOME c,_) -> mul_const exp2 c
           | (_,SOME c) -> mul_const exp1 c
           | _ -> Crepop op exps)
      | _ -> Crepop op exps) /\
   (simp_exp (crep_Load32 exp) = crep_Load32 (simp_exp exp)) /\
   (simp_exp (crep_LoadByte exp) = crep_LoadByte (simp_exp exp)) /\
   (simp_exp (crep_Load exp) = crep_Load (simp_exp exp)) /\
   (simp_exp (crep_Op bop exps) = crep_Op bop (MAP simp_exp exps)) /\
   (simp_exp (crep_Cmp cmp exp1 exp2) =
      crep_Cmp cmp (simp_exp exp1) (simp_exp exp2)) /\
   (simp_exp (crep_Shift s exp1 exp2) =
      crep_Shift s (simp_exp exp1) (simp_exp exp2)) /\
   (simp_exp exp = exp)`;;

cake_let_cong := false;;

let simp_exp_ind = cake_ind "simp_exp";;

(* the clause for crep_Return is parsed apart: exp is an expression list    *)
(* there and an expression in the other clauses                            *)

let simp_prog_def = cake_def
  (list_mk_conj
   [`(simp_prog (crep_Dec v exp p:(A)crep_prog) =
        crep_Dec v (simp_exp exp) (simp_prog p)) /\
     (simp_prog (crep_Assign v exp) = crep_Assign v (simp_exp exp)) /\
     (simp_prog (crep_Store exp1 exp2) =
        crep_Store (simp_exp exp1) (simp_exp exp2)) /\
     (simp_prog (crep_Store32 exp1 exp2) =
        crep_Store32 (simp_exp exp1) (simp_exp exp2)) /\
     (simp_prog (crep_StoreByte exp1 exp2) =
        crep_StoreByte (simp_exp exp1) (simp_exp exp2)) /\
     (simp_prog (StoreGlob g exp) = StoreGlob g (simp_exp exp)) /\
     (simp_prog (crep_Seq p1 p2) = crep_Seq (simp_prog p1) (simp_prog p2)) /\
     (simp_prog (crep_If exp p1 p2) =
        crep_If (simp_exp exp) (simp_prog p1) (simp_prog p2)) /\
     (simp_prog (crep_While exp p) = crep_While (simp_exp exp) (simp_prog p)) /\
     (simp_prog (crep_Call call_type e exps) =
        let call_type2 =
          match call_type with
            NONE -> NONE
          | SOME (rv,opt_handler) ->
              SOME (rv,match opt_handler with
                         NONE -> NONE
                       | SOME (ix,ep) -> SOME (ix,simp_prog ep)) in
        crep_Call call_type2 e (MAP simp_exp exps))`;
    `simp_prog (crep_Return exp:(A)crep_prog) =
       crep_Return (MAP simp_exp exp)`;
    `(simp_prog (crep_ShMem op vn exp:(A)crep_prog) =
        crep_ShMem op vn (simp_exp exp)) /\
     (simp_prog p = p)`]);;

let simp_prog_ind = cake_ind "simp_prog";;
