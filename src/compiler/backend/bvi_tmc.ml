(* ========================================================================= *)
(* bvi_tmc: port of HOL4 compiler/backend/bvi_tmcScript.sml (CakeML v3479).  *)
(* Perform tailrec modulo cons optimisation to make more functions           *)
(* tail-recursive.                                                           *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 exp_size is bvi_exp_size, its exp2_size list_size bvi_exp_size;    *)
(*   EVERY is ALL; cj 2 th is CONJUNCT2 th.                                  *)
(* - The clauses of a HOL Light definition share their variables, so the     *)
(*   arguments of LetCall in pure_exp get their own names.                   *)
(* - Definitions with catch-all or overlapping clauses are made with         *)
(*   sem1aux_def(_wf) (HOL4's TFL completion).                               *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/backend_common.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

let bvi_tmc_pure_op_def = sem1aux_def
  `(bvi_tmc_pure_op (clos_Label _) (_:A list) <=> F) /\
   (bvi_tmc_pure_op (clos_FFI _) _ <=> F) /\
   (bvi_tmc_pure_op (IntOp (clos_Const n)) [] <=> small_enough_int n) /\
   (bvi_tmc_pure_op (IntOp _) _ <=> F) /\
   (bvi_tmc_pure_op (WordOp _) _ <=> F) /\
   (bvi_tmc_pure_op (BlockOp (clos_Cons _)) _ <=> T) /\
   (bvi_tmc_pure_op (BlockOp _) _ <=> F) /\
   (bvi_tmc_pure_op (GlobOp _) _ <=> F) /\
   (bvi_tmc_pure_op (MemOp _) _ <=> F) /\
   (bvi_tmc_pure_op clos_Install _ <=> F) /\
   (bvi_tmc_pure_op (clos_ThunkOp _) _ <=> F)`;;

let pure_exp_def = sem1aux_def_wf
  `measure (\x:(num # bvi_exp) + (num # bvi_exp list).
              sum_CASE x (\p. bvi_exp_size (SND p))
                         (\p. list_size bvi_exp_size (SND p)))`
  SEM1AUX_TC_TAC
  `(pure_exp n (bvi_Var v) <=> v < n) /\
   (pure_exp n (bvi_If e1 e2 e3) <=> F) /\
   (pure_exp n (bvi_Let es e) <=> pure_exp n e /\ pure_exps n es) /\
   (pure_exp n (bvi_Raise _) <=> F) /\
   (pure_exp n (bvi_Tick e) <=> F) /\
   (pure_exp n (bvi_Call _ _ _ _) <=> F) /\
   (pure_exp n (bvi_Force _ _) <=> F) /\
   (pure_exp n (LetCall _ _ _ _ _) <=> F) /\
   (pure_exp n (bvi_Return _) <=> F) /\
   (pure_exp n (bvi_Op op args) <=> bvi_tmc_pure_op op args /\ pure_exps n args) /\
   (pure_exps n [] <=> T) /\
   (pure_exps n (CONS h t) <=> pure_exp n h /\ pure_exps n t)`;;

let pure_exp_ind = cake_ind "pure_exp";;

let pure_exps_sing = prove
 (`!n h. pure_exps n [h] <=> pure_exp n h`,
  REWRITE_TAC[pure_exp_def]);;
let _ = cake_add_simps [pure_exps_sing];;

let pure_exps_cons = prove
 (`!n h t. pure_exps n [h] /\ pure_exps n t <=> pure_exps n (CONS h t)`,
  REWRITE_TAC[pure_exp_def]);;

(* The equations below express pure_exps without the auxiliary pure_exp.   *)
(* This is the shape the ml_translator prefers (cf. bvi_let compile_def),   *)
(* whereas the mutually recursive pure_exp_def above is the shape cv_trans  *)
(* requires.                                                                 *)

let pure_exps_eqns = prove
 (`(pure_exps n [] <=> T) /\
   (pure_exps n [bvi_Var v] <=> v < n) /\
   (pure_exps n [bvi_If e1 e2 e3] <=> F) /\
   (pure_exps n [bvi_Let les le] <=> pure_exps n [le] /\ pure_exps n les) /\
   (pure_exps n [bvi_Raise re] <=> F) /\
   (pure_exps n [bvi_Tick te] <=> F) /\
   (pure_exps n [bvi_Call ct cd cargs ch] <=> F) /\
   (pure_exps n [bvi_Force fl fw] <=> F) /\
   (pure_exps n [LetCall la lb lc largs lce] <=> F) /\
   (pure_exps n [bvi_Return res] <=> F) /\
   (pure_exps n [bvi_Op oop oargs] <=>
      bvi_tmc_pure_op oop oargs /\ pure_exps n oargs) /\
   (pure_exps n (CONS x1 (CONS x2 xs)) <=>
      pure_exps n [x1] /\ pure_exps n (CONS x2 xs))`,
  REWRITE_TAC[pure_exp_def]);;

let pure_exp_eq = prove
 (`!n e. pure_exp n e <=> pure_exps n [e]`,
  REWRITE_TAC[pure_exp_def]);;

let pure_exps_append = prove
 (`!n es1 es2.
     pure_exps n es1 /\ pure_exps n es2 ==> pure_exps n (APPEND es1 es2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_SIMP_TAC[APPEND; pure_exp_def]);;

let bvi_tmc_dest_Cons_def = sem1aux_def
  `(bvi_tmc_dest_Cons (BlockOp (clos_Cons block_tag)) = SOME block_tag) /\
   (bvi_tmc_dest_Cons _ = NONE)`;;

(* PHASE 1: extract everything into a let bound "call block".             *)
(* CallBlock tag left child right is the "skeleton" of the BlockOp Cons    *)
(* - with the same tag,                                                     *)
(* - where the recursive call is at the bottom of child,                    *)
(* - where left and right are de Bruijn indices of the other args,          *)
(*   positions preserved, with the original expressions assumed to be let   *)
(*   bound.                                                                 *)

let call_block_INDUCT,call_block_RECURSION = cake_type
  "call_block = CallBlock num (num list) call_block (num list)
              | RCall num (num list)";;

let bind_def = cake_def
  `(bind (n:num) ([]:A list) = ([],n)) /\
   (bind (n:num) (CONS (_:A) t) =
      match bind (n + 1) t with
        (vs,n') -> (CONS n vs,n'))`;;

let bind_size = prove
 (`!args n vs n'. bind n (args:A list) = (vs,n') ==> LENGTH args = LENGTH vs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[bind_def; PAIR_EQ] THENL
   [MESON_TAC[LENGTH]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN
  ASM_MESON_TAC[]);;

let shift_vars_def = cake_def
  `(shift_vars (n:num) [] = []) /\
   (shift_vars (n:num) (CONS h t) = CONS (h + n:num) (shift_vars n t))`;;

let shift_cb_def = cake_def
  `(shift_cb n (RCall ts args) = RCall ts (shift_vars n args)) /\
   (shift_cb n (CallBlock tag l c r) =
      let l' = shift_vars n l in
      let c' = shift_cb n c in
      let r' = shift_vars n r in
        CallBlock tag l' c' r')`;;

let call_to_cb_def = cake_def
  `call_to_cb (loc:A) call_ts call_loc (call_args:C list) (call_h:B option) =
     if call_loc = SOME loc /\ call_h = NONE then
       match bind 0 call_args with
         (vs,_) -> SOME (call_args,RCall call_ts vs)
     else NONE`;;

let shift_vars_zero = prove
 (`!ns. shift_vars 0 ns = ns`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[shift_vars_def; ADD_CLAUSES]);;

let length_shift_vars = prove
 (`!l n. LENGTH (shift_vars n l) = LENGTH l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[shift_vars_def; LENGTH]);;

let shift_vars_dist = prove
 (`!l n1 n2. shift_vars n1 (shift_vars n2 l) = shift_vars (n1 + n2) l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[shift_vars_def; CONS_11] THEN
  ARITH_TAC);;

let shift_cb_dist = prove
 (`!cb n1 n2. shift_cb n1 (shift_cb n2 cb) = shift_cb (n1 + n2) cb`,
  MATCH_MP_TAC call_block_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[shift_cb_def; LET_DEF; LET_END_DEF; shift_vars_dist]);;

(* Attempts to build a CallBlock from the tag and args of a BlockOp Cons.  *)
(* If no recursive call found, returns each op arg expression in a list    *)
(* and (INL) a list of corresponding de Bruijn indices.  If a recursive    *)
(* call is found, returns all extracted/let-bound expressions and (INR)    *)
(* the call block.  If an effectful operation appears right of the         *)
(* recursive call, the expression is not eligible for transformation and   *)
(* NONE is returned.  If multiple recursive calls are found, all but the   *)
(* last are let bound.                                                      *)

let bvi_to_cb_aux_def = sem1aux_def_wf
  `measure (\x:(num # num # num # bvi_exp) + (num # num # num # bvi_exp list).
              sum_CASE x (\p. bvi_exp_size (SND (SND (SND p))))
                         (\p. list_size bvi_exp_size (SND (SND (SND p)))))`
  SEM1AUX_TC_TAC
  `(bvi_to_cb_aux_sing n loc tag (bvi_Call t' loc' args h') =
      match call_to_cb loc t' loc' args h' with
        SOME (bs,cb) -> SOME (bs,INR (CallBlock tag [] cb []))
      | _ -> NONE) /\
   (bvi_to_cb_aux_sing n loc tag (bvi_Op op args) =
      match bvi_tmc_dest_Cons op with
        SOME tag' ->
          (match bvi_to_cb_aux n loc tag' args with
             NONE -> NONE
           | SOME (bs,INL vs) ->
               if pure_exp n (bvi_Op op args) then
                 SOME ([bvi_Op op args],INL [0])
               else NONE
           | SOME (bs,INR cb) -> SOME (bs,INR (CallBlock tag [] cb [])))
      | NONE ->
          if pure_exp n (bvi_Op op args) then SOME ([bvi_Op op args],INL [0])
          else NONE) /\
   (bvi_to_cb_aux_sing n _ _ exp =
      if pure_exp n exp then SOME ([exp],INL [0]) else NONE) /\
   (bvi_to_cb_aux _ _ _ [] = SOME ([],INL [])) /\
   (bvi_to_cb_aux n loc tag [exp] = bvi_to_cb_aux_sing n loc tag exp) /\
   (bvi_to_cb_aux n loc tag (CONS h t) =
      match bvi_to_cb_aux n loc tag t with
        NONE -> NONE
      | SOME (bs2,INL vs2) ->
          (match bvi_to_cb_aux_sing n loc tag h with
             NONE -> NONE
           | SOME (bs1,INL vs1) ->
               if small_enough_int (&(LENGTH vs1 + LENGTH vs2)) then
                 let vs2' = shift_vars (LENGTH bs1) vs2 in
                   SOME (APPEND bs1 bs2,INL (APPEND vs1 vs2'))
               else NONE
           | SOME (bs1,INR (CallBlock _ [] child [])) ->
               let vs2' = shift_vars (LENGTH bs1) vs2 in
                 SOME (APPEND bs1 bs2,INR (CallBlock tag [] child vs2'))
           | _ -> NONE)
      | SOME (bs2,INR cb) ->
          (match shift_cb 1 cb with
             CallBlock tag l child r ->
               let cb' = CallBlock tag (CONS 0 l) child r in
                 SOME (CONS h bs2,INR cb')
           | _ -> NONE))`;;

let bvi_to_cb_aux_ind = cake_ind "bvi_to_cb_aux";;

let wf_vars_def = cake_def
  `wf_vars n (vs:num list) <=> ALL (\v. v < n) vs`;;

let wf_vars_empty = prove
 (`!n. wf_vars n []`,
  REWRITE_TAC[wf_vars_def; ALL]);;

let wf_vars_expand = prove
 (`!n1 n2 vs. wf_vars n1 vs /\ n1 <= n2 ==> wf_vars n2 vs`,
  REWRITE_TAC[wf_vars_def; GSYM ALL_MEM] THEN MESON_TAC[LTE_TRANS]);;

let wf_vars_shift = prove
 (`!n1 n2 vs. wf_vars n1 vs ==> wf_vars (n2 + n1) (shift_vars n2 vs)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[wf_vars_def; shift_vars_def; ALL] THEN
  REWRITE_TAC[GSYM wf_vars_def] THEN ASM_SIMP_TAC[] THEN ARITH_TAC);;

let wf_vars_shift_sing = prove
 (`!n vs. wf_vars n vs ==> wf_vars (SUC n) (shift_vars 1 vs)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `1` o MATCH_MP wf_vars_shift) THEN
  REWRITE_TAC[ARITH_RULE `1 + n = SUC n`]);;

let wf_vars_append = prove
 (`!n vs1 vs2. wf_vars n vs1 /\ wf_vars n vs2 ==> wf_vars n (APPEND vs1 vs2)`,
  SIMP_TAC[wf_vars_def; ALL_APPEND]);;

let wf_vars_cons = prove
 (`!n v vs. v < n /\ wf_vars n vs ==> wf_vars n (CONS v vs)`,
  SIMP_TAC[wf_vars_def; ALL]);;

let wf_vars_bind = prove
 (`!bs vs n n'. bind n (bs:A list) = (vs,n') ==> wf_vars (n + LENGTH bs) vs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[bind_def; PAIR_EQ] THENL
   [MESON_TAC[wf_vars_empty]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN MATCH_MP_TAC wf_vars_cons THEN
  CONJ_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> FIRST_X_ASSUM(MP_TAC o MATCH_MP th)) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `(n + 1) + l = n + SUC l`]);;

let wf_cb_def = cake_def
  `(wf_cb n (RCall ts args) <=> wf_vars n args) /\
   (wf_cb n (CallBlock tag left child right) <=>
      wf_vars n left /\ wf_cb n child /\ wf_vars n right /\
      small_enough_int (&(LENGTH right)))`;;

let wf_cb_expand = prove
 (`!n1 n2 cb. wf_cb n1 cb /\ n1 <= n2 ==> wf_cb n2 cb`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC call_block_INDUCT THEN
  REWRITE_TAC[wf_cb_def] THEN MESON_TAC[wf_vars_expand]);;

let wf_cb_shift_sing = prove
 (`!n cb. wf_cb n cb ==> wf_cb (SUC n) (shift_cb 1 cb)`,
  GEN_TAC THEN MATCH_MP_TAC call_block_INDUCT THEN
  REWRITE_TAC[wf_cb_def; shift_cb_def; LET_DEF; LET_END_DEF;
              length_shift_vars] THEN
  MESON_TAC[wf_vars_shift_sing]);;

let BVIPAUX_TMC_wf_vars_append_shift = prove
 (`!n1 n2 vs1 vs2.
     wf_vars n1 vs1 /\ wf_vars n2 vs2
     ==> wf_vars (n1 + n2) (APPEND vs1 (shift_vars n1 vs2))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC wf_vars_append THEN CONJ_TAC THENL
   [MATCH_MP_TAC wf_vars_expand THEN EXISTS_TAC `n1:num` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    MATCH_MP_TAC wf_vars_shift THEN ASM_REWRITE_TAC[]]);;

let bvi_to_cb_aux_wf_inl_lemma = prove
 (`(!n loc tag exp bs vs.
      bvi_to_cb_aux_sing n loc tag exp = SOME (bs,INL vs) ==>
      pure_exps n bs /\ wf_vars (LENGTH bs) vs /\
      small_enough_int (&(LENGTH vs))) /\
   (!n loc tag args bs vs.
      bvi_to_cb_aux n loc tag args = SOME (bs,INL vs) ==>
      pure_exps n bs /\ wf_vars (LENGTH bs) vs /\
      small_enough_int (&(LENGTH vs)))`,
  MATCH_MP_TAC bvi_to_cb_aux_ind THEN REPEAT STRIP_TAC THEN
  GVS[bvi_to_cb_aux_def; option_case_eq; sum_case_eq; pair_case_eq;
      case_eq "call_block"; list_case_eq; COND_CASE_EQ; length_shift_vars] THEN
  TRY(ASM_SIMP_TAC[pure_exps_append; BVIPAUX_TMC_wf_vars_append_shift; LENGTH_APPEND] THEN
      NO_TAC) THEN
  REWRITE_TAC[pure_exp_def; wf_vars_def; ALL; small_enough_int_def; LENGTH] THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let bvi_to_cb_aux_wf_inl = CONJUNCT2 bvi_to_cb_aux_wf_inl_lemma;;

let bvi_to_cb_aux_sing = prove
 (`!n loc tag arg bs cb.
     bvi_to_cb_aux n loc tag [arg] = SOME (bs,INR cb) ==>
     ?child. cb = CallBlock tag [] child []`,
  REPEAT GEN_TAC THEN CASES_ON `arg:bvi_exp` THEN
  REWRITE_TAC[bvi_to_cb_aux_def] THEN
  GVS[option_case_eq; sum_case_eq; pair_case_eq; COND_CASE_EQ] THEN
  REPEAT STRIP_TAC THEN GVS[] THEN MESON_TAC[]);;

let bvi_to_cb_aux_wf_inr_lemma = prove
 (`(!n loc tag exp bs cb.
      bvi_to_cb_aux_sing n loc tag exp = SOME (bs,INR cb) ==>
      wf_cb (LENGTH bs) cb /\ ?l child r. cb = CallBlock tag l child r) /\
   (!n loc tag args bs cb.
      bvi_to_cb_aux n loc tag args = SOME (bs,INR cb) ==>
      wf_cb (LENGTH bs) cb /\ ?l child r. cb = CallBlock tag l child r)`,
  MATCH_MP_TAC bvi_to_cb_aux_ind THEN REPEAT STRIP_TAC THEN
  GVS[bvi_to_cb_aux_def; call_to_cb_def; wf_cb_def; shift_cb_def;
      option_case_eq; sum_case_eq; pair_case_eq; case_eq "call_block";
      list_case_eq; COND_CASE_EQ; wf_vars_empty; length_shift_vars;
      LET_DEF; LET_END_DEF] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvi_to_cb_aux_wf_inl)) THEN
  TRY(FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[ADD_CLAUSES] o
                  MATCH_MP wf_vars_bind)) THEN
  ASM_REWRITE_TAC[small_enough_int_def] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM small_enough_int_def] THEN
  ASM_SIMP_TAC[wf_vars_cons; wf_vars_shift_sing; wf_cb_shift_sing;
               wf_vars_shift; LT_0] THEN
  ASM_MESON_TAC[wf_cb_expand; LE_ADD; ADD_SYM]);;

let bvi_to_cb_aux_wf_inr = CONJUNCT2 bvi_to_cb_aux_wf_inr_lemma;;

let bvi_to_cb_def = sem1aux_def
  `(bvi_to_cb n loc (bvi_Call call_ts call_loc call_args call_h) =
      call_to_cb loc call_ts call_loc call_args call_h) /\
   (bvi_to_cb n loc (bvi_Op op xs) =
      match bvi_tmc_dest_Cons op with
        SOME tag ->
          (match bvi_to_cb_aux n loc tag xs with
             SOME (bs,INR cb) -> SOME (bs,cb)
           | _ -> NONE)
      | _ -> NONE) /\
   (bvi_to_cb _ _ _ = NONE)`;;

let bvi_to_cb_wf = prove
 (`!n loc x bs cb. bvi_to_cb n loc x = SOME (bs,cb) ==> wf_cb (LENGTH bs) cb`,
  REPEAT GEN_TAC THEN CASES_ON `x:bvi_exp` THEN
  REWRITE_TAC[bvi_to_cb_def; call_to_cb_def] THEN
  GVS[option_case_eq; pair_case_eq; sum_case_eq; COND_CASE_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[wf_cb_def] THEN
  TRY(FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[ADD_CLAUSES] o
                  MATCH_MP wf_vars_bind)) THEN
  ASM_MESON_TAC[bvi_to_cb_aux_wf_inr]);;

let BVIPAUX_TMC_dest_Cons_SOME = prove
 (`!op tag. bvi_tmc_dest_Cons op = SOME tag <=> op = BlockOp (clos_Cons tag)`,
  SUBGOAL_THEN
   `!b tag. bvi_tmc_dest_Cons (BlockOp b) = SOME tag <=> b = clos_Cons tag`
   ASSUME_TAC THENL
   [GEN_TAC THEN CASES_ON `b:block_op` THEN
    REWRITE_TAC[bvi_tmc_dest_Cons_def] THEN CASE_REWRITE_TAC[] THEN
    MESON_TAC[];
    GEN_TAC THEN CASES_ON `op:clos_op` THEN
    ASM_REWRITE_TAC[bvi_tmc_dest_Cons_def] THEN CASE_REWRITE_TAC[]]);;

let bvi_to_cb_cases = prove
 (`!n loc x bs cb.
     bvi_to_cb n loc x = SOME (bs,cb) ==>
     (?tag args l child r.
        x = bvi_Op (BlockOp (clos_Cons tag)) args /\
        cb = CallBlock tag l child r) \/
     (?ts args vs. x = bvi_Call ts (SOME loc) args NONE /\ cb = RCall ts vs)`,
  REPEAT GEN_TAC THEN CASES_ON `x:bvi_exp` THEN
  REWRITE_TAC[bvi_to_cb_def; call_to_cb_def] THEN
  GVS[option_case_eq; pair_case_eq; sum_case_eq; COND_CASE_EQ;
      BVIPAUX_TMC_dest_Cons_SOME] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  TRY(FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvi_to_cb_aux_wf_inr)) THEN
  RVEQ_TAC THEN CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

(* Convert back to BlockOp Cons for comparing semantics *)

let cb_to_bvi_def = cake_def
  `(cb_to_bvi loc (CallBlock tag l child r) =
      let l' = MAP (\n. bvi_Var n) l in
      let child' = cb_to_bvi loc child in
      let r' = MAP (\n. bvi_Var n) r in
        bvi_Op (BlockOp (clos_Cons tag)) (APPEND (APPEND l' [child']) r')) /\
   (cb_to_bvi loc (RCall ts args) =
      let args' = MAP (\n. bvi_Var n) args in
        bvi_Call ts (SOME loc) args' NONE)`;;

let bvi_to_cb_aux_size_lemma = prove
 (`(!n loc tag exp bs sm.
      bvi_to_cb_aux_sing n loc tag exp = SOME (bs,sm) ==>
      list_size bvi_exp_size bs <= bvi_exp_size exp + 1) /\
   (!n loc tag args bs sm.
      bvi_to_cb_aux n loc tag args = SOME (bs,sm) ==>
      list_size bvi_exp_size bs <= list_size bvi_exp_size args)`,
  MATCH_MP_TAC bvi_to_cb_aux_ind THEN REPEAT STRIP_TAC THEN
  GVS[bvi_to_cb_aux_def; call_to_cb_def; option_case_eq; sum_case_eq;
      pair_case_eq; case_eq "call_block"; list_case_eq; COND_CASE_EQ;
      LET_DEF; LET_END_DEF; list_size_append] THEN
  REWRITE_TAC[list_size; type_size_def "bvi_exp"] THEN
  REWRITE_TAC(size_aux_eqs "bvi_exp") THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_imp(snd(strip_forall(concl th)))
                                 then NO_TAC else MP_TAC th)) THEN
  REWRITE_TAC[list_size; type_size_def "bvi_exp"] THEN
  REWRITE_TAC(size_aux_eqs "bvi_exp") THEN ARITH_TAC);;

let bvi_to_cb_aux_size = CONJUNCT2 bvi_to_cb_aux_size_lemma;;

let bvi_to_cb_size = prove
 (`!n loc x bs cb.
     bvi_to_cb n loc x = SOME (bs,cb) ==>
     list_size bvi_exp_size bs < bvi_exp_size x`,
  REPEAT GEN_TAC THEN CASES_ON `x:bvi_exp` THEN
  REWRITE_TAC[bvi_to_cb_def; call_to_cb_def] THEN
  GVS[option_case_eq; pair_case_eq; sum_case_eq; COND_CASE_EQ;
      BVIPAUX_TMC_dest_Cons_SOME] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  TRY(FIRST_X_ASSUM(MP_TAC o MATCH_MP bvi_to_cb_aux_size)) THEN
  REWRITE_TAC[type_size_def "bvi_exp"] THEN REWRITE_TAC(size_aux_eqs "bvi_exp") THEN
  ARITH_TAC);;

(* Phase 2 - Transformations. *)

let mut_cons_def = cake_def
  `mut_cons t l r =
     let l' = MAP (\n. bvi_Var n) l in
     let hole' = bvi_Op (IntOp (clos_Const (&0))) [] in
     let r' = MAP (\n. bvi_Var n) r in
     let i = LENGTH r in
       bvi_Op (MemOp (MutCons t i)) (APPEND (APPEND l' [hole']) r')`;;

let bvi_tmc_finalise_cons_def = cake_def
  `bvi_tmc_finalise_cons i_top_ptr =
     bvi_Op (MemOp FinaliseCons) [bvi_Var i_top_ptr]`;;

let fill_hole_def = cake_def
  `fill_hole i_ptr i_idx exp =
     bvi_Op (MemOp UpdateCons) [exp; bvi_Var i_idx; bvi_Var i_ptr]`;;

let optimise_call_def = cake_def
  `optimise_call call_ts loc_opt call_args exp_ptr exp_idx =
     let args = APPEND (MAP (\n. bvi_Var n) call_args) [exp_ptr; exp_idx] in
       bvi_Call call_ts (SOME loc_opt) args NONE`;;

let update_cons_def = cake_def
  `update_cons exp_ptr exp_idx exp_val =
     bvi_Op (MemOp UpdateCons) [exp_val; exp_idx; exp_ptr]`;;

let cb_size_def = sem1aux_def
  `(cb_size (CallBlock _ _ x _) = cb_size x + 1) /\
   (cb_size _ = 0)`;;

let call_block_size_shift = prove
 (`!x n. cb_size (shift_cb n x) = cb_size x`,
  MATCH_MP_TAC call_block_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[cb_size_def; shift_cb_def; LET_DEF; LET_END_DEF]);;

let cb_to_bvi_worker_aux_def = cake_def_wf
  `measure (\p:call_block # num # num # num. cb_size (FST p))`
  (REWRITE_TAC[measure_THM; FST; call_block_size_shift; cb_size_def] THEN
   ARITH_TAC)
  `(cb_to_bvi_worker_aux (RCall call_ts call_args) loc_opt ptr idx =
      optimise_call call_ts loc_opt call_args (bvi_Var ptr)
        (bvi_Op (IntOp (clos_Const (&idx))) [])) /\
   (cb_to_bvi_worker_aux (CallBlock tag left child right) loc_opt ptr idx =
      bvi_Let [mut_cons tag left right]
        (bvi_Let [update_cons (bvi_Var (ptr + 1))
                    (bvi_Op (IntOp (clos_Const (&idx))) []) (bvi_Var 0)]
           (cb_to_bvi_worker_aux (shift_cb 2 child) loc_opt 1 (LENGTH right))))`;;

let cb_to_bvi_worker_aux_ind = cake_ind "cb_to_bvi_worker_aux";;

let shift_cb_zero = prove
 (`!x. shift_cb 0 x = x`,
  MATCH_MP_TAC call_block_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[shift_cb_def; shift_vars_zero; LET_DEF; LET_END_DEF]);;

(* Same as cb_to_bvi_worker_aux, but with the shift carried as an           *)
(* accumulator so that the recursion is on a subterm of the call block.     *)
(* This version is the one used by the cv translation.                      *)

let cb_to_bvi_worker_aux_alt_def = cake_def
  `(cb_to_bvi_worker_aux_alt sh (RCall call_ts call_args) loc_opt ptr idx =
      optimise_call call_ts loc_opt (shift_vars sh call_args) (bvi_Var ptr)
        (bvi_Op (IntOp (clos_Const (&idx))) [])) /\
   (cb_to_bvi_worker_aux_alt sh (CallBlock tag left child right) loc_opt ptr idx =
      bvi_Let [mut_cons tag (shift_vars sh left) (shift_vars sh right)]
        (bvi_Let [update_cons (bvi_Var (ptr + 1))
                    (bvi_Op (IntOp (clos_Const (&idx))) []) (bvi_Var 0)]
           (cb_to_bvi_worker_aux_alt (sh + 2) child loc_opt 1 (LENGTH right))))`;;

let cb_to_bvi_worker_aux_alt_thm = prove
 (`!cb sh loc_opt ptr idx.
     cb_to_bvi_worker_aux_alt sh cb loc_opt ptr idx =
     cb_to_bvi_worker_aux (shift_cb sh cb) loc_opt ptr idx`,
  MATCH_MP_TAC call_block_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[cb_to_bvi_worker_aux_alt_def; cb_to_bvi_worker_aux_def;
                  shift_cb_def; LET_DEF; LET_END_DEF; length_shift_vars;
                  shift_cb_dist] THEN
  REWRITE_TAC[ADD_SYM]);;

let cb_to_bvi_worker_aux_eq = prove
 (`!cb loc_opt ptr idx.
     cb_to_bvi_worker_aux cb loc_opt ptr idx =
     cb_to_bvi_worker_aux_alt 0 cb loc_opt ptr idx`,
  REWRITE_TAC[cb_to_bvi_worker_aux_alt_thm; shift_cb_zero]);;

let cb_to_bvi_worker_def = cake_def
  `(cb_to_bvi_worker (RCall call_ts call_args) loc_opt ptr idx =
      optimise_call call_ts loc_opt call_args (bvi_Var ptr) (bvi_Var idx)) /\
   (cb_to_bvi_worker (CallBlock tag left child right) loc_opt ptr idx =
      bvi_Let [mut_cons tag left right]
        (bvi_Let [update_cons (bvi_Var (ptr + 1)) (bvi_Var (idx + 1))
                    (bvi_Var 0)]
           (cb_to_bvi_worker_aux (shift_cb 2 child) loc_opt 1 (LENGTH right))))`;;

let cb_to_bvi_wrapper_def = cake_def
  `cb_to_bvi_wrapper tag left child right loc_opt =
     bvi_Let [mut_cons tag left right]
       (bvi_Let [cb_to_bvi_worker_aux (shift_cb 1 child) loc_opt 0 (LENGTH right)]
          (bvi_tmc_finalise_cons 1))`;;

(* Expression rewriting *)

let rewrite_wrapper_def = sem1aux_def_wf
  `measure (\p:num # num # num # bvi_exp. bvi_exp_size (SND (SND (SND p))))`
  SEM1AUX_TC_TAC
  `(rewrite_wrapper loc loc_opt _ (bvi_Var n) = NONE) /\
   (rewrite_wrapper loc loc_opt n (bvi_If xi xt xe) =
      let opt_t = rewrite_wrapper loc loc_opt n xt in
      let opt_e = rewrite_wrapper loc loc_opt n xe in
        match (opt_t,opt_e) with
          (NONE,NONE) -> NONE
        | (SOME yt,NONE) -> SOME (bvi_If xi yt xe)
        | (NONE,SOME ye) -> SOME (bvi_If xi xt ye)
        | (SOME yt,SOME ye) -> SOME (bvi_If xi yt ye)) /\
   (rewrite_wrapper loc loc_opt n (bvi_Let xs x) =
      match rewrite_wrapper loc loc_opt (n + LENGTH xs) x with
        NONE -> NONE
      | SOME y -> SOME (bvi_Let xs y)) /\
   (rewrite_wrapper loc loc_opt _ (bvi_Raise x) = NONE) /\
   (rewrite_wrapper loc loc_opt n (bvi_Tick x) =
      OPTION_MAP bvi_Tick (rewrite_wrapper loc loc_opt n x)) /\
   (rewrite_wrapper loc loc_opt _ (bvi_Force _ n) = NONE) /\
   (rewrite_wrapper loc loc_opt _ (bvi_Call t d args h) = NONE) /\
   (rewrite_wrapper loc loc_opt n (bvi_Op op op_args) =
      match bvi_to_cb n loc (bvi_Op op op_args) with
        SOME (bs,CallBlock tag left child right) ->
          SOME (bvi_Let bs (cb_to_bvi_wrapper tag left child right loc_opt))
      | _ -> NONE) /\
   (rewrite_wrapper loc loc_opt _ _ = NONE)`;;

let rewrite_wrapper_ind = cake_ind "rewrite_wrapper";;

(* Assumes that the function can and should be optimised - has been        *)
(* checked by rewrite_wrapper.                                              *)

let rewrite_worker_def = sem1aux_def_wf
  `measure (\p:num # num # num # num # num # bvi_exp.
              bvi_exp_size (SND (SND (SND (SND (SND p))))))`
  SEM1AUX_TC_TAC
  `(rewrite_worker loc loc_opt i_old_ptr i_old_idx n (bvi_If xi xt xe) =
      let yt = rewrite_worker loc loc_opt i_old_ptr i_old_idx n xt in
      let ye = rewrite_worker loc loc_opt i_old_ptr i_old_idx n xe in
        bvi_If xi yt ye) /\
   (rewrite_worker loc loc_opt i_old_ptr i_old_idx n (bvi_Let xs x) =
      let offset = LENGTH xs in
        bvi_Let xs (rewrite_worker loc loc_opt (i_old_ptr + offset)
                      (i_old_idx + offset) (n + offset) x)) /\
   (rewrite_worker loc loc_opt i_old_ptr i_old_idx _ (bvi_Raise x) =
      bvi_Raise x) /\
   (rewrite_worker loc loc_opt i_old_ptr i_old_idx n (bvi_Op op op_args) =
      match bvi_to_cb n loc (bvi_Op op op_args) with
        SOME (bs,cb) ->
          (let offset = LENGTH bs in
             bvi_Let bs (cb_to_bvi_worker cb loc_opt (offset + i_old_ptr)
                           (offset + i_old_idx)))
      | NONE -> fill_hole i_old_ptr i_old_idx (bvi_Op op op_args)) /\
   (rewrite_worker loc loc_opt i_old_ptr i_old_idx n (bvi_Tick x) =
      bvi_Tick (rewrite_worker loc loc_opt i_old_ptr i_old_idx n x)) /\
   (rewrite_worker loc loc_opt i_old_ptr i_old_idx n (bvi_Call ts l args h) =
      (match bvi_to_cb n loc (bvi_Call ts l args h) with
         SOME (bs,cb) ->
           (let offset = LENGTH bs in
              bvi_Let bs (cb_to_bvi_worker cb loc_opt (offset + i_old_ptr)
                            (offset + i_old_idx)))
       | NONE -> fill_hole i_old_ptr i_old_idx (bvi_Call ts l args h))) /\
   (rewrite_worker loc loc_opt i_old_ptr i_old_idx _ expr =
      fill_hole i_old_ptr i_old_idx expr)`;;

let rewrite_worker_ind = cake_ind "rewrite_worker";;

let bvi_tmc_compile_exp_def = cake_def
  `bvi_tmc_compile_exp (loc:num) (next:num) (arity:num) (exp:bvi_exp) =
     match rewrite_wrapper loc next arity exp with
       NONE -> NONE
     | SOME exp_wrapper ->
         let exp_worker = rewrite_worker loc next arity (arity + 1) arity exp in
           SOME (exp_wrapper,exp_worker)`;;

let bvi_tmc_compile_each_def = cake_def
  `(bvi_tmc_compile_each next [] = (next,[])) /\
   (bvi_tmc_compile_each next (CONS (loc,arity,exp) xs) =
      match bvi_tmc_compile_exp loc next arity exp with
        NONE ->
          let (n,ys) = bvi_tmc_compile_each next xs in
            (n,CONS (loc,arity,exp) ys)
      | SOME (exp_wrapper,exp_worker) ->
          let (n,ys) = bvi_tmc_compile_each (next + bvl_to_bvi_namespaces) xs in
            (n,CONS (loc,arity,exp_wrapper) (CONS (next,arity + 2,exp_worker) ys)))`;;

let bvi_tmc_compile_each_ind = cake_ind "bvi_tmc_compile_each";;

let bvi_tmc_compile_prog_def = cake_def
  `bvi_tmc_compile_prog do_it next xs =
     if do_it then bvi_tmc_compile_each next xs else (next,xs)`;;
