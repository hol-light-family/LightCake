(* ========================================================================= *)
(* clos_op: port of HOL4 compiler/backend/clos_opScript.sml (CakeML v3479).  *)
(* This file implements a smart version of ClosLang's Op constructor. When  *)
(* possible, this smart constructor breaks the operation into faster        *)
(* separate operators.                                                       *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's pmatch case expressions are written with match like all others, *)
(*   so the NAME_pmatch theorems restate the definitions in match form.      *)
(* - The local overloads dest_Op_Cons = dest_Op clos_op_dest_Cons,           *)
(*   dest_Op_Cons_Nil = dest_Op_Nil clos_op_dest_Cons,                       *)
(*   dest_Op_Const = dest_Op_Nil dest_Const and                              *)
(*   dest_Op_Constant = dest_Op_Nil clos_op_dest_Constant are expanded.      *)
(* - HOL4 int / and % are int_div and integer_int_mod; ZIP (l1,l2) is        *)
(*   ZIP l1 l2; the app_list constructors are misc_List, misc_Append, Nil;   *)
(*   HOL4 exp3_size is list_size clos_exp_size.                              *)
(* - The clauses of a HOL Light definition share their variables, so a name *)
(*   used with two types gets a second name (dest_Constant: the constants c *)
(*   of HOL4 are c, i and w).                                                *)
(* - Definitions with catch-all clauses are made with sem1aux_def(_wf)       *)
(*   (semantics/sem1aux_tfl.ml).                                             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/backend_common.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* the NAME_pmatch theorems: the definition by cases (the match form is     *)
(* compiled into case constants, a case split proves it)                    *)

let IL1AUX_PMATCH_TAC (defs:thm list) : tactic =
  REPEAT GEN_TAC THEN REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC defs) THEN
  FS defs;;

(* matchers *)

let dest_Const_def = sem1aux_def
  `(dest_Const (IntOp (clos_Const i)) = SOME i) /\
   (dest_Const _ = NONE)`;;

let dest_Const_pmatch = prove
 (CASE_TERM
  `!x. dest_Const x = match x with IntOp (clos_Const i) -> SOME i | _ -> NONE`,
  IL1AUX_PMATCH_TAC[dest_Const_def]);;

(* HOL4: dest_Constant *)

let clos_op_dest_Constant_def = sem1aux_def
  `(clos_op_dest_Constant (BlockOp (Constant (ConstStr c))) = SOME (clos_Str c)) /\
   (clos_op_dest_Constant (BlockOp (Constant (ConstInt i))) = SOME (clos_Int i)) /\
   (clos_op_dest_Constant (BlockOp (Constant (ConstWord64 w))) =
      SOME (clos_W64 w)) /\
   (clos_op_dest_Constant _ = NONE)`;;

let clos_op_dest_Constant_pmatch = prove
 (CASE_TERM
  `!x. clos_op_dest_Constant x =
       match x with
         BlockOp (Constant (ConstStr c)) -> SOME (clos_Str c)
       | BlockOp (Constant (ConstInt c)) -> SOME (clos_Int c)
       | BlockOp (Constant (ConstWord64 c)) -> SOME (clos_W64 c)
       | _ -> NONE`,
  IL1AUX_PMATCH_TAC[clos_op_dest_Constant_def]);;

(* HOL4: dest_Cons *)

let clos_op_dest_Cons_def = sem1aux_def
  `(clos_op_dest_Cons (BlockOp (clos_Cons i)) = SOME i) /\
   (clos_op_dest_Cons _ = NONE)`;;

let dest_Cons_pmatch = prove
 (CASE_TERM
  `!x. clos_op_dest_Cons x =
       match x with BlockOp (clos_Cons i) -> SOME i | _ -> NONE`,
  IL1AUX_PMATCH_TAC[clos_op_dest_Cons_def]);;

let dest_ElemAt_def = sem1aux_def
  `(dest_ElemAt (BlockOp (ElemAt i)) = SOME i) /\
   (dest_ElemAt _ = NONE)`;;

let dest_ElemAt_pmatch = prove
 (CASE_TERM
  `!x. dest_ElemAt x = match x with BlockOp (ElemAt i) -> SOME i | _ -> NONE`,
  IL1AUX_PMATCH_TAC[dest_ElemAt_def]);;

let dest_TagEq_def = sem1aux_def
  `(dest_TagEq (BlockOp (TagEq i)) = SOME i) /\
   (dest_TagEq _ = NONE)`;;

let dest_TagEq_pmatch = prove
 (CASE_TERM
  `!x. dest_TagEq x = match x with BlockOp (TagEq i) -> SOME i | _ -> NONE`,
  IL1AUX_PMATCH_TAC[dest_TagEq_def]);;

let dest_LenEq_def = sem1aux_def
  `(dest_LenEq (BlockOp (clos_LenEq i)) = SOME i) /\
   (dest_LenEq _ = NONE)`;;

let dest_LenEq_pmatch = prove
 (CASE_TERM
  `!x. dest_LenEq x = match x with BlockOp (clos_LenEq i) -> SOME i | _ -> NONE`,
  IL1AUX_PMATCH_TAC[dest_LenEq_def]);;

let dest_TagLenEq_def = sem1aux_def
  `(dest_TagLenEq (BlockOp (clos_TagLenEq i j)) = SOME (i,j)) /\
   (dest_TagLenEq _ = NONE)`;;

let dest_TagLenEq_pmatch = prove
 (CASE_TERM
  `!x. dest_TagLenEq x =
       match x with BlockOp (clos_TagLenEq i j) -> SOME (i,j) | _ -> NONE`,
  IL1AUX_PMATCH_TAC[dest_TagLenEq_def]);;

let dest_Op_def = sem1aux_def
  `(dest_Op (f:clos_op->A option) (clos_Op t op xs) =
      match f op with
        NONE -> NONE
      | SOME i -> SOME (i,xs)) /\
   (dest_Op f _ = NONE)`;;

let dest_Op_pmatch = prove
 (CASE_TERM
  `!(f:clos_op->A option) x.
     dest_Op f x =
       match x with
         clos_Op t op xs -> (match f op with NONE -> NONE | SOME i -> SOME (i,xs))
       | _ -> NONE`,
  IL1AUX_PMATCH_TAC[dest_Op_def]);;

let dest_Op_Nil_def = cake_def
  `dest_Op_Nil (f:clos_op->A option) x =
     match dest_Op f x with
       NONE -> NONE
     | SOME (i,xs) -> if NULL xs then SOME i else NONE`;;

let dest_Op_Consts_def = cake_def
  `dest_Op_Consts x y =
     match dest_Op_Nil dest_Const x with
       NONE -> NONE
     | SOME i ->
         (match dest_Op_Nil dest_Const y with
            NONE -> NONE
          | SOME j -> SOME (i,j))`;;

let MakeBool_def = cake_def
  `MakeBool b =
     clos_Op backend_common_None (BlockOp (clos_Cons (if b then 1 else 0))) []`;;

let MakeInt_def = cake_def
  `MakeInt i = clos_Op backend_common_None (IntOp (clos_Const i)) []`;;

(* HOL4: int_op *)

let clos_op_int_op_def = cake_def
  `clos_op_int_op op (i:int) j =
     if op = IntOp clos_Add then SOME (MakeInt (j + i)) else
     if op = IntOp clos_Sub then SOME (MakeInt (j - i)) else
     if op = IntOp Mult then SOME (MakeInt (j * i)) else
     if op = IntOp clos_Div
     then SOME (MakeInt (if i = &0 then &0 else int_div j i)) else
     if op = IntOp clos_Mod
     then SOME (MakeInt (if i = &0 then &0 else integer_int_mod j i)) else
     if op = IntOp clos_Less then SOME (MakeBool (j < i)) else
     if op = IntOp LessEq then SOME (MakeBool (j <= i)) else
     if op = IntOp Greater then SOME (MakeBool (i < j)) else
     if op = IntOp GreaterEq then SOME (MakeBool (i <= j)) else
     if op = BlockOp clos_Equal then SOME (MakeBool (j = i)) else NONE`;;

let cons_op_def = cake_def
  `cons_op op t xs =
     match dest_ElemAt op with
       SOME n ->
         (if n < LENGTH xs then
            SOME (clos_Let backend_common_None xs
                    (clos_Var backend_common_None (LENGTH xs - (n + 1))))
          else NONE)
     | NONE ->
     (match dest_TagLenEq op with
        SOME (n,l) ->
          SOME (clos_Let backend_common_None xs
                  (MakeBool (n = t /\ LENGTH xs = l)))
      | NONE ->
      (match dest_TagEq op with
         SOME n -> SOME (clos_Let backend_common_None xs (MakeBool (n = t)))
       | NONE ->
       (match dest_LenEq op with
          SOME l ->
            SOME (clos_Let backend_common_None xs (MakeBool (LENGTH xs = l)))
        | NONE -> NONE)))`;;

let is_Var_def = sem1aux_def
  `(is_Var (clos_Var _ _) <=> T) /\
   (is_Var _ <=> F)`;;

let is_Var_pmatch = prove
 (CASE_TERM
  `!x. is_Var x <=> match x with clos_Var _ _ -> T | _ -> F`,
  IL1AUX_PMATCH_TAC[is_Var_def]);;

let eq_direct_nil_def = cake_def
  `eq_direct_nil x y =
     match dest_Op_Nil clos_op_dest_Cons x with
       SOME i ->
         (match dest_Op_Nil clos_op_dest_Cons y with
            SOME j -> SOME (MakeBool (i = j))
          | NONE ->
              SOME (clos_Op backend_common_None (BlockOp (clos_TagLenEq i 0)) [y]))
     | NONE ->
         (match dest_Op_Nil clos_op_dest_Cons y with
            SOME i ->
              SOME (clos_Op backend_common_None (BlockOp (clos_TagLenEq i 0)) [x])
          | NONE -> NONE)`;;

let eq_direct_const_def = cake_def
  `eq_direct_const x y =
     match dest_Op_Nil dest_Const x with
       SOME i ->
         (match dest_Op_Nil dest_Const y with
            SOME j -> SOME (MakeBool (i = j))
          | NONE ->
              SOME (clos_Op backend_common_None
                      (BlockOp (EqualConst (clos_Int i))) [y]))
     | NONE ->
         (match dest_Op_Nil dest_Const y with
            SOME i ->
              SOME (clos_Op backend_common_None
                      (BlockOp (EqualConst (clos_Int i))) [x])
          | NONE -> NONE)`;;

let eq_direct_constant_def = cake_def
  `eq_direct_constant x y =
     match dest_Op_Nil clos_op_dest_Constant x with
       SOME p ->
         (match dest_Op_Nil clos_op_dest_Constant y with
            SOME q -> SOME (MakeBool (q = p))
          | NONE ->
              SOME (clos_Op backend_common_None (BlockOp (EqualConst p)) [y]))
     | NONE ->
         (match dest_Op_Nil clos_op_dest_Constant y with
            SOME p ->
              SOME (clos_Op backend_common_None (BlockOp (EqualConst p)) [x])
          | NONE -> NONE)`;;

let eq_direct_def = cake_def
  `eq_direct x y =
     match eq_direct_const x y with
       SOME res -> SOME res
     | NONE ->
         (match eq_direct_constant x y with
            SOME res -> SOME res
          | NONE -> eq_direct_nil x y)`;;

(* the arguments of an expression that dest_Op takes apart *)

let IL1AUX_dest_Op_SOME = prove
 (`!(f:clos_op->A option) x i xs.
     dest_Op f x = SOME (i,xs) ==> ?t op. x = clos_Op t op xs`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `x:clos_exp` THEN
  REWRITE_TAC[dest_Op_def; distinctness "option"] THEN
  REPEAT GEN_TAC THEN TOP_CASE_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN
  MESON_TAC[]);;

let cons_measure_def = cake_def_wf
  `MEASURE clos_exp_size`
  (REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IL1AUX_dest_Op_SOME) THEN
   RVEQ_TAC THEN TERM_TAC)
  `cons_measure x =
     match dest_Op clos_op_dest_Cons x with
       NONE -> 0
     | SOME (_,xs) -> SUM (MAP cons_measure xs) + LENGTH xs + 1`;;

let cons_measure_ind = cake_ind "cons_measure";;

let cons_measure_lemma = prove
 (`(!x t xs. dest_Op clos_op_dest_Cons x = SOME (t,xs)
             ==> cons_measure x = SUM (MAP cons_measure xs) + LENGTH xs + 1) /\
   (!x. dest_Op clos_op_dest_Cons x = NONE ==> cons_measure x = 0) /\
   (!i y. cons_measure (clos_Op backend_common_None (BlockOp (ElemAt i)) [y]) =
          0)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [cons_measure_def] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP[dest_Op_def; clos_op_dest_Cons_def]);;

(* termination of eq_pure_list (HOL4's relation and proof steps): the sum  *)
(* over a ZIP of two lists, the sum over MAPi with ElemAt                   *)

let IL1AUX_EPL_ZIP = prove
 (`!l1 l2. LENGTH l1 = LENGTH l2 ==>
     SUM (MAP (\p. 1 + cons_measure (FST p) + cons_measure (SND p) +
                   (if cons_measure (FST p) < cons_measure (SND p) then 1 else 0))
              (ZIP l1 l2)) <=
     2 * LENGTH l1 + SUM (MAP cons_measure l1) + SUM (MAP cons_measure l2)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; ZIP; MAP; SUM; NOT_SUC; SUC_INJ; LE_REFL; MULT_CLAUSES;
              ADD_CLAUSES] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `t':clos_exp list`) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ARITH_TAC);;

let IL1AUX_EPL_MAPi = prove
 (`!l (f:num->clos_exp->clos_exp#clos_exp).
     (!i x. FST (f i x) = x /\ cons_measure (SND (f i x)) = 0) ==>
     SUM (MAP (\p. 1 + cons_measure (FST p) + cons_measure (SND p) +
                   (if cons_measure (FST p) < cons_measure (SND p) then 1 else 0))
              (MAPi f l)) =
     LENGTH l + SUM (MAP cons_measure l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAPi_DEF; MAP; SUM; LENGTH; ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LT] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(f:num->clos_exp->clos_exp#clos_exp) o SUC`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ARITH_TAC);;

let IL1AUX_EPL_TC_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[DE_MORGAN_THM; NOT_CLAUSES] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  IMP_RES_TAC (CONJUNCT1 cons_measure_lemma) THEN
  IMP_RES_TAC (CONJUNCT1 (CONJUNCT2 cons_measure_lemma)) THEN
  REWRITE_TAC WF_REL_THMS THEN REWRITE_TAC[MAP; SUM; ADD_CLAUSES] THEN
  FIRST
   [(* the completed clause: the head and the tail of a longer list *)
    ARITH_TAC;
    (* [(y,x)] for [(x,y)] *)
    ASM_REWRITE_TAC[LT] THEN ARITH_TAC;
    (* the elements of x against ElemAt i of y *)
    MP_TAC (ISPECL [`REVERSE xs:clos_exp list`;
                    `\i (x:clos_exp). x,clos_Op backend_common_None
                                         (BlockOp (ElemAt i)) [y]`]
                   IL1AUX_EPL_MAPi) THEN
    REWRITE_TAC[cons_measure_lemma] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[LENGTH_REVERSE; rich_list_MAP_REVERSE; SUM_REVERSE;
                    LT] THEN
    ARITH_TAC;
    (* the elements of x against those of y *)
    MP_TAC (ISPECL [`REVERSE xs:clos_exp list`; `REVERSE ys:clos_exp list`]
                   IL1AUX_EPL_ZIP) THEN
    ASM_REWRITE_TAC[LENGTH_REVERSE; rich_list_MAP_REVERSE; SUM_REVERSE] THEN
    COND_CASES_TAC THEN ARITH_TAC];;

let eq_pure_list_def = cake_def_wf
  `MEASURE (\l:(clos_exp # clos_exp) list.
     SUM (MAP (\p. 1 + cons_measure (FST p) + cons_measure (SND p) +
                   (if cons_measure (FST p) < cons_measure (SND p) then 1 else 0))
              l))`
  IL1AUX_EPL_TC_TAC
  `(eq_pure_list [] = Nil) /\
   (eq_pure_list [(x,y)] =
      match eq_direct x y with
        SOME z -> misc_List [z]
      | NONE ->
        (match (dest_Op clos_op_dest_Cons x, dest_Op clos_op_dest_Cons y) with
           (NONE, NONE) ->
             misc_List [clos_Op backend_common_None (BlockOp clos_Equal) [x; y]]
         | (SOME (t1,xs), SOME (t2,ys)) ->
             if ~(t1 = t2) \/ ~(LENGTH xs = LENGTH ys)
             then misc_List [MakeBool F]
             else eq_pure_list (ZIP (REVERSE xs) (REVERSE ys))
         | (SOME (t1,xs), NONE) ->
             misc_Append
               (misc_List [clos_Op backend_common_None
                             (BlockOp (clos_TagLenEq t1 (LENGTH xs))) [y]])
               (eq_pure_list
                  (MAPi (\i x. (x, clos_Op backend_common_None
                                     (BlockOp (ElemAt i)) [y]))
                        (REVERSE xs)))
         | (NONE, SOME (t1,ys)) -> eq_pure_list [(y,x)])) /\
   (eq_pure_list (CONS xy xys) =
      misc_Append (eq_pure_list [xy]) (eq_pure_list xys))`;;

let eq_pure_list_ind = cake_ind "eq_pure_list";;

let ConjList_def = cake_def
  `(ConjList [] = MakeBool T) /\
   (ConjList [x] = x) /\
   (ConjList (CONS x xs) =
      clos_If backend_common_None x (ConjList xs) (MakeBool F))`;;

let ConjList_ind = cake_ind "ConjList";;

let eq_pure_def = cake_def
  `eq_pure x y = ConjList (append (eq_pure_list [(x,y)]))`;;

(* HOL4: eq_pure_list_test[local], an EVAL test, is not ported *)

let dont_lift_def = cake_def
  `dont_lift x <=>
     match dest_Op_Nil dest_Const x with
       SOME i -> T
     | NONE ->
       (match dest_Op_Nil clos_op_dest_Cons x with
          SOME t -> T
        | NONE ->
          (match dest_Op_Nil clos_op_dest_Constant x with
             SOME t -> T
           | NONE -> F))`;;

let lift_exps_def = cake_def_wf
  `MEASURE (\p:clos_exp list # num # clos_exp list.
              list_size clos_exp_size (FST p))`
  (REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   TRY (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IL1AUX_dest_Op_SOME)) THEN
   RVEQ_TAC THEN TERM_TAC)
  `(lift_exps [] n binds = ([],n,binds)) /\
   (lift_exps (CONS x xs) n binds =
      if dont_lift x then
        (let (xs,n,binds) = lift_exps xs n binds in
           (CONS x xs,n,binds))
      else
        match dest_Op clos_op_dest_Cons x with
          SOME (t,ys) ->
            (let (ys,n,binds) = lift_exps ys n binds in
             let (xs,n,binds) = lift_exps xs n binds in
               (CONS (clos_Op backend_common_None (BlockOp (clos_Cons t)) ys) xs,
                n,binds))
        | NONE ->
            (let (xs,n1,binds) = lift_exps xs (n + 1) (APPEND binds [x]) in
               (CONS (clos_Var backend_common_None n) xs,n1,binds)))`;;

let lift_exps_ind = cake_ind "lift_exps";;

let eq_any_def = cake_def
  `eq_any x y =
     match lift_exps [x; y] 0 [] with
       (CONS x (CONS y _), _, binds) ->
         SOME (clos_Let backend_common_None binds (eq_pure x y))
     | _ -> NONE`;;

let eq_op_def = cake_def
  `eq_op x y =
     if is_Var x /\ is_Var y then NONE else
     match eq_direct x y with
       NONE -> eq_any x y
     | SOME res -> SOME res`;;

(* top-level implementations *)

let SmartOp'_def = cake_def
  `SmartOp' (tra:A) op xs =
     match xs with
       [x] ->
         (match dest_Op clos_op_dest_Cons x with
            SOME (t,xs) -> cons_op op t xs
          | NONE -> NONE)
     | [x; y] ->
         (match dest_Op_Consts x y with
            SOME (i,j) -> clos_op_int_op op i j
          | NONE -> if op = BlockOp clos_Equal then eq_op x y else NONE)
     | _ -> NONE`;;

(* HOL4: SmartOp *)

let clos_op_SmartOp_def = cake_def
  `clos_op_SmartOp tra op xs =
     match SmartOp' tra op xs with
       NONE -> clos_Op tra op xs
     | SOME x -> x`;;
