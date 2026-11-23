(* ========================================================================= *)
(* bvl_const: port of HOL4 compiler/backend/bvl_constScript.sml (CakeML      *)
(* v3479).  A BVL transformation that propagates simple and cheap-to-compute *)
(* context-free expressions from Let bindings; it also performs some simple  *)
(* constant folding with SmartOp (below).                                   *)
(*                                                                           *)
(* The most significant impact of this optimisation is that it removes each *)
(* Var in a Let, i.e. Let [...; Var ...; ...] ..., and replaces them with   *)
(* constants Let [...; Op (IntOp (Const _)) []; ...] ... and replaces all   *)
(* occurrences of the bound var with a lookup to the original variable.     *)
(* bvi_let is a simpler version of this optimisation.                        *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/bvl.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* HOL4 makes an induction theorem (a case analysis) for some of the        *)
(* non-recursive definitions by patterns below: one case per clause of the  *)
(* completed definition (as IL2AUX_case_ind of wordLang.ml)                 *)

let BVLPAUX_case_ind (def:thm) : thm =
  let cls = map (fun cl -> let vs,eq = strip_forall cl in
                           let c,args = strip_comb(lhs eq) in vs,c,args)
                (conjuncts(concl def)) in
  let _,c,args0 = hd cls in
  let tty = mk_tuple_ty (map type_of args0) in
  let wfth = ISPEC (mk_abs(mk_var("x",tty),`0`)) WF_MEASURE in
  derive_induction c (map (fun (vs,_,args) -> vs,args) cls) [] wfth;;

(* HOL4 pmatch case expressions are written as match, like case expressions *)
(* (both compile to the case constants), so the _pmatch theorems below     *)
(* state the definitions with the patterns of the HOL4 pmatch statements   *)

let dest_simple_def = sem1aux_def
  `(dest_simple (bvl_Op (IntOp (clos_Const i)) xs) =
      if NULL xs then SOME i else NONE) /\
   (dest_simple _ = NONE:int option)`;;

let dest_simple_ind = BVLPAUX_case_ind dest_simple_def;;

let _ = cake_add_simps [dest_simple_def];;

let dest_simple_pmatch = prove
 (CASE_TERM
  `!op. dest_simple op =
        match op with bvl_Op (IntOp (clos_Const i)) [] -> SOME i | _ -> NONE`,
  MATCH_MP_TAC dest_simple_ind THEN SIMP[] THEN
  REPEAT GEN_TAC THEN CASES_ON `xs:bvl_exp list` THEN SIMP[NULL]);;

let case_op_const_def = cake_def
  `case_op_const (exp:bvl_exp) =
     match exp with
       bvl_Op op [x1; bvl_Op (IntOp (clos_Const n2)) l] ->
         if NULL l then SOME (op,x1,n2) else NONE
     | _ -> NONE`;;

let case_op_const_pmatch = prove
 (CASE_TERM
  `!exp. case_op_const exp =
         match exp with
           bvl_Op op [x1; bvl_Op (IntOp (clos_Const n2)) []] -> SOME (op,x1,n2)
         | _ -> NONE`,
  GEN_TAC THEN REWRITE_TAC[case_op_const_def] THEN EVERY_CASE_TAC THEN
  FS[NULL]);;

let SmartOp_flip_def = cake_def
  `SmartOp_flip op (x1:bvl_exp) (x2:bvl_exp) =
     match dest_simple x1 with
       SOME i ->
         if MEM op [IntOp clos_Add; IntOp Mult] then (op,x2,x1)
         else if op = IntOp clos_Sub
         then (IntOp clos_Add,x2,bvl_Op (IntOp (clos_Const (--i))) [])
         else (op,x1,x2)
     | _ -> (op,x1,x2)`;;

let SmartOp_flip_pmatch = prove
 (CASE_TERM
  `!op x1 x2. SmartOp_flip op x1 x2 =
     match dest_simple x1 with
       SOME i ->
         if MEM op [IntOp clos_Add; IntOp Mult] then (op,x2,x1)
         else if op = IntOp clos_Sub
         then (IntOp clos_Add,x2,bvl_Op (IntOp (clos_Const (--i))) [])
         else (op,x1,x2)
     | _ -> (op,x1,x2)`,
  REWRITE_TAC[SmartOp_flip_def]);;

(* HOL4 defines SmartOp2 from a quotation and states SmartOp2_pmatch with   *)
(* the same quotation (case replaced by pmatch); the port does the same     *)
(* with the term BVLPAUX_SmartOp2_tm (the local functions of HOL4's         *)
(* let f x y = .. in are written let f = \x y. .. in)                       *)

let BVLPAUX_SmartOp2_tm =
 `SmartOp2 (op,x1:bvl_exp,x2:bvl_exp) =
    let mk_add_const = \x1 c2.
      (if c2 = (&0:int) then x1
       else bvl_Op (IntOp clos_Add) [x1; bvl_Op (IntOp (clos_Const c2)) []]) in
    let mk_add = \x1 x2.
      (let default = bvl_Op (IntOp clos_Add) [x1; x2] in
       match dest_simple x2 with
         SOME n2 ->
           (match case_op_const x1 with
              SOME (op,x11,n12) ->
                if op = IntOp clos_Add then mk_add_const x11 (n2 + n12)
                else if op = IntOp clos_Sub then
                  bvl_Op (IntOp clos_Sub)
                    [x11; bvl_Op (IntOp (clos_Const (n2 + n12))) []]
                else default
            | _ ->
                (match dest_simple x1 with
                   SOME n1 -> bvl_Op (IntOp (clos_Const (n2 + n1))) []
                 | _ -> mk_add_const x1 n2))
       | _ ->
           (match (case_op_const x1,case_op_const x2) with
              (SOME (op1,x11,n12),SOME (op2,x21,n22)) ->
                if op1 = IntOp clos_Add /\ op2 = IntOp clos_Add then
                  mk_add_const (bvl_Op (IntOp clos_Add) [x11; x21]) (n22 + n12)
                else if op1 = IntOp clos_Add /\ op2 = IntOp clos_Sub then
                  bvl_Op (IntOp clos_Sub)
                    [bvl_Op (IntOp clos_Sub) [x11; x21];
                     bvl_Op (IntOp (clos_Const (n22 + n12))) []]
                else if op1 = IntOp clos_Sub /\ op2 = IntOp clos_Add then
                  mk_add_const (bvl_Op (IntOp clos_Sub) [x11; x21]) (n22 + n12)
                else default
            | _ -> default)) in
    let mk_sub = \x1 x2.
      (let default = bvl_Op (IntOp clos_Sub) [x1; x2] in
       match dest_simple x2 with
         SOME n2 ->
           (match case_op_const x1 with
              SOME (op,x11,n12) ->
                if op = IntOp clos_Add then
                  bvl_Op (IntOp clos_Sub)
                    [x11; bvl_Op (IntOp (clos_Const (n2 - n12))) []]
                else if op = IntOp clos_Sub then mk_add_const x11 (n2 - n12)
                else default
            | _ ->
                (match dest_simple x1 with
                   SOME n1 -> bvl_Op (IntOp (clos_Const (n2 - n1))) []
                 | _ -> default))
       | _ ->
           (match (case_op_const x1,case_op_const x2) with
              (SOME (op1,x11,n12),SOME (op2,x21,n22)) ->
                if op1 = IntOp clos_Add /\ op2 = IntOp clos_Add then
                  bvl_Op (IntOp clos_Add)
                    [bvl_Op (IntOp clos_Sub) [x11; x21];
                     bvl_Op (IntOp (clos_Const (n22 - n12))) []]
                else if op1 = IntOp clos_Add /\ op2 = IntOp clos_Sub then
                  bvl_Op (IntOp clos_Sub)
                    [bvl_Op (IntOp clos_Add) [x11; x21];
                     bvl_Op (IntOp (clos_Const (n22 - n12))) []]
                else if op1 = IntOp clos_Sub /\ op2 = IntOp clos_Add then
                  mk_add_const (bvl_Op (IntOp clos_Add) [x11; x21]) (n22 - n12)
                else default
            | _ -> default)) in
    let mk_mul = \x1 x2.
      (let default = bvl_Op (IntOp Mult) [x1; x2] in
       match dest_simple x2 with
         SOME n2 ->
           (match case_op_const x1 with
              SOME (op,x11,n12) ->
                if op = IntOp Mult then
                  bvl_Op (IntOp Mult)
                    [x11; bvl_Op (IntOp (clos_Const (n2 * n12))) []]
                else default
            | _ ->
                (match dest_simple x1 with
                   SOME n1 -> bvl_Op (IntOp (clos_Const (n2 * n1))) []
                 | _ ->
                     if n2 = &1 then x1
                     else if n2 = -- &1
                     then mk_sub x1 (bvl_Op (IntOp (clos_Const (&0))) [])
                     else default))
       | _ ->
           (match (case_op_const x1,case_op_const x2) with
              (SOME (op1,x11,n12),SOME (op2,x21,n22)) ->
                if op1 = IntOp Mult /\ op2 = IntOp Mult then
                  bvl_Op (IntOp Mult)
                    [bvl_Op (IntOp (clos_Const (n22 * n12))) [];
                     bvl_Op (IntOp Mult) [x11; x21]]
                else default
            | _ -> default)) in
    let default = bvl_Op op [x1; x2] in
    if op = IntOp clos_Add then mk_add x1 x2
    else if op = IntOp clos_Sub then mk_sub x1 x2
    else if op = IntOp Mult then mk_mul x1 x2
    else if MEM op [IntOp clos_Div; IntOp clos_Mod; IntOp clos_Less;
                    IntOp LessEq; IntOp Greater; IntOp GreaterEq] then
      (match (dest_simple x1,dest_simple x2) with
         (SOME x1,SOME (x2:int)) ->
           (match op with
              IntOp clos_Div ->
                if x1 = &0 then default
                else bvl_Op (IntOp (clos_Const (int_div x2 x1))) []
            | IntOp clos_Mod ->
                if x1 = &0 then default
                else bvl_Op (IntOp (clos_Const (integer_int_mod x2 x1))) []
            | IntOp clos_Less -> bvl_Bool (x2 < x1)
            | IntOp LessEq -> bvl_Bool (x2 <= x1)
            | IntOp Greater -> bvl_Bool (x2 > x1)
            | IntOp GreaterEq -> bvl_Bool (x2 >= x1)
            | _ -> default)
       | _ -> default)
    else if op = BlockOp clos_Equal then
      (match (dest_simple x1,dest_simple x2) with
         (SOME i,SOME j) -> bvl_Bool (j = i)
       | (SOME i,_) -> bvl_Op (BlockOp (EqualConst (clos_Int i))) [x2]
       | (_,SOME i) -> bvl_Op (BlockOp (EqualConst (clos_Int i))) [x1]
       | _ -> default)
    else if op = MemOp clos_El then
      (match dest_simple x1 with
         SOME i ->
           if i < &0 then default
           else bvl_Op (BlockOp (ElemAt (num_of_int i))) [x2]
       | _ -> default)
    else default`;;

let SmartOp2_def = cake_def BVLPAUX_SmartOp2_tm;;

(* the quotation was parsed before SmartOp2 was defined: its SmartOp2 is a  *)
(* variable, replaced by the constant                                       *)

let SmartOp2_pmatch = prove
 (let tm = CASE_TERM BVLPAUX_SmartOp2_tm in
  vsubst [`SmartOp2`,repeat rator (lhs tm)] tm,
  REWRITE_TAC[SmartOp2_def]);;

let dest_EqualInt_def = sem1aux_def
  `(dest_EqualInt (BlockOp (EqualConst (clos_Int i))) = SOME i) /\
   (dest_EqualInt _ = NONE:int option)`;;

let dest_EqualInt_pmatch = prove
 (CASE_TERM
  `dest_EqualInt x =
     match x with BlockOp (EqualConst (clos_Int i)) -> SOME i | _ -> NONE`,
  SPEC_TAC(`x:clos_op`,`x:clos_op`) THEN
  MATCH_MP_TAC (BVLPAUX_case_ind dest_EqualInt_def) THEN
  REWRITE_TAC[dest_EqualInt_def] THEN CASE_REWRITE_TAC[]);;

let SmartOp1_def = cake_def
  `SmartOp1 op (x:bvl_exp) =
     match dest_EqualInt op with
       NONE -> bvl_Op op [x]
     | SOME i ->
         (match dest_simple x with
            NONE -> bvl_Op op [x]
          | SOME j -> bvl_Bool (j = i))`;;

let bvl_const_SmartOp_def = cake_def
  `bvl_const_SmartOp op (xs:bvl_exp list) =
     match xs with
       [x1; x2] -> SmartOp2 (SmartOp_flip op x1 x2)
     | [x] -> SmartOp1 op x
     | _ -> bvl_Op op xs`;;

let SmartOp_pmatch = prove
 (CASE_TERM
  `!op xs. bvl_const_SmartOp op xs =
     match xs with
       [x1; x2] -> SmartOp2 (SmartOp_flip op x1 x2)
     | [x] -> SmartOp1 op x
     | _ -> bvl_Op op xs`,
  REWRITE_TAC[bvl_const_SmartOp_def]);;

(* HOL4 infers ys : 'a list for extract (it is used with bvl_exp list)      *)

let bvl_const_extract_def = sem1aux_def
  `(bvl_const_extract (bvl_Var n) (ys:A list) =
      SOME (bvl_Var (n + LENGTH ys + 1))) /\
   (bvl_const_extract (bvl_Op (IntOp (clos_Const i)) xs) ys =
      SOME (bvl_Op (IntOp (clos_Const i)) [])) /\
   (bvl_const_extract (bvl_Op (BlockOp (clos_Cons t)) xs) ys =
      if NULL xs then SOME (bvl_Op (BlockOp (clos_Cons t)) []) else NONE) /\
   (bvl_const_extract _ _ = NONE)`;;

let extract_pmatch = prove
 (CASE_TERM
  `!op (ys:A list). bvl_const_extract op ys =
     match op with
       bvl_Var n -> SOME (bvl_Var (n + LENGTH ys + 1))
     | bvl_Op (IntOp (clos_Const i)) xs ->
         SOME (bvl_Op (IntOp (clos_Const i)) [])
     | bvl_Op (BlockOp (clos_Cons t)) [] ->
         SOME (bvl_Op (BlockOp (clos_Cons t)) [])
     | _ -> NONE`,
  MATCH_MP_TAC (BVLPAUX_case_ind bvl_const_extract_def) THEN
  REWRITE_TAC[bvl_const_extract_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN CASES_ON `xs:bvl_exp list` THEN
  REWRITE_TAC[NULL] THEN CASE_REWRITE_TAC[]);;

let bvl_const_extract_list_def = cake_def
  `(bvl_const_extract_list [] = []) /\
   (bvl_const_extract_list (CONS x xs) =
      CONS (bvl_const_extract x xs) (bvl_const_extract_list xs))`;;

let bvl_const_delete_var_def = sem1aux_def
  `(bvl_const_delete_var (bvl_Var n) = bvl_Op (IntOp (clos_Const (&0))) []) /\
   (bvl_const_delete_var x = x)`;;

let bvl_const_delete_var_ind = BVLPAUX_case_ind bvl_const_delete_var_def;;

let delete_var_pmatch = prove
 (CASE_TERM
  `!op. bvl_const_delete_var op =
     match op with
       bvl_Var n -> bvl_Op (IntOp (clos_Const (&0))) []
     | x -> x`,
  MATCH_MP_TAC bvl_const_delete_var_ind THEN
  REWRITE_TAC[bvl_const_delete_var_def] THEN CASE_REWRITE_TAC[]);;

(* HOL4 LLOOKUP env v is oEL v env (misc); HOL4 proves termination of      *)
(* compile automatically, with the size of the expression list             *)

let bvl_const_compile_def = sem1aux_def_wf
  `MEASURE (\p:(bvl_exp option) list # bvl_exp list.
              list_size bvl_exp_size (SND p))`
  SEM1AUX_TC_TAC
  `(bvl_const_compile (env:(bvl_exp option) list) [] = []) /\
   (bvl_const_compile env (CONS x (CONS y xs)) =
      APPEND (bvl_const_compile env [x]) (bvl_const_compile env (CONS y xs))) /\
   (bvl_const_compile env [bvl_Var v] =
      match oEL v env with
        NONE -> [bvl_Var v]
      | SOME NONE -> [bvl_Var v]
      | SOME (SOME (bvl_Var i)) -> [bvl_Var (v + i)]
      | SOME (SOME x) -> [x]) /\
   (bvl_const_compile env [bvl_If x1 x2 x3] =
      let y1 = HD (bvl_const_compile env [x1]) in
      let y2 = HD (bvl_const_compile env [x2]) in
      let y3 = HD (bvl_const_compile env [x3]) in
        if y1 = bvl_Bool T then [y2] else
        if y1 = bvl_Bool F then [y3] else
          [bvl_If y1 y2 y3]) /\
   (bvl_const_compile env [bvl_Let xs x2] =
      let ys = bvl_const_compile env xs in
        [bvl_Let (MAP bvl_const_delete_var ys)
           (HD (bvl_const_compile (APPEND (bvl_const_extract_list ys) env)
                  [x2]))]) /\
   (bvl_const_compile env [bvl_Handle x1 x2] =
      [bvl_Handle (HD (bvl_const_compile env [x1]))
                  (HD (bvl_const_compile (CONS NONE env) [x2]))]) /\
   (bvl_const_compile env [bvl_Raise x1] =
      [bvl_Raise (HD (bvl_const_compile env [x1]))]) /\
   (bvl_const_compile env [bvl_Op op xs] =
      [bvl_const_SmartOp op (bvl_const_compile env xs)]) /\
   (bvl_const_compile env [bvl_Tick x] =
      [bvl_Tick (HD (bvl_const_compile env [x]))]) /\
   (bvl_const_compile env [bvl_Force loc v] =
      match oEL v env with
        NONE -> [bvl_Force loc v]
      | SOME NONE -> [bvl_Force loc v]
      | SOME (SOME (bvl_Var i)) -> [bvl_Force loc (v + i)]
      | SOME (SOME x) -> [bvl_Force loc v]) /\
   (bvl_const_compile env [bvl_Call t dest xs] =
      [bvl_Call t dest (bvl_const_compile env xs)])`;;

let bvl_const_compile_ind = cake_ind "bvl_const_compile";;

let bvl_const_compile_sing_def = sem1aux_def_wf
  `MEASURE (\x:(bvl_exp option) list # bvl_exp +
               (bvl_exp option) list # bvl_exp list.
              sum_CASE x (\p. bvl_exp_size (SND p))
                         (\p. list_size bvl_exp_size (SND p)))`
  SEM1AUX_TC_TAC
  `(bvl_const_compile_sing (env:(bvl_exp option) list) (bvl_Var v) =
      match oEL v env with
        NONE -> bvl_Var v
      | SOME NONE -> bvl_Var v
      | SOME (SOME (bvl_Var i)) -> bvl_Var (v + i)
      | SOME (SOME x) -> x) /\
   (bvl_const_compile_sing env (bvl_If x1 x2 x3) =
      let y1 = bvl_const_compile_sing env x1 in
      let y2 = bvl_const_compile_sing env x2 in
      let y3 = bvl_const_compile_sing env x3 in
        if y1 = bvl_Bool T then y2 else
        if y1 = bvl_Bool F then y3 else
          bvl_If y1 y2 y3) /\
   (bvl_const_compile_sing env (bvl_Let xs x2) =
      let ys = bvl_const_compile_list env xs in
        bvl_Let (MAP bvl_const_delete_var ys)
          (bvl_const_compile_sing (APPEND (bvl_const_extract_list ys) env) x2)) /\
   (bvl_const_compile_sing env (bvl_Handle x1 x2) =
      bvl_Handle (bvl_const_compile_sing env x1)
                 (bvl_const_compile_sing (CONS NONE env) x2)) /\
   (bvl_const_compile_sing env (bvl_Raise x1) =
      bvl_Raise (bvl_const_compile_sing env x1)) /\
   (bvl_const_compile_sing env (bvl_Op op xs) =
      bvl_const_SmartOp op (bvl_const_compile_list env xs)) /\
   (bvl_const_compile_sing env (bvl_Tick x) =
      bvl_Tick (bvl_const_compile_sing env x)) /\
   (bvl_const_compile_sing env (bvl_Force loc v) =
      match oEL v env with
        NONE -> bvl_Force loc v
      | SOME NONE -> bvl_Force loc v
      | SOME (SOME (bvl_Var i)) -> bvl_Force loc (v + i)
      | SOME (SOME x) -> bvl_Force loc v) /\
   (bvl_const_compile_sing env (bvl_Call t dest xs) =
      bvl_Call t dest (bvl_const_compile_list env xs)) /\
   (bvl_const_compile_list env [] = []) /\
   (bvl_const_compile_list env (CONS x xs) =
      CONS (bvl_const_compile_sing env x) (bvl_const_compile_list env xs))`;;

let bvl_const_compile_eq = prove
 (`(!e env. bvl_const_compile env [e] = [bvl_const_compile_sing env e]) /\
   (!es env. bvl_const_compile env es = bvl_const_compile_list env es)`,
  MATCH_MP_TAC bvl_exp_INDUCT THEN
  RW[bvl_const_compile_def; bvl_const_compile_sing_def] THEN
  REPEAT (TOP_CASE_TAC THEN GVS[]) THEN
  CASES_ON `a1:bvl_exp list` THEN
  SIMP[bvl_const_compile_def; bvl_const_compile_sing_def; APPEND]);;

let bvl_const_compile_length = prove
 (`!n xs. LENGTH (bvl_const_compile n xs) = LENGTH xs`,
  MATCH_MP_TAC bvl_const_compile_ind THEN REPEAT STRIP_TAC THEN
  FS[bvl_const_compile_def; LENGTH_APPEND; LET_DEF; LET_END_DEF] THEN
  EVERY_CASE_TAC THEN RW[] THEN ARITH_TAC);;

let _ = cake_add_simps [bvl_const_compile_length];;

let bvl_const_compile_HD_SING = prove
 (`[HD (bvl_const_compile n [x])] = bvl_const_compile n [x]`,
  MP_TAC (SPECL [`n:(bvl_exp option) list`; `[x:bvl_exp]`]
            bvl_const_compile_length) THEN
  CASES_ON `bvl_const_compile n [x]` THEN FS[LENGTH_EQ_NIL] THEN
  CASES_ON `t:bvl_exp list` THEN FS[LENGTH] THEN ARITH_TAC);;

(* HOL4: the last case of compile_exp is impossible *)

let bvl_const_compile_exp_def = cake_def
  `bvl_const_compile_exp x =
     match bvl_const_compile [] [x] with
       CONS y _ -> y
     | _ -> bvl_Var 0`;;

(* HOL4: compile_exp_def |> SRULE [compile_eq] *)

let bvl_const_compile_exp_eq = prove
 (`!x. bvl_const_compile_exp x = bvl_const_compile_sing [] x`,
  REWRITE_TAC[bvl_const_compile_exp_def; bvl_const_compile_eq] THEN
  CASE_REWRITE_TAC[]);;
