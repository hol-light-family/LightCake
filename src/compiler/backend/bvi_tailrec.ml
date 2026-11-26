(* ========================================================================= *)
(* bvi_tailrec: port of HOL4 compiler/backend/bvi_tailrecScript.sml (CakeML  *)
(* v3479).                                                                   *)
(* A compiler phase that turns some non-tail-recursive functions into        *)
(* tail-recursive functions.                                                 *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 dummy is bvi_tailrec_dummy (dummy is a variable of word_simp).     *)
(* - HOL4 exp2_size is list_size bvi_exp_size; GENLIST is list_of_seq;       *)
(*   EXISTS is EX.  HOL4's MAP2 truncates the longer list, HOL Light's has   *)
(*   the length of its first argument: scan_expr applies it to two contexts *)
(*   of the same length (bvi_tailrecProof scan_expr_LENGTH).                 *)
(* - The clauses of a HOL Light definition share their variables, so a name  *)
(*   used with two types gets a second name: the target of LetCall (HOL4 d   *)
(*   or dest, the num option of bvi_Call) is d' or dest', the assoc_op       *)
(*   option of scan_expr (HOL4 op, also the clos_op of bvi_Op) is opo.       *)
(* - Definitions with catch-all or overlapping clauses are made with         *)
(*   sem1aux_def(_wf) (HOL4's TFL completion); HOL4's induction theorems of  *)
(*   the non-recursive ones are case analyses (BVIPAUX_TR_case_ind).         *)
(* - The PMATCH theorems (HOL4 pmatch, for the translators) are stated with  *)
(*   match, which the kit compiles into case constants.                      *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/backend_common.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* the induction theorem (a case analysis) that HOL4 makes for a            *)
(* non-recursive definition by patterns: one case per clause of the         *)
(* definition theorem def (the completed clauses)                          *)

let BVIPAUX_TR_case_ind (def:thm) : thm =
  let cls = map (fun cl -> let vs,eq = strip_forall cl in
                           let c,args = strip_comb(lhs eq) in vs,c,args)
                (conjuncts(concl def)) in
  let _,c,args0 = hd cls in
  let tty = mk_tuple_ty (map type_of args0) in
  let wfth = ISPEC (mk_abs(mk_var("x",tty),`0`)) WF_MEASURE in
  derive_induction c (map (fun (vs,_,args) -> vs,args) cls) [] wfth;;

(* the tactic of the PMATCH theorems: split on the variables that the case *)
(* constants of the goal inspect, rewriting with defs after each split      *)

let BVIPAUX_TR_SPLIT_TAC : tactic = fun (asl,w as g) ->
  let scr t = let _,s,_ = dest_case_app t in s in
  let fvs = frees w in
  match find_terms (fun t -> is_case_app t && is_var (scr t) &&
                             mem (scr t) fvs) w with
    [] -> failwith "BVIPAUX_TR_SPLIT_TAC"
  | t::_ -> CASES_ON (scr t) g;;

let BVIPAUX_TR_PMATCH_TAC (defs:thm list) : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC defs THEN CAKE_REWRITE_TAC[] THEN
  REPEAT(BVIPAUX_TR_SPLIT_TAC THEN REWRITE_TAC defs THEN CAKE_REWRITE_TAC[]);;

(* HOL4: dummy *)

let bvi_tailrec_dummy_def = cake_def
  `bvi_tailrec_dummy = bvi_Var 1234567890`;;

let MEM_exp_size_imp = prove
 (`!xs a. MEM a xs ==> bvi_exp_size a < list_size bvi_exp_size xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; list_size] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN RES_TAC THEN ASM_ARITH_TAC);;

let bvi_tailrec_is_rec_def = sem1aux_def
  `(bvi_tailrec_is_rec name (bvi_Call _ d _ NONE) <=> d = SOME name) /\
   (bvi_tailrec_is_rec _ _ <=> F)`;;

let is_rec_PMATCH = prove
 (CASE_TERM
  `!expr. bvi_tailrec_is_rec name expr =
          match expr with
            bvi_Call _ d _ NONE -> d = SOME name
          | _ -> F`,
  BVIPAUX_TR_PMATCH_TAC [bvi_tailrec_is_rec_def]);;

let bvi_tailrec_is_const_def = sem1aux_def
  `(bvi_tailrec_is_const (IntOp (clos_Const i)) <=> small_enough_int i) /\
   (bvi_tailrec_is_const _ <=> F)`;;
let _ = cake_add_simps [bvi_tailrec_is_const_def];;

let is_const_PMATCH = prove
 (CASE_TERM
  `!op. bvi_tailrec_is_const op =
        match op with
          IntOp (clos_Const i) -> small_enough_int i
        | _ -> F`,
  BVIPAUX_TR_PMATCH_TAC [bvi_tailrec_is_const_def]);;

let assoc_op_INDUCT,assoc_op_RECURSION = cake_type
  "assoc_op = Plus
            | Times
            | bvi_tailrec_Append
            | Noop";;

let v_ty_INDUCT,v_ty_RECURSION = cake_type
  "v_ty = bvi_tailrec_Int | bvi_tailrec_List | bvi_tailrec_Any";;

let op_type_def = sem1aux_def
  `(op_type bvi_tailrec_Append = bvi_tailrec_List) /\
   (op_type Noop = bvi_tailrec_Any) /\
   (op_type _ = bvi_tailrec_Int)`;;

let to_op_def = cake_def
  `(to_op Plus = IntOp clos_Add) /\
   (to_op Times = IntOp Mult) /\
   (to_op bvi_tailrec_Append = BlockOp clos_ListAppend) /\
   (to_op Noop = IntOp clos_Mod)`;;

let from_op_def = cake_def
  `from_op op =
     if op = IntOp clos_Add then Plus
     else if op = IntOp Mult then Times
     else if op = BlockOp clos_ListAppend then bvi_tailrec_Append
     else Noop`;;

let from_op_PMATCH = prove
 (CASE_TERM
  `!op. from_op op =
        match op with
          IntOp clos_Add -> Plus
        | IntOp Mult -> Times
        | BlockOp clos_ListAppend -> bvi_tailrec_Append
        | _ -> Noop`,
  BVIPAUX_TR_PMATCH_TAC [from_op_def]);;

(* HOL4: from_op_thm (EVAL of from_op on each constructor of clos_op) *)

let from_op_thm = prove
 (`(!a. from_op (clos_Label a) = Noop) /\
   (!a. from_op (clos_FFI a) = Noop) /\
   (!a. from_op (IntOp a) =
        if a = clos_Add then Plus else if a = Mult then Times else Noop) /\
   (!a. from_op (WordOp a) = Noop) /\
   (!a. from_op (BlockOp a) =
        if a = clos_ListAppend then bvi_tailrec_Append else Noop) /\
   (!a. from_op (GlobOp a) = Noop) /\
   (!a. from_op (MemOp a) = Noop) /\
   from_op clos_Install = Noop /\
   (!a. from_op (clos_ThunkOp a) = Noop)`,
  REWRITE_TAC[from_op_def] THEN CAKE_REWRITE_TAC[]);;
let _ = cake_add_simps [from_op_thm];;

let op_eq_def = sem1aux_def
  `(op_eq Plus (bvi_Op op xs) <=> op = IntOp clos_Add) /\
   (op_eq Times (bvi_Op op xs) <=> op = IntOp Mult) /\
   (op_eq bvi_tailrec_Append (bvi_Op op xs) <=> op = BlockOp clos_ListAppend) /\
   (op_eq _ _ <=> F)`;;

let op_eq_PMATCH = prove
 (CASE_TERM
  `!a expr.
     op_eq a expr =
       match expr with
         bvi_Op op xs ->
           (match a with
              Plus -> op = IntOp clos_Add
            | Times -> op = IntOp Mult
            | bvi_tailrec_Append -> op = BlockOp clos_ListAppend
            | _ -> F)
       | _ -> F`,
  BVIPAUX_TR_PMATCH_TAC [op_eq_def]);;

let op_eq_to_op = prove
 (`!iop op xs.
     op_eq iop (bvi_Op op xs) <=> op = to_op iop /\ ~(iop = Noop)`,
  GEN_TAC THEN CASES_ON `iop:assoc_op` THEN REWRITE_TAC[op_eq_def; to_op_def] THEN
  CAKE_REWRITE_TAC[]);;
let _ = cake_add_simps [op_eq_to_op];;

let apply_op_def = cake_def
  `apply_op op e1 e2 = bvi_Op (to_op op) [e1; e2]`;;

let id_from_op_def = cake_def
  `(id_from_op Plus = bvi_Op (IntOp (clos_Const (&0))) []) /\
   (id_from_op Times = bvi_Op (IntOp (clos_Const (&1))) []) /\
   (id_from_op bvi_tailrec_Append = bvi_Op (BlockOp (clos_Cons nil_tag)) []) /\
   (id_from_op Noop = bvi_tailrec_dummy)`;;

let index_of_def = sem1aux_def
  `(index_of (bvi_Var i) = SOME i) /\
   (index_of _ = NONE)`;;

let index_of_PMATCH = prove
 (CASE_TERM
  `!expr. index_of expr =
          match expr with
            bvi_Var i -> SOME i
          | _ -> NONE`,
  BVIPAUX_TR_PMATCH_TAC [index_of_def]);;

let args_from_def = sem1aux_def
  `(args_from (bvi_Call t (SOME d) as hdl) = SOME (t,d,as,hdl)) /\
   (args_from _ = NONE)`;;

let args_from_PMATCH = prove
 (CASE_TERM
  `!expr. args_from expr =
          match expr with
            bvi_Call t (SOME d) as hdl -> SOME (t,d,as,hdl)
          | _ -> NONE`,
  BVIPAUX_TR_PMATCH_TAC [args_from_def]);;

let get_bin_args_def = cake_def
  `get_bin_args op =
     match op with
       bvi_Op _ [e1; e2] -> SOME (e1,e2)
     | _ -> NONE`;;

let get_bin_args_PMATCH = prove
 (CASE_TERM
  `!op. get_bin_args op =
        match op with
          bvi_Op _ [e1; e2] -> SOME (e1,e2)
        | _ -> NONE`,
  REWRITE_TAC[get_bin_args_def]);;

let exp_size_get_bin_args = prove
 (`!x x1 x2.
     get_bin_args x = SOME (x1,x2) ==>
     bvi_exp_size x1 + bvi_exp_size x2 < bvi_exp_size x`,
  GEN_TAC THEN CASES_ON `x:bvi_exp` THEN REWRITE_TAC[get_bin_args_def] THEN
  CAKE_REWRITE_TAC[] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[type_size_def "bvi_exp"] THEN
  REWRITE_TAC(size_aux_eqs "bvi_exp") THEN REWRITE_TAC[list_size] THEN ARITH_TAC);;

let opbinargs_def = cake_def
  `opbinargs opr exp = if ~op_eq opr exp then NONE else get_bin_args exp`;;

let try_update_def = cake_def
  `(try_update vty NONE ts = ts) /\
   (try_update vty (SOME n) ts =
      if n < LENGTH ts then
        if EL n ts = bvi_tailrec_Any then
          APPEND (APPEND (TAKE n ts) [vty]) (DROP (n + 1) ts)
        else ts
      else ts)`;;

let is_arith_def = cake_def
  `is_arith op =
     match op with
       IntOp clos_Add -> T
     | IntOp clos_Sub -> T
     | IntOp Mult -> T
     | _ -> F`;;

let is_arith_PMATCH = prove
 (CASE_TERM
  `!op. is_arith op =
        match op with
          IntOp clos_Add -> T
        | IntOp clos_Sub -> T
        | IntOp Mult -> T
        | _ -> F`,
  REWRITE_TAC[is_arith_def]);;

let is_rel_def = cake_def
  `is_rel op =
     match op with
       IntOp clos_Less -> T
     | IntOp LessEq -> T
     | IntOp Greater -> T
     | IntOp GreaterEq -> T
     | _ -> F`;;

let is_rel_PMATCH = prove
 (CASE_TERM
  `!op. is_rel op =
        match op with
          IntOp clos_Less -> T
        | IntOp LessEq -> T
        | IntOp Greater -> T
        | IntOp GreaterEq -> T
        | _ -> F`,
  REWRITE_TAC[is_rel_def]);;

(* the termination tactic: TERM_TAC with the size fact of each assumption *)
(* get_bin_args e = SOME (x,y) (HOL4: imp_res_tac exp_size_get_bin_args)   *)

let BVIPAUX_TR_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    let th' = try MATCH_MP exp_size_get_bin_args th with Failure _ ->
              MATCH_MP exp_size_get_bin_args (SYM th) in
    MP_TAC th')) THEN
  (TERM_TAC ORELSE (PRINT_GOAL_TAC THEN NO_TAC));;

let term_ok_int_def = sem1aux_def_wf
  `MEASURE (\p:v_ty list # bvi_exp. bvi_exp_size (SND p))`
  BVIPAUX_TR_TC_TAC
  `term_ok_int ts expr <=>
     match expr with
       bvi_Var i -> if i < LENGTH ts then EL i ts = bvi_tailrec_Int else F
     | bvi_Op op xs ->
         (match get_bin_args expr with
            NONE -> xs = [] /\ bvi_tailrec_is_const op
          | SOME (x,y) -> is_arith op /\ term_ok_int ts x /\ term_ok_int ts y)
     | _ -> F`;;

let term_ok_int_ind = cake_ind "term_ok_int";;

let term_ok_any_def = sem1aux_def_wf
  `MEASURE (\p:v_ty list # bool # bvi_exp. bvi_exp_size (SND (SND p)))`
  BVIPAUX_TR_TC_TAC
  `(term_ok_any ts list (bvi_Var i) <=>
      if ~list then i < LENGTH ts
      else if i < LENGTH ts then EL i ts = bvi_tailrec_List
      else F) /\
   (term_ok_any ts list (bvi_Op op xs) <=>
      match get_bin_args (bvi_Op op xs) with
        NONE -> xs = [] /\
                (if list then op = BlockOp (clos_Cons 0)
                 else bvi_tailrec_is_const op)
      | SOME (x,y) ->
          if op = BlockOp clos_ListAppend then
            term_ok_any ts T x /\ term_ok_any ts T y
          else if ~list /\ is_arith op then term_ok_int ts x /\ term_ok_int ts y
          else if ~list /\ is_rel op then term_ok_int ts x /\ term_ok_int ts y
          else if op = BlockOp (clos_Cons 0) then
            term_ok_any ts T x /\ term_ok_any ts F y
          else F) /\
   (term_ok_any ts list expr <=> F)`;;

let BVIPAUX_term_ok_any_ind0 = cake_ind "term_ok_any";;

let is_op_thms = prove
 (`~is_arith (BlockOp (clos_Cons 0)) /\ ~is_arith (BlockOp clos_ListAppend) /\
   ~is_rel (BlockOp (clos_Cons 0)) /\ ~is_rel (BlockOp clos_ListAppend) /\
   (!op. ~(op = BlockOp clos_ListAppend) /\ is_arith op <=> is_arith op) /\
   (!op. ~(op = BlockOp clos_ListAppend) /\ ~is_arith op /\ is_rel op <=>
         is_rel op) /\
   (!op. ~is_arith op /\ ~is_rel op /\ op = BlockOp (clos_Cons 0) <=>
         op = BlockOp (clos_Cons 0)) /\
   (!op. ~(op = BlockOp clos_ListAppend) /\ op = BlockOp (clos_Cons 0) <=>
         op = BlockOp (clos_Cons 0))`,
  REPEAT CONJ_TAC THEN BVIPAUX_TR_PMATCH_TAC [is_arith_def; is_rel_def] THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[]);;

(* HOL4: term_ok_any_ind = term_ok_any_ind |> SRULE [is_op_thms]: the     *)
(* conditions that op = BlockOp (clos_Cons 0) implies are dropped          *)

let term_ok_any_ind = prove
 (`!P:v_ty list->bool->bvi_exp->bool.
       (!ts list i. P ts list (bvi_Var i)) /\
       (!ts list op xs.
          (!x y. get_bin_args (bvi_Op op xs) = SOME (x,y) /\
                 op = BlockOp (clos_Cons 0)
                 ==> P ts F y) /\
          (!y x. get_bin_args (bvi_Op op xs) = SOME (x,y) /\
                 op = BlockOp (clos_Cons 0)
                 ==> P ts T x) /\
          (!y x. get_bin_args (bvi_Op op xs) = SOME (x,y) /\
                 op = BlockOp clos_ListAppend
                 ==> P ts T x) /\
          (!x y. get_bin_args (bvi_Op op xs) = SOME (x,y) /\
                 op = BlockOp clos_ListAppend
                 ==> P ts T y)
          ==> P ts list (bvi_Op op xs)) /\
       (!ts list v4 v5 v6. P ts list (bvi_If v4 v5 v6)) /\
       (!ts list v7 v8. P ts list (bvi_Let v7 v8)) /\
       (!ts list v9. P ts list (bvi_Raise v9)) /\
       (!ts list v10. P ts list (bvi_Tick v10)) /\
       (!ts list v11 v12 v13 v14. P ts list (bvi_Call v11 v12 v13 v14)) /\
       (!ts list v15 v16. P ts list (bvi_Force v15 v16)) /\
       (!ts list v19 v20 v21 v22 v23.
          P ts list (LetCall v19 v20 v21 v22 v23)) /\
       (!ts list v24. P ts list (bvi_Return v24))
       ==> !x1 x2 x3. P x1 x2 x3`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC BVIPAUX_term_ok_any_ind0 THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o SPECL [`ts:v_ty list`; `list:bool`]) THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_MESON_TAC[is_op_thms]);;

let term_ok_def = cake_def
  `term_ok ts ty expr <=>
     match ty with
       bvi_tailrec_Any -> term_ok_any ts F expr
     | bvi_tailrec_Int -> term_ok_int ts expr
     | bvi_tailrec_List -> term_ok_any ts T expr`;;

(* Simple tail checking before rewriting.  Swap arguments when commutative. *)

let try_swap_def = sem1aux_def
  `(try_swap loc bvi_tailrec_Append exp = exp) /\
   (try_swap loc opr exp =
      match opbinargs opr exp with
        NONE -> exp
      | SOME (l,r) ->
          if bvi_tailrec_is_rec loc l then apply_op opr r l else exp)`;;

(* Check if ok to lift xs into accumulator *)

let check_op_def = cake_def
  `check_op ts opr loc exp =
     match opbinargs opr (try_swap loc opr exp) with
       NONE -> NONE
     | SOME (xs,f) ->
         if bvi_tailrec_is_rec loc f /\ term_ok ts (op_type opr) xs then
           SOME (apply_op opr xs f)
         else NONE`;;

(* Type analysis *)

let decide_ty_def = sem1aux_def
  `(decide_ty bvi_tailrec_Int bvi_tailrec_Int = bvi_tailrec_Int) /\
   (decide_ty bvi_tailrec_List bvi_tailrec_List = bvi_tailrec_List) /\
   (decide_ty _ _ = bvi_tailrec_Any)`;;
let _ = cake_add_simps [decide_ty_def];;

let decide_ty_PMATCH = prove
 (CASE_TERM
  `!ty1 ty2.
     decide_ty ty1 ty2 =
       match (ty1,ty2) with
         (bvi_tailrec_Int,bvi_tailrec_Int) -> bvi_tailrec_Int
       | (bvi_tailrec_List,bvi_tailrec_List) -> bvi_tailrec_List
       | _ -> bvi_tailrec_Any`,
  REPEAT GEN_TAC THEN CASES_ON `ty1:v_ty` THEN CASES_ON `ty2:v_ty` THEN
  REWRITE_TAC[decide_ty_def] THEN CAKE_REWRITE_TAC[]);;

let LAST1_def = sem1aux_def
  `(LAST1 [] = NONE:A option) /\
   (LAST1 [x] = SOME x) /\
   (LAST1 (CONS x xs) = LAST1 xs)`;;

let LAST1_ind = cake_ind "LAST1";;

let update_context_def = cake_def
  `update_context ty ts x1 x2 =
     try_update ty (index_of x2) (try_update ty (index_of x1) ts)`;;

let arg_ty_def = sem1aux_def
  `(arg_ty (IntOp (clos_Const i)) =
      (if small_enough_int i then bvi_tailrec_Int else bvi_tailrec_Any)) /\
   (arg_ty (IntOp clos_Add) = bvi_tailrec_Int) /\
   (arg_ty (IntOp clos_Sub) = bvi_tailrec_Int) /\
   (arg_ty (IntOp Mult) = bvi_tailrec_Int) /\
   (arg_ty (IntOp clos_Div) = bvi_tailrec_Int) /\
   (arg_ty (IntOp clos_Mod) = bvi_tailrec_Int) /\
   (arg_ty (IntOp LessEq) = bvi_tailrec_Int) /\
   (arg_ty (IntOp clos_Less) = bvi_tailrec_Int) /\
   (arg_ty (IntOp Greater) = bvi_tailrec_Int) /\
   (arg_ty (IntOp GreaterEq) = bvi_tailrec_Int) /\
   (arg_ty (BlockOp clos_ListAppend) = bvi_tailrec_List) /\
   (arg_ty _ = bvi_tailrec_Any)`;;

let arg_ty_PMATCH = prove
 (CASE_TERM
  `!op.
     arg_ty op =
       match op with
         IntOp clos_Add -> bvi_tailrec_Int
       | IntOp clos_Sub -> bvi_tailrec_Int
       | IntOp Mult -> bvi_tailrec_Int
       | IntOp clos_Div -> bvi_tailrec_Int
       | IntOp clos_Mod -> bvi_tailrec_Int
       | IntOp LessEq -> bvi_tailrec_Int
       | IntOp clos_Less -> bvi_tailrec_Int
       | IntOp Greater -> bvi_tailrec_Int
       | IntOp GreaterEq -> bvi_tailrec_Int
       | IntOp (clos_Const i) ->
           if small_enough_int i then bvi_tailrec_Int else bvi_tailrec_Any
       | BlockOp clos_ListAppend -> bvi_tailrec_List
       | _ -> bvi_tailrec_Any`,
  BVIPAUX_TR_PMATCH_TAC [arg_ty_def]);;

let op_ty_def = sem1aux_def
  `(op_ty (IntOp clos_Add) = bvi_tailrec_Int) /\
   (op_ty (IntOp clos_Sub) = bvi_tailrec_Int) /\
   (op_ty (IntOp Mult) = bvi_tailrec_Int) /\
   (op_ty (IntOp clos_Div) = bvi_tailrec_Int) /\
   (op_ty (IntOp clos_Mod) = bvi_tailrec_Int) /\
   (op_ty (BlockOp clos_ListAppend) = bvi_tailrec_List) /\
   (op_ty (BlockOp (clos_Cons tag)) =
      if tag = nil_tag \/ tag = cons_tag then bvi_tailrec_List
      else bvi_tailrec_Any) /\
   (op_ty (IntOp (clos_Const i)) =
      if small_enough_int i then bvi_tailrec_Int else bvi_tailrec_Any) /\
   (op_ty _ = bvi_tailrec_Any)`;;

let op_ty_PMATCH = prove
 (CASE_TERM
  `!op.
     op_ty op =
       match op with
         IntOp clos_Add -> bvi_tailrec_Int
       | IntOp clos_Sub -> bvi_tailrec_Int
       | IntOp Mult -> bvi_tailrec_Int
       | IntOp clos_Div -> bvi_tailrec_Int
       | IntOp clos_Mod -> bvi_tailrec_Int
       | BlockOp clos_ListAppend -> bvi_tailrec_List
       | BlockOp (clos_Cons tag) ->
           if tag = cons_tag \/ tag = nil_tag then bvi_tailrec_List
           else bvi_tailrec_Any
       | IntOp (clos_Const i) ->
           if small_enough_int i then bvi_tailrec_Int else bvi_tailrec_Any
       | _ -> bvi_tailrec_Any`,
  BVIPAUX_TR_PMATCH_TAC [op_ty_def] THEN REWRITE_TAC[DISJ_SYM]);;

let scan_expr_def = sem1aux_def_wf
  `MEASURE (\p:v_ty list # num # bvi_exp list.
              list_size bvi_exp_size (SND (SND p)))`
  BVIPAUX_TR_TC_TAC
  `(scan_expr ts loc [] = []) /\
   (scan_expr ts loc (CONS x (CONS y xs)) =
      let (tx,ty,r,opo) = HD (scan_expr ts loc [x]) in
        CONS (tx,ty,r,opo) (scan_expr tx loc (CONS y xs))) /\
   (scan_expr ts loc [bvi_Var n] =
      let ty = if n < LENGTH ts then EL n ts else bvi_tailrec_Any in
        [(ts,ty,F,NONE)]) /\
   (scan_expr ts loc [bvi_If xi xt xe] =
      (match HD (scan_expr ts loc [xi]) with
         (ti,tyi,_,oi) ->
           (match HD (scan_expr ti loc [xt]) with
              (tt,ty1,_,ot) ->
                (match HD (scan_expr ti loc [xe]) with
                   (te,ty2,_,oe) ->
                     let opo = (match ot with NONE -> oe | _ -> ot) in
                     let ty = (match opo with
                                 NONE -> decide_ty ty1 ty2
                               | SOME opr ->
                                   decide_ty ty1 (decide_ty ty2 (op_type opr))) in
                       [(MAP2 decide_ty tt te,ty,IS_SOME oe,opo)])))) /\
   (scan_expr ts loc [bvi_Let xs x] =
      let ys = scan_expr ts loc xs in
      let tt = MAP (FST o SND) ys in
      let tr = (match LAST1 ys with SOME c -> FST c | NONE -> ts) in
        (match HD (scan_expr (APPEND tt tr) loc [x]) with
           (tu,ty,_,opo) -> [(DROP (LENGTH ys) tu,ty,F,opo)])) /\
   (scan_expr ts loc [bvi_Raise x] = [(ts,bvi_tailrec_Any,F,NONE)]) /\
   (scan_expr ts loc [bvi_Tick x] = scan_expr ts loc [x]) /\
   (scan_expr ts loc [bvi_Force _ n] =
      let ty = if n < LENGTH ts then EL n ts else bvi_tailrec_Any in
        [(ts,ty,F,NONE)]) /\
   (scan_expr ts loc [bvi_Call t d xs h] = [(ts,bvi_tailrec_Any,F,NONE)]) /\
   (scan_expr ts loc [bvi_Return xs] = [(ts,bvi_tailrec_Any,F,NONE)]) /\
   (scan_expr ts loc [LetCall rets t d' xs y] =
      [(ts,bvi_tailrec_Any,F,NONE)]) /\
   (scan_expr ts loc [bvi_Op op xs] =
      let opr = from_op op in
      let opt = op_type opr in
        match opr with
          Noop ->
            if arg_ty op = bvi_tailrec_Int then
              (match get_bin_args (bvi_Op op xs) with
                 NONE ->
                   if bvi_tailrec_is_const op then [(ts,bvi_tailrec_Int,F,NONE)]
                   else [(ts,bvi_tailrec_Any,F,NONE)]
               | SOME (x,y) ->
                   if ~bvi_tailrec_is_const op then
                     [(update_context bvi_tailrec_Int ts x y,bvi_tailrec_Any,F,
                       NONE)]
                   else [(ts,bvi_tailrec_Any,F,NONE)])
            else if op = BlockOp (clos_Cons 0) /\ xs = [] then
              [(ts,bvi_tailrec_List,F,NONE)]
            else [(ts,bvi_tailrec_Any,F,NONE)]
        | _ ->
            if IS_SOME (check_op ts opr loc (bvi_Op op xs)) then
              [(ts,opt,F,SOME opr)]
            else if term_ok ts opt (bvi_Op op xs) then
              (match get_bin_args (bvi_Op op xs) with
                 NONE -> [(ts,bvi_tailrec_Any,F,NONE)]
               | SOME (x,y) -> [(update_context opt ts x y,opt,F,NONE)])
            else [(ts,bvi_tailrec_Any,F,NONE)])`;;

let scan_expr_ind = cake_ind "scan_expr";;

let scan_expr_sing_def = sem1aux_def_wf
  `MEASURE (\x:(v_ty list # num # bvi_exp) + (v_ty list # num # bvi_exp list).
              sum_CASE x (\p. bvi_exp_size (SND (SND p)))
                         (\p. list_size bvi_exp_size (SND (SND p))))`
  BVIPAUX_TR_TC_TAC
  `(scan_expr_sing ts loc (bvi_Var n) =
      let ty = if n < LENGTH ts then EL n ts else bvi_tailrec_Any in
        (ts,ty,F,NONE)) /\
   (scan_expr_sing ts loc (bvi_If xi xt xe) =
      (match scan_expr_sing ts loc xi with
         (ti,tyi,_,oi) ->
           (match scan_expr_sing ti loc xt with
              (tt,ty1,_,ot) ->
                (match scan_expr_sing ti loc xe with
                   (te,ty2,_,oe) ->
                     let opo = (match ot with NONE -> oe | _ -> ot) in
                     let ty = (match opo with
                                 NONE -> decide_ty ty1 ty2
                               | SOME opr ->
                                   decide_ty ty1 (decide_ty ty2 (op_type opr))) in
                       (MAP2 decide_ty tt te,ty,IS_SOME oe,opo))))) /\
   (scan_expr_sing ts loc (bvi_Let xs x) =
      let ys = scan_expr_list ts loc xs in
      let tt = MAP (FST o SND) ys in
      let tr = (match LAST1 ys with SOME c -> FST c | NONE -> ts) in
        (match scan_expr_sing (APPEND tt tr) loc x with
           (tu,ty,_,opo) -> (DROP (LENGTH ys) tu,ty,F,opo))) /\
   (scan_expr_sing ts loc (bvi_Raise x) = (ts,bvi_tailrec_Any,F,NONE)) /\
   (scan_expr_sing ts loc (bvi_Tick x) = scan_expr_sing ts loc x) /\
   (scan_expr_sing ts loc (bvi_Force _ n) =
      let ty = if n < LENGTH ts then EL n ts else bvi_tailrec_Any in
        (ts,ty,F,NONE)) /\
   (scan_expr_sing ts loc (bvi_Call t d xs h) = (ts,bvi_tailrec_Any,F,NONE)) /\
   (scan_expr_sing ts loc (bvi_Return xs) = (ts,bvi_tailrec_Any,F,NONE)) /\
   (scan_expr_sing ts loc (LetCall rets t d' xs y) =
      (ts,bvi_tailrec_Any,F,NONE)) /\
   (scan_expr_sing ts loc (bvi_Op op xs) =
      let opr = from_op op in
      let opt = op_type opr in
        match opr with
          Noop ->
            if arg_ty op = bvi_tailrec_Int then
              (match get_bin_args (bvi_Op op xs) with
                 NONE ->
                   if bvi_tailrec_is_const op then (ts,bvi_tailrec_Int,F,NONE)
                   else (ts,bvi_tailrec_Any,F,NONE)
               | SOME (x,y) ->
                   if ~bvi_tailrec_is_const op then
                     (update_context bvi_tailrec_Int ts x y,bvi_tailrec_Any,F,NONE)
                   else (ts,bvi_tailrec_Any,F,NONE))
            else if op = BlockOp (clos_Cons 0) /\ xs = [] then
              (ts,bvi_tailrec_List,F,NONE)
            else (ts,bvi_tailrec_Any,F,NONE)
        | _ ->
            if IS_SOME (check_op ts opr loc (bvi_Op op xs)) then
              (ts,opt,F,SOME opr)
            else if term_ok ts opt (bvi_Op op xs) then
              (match get_bin_args (bvi_Op op xs) with
                 NONE -> (ts,bvi_tailrec_Any,F,NONE)
               | SOME (x,y) -> (update_context opt ts x y,opt,F,NONE))
            else (ts,bvi_tailrec_Any,F,NONE)) /\
   (scan_expr_list ts loc [] = []) /\
   (scan_expr_list ts loc (CONS x xs) =
      let (tx,ty,r,opo) = scan_expr_sing ts loc x in
        CONS (tx,ty,r,opo) (scan_expr_list tx loc xs))`;;

let scan_expr_sing_ind = cake_ind "scan_expr_sing";;

(* the structural induction of bvi_exp and bvi_exp list (HOL4 Induct on   *)
(* the mutual datatype), with no predicate for bvi_exp option             *)

let BVIPAUX_TR_exp_induct = prove
 (`!P0 P1.
     (!a. P0 (bvi_Var a)) /\
     (!a0 a1 a2. P0 a0 /\ P0 a1 /\ P0 a2 ==> P0 (bvi_If a0 a1 a2)) /\
     (!a0 a1. P1 a0 /\ P0 a1 ==> P0 (bvi_Let a0 a1)) /\
     (!a. P0 a ==> P0 (bvi_Raise a)) /\
     (!a. P0 a ==> P0 (bvi_Tick a)) /\
     (!a0 a1 a2 a3. P1 a2 /\ (!e. a3 = SOME e ==> P0 e)
                    ==> P0 (bvi_Call a0 a1 a2 a3)) /\
     (!a0 a1. P0 (bvi_Force a0 a1)) /\
     (!a0 a1. P1 a1 ==> P0 (bvi_Op a0 a1)) /\
     (!a0 a1 a2 a3 a4. P1 a3 /\ P0 a4 ==> P0 (LetCall a0 a1 a2 a3 a4)) /\
     (!a. P1 a ==> P0 (bvi_Return a)) /\
     P1 [] /\
     (!a0 a1. P0 a0 /\ P1 a1 ==> P1 (CONS a0 a1))
     ==> (!x. P0 x) /\ (!l. P1 l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`P0:bvi_exp->bool`; `P1:bvi_exp list->bool`;
                 `\opt:bvi_exp option. !e. opt = SOME e ==> P0 e`]
                bvi_exp_INDUCT) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    TRY(ASM_SIMP_TAC[] THEN NO_TAC) THEN ASM_MESON_TAC[];
    SIMP_TAC[]]);;

let scan_expr_eq = prove
 (`(!e ts loc. scan_expr ts loc [e] = [scan_expr_sing ts loc e]) /\
   (!es ts loc. scan_expr ts loc es = scan_expr_list ts loc es)`,
  MATCH_MP_TAC BVIPAUX_TR_exp_induct THEN REPEAT STRIP_TAC THEN
  GVS[scan_expr_def; scan_expr_sing_def] THEN
  REPEAT(PAIRARG_TAC THEN TRY(GVS[])) THEN
  REPEAT(TOP_CASE_TAC THEN TRY(GVS[])) THEN
  CASES_ON `a1:bvi_exp list` THEN GVS[scan_expr_def; scan_expr_sing_def] THEN
  REPEAT(PAIRARG_TAC THEN TRY(GVS[])));;

let push_call_def = sem1aux_def
  `(push_call n op acc exp (SOME (ticks,dest:A,args,handler)) =
      bvi_Call ticks (SOME n) (APPEND args [apply_op op (bvi_Var acc) exp])
        handler) /\
   (push_call _ _ _ _ _ = bvi_tailrec_dummy)`;;

let rewrite_def = sem1aux_def_wf
  `MEASURE (\p:num # num # assoc_op # num # v_ty list # bvi_exp.
              bvi_exp_size (SND (SND (SND (SND (SND p))))))`
  BVIPAUX_TR_TC_TAC
  `(rewrite loc next opr acc ts (bvi_Var n) = (F,bvi_Var n)) /\
   (rewrite loc next opr acc ts (bvi_If x1 x2 x3) =
      let t1 = FST (HD (scan_expr ts loc [x1])) in
      let (r2,y2) = rewrite loc next opr acc t1 x2 in
      let (r3,y3) = rewrite loc next opr acc t1 x3 in
      let z2 = if r2 then y2 else apply_op opr (bvi_Var acc) x2 in
      let z3 = if r3 then y3 else apply_op opr (bvi_Var acc) x3 in
        ((r2 \/ r3),bvi_If x1 z2 z3)) /\
   (rewrite loc next opr acc ts (bvi_Let xs x) =
      let ys = scan_expr ts loc xs in
      let tt = MAP (FST o SND) ys in
      let tr = (match LAST1 ys with NONE -> ts | SOME c -> FST c) in
      let (r,y) = rewrite loc next opr (acc + LENGTH xs) (APPEND tt tr) x in
        (r,bvi_Let xs y)) /\
   (rewrite loc next opr acc ts (bvi_Tick x) =
      let (r,y) = rewrite loc next opr acc ts x in (r,bvi_Tick y)) /\
   (rewrite loc next opr acc ts (bvi_Force l v) = (F,bvi_Force l v)) /\
   (rewrite loc next opr acc ts exp =
      match check_op ts opr loc exp with
        NONE -> (F,apply_op opr (bvi_Var acc) exp)
      | SOME exp ->
          (match opbinargs opr exp with
             NONE -> (F,apply_op opr (bvi_Var acc) exp)
           | SOME (xs,f) -> (T,push_call next opr acc xs (args_from f))))`;;

let rewrite_ind = cake_ind "rewrite";;

let rewrite_PMATCH = prove
 (CASE_TERM
  `!loc next opr acc ts expr.
     rewrite loc next opr acc ts expr =
       match expr with
         bvi_Var n -> (F,bvi_Var n)
       | bvi_If x1 x2 x3 ->
           let t1 = FST (HD (scan_expr ts loc [x1])) in
           let (r2,y2) = rewrite loc next opr acc t1 x2 in
           let (r3,y3) = rewrite loc next opr acc t1 x3 in
           let z2 = if r2 then y2 else apply_op opr (bvi_Var acc) x2 in
           let z3 = if r3 then y3 else apply_op opr (bvi_Var acc) x3 in
             ((r2 \/ r3),bvi_If x1 z2 z3)
       | bvi_Let xs x ->
           let ys = scan_expr ts loc xs in
           let tt = MAP (FST o SND) ys in
           let tr = (match LAST1 ys with NONE -> ts | SOME c -> FST c) in
           let (r,y) = rewrite loc next opr (acc + LENGTH xs) (APPEND tt tr) x in
             (r,bvi_Let xs y)
       | bvi_Tick x ->
           let (r,y) = rewrite loc next opr acc ts x in (r,bvi_Tick y)
       | bvi_Force l v -> (F,bvi_Force l v)
       | _ ->
           (match check_op ts opr loc expr with
              NONE -> (F,apply_op opr (bvi_Var acc) expr)
            | SOME expr2 ->
                (match opbinargs opr expr2 with
                   NONE -> (F,apply_op opr (bvi_Var acc) expr2)
                 | SOME (xs,f) ->
                     (T,push_call next opr acc xs (args_from f))))`,
  REPEAT GEN_TAC THEN CASES_ON `expr:bvi_exp` THEN
  REWRITE_TAC[rewrite_def] THEN CAKE_REWRITE_TAC[]);;

(* HOL4: rewrite_eq = rewrite_def |> SRULE [scan_expr_eq] *)

let rewrite_eq =
  REWRITE_RULE[CONJUNCT2 scan_expr_eq]
    (REWRITE_RULE[CONJUNCT1 scan_expr_eq; HD] rewrite_def);;

(* Top-level expression check *)

let has_rec_def = sem1aux_def_wf
  `MEASURE (\p:num # bvi_exp list. list_size bvi_exp_size (SND p))`
  BVIPAUX_TR_TC_TAC
  `(has_rec loc [] <=> F) /\
   (has_rec loc (CONS x (CONS y xs)) <=>
      if has_rec loc [x] then T else has_rec loc (CONS y xs)) /\
   (has_rec loc [bvi_If x1 x2 x3] <=>
      if has_rec loc [x2] then T else has_rec loc [x3]) /\
   (has_rec loc [bvi_Let xs x] <=> has_rec loc [x]) /\
   (has_rec loc [bvi_Tick x] <=> has_rec loc [x]) /\
   (has_rec loc [bvi_Op op xs] <=>
      if EX (bvi_tailrec_is_rec loc) xs then T else has_rec loc xs) /\
   (has_rec loc [x] <=> F)`;;

let has_rec_ind = cake_ind "has_rec";;

let has_rec1_def = cake_def
  `has_rec1 loc x <=> has_rec loc [x]`;;

let has_rec_sing_def = sem1aux_def_wf
  `MEASURE (\x:(num # bvi_exp) + (num # bvi_exp list).
              sum_CASE x (\p. bvi_exp_size (SND p))
                         (\p. list_size bvi_exp_size (SND p)))`
  BVIPAUX_TR_TC_TAC
  `(has_rec_sing loc (bvi_If x1 x2 x3) <=>
      if has_rec_sing loc x2 then T else has_rec_sing loc x3) /\
   (has_rec_sing loc (bvi_Let xs x) <=> has_rec_sing loc x) /\
   (has_rec_sing loc (bvi_Tick x) <=> has_rec_sing loc x) /\
   (has_rec_sing loc (bvi_Op op xs) <=>
      if EX (bvi_tailrec_is_rec loc) xs then T else has_rec_list loc xs) /\
   (has_rec_sing loc x <=> F) /\
   (has_rec_list loc [] <=> F) /\
   (has_rec_list loc (CONS x xs) <=>
      if has_rec_sing loc x then T else has_rec_list loc xs)`;;

let has_rec_sing_ind = cake_ind "has_rec_sing";;

let has_rec_eq = prove
 (`(!e loc. has_rec loc [e] <=> has_rec_sing loc e) /\
   (!es loc. has_rec loc es <=> has_rec_list loc es)`,
  MATCH_MP_TAC BVIPAUX_TR_exp_induct THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[has_rec_def; has_rec_sing_def] THEN
  CASES_ON `a1:bvi_exp list` THEN
  ASM_REWRITE_TAC[has_rec_def; has_rec_sing_def] THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[]));;

let has_rec_test1 = prove
 (`has_rec1 0 (bvi_Let [] (bvi_Call 0 (SOME 0) [] NONE)) <=> F`,
  REWRITE_TAC[has_rec1_def; has_rec_def]);;

let has_rec_test2 = prove
 (`has_rec1 0 (bvi_Op (IntOp clos_Add) [bvi_Call 0 (SOME 0) [] NONE; bvi_Var 0])
   <=> T`,
  REWRITE_TAC[has_rec1_def; has_rec_def; EX; bvi_tailrec_is_rec_def]);;

let check_exp_def = cake_def
  `check_exp loc arity exp =
     if ~has_rec1 loc exp then NONE else
       let context = REPLICATE arity bvi_tailrec_Any in
         match scan_expr context loc [exp] with
           [] -> NONE
         | CONS (ts,ty,r,opr) _ ->
             (match opr with
                NONE -> NONE
              | SOME op -> if ~(ty = op_type op) then NONE else opr)`;;

(* HOL4: check_exp_eq = check_exp_def |> SRULE [scan_expr_eq, has_rec1_def, *)
(* has_rec_eq]                                                               *)

let check_exp_eq =
  CAKE_REWRITE_RULE[]
    (REWRITE_RULE[CONJUNCT1 scan_expr_eq; has_rec1_def; CONJUNCT1 has_rec_eq]
       check_exp_def);;

let let_wrap_def = cake_def
  `let_wrap arity id exp =
     bvi_Let (APPEND (list_of_seq (\i. bvi_Var i) arity) [id]) exp`;;

let mk_aux_call_def = cake_def
  `mk_aux_call loc arity id =
     bvi_Call 0 (SOME loc) (CONS id (list_of_seq (\i. bvi_Var i) arity)) NONE`;;

let bvi_tailrec_compile_exp_def = cake_def
  `bvi_tailrec_compile_exp loc next arity exp =
     match check_exp loc arity exp with
       NONE -> NONE
     | SOME op ->
         let context = REPLICATE arity bvi_tailrec_Any in
         let (r,opt) = rewrite loc next op arity context exp in
         let aux = let_wrap arity (id_from_op op) opt in
           SOME (aux,opt)`;;

let bvi_tailrec_compile_each_def = cake_def
  `(bvi_tailrec_compile_each next [] = (next,[])) /\
   (bvi_tailrec_compile_each next (CONS (loc,arity,exp) xs) =
      match bvi_tailrec_compile_exp loc next arity exp with
        NONE ->
          let (n,ys) = bvi_tailrec_compile_each next xs in
            (n,CONS (loc,arity,exp) ys)
      | SOME (exp_aux,exp_opt) ->
          let (n,ys) = bvi_tailrec_compile_each (next + bvl_to_bvi_namespaces) xs in
            (n,CONS (loc,arity,exp_aux) (CONS (next,arity + 1,exp_opt) ys)))`;;

let bvi_tailrec_compile_each_ind = cake_ind "bvi_tailrec_compile_each";;

let bvi_tailrec_compile_prog_def = cake_def
  `bvi_tailrec_compile_prog do_it next xs =
     if do_it then bvi_tailrec_compile_each next xs else (next,xs)`;;

let scan_expr_not_nil = prove
 (`!ts loc x. ~(scan_expr ts loc [x] = [])`,
  REWRITE_TAC[CONJUNCT1 scan_expr_eq; NOT_CONS_NIL]);;
let _ = cake_add_simps [scan_expr_not_nil];;

let LENGTH_scan_expr = prove
 (`!ts loc xs. LENGTH (scan_expr ts loc xs) = LENGTH xs`,
  REWRITE_TAC[CONJUNCT2 scan_expr_eq] THEN
  SUBGOAL_THEN `!xs ts loc. LENGTH (scan_expr_list ts loc xs) = LENGTH xs`
    (fun th -> REWRITE_TAC[th]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[scan_expr_sing_def; LENGTH] THEN
  REPEAT GEN_TAC THEN REPEAT(PAIRARG_TAC THEN TRY(GVS[])) THEN
  ASM_REWRITE_TAC[LENGTH]);;
let _ = cake_add_simps [LENGTH_scan_expr];;

let scan_expr_SING = prove
 (`!ts loc x. [HD (scan_expr ts loc [x])] = scan_expr ts loc [x]`,
  REWRITE_TAC[CONJUNCT1 scan_expr_eq; HD]);;
let _ = cake_add_simps [scan_expr_SING];;

let scan_expr_HD_SING = prove
 (`!ts loc x y. HD (scan_expr ts loc [x]) = y <=> scan_expr ts loc [x] = [y]`,
  REWRITE_TAC[CONJUNCT1 scan_expr_eq; HD; CONS_11]);;
let _ = cake_add_simps [scan_expr_HD_SING];;

let check_exp_SOME_simp = prove
 (`!loc arity expr op.
     check_exp loc arity expr = SOME op <=>
     ?ts ty r.
       has_rec1 loc expr /\
       scan_expr (REPLICATE arity bvi_tailrec_Any) loc [expr] =
         [(ts,ty,r,SOME op)] /\
       ty = op_type op`,
  REPEAT GEN_TAC THEN REWRITE_TAC[check_exp_def; CONJUNCT1 scan_expr_eq] THEN
  CAKE_REWRITE_TAC[LET_DEF; LET_END_DEF; CONS_11] THEN
  ASM_CASES_TAC `has_rec1 loc expr` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  REPEAT(PAIRARG_TAC THEN TRY(GVS[])) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  REPEAT(TOP_CASE_TAC THEN TRY(GVS[])) THEN
  MESON_TAC[]);;
let _ = cake_add_simps [check_exp_SOME_simp];;

(* Test rewriting.  HOL4 proves these tests by EVAL; here by the call-by- *)
(* value conversion of HOL Light (compute.ml) with the equations of this  *)
(* file and the case, distinctness and injectivity theorems of the types. *)

let BVIPAUX_TR_EL = prove
 (`!n (l:A list). EL n l = if n = 0 then HD l else EL (n - 1) (TL l)`,
  INDUCT_TAC THEN REWRITE_TAC[EL; NOT_SUC; SUC_SUB1]);;

let BVIPAUX_TR_REPLICATE = prove
 (`!n (x:A). REPLICATE n x = if n = 0 then [] else CONS x (REPLICATE (n - 1) x)`,
  INDUCT_TAC THEN REWRITE_TAC[REPLICATE; NOT_SUC; SUC_SUB1]);;

let BVIPAUX_TR_list_of_seq = prove
 (`!n (s:num->A). list_of_seq s n =
     if n = 0 then [] else APPEND (list_of_seq s (n - 1)) [s (n - 1)]`,
  INDUCT_TAC THEN REWRITE_TAC[list_of_seq; NOT_SUC; SUC_SUB1]);;

let BVIPAUX_TR_cs =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  num_compute_add_convs cs;
  int_compute_add_convs cs;
  Compute.add_conv (`LET:(A->B)->A->B`,2,let_CONV) cs;
  let tys = ["bvi_exp"; "clos_op"; "int_op"; "block_op"; "mem_op";
             "assoc_op"; "v_ty"; "list"; "option"; "prod"] in
  let cis = map case_info_of_tyname tys in
  Compute.add_thms (map (fun ci -> ci.ci_def) cis) cs;
  Compute.add_thms (flat (map (fun ci -> ci.ci_distinct @ ci.ci_inject) cis)) cs;
  Compute.add_thms
   [LET_END_DEF; HD; TL; LENGTH; APPEND; MAP; o_THM; FST; SND; IS_SOME_DEF; EX;
    MAP2;
    TAKE_DEF; DROP_DEF; BVIPAUX_TR_EL; BVIPAUX_TR_REPLICATE;
    BVIPAUX_TR_list_of_seq; PAIR_EQ; small_enough_int_def; nil_tag_def;
    check_exp_eq; has_rec_sing_def; bvi_tailrec_is_rec_def; scan_expr_sing_def;
    from_op_def; op_type_def; arg_ty_def; get_bin_args_def;
    bvi_tailrec_is_const_def; update_context_def; try_update_def;
    index_of_def; check_op_def; opbinargs_def; op_eq_def; try_swap_def;
    apply_op_def; to_op_def; term_ok_def; term_ok_int_def; term_ok_any_def;
    decide_ty_def; LAST1_def; is_arith_def; is_rel_def; push_call_def;
    args_from_def; rewrite_eq; id_from_op_def; let_wrap_def;
    bvi_tailrec_compile_exp_def] cs;
  cs;;

let BVIPAUX_TR_EVAL_CONV = Compute.CBV_CONV BVIPAUX_TR_cs;;

let fac_check_exp = prove
 (`check_exp 0 1
     (bvi_Let [bvi_Op (IntOp LessEq)
                 [bvi_Var 0; bvi_Op (IntOp (clos_Const (&1))) []]]
        (bvi_If (bvi_Var 0)
           (bvi_Op (IntOp (clos_Const (&1))) [])
           (bvi_Let [bvi_Op (IntOp clos_Sub)
                       [bvi_Op (IntOp (clos_Const (&1))) []; bvi_Var 1]]
              (bvi_Op (IntOp Mult)
                 [bvi_Var 2; bvi_Call 0 (SOME 0) [bvi_Var 0] NONE])))) =
   SOME Times`,
  CONV_TAC BVIPAUX_TR_EVAL_CONV);;

let fac_compile_exp = prove
 (`bvi_tailrec_compile_exp 0 1 1
     (bvi_Let [bvi_Op (IntOp LessEq)
                 [bvi_Var 0; bvi_Op (IntOp (clos_Const (&1))) []]]
        (bvi_If (bvi_Var 0)
           (bvi_Op (IntOp (clos_Const (&1))) [])
           (bvi_Let [bvi_Op (IntOp clos_Sub)
                       [bvi_Op (IntOp (clos_Const (&1))) []; bvi_Var 1]]
              (bvi_Op (IntOp Mult)
                 [bvi_Var 2; bvi_Call 0 (SOME 0) [bvi_Var 0] NONE])))) =
   SOME
    (bvi_Let [bvi_Var 0; bvi_Op (IntOp (clos_Const (&1))) []]
       (bvi_Let [bvi_Op (IntOp LessEq)
                   [bvi_Var 0; bvi_Op (IntOp (clos_Const (&1))) []]]
          (bvi_If (bvi_Var 0)
             (bvi_Op (IntOp Mult)
                [bvi_Var 2; bvi_Op (IntOp (clos_Const (&1))) []])
             (bvi_Let [bvi_Op (IntOp clos_Sub)
                         [bvi_Op (IntOp (clos_Const (&1))) []; bvi_Var 1]]
                (bvi_Call 0 (SOME 1)
                   [bvi_Var 0; bvi_Op (IntOp Mult) [bvi_Var 3; bvi_Var 2]]
                   NONE)))),
     bvi_Let [bvi_Op (IntOp LessEq)
                [bvi_Var 0; bvi_Op (IntOp (clos_Const (&1))) []]]
       (bvi_If (bvi_Var 0)
          (bvi_Op (IntOp Mult)
             [bvi_Var 2; bvi_Op (IntOp (clos_Const (&1))) []])
          (bvi_Let [bvi_Op (IntOp clos_Sub)
                      [bvi_Op (IntOp (clos_Const (&1))) []; bvi_Var 1]]
             (bvi_Call 0 (SOME 1)
                [bvi_Var 0; bvi_Op (IntOp Mult) [bvi_Var 3; bvi_Var 2]]
                NONE))))`,
  CONV_TAC BVIPAUX_TR_EVAL_CONV);;

let rev_check_exp = prove
 (`check_exp 444 1
     (bvi_Let [bvi_Op (IntOp (clos_Const (&0))) []]
        (bvi_If (bvi_Op (BlockOp (clos_TagLenEq 0 0)) [bvi_Var 1])
           (bvi_Op (BlockOp (clos_Cons 0)) [])
           (bvi_Let [bvi_Op (MemOp clos_El)
                       [bvi_Op (IntOp (clos_Const (&0))) []; bvi_Var 1]]
              (bvi_Let [bvi_Op (MemOp clos_El)
                          [bvi_Op (IntOp (clos_Const (&1))) []; bvi_Var 2]]
                 (bvi_Op (BlockOp clos_ListAppend)
                    [bvi_Op (BlockOp (clos_Cons 0))
                       [bvi_Op (BlockOp (clos_Cons 0)) []; bvi_Var 1];
                     bvi_Call 0 (SOME 444) [bvi_Var 0] NONE]))))) =
   SOME bvi_tailrec_Append`,
  CONV_TAC BVIPAUX_TR_EVAL_CONV);;

let rev_compile_exp = prove
 (`bvi_tailrec_compile_exp 444 445 1
     (bvi_Let [bvi_Op (IntOp (clos_Const (&0))) []]
        (bvi_If (bvi_Op (BlockOp (clos_TagLenEq 0 0)) [bvi_Var 1])
           (bvi_Op (BlockOp (clos_Cons 0)) [])
           (bvi_Let [bvi_Op (MemOp clos_El)
                       [bvi_Op (IntOp (clos_Const (&0))) []; bvi_Var 1]]
              (bvi_Let [bvi_Op (MemOp clos_El)
                          [bvi_Op (IntOp (clos_Const (&1))) []; bvi_Var 2]]
                 (bvi_Op (BlockOp clos_ListAppend)
                    [bvi_Op (BlockOp (clos_Cons 0))
                       [bvi_Op (BlockOp (clos_Cons 0)) []; bvi_Var 1];
                     bvi_Call 0 (SOME 444) [bvi_Var 0] NONE]))))) =
   SOME
    (bvi_Let [bvi_Var 0; bvi_Op (BlockOp (clos_Cons 0)) []]
       (bvi_Let [bvi_Op (IntOp (clos_Const (&0))) []]
          (bvi_If (bvi_Op (BlockOp (clos_TagLenEq 0 0)) [bvi_Var 1])
             (bvi_Op (BlockOp clos_ListAppend)
                [bvi_Var 2; bvi_Op (BlockOp (clos_Cons 0)) []])
             (bvi_Let [bvi_Op (MemOp clos_El)
                         [bvi_Op (IntOp (clos_Const (&0))) []; bvi_Var 1]]
                (bvi_Let [bvi_Op (MemOp clos_El)
                            [bvi_Op (IntOp (clos_Const (&1))) []; bvi_Var 2]]
                   (bvi_Call 0 (SOME 445)
                      [bvi_Var 0;
                       bvi_Op (BlockOp clos_ListAppend)
                         [bvi_Var 4;
                          bvi_Op (BlockOp (clos_Cons 0))
                            [bvi_Op (BlockOp (clos_Cons 0)) []; bvi_Var 1]]]
                      NONE))))),
     bvi_Let [bvi_Op (IntOp (clos_Const (&0))) []]
       (bvi_If (bvi_Op (BlockOp (clos_TagLenEq 0 0)) [bvi_Var 1])
          (bvi_Op (BlockOp clos_ListAppend)
             [bvi_Var 2; bvi_Op (BlockOp (clos_Cons 0)) []])
          (bvi_Let [bvi_Op (MemOp clos_El)
                      [bvi_Op (IntOp (clos_Const (&0))) []; bvi_Var 1]]
             (bvi_Let [bvi_Op (MemOp clos_El)
                         [bvi_Op (IntOp (clos_Const (&1))) []; bvi_Var 2]]
                (bvi_Call 0 (SOME 445)
                   [bvi_Var 0;
                    bvi_Op (BlockOp clos_ListAppend)
                      [bvi_Var 4;
                       bvi_Op (BlockOp (clos_Cons 0))
                         [bvi_Op (BlockOp (clos_Cons 0)) []; bvi_Var 1]]]
                   NONE)))))`,
  CONV_TAC BVIPAUX_TR_EVAL_CONV);;
