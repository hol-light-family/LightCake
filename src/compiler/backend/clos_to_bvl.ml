(* ========================================================================= *)
(* clos_to_bvl: port of HOL4 compiler/backend/clos_to_bvlScript.sml (CakeML  *)
(* v3479).                                                                   *)
(* This compiler phase performs closure conversion.  This phase puts all of  *)
(* the code into a table of first-order, closed, multi-argument functions   *)
(* (indexed by natural numbers; each entry is the arity and the BVL body).  *)
(* The table: entries 0 .. max_app - 1, generic application of a closure to *)
(* i+1 arguments; then the code to fully apply a partially applied closure  *)
(* wrapper (location max_app + (tot times (tot - 1)) DIV 2 + prev); the code *)
(* that initialises the jump table in a global; the force_thunk stub        *)
(* (num_stubs gives the total number of these); then the expressions; then, *)
(* at even numbers, the bodies of the functions of the program, with one    *)
(* extra argument for the closure value (the odd entries, bodies of         *)
(* functions without free variables, are made by clos_call).                *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 ++ is APPEND (left-associative in HOL4: l1 ++ l2 ++ l3 is          *)
(*   APPEND (APPEND l1 l2) l3); GENLIST is list_of_seq; the bvl overloads   *)
(*   mk_unit = bvl_Op (BlockOp (clos_Cons 0)) [] and                         *)
(*   mk_elem_at b i = bvl_Op (BlockOp (ElemAt i)) [b] are expanded.          *)
(* - HOL4's paired lambdas are written as pair cases (\p. match p with ..).  *)
(* - In the compile functions the names of Fn and clos_Letrec (HOL4 t) are   *)
(*   nm and nms; HOL4 exp3_size is list_size clos_exp_size.                  *)
(* - CLOS2AUX_ names are local proof helpers (some are clos_known.ml's).     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/clos_mti.ml";;
needs "compiler/backend/clos_call.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/clos_number.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/bvl_jump.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/bvl.ml";;

type_invention_error := true;;

(* HOL4: partial_app_tag_neq_closure_tag (an EVAL theorem) *)

let partial_app_tag_neq_closure_tag = prove
 (`~(partial_app_tag = closure_tag)`,
  REWRITE_TAC[partial_app_tag_def; closure_tag_def] THEN ARITH_TAC);;

let clos_tag_shift_nil_tag = prove
 (`clos_tag_shift nil_tag = nil_tag`,
  REWRITE_TAC[clos_tag_shift_def; nil_tag_def] THEN ARITH_TAC);;

let clos_tag_shift_cons_tag = prove
 (`clos_tag_shift cons_tag = cons_tag`,
  REWRITE_TAC[clos_tag_shift_def; cons_tag_def] THEN ARITH_TAC);;

let _ = cake_add_simps [partial_app_tag_neq_closure_tag; clos_tag_shift_nil_tag;
                        clos_tag_shift_cons_tag];;

let clos_tag_shift_inj = prove
 (`!n1 n2. clos_tag_shift n1 = clos_tag_shift n2 ==> n1 = n2`,
  REWRITE_TAC[clos_tag_shift_def] THEN ARITH_TAC);;

(* Constant flattening *)

(* HOL4 local overload PRIME = 999983 (expanded) *)

let part_hash_def = cake_def
  `(part_hash (clos_Int i) = num_of_int (abs i) MOD 999983) /\
   (part_hash (clos_Str s) =
      (strlen s + 3 * SUM (MAP ORD (explode s))) MOD 999983) /\
   (part_hash (clos_W64 w) = (17 + val w) MOD 999983) /\
   (part_hash (clos_Con t ns) = (18 + 5 * t + 7 * SUM ns) MOD 999983)`;;

let add_part_def = cake_def
  `add_part n p (aux:((const_part # num) list) spt) acc =
     let h = part_hash p in
       match lookup h aux with
         NONE -> (n + 1,n,insert h [(p,n)] aux,CONS p acc)
       | SOME bucket ->
           match ALOOKUP bucket p with
             NONE -> (n + 1,n,insert h (CONS (p,n) bucket) aux,CONS p acc)
           | SOME k -> (n,k,aux,acc)`;;

let add_parts_def = cake_def
  `(add_parts (ConstInt i) n (aux:((const_part # num) list) spt) acc =
      add_part n (clos_Int i) aux acc) /\
   (add_parts (ConstStr s) n aux acc = add_part n (clos_Str s) aux acc) /\
   (add_parts (ConstWord64 w) n aux acc = add_part n (clos_W64 w) aux acc) /\
   (add_parts (ConstCons t cs) n aux acc =
      let (n,rs,aux,acc) = add_parts_list cs n aux acc in
        add_part n (clos_Con (clos_tag_shift t) rs) aux acc) /\
   (add_parts_list [] n aux acc = (n,[],aux,acc)) /\
   (add_parts_list (CONS c cs) n aux acc =
      let (n,r,aux,acc) = add_parts c n aux acc in
      let (n,rs,aux,acc) = add_parts_list cs n aux acc in
        (n,CONS r rs,aux,acc))`;;

let compile_const_def = cake_def
  `(compile_const (ConstInt i) = IntOp (clos_Const i)) /\
   (compile_const (ConstStr s) = BlockOp (Build [clos_Str s])) /\
   (compile_const (ConstWord64 w) = BlockOp (Build [clos_W64 w])) /\
   (compile_const (ConstCons t cs) =
      if NULL cs then BlockOp (clos_Cons (clos_tag_shift t)) else
        let (n,rs,aux,acc) = add_parts_list cs 0 LN [] in
          BlockOp (Build (REVERSE (CONS (clos_Con (clos_tag_shift t) rs) acc))))`;;

(* / Constant flattening *)

let num_added_globals_def = cake_def
  `num_added_globals = 1`;;

let partial_app_label_table_loc_def = cake_def
  `partial_app_label_table_loc = 0`;;

(* HOL4: compile_op [simp] *)

let clos_to_bvl_compile_op_def = sem1aux_def
  `(clos_to_bvl_compile_op (BlockOp (clos_Cons tag)) =
      BlockOp (clos_Cons (clos_tag_shift tag))) /\
   (clos_to_bvl_compile_op (BlockOp (ConsExtend tag)) =
      BlockOp (ConsExtend (clos_tag_shift tag))) /\
   (clos_to_bvl_compile_op (BlockOp (TagEq tag)) =
      BlockOp (TagEq (clos_tag_shift tag))) /\
   (clos_to_bvl_compile_op (BlockOp (clos_TagLenEq tag a)) =
      BlockOp (clos_TagLenEq (clos_tag_shift tag) a)) /\
   (clos_to_bvl_compile_op (BlockOp (FromList tag)) =
      BlockOp (FromList (clos_tag_shift tag))) /\
   (clos_to_bvl_compile_op (MemOp LengthByteVec) = MemOp LengthByte) /\
   (clos_to_bvl_compile_op (MemOp DerefByteVec) = MemOp DerefByte) /\
   (clos_to_bvl_compile_op (GlobOp (SetGlobal n)) =
      GlobOp (SetGlobal (n + num_added_globals))) /\
   (clos_to_bvl_compile_op (GlobOp (clos_Global n)) =
      GlobOp (clos_Global (n + num_added_globals))) /\
   (clos_to_bvl_compile_op (BlockOp (Constant c)) = compile_const c) /\
   (clos_to_bvl_compile_op x = x)`;;

let _ = cake_add_simps [clos_to_bvl_compile_op_def];;

(* HOL4: compile_op_pmatch *)

let clos_to_bvl_compile_op_pmatch = prove
 (CASE_TERM
  `!op. clos_to_bvl_compile_op op =
        match op with
          BlockOp (clos_Cons tag) -> BlockOp (clos_Cons (clos_tag_shift tag))
        | BlockOp (ConsExtend tag) -> BlockOp (ConsExtend (clos_tag_shift tag))
        | BlockOp (TagEq tag) -> BlockOp (TagEq (clos_tag_shift tag))
        | BlockOp (clos_TagLenEq tag a) ->
            BlockOp (clos_TagLenEq (clos_tag_shift tag) a)
        | BlockOp (FromList tag) -> BlockOp (FromList (clos_tag_shift tag))
        | MemOp LengthByteVec -> MemOp LengthByte
        | MemOp DerefByteVec -> MemOp DerefByte
        | GlobOp (SetGlobal n) -> GlobOp (SetGlobal (n + num_added_globals))
        | GlobOp (clos_Global n) -> GlobOp (clos_Global (n + num_added_globals))
        | BlockOp (Constant c) -> compile_const c
        | x -> x`,
  GEN_TAC THEN REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[]) THEN
  FS[clos_to_bvl_compile_op_def]);;

let mk_const_def = cake_def
  `mk_const n = bvl_Op (IntOp (clos_Const (&n))) []`;;

let mk_label_def = cake_def
  `mk_label n = bvl_Op (clos_Label n) []`;;

let mk_el_def = cake_def
  `mk_el b i = bvl_Op (MemOp clos_El) [i; b]`;;

let _ = cake_add_simps [mk_const_def; mk_label_def; mk_el_def];;

(* HOL4 mk_elem_at b i (an overload of bvl) is                              *)
(* bvl_Op (BlockOp (ElemAt i)) [b]                                          *)

let free_let_def = cake_def
  `free_let cl n = list_of_seq (\n. bvl_Op (BlockOp (ElemAt (n + 2))) [cl]) n`;;

let code_for_recc_case_def = cake_def
  `code_for_recc_case n num_args (c:bvl_exp) =
     (num_args + 1,
      bvl_Let [bvl_Op (BlockOp (ElemAt 2)) [bvl_Var num_args]]
        (bvl_Let (APPEND (list_of_seq (\a. bvl_Var (a + 1)) num_args)
                         (list_of_seq (\i. bvl_Op (BlockOp (ElemAt i)) [bvl_Var 0]) n))
                 c))`;;

let build_aux_def = cake_def
  `(build_aux i [] aux = (i:num,aux)) /\
   (build_aux i (CONS (x:num#bvl_exp) xs) aux =
      build_aux (i + 2) xs (CONS (i,x) aux))`;;

let build_aux_LENGTH = prove
 (`!l n aux n1 t.
     build_aux n l aux = (n1,t) ==> n1 = n + 2 * LENGTH l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[build_aux_def; PAIR_EQ; LENGTH] THENL
   [ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_ARITH_TAC);;

let CLOS2AUX_APPEND_SNOC_CONS = prove
 (`!a (y:A) z. APPEND (APPEND a [y]) z = APPEND a (CONS y z)`,
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

let build_aux_MOVE = prove
 (`!xs n aux n1 aux1.
     build_aux n xs aux = (n1,aux1) <=>
     ?aux2. build_aux n xs [] = (n1,aux2) /\ aux1 = APPEND aux2 aux`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[build_aux_def; PAIR_EQ] THEN MESON_TAC[APPEND];
    ONCE_REWRITE_TAC[build_aux_def] THEN
    FIRST_X_ASSUM(fun th -> ONCE_REWRITE_TAC[th]) THEN
    MESON_TAC[CLOS2AUX_APPEND_SNOC_CONS]]);;

let build_aux_acc = prove
 (`!k n aux. ?aux1. SND (build_aux n k aux) = APPEND aux1 aux`,
  MESON_TAC[build_aux_MOVE; SND; PAIR]);;

let build_aux_MEM = prove
 (`!c n aux n7 aux7.
     build_aux n c aux = (n7,aux7) ==>
     !k. k < LENGTH c ==> ?d. MEM (n + 2 * k,d) aux7`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[build_aux_def; LENGTH; CONJUNCT1 LT] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [DISCH_THEN(K ALL_TAC) THEN
    MP_TAC(ISPECL [`t:(num#bvl_exp)list`; `n + 2`;
                   `CONS (n:num,h:num#bvl_exp) (aux:(num#num#bvl_exp)list)`]
                  build_aux_acc) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `h:num#bvl_exp` THEN
    REWRITE_TAC[MEM_APPEND; MEM; ARITH_RULE `n + 2 * 0 = n`];
    REWRITE_TAC[LT_SUC] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n + 2`;
                   `CONS (n:num,h:num#bvl_exp) (aux:(num#num#bvl_exp)list)`;
                                  `n7:num`; `aux7:(num#num#bvl_exp)list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[ARITH_RULE `n + 2 * SUC k = (n + 2) + 2 * k`]]);;

let build_aux_APPEND1 = prove
 (CASE_TERM
  `!xs (x:num#bvl_exp) n aux.
     build_aux n (APPEND xs [x]) aux =
       let (n1,aux1) = build_aux n xs aux in
         (n1 + 2,CONS (n1,x) aux1)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[build_aux_def; APPEND; pair_CASE]);;

let recc_Let_def = cake_def
  `recc_Let n num_args i =
     bvl_Let [bvl_Op (BlockOp (ElemAt 2)) [bvl_Var 0]]
       (bvl_Let [bvl_Op (BlockOp (clos_Cons closure_tag))
                   [bvl_Var 0; mk_const (num_args - 1); mk_label n]]
          (bvl_Let [bvl_Op (MemOp Update) [bvl_Var 0; mk_const i; bvl_Var 1]]
             (bvl_Var 1)))`;;

let recc_Lets_def = cake_def_wf
  `measure (\p:num#num list#num#bvl_exp. FST (SND (SND p)))`
  TERM_TAC
  `recc_Lets n nargs k rest =
     if k = 0 then rest else
       let k = k - 1 in
         bvl_Let [recc_Let (n + 2 * k) (HD nargs) k]
                 (recc_Lets n (TL nargs) k rest)`;;

let recc_Lets_ind = cake_ind "recc_Lets";;

let recc_Let0_def = cake_def
  `recc_Let0 n num_args i =
     bvl_Let [bvl_Op (BlockOp (clos_Cons closure_tag))
                [bvl_Var 0; mk_const (num_args - 1); mk_label n]]
       (bvl_Let [bvl_Op (MemOp Update) [bvl_Var 0; mk_const i; bvl_Var 1]]
          (bvl_Var 1))`;;

let build_recc_lets_def = cake_def
  `build_recc_lets (nargs:num list) vs n1 fns_l (c3:bvl_exp) =
     bvl_Let [bvl_Let [bvl_Op (MemOp clos_Ref)
                         (REVERSE (APPEND (MAP (K (mk_const 0)) nargs)
                                          (MAP bvl_Var vs)))]
                (recc_Let0 (n1 + 2 * (fns_l - 1)) (HD (REVERSE nargs))
                           (fns_l - 1))]
       (recc_Lets n1 (TL (REVERSE nargs)) (fns_l - 1) c3)`;;

let num_stubs_def = cake_def
  `num_stubs max_app =
     max_app + (max_app * (max_app - 1)) DIV 2 + 1 + 1`;;

let generic_app_fn_location_def = cake_def
  `generic_app_fn_location n = n:num`;;

let partial_app_fn_location_def = cake_def
  `partial_app_fn_location (max_app:num) tot prev =
     max_app + (tot * (tot - 1)) DIV 2 + prev`;;

let partial_app_fn_location_code_def = cake_def
  `partial_app_fn_location_code (max_app:num) tot_exp prev_exp =
     bvl_Let [tot_exp]
       (bvl_Op (IntOp clos_Add)
          [prev_exp;
           bvl_Op (IntOp clos_Div)
             [mk_const 2;
              bvl_Op (IntOp Mult)
                [bvl_Var 0; bvl_Op (IntOp clos_Sub) [mk_const 1; bvl_Var 0]]]])`;;

let mk_cl_call_def = cake_def
  `mk_cl_call cl args =
     bvl_If (bvl_Op (BlockOp (EqualConst (clos_Int (&(LENGTH args - 1)))))
               [bvl_Op (BlockOp (ElemAt 1)) [cl]])
       (bvl_Call (LENGTH args - 1) NONE
          (APPEND (APPEND args [cl]) [bvl_Op (BlockOp (ElemAt 0)) [cl]]))
       (bvl_Call 0 (SOME (generic_app_fn_location (LENGTH args - 1)))
          (APPEND args [cl]))`;;

(* Generic application of a function to n+1 arguments *)

let generate_generic_app_def = cake_def
  `generate_generic_app max_app n =
     bvl_Let [bvl_Op (IntOp clos_Sub)
                [mk_const (n + 1); bvl_Op (BlockOp (ElemAt 1)) [bvl_Var (n + 1)]]]
       (bvl_If (bvl_Op (IntOp clos_Less) [mk_const 0; bvl_Var 0])
          (bvl_jump_Jump (bvl_Op (BlockOp (ElemAt 1)) [bvl_Var (n + 2)])
             (list_of_seq (\num_args.
                bvl_Let [bvl_Call num_args NONE
                           (APPEND
                              (APPEND
                                 (list_of_seq
                                    (\arg. bvl_Var (((arg + 2) + n) - num_args))
                                    (num_args + 1))
                                 [bvl_Var (n + 3)])
                              [bvl_Op (BlockOp (ElemAt 0)) [bvl_Var (n + 3)]])]
                  (mk_cl_call (bvl_Var 0)
                     (list_of_seq (\n. bvl_Var (n + 3)) (n - num_args))))
                max_app))
          (mk_tick n
             (bvl_If (bvl_Op (BlockOp (TagEq closure_tag)) [bvl_Var (n + 2)])
                (bvl_Op (BlockOp (clos_Cons partial_app_tag))
                   (REVERSE
                      (CONS (mk_el (bvl_Op (GlobOp (clos_Global 0)) [])
                               (partial_app_fn_location_code max_app
                                  (bvl_Op (BlockOp (ElemAt 1)) [bvl_Var (n + 2)])
                                  (mk_const n)))
                       (CONS (bvl_Var 0)
                       (CONS (bvl_Var (n + 2))
                          (list_of_seq (\n. bvl_Var (n + 1)) (n + 1)))))))
                (bvl_Let [bvl_Op (IntOp clos_Sub)
                            [mk_const 3;
                             bvl_Op (BlockOp LengthBlock) [bvl_Var (n + 2)]]]
                   (bvl_Op (BlockOp (ConsExtend partial_app_tag))
                      (REVERSE
                         (CONS (bvl_Var (n + 3))
                         (CONS (mk_const 3)
                         (CONS (bvl_Var 0)
                         (CONS (bvl_Op (IntOp clos_Add) [bvl_Var 0; mk_const (n + 4)])
                         (CONS (mk_el (bvl_Op (GlobOp (clos_Global 0)) [])
                                  (partial_app_fn_location_code max_app
                                     (bvl_Op (IntOp clos_Add)
                                        [bvl_Var 0;
                                         bvl_Op (IntOp clos_Add)
                                           [mk_const (n + 1); bvl_Var 1]])
                                     (bvl_Op (IntOp clos_Add)
                                        [bvl_Var 1; mk_const n])))
                         (CONS (bvl_Var 1)
                         (CONS (bvl_Op (BlockOp (ElemAt 2)) [bvl_Var (n + 3)])
                            (list_of_seq (\this_arg. bvl_Var (this_arg + 2))
                                         (n + 1)))))))))))))))`;;

(* The functions to complete the application of a partial closure.  We   *)
(* expect prev_args < total_args, also the function should take one more   *)
(* argument than total, and have seen one more than prev (since there is   *)
(* possiblity for a 0 argument function, or a partial application wrapper  *)
(* that has seen no arguments yet.                                          *)

let generate_partial_app_closure_fn_def = cake_def
  `generate_partial_app_closure_fn total_args prev_args =
     bvl_Let [bvl_Op (BlockOp (ElemAt 2)) [bvl_Var (total_args - prev_args)]]
       (bvl_Call 0 NONE
          (APPEND
            (APPEND
              (APPEND (list_of_seq (\this_arg. bvl_Var (this_arg + 1))
                                   (total_args - prev_args))
                      (list_of_seq (\prev_arg.
                          bvl_Op (BlockOp (ElemAt (prev_arg + 3)))
                            [bvl_Var (total_args - prev_args + 1)])
                         (prev_args + 1)))
              [bvl_Var 0])
            [bvl_Op (BlockOp (ElemAt 0)) [bvl_Var 0]]))`;;

let check_closure_def = cake_def
  `check_closure v e =
     bvl_If (bvl_Op (BlockOp (TagEq closure_tag)) [bvl_Var v]) (bvl_Bool T)
       (bvl_If (bvl_Op (BlockOp (TagEq partial_app_tag)) [bvl_Var v])
          (bvl_Bool T) e)`;;

let clos_to_bvl_init_code_def = cake_def
  `clos_to_bvl_init_code max_app =
     fromList
       (APPEND
          (list_of_seq (\n. (n + 2,generate_generic_app max_app n)) max_app)
          (FLAT
             (list_of_seq
                (\tot. list_of_seq
                         (\prev. (tot - prev + 1,
                                  generate_partial_app_closure_fn tot prev))
                         tot)
                max_app)))`;;

let init_globals_def = cake_def
  `init_globals max_app start_loc =
     bvl_Let [bvl_Op (GlobOp AllocGlobal) [bvl_Op (IntOp (clos_Const (&1))) []]]
       (bvl_Let
          [bvl_Op (GlobOp (SetGlobal partial_app_label_table_loc))
             [bvl_Op (BlockOp (clos_Cons tuple_tag))
                (REVERSE (FLAT
                   (list_of_seq
                      (\tot. list_of_seq
                               (\prev. mk_label
                                         (partial_app_fn_location max_app tot prev))
                               tot)
                      max_app)))]]
          (bvl_Call 0 (SOME start_loc) []))`;;

(* HOL4 mk_unit (an overload of bvl) is bvl_Op (BlockOp (clos_Cons 0)) [] *)

let force_thunk_code_def = cake_def
  `force_thunk_code =
     bvl_If (bvl_Op (BlockOp (EqualConst (clos_Int (&0))))
               [bvl_Op (BlockOp (ElemAt 1)) [bvl_Var 1]])
       (bvl_Let [bvl_Call 0 NONE
                   [bvl_Op (BlockOp (clos_Cons 0)) []; bvl_Var 1;
                    bvl_Op (BlockOp (ElemAt 0)) [bvl_Var 1]]]
          (bvl_Let [bvl_Op (clos_ThunkOp (UpdateThunk Evaluated))
                      [bvl_Var 0; bvl_Var 1]]
             (bvl_Var 1)))
       (bvl_Let [bvl_Call 0 (SOME 0) [bvl_Op (BlockOp (clos_Cons 0)) []; bvl_Var 1]]
          (bvl_Let [bvl_Op (clos_ThunkOp (UpdateThunk Evaluated))
                      [bvl_Var 0; bvl_Var 1]]
             (bvl_Var 1)))`;;

(* proof helpers of this file *)

(* HOL4 rfs/metis steps that instantiate a universally quantified          *)
(* assumption: find an assumption !v1 .. vn. P and an equation assumption   *)
(* l = r such that a subterm of P becomes l for an instance of v1 .. vn     *)
(* that determines all of them; replace the assumption by that instance    *)

let CLOS2AUX_INST_TAC : tactic = fun (asl,w as g) ->
  let eqs = filter (fun (_,th) -> is_eq (concl th)) asl in
  let try_all ath =
    let vs,body = strip_forall (concl ath) in
    if vs = [] then failwith "CLOS2AUX_INST_TAC" else
    tryfind (fun (_,eth) ->
      let l = lhs(concl eth) in
      let ok t = try let fixed = subtract (frees t) vs in
                     let _,tmin,tyin = term_match fixed t l in
                     tyin = [] &&
                     forall (fun v -> exists (fun (_,x) -> x = v) tmin) vs
                 with Failure _ -> false in
      let t = find_term ok body in
      let fixed = subtract (frees t) vs in
      let _,tmin,_ = term_match fixed t l in
      let insts = map (fun v -> rev_assoc v tmin) vs in
      UNDISCH_THEN (concl ath) (fun th -> ASSUME_TAC (SPECL insts th))) eqs in
  tryfind (fun (_,th) -> try_all th) asl g;;



(* HOL4: compile_exps; in Fn and Letrec the names (HOL4 t) are nm and nms *)

let clos_to_bvl_compile_exps_def = sem1aux_def_wf
  `measure (\p:num#clos_exp list#(num#num#bvl_exp) list.
              list_size clos_exp_size (FST (SND p)))`
  CLOS2AUX_SIZE_TC_TAC
  `(clos_to_bvl_compile_exps max_app [] aux = ([],aux)) /\
   (clos_to_bvl_compile_exps max_app (CONS (x:clos_exp) (CONS y xs)) aux =
      let (c1,aux1) = clos_to_bvl_compile_exps max_app [x] aux in
      let (c2,aux2) = clos_to_bvl_compile_exps max_app (CONS y xs) aux1 in
        (APPEND c1 c2,aux2)) /\
   (clos_to_bvl_compile_exps max_app [clos_Var t v] aux = ([bvl_Var v],aux)) /\
   (clos_to_bvl_compile_exps max_app [clos_If t x1 x2 x3] aux =
      let (c1,aux1) = clos_to_bvl_compile_exps max_app [x1] aux in
      let (c2,aux2) = clos_to_bvl_compile_exps max_app [x2] aux1 in
      let (c3,aux3) = clos_to_bvl_compile_exps max_app [x3] aux2 in
        ([bvl_If (HD c1) (HD c2) (HD c3)],aux3)) /\
   (clos_to_bvl_compile_exps max_app [clos_Let t xs x2] aux =
      let (c1,aux1) = clos_to_bvl_compile_exps max_app xs aux in
      let (c2,aux2) = clos_to_bvl_compile_exps max_app [x2] aux1 in
        ([bvl_Let c1 (HD c2)],aux2)) /\
   (clos_to_bvl_compile_exps max_app [clos_Raise t x1] aux =
      let (c1,aux1) = clos_to_bvl_compile_exps max_app [x1] aux in
        ([bvl_Raise (HD c1)],aux1)) /\
   (clos_to_bvl_compile_exps max_app [clos_Tick t x1] aux =
      let (c1,aux1) = clos_to_bvl_compile_exps max_app [x1] aux in
        ([bvl_Tick (HD c1)],aux1)) /\
   (clos_to_bvl_compile_exps max_app [clos_Op t op xs] aux =
      let (c1,aux1) = clos_to_bvl_compile_exps max_app xs aux in
        ([if op = clos_Install then
            bvl_Call 0 NONE [bvl_Op clos_Install c1]
          else if op = clos_ThunkOp ForceThunk then
            bvl_Let c1 (bvl_Force (num_stubs max_app - 2) 0)
          else
            bvl_Op (clos_to_bvl_compile_op op) c1],
         aux1)) /\
   (clos_to_bvl_compile_exps max_app [clos_App t loc_opt x1 xs2] aux =
      let (c1,aux1) = clos_to_bvl_compile_exps max_app [x1] aux in
      let (c2,aux2) = clos_to_bvl_compile_exps max_app xs2 aux1 in
        ([match loc_opt with
            NONE ->
              bvl_Let (APPEND c2 c1)
                (mk_cl_call (bvl_Var (LENGTH c2)) (list_of_seq bvl_Var (LENGTH c2)))
          | SOME loc ->
              bvl_Call (LENGTH c2 - 1) (SOME (loc + num_stubs max_app))
                (APPEND c2 c1)],
         aux2)) /\
   (clos_to_bvl_compile_exps max_app [Fn nm loc_opt vs_opt num_args x1] aux =
      let loc = (match loc_opt with NONE -> 0 | SOME n -> n) in
      let vs = (match vs_opt with NONE -> [] | SOME vs -> vs) in
      let (c1,aux1) = clos_to_bvl_compile_exps max_app [x1] aux in
      let c2 =
        bvl_Let (APPEND (list_of_seq bvl_Var num_args)
                        (free_let (bvl_Var num_args) (LENGTH vs)))
                (HD c1) in
        ([bvl_Op (BlockOp (clos_Cons closure_tag))
            (REVERSE (CONS (mk_label (loc + num_stubs max_app))
                       (CONS (mk_const (num_args - 1)) (MAP bvl_Var vs))))],
         CONS (loc + num_stubs max_app,num_args + 1,c2) aux1)) /\
   (clos_to_bvl_compile_exps max_app [clos_Letrec nms loc_opt vsopt fns x1] aux =
      let loc = (match loc_opt with NONE -> 0 | SOME n -> n) in
      let vs = (match vsopt with NONE -> [] | SOME x -> x) in
      match fns with
        [] -> clos_to_bvl_compile_exps max_app [x1] aux
      | [(num_args,exp)] ->
          let (c1,aux1) = clos_to_bvl_compile_exps max_app [exp] aux in
          let c3 =
            bvl_Let (APPEND (APPEND (list_of_seq bvl_Var num_args)
                                    [bvl_Var num_args])
                            (free_let (bvl_Var num_args) (LENGTH vs)))
                    (HD c1) in
          let (c2,aux2) =
            clos_to_bvl_compile_exps max_app [x1]
              (CONS (loc + num_stubs max_app,num_args + 1,c3) aux1) in
          let c4 =
            bvl_Op (BlockOp (clos_Cons closure_tag))
              (REVERSE (CONS (mk_label (loc + num_stubs max_app))
                         (CONS (mk_const (num_args - 1)) (MAP bvl_Var vs)))) in
            ([bvl_Let [c4] (HD c2)],aux2)
      | _ ->
          let fns_l = LENGTH fns in
          let l = fns_l + LENGTH vs in
          let (cs,aux1) = clos_to_bvl_compile_exps max_app (MAP SND fns) aux in
          let cs1 = MAP2 (code_for_recc_case l) (MAP FST fns) cs in
          let (n2,aux2) = build_aux (loc + num_stubs max_app) cs1 aux1 in
          let (c3,aux3) = clos_to_bvl_compile_exps max_app [x1] aux2 in
          let c4 = build_recc_lets (MAP FST fns) vs (loc + num_stubs max_app)
                                   fns_l (HD c3) in
            ([c4],aux3)) /\
   (clos_to_bvl_compile_exps max_app [clos_Handle t x1 x2] aux =
      let (c1,aux1) = clos_to_bvl_compile_exps max_app [x1] aux in
      let (c2,aux2) = clos_to_bvl_compile_exps max_app [x2] aux1 in
        ([bvl_Handle (HD c1) (HD c2)],aux2)) /\
   (clos_to_bvl_compile_exps max_app [clos_Call t ticks dest xs] aux =
      let (c1,aux1) = clos_to_bvl_compile_exps max_app xs aux in
        ([bvl_Call ticks (SOME (dest + num_stubs max_app)) c1],aux1))`;;

let clos_to_bvl_compile_exps_ind = cake_ind "clos_to_bvl_compile_exps";;

(* HOL4: compile_exp_sing, compile_exp_list *)

let compile_exp_sing_def = sem1aux_def_wf
  `measure (\x:num#clos_exp#(num#num#bvl_exp) list +
               num#clos_exp list#(num#num#bvl_exp) list.
              sum_CASE x (\p. clos_exp_size (FST (SND p)))
                         (\p. list_size clos_exp_size (FST (SND p))))`
  CLOS2AUX_SIZE_TC_TAC
  `(compile_exp_sing max_app (clos_Var t v) aux = (bvl_Var v,aux)) /\
   (compile_exp_sing max_app (clos_If t x1 x2 x3) aux =
      let (c1,aux1) = compile_exp_sing max_app x1 aux in
      let (c2,aux2) = compile_exp_sing max_app x2 aux1 in
      let (c3,aux3) = compile_exp_sing max_app x3 aux2 in
        (bvl_If c1 c2 c3,aux3)) /\
   (compile_exp_sing max_app (clos_Let t xs x2) aux =
      let (c1,aux1) = compile_exp_list max_app xs aux in
      let (c2,aux2) = compile_exp_sing max_app x2 aux1 in
        (bvl_Let c1 c2,aux2)) /\
   (compile_exp_sing max_app (clos_Raise t x1) aux =
      let (c1,aux1) = compile_exp_sing max_app x1 aux in
        (bvl_Raise c1,aux1)) /\
   (compile_exp_sing max_app (clos_Tick t x1) aux =
      let (c1,aux1) = compile_exp_sing max_app x1 aux in
        (bvl_Tick c1,aux1)) /\
   (compile_exp_sing max_app (clos_Op t op xs) aux =
      let (c1,aux1) = compile_exp_list max_app xs aux in
        ((if op = clos_Install then bvl_Call 0 NONE [bvl_Op clos_Install c1]
          else if op = clos_ThunkOp ForceThunk then
            bvl_Let c1 (bvl_Force (num_stubs max_app - 2) 0)
          else bvl_Op (clos_to_bvl_compile_op op) c1),
         aux1)) /\
   (compile_exp_sing max_app (clos_App t loc_opt x1 xs2) aux =
      let (c1,aux1) = compile_exp_sing max_app x1 aux in
      let (c2,aux2) = compile_exp_list max_app xs2 aux1 in
        ((match loc_opt with
            NONE ->
              bvl_Let (APPEND c2 [c1])
                (mk_cl_call (bvl_Var (LENGTH c2)) (list_of_seq bvl_Var (LENGTH c2)))
          | SOME loc ->
              bvl_Call (LENGTH c2 - 1) (SOME (loc + num_stubs max_app))
                (APPEND c2 [c1])),
         aux2)) /\
   (compile_exp_sing max_app (Fn nm loc_opt vs_opt num_args x1) aux =
      let loc = (match loc_opt with NONE -> 0 | SOME n -> n) in
      let vs = (match vs_opt with NONE -> [] | SOME vs -> vs) in
      let (c1,aux1) = compile_exp_sing max_app x1 aux in
      let c2 =
        bvl_Let (APPEND (list_of_seq bvl_Var num_args)
                        (free_let (bvl_Var num_args) (LENGTH vs)))
                c1 in
        (bvl_Op (BlockOp (clos_Cons closure_tag))
           (REVERSE (CONS (mk_label (loc + num_stubs max_app))
                      (CONS (mk_const (num_args - 1)) (MAP bvl_Var vs)))),
         CONS (loc + num_stubs max_app,num_args + 1,c2) aux1)) /\
   (compile_exp_sing max_app (clos_Letrec nms loc_opt vsopt fns x1) aux =
      let loc = (match loc_opt with NONE -> 0 | SOME n -> n) in
      let vs = (match vsopt with NONE -> [] | SOME x -> x) in
      match fns with
        [] -> compile_exp_sing max_app x1 aux
      | [(num_args,exp)] ->
          let (c1,aux1) = compile_exp_sing max_app exp aux in
          let c3 =
            bvl_Let (APPEND (APPEND (list_of_seq bvl_Var num_args)
                                    [bvl_Var num_args])
                            (free_let (bvl_Var num_args) (LENGTH vs)))
                    c1 in
          let (c2,aux2) =
            compile_exp_sing max_app x1
              (CONS (loc + num_stubs max_app,num_args + 1,c3) aux1) in
          let c4 =
            bvl_Op (BlockOp (clos_Cons closure_tag))
              (REVERSE (CONS (mk_label (loc + num_stubs max_app))
                         (CONS (mk_const (num_args - 1)) (MAP bvl_Var vs)))) in
            (bvl_Let [c4] c2,aux2)
      | _ ->
          let fns_l = LENGTH fns in
          let l = fns_l + LENGTH vs in
          let (cs,aux1) = compile_exp_list max_app (MAP SND fns) aux in
          let cs1 = MAP2 (code_for_recc_case l) (MAP FST fns) cs in
          let (n2,aux2) = build_aux (loc + num_stubs max_app) cs1 aux1 in
          let (c3,aux3) = compile_exp_sing max_app x1 aux2 in
          let c4 = build_recc_lets (MAP FST fns) vs (loc + num_stubs max_app)
                                   fns_l c3 in
            (c4,aux3)) /\
   (compile_exp_sing max_app (clos_Handle t x1 x2) aux =
      let (c1,aux1) = compile_exp_sing max_app x1 aux in
      let (c2,aux2) = compile_exp_sing max_app x2 aux1 in
        (bvl_Handle c1 c2,aux2)) /\
   (compile_exp_sing max_app (clos_Call t ticks dest xs) aux =
      let (c1,aux1) = compile_exp_list max_app xs aux in
        (bvl_Call ticks (SOME (dest + num_stubs max_app)) c1,aux1)) /\
   (compile_exp_list max_app [] aux = ([],aux)) /\
   (compile_exp_list max_app (CONS (x:clos_exp) xs) aux =
      let (c1,aux1) = compile_exp_sing max_app x aux in
      let (c2,aux2) = compile_exp_list max_app xs aux1 in
        (CONS c1 c2,aux2))`;;

let compile_exp_sing_ind = cake_ind "compile_exp_sing";;

(* HOL4: compile_exp_sing_eq; HOL4's paired lambda (\(a,b). ([a],b)) is a *)
(* pair case                                                               *)

let compile_exp_sing_eq = prove
 (CASE_TERM
  `(!n e l. clos_to_bvl_compile_exps n [e] l =
            (\p. match p with (a,b) -> ([a],b)) (compile_exp_sing n e l)) /\
   (!n es l. clos_to_bvl_compile_exps n es l = compile_exp_list n es l)`,
  let defs = [clos_to_bvl_compile_exps_def; compile_exp_sing_def] in
  let letrec_tac =
    CASES_ON `fns:(num#clos_exp)list` THEN REWRITE_TAC defs THEN GVS[] THEN
    CASES_ON `a0:num#clos_exp` THEN CASES_ON `a1:(num#clos_exp)list` THEN
    GVS[] THENL
     [REPEAT (PAIRARG_TAC THEN GVS[]);
      PAIRARG_TAC THEN FS[] THEN PAIRARG_TAC THEN
      FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(fun ba -> MP_TAC(MATCH_MP ih ba))) THEN
      DISCH_TAC THEN PAIRARG_TAC THEN FS[] THEN PAIRARG_TAC THEN FS[] THEN
      PAIRARG_TAC THEN FS[]] in
  let other_tac =
    REWRITE_TAC defs THEN GVS[] THEN REPEAT (PAIRARG_TAC THEN GVS[]) THEN
    CASES_ON `xs:clos_exp list` THEN FS[clos_to_bvl_compile_exps_def; APPEND] in
  MATCH_MP_TAC compile_exp_sing_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  (fun g -> if CLOS2AUX_CONST_IN "clos_Letrec" (snd g) then letrec_tac g
            else other_tac g));;

(* HOL4: compile_prog *)

let clos_to_bvl_compile_prog_def = cake_def
  `clos_to_bvl_compile_prog max_app (prog:(num#num#clos_exp) list) =
     let (new_exps,aux) =
       clos_to_bvl_compile_exps max_app (MAP (SND o SND) prog) [] in
       APPEND (MAP2 (\p (exp:bvl_exp). match p with
                        (loc,args,_) -> (loc + num_stubs max_app,args,exp))
                    prog new_exps)
              aux`;;

(* HOL4: compile_prog_eq *)

let clos_to_bvl_compile_prog_eq = prove
 (CASE_TERM
  `!max_app (prog:(num#num#clos_exp) list).
     clos_to_bvl_compile_prog max_app prog =
     let (new_exps,aux) =
       compile_exp_list max_app (MAP (SND o SND) prog) [] in
       APPEND (MAP2 (\p (exp:bvl_exp). match p with
                        (loc,args,_) -> (loc + num_stubs max_app,args,exp))
                    prog new_exps)
              aux`,
  REWRITE_TAC[clos_to_bvl_compile_prog_def; compile_exp_sing_eq]);;

(* HOL4: pair_lem1 [local], with HOL4's paired lambda as a pair case *)

let pair_lem1 = prove
 (CASE_TERM
  `!(f:A->B->C) x. (\p. match p with (a,b) -> f a b) x = f (FST x) (SND x)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; FST; SND]);;

(* HOL4: pair_lem2 [local] *)

let pair_lem2 = prove
 (`!(x:A) (y:B) z. (x,y) = z <=> x = FST z /\ y = SND z`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; FST; SND]);;

let CLOS2AUX_BUILD_AUX_APPEND = prove
 (`!n xs aux n1 aux1.
     build_aux n xs aux = (n1,aux1) ==> ?ys. aux1 = APPEND ys aux`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[build_aux_MOVE] THEN MESON_TAC[]);;

let compile_exps_acc = prove
 (CASE_TERM
  `!max_app xs aux.
     let (c,aux1) = clos_to_bvl_compile_exps max_app xs aux in
       LENGTH c = LENGTH (xs:clos_exp list) /\ ?ys. aux1 = APPEND ys aux`,
  let other_tac =
    REWRITE_TAC[clos_to_bvl_compile_exps_def] THEN GVS[] THEN
    REPEAT (PAIRARG_TAC THEN GVS[]) THEN
    TRY ARITH_TAC THEN TRY (MESON_TAC[APPEND; APPEND_ASSOC]) in
  let letrec_tac =
    CASES_ON `fns:(num#clos_exp)list` THEN
    REWRITE_TAC[clos_to_bvl_compile_exps_def] THEN GVS[] THEN
    CASES_ON `a0:num#clos_exp` THEN CASES_ON `a1:(num#clos_exp)list` THEN
    GVS[] THENL
     [REPEAT (PAIRARG_TAC THEN GVS[]) THEN CLOS2AUX_INST_TAC THEN GVS[] THEN
      MESON_TAC[APPEND; APPEND_ASSOC];
      CLOS2AUX_SPLIT_PAIR_TAC THEN FS[] THEN RVEQ_TAC THEN CLOS2AUX_SPLIT_PAIR_TAC THEN
      FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(fun ba -> MP_TAC(MATCH_MP ih ba))) THEN
      DISCH_TAC THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOS2AUX_BUILD_AUX_APPEND) THEN
      CLOS2AUX_SPLIT_PAIR_TAC THEN
      REWRITE_TAC[LENGTH; ONE] THEN ASM_MESON_TAC[APPEND; APPEND_ASSOC]] in
  MATCH_MP_TAC clos_to_bvl_compile_exps_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN
  (fun g -> if CLOS2AUX_CONST_IN "clos_Letrec" (snd g) then letrec_tac g
            else other_tac g));;

let clos_to_bvl_compile_exps_LENGTH = prove
 (`!max_app xs aux c aux1.
     clos_to_bvl_compile_exps max_app xs aux = (c,aux1)
     ==> LENGTH c = LENGTH (xs:clos_exp list)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`max_app:num`; `xs:clos_exp list`;
                `aux:(num#num#bvl_exp)list`] compile_exps_acc) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN SIMP_TAC[]);;

let clos_to_bvl_compile_exps_SING = prove
 (`!max_app x aux c aux1.
     clos_to_bvl_compile_exps max_app [x] aux = (c,aux1) ==> ?d. c = [d]`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP clos_to_bvl_compile_exps_LENGTH) THEN
  STRUCT_CASES_TAC(ISPEC `c:bvl_exp list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; LENGTH_EQ_NIL; CONS_11] THEN
  MESON_TAC[]);;

let compile_exps_CONS = prove
 (CASE_TERM
  `!max_app xs x aux.
     clos_to_bvl_compile_exps max_app (CONS x xs) aux =
     let (c1,aux1) = clos_to_bvl_compile_exps max_app [x] aux in
     let (c2,aux2) = clos_to_bvl_compile_exps max_app xs aux1 in
       (APPEND c1 c2,aux2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[clos_to_bvl_compile_exps_def] THEN REPEAT GEN_TAC THEN
  CLOS2AUX_SPLIT_PAIR_TAC THEN REWRITE_TAC[pair_CASE; APPEND_NIL]);;

let compile_exps_SNOC = prove
 (CASE_TERM
  `!xs (x:clos_exp) aux max_app.
     clos_to_bvl_compile_exps max_app (SNOC x xs) aux =
     let (c1,aux1) = clos_to_bvl_compile_exps max_app xs aux in
     let (c2,aux2) = clos_to_bvl_compile_exps max_app [x] aux1 in
       (APPEND c1 c2,aux2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC] THENL
   [REWRITE_TAC[clos_to_bvl_compile_exps_def; pair_CASE; APPEND] THEN
    REPEAT GEN_TAC THEN CLOS2AUX_SPLIT_PAIR_TAC THEN REWRITE_TAC[pair_CASE];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [compile_exps_CONS] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [compile_exps_CONS] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_to_bvl_compile_exps_def; pair_CASE] THEN
  REPEAT (CLOS2AUX_SPLIT_PAIR_TAC THEN ASM_REWRITE_TAC[pair_CASE]) THEN
  REWRITE_TAC[APPEND_ASSOC; APPEND_NIL]);;

(* HOL4: Datatype config *)

let clos_to_bvl_config_INFO = cake_record "clos_to_bvl_config"
  ["next_loc","num";
   "start","num";
   "do_mti","bool";
   "known_conf","clos_known_config option";
   "do_call","bool";
   "call_state","num_set # (num # num # clos_exp) list";
   "max_app","num"];;

let clos_to_bvl_default_config_def = cake_def
  `clos_to_bvl_default_config =
     clos_to_bvl_config_REC 0 1 T (SOME (clos_known_default_config 10)) T
       (LN,[]) 10`;;

let code_split_def = cake_def
  `(code_split [] xs ys = (xs,ys)) /\
   (code_split (CONS (z:A) zs) xs ys = code_split zs (CONS z ys) xs)`;;

let code_merge_def = cake_def_wf
  `measure (\p:(num#A) list # (num#A) list. LENGTH (FST p) + LENGTH (SND p))`
  (REWRITE_TAC[measure_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC)
  `code_merge (xs:(num#A) list) ys =
     match (xs,ys) with
       ([],[]) -> []
     | ([],_) -> ys
     | (_,[]) -> xs
     | (CONS x1 xs1,CONS y1 ys1) ->
         if FST x1 < FST y1 then CONS x1 (code_merge xs1 ys)
         else CONS y1 (code_merge xs ys1)`;;

let code_merge_ind = cake_ind "code_merge";;

let code_split_NULL = prove
 (`!ts1 ts2 ts3 xs ys.
     (xs,ys) = code_split ts1 ts2 (ts3:A list) /\ ~(ts2 = []) /\ ~(ts3 = [])
     ==> ~(xs = []) /\ ~(ys = [])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[code_split_def; PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
    [`CONS (h:A) ts3`; `ts2:A list`; `xs:A list`; `ys:A list`]) THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL]);;

let code_split_LENGTH = prove
 (`!ts1 ts2 ts3 xs ys.
     (xs,ys) = code_split ts1 ts2 (ts3:A list)
     ==> LENGTH xs + LENGTH ys = LENGTH ts1 + LENGTH ts2 + LENGTH ts3`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[code_split_def; PAIR_EQ; LENGTH] THENL
   [MESON_TAC[ADD_CLAUSES]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
    [`CONS (h:A) ts3`; `ts2:A list`; `xs:A list`; `ys:A list`]) THEN
  ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* the termination of code_sort: HOL4's code_split_LENGTH and              *)
(* code_split_NULL on the context code_split xs [x] [y] = (xs',ys')       *)

let CLOS2AUX_CODE_SORT_TC_TAC : tactic =
  REWRITE_TAC[measure_THM; IMP_CONJ] THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    let th' = SYM th in
    MP_TAC(MATCH_MP code_split_LENGTH th') THEN
    MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] code_split_NULL) th')) THEN
  REWRITE_TAC[NOT_CONS_NIL; GSYM LENGTH_EQ_NIL; LENGTH] THEN ARITH_TAC;;

let code_sort_def = cake_def_wf
  `measure (LENGTH:(num#A) list->num)`
  CLOS2AUX_CODE_SORT_TC_TAC
  `(code_sort ([]:(num#A) list) = []) /\
   (code_sort [x] = [x]) /\
   (code_sort (CONS x (CONS y xs)) =
      let (xs,ys) = code_split xs [x] [y] in
        code_merge (code_sort xs) (code_sort ys))`;;

let code_sort_ind = cake_ind "code_sort";;

let chain_exps_def = cake_def
  `(chain_exps i [] =
      [(i,0,clos_Op backend_common_None (IntOp (clos_Const (&0))) [])]) /\
   (chain_exps i [e] = [(i,0,e)]) /\
   (chain_exps i (CONS e es) =
      CONS (i,0,clos_Let backend_common_None [e]
                  (clos_Call backend_common_None 0 (i + 1) []))
           (chain_exps (i + 1) es))`;;

let chain_exps_ind = cake_ind "chain_exps";;

(* c.max_app must be the same each time this is called; the next locations *)
(* leave space for the functions that call the expressions, and keep the   *)
(* alignment (padding)                                                     *)

let compile_common_def = cake_def
  `compile_common c es =
     let es = clos_mti_compile (clos_to_bvl_config_do_mti c)
                               (clos_to_bvl_config_max_app c) es in
     let loc = clos_to_bvl_config_next_loc c + MAX 1 (LENGTH es) in
     let loc = if loc MOD 2 = 0 then loc else loc + 1 in
     let (n,es) = renumber_code_locs_list loc es in
     let (kc,es) = clos_known_compile (clos_to_bvl_config_known_conf c) es in
     let (es,g,aux) = clos_call_compile (clos_to_bvl_config_do_call c) es in
     let prog = APPEND (chain_exps (clos_to_bvl_config_next_loc c) es) aux in
     let prog = clos_annotate_compile prog in
       (clos_to_bvl_config_start_fupd (K (clos_to_bvl_config_next_loc c))
          (clos_to_bvl_config_next_loc_fupd (K n)
             (clos_to_bvl_config_known_conf_fupd (K kc)
                (clos_to_bvl_config_call_state_fupd (K (g,aux)) c))),
        prog)`;;

let add_src_names_def = cake_def
  `(add_src_names n [] (l:mlstring spt) = l) /\
   (add_src_names n (CONS x xs) l =
      add_src_names (n + 2) xs
        (insert n (mlstring_concat [x; implode "_clos"]) (insert (n + 1) x l)))`;;

(* HOL4: get_src_names; the names of clos_If, clos_Let, .. (HOL4 _) are    *)
(* wildcards, the names of Fn and clos_Letrec name and names              *)

let get_src_names_def = sem1aux_def_wf
  `measure (\p:clos_exp list # mlstring spt. list_size clos_exp_size (FST p))`
  CLOS2AUX_SIZE_TC_TAC
  `(get_src_names [] (l:mlstring spt) = l) /\
   (get_src_names (CONS x (CONS y xs)) l =
      get_src_names (CONS y xs) (get_src_names [x] l)) /\
   (get_src_names [clos_If _ x y z] l =
      get_src_names [x] (get_src_names [y] (get_src_names [z] l))) /\
   (get_src_names [clos_Var _ _] l = l) /\
   (get_src_names [clos_Let _ xs x] l = get_src_names (CONS x xs) l) /\
   (get_src_names [clos_Raise _ x] l = get_src_names [x] l) /\
   (get_src_names [clos_Handle _ x y] l =
      get_src_names [x] (get_src_names [y] l)) /\
   (get_src_names [clos_Tick _ x] l = get_src_names [x] l) /\
   (get_src_names [clos_Call _ _ _ xs] l = get_src_names xs l) /\
   (get_src_names [clos_Op _ _ xs] l = get_src_names xs l) /\
   (get_src_names [clos_App _ _ x xs] l = get_src_names (CONS x xs) l) /\
   (get_src_names [Fn name loc_opt _ _ x] l =
      let l1 = get_src_names [x] l in
        match loc_opt with
          NONE -> l1
        | SOME n -> add_src_names n [name] l1) /\
   (get_src_names [clos_Letrec names loc_opt _ funs x] l =
      let l0 = get_src_names (MAP SND funs) l in
      let l1 = get_src_names [x] l0 in
        match loc_opt with
          NONE -> l1
        | SOME n -> add_src_names n names l1)`;;

let get_src_names_ind = cake_ind "get_src_names";;

let get_src_names_sing_def = sem1aux_def_wf
  `measure (\x:clos_exp # mlstring spt + clos_exp list # mlstring spt.
              sum_CASE x (\p. clos_exp_size (FST p))
                         (\p. list_size clos_exp_size (FST p)))`
  CLOS2AUX_SIZE_TC_TAC
  `(get_src_names_sing (clos_If _ x y z) (l:mlstring spt) =
      get_src_names_sing x (get_src_names_sing y (get_src_names_sing z l))) /\
   (get_src_names_sing (clos_Var _ _) l = l) /\
   (get_src_names_sing (clos_Let _ xs x) l =
      get_src_names_list xs (get_src_names_sing x l)) /\
   (get_src_names_sing (clos_Raise _ x) l = get_src_names_sing x l) /\
   (get_src_names_sing (clos_Handle _ x y) l =
      get_src_names_sing x (get_src_names_sing y l)) /\
   (get_src_names_sing (clos_Tick _ x) l = get_src_names_sing x l) /\
   (get_src_names_sing (clos_Call _ _ _ xs) l = get_src_names_list xs l) /\
   (get_src_names_sing (clos_Op _ _ xs) l = get_src_names_list xs l) /\
   (get_src_names_sing (clos_App _ _ x xs) l =
      get_src_names_list xs (get_src_names_sing x l)) /\
   (get_src_names_sing (Fn name loc_opt _ _ x) l =
      let l1 = get_src_names_sing x l in
        match loc_opt with
          NONE -> l1
        | SOME n -> add_src_names n [name] l1) /\
   (get_src_names_sing (clos_Letrec names loc_opt _ funs x) l =
      let l0 = get_src_names_list (MAP SND funs) l in
      let l1 = get_src_names_sing x l0 in
        match loc_opt with
          NONE -> l1
        | SOME n -> add_src_names n names l1) /\
   (get_src_names_list [] l = l) /\
   (get_src_names_list (CONS x xs) l =
      get_src_names_list xs (get_src_names_sing x l))`;;

let get_src_names_sing_ind = cake_ind "get_src_names_sing";;

let get_src_names_sing_eq = prove
 (`(!e (l:mlstring spt). get_src_names [e] l = get_src_names_sing e l) /\
   (!es (l:mlstring spt). get_src_names es l = get_src_names_list es l)`,
  MATCH_MP_TAC get_src_names_sing_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[get_src_names_sing_def; get_src_names_def] THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `xs:clos_exp list` THEN
  ASM_REWRITE_TAC[get_src_names_def; get_src_names_sing_def]);;

let make_name_alist_def = cake_def
  `make_name_alist nums (prog:(num#num#clos_exp) list) nstubs dec_start
                   (dec_length:num) =
     let src_names = get_src_names (MAP (SND o SND) prog) LN in
       fromAList
         (MAP (\n. (n,if n < nstubs then
                        if n = nstubs - 1 then implode "bvl_init" else
                        if n = nstubs - 2 then implode "bvl_force" else
                          implode "bvl_stub"
                      else let clos_name = n - nstubs in
                        if dec_start <= clos_name /\
                           clos_name < dec_start + dec_length
                        then implode "dec" else
                          match lookup clos_name src_names with
                            NONE -> implode "unknown_clos_fun"
                          | SOME s -> s)) nums)`;;

let make_name_alist_eq = prove
 (CASE_TERM
  `!nums (prog:(num#num#clos_exp) list) nstubs dec_start (dec_length:num).
     make_name_alist nums prog nstubs dec_start dec_length =
     let src_names = get_src_names_list (MAP (SND o SND) prog) LN in
       fromAList
         (MAP (\n. (n,if n < nstubs then
                        if n = nstubs - 1 then implode "bvl_init" else
                        if n = nstubs - 2 then implode "bvl_force" else
                          implode "bvl_stub"
                      else let clos_name = n - nstubs in
                        if dec_start <= clos_name /\
                           clos_name < dec_start + dec_length
                        then implode "dec" else
                          match lookup clos_name src_names with
                            NONE -> implode "unknown_clos_fun"
                          | SOME s -> s)) nums)`,
  REWRITE_TAC[make_name_alist_def; get_src_names_sing_eq]);;

(* HOL4: compile *)

let clos_to_bvl_compile_def = cake_def
  `clos_to_bvl_compile c0 es =
     let (c,prog) = compile_common c0 es in
     let n = num_stubs (clos_to_bvl_config_max_app c) in
     let init_stubs = toAList (clos_to_bvl_init_code (clos_to_bvl_config_max_app c)) in
     let init_globs =
       [(n - 1,0,init_globals (clos_to_bvl_config_max_app c)
                              (n + clos_to_bvl_config_start c))] in
     let force_stub = [(n - 2,2,force_thunk_code)] in
     let comp_progs = clos_to_bvl_compile_prog (clos_to_bvl_config_max_app c) prog in
     let prog' = APPEND (APPEND (APPEND init_stubs force_stub) init_globs)
                        comp_progs in
     let func_names = make_name_alist (MAP FST prog') prog n
                        (clos_to_bvl_config_next_loc c0) (LENGTH es) in
     let c = clos_to_bvl_config_start_fupd (K (n - 1)) c in
       (c,code_sort prog',func_names)`;;

let extract_name_def = cake_def
  `(extract_name [] = (0,[])) /\
   (extract_name (CONS x xs) =
      match (some n. ?t. x = clos_Op t (IntOp (clos_Const (&n))) []) with
        NONE -> (0,CONS x xs)
      | SOME n -> (n,if xs = [] then [x] else xs))`;;

let CLOS2AUX_SOME_NUM = prove
 (`!i:int. (some n. i = &n) =
           if i < &0 then NONE else SOME (num_of_int (abs i))`,
  GEN_TAC THEN COND_CASES_TAC THENL
   [REWRITE_TAC[some_DEF] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM CHOOSE_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_LT; CONJUNCT1 LT]) THEN
    FIRST_ASSUM CONTR_TAC;
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[INT_NOT_LT]) THEN
    SUBGOAL_THEN `abs (i:int) = i` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[INT_ABS_REFL]; ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP INT_OF_NUM_OF_INT) THEN
    REWRITE_TAC[INT_OF_NUM_EQ; NUM_OF_INT_OF_NUM; some_EQ]]);;

(* the choice of extract_name: some n. ... is a case on the expression *)

let CLOS2AUX_EXTRACT_SOME = prove
 (CASE_TERM
  `!x. (some n. ?t. x = clos_Op t (IntOp (clos_Const (&n))) []) =
       match x with
         clos_Op t (IntOp (clos_Const i)) [] ->
           if i < &0 then NONE else SOME (num_of_int (abs i))
       | _ -> NONE`,
  GEN_TAC THEN CASES_ON `x:clos_exp` THEN CASE_REWRITE_TAC[some_F] THEN
  REWRITE_TAC[UNWIND_THM1] THEN CASES_ON `a1:clos_op` THEN
  CASE_REWRITE_TAC[some_F] THEN CASES_ON `a:int_op` THEN
  CASE_REWRITE_TAC[some_F] THEN CASES_ON `a2:clos_exp list` THEN
  CASE_REWRITE_TAC[some_F; CLOS2AUX_SOME_NUM]);;

let CLOS2AUX_EXTRACT_NAME_CONS = prove
 (CASE_TERM
  `!x xs. extract_name (CONS x xs) =
          match x with
            clos_Op t (IntOp (clos_Const i)) [] ->
              (if i < &0 then (0,CONS x xs) else
                 (num_of_int (abs i),if xs = [] then [x] else xs))
          | _ -> (0,CONS x xs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[extract_name_def; CLOS2AUX_EXTRACT_SOME] THEN
  CASES_ON `x:clos_exp` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a1:clos_op` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a:int_op` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a2:clos_exp list` THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[]);;

let extract_name_pmatch = prove
 (CASE_TERM
  `!xs. extract_name xs =
        match xs with
          [] -> (0,xs)
        | CONS x xs ->
            match x with
              clos_Op t (IntOp (clos_Const i)) [] ->
                (if i < &0 then (0,CONS x xs) else
                   (num_of_int (abs i),if xs = [] then [x] else xs))
            | _ -> (0,CONS x xs)`,
  GEN_TAC THEN CASES_ON `xs:clos_exp list` THEN
  REWRITE_TAC[extract_name_def; CLOS2AUX_EXTRACT_NAME_CONS] THEN
  CASE_REWRITE_TAC[]);;

(* HOL4: compile_inc *)

let clos_to_bvl_compile_inc'_def = cake_def
  `clos_to_bvl_compile_inc' max_app (es,prog) =
     let (n,real_es) = extract_name es in
       clos_to_bvl_compile_prog max_app (APPEND (chain_exps n real_es) prog)`;;

let clos_to_bvl_compile_inc_def = cake_def
  `clos_to_bvl_compile_inc c (p:clos_prog) =
     let p = cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
                                  (clos_to_bvl_config_max_app c) p in
     let (n,p) = ignore_table clos_number_compile_inc
                              (clos_to_bvl_config_next_loc c) p in
     let c = clos_to_bvl_config_next_loc_fupd (K n) c in
     let spt = option_val_approx_spt (clos_to_bvl_config_known_conf c) in
     let (spt,p) = known_compile_inc
                     (known_static_conf (clos_to_bvl_config_known_conf c)) spt p in
     let c = clos_to_bvl_config_known_conf_fupd
               (K (option_upd_val_spt spt (clos_to_bvl_config_known_conf c))) c in
     let (c',p) = cond_call_compile_inc (clos_to_bvl_config_do_call c)
                    (FST (clos_to_bvl_config_call_state c)) p in
     let c = clos_to_bvl_config_call_state_fupd (K (c',[])) c in
     let p = clos_annotate_compile_inc p in
     let p = clos_to_bvl_compile_inc' (clos_to_bvl_config_max_app c) p in
       (c,p)`;;
