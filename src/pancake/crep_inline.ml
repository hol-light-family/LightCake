(* ========================================================================= *)
(* crep_inline: port of HOL4 pancake/crep_inlineScript.sml (CakeML v3479).   *)
(* Function inlining pass in crepLang.                                       *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as notes/naming/names.tsv says: the early_exit constructors Exn   *)
(*   and Ret are crep_inline_Exn and crep_inline_Ret (Loop_exit keeps its   *)
(*   name); the crepLang constructors are crep_Dec, crep_Call, ...           *)
(* - ++ is APPEND, GENLIST f n is list_of_seq f n, fm \\ k is fdomsub;       *)
(*   0w and 1w are word 0 and word 1; f $ x is f x.                          *)
(* - MAP2: HOL Light's MAP2 has the length of its first list (HOL4's MAP2   *)
(*   truncates the longer list).  transform_eoc and transform_branch write  *)
(*   HOL4's MAP2 Assign rets es as MAP2 crep_Assign (TAKE (LENGTH es) rets)  *)
(*   es, which is HOL4's list for all lengths (TAKE is HOL4's): a callee's   *)
(*   Return es may have fewer expressions than rets, and HOL Light's MAP2    *)
(*   would then put unspecified expressions HD [] into the code             *)
(*   (crep_inlineProof's every_inst_crep_inline would fail).  inline_nontail *)
(*   keeps HOL Light's MAP2: its one use (inline_prog) has rts and temp_rets *)
(*   of equal lengths (notes/DEVIATIONS.md).                                 *)
(* - The clauses for crep_Call are parsed apart from the others (e is an    *)
(*   expression in crep_Dec and a function name in crep_Call; in one         *)
(*   quotation a variable has one type).  Bound pattern variables that HOL4 *)
(*   reuses with another type (e in unreach_elim's case on (r1,r2)) are      *)
(*   renamed.                                                                *)
(* - HOL4 inline_prog Termination: WF_REL_TAC with HOL4's relation           *)
(*   inv_image (measure I LEX measure (prog_size ARB)) on (CARD (FDOM fs),p).*)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "pancake/crepLang.ml";;

prioritize_num();;
type_invention_error := true;;

(* Counting all the variables that appear in a prog *)

let var_prog_def = cake_def
  (list_mk_conj
   [`(var_prog (crep_Dec v e p:(A)crep_prog) =
        APPEND (APPEND [v] (var_cexp e)) (var_prog p):num list) /\
     (var_prog (crep_Assign v e) = APPEND [v] (var_cexp e)) /\
     (var_prog (crep_Store e1 e2) = APPEND (var_cexp e1) (var_cexp e2)) /\
     (var_prog (crep_Store32 e1 e2) = APPEND (var_cexp e1) (var_cexp e2)) /\
     (var_prog (crep_StoreByte e1 e2) = APPEND (var_cexp e1) (var_cexp e2)) /\
     (var_prog (StoreGlob w e) = var_cexp e) /\
     (var_prog (crep_Seq p1 p2) = APPEND (var_prog p1) (var_prog p2)) /\
     (var_prog (crep_If e p1 p2) =
        APPEND (APPEND (var_cexp e) (var_prog p1)) (var_prog p2)) /\
     (var_prog (crep_While e p) = APPEND (var_cexp e) (var_prog p))`;
    `(var_prog (crep_Call ctyp e es:(A)crep_prog) =
        let var_ctyp =
          match ctyp with
            NONE -> []
          | SOME (vs,NONE) -> vs
          | SOME (vs,SOME (w,hdl)) -> APPEND vs (var_prog hdl) in
        APPEND (FLAT (MAP var_cexp es)) var_ctyp:num list)`;
    `(var_prog (crep_ExtCall f v1 v2 v3 v4:(A)crep_prog) = [v1; v2; v3; v4]:num list) /\
     (var_prog (crep_Return es) = FLAT (MAP var_cexp es)) /\
     (var_prog (crep_ShMem mop v e) = APPEND [v] (var_cexp e)) /\
     (var_prog (crep_Primitive lhss pop rhss) = APPEND lhss rhss) /\
     (var_prog _ = [])`]);;

(* Largest variable of a prog *)

let vmax_prog_def = cake_def
  `vmax_prog (p:(A)crep_prog) = MAX_LIST (var_prog p)`;;

(* Check if a prog has a return statement or a tail call *)

let has_return_def = cake_def
  (list_mk_conj
   [`(has_return (crep_Dec v e p:(A)crep_prog) <=> has_return p) /\
     (has_return (crep_Seq p1 p2) <=> has_return p1 \/ has_return p2) /\
     (has_return (crep_If e p1 p2) <=> has_return p1 \/ has_return p2) /\
     (has_return (crep_While e p) <=> has_return p)`;
    `(has_return (crep_Call ctyp e args:(A)crep_prog) <=>
        match ctyp with
          NONE -> T
        | SOME (_,NONE) -> F
        | SOME (_,SOME (w,hdl)) -> has_return hdl)`;
    `(has_return (crep_Return e:(A)crep_prog) <=> T) /\
     (has_return _ <=> F)`]);;

let has_return_ind = cake_ind "has_return";;

(* This simulates the argument loading of a function call.  Conceptually,  *)
(* only one nested_decs round is needed: nested_decs args_vname args p, but *)
(* variables in args might be shadowed by those in args_vname.              *)

let arg_load_def = cake_def
  `arg_load tmp_vars args args_vname (p:(A)crep_prog) =
     nested_decs tmp_vars args (nested_decs args_vname (MAP crep_Var tmp_vars) p)`;;

(* Whether a function has a return in a branching statement; this includes *)
(* Returns inside a While loop                                              *)

let not_branch_ret_def = cake_def
  (list_mk_conj
   [`(not_branch_ret (crep_Dec v e p:(A)crep_prog) <=> not_branch_ret p) /\
     (not_branch_ret (crep_Seq p1 p2) <=> not_branch_ret p1 /\ not_branch_ret p2) /\
     (not_branch_ret (crep_If e p1 p2) <=> ~has_return p1 /\ ~has_return p2) /\
     (not_branch_ret (crep_While e p) <=> ~has_return p)`;
    `(not_branch_ret (crep_Call ctyp e args:(A)crep_prog) <=>
        match ctyp with
          NONE -> T
        | SOME (_,NONE) -> T
        | SOME (_,SOME (w,hdl)) -> ~has_return hdl) /\
     (not_branch_ret _ <=> T)`]);;

let not_branch_ret_ind = cake_ind "not_branch_ret";;

(* Types of early exit *)

let early_exit_INDUCT,early_exit_RECURSION = cake_type
  "early_exit = crep_inline_Exn | crep_inline_Ret | Loop_exit";;

(* Eliminate all unreachable code after Return/Raise/Continue/Break.  This  *)
(* treats a while loop as a non-stopping statement, as the reachability of  *)
(* the loop body is not determined at compile time.                         *)

let unreach_elim_def = cake_def
  (list_mk_conj
   [`(unreach_elim (crep_Return e:(A)crep_prog) =
        (crep_Return e,SOME crep_inline_Ret)) /\
     (unreach_elim (crep_Raise eid) = (crep_Raise eid,SOME crep_inline_Exn)) /\
     (unreach_elim (crep_Break n) = (crep_Break n,SOME Loop_exit)) /\
     (unreach_elim (crep_Continue n) = (crep_Continue n,SOME Loop_exit)) /\
     (unreach_elim (crep_Seq p1 p2) =
        let (p1',r1) = unreach_elim p1 in
        if ~(r1 = NONE) then (p1',r1) else
        let (p2',r2) = unreach_elim p2 in (crep_Seq p1' p2',r2))`;
    `(unreach_elim (crep_Dec v e p:(A)crep_prog) =
        let (p',r) = unreach_elim p in (crep_Dec v e p',r)) /\
     (unreach_elim (crep_If e p1 p2) =
        let (p1',r1) = unreach_elim p1 in
        let (p2',r2) = unreach_elim p2 in
        let r3 = (match (r1,r2) with
                    (SOME crep_inline_Ret,x) -> x
                  | (x,SOME crep_inline_Ret) -> x
                  | (SOME crep_inline_Exn,x) -> x
                  | (x,SOME crep_inline_Exn) -> x
                  | (SOME Loop_exit,x) -> x
                  | (x,SOME Loop_exit) -> x
                  | (NONE,NONE) -> NONE) in
        (crep_If e p1' p2',r3)) /\
     (unreach_elim (crep_While e p) =
        let (p',r) = unreach_elim p in (crep_While e p',NONE))`;
    `(unreach_elim (crep_Call ctyp e args:(A)crep_prog) =
        match ctyp with
          NONE -> (crep_Call NONE e args,SOME crep_inline_Ret)
        | SOME (rt,NONE) -> (crep_Call (SOME (rt,NONE)) e args,NONE)
        | SOME (rt,SOME (w,hdl)) ->
            let (hdl',rhdl) = unreach_elim hdl in
            (crep_Call (SOME (rt,SOME (w,hdl'))) e args,NONE)) /\
     (unreach_elim p = (p,NONE))`]);;

let unreach_elim_ind = cake_ind "unreach_elim";;

(* Transformation of Return statements; rets: the variables to be returned *)
(* to at the call site.                                                     *)

(* Transform the callee's body where Returns are not inside any branching  *)
(* statements                                                               *)

let transform_eoc_def = cake_def
  (list_mk_conj
   [`(transform_eoc rets (crep_Return es:(A)crep_prog) =
        crep_nested_seq (MAP2 crep_Assign (TAKE (LENGTH es) rets) es))`;
    `(transform_eoc rets (crep_Call ctyp e args:(A)crep_prog) =
        match ctyp with
          NONE -> crep_Call (SOME (rets,NONE)) e args
        | SOME (rs,NONE) -> crep_Call (SOME (rs,NONE)) e args
        | SOME (rs,SOME (w,hdl)) ->
            crep_Call (SOME (rs,SOME (w,transform_eoc rets hdl))) e args)`;
    `(transform_eoc (rets:num list) (crep_Dec v e p:(A)crep_prog) =
        crep_Dec v e (transform_eoc rets p)) /\
     (transform_eoc rets (crep_While e p) = crep_While e (transform_eoc rets p)) /\
     (transform_eoc rets (crep_Seq p1 p2) =
        crep_Seq (transform_eoc rets p1) (transform_eoc rets p2)) /\
     (transform_eoc rets (crep_If e p1 p2) =
        crep_If e (transform_eoc rets p1) (transform_eoc rets p2)) /\
     (transform_eoc rets p = p)`]);;

let transform_eoc_ind = cake_ind "transform_eoc";;

(* Transform the callee's body where Returns are inside branching           *)
(* statements (If/While).  The implementation wraps a While(true) loop      *)
(* around the callee's body and turns Returns into multi-level Breaks.      *)

let transform_branch_def = cake_def
  (list_mk_conj
   [`(transform_branch ld rets (crep_Return es:(A)crep_prog) =
        crep_Seq (crep_nested_seq (MAP2 crep_Assign (TAKE (LENGTH es) rets) es))
                 (crep_Break ld))`;
    `(transform_branch ld rets (crep_Call ctyp e args:(A)crep_prog) =
        match ctyp with
          NONE -> crep_Seq (crep_Call (SOME (rets,NONE)) e args) (crep_Break ld)
        | SOME (rs,NONE) -> crep_Call (SOME (rs,NONE)) e args
        | SOME (rs,SOME (w,hdl)) ->
            crep_Call (SOME (rs,SOME (w,transform_branch ld rets hdl))) e args)`;
    `(transform_branch ld (rets:num list) (crep_Dec v e p:(A)crep_prog) =
        crep_Dec v e (transform_branch ld rets p)) /\
     (transform_branch ld rets (crep_While e p) =
        crep_While e (transform_branch (ld + 1) rets p)) /\
     (transform_branch ld rets (crep_Seq p1 p2) =
        crep_Seq (transform_branch ld rets p1) (transform_branch ld rets p2)) /\
     (transform_branch ld rets (crep_If e p1 p2) =
        crep_If e (transform_branch ld rets p1) (transform_branch ld rets p2)) /\
     (transform_branch ld rets p = p)`]);;

let transform_branch_ind = cake_ind "transform_branch";;

(* Merge the callee body of a tail call into the caller's body; Tick is for *)
(* clock synchronisation                                                    *)

let inline_tail_def = cake_def
  `inline_tail (p:(A)crep_prog) = crep_Seq crep_Tick p`;;

(* Inline a (transformed) function body where the call site is not a tail  *)
(* call.  p: the transformed callee's body; rts: the variables to be        *)
(* returned to, defined at the call site; temp_rets: temporary variables   *)
(* to avoid shadowing (rts might be shadowed by a variable inside the       *)
(* callee's body); tmp_vars: temporary variables to avoid shadowing the    *)
(* function arguments; args: the expressions passed as arguments;          *)
(* args_vname: the original names of the function's arguments.  The main  *)
(* transformed body arg_load .. guarantees to assign the Return values of  *)
(* the call to temp_rets, and the nested_seq after it assigns them back to *)
(* rts.                                                                     *)

let inline_nontail_def = cake_def
  `inline_nontail (p:(A)crep_prog) rts temp_rets tmp_vars args args_vname =
     nested_decs temp_rets (REPLICATE (LENGTH temp_rets) (crep_Const (word 0)))
       (crep_Seq (arg_load tmp_vars args args_vname p)
                 (crep_nested_seq (MAP2 crep_Assign rts (MAP crep_Var temp_rets))))`;;

(* Perform function inlining over a program's body, with a known inline    *)
(* map.  This ignores all function calls with a handler.                    *)

(* the termination condition of the inlined callee: the inline map shrinks *)

let PCINLAUX_CARD_FDOM_DOMSUB_LT = prove
 (`!(fm:(A,B)fmap) k v.
     FLOOKUP fm k = SOME v ==> CARD (FDOM (fm \\ k)) < CARD (FDOM fm)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flookup_thm; FDOM_DOMSUB] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_DELETE; FDOM_FINITE] THEN
  SUBGOAL_THEN `~(CARD (FDOM (fm:(A,B)fmap)) = 0)` MP_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0; FDOM_FINITE] THEN ASM SET_TAC[]; ARITH_TAC]);;

let PCINLAUX_INLINE_TC_TAC : tactic =
  let lt th = MATCH_ACCEPT_TAC (MATCH_MP PCINLAUX_CARD_FDOM_DOMSUB_LT th) in
  FIRST
   [TERM_TAC;
    REPEAT BOSS_STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[inv_image_THM] THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[LEX_THM; measure_THM; I_THM] THEN
    DISJ1_TAC THEN FIRST_ASSUM(fun th g -> try lt th g with Failure _ -> lt (SYM th) g)];;

let inline_prog_def = cake_def_wf
  `inv_image (measure I LEX measure (crep_prog_size ARB))
     (\(x:(mlstring,num list # (A)crep_prog)fmap,y:(A)crep_prog). (CARD (FDOM x),y))`
  PCINLAUX_INLINE_TC_TAC
  (list_mk_conj
   [`(inline_prog inlineable_fs (crep_Call ctyp e args:(A)crep_prog) =
        let ctyp_inl =
          match ctyp with
            NONE -> NONE
          | SOME (x,NONE) -> SOME (x,NONE)
          | SOME (x,SOME (w,hdl)) -> SOME (x,SOME (w,inline_prog inlineable_fs hdl)) in
        if (match ctyp_inl with NONE -> F | SOME (rts,_) -> ~ALL_DISTINCT rts)
        then crep_Call ctyp_inl e args else
        match FLOOKUP inlineable_fs e with
          NONE -> crep_Call ctyp_inl e args
        | SOME (args_vname,p) ->
            let n_inlineable_fs = inlineable_fs \\ e in
            let inlined_callee_unnormalised = inline_prog n_inlineable_fs p in
            let (inlined_callee,exit_type) = unreach_elim inlined_callee_unnormalised in
            let max_args = MAX_LIST (FLAT (MAP var_cexp args)) in
            let max_args_vname = MAX_LIST args_vname in
            let tmp_vars = list_of_seq (\x. SUC x + MAX max_args max_args_vname)
                             (LENGTH args_vname) in
            match ctyp_inl with
              NONE -> inline_tail (arg_load tmp_vars args args_vname inlined_callee)
            | SOME (rts,hdl) ->
                (match hdl with
                   NONE ->
                     let ret_max = MAX_LIST [MAX_LIST rts; vmax_prog inlined_callee;
                                             MAX_LIST tmp_vars] in
                     let temp_rets = list_of_seq (\x. SUC x + ret_max) (LENGTH rts) in
                     let n_br = not_branch_ret inlined_callee in
                     let transformed_callee =
                       if n_br
                       then crep_Seq crep_Tick (transform_eoc temp_rets inlined_callee)
                       else crep_While (crep_Const (word 1))
                              (transform_branch 0 temp_rets inlined_callee) in
                     inline_nontail transformed_callee rts temp_rets tmp_vars args
                       args_vname
                 | SOME w_hdl -> crep_Call ctyp_inl e args))`;
    `(inline_prog (inlineable_fs:(mlstring,num list # (A)crep_prog)fmap)
                  (crep_Dec v e p:(A)crep_prog) =
        crep_Dec v e (inline_prog inlineable_fs p)) /\
     (inline_prog inlineable_fs (crep_Seq p1 p2) =
        let inline_p1 = inline_prog inlineable_fs p1 in
        let inline_p2 = inline_prog inlineable_fs p2 in
        crep_Seq inline_p1 inline_p2) /\
     (inline_prog inlineable_fs (crep_If e p1 p2) =
        let inline_p1 = inline_prog inlineable_fs p1 in
        let inline_p2 = inline_prog inlineable_fs p2 in
        crep_If e inline_p1 inline_p2) /\
     (inline_prog inlineable_fs (crep_While e p) =
        crep_While e (inline_prog inlineable_fs p)) /\
     (inline_prog inlineable_fs p = p)`]);;

let inline_prog_ind = cake_ind "inline_prog";;


let compile_inl_prog_def = cake_def
  `compile_inl_prog (inl_fs:(mlstring,num list # (A)crep_prog)fmap) prog =
     MAP (\(name,params:B,body). (name,params,inline_prog (inl_fs \\ name) body)) prog`;;

let compile_inl_top_def = cake_def
  `compile_inl_top inl_fname (prog:(mlstring # num list # (A)crep_prog)list) =
     let inl_fs_alist = FILTER (\(x,y). MEM x inl_fname) prog in
     let inl_fs = alist_to_fmap inl_fs_alist in
     compile_inl_prog inl_fs prog`;;
