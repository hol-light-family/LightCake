(* ========================================================================= *)
(* panStatic: port of HOL4 pancake/panStaticScript.sml (CakeML v3479).       *)
(* Static checking for Pancake (see the HOL4 header for the full list):      *)
(* general checks (main function, exported functions, missing function      *)
(* exits, loop exits outside loops, argument numbers; warnings for          *)
(* unreachable statements and base-calculated addresses), scope checks,     *)
(* shape checks and primitive checks.                                        *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: the record context is                     *)
(*   panStatic_context (fields panStatic_context_locals, ...); the          *)
(*   scoped_id constructors Var and Fun are panStatic_Var and panStatic_Fun; *)
(*   the constructors of panLang and asm are as there (panLang_Skip,         *)
(*   asm_Sub, ...); the mlmap functions are mlmap_lookup, mlmap_insert, ...; *)
(*   errorLogMonad's return, error and bind are errorLogMonad_return, ....   *)
(* - The type abbreviation static_result of HOL4 (with a type variable) is   *)
(*   written out: (A,staterr)error # (staterr)list.                          *)
(* - Variables named like constants of the port are renamed: is_load (asm)   *)
(*   is is_load', field (then a constant of bitstring, now bitstring_field)  *)
(*   and fields are field' and fields', the let variable                     *)
(*   op_type (a constant of bvi_tailrec) is op_type'.                        *)
(* - Record literals are the record constructors (fields in declaration     *)
(*   order), r.f is RECTYPE_f r, r with f := v is RECTYPE_f_fupd (K v) r;   *)
(*   LLOOKUP l i is oEL i l, ZIP (l1,l2) is ZIP l1 l2 (in all three uses    *)
(*   both lists have the same length: OPT_MMAP and static_check_exps         *)
(*   preserve the length), concat is mlstring_concat, strlit and an          *)
(*   mlstring literal are implode, ^ is strcat, () is one, num_to_str is     *)
(*   mlint's.                                                                *)
(* - Paired lambdas of HOL4 inside recursive definitions (sh_bd_from_bd)     *)
(*   are \p. match p with (a,b) -> .. (pair_CASE), so that the recursive    *)
(*   calls get the pattern as context.                                       *)
(* - Helpers that are not HOL4 names have the prefix PPARSEAUX_.             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/errorLogMonad.ml";;
needs "basis/pure/mllist.ml";;
needs "basis/pure/mlint.ml";;
needs "basis/pure/mlmap.ml";;
needs "pancake/panLang.ml";;

type_invention_error := true;;

(* Error categories for printing *)

let staterr_INDUCT,staterr_RECURSION = cake_type
  "staterr = ScopeErr mlstring
           | WarningErr mlstring
           | GenErr mlstring
           | ShapeErr mlstring";;

(* HOL4 Type static_result = :('a, staterr) error # staterr list (the        *)
(* return type of the static_check functions: the value or the proper       *)
(* error, with the list of warnings) is written out where it is used        *)

(* Exp-level state for references to @base.  "Priority": Based >           *)
(* NotTrusted > Trusted > NotBased, where an exp can never have a lower     *)
(* priority state than its components                                       *)

let based_INDUCT,based_RECURSION = cake_type
  "based = Based | NotBased | Trusted | NotTrusted";;

(* Exp-level state for shape-aware basedness *)

let shaped_based_INDUCT,shaped_based_RECURSION = cake_type
  "shaped_based = WordB based
                | StructB (shaped_based list)
                | NamedB stcname ((fldname # shaped_based) list)";;

(* Prog-level state for reachability: the transitions are linear, IsReach  *)
(* -> WarnReach -> NotReach, where NotReach only comes after a reachability *)
(* warning                                                                  *)

let reachable_INDUCT,reachable_RECURSION = cake_type
  "reachable = IsReach | NotReach | WarnReach";;

(* Prog-level state for the exit-ness of the final statement: function      *)
(* exits, loop exits, ambiguous exit (after conditionals), non-exits        *)

let last_stmt_INDUCT,last_stmt_RECURSION = cake_type
  "last_stmt = RetLast | RaiseLast | TailLast
             | BreakLast | ContLast
             | CondExitLast
             | InvisLast | OtherLast";;

(* Type for function state: the shape of the return value, the parameters *)

let func_info_INFO = cake_record "func_info"
  ["ret_shape","shape";
   "params","(varname#shape)list"];;

(* Type for local var state: the shaped basedness of the var *)

let local_info_INFO = cake_record "local_info"
  ["vsh_bd","shaped_based"];;

(* Type for global var state: the shape of the var *)

let global_info_INFO = cake_record "global_info"
  ["vshape","shape"];;

(* Type for error scope: in a function (possibly more specific), in a      *)
(* global declaration, in a struct name declaration, top level              *)

let scope_INDUCT,scope_RECURSION = cake_type
  "scope = FunScope funname mlstring
         | DeclScope varname
         | StcScope stcname fldname
         | TopLevel";;

(* Record for the current (per-func) context: tracked var state, declared  *)
(* globals, all function info, all exception declaration info, the struct  *)
(* name context, the current scope info, loop status, reachability,        *)
(* exit-ness of the last statement, location string                         *)

let panStatic_context_INFO = cake_record "panStatic_context"
  ["locals","(varname,local_info)map";
   "globals","(varname,global_info)map";
   "funcs","(funname,func_info)map";
   "exns","(eid,shape)map";
   "structs","(stcname#struct_info)list";
   "scope","scope";
   "in_loop","bool";
   "is_reachable","reachable";
   "last","last_stmt";
   "loc","mlstring"];;

(* Record for static_check_exp returns: shaped basedness of the exp *)

let exp_return_INFO = cake_record "exp_return"
  ["sh_bd","shaped_based"];;

(* Record for static_check_exps returns: shaped basedness of the exps *)

let exps_return_INFO = cake_record "exps_return"
  ["sh_bds","(shaped_based)list"];;

(* Record for static_check_prog returns: function exit status for all      *)
(* paths, loop exit status for all paths, new exit-ness of the last         *)
(* statement, change in var state, latest location string                   *)

let prog_return_INFO = cake_record "prog_return"
  ["exits_fun","bool";
   "exits_loop","bool";
   "last","last_stmt";
   "var_delta","(varname,local_info)map";
   "curr_loc","mlstring"];;

(* Varieties of identifiers that can be out of scope *)

let scoped_id_INDUCT,scoped_id_RECURSION = cake_type
  "scoped_id = panStatic_Var | panStatic_Fun | Stc";;

(* Functions for based and shaped_based *)

(* Builds a shaped based from a given shape and single based.  USED ON      *)
(* PRE-CHECKED SHAPES ONLY (will never be NONE)                             *)

(* HOL4's termination proof uses the local lemma dropWhile P xs = ys ==>   *)
(* LENGTH ys <= LENGTH xs (from LENGTH_dropWhile_LESS_EQ)                    *)

let sh_bd_from_sh_def = cake_def_wf
  `MEASURE (LENGTH:(mlstring#struct_info)list->num) LEX
   MEASURE (shape_size o (SND:based#shape->shape))`
  (REWRITE_TAC[LEX_THM; measure_THM; o_THM] THEN REPEAT STRIP_TAC THEN
   ((DISJ1_TAC THEN FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP LIBXAUX_dropWhile_CONS))
    ORELSE
    (DISJ2_TAC THEN REWRITE_TAC(type_size_def "shape" :: size_aux_eqs "shape") THEN
     FIRST_ASSUM(MP_TAC o MATCH_MP MEM_IMP_shape_size) THEN ARITH_TAC)))
  `(sh_bd_from_sh (sctxt:(mlstring#struct_info)list) b One = SOME (WordB b)) /\
   (sh_bd_from_sh sctxt b (Comb shs) =
      match OPT_MMAP (sh_bd_from_sh sctxt b) shs with
        SOME sbs -> SOME (StructB sbs)
      | NONE -> NONE) /\
   (sh_bd_from_sh sctxt b (Named nm) =
      match dropWhile (\(n,i). ~(n = nm)) sctxt with
        CONS (nm,info) sctxt' ->
          (let (field_nms,field_shs) = UNZIP (struct_info_fields info) in
           match OPT_MMAP (sh_bd_from_sh sctxt' b) field_shs with
             SOME field_sbs -> SOME (NamedB nm (ZIP field_nms field_sbs))
           | NONE -> NONE)
      | _ -> NONE)`;;

let sh_bd_from_sh_ind = cake_ind "sh_bd_from_sh";;

(* Builds a shaped based with the shape of a given shaped based and a       *)
(* single based (HOL4's paired lambda \(nm,sb). .. is a pair_CASE here)     *)

let sh_bd_from_bd_def = cake_def_wf
  `MEASURE (\p:based#shaped_based. shaped_based_size (SND p))`
  TERM_TAC
  `(sh_bd_from_bd b (WordB b') = WordB b) /\
   (sh_bd_from_bd b (StructB sbs) = StructB (MAP (sh_bd_from_bd b) sbs)) /\
   (sh_bd_from_bd b (NamedB nm flds) =
      NamedB nm (MAP (\p. match p with (nm,sb) -> (nm,sh_bd_from_bd b sb)) flds))`;;

(* Determine if a shaped based has a given shape *)

let sh_bd_has_shape_def = cake_def_wf
  `MEASURE (\s:(shape#shaped_based)+((shape)list#(shaped_based)list).
              sum_CASE s (\p. shape_size (FST p))
                         (\p. list_size shape_size (FST p)))`
  TERM_TAC
  `(sh_bd_has_shape sh sb <=>
      match (sh,sb) with
        (One,WordB b) -> T
      | (Comb shs,StructB sbs) -> sh_bd_has_shape_list shs sbs
      | (Named nm,NamedB nm' flds) -> nm = nm'
      | _ -> F) /\
   (sh_bd_has_shape_list [] [] <=> T) /\
   (sh_bd_has_shape_list (CONS sh shs) [] <=> F) /\
   (sh_bd_has_shape_list [] (CONS sb sbs) <=> F) /\
   (sh_bd_has_shape_list (CONS sh shs) (CONS sb sbs) <=>
      sh_bd_has_shape sh sb /\ sh_bd_has_shape_list shs sbs)`;;

(* Determine if two shaped baseds have the same shape *)

let sh_bd_eq_shapes_def = cake_def_wf
  `MEASURE (\s:(shaped_based#shaped_based)+
               ((shaped_based)list#(shaped_based)list).
              sum_CASE s (\p. shaped_based_size (FST p))
                         (\p. list_size shaped_based_size (FST p)))`
  TERM_TAC
  `(sh_bd_eq_shapes sb sh <=>
      match (sb,sh) with
        (WordB b,WordB b') -> T
      | (StructB sbs,StructB sbs') -> sh_bd_eq_shapes_list sbs sbs'
      | (NamedB nm flds,NamedB nm' flds') -> nm = nm'
      | _ -> F) /\
   (sh_bd_eq_shapes_list [] [] <=> T) /\
   (sh_bd_eq_shapes_list (CONS sb sbs) [] <=> F) /\
   (sh_bd_eq_shapes_list [] (CONS sb sbs) <=> F) /\
   (sh_bd_eq_shapes_list (CONS sb sbs) (CONS sb' sbs') <=>
      sh_bd_eq_shapes sb sb' /\ sh_bd_eq_shapes_list sbs sbs')`;;

(* Lookup shaped basedness at a certain struct index (HOL4 LLOOKUP sbs i is *)
(* oEL i sbs)                                                               *)

let index_sh_bd_def = cake_def
  `(index_sh_bd i (WordB b) = NONE) /\
   (index_sh_bd i (StructB sbs) = oEL i sbs) /\
   (index_sh_bd i (NamedB nm flds) = NONE)`;;

(* Lookup shaped basedness at a certain struct field *)

let field_sh_bd_def = cake_def
  `(field_sh_bd (fld:mlstring) (WordB b) = NONE) /\
   (field_sh_bd fld (StructB sbs) = NONE) /\
   (field_sh_bd fld (NamedB nm flds) = ALOOKUP flds fld)`;;

(* Merge basedness according to priority *)

let based_merge_def = cake_def
  `based_merge x y =
     match (x,y) with
       (Based,_) -> Based
     | (_,Based) -> Based
     | (NotTrusted,_) -> NotTrusted
     | (_,NotTrusted) -> NotTrusted
     | (Trusted,_) -> Trusted
     | (_,Trusted) -> Trusted
     | (NotBased,NotBased) -> NotBased`;;

(* Comparison for combining basedness between If/While branches *)

let sh_bd_branch_def = cake_def
  `sh_bd_branch x y = if x = y then x else sh_bd_from_bd NotTrusted x`;;

(* Combine the local var state deltas of If/While branches, where states   *)
(* are either combined between the two deltas (if in both) or with the      *)
(* prior context (if in just one); needs extension with extension of the   *)
(* local_info type                                                          *)

let branch_loc_inf_def = cake_def
  `branch_loc_inf (vctxt:(mlstring,local_info)map) x y =
     let x' =
       mlmap_mapWithKey (\k v. local_info_vsh_bd_fupd (combin_K
           (if ~(mlmap_member k y) then
              match mlmap_lookup vctxt k with
                SOME v' -> sh_bd_branch (local_info_vsh_bd v) (local_info_vsh_bd v')
              | NONE -> sh_bd_from_bd NotTrusted (local_info_vsh_bd v)
            else local_info_vsh_bd v)) v) x in
     let y' =
       mlmap_mapWithKey (\k v. local_info_vsh_bd_fupd (combin_K
           (if ~(mlmap_member k x) then
              match mlmap_lookup vctxt k with
                SOME v' -> sh_bd_branch (local_info_vsh_bd v) (local_info_vsh_bd v')
              | NONE -> sh_bd_from_bd NotTrusted (local_info_vsh_bd v)
            else local_info_vsh_bd v)) v) y in
     mlmap_unionWith (\vx vy. local_info_vsh_bd_fupd (combin_K
         (sh_bd_branch (local_info_vsh_bd vx) (local_info_vsh_bd vy))) vx) x' y'`;;

(* Combine the local var state deltas of Seq'd progs *)

let seq_loc_inf_def = cake_def
  `seq_loc_inf (x:(mlstring,local_info)map) y = mlmap_union y x`;;

(* Get the shape string of a shaped based *)

let sh_bd_to_str_def = cake_def_wf
  `MEASURE shaped_based_size`
  TERM_TAC
  `(sh_bd_to_str (WordB b) = implode "1") /\
   (sh_bd_to_str (StructB []) = implode "{}") /\
   (sh_bd_to_str (StructB (CONS x xs)) =
      mlstring_concat
        (APPEND (CONS (implode "{")
                   (CONS (sh_bd_to_str x)
                      (MAP (\x. strcat (implode ",") x) (MAP sh_bd_to_str xs))))
                [implode "}"])) /\
   (sh_bd_to_str (NamedB nm flds) = nm)`;;

(* Functions for last_stmt and reachable *)

(* Get the string name for statement exit-ness.  USED FOR PRINTING          *)
(* ASSOCIATED WARNINGS ONLY                                                 *)

let last_to_str_def = cake_def
  `last_to_str l =
     match l with
       RetLast -> implode "return"
     | RaiseLast -> implode "raise"
     | TailLast -> implode "tail call"
     | BreakLast -> implode "break"
     | ContLast -> implode "continue"
     | CondExitLast -> implode "exiting conditional"
     | _ -> implode ""`;;

(* Determine the next reachability state for prog sequences based on the   *)
(* current state and exit-ness; handles the IsReach -> WarnReach transition *)

let next_is_reachable_def = cake_def
  `next_is_reachable r x =
     match r with
       IsReach -> if ~(x = InvisLast \/ x = OtherLast) then WarnReach else IsReach
     | _ -> r`;;

(* Determine whether reachability has decreased *)

let next_now_unreachable_def = cake_def
  `next_now_unreachable r r' <=> r = IsReach /\ ~(r' = IsReach)`;;

(* Determine whether a prog that can trigger a reachability warning is      *)
(* reached, and return the last exit-ness and update the context if so;    *)
(* handles the WarnReach -> NotReach transition                             *)

let reached_warnable_def = cake_def
  `reached_warnable (s:(A)panLang_prog) ctxt =
     match s with
       panLang_Seq prog1 prog2 -> (NONE,ctxt)
     | panLang_Tick -> (NONE,ctxt)
     | Annot str1 str2 -> (NONE,ctxt)
     | _ ->
         if panStatic_context_is_reachable ctxt = WarnReach then
           (SOME (panStatic_context_last ctxt),
            panStatic_context_is_reachable_fupd (combin_K NotReach) ctxt)
         else (NONE,ctxt)`;;

(* Determine the exit-ness of branches, based on whether a definite func or *)
(* loop exit occurred                                                       *)

let branch_last_stmt_def = cake_def
  `branch_last_stmt double_ret double_loop_exit =
     if double_ret \/ double_loop_exit then CondExitLast else OtherLast`;;

(* Determine the exit-ness of Seq'd progs by ignoring invisible exit-ness *)

let seq_last_stmt_def = cake_def
  `seq_last_stmt x y = if y = InvisLast then x else y`;;

(* Error message helpers *)

(* Get the description of the current scope *)

let get_scope_desc_def = cake_def
  `get_scope_desc scope =
     match scope with
       FunScope fname desc ->
         mlstring_concat [implode "function "; fname; desc]
     | DeclScope vname ->
         mlstring_concat [implode "initialisation of global variable "; vname]
     | StcScope sname fld ->
         mlstring_concat [implode "declaration of field "; fld;
                          implode " in named struct "; sname]
     | TopLevel -> implode "top-level declaration"`;;

(* Get the message for out of scope identifiers (id_type: scoped_id) *)

let get_scope_msg_def = cake_def
  `get_scope_msg id_type loc id scope =
     let id_desc =
       match id_type with
         panStatic_Var -> implode "variable "
       | panStatic_Fun -> implode "function "
       | Stc -> implode "struct name " in
     mlstring_concat [loc; id_desc; id;
                      implode " is not in scope in ";
                      get_scope_desc scope; implode "\n"]`;;

(* List of recognised Primitive identifiers for usage hints *)

let primitive_idents_def = cake_def
  `primitive_idents = [implode "__add_with_carry__"]`;;

(* Adds a hint when a primitive is used in an unsupported position *)

let add_primitive_hint_def = cake_def
  `add_primitive_hint fname msg =
     if MEM fname primitive_idents
     then mlstring_concat
            [msg;
             implode "  note: "; fname;
             implode " is a built-in primitive only available in ";
             implode "declaration or assignment RHS positions\n"]
     else msg`;;

(* Get the message for redefined identifiers (id_type: scoped_id) *)

let get_redec_msg_def = cake_def
  `get_redec_msg id_type loc id scope =
     let id_desc =
       match id_type with
         panStatic_Var -> implode "variable "
       | panStatic_Fun -> implode "function "
       | Stc -> implode "struct name " in
     mlstring_concat [
       loc; id_desc; id;
       implode " is redeclared in ";
       get_scope_desc scope; implode "\n"]`;;

(* Get the message for memory op addresses (is_local: local vs shared,     *)
(* is_load: load vs store, is_untrust: NotTrusted vs other; the variable   *)
(* is_load is is_load' here: is_load is a constant of asm)                 *)

let get_memop_msg_def = cake_def
  `get_memop_msg is_local is_load' is_untrust loc scope =
     let mem_type = if is_local then implode "local " else implode "shared " in
     let op_type' = if is_load' then implode "load " else implode "store " in
     let issue =
       match (is_local,is_untrust) with
         (F,F) -> implode "is "
       | (F,T) -> implode "may be "
       | (T,F) -> implode "is not "
       | (T,T) -> implode "may not be " in
     mlstring_concat [
       loc; mem_type; op_type';
       implode "address "; issue; implode "calculated from base in ";
       get_scope_desc scope; implode "\n"]`;;

(* Get the message for op argument number (is_exact: exactly vs at least) *)

let get_oparg_msg_def = cake_def
  `get_oparg_msg is_exact n_expected n_given loc op scope =
     let issue =
       if is_exact then implode " only accepts "
       else implode " requires at least " in
     mlstring_concat [
       loc; implode "operation "; op;
       issue; n_expected; implode " operands, ";
       n_given; implode " provided in ";
       get_scope_desc scope; implode "\n"]`;;

(* Get the message for an unreachable statement *)

let get_unreach_msg_def = cake_def
  `get_unreach_msg loc last scope = mlstring_concat [
     loc;
     implode "unreachable statement(s) after "; last;
     implode " in ";
     get_scope_desc scope; implode "\n"]`;;

(* Get the message for a rogue loop exit (is_break: break vs continue) *)

let get_rogue_msg_def = cake_def
  `get_rogue_msg is_break loc scope =
     let stmt = if is_break then implode "break " else implode "continue " in
     mlstring_concat [
       loc; stmt;
       implode "statement outside loop in ";
       get_scope_desc scope; implode "\n"]`;;

(* Get the message for a non-word shape *)

let get_non_word_msg_def = cake_def
  `get_non_word_msg desc sh_str loc scope = mlstring_concat [
     loc; desc; implode " has shape "; sh_str;
     implode " instead of a word in ";
     get_scope_desc scope; implode "\n"]`;;

(* Get the message for a declared shape mismatch *)

let get_shape_mismatch_msg_def = cake_def
  `get_shape_mismatch_msg desc sh_str_actual sh_str_expect loc scope =
     mlstring_concat [
       loc; desc; implode " has shape "; sh_str_actual;
       implode " instead of declared shape "; sh_str_expect;
       implode " in ";
       get_scope_desc scope; implode "\n"]`;;

let get_implementation_err_msg_def = cake_def
  `get_implementation_err_msg desc loc scope = mlstring_concat [
     loc; desc; implode " in "; get_scope_desc scope; implode "\n";
     implode "this should never happen. please report to a compiler developer\n"]`;;

(* Misc functions *)

(* Find the first element in a sorted list that is repeated *)

let first_repeat_def = cake_def
  `first_repeat (xs:A list) =
     match xs with
       CONS x1 (CONS x2 xs) ->
         if x1 = x2 then SOME x1
         else first_repeat (CONS x2 xs)
     | _ -> NONE`;;

(* Get the string name of binary ops *)

let binop_to_str_def = cake_def
  `binop_to_str op =
     match op with
       asm_Add -> implode "Add"
     | asm_Sub -> implode "Sub"
     | asm_And -> implode "And"
     | asm_Or -> implode "Or"
     | asm_Xor -> implode "Xor"`;;

(* Get the string name of Pancake ops *)

let panop_to_str_def = cake_def
  `panop_to_str op =
     match op with
       panLang_Mul -> implode "Mul"`;;

(* Get the string name of Pancake primitives *)

let primop_to_str_def = cake_def
  `primop_to_str pop =
     match pop with
       panLang_AddCarry -> implode "AddCarry"`;;

(* Static check helpers.  HOL4's errorLog monad syntax is written out: do  *)
(* x <- m; r od is errorLogMonad_bind m (\x. r), do m; r od is              *)
(* errorLogMonad_bind m (\u. r) (the monad has no ignore-bind; u does not  *)
(* occur in r), x <<- e; r is let x = e in r, return and error are          *)
(* errorLogMonad_return and errorLogMonad_error, () is one                  *)

(* Check for an out of scope func *)

let check_fun_name_def = cake_def
  `check_fun_name ctxt fname =
     match mlmap_lookup (panStatic_context_funcs ctxt) fname with
       NONE -> errorLogMonad_error (ScopeErr
                 (add_primitive_hint fname
                    (get_scope_msg panStatic_Fun (panStatic_context_loc ctxt) fname
                                   (panStatic_context_scope ctxt))))
     | SOME f -> errorLogMonad_return f
       :(func_info,staterr)error#(staterr)list`;;

(* Check for an out of scope global *)

let check_global_var_def = cake_def
  `check_global_var ctxt vname =
     match mlmap_lookup (panStatic_context_globals ctxt) vname with
       NONE -> errorLogMonad_error (ScopeErr
                 (get_scope_msg panStatic_Var (panStatic_context_loc ctxt) vname
                                (panStatic_context_scope ctxt)))
     | SOME v -> errorLogMonad_return v
       :(global_info,staterr)error#(staterr)list`;;

(* Check for an out of scope local *)

let check_local_var_def = cake_def
  `check_local_var ctxt vname =
     match mlmap_lookup (panStatic_context_locals ctxt) vname with
       NONE -> errorLogMonad_error (ScopeErr
                 (get_scope_msg panStatic_Var (panStatic_context_loc ctxt) vname
                                (panStatic_context_scope ctxt)))
     | SOME v -> errorLogMonad_return v
       :(local_info,staterr)error#(staterr)list`;;

(* Check for a redeclared variable *)

let check_redec_var_def = cake_def
  `check_redec_var ctxt vname =
     match (mlmap_lookup (panStatic_context_locals ctxt) vname,
            mlmap_lookup (panStatic_context_globals ctxt) vname) with
       (NONE,NONE) -> errorLogMonad_return one
     | _ -> errorLogMonad_log (WarningErr (get_redec_msg panStatic_Var (panStatic_context_loc ctxt)
                                           vname (panStatic_context_scope ctxt)))
       :(1,staterr)error#(staterr)list`;;

(* Check the shapes of exported arguments *)

let check_export_params_def = cake_def
  `(check_export_params loc scope [] =
      errorLogMonad_return one:(1,staterr)error#(staterr)list) /\
   (check_export_params loc scope (CONS (vname,shape) ps) =
      if ~(shape = One) then
        errorLogMonad_error (ShapeErr (get_non_word_msg
            (mlstring_concat [implode "exported function parameter "; vname])
            (shape_to_str shape) loc scope))
      else check_export_params loc scope ps)`;;

(* Check operand shape and return the merged shaped basedness *)

let check_operands_def = cake_def
  `(check_operands ctxt op_str [] =
      errorLogMonad_return NotBased:(based,staterr)error#(staterr)list) /\
   (check_operands ctxt op_str (CONS sb sbs) =
      match sb with
        WordB b ->
          errorLogMonad_bind (check_operands ctxt op_str sbs) (\b'.
            errorLogMonad_return (based_merge b b'))
      | _ -> errorLogMonad_error (ShapeErr (get_non_word_msg
               (mlstring_concat [implode "operation "; op_str; implode " operand"])
               (sh_bd_to_str sb) (panStatic_context_loc ctxt)
               (panStatic_context_scope ctxt))))`;;

(* Check args for primitives and return the result shaped basedness *)

let check_primitive_args_def = cake_def
  `check_primitive_args ctxt panLang_AddCarry sh_bds =
     let op_str = primop_to_str panLang_AddCarry in
     let nargs = LENGTH sh_bds in
     errorLogMonad_bind
       (if ~(nargs = 3)
        then errorLogMonad_error (GenErr (get_oparg_msg T (implode "3")
               (num_to_str nargs) (panStatic_context_loc ctxt) op_str
               (panStatic_context_scope ctxt)))
        else errorLogMonad_return one) (\u.
     errorLogMonad_bind (check_operands ctxt op_str sh_bds) (\b.
     errorLogMonad_return (StructB [WordB b; WordB NotBased])))
       :(shaped_based,staterr)error#(staterr)list`;;

(* Check the argument number and shapes *)

let check_func_args_def = cake_def
  `check_func_args ctxt fname (params:(mlstring#shape)list) sh_bds =
     match (params,sh_bds) with
       (CONS (p,s) ps,CONS sb sbs) ->
         if ~(sh_bd_has_shape s sb) then
           errorLogMonad_error (ShapeErr (get_shape_mismatch_msg
             (mlstring_concat [implode "value for argument "; p;
                               implode " given to function "; fname])
             (sh_bd_to_str sb) (shape_to_str s) (panStatic_context_loc ctxt)
             (panStatic_context_scope ctxt)))
         else check_func_args ctxt fname ps sbs
     | (CONS (p,s) ps,[]) -> errorLogMonad_error (GenErr (mlstring_concat [
         panStatic_context_loc ctxt; implode "argument "; p;
         implode " for call to function "; fname;
         implode " is missing in ";
         get_scope_desc (panStatic_context_scope ctxt); implode "\n"]))
     | ([],CONS sb sbs) -> errorLogMonad_error (GenErr (mlstring_concat [
         panStatic_context_loc ctxt; implode "extra arguments given to function ";
         fname; implode " in ";
         get_scope_desc (panStatic_context_scope ctxt); implode "\n"]))
     | ([],[]) -> errorLogMonad_return one:(1,staterr)error#(staterr)list`;;

(* Check that all fields are given exactly one value and shape (the        *)
(* variable fields is fields' here: fields is a constant of mlstring)       *)

let check_struct_fields_def = cake_def_wf
  `MEASURE (\p:panStatic_context#mlstring#(mlstring#shape)list#
                (mlstring#shaped_based)list. LENGTH (FST (SND (SND p))))`
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN
   ASM_REWRITE_TAC[LENGTH; FST; SND] THEN ARITH_TAC)
  `check_struct_fields ctxt sname (fields':(mlstring#shape)list)
                       (fsbs:(mlstring#shaped_based)list) =
     match (fields',fsbs) with
       (CONS (fld,sh) fss,fsbs) ->
         errorLogMonad_bind
           (match FILTER (\(fld',sb). fld = fld') fsbs with
              [(fld,sb)] -> errorLogMonad_return sb
            | [] -> errorLogMonad_error (ShapeErr (mlstring_concat [
                panStatic_context_loc ctxt; implode "missing field "; fld;
                implode " in named struct "; sname;
                implode " constant in ";
                get_scope_desc (panStatic_context_scope ctxt); implode "\n"]))
            | _ -> errorLogMonad_error (ShapeErr (mlstring_concat [
                panStatic_context_loc ctxt; implode "multiple values for field ";
                fld; implode " in named struct "; sname;
                implode " constant in ";
                get_scope_desc (panStatic_context_scope ctxt); implode "\n"])))
           (\sb.
         if ~(sh_bd_has_shape sh sb) then
           errorLogMonad_error (ShapeErr (get_shape_mismatch_msg
             (mlstring_concat [implode "value for field "; fld;
                               implode " given to named struct "; sname])
             (sh_bd_to_str sb) (shape_to_str sh) (panStatic_context_loc ctxt)
             (panStatic_context_scope ctxt)))
         else check_struct_fields ctxt sname fss (ADELKEY fld fsbs))
     | ([],CONS fsb fsbs) -> errorLogMonad_error (GenErr (mlstring_concat [
         panStatic_context_loc ctxt; implode "unexpected field "; FST fsb;
         implode " given to named struct "; sname;
         implode " in ";
         get_scope_desc (panStatic_context_scope ctxt); implode "\n"]))
     | ([],[]) -> errorLogMonad_return one:(1,staterr)error#(staterr)list`;;

(* Check that the shape names are in scope *)

let check_shape_def = cake_def_wf
  `MEASURE (\s:((mlstring#B)list#mlstring#scope#shape)+
               ((mlstring#B)list#mlstring#scope#(shape)list).
              sum_CASE s (\p. shape_size (SND (SND (SND p))))
                         (\p. list_size shape_size (SND (SND (SND p)))))`
  TERM_TAC
  `(check_shape (sctxt:(mlstring#B)list) (loc:mlstring) (scope:scope) One =
      errorLogMonad_return one:(1,staterr)error#(staterr)list) /\
   (check_shape sctxt loc scope (Comb shs) = check_shapes sctxt loc scope shs) /\
   (check_shape sctxt loc scope (Named nm) =
      match ALOOKUP sctxt nm with
        SOME flds -> errorLogMonad_return one
      | NONE -> errorLogMonad_error (ScopeErr (get_scope_msg Stc loc nm scope))) /\
   (check_shapes sctxt loc scope [] = errorLogMonad_return one) /\
   (check_shapes sctxt loc scope (CONS sh shs) =
      errorLogMonad_bind (check_shape sctxt loc scope sh) (\u.
        check_shapes sctxt loc scope shs))`;;

(* Check field/param shape *)

let check_id_shapes_def = cake_def
  `(check_id_shapes (sctxt:(mlstring#B)list) (loc:mlstring) (scope:scope) [] =
      errorLogMonad_return one:(1,staterr)error#(staterr)list) /\
   (check_id_shapes sctxt loc scope (CONS (id,shape) ids) =
      errorLogMonad_bind
        (match scope with
           FunScope fname _ ->
             errorLogMonad_return
               (FunScope fname (mlstring_concat [implode " parameter "; id]))
         | StcScope sname _ -> errorLogMonad_return (StcScope sname id)
         | s -> errorLogMonad_error (GenErr (get_implementation_err_msg
                  (implode "parameter or field found in unexpected scope")
                  loc scope))) (\scope'.
      errorLogMonad_bind (check_shape sctxt loc scope' shape) (\u.
      check_id_shapes sctxt loc scope ids)))`;;

(* Main static checking functions *)

(* for the termination of static_check_exp: the expressions of a list of   *)
(* named fields are smaller than the list (HOL4 proves it inline, by        *)
(* induction on eflds)                                                      *)

let PPARSEAUX_list_size_MAP_SND = prove
 (`!(f:B->num) (g:A->num) l. list_size f (MAP SND l) <= list_size (pair_size g f) l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; list_size; LE_REFL] THEN PAIR_CASES_ON `h:A#B` THEN
  REWRITE_TAC[pair_size_THM; SND] THEN ASM_ARITH_TAC);;

let PPARSEAUX_EXP_SIZE_TAC =
  TERM_TAC ORELSE
  (REWRITE_TAC[measure_THM; case_def "sum"] THEN REPEAT STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[UNZIP_DEF; PAIR_EQ]) THEN
   REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
   REPEAT VAR_EQ_TAC THEN
   REWRITE_TAC(type_size_def "panLang_exp" :: size_aux_eqs "panLang_exp") THEN
   MATCH_MP_TAC(ARITH_RULE `a <= b ==> a < 1 + c + b`) THEN
   REWRITE_TAC[PPARSEAUX_list_size_MAP_SND]);;

(* static_check_exp returns (exp info (exp_return)) static_result,          *)
(* static_check_exps (exps info (exps_return)) static_result.  The last     *)
(* clause of static_check_exp is written for its pattern variable            *)
(* BytesInWordB in HOL4, which covers only BytesInWord (all the other       *)
(* constructors come before it); the variable field is field' here (field  *)
(* was a constant of the library, now bitstring_field)                      *)

let static_check_exp_def = cake_def_wf
  `MEASURE (\s:(panStatic_context#(A)panLang_exp)+
               (panStatic_context#((A)panLang_exp)list).
              sum_CASE s (\p. panLang_exp_size (\x:A. 0) (SND p))
                         (\p. list_size (panLang_exp_size (\x:A. 0)) (SND p)))`
  PPARSEAUX_EXP_SIZE_TAC
  `(static_check_exp ctxt (panLang_Const num:(A)panLang_exp) =
      errorLogMonad_return (exp_return_REC (WordB NotBased))
        :(exp_return,staterr)error#(staterr)list) /\
   (static_check_exp ctxt (panLang_Var panLang_Local vname) =
      errorLogMonad_bind (check_local_var ctxt vname) (\vinf.
      errorLogMonad_return (exp_return_REC (local_info_vsh_bd vinf)))) /\
   (static_check_exp ctxt (panLang_Var panLang_Global vname) =
      errorLogMonad_bind (check_global_var ctxt vname) (\vinf.
      match sh_bd_from_sh (panStatic_context_structs ctxt) Trusted
                          (global_info_vshape vinf) with
        SOME sb -> errorLogMonad_return (exp_return_REC sb)
      | NONE -> errorLogMonad_error (ScopeErr (get_implementation_err_msg
          (implode "static analysis failed to convert in-scope shape")
          (panStatic_context_loc ctxt) (panStatic_context_scope ctxt))))) /\
   (static_check_exp ctxt (RStruct exps) =
      errorLogMonad_bind (static_check_exps ctxt exps) (\esret.
      errorLogMonad_return (exp_return_REC (StructB (exps_return_sh_bds esret))))) /\
   (static_check_exp ctxt (RField index exp) =
      errorLogMonad_bind (static_check_exp ctxt exp) (\eret.
      match index_sh_bd index (exp_return_sh_bd eret) with
        NONE -> errorLogMonad_error (ShapeErr (mlstring_concat [
            panStatic_context_loc ctxt; implode "expression shape ";
            sh_bd_to_str (exp_return_sh_bd eret);
            implode " has no field at index "; num_to_str index;
            implode " in "; get_scope_desc (panStatic_context_scope ctxt);
            implode "\n"]))
      | SOME sb -> errorLogMonad_return (exp_return_REC sb))) /\
   (static_check_exp ctxt (NStruct name eflds) =
      errorLogMonad_bind
        (match ALOOKUP (panStatic_context_structs ctxt) name with
           SOME info -> errorLogMonad_return info
         | NONE -> errorLogMonad_error (ScopeErr (get_scope_msg Stc
                     (panStatic_context_loc ctxt) name
                     (panStatic_context_scope ctxt)))) (\sinfo.
      let (field_names,field_exps) = UNZIP eflds in
      errorLogMonad_bind (static_check_exps ctxt field_exps) (\esret.
      let field_sbs = ZIP field_names (exps_return_sh_bds esret) in
      errorLogMonad_bind
        (check_struct_fields ctxt name (struct_info_fields sinfo) field_sbs) (\u.
      errorLogMonad_return (exp_return_REC (NamedB name field_sbs)))))) /\
   (static_check_exp ctxt (NField field' exp) =
      errorLogMonad_bind (static_check_exp ctxt exp) (\eret.
      match field_sh_bd field' (exp_return_sh_bd eret) with
        NONE -> errorLogMonad_error (ShapeErr (mlstring_concat [
            panStatic_context_loc ctxt; implode "expression shape ";
            sh_bd_to_str (exp_return_sh_bd eret);
            implode " has no field "; field'; implode " in ";
            get_scope_desc (panStatic_context_scope ctxt); implode "\n"]))
      | SOME sb -> errorLogMonad_return (exp_return_REC sb))) /\
   (static_check_exp ctxt (panLang_Load shape addr) =
      errorLogMonad_bind
        (check_shape (panStatic_context_structs ctxt) (panStatic_context_loc ctxt)
                     (panStatic_context_scope ctxt) shape) (\u.
      errorLogMonad_bind (static_check_exp ctxt addr) (\aret.
      errorLogMonad_bind
        (match exp_return_sh_bd aret with
           StructB _ ->
             errorLogMonad_error (ShapeErr (get_non_word_msg
               (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
               (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         | NamedB _ _ ->
             errorLogMonad_error (ShapeErr (get_non_word_msg
               (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
               (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         | WordB NotBased ->
             errorLogMonad_log (WarningErr (get_memop_msg T T F (panStatic_context_loc ctxt)
                                            (panStatic_context_scope ctxt)))
         | WordB NotTrusted ->
             errorLogMonad_log (WarningErr (get_memop_msg T T T (panStatic_context_loc ctxt)
                                            (panStatic_context_scope ctxt)))
         | _ -> errorLogMonad_return one) (\u.
      match sh_bd_from_sh (panStatic_context_structs ctxt) Trusted shape with
        SOME sb -> errorLogMonad_return (exp_return_REC sb)
      | NONE -> errorLogMonad_error (ScopeErr (get_implementation_err_msg
          (implode "static analysis failed to convert in-scope shape")
          (panStatic_context_loc ctxt) (panStatic_context_scope ctxt))))))) /\
   (static_check_exp ctxt (panLang_Load32 addr) =
      errorLogMonad_bind (static_check_exp ctxt addr) (\aret.
      errorLogMonad_bind
        (match exp_return_sh_bd aret with
           StructB _ ->
             errorLogMonad_error (ShapeErr (get_non_word_msg
               (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
               (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         | NamedB _ _ ->
             errorLogMonad_error (ShapeErr (get_non_word_msg
               (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
               (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         | WordB NotBased ->
             errorLogMonad_log (WarningErr (get_memop_msg T T F (panStatic_context_loc ctxt)
                                            (panStatic_context_scope ctxt)))
         | WordB NotTrusted ->
             errorLogMonad_log (WarningErr (get_memop_msg T T T (panStatic_context_loc ctxt)
                                            (panStatic_context_scope ctxt)))
         | _ -> errorLogMonad_return one) (\u.
      errorLogMonad_return (exp_return_REC (WordB Trusted))))) /\
   (static_check_exp ctxt (LoadByte addr) =
      errorLogMonad_bind (static_check_exp ctxt addr) (\aret.
      errorLogMonad_bind
        (match exp_return_sh_bd aret with
           StructB _ ->
             errorLogMonad_error (ShapeErr (get_non_word_msg
               (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
               (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         | NamedB _ _ ->
             errorLogMonad_error (ShapeErr (get_non_word_msg
               (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
               (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         | WordB NotBased ->
             errorLogMonad_log (WarningErr (get_memop_msg T T F (panStatic_context_loc ctxt)
                                            (panStatic_context_scope ctxt)))
         | WordB NotTrusted ->
             errorLogMonad_log (WarningErr (get_memop_msg T T T (panStatic_context_loc ctxt)
                                            (panStatic_context_scope ctxt)))
         | _ -> errorLogMonad_return one) (\u.
      errorLogMonad_return (exp_return_REC (WordB Trusted))))) /\
   (static_check_exp ctxt (panLang_Op bop exps) =
      let op_str = binop_to_str bop in
      let nargs = LENGTH exps in
      errorLogMonad_bind
        (match bop with
           asm_Sub ->
             if ~(nargs = 2) then
               errorLogMonad_error (GenErr (get_oparg_msg T (implode "2")
                 (num_to_str nargs) (panStatic_context_loc ctxt) op_str
                 (panStatic_context_scope ctxt)))
             else errorLogMonad_return one
         | _ ->
             if nargs < 2 then
               errorLogMonad_error (GenErr (get_oparg_msg F (implode "2")
                 (num_to_str nargs) (panStatic_context_loc ctxt) op_str
                 (panStatic_context_scope ctxt)))
             else errorLogMonad_return one) (\u.
      errorLogMonad_bind (static_check_exps ctxt exps) (\esret.
      errorLogMonad_bind (check_operands ctxt op_str (exps_return_sh_bds esret)) (\b.
      errorLogMonad_return (exp_return_REC (WordB b)))))) /\
   (static_check_exp ctxt (Panop pop exps) =
      let op_str = panop_to_str pop in
      let nargs = LENGTH exps in
      errorLogMonad_bind
        (match pop with
           panLang_Mul ->
             if ~(nargs = 2) then
               errorLogMonad_error (GenErr (get_oparg_msg T (implode "2")
                 (num_to_str nargs) (panStatic_context_loc ctxt) op_str
                 (panStatic_context_scope ctxt)))
             else errorLogMonad_return one) (\u.
      errorLogMonad_bind (static_check_exps ctxt exps) (\esret.
      errorLogMonad_bind (check_operands ctxt op_str (exps_return_sh_bds esret)) (\b.
      errorLogMonad_return (exp_return_REC (WordB b)))))) /\
   (static_check_exp ctxt (Cmp cop exp1 exp2) =
      errorLogMonad_bind (static_check_exp ctxt exp1) (\eret1.
      errorLogMonad_bind (static_check_exp ctxt exp2) (\eret2.
      errorLogMonad_bind
        (if ~(sh_bd_eq_shapes (exp_return_sh_bd eret1) (exp_return_sh_bd eret2))
         then errorLogMonad_error (ShapeErr (mlstring_concat [
                panStatic_context_loc ctxt;
                implode "comparison given operands of different shapes in ";
                get_scope_desc (panStatic_context_scope ctxt); implode "\n"]))
         else errorLogMonad_return one) (\u.
      errorLogMonad_return (exp_return_REC (WordB NotBased)))))) /\
   (static_check_exp ctxt (panLang_Shift sop exp1 exp2) =
      errorLogMonad_bind (static_check_exp ctxt exp1) (\eret1.
      errorLogMonad_bind (static_check_exp ctxt exp2) (\eret2.
      errorLogMonad_bind
        (if ~(sh_bd_has_shape One (exp_return_sh_bd eret1)) then
           errorLogMonad_error (ShapeErr (get_non_word_msg
             (implode "shifted expression")
             (sh_bd_to_str (exp_return_sh_bd eret1))
             (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         else if ~(sh_bd_has_shape One (exp_return_sh_bd eret2)) then
           errorLogMonad_error (ShapeErr (get_non_word_msg
             (implode "shift expression")
             (sh_bd_to_str (exp_return_sh_bd eret2))
             (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      errorLogMonad_return eret2)))) /\
   (static_check_exp ctxt BaseAddr =
      errorLogMonad_return (exp_return_REC (WordB Based))) /\
   (static_check_exp ctxt TopAddr =
      errorLogMonad_return (exp_return_REC (WordB Based))) /\
   (static_check_exp ctxt BytesInWord =
      errorLogMonad_return (exp_return_REC (WordB NotBased))) /\
   (static_check_exps ctxt [] =
      errorLogMonad_return (exps_return_REC [])
        :(exps_return,staterr)error#(staterr)list) /\
   (static_check_exps ctxt (CONS exp exps) =
      errorLogMonad_bind (static_check_exp ctxt exp) (\eret.
      errorLogMonad_bind (static_check_exps ctxt exps) (\esret.
      errorLogMonad_return
        (exps_return_REC (CONS (exp_return_sh_bd eret)
                               (exps_return_sh_bds esret))))))`;;

let static_check_exp_ind = cake_ind "static_check_exp";;

(* static_check_prog returns (prog info (prog_return)) static_result.  The  *)
(* HOL4 overloads AssignCall s h, TailCall and StandAloneCall h are written *)
(* out: panLang_Call (SOME (SOME s,h)), panLang_Call NONE and panLang_Call   *)
(* (SOME (NONE,h)).  A prog_return literal <| exits_fun := a; exits_loop :=  *)
(* b; last := c; var_delta := d; curr_loc := e |> is prog_return_REC a b c   *)
(* d e; ctxt with f := v is panStatic_context_f_fupd (K v) ctxt              *)

let PPARSEAUX_PROG_SIZE_TAC =
  TERM_TAC ORELSE (REPEAT STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN TERM_TAC);;

let static_check_prog_def = cake_def_wf
  `MEASURE (\p:panStatic_context#(A)panLang_prog.
              panLang_prog_size (\x:A. 0) (SND p))`
  PPARSEAUX_PROG_SIZE_TAC
  `(static_check_prog ctxt (panLang_Skip:(A)panLang_prog) =
      errorLogMonad_return
        (prog_return_REC F F OtherLast (mlmap_empty mlstring_compare)
                         (panStatic_context_loc ctxt))
        :(prog_return,staterr)error#(staterr)list) /\
   (static_check_prog ctxt (Dec vname shape exp prog) =
      errorLogMonad_bind (check_redec_var ctxt vname) (\u.
      errorLogMonad_bind
        (check_shape (panStatic_context_structs ctxt) (panStatic_context_loc ctxt)
                     (panStatic_context_scope ctxt) shape) (\u.
      errorLogMonad_bind (static_check_exp ctxt exp) (\eret.
      errorLogMonad_bind
        (if ~(sh_bd_has_shape shape (exp_return_sh_bd eret)) then
           errorLogMonad_error (ShapeErr (get_shape_mismatch_msg
             (mlstring_concat [implode "expression to initialise local variable ";
                               vname])
             (sh_bd_to_str (exp_return_sh_bd eret)) (shape_to_str shape)
             (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      let ctxt' =
        panStatic_context_last_fupd (combin_K OtherLast)
          (panStatic_context_locals_fupd
             (combin_K (mlmap_insert (panStatic_context_locals ctxt) vname
                              (local_info_REC (exp_return_sh_bd eret)))) ctxt) in
      errorLogMonad_bind (static_check_prog ctxt' prog) (\pret.
      errorLogMonad_return
        (prog_return_REC (prog_return_exits_fun pret) (prog_return_exits_loop pret)
           (prog_return_last pret) (mlmap_delete (prog_return_var_delta pret) vname)
           (prog_return_curr_loc pret)))))))) /\
   (static_check_prog ctxt (DecCall vname shape fname args prog) =
      errorLogMonad_bind (check_redec_var ctxt vname) (\u.
      errorLogMonad_bind
        (check_shape (panStatic_context_structs ctxt) (panStatic_context_loc ctxt)
                     (panStatic_context_scope ctxt) shape) (\u.
      errorLogMonad_bind (check_fun_name ctxt fname) (\finf.
      errorLogMonad_bind (static_check_exps ctxt args) (\esret.
      errorLogMonad_bind
        (check_func_args ctxt fname (func_info_params finf)
                         (exps_return_sh_bds esret)) (\u.
      errorLogMonad_bind
        (if ~(shape = func_info_ret_shape finf) then
           errorLogMonad_error (ShapeErr (get_shape_mismatch_msg
             (mlstring_concat [implode "result of function call "; fname;
                               implode " to initialise local variable "; vname])
             (shape_to_str (func_info_ret_shape finf)) (shape_to_str shape)
             (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      errorLogMonad_bind
        (match sh_bd_from_sh (panStatic_context_structs ctxt) Trusted shape with
           SOME sb -> errorLogMonad_return sb
         | NONE -> errorLogMonad_error (ScopeErr (get_implementation_err_msg
             (implode "static analysis failed to convert in-scope shape")
             (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))) (\sb.
      let ctxt' =
        panStatic_context_last_fupd (combin_K OtherLast)
          (panStatic_context_locals_fupd
             (combin_K (mlmap_insert (panStatic_context_locals ctxt) vname
                              (local_info_REC sb))) ctxt) in
      errorLogMonad_bind (static_check_prog ctxt' prog) (\pret.
      errorLogMonad_return
        (prog_return_REC (prog_return_exits_fun pret) (prog_return_exits_loop pret)
           (prog_return_last pret) (mlmap_delete (prog_return_var_delta pret) vname)
           (prog_return_curr_loc pret))))))))))) /\
   (static_check_prog ctxt (panLang_Assign panLang_Local vname exp) =
      errorLogMonad_bind (check_local_var ctxt vname) (\vinf.
      errorLogMonad_bind (static_check_exp ctxt exp) (\eret.
      errorLogMonad_bind
        (if ~(sh_bd_eq_shapes (local_info_vsh_bd vinf) (exp_return_sh_bd eret)) then
           errorLogMonad_error (ShapeErr (get_shape_mismatch_msg
             (mlstring_concat [implode "expression assigned to local variable ";
                               vname])
             (sh_bd_to_str (exp_return_sh_bd eret))
             (sh_bd_to_str (local_info_vsh_bd vinf))
             (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      errorLogMonad_return
        (prog_return_REC F F OtherLast
           (mlmap_singleton mlstring_compare vname
              (local_info_vsh_bd_fupd (combin_K (exp_return_sh_bd eret)) vinf))
           (panStatic_context_loc ctxt)))))) /\
   (static_check_prog ctxt (panLang_Assign panLang_Global vname exp) =
      errorLogMonad_bind (check_global_var ctxt vname) (\vinf.
      errorLogMonad_bind (static_check_exp ctxt exp) (\eret.
      errorLogMonad_bind
        (if ~(sh_bd_has_shape (global_info_vshape vinf) (exp_return_sh_bd eret)) then
           errorLogMonad_error (ShapeErr (get_shape_mismatch_msg
             (mlstring_concat [implode "expression assigned to global variable ";
                               vname])
             (sh_bd_to_str (exp_return_sh_bd eret))
             (shape_to_str (global_info_vshape vinf))
             (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      errorLogMonad_return
        (prog_return_REC F F OtherLast (mlmap_empty mlstring_compare)
           (panStatic_context_loc ctxt)))))) /\
   (static_check_prog ctxt
      (panLang_Call (SOME (SOME (panLang_Local,vname),hdl)) fname args) =
      errorLogMonad_bind (check_local_var ctxt vname) (\vinf.
      errorLogMonad_bind (check_fun_name ctxt fname) (\finf.
      errorLogMonad_bind (static_check_exps ctxt args) (\esret.
      errorLogMonad_bind
        (check_func_args ctxt fname (func_info_params finf)
                         (exps_return_sh_bds esret)) (\u.
      errorLogMonad_bind
        (if ~(sh_bd_has_shape (func_info_ret_shape finf) (local_info_vsh_bd vinf))
         then errorLogMonad_error (ShapeErr (get_shape_mismatch_msg
             (mlstring_concat [implode "result of function call "; fname;
                               implode " assigned to local variable "; vname])
             (shape_to_str (func_info_ret_shape finf))
             (sh_bd_to_str (local_info_vsh_bd vinf))
             (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      errorLogMonad_bind
        (match hdl with
           NONE -> errorLogMonad_return one
         | SOME (eid,evar,prog) ->
             errorLogMonad_bind
               (match mlmap_lookup (panStatic_context_exns ctxt) eid with
                  NONE -> errorLogMonad_error (ScopeErr (mlstring_concat [
                            implode "exception "; eid;
                            implode " is not declared\n"]))
                | SOME sh -> errorLogMonad_return sh) (\sh.
             errorLogMonad_bind (check_local_var ctxt evar) (\evinf.
             errorLogMonad_bind
               (if ~(sh_bd_has_shape sh (local_info_vsh_bd evinf)) then
                  errorLogMonad_error (ShapeErr (mlstring_concat [
                    implode "handler variable "; evar;
                    implode " does not match shape of exception "; eid;
                    implode "\n"]))
                else errorLogMonad_return one) (\u.
             errorLogMonad_bind
               (match sh_bd_from_sh (panStatic_context_structs ctxt) Trusted sh with
                  SOME sb -> errorLogMonad_return sb
                | NONE -> errorLogMonad_error (ScopeErr (get_implementation_err_msg
                    (implode "static analysis failed to convert in-scope shape")
                    (panStatic_context_loc ctxt)
                    (panStatic_context_scope ctxt)))) (\sb.
             errorLogMonad_bind
               (static_check_prog
                  (panStatic_context_locals_fupd
                     (combin_K (mlmap_insert (panStatic_context_locals ctxt) evar
                           (local_info_vsh_bd_fupd (combin_K sb) evinf))) ctxt)
                  prog) (\u.
             errorLogMonad_return one)))))) (\u.
      errorLogMonad_return
        (prog_return_REC F F OtherLast
           (mlmap_singleton mlstring_compare vname
              (local_info_vsh_bd_fupd
                 (combin_K (sh_bd_from_bd Trusted (local_info_vsh_bd vinf))) vinf))
           (panStatic_context_loc ctxt))))))))) /\
   (static_check_prog ctxt
      (panLang_Call (SOME (SOME (panLang_Global,vname),hdl)) fname args) =
      errorLogMonad_bind (check_global_var ctxt vname) (\vinf.
      errorLogMonad_bind (check_fun_name ctxt fname) (\finf.
      errorLogMonad_bind (static_check_exps ctxt args) (\esret.
      errorLogMonad_bind
        (check_func_args ctxt fname (func_info_params finf)
                         (exps_return_sh_bds esret)) (\u.
      errorLogMonad_bind
        (if ~(global_info_vshape vinf = func_info_ret_shape finf) then
           errorLogMonad_error (ShapeErr (get_shape_mismatch_msg
             (mlstring_concat [implode "result of function call "; fname;
                               implode " assigned to global variable "; vname])
             (shape_to_str (func_info_ret_shape finf))
             (shape_to_str (global_info_vshape vinf))
             (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      errorLogMonad_bind
        (match hdl with
           NONE -> errorLogMonad_return one
         | SOME (eid,evar,prog) ->
             errorLogMonad_bind (check_local_var ctxt evar) (\evinf.
             errorLogMonad_bind
               (static_check_prog
                  (panStatic_context_locals_fupd
                     (combin_K (mlmap_insert (panStatic_context_locals ctxt) evar
                           (local_info_vsh_bd_fupd
                              (combin_K (sh_bd_from_bd Trusted (local_info_vsh_bd evinf)))
                              evinf))) ctxt)
                  prog) (\u.
             errorLogMonad_return one))) (\u.
      errorLogMonad_return
        (prog_return_REC F F OtherLast (mlmap_empty mlstring_compare)
           (panStatic_context_loc ctxt))))))))) /\
   (static_check_prog ctxt (Primitive vname pop es) =
      errorLogMonad_bind (check_local_var ctxt vname) (\vinf.
      errorLogMonad_bind (static_check_exps ctxt es) (\esret.
      errorLogMonad_bind
        (check_primitive_args ctxt pop (exps_return_sh_bds esret)) (\res_sb.
      errorLogMonad_bind
        (if ~(sh_bd_eq_shapes (local_info_vsh_bd vinf) res_sb) then
           errorLogMonad_error (ShapeErr (get_shape_mismatch_msg
             (mlstring_concat [implode "result of primitive "; primop_to_str pop;
                               implode " assigned to local variable "; vname])
             (sh_bd_to_str res_sb) (sh_bd_to_str (local_info_vsh_bd vinf))
             (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      errorLogMonad_return
        (prog_return_REC F F OtherLast
           (mlmap_singleton mlstring_compare vname
              (local_info_vsh_bd_fupd (combin_K res_sb) vinf))
           (panStatic_context_loc ctxt))))))) /\
   (static_check_prog ctxt (panLang_Return exp) =
      errorLogMonad_bind (static_check_exp ctxt exp) (\eret.
      errorLogMonad_bind
        (match panStatic_context_scope ctxt with
           FunScope fname _ -> check_fun_name ctxt fname
         | _ -> errorLogMonad_error (GenErr (get_implementation_err_msg
                  (implode "return found outside function scope")
                  (panStatic_context_loc ctxt) (panStatic_context_scope ctxt))))
        (\finf.
      errorLogMonad_bind
        (if ~(sh_bd_has_shape (func_info_ret_shape finf) (exp_return_sh_bd eret))
         then errorLogMonad_error (ShapeErr (get_shape_mismatch_msg
             (implode "expression to return")
             (sh_bd_to_str (exp_return_sh_bd eret))
             (shape_to_str (func_info_ret_shape finf))
             (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      errorLogMonad_return
        (prog_return_REC T F RetLast (mlmap_empty mlstring_compare)
           (panStatic_context_loc ctxt)))))) /\
   (static_check_prog ctxt (panLang_Call NONE fname args) =
      errorLogMonad_bind
        (match panStatic_context_scope ctxt with
           FunScope caller _ -> check_fun_name ctxt caller
         | _ -> errorLogMonad_error
                  (GenErr (implode "tail call found outside function scope")))
        (\caller_inf.
      errorLogMonad_bind (check_fun_name ctxt fname) (\callee_inf.
      errorLogMonad_bind (static_check_exps ctxt args) (\esret.
      errorLogMonad_bind
        (if ~(func_info_ret_shape caller_inf = func_info_ret_shape callee_inf)
         then errorLogMonad_error (ShapeErr (get_shape_mismatch_msg
             (mlstring_concat [implode "result of function call "; fname;
                               implode " to return"])
             (shape_to_str (func_info_ret_shape callee_inf))
             (shape_to_str (func_info_ret_shape caller_inf))
             (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      errorLogMonad_bind
        (check_func_args ctxt fname (func_info_params callee_inf)
                         (exps_return_sh_bds esret)) (\u.
      errorLogMonad_return
        (prog_return_REC T F TailLast (mlmap_empty mlstring_compare)
           (panStatic_context_loc ctxt)))))))) /\
   (static_check_prog ctxt (panLang_Call (SOME (NONE,hdl)) fname args) =
      errorLogMonad_bind (check_fun_name ctxt fname) (\finf.
      errorLogMonad_bind (static_check_exps ctxt args) (\esret.
      errorLogMonad_bind
        (check_func_args ctxt fname (func_info_params finf)
                         (exps_return_sh_bds esret)) (\u.
      errorLogMonad_bind
        (match hdl with
           NONE -> errorLogMonad_return one
         | SOME (eid,evar,prog) ->
             errorLogMonad_bind
               (match mlmap_lookup (panStatic_context_exns ctxt) eid with
                  NONE -> errorLogMonad_error (ScopeErr (mlstring_concat [
                            implode "exception "; eid;
                            implode " is not declared\n"]))
                | SOME sh -> errorLogMonad_return sh) (\sh.
             errorLogMonad_bind (check_local_var ctxt evar) (\evinf.
             errorLogMonad_bind
               (if ~(sh_bd_has_shape sh (local_info_vsh_bd evinf)) then
                  errorLogMonad_error (ShapeErr (mlstring_concat [
                    implode "handler variable "; evar;
                    implode " does not match shape of exception "; eid;
                    implode "\n"]))
                else errorLogMonad_return one) (\u.
             errorLogMonad_bind
               (match sh_bd_from_sh (panStatic_context_structs ctxt) Trusted sh with
                  SOME sb -> errorLogMonad_return sb
                | NONE -> errorLogMonad_error (ScopeErr (get_implementation_err_msg
                    (implode "static analysis failed to convert in-scope shape")
                    (panStatic_context_loc ctxt)
                    (panStatic_context_scope ctxt)))) (\sb.
             errorLogMonad_bind
               (static_check_prog
                  (panStatic_context_locals_fupd
                     (combin_K (mlmap_insert (panStatic_context_locals ctxt) evar
                           (local_info_vsh_bd_fupd (combin_K sb) evinf))) ctxt)
                  prog) (\u.
             errorLogMonad_return one)))))) (\u.
      errorLogMonad_return
        (prog_return_REC F F OtherLast (mlmap_empty mlstring_compare)
           (panStatic_context_loc ctxt))))))) /\
   (static_check_prog ctxt (panLang_ExtCall fname ptr1 len1 ptr2 len2) =
      errorLogMonad_bind (static_check_exps ctxt [ptr1;len1;ptr2;len2]) (\esret.
      errorLogMonad_bind
        (match FIND (\sb. ~(sh_bd_has_shape One sb)) (exps_return_sh_bds esret) with
           SOME sb -> errorLogMonad_error (ShapeErr (get_non_word_msg
             (mlstring_concat [implode "value for argument given to FFI "; fname])
             (sh_bd_to_str sb) (panStatic_context_loc ctxt)
             (panStatic_context_scope ctxt)))
         | NONE -> errorLogMonad_return one) (\u.
      errorLogMonad_return
        (prog_return_REC F F OtherLast (mlmap_empty mlstring_compare)
           (panStatic_context_loc ctxt))))) /\
   (static_check_prog ctxt (panLang_Seq prog1 prog2) =
      let (warn_p1,ctxt1) = reached_warnable prog1 ctxt in
      errorLogMonad_bind
        (match warn_p1 with
           SOME ls -> errorLogMonad_log (WarningErr (get_unreach_msg (panStatic_context_loc ctxt1)
                             (last_to_str ls) (panStatic_context_scope ctxt1)))
         | NONE -> errorLogMonad_return one) (\u.
      errorLogMonad_bind (static_check_prog ctxt1 prog1) (\pret1.
      let next_r = next_is_reachable (panStatic_context_is_reachable ctxt1)
                                     (prog_return_last pret1) in
      let ctxt2 =
        panStatic_context_loc_fupd (combin_K (prog_return_curr_loc pret1))
          (panStatic_context_last_fupd
             (combin_K (if next_now_unreachable (panStatic_context_is_reachable ctxt1) next_r
                 then prog_return_last pret1 else panStatic_context_last ctxt1))
             (panStatic_context_is_reachable_fupd (combin_K next_r)
                (panStatic_context_locals_fupd
                   (combin_K (seq_loc_inf (panStatic_context_locals ctxt1)
                                   (prog_return_var_delta pret1))) ctxt1))) in
      let (warn_p2,ctxt3) = reached_warnable prog2 ctxt2 in
      errorLogMonad_bind
        (match warn_p2 with
           SOME ls -> errorLogMonad_log (WarningErr (get_unreach_msg (panStatic_context_loc ctxt3)
                             (last_to_str ls) (panStatic_context_scope ctxt1)))
         | NONE -> errorLogMonad_return one) (\u.
      errorLogMonad_bind (static_check_prog ctxt3 prog2) (\pret2.
      errorLogMonad_return
        (prog_return_REC
           (prog_return_exits_fun pret1 \/ prog_return_exits_fun pret2)
           (prog_return_exits_loop pret1 \/ prog_return_exits_loop pret2)
           (seq_last_stmt (prog_return_last pret1) (prog_return_last pret2))
           (seq_loc_inf (prog_return_var_delta pret1) (prog_return_var_delta pret2))
           (prog_return_curr_loc pret2))))))) /\
   (static_check_prog ctxt (panLang_If exp prog1 prog2) =
      errorLogMonad_bind (static_check_exp ctxt exp) (\eret.
      errorLogMonad_bind
        (if ~(sh_bd_has_shape One (exp_return_sh_bd eret)) then
           errorLogMonad_error (ShapeErr (get_non_word_msg (implode "if condition")
             (sh_bd_to_str (exp_return_sh_bd eret)) (panStatic_context_loc ctxt)
             (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      errorLogMonad_bind (static_check_prog ctxt prog1) (\pret1.
      errorLogMonad_bind
        (static_check_prog
           (panStatic_context_loc_fupd (combin_K (prog_return_curr_loc pret1)) ctxt)
           prog2) (\pret2.
      let double_ret = (prog_return_exits_fun pret1 /\ prog_return_exits_fun pret2) in
      let double_loop_exit =
        (prog_return_exits_loop pret1 /\ prog_return_exits_loop pret2) in
      errorLogMonad_return
        (prog_return_REC double_ret double_loop_exit
           (branch_last_stmt double_ret double_loop_exit)
           (branch_loc_inf (panStatic_context_locals ctxt)
              (prog_return_var_delta pret1) (prog_return_var_delta pret2))
           (prog_return_curr_loc pret2))))))) /\
   (static_check_prog ctxt (While exp prog) =
      errorLogMonad_bind (static_check_exp ctxt exp) (\eret.
      errorLogMonad_bind
        (if ~(sh_bd_has_shape One (exp_return_sh_bd eret)) then
           errorLogMonad_error (ShapeErr (get_non_word_msg (implode "while condition")
             (sh_bd_to_str (exp_return_sh_bd eret)) (panStatic_context_loc ctxt)
             (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      errorLogMonad_bind
        (static_check_prog (panStatic_context_in_loop_fupd (combin_K T) ctxt) prog) (\pret.
      errorLogMonad_return
        (prog_return_REC F F OtherLast
           (branch_loc_inf (panStatic_context_locals ctxt) (prog_return_var_delta pret)
              (mlmap_empty mlstring_compare))
           (panStatic_context_loc ctxt)))))) /\
   (static_check_prog ctxt panLang_Break =
      errorLogMonad_bind
        (if ~(panStatic_context_in_loop ctxt) then
           errorLogMonad_error (GenErr (get_rogue_msg T (panStatic_context_loc ctxt)
                                          (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      errorLogMonad_return
        (prog_return_REC F T BreakLast (mlmap_empty mlstring_compare)
           (panStatic_context_loc ctxt)))) /\
   (static_check_prog ctxt panLang_Continue =
      errorLogMonad_bind
        (if ~(panStatic_context_in_loop ctxt) then
           errorLogMonad_error (GenErr (get_rogue_msg F (panStatic_context_loc ctxt)
                                          (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      errorLogMonad_return
        (prog_return_REC F T ContLast (mlmap_empty mlstring_compare)
           (panStatic_context_loc ctxt)))) /\
   (static_check_prog ctxt (panLang_Raise eid exp) =
      errorLogMonad_bind
        (match mlmap_lookup (panStatic_context_exns ctxt) eid with
           NONE -> errorLogMonad_error (ScopeErr (mlstring_concat [
                     implode "exception "; eid; implode " is not declared\n"]))
         | SOME sh -> errorLogMonad_return sh) (\sh.
      errorLogMonad_bind (static_check_exp ctxt exp) (\eret.
      errorLogMonad_bind
        (if ~(sh_bd_has_shape sh (exp_return_sh_bd eret)) then
           errorLogMonad_error (ShapeErr (mlstring_concat [
             implode "raised exception "; eid; implode " has wrong value shape\n"]))
         else errorLogMonad_return one) (\u.
      errorLogMonad_return
        (prog_return_REC T F RaiseLast (mlmap_empty mlstring_compare)
           (panStatic_context_loc ctxt)))))) /\
   (static_check_prog ctxt (panLang_Store addr exp) =
      errorLogMonad_bind (static_check_exp ctxt addr) (\aret.
      errorLogMonad_bind (static_check_exp ctxt exp) (\eret.
      errorLogMonad_bind
        (match exp_return_sh_bd aret with
           StructB _ ->
             errorLogMonad_error (ShapeErr (get_non_word_msg
               (implode "store address") (sh_bd_to_str (exp_return_sh_bd aret))
               (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         | NamedB _ _ ->
             errorLogMonad_error (ShapeErr (get_non_word_msg
               (implode "store address") (sh_bd_to_str (exp_return_sh_bd aret))
               (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         | WordB NotBased ->
             errorLogMonad_log (WarningErr (get_memop_msg T F F (panStatic_context_loc ctxt)
                                            (panStatic_context_scope ctxt)))
         | WordB NotTrusted ->
             errorLogMonad_log (WarningErr (get_memop_msg T F T (panStatic_context_loc ctxt)
                                            (panStatic_context_scope ctxt)))
         | _ -> errorLogMonad_return one) (\u.
      errorLogMonad_return
        (prog_return_REC F F OtherLast (mlmap_empty mlstring_compare)
           (panStatic_context_loc ctxt)))))) /\
   (static_check_prog ctxt (panLang_Store32 addr exp) =
      errorLogMonad_bind (static_check_exp ctxt addr) (\aret.
      errorLogMonad_bind (static_check_exp ctxt exp) (\eret.
      errorLogMonad_bind
        (match exp_return_sh_bd aret with
           StructB _ ->
             errorLogMonad_error (ShapeErr (get_non_word_msg
               (implode "store address") (sh_bd_to_str (exp_return_sh_bd aret))
               (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         | NamedB _ _ ->
             errorLogMonad_error (ShapeErr (get_non_word_msg
               (implode "store address") (sh_bd_to_str (exp_return_sh_bd aret))
               (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         | WordB NotBased ->
             errorLogMonad_log (WarningErr (get_memop_msg T F F (panStatic_context_loc ctxt)
                                            (panStatic_context_scope ctxt)))
         | WordB NotTrusted ->
             errorLogMonad_log (WarningErr (get_memop_msg T F T (panStatic_context_loc ctxt)
                                            (panStatic_context_scope ctxt)))
         | _ -> errorLogMonad_return one) (\u.
      errorLogMonad_bind
        (if ~(sh_bd_has_shape One (exp_return_sh_bd eret)) then
           errorLogMonad_error (ShapeErr (get_non_word_msg (implode "store value")
             (sh_bd_to_str (exp_return_sh_bd eret)) (panStatic_context_loc ctxt)
             (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      errorLogMonad_return
        (prog_return_REC F F OtherLast (mlmap_empty mlstring_compare)
           (panStatic_context_loc ctxt))))))) /\
   (static_check_prog ctxt (StoreByte addr exp) =
      errorLogMonad_bind (static_check_exp ctxt addr) (\aret.
      errorLogMonad_bind (static_check_exp ctxt exp) (\eret.
      errorLogMonad_bind
        (match exp_return_sh_bd aret with
           StructB _ ->
             errorLogMonad_error (ShapeErr (get_non_word_msg
               (implode "store address") (sh_bd_to_str (exp_return_sh_bd aret))
               (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         | NamedB _ _ ->
             errorLogMonad_error (ShapeErr (get_non_word_msg
               (implode "store address") (sh_bd_to_str (exp_return_sh_bd aret))
               (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         | WordB NotBased ->
             errorLogMonad_log (WarningErr (get_memop_msg T F F (panStatic_context_loc ctxt)
                                            (panStatic_context_scope ctxt)))
         | WordB NotTrusted ->
             errorLogMonad_log (WarningErr (get_memop_msg T F T (panStatic_context_loc ctxt)
                                            (panStatic_context_scope ctxt)))
         | _ -> errorLogMonad_return one) (\u.
      errorLogMonad_bind
        (if ~(sh_bd_has_shape One (exp_return_sh_bd eret)) then
           errorLogMonad_error (ShapeErr (get_non_word_msg (implode "store value")
             (sh_bd_to_str (exp_return_sh_bd eret)) (panStatic_context_loc ctxt)
             (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      errorLogMonad_return
        (prog_return_REC F F OtherLast (mlmap_empty mlstring_compare)
           (panStatic_context_loc ctxt))))))) /\
   (static_check_prog ctxt (ShMemLoad mop panLang_Local vname addr) =
      errorLogMonad_bind (check_local_var ctxt vname) (\vinf.
      errorLogMonad_bind (static_check_exp ctxt addr) (\aret.
      errorLogMonad_bind
        (match exp_return_sh_bd aret with
           StructB _ ->
             errorLogMonad_error (ShapeErr (get_non_word_msg
               (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
               (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         | NamedB _ _ ->
             errorLogMonad_error (ShapeErr (get_non_word_msg
               (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
               (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         | WordB Based ->
             errorLogMonad_log (WarningErr (get_memop_msg F T F (panStatic_context_loc ctxt)
                                            (panStatic_context_scope ctxt)))
         | WordB NotTrusted ->
             errorLogMonad_log (WarningErr (get_memop_msg F T T (panStatic_context_loc ctxt)
                                            (panStatic_context_scope ctxt)))
         | _ -> errorLogMonad_return one) (\u.
      errorLogMonad_bind
        (if ~(sh_bd_has_shape One (local_info_vsh_bd vinf)) then
           errorLogMonad_error (ShapeErr (get_non_word_msg (implode "load variable")
             (sh_bd_to_str (local_info_vsh_bd vinf)) (panStatic_context_loc ctxt)
             (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      errorLogMonad_return
        (prog_return_REC F F OtherLast
           (mlmap_singleton mlstring_compare vname
              (local_info_vsh_bd_fupd
                 (combin_K (sh_bd_from_bd Trusted (local_info_vsh_bd vinf))) vinf))
           (panStatic_context_loc ctxt))))))) /\
   (static_check_prog ctxt (ShMemLoad mop panLang_Global vname addr) =
      errorLogMonad_bind (check_global_var ctxt vname) (\vinf.
      errorLogMonad_bind (static_check_exp ctxt addr) (\aret.
      errorLogMonad_bind
        (match exp_return_sh_bd aret with
           StructB _ ->
             errorLogMonad_error (ShapeErr (get_non_word_msg
               (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
               (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         | NamedB _ _ ->
             errorLogMonad_error (ShapeErr (get_non_word_msg
               (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
               (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         | WordB Based ->
             errorLogMonad_log (WarningErr (get_memop_msg F T F (panStatic_context_loc ctxt)
                                            (panStatic_context_scope ctxt)))
         | WordB NotTrusted ->
             errorLogMonad_log (WarningErr (get_memop_msg F T T (panStatic_context_loc ctxt)
                                            (panStatic_context_scope ctxt)))
         | _ -> errorLogMonad_return one) (\u.
      errorLogMonad_bind
        (if ~(One = global_info_vshape vinf) then
           errorLogMonad_error (ShapeErr (get_non_word_msg (implode "load variable")
             (shape_to_str (global_info_vshape vinf)) (panStatic_context_loc ctxt)
             (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      errorLogMonad_return
        (prog_return_REC F F OtherLast (mlmap_empty mlstring_compare)
           (panStatic_context_loc ctxt))))))) /\
   (static_check_prog ctxt (ShMemStore mop addr exp) =
      errorLogMonad_bind (static_check_exp ctxt addr) (\aret.
      errorLogMonad_bind (static_check_exp ctxt exp) (\eret.
      errorLogMonad_bind
        (match exp_return_sh_bd aret with
           StructB _ ->
             errorLogMonad_error (ShapeErr (get_non_word_msg
               (implode "store address") (sh_bd_to_str (exp_return_sh_bd aret))
               (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         | NamedB _ _ ->
             errorLogMonad_error (ShapeErr (get_non_word_msg
               (implode "store address") (sh_bd_to_str (exp_return_sh_bd aret))
               (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
         | WordB Based ->
             errorLogMonad_log (WarningErr (get_memop_msg F F F (panStatic_context_loc ctxt)
                                            (panStatic_context_scope ctxt)))
         | WordB NotTrusted ->
             errorLogMonad_log (WarningErr (get_memop_msg F F T (panStatic_context_loc ctxt)
                                            (panStatic_context_scope ctxt)))
         | _ -> errorLogMonad_return one) (\u.
      errorLogMonad_bind
        (if ~(sh_bd_has_shape One (exp_return_sh_bd eret)) then
           errorLogMonad_error (ShapeErr (get_non_word_msg (implode "store value")
             (sh_bd_to_str (exp_return_sh_bd eret)) (panStatic_context_loc ctxt)
             (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      errorLogMonad_return
        (prog_return_REC F F OtherLast (mlmap_empty mlstring_compare)
           (panStatic_context_loc ctxt))))))) /\
   (static_check_prog ctxt panLang_Tick =
      errorLogMonad_return
        (prog_return_REC F F InvisLast (mlmap_empty mlstring_compare)
           (panStatic_context_loc ctxt))) /\
   (static_check_prog ctxt (Annot tag str) =
      let loc =
        if tag = implode "location" then
          mlstring_concat [implode "AT "; str; implode ": "]
        else panStatic_context_loc ctxt in
      errorLogMonad_return
        (prog_return_REC F F InvisLast (mlmap_empty mlstring_compare) loc))`;;

(* static_check_progs returns (unit) static_result.  A panStatic_context    *)
(* literal lists its fields in the order locals, globals, funcs, exns,      *)
(* structs, scope, in_loop, is_reachable, last, loc                         *)

let static_check_progs_def = cake_def_wf
  `MEASURE (\p:(mlstring,func_info)map#(mlstring,global_info)map#
               (mlstring#struct_info)list#(mlstring,shape)map#((A)decl)list.
              LENGTH (SND (SND (SND (SND p)))))`
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; SND]) THEN REWRITE_TAC[LENGTH; SND] THEN
   ASM_ARITH_TAC)
  `(static_check_progs fctxt gctxt sctxt ectxt ([]:((A)decl)list) =
      errorLogMonad_return one:(1,staterr)error#(staterr)list) /\
   (static_check_progs fctxt gctxt sctxt ectxt (CONS (Name _ _) decls) =
      static_check_progs fctxt gctxt sctxt ectxt decls) /\
   (static_check_progs fctxt gctxt sctxt ectxt (CONS (ExnDecl _ _) decls) =
      static_check_progs fctxt gctxt sctxt ectxt decls) /\
   (static_check_progs fctxt gctxt sctxt ectxt (CONS (Decl _ _ _) decls) =
      static_check_progs fctxt gctxt sctxt ectxt decls) /\
   (static_check_progs fctxt gctxt sctxt ectxt (CONS (Function fi) decls) =
      let (param_names,param_shapes) = UNZIP (fun_decl_params fi) in
      errorLogMonad_bind
        (match OPT_MMAP (sh_bd_from_sh sctxt Trusted) param_shapes with
           SOME sbs -> errorLogMonad_return (ZIP param_names sbs)
         | NONE -> errorLogMonad_error (ScopeErr (get_implementation_err_msg
             (implode "static analysis failed to convert in-scope shape")
             (implode "") (FunScope (fun_decl_name fi) (implode ""))))) (\param_sbs.
      let ctxt =
        panStatic_context_REC
          (FOLDL (\m (v,sb). mlmap_insert m v (local_info_REC sb))
                 (mlmap_empty mlstring_compare) param_sbs)
          gctxt fctxt ectxt sctxt
          (FunScope (fun_decl_name fi) (implode ""))
          F IsReach InvisLast (implode "") in
      errorLogMonad_bind (static_check_prog ctxt (fun_decl_body fi)) (\prog_ret.
      errorLogMonad_bind
        (if ~(prog_return_exits_fun prog_ret) then
           errorLogMonad_error (GenErr (mlstring_concat [
             implode "branches missing return statement in ";
             get_scope_desc (FunScope (fun_decl_name fi) (implode ""));
             implode "\n"]))
         else errorLogMonad_return one) (\u.
      static_check_progs fctxt gctxt sctxt ectxt decls))))`;;

(* static_check_decls returns ((varname, global_info) map, (funname,        *)
(* func_info) map) static_result.  As HOL4's do-block parses, in the case    *)
(* of a non-main function the else branch of if fi.export ends at its       *)
(* semicolon: the checks of the return shape and of its size follow for     *)
(* exported functions too                                                   *)

let static_check_decls_def = cake_def_wf
  `MEASURE (\p:(mlstring,func_info)map#(mlstring,global_info)map#
               (mlstring#struct_info)list#(mlstring,shape)map#((A)decl)list.
              LENGTH (SND (SND (SND (SND p)))))`
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; SND]) THEN REWRITE_TAC[LENGTH; SND] THEN
   ASM_ARITH_TAC)
  `(static_check_decls fctxt gctxt sctxt ectxt ([]:((A)decl)list) =
      errorLogMonad_return (fctxt,gctxt,ectxt)
        :((mlstring,func_info)map#(mlstring,global_info)map#(mlstring,shape)map,
          staterr)error#(staterr)list) /\
   (static_check_decls fctxt gctxt sctxt ectxt (CONS (Name _ _) decls) =
      static_check_decls fctxt gctxt sctxt ectxt decls) /\
   (static_check_decls fctxt gctxt sctxt ectxt (CONS (Decl shape vname exp) decls) =
      let ctxt =
        panStatic_context_REC
          (mlmap_empty mlstring_compare) gctxt (mlmap_empty mlstring_compare)
          ectxt sctxt (DeclScope vname) F IsReach InvisLast (implode "") in
      errorLogMonad_bind
        (check_redec_var (panStatic_context_scope_fupd (combin_K TopLevel) ctxt) vname) (\u.
      errorLogMonad_bind
        (check_shape sctxt (implode "") (panStatic_context_scope ctxt) shape) (\u.
      errorLogMonad_bind (static_check_exp ctxt exp) (\eret.
      errorLogMonad_bind
        (if ~(sh_bd_has_shape shape (exp_return_sh_bd eret)) then
           errorLogMonad_error (ShapeErr (get_shape_mismatch_msg
             (mlstring_concat [implode "expression to initialise global variable ";
                               vname])
             (sh_bd_to_str (exp_return_sh_bd eret)) (shape_to_str shape)
             (implode "") (panStatic_context_scope ctxt)))
         else errorLogMonad_return one) (\u.
      static_check_decls fctxt
        (mlmap_insert gctxt vname (global_info_REC shape)) sctxt ectxt decls))))) /\
   (static_check_decls fctxt gctxt sctxt ectxt (CONS (ExnDecl eid sh) decls) =
      errorLogMonad_bind
        (if mlmap_member eid ectxt then
           errorLogMonad_error (ScopeErr (mlstring_concat [
             implode "exception "; eid; implode " is redeclared\n"]))
         else errorLogMonad_return one) (\u.
      static_check_decls fctxt gctxt sctxt (mlmap_insert ectxt eid sh) decls)) /\
   (static_check_decls fctxt gctxt sctxt ectxt (CONS (Function fi) decls) =
      errorLogMonad_bind
        (if mlmap_member (fun_decl_name fi) fctxt then
           errorLogMonad_error (ScopeErr (get_redec_msg panStatic_Fun (implode "")
                                            (fun_decl_name fi) TopLevel))
         else errorLogMonad_return one) (\u.
      errorLogMonad_bind
        (if fun_decl_name fi = implode "main" then
           errorLogMonad_bind
             (if LENGTH (fun_decl_params fi) > 0 then
                errorLogMonad_error (GenErr (implode "main function has arguments\n"))
              else errorLogMonad_return one) (\u.
           errorLogMonad_bind
             (if fun_decl_export fi then
                errorLogMonad_error (GenErr (implode "main function is exported\n"))
              else errorLogMonad_return one) (\u.
           if ~(fun_decl_return fi = One) then
             errorLogMonad_error (ShapeErr (get_non_word_msg
               (implode "main function return") (shape_to_str (fun_decl_return fi))
               (implode "") (FunScope (fun_decl_name fi) (implode ""))))
           else errorLogMonad_return one))
         else
           errorLogMonad_bind
             (match first_repeat (sort mlstring_lt (MAP FST (fun_decl_params fi))) with
                SOME pname -> errorLogMonad_error (ScopeErr (mlstring_concat [
                    implode "parameter "; pname;
                    implode " is redeclared in function ";
                    fun_decl_name fi; implode "\n"]))
              | NONE -> errorLogMonad_return one) (\u.
           errorLogMonad_bind
             (if fun_decl_export fi then
                errorLogMonad_bind
                  (if LENGTH (fun_decl_params fi) > 4 then
                     errorLogMonad_error (GenErr (mlstring_concat [
                       implode "exported function "; fun_decl_name fi;
                       implode " has more than 4 arguments\n"]))
                   else errorLogMonad_return one) (\u.
                errorLogMonad_bind
                  (check_export_params (implode "")
                     (FunScope (fun_decl_name fi) (implode "")) (fun_decl_params fi))
                  (\u.
                if ~(fun_decl_return fi = One) then
                  errorLogMonad_error (ShapeErr (get_non_word_msg
                    (implode "exported function return")
                    (shape_to_str (fun_decl_return fi))
                    (implode "") (FunScope (fun_decl_name fi) (implode ""))))
                else errorLogMonad_return one))
              else
                check_id_shapes sctxt (implode "")
                  (FunScope (fun_decl_name fi) (implode "")) (fun_decl_params fi))
             (\u.
           errorLogMonad_bind
             (check_shape sctxt (implode "")
                (FunScope (fun_decl_name fi) (implode " return"))
                (fun_decl_return fi)) (\u.
           if size_of_sh_with_ctxt sctxt (fun_decl_return fi) > 32 then
             errorLogMonad_error (ShapeErr (mlstring_concat [
               implode "function "; fun_decl_name fi;
               implode " returns a shape bigger than 32 words\n"]))
           else errorLogMonad_return one)))) (\u.
      static_check_decls
        (mlmap_insert fctxt (fun_decl_name fi)
           (func_info_REC (fun_decl_return fi) (fun_decl_params fi)))
        gctxt sctxt ectxt decls)))`;;

(* static_check_names returns ((stcname # struct_info) list) static_result *)

let static_check_names_def = cake_def_wf
  `MEASURE (\p:(mlstring#struct_info)list#((A)decl)list. LENGTH (SND p))`
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; SND]) THEN REWRITE_TAC[LENGTH; SND] THEN
   ASM_ARITH_TAC)
  `(static_check_names sctxt ([]:((A)decl)list) =
      errorLogMonad_return sctxt
        :((mlstring#struct_info)list,staterr)error#(staterr)list) /\
   (static_check_names sctxt (CONS (Name name flds) decls) =
      errorLogMonad_bind
        (match ALOOKUP sctxt name with
           SOME info -> errorLogMonad_error (ScopeErr
                          (get_redec_msg Stc (implode "") name TopLevel))
         | NONE -> errorLogMonad_return one) (\u.
      errorLogMonad_bind
        (match first_repeat (sort mlstring_lt (MAP FST flds)) with
           SOME fld -> errorLogMonad_error (ScopeErr (mlstring_concat [
               implode "field "; fld; implode " is redeclared in struct name ";
               name; implode "\n"]))
         | NONE -> errorLogMonad_return one) (\u.
      errorLogMonad_bind
        (check_id_shapes sctxt (implode "") (StcScope name (implode "")) flds) (\u.
      let info =
        struct_info_REC flds (size_of_sh_with_ctxt sctxt (Comb (MAP SND flds))) in
      static_check_names (CONS (name,info) sctxt) decls)))) /\
   (static_check_names sctxt (CONS _ decls) = static_check_names sctxt decls)`;;

(* static_check returns (unit) static_result.  The static checker returns   *)
(* () if no error occurred, or the static error encountered, along with a   *)
(* list of warnings encountered (if any).  All warnings and errors come     *)
(* with a message containing the issue and its location                     *)

let static_check_def = cake_def
  `static_check (decls:((A)decl)list) =
     errorLogMonad_bind (static_check_names [] decls) (\sctxt.
     errorLogMonad_bind
       (static_check_decls (mlmap_empty mlstring_compare)
          (mlmap_empty mlstring_compare) sctxt (mlmap_empty mlstring_compare) decls)
       (\p. match p with
              (fctxt,gctxt,ectxt) -> static_check_progs fctxt gctxt sctxt ectxt decls))
       :(1,staterr)error#(staterr)list`;;
