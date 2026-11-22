(* ========================================================================= *)
(* pan_to_crep: port of HOL4 pancake/pan_to_crepScript.sml (CakeML v3479).   *)
(* Compilation from panLang to crepLang.                                     *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as notes/naming/names.tsv says: the record context is            *)
(*   pan_to_crep_context (fields pan_to_crep_context_vars, ..._funcs,       *)
(*   ..._eids, ..._vmax; constructor pan_to_crep_context_REC); compile_exp, *)
(*   compile, mk_ctxt, make_vmap, comp_func, make_funcs and compile_prog    *)
(*   get the prefix pan_to_crep_.                                            *)
(* - HOL4 GENLIST f n is list_of_seq f n; FOLDR MAX 0 l is ITLIST MAX l 0;  *)
(*   n2w is word, 0w is word 0; r.f is RECTYPE_f r; HOL4's                  *)
(*   ctxt with <|vars := X; vmax := Y|> is                                  *)
(*   pan_to_crep_context_vars_fupd (K X) (pan_to_crep_context_vmax_fupd     *)
(*   (K Y) ctxt); f $ x is f x; HOL4's sequential lets are nested lets.     *)
(* - compile_exp: the context has its own type variable B, as in HOL4      *)
(*   (nothing links the context's 'a to the expression's).                  *)
(* - Pattern variables that HOL4 names like an argument of another type    *)
(*   (e, es, e' in the arms of compile_exp's matches) are e1, es1, e2,      *)
(*   es2; clauses whose variables have different types in HOL4 (sh is a     *)
(*   shape and a shift in compile_exp, v a variable name and an expression  *)
(*   in compile) are parsed apart.                                           *)
(* - MAP2 and ZIP (HOL4's truncate, HOL Light's take HD/TL of the second    *)
(*   list): every use here is on lists of equal lengths (exp_hdl,           *)
(*   compile Assign under LENGTH ns = LENGTH es, get_eids_from_decls,       *)
(*   make_vmap: LENGTH (with_shape shs ns) = LENGTH shs).                    *)
(* - compile_exp and compile are defined with cake_let_cong (HOL4's         *)
(*   LET_CONG), so that their induction theorems have HOL4's hypotheses    *)
(*   (P ctxt e /\ P ctxt e' for Cmp, not P ctxt e' under a case on e); the *)
(*   trivial antecedents x = x that this leaves are removed by REWRITE_RULE.*)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/libext.ml";;
needs "compiler/backend/backend_common.ml";;
needs "pancake/pan_common.ml";;
needs "pancake/panLang.ml";;
needs "pancake/crepLang.ml";;
needs "pancake/crep_inline.ml";;

prioritize_num();;
type_invention_error := true;;

let pan_to_crep_context_INFO = cake_record "pan_to_crep_context"
  ["vars","(varname,shape#num list)fmap";
   "funcs","(funname,(varname#shape)list#shape)fmap";
   "eids","(eid,A word)fmap";
   "vmax","num"];;

let pan_to_crep_context_component_equality =
  (record_info "pan_to_crep_context").ri_component_equality;;

(* using this style to avoid using HD for code extraction later *)

let cexp_heads_def = cake_def
  `(cexp_heads ([]:(A list)list) = SOME []) /\
   (cexp_heads (CONS e es) =
      match (e,cexp_heads es) with
        ([],_) -> NONE
      | (_,NONE) -> NONE
      | (CONS x xs,SOME ys) -> SOME (CONS x ys))`;;

let comp_field_def = cake_def
  `(comp_field i [] (es:((A)crep_exp)list) = ([crep_Const (word 0)],One)) /\
   (comp_field i (CONS sh shs) es =
      if i = 0 then (TAKE (size_of_shape sh) es,sh)
      else comp_field (i - 1) shs (DROP (size_of_shape sh) es))`;;

let compile_panop_def = cake_def
  `compile_panop panLang_Mul = crep_Mul`;;

cake_let_cong := true;;
let pan_to_crep_compile_exp_def = cake_def_wf_clauses
  `measure (\p:(B)pan_to_crep_context#(A)panLang_exp.
              panLang_exp_size ARB (SND p))`
  TERM_TAC
  [`(pan_to_crep_compile_exp (ctxt:(B)pan_to_crep_context)
       (panLang_Const c:(A)panLang_exp) =
      ([crep_Const c:(A)crep_exp],One)) /\
   (pan_to_crep_compile_exp ctxt (panLang_Var panLang_Local vname) =
      match FLOOKUP (pan_to_crep_context_vars ctxt) vname with
        SOME (shape,ns) -> (MAP crep_Var ns,shape)
      | NONE -> ([crep_Const (word 0)],One)) /\
   (pan_to_crep_compile_exp ctxt (panLang_Var panLang_Global vname) =
      ([crep_Const (word 0)],One)) /\
   (pan_to_crep_compile_exp ctxt (RStruct es) =
      let cexps = MAP (pan_to_crep_compile_exp ctxt) es in
      (FLAT (MAP FST cexps),Comb (MAP SND cexps))) /\
   (pan_to_crep_compile_exp ctxt (RField index e) =
      let (cexp,shape) = pan_to_crep_compile_exp ctxt e in
      match shape with
        Comb shapes -> comp_field index shapes cexp
      | _ -> ([crep_Const (word 0)],One)) /\
   (pan_to_crep_compile_exp ctxt (NStruct nm flds) =
      ([crep_Const (word 0)],One)) /\
   (pan_to_crep_compile_exp ctxt (NField fld e) =
      ([crep_Const (word 0)],One)) /\
   (pan_to_crep_compile_exp ctxt (panLang_Load sh e) =
      let (cexp,shape) = pan_to_crep_compile_exp ctxt e in
      match cexp with
        CONS e1 es1 -> (load_shape (word 0) (size_of_shape sh) e1,sh)
      | _ -> ([crep_Const (word 0)],One)) /\
   (pan_to_crep_compile_exp ctxt (panLang_Load32 e) =
      let (cexp,shape) = pan_to_crep_compile_exp ctxt e in
      match (cexp,shape) with
        (CONS e1 es1,One) -> ([crep_Load32 e1],One)
      | (_,_) -> ([crep_Const (word 0)],One)) /\
   (pan_to_crep_compile_exp ctxt (LoadByte e) =
      let (cexp,shape) = pan_to_crep_compile_exp ctxt e in
      match (cexp,shape) with
        (CONS e1 es1,One) -> ([crep_LoadByte e1],One)
      | (_,_) -> ([crep_Const (word 0)],One)) /\
   (pan_to_crep_compile_exp ctxt (panLang_Op bop es) =
      let cexps = MAP FST (MAP (pan_to_crep_compile_exp ctxt) es) in
      match cexp_heads cexps with
        SOME es1 -> ([crep_Op bop es1],One)
      | _ -> ([crep_Const (word 0)],One)) /\
   (pan_to_crep_compile_exp ctxt (Panop pop es) =
      let cexps = MAP FST (MAP (pan_to_crep_compile_exp ctxt) es) in
      match cexp_heads cexps with
        SOME es1 -> ([Crepop (compile_panop pop) es1],One)
      | _ -> ([crep_Const (word 0)],One)) /\
   (pan_to_crep_compile_exp ctxt (Cmp cmp e e') =
      let ce = FST (pan_to_crep_compile_exp ctxt e) in
      let ce' = FST (pan_to_crep_compile_exp ctxt e') in
      match (ce,ce') with
        (CONS e1 es1,CONS e2 es2) -> ([crep_Cmp cmp e1 e2],One)
      | (_,_) -> ([crep_Const (word 0)],One))`;
   `(pan_to_crep_compile_exp (ctxt:(B)pan_to_crep_context)
       (panLang_Shift sh e e':(A)panLang_exp) =
      let ce = FST (pan_to_crep_compile_exp ctxt e) in
      let ce' = FST (pan_to_crep_compile_exp ctxt e') in
      match (ce,ce') with
        (CONS e1 es1,CONS e2 es2) -> ([crep_Shift sh e1 e2],One)
      | _ -> ([crep_Const (word 0)],One):((A)crep_exp)list#shape)`;
   `(pan_to_crep_compile_exp (ctxt:(B)pan_to_crep_context)
       (BaseAddr:(A)panLang_exp) =
      ([crep_BaseAddr:(A)crep_exp],One)) /\
   (pan_to_crep_compile_exp ctxt TopAddr = ([crep_TopAddr],One)) /\
   (pan_to_crep_compile_exp ctxt BytesInWord =
      ([crep_Const bytes_in_word],One))`];;
cake_let_cong := false;;
let pan_to_crep_compile_exp_ind =
  REWRITE_RULE[] (cake_ind "pan_to_crep_compile_exp");;

let () = cake_ind_store :=
  ("pan_to_crep_compile_exp",pan_to_crep_compile_exp_ind) :: !cake_ind_store;;

let exp_hdl_def = cake_def
  `exp_hdl (fm:(B,C#num list)fmap) v =
     match FLOOKUP fm v with
       NONE -> crep_Skip:(A)crep_prog
     | SOME (vshp,ns) ->
         crep_nested_seq
           (MAP2 crep_Assign ns (load_globals (word 0) (LENGTH ns)))`;;

let ret_var_def = cake_def_clauses
  [`ret_var One (ns:A list) = oHD ns`;
   `ret_var (Comb sh) (ns:A list) =
      if size_of_shape (Comb sh) = 1 then oHD ns else NONE`;
   `ret_var (Named sh) (ns:A list) = NONE:A option`];;

let ret_hdl_def = cake_def_clauses
  [`ret_hdl One (ns:num list) = crep_Skip:(A)crep_prog`;
   `ret_hdl (Comb sh) (ns:num list) =
      if 1 < size_of_shape (Comb sh) then assign_ret ns
      else crep_Skip:(A)crep_prog`;
   `ret_hdl (Named sh) (ns:num list) = crep_Skip:(A)crep_prog`];;

(* defining it with inner case to enable rewriting later *)

let wrap_rt_def = cake_def
  `wrap_rt (n:(shape#A list)option) =
     match n with
       NONE -> NONE
     | SOME (One,[]) -> NONE
     | m -> m`;;

cake_let_cong := true;;
let pan_to_crep_compile_def = cake_def_wf_clauses
  `measure (\p:(A)pan_to_crep_context#(A)panLang_prog.
              panLang_prog_size ARB (SND p))`
  TERM_TAC
  [`(pan_to_crep_compile (_:(A)pan_to_crep_context)
       (panLang_Skip:(A)panLang_prog) = crep_Skip:(A)crep_prog) /\
    (pan_to_crep_compile ctxt (Dec v s e p) =
       let (es,sh) = pan_to_crep_compile_exp ctxt e in
       let vmax = pan_to_crep_context_vmax ctxt in
       let nvars = list_of_seq (\x. vmax + SUC x) (size_of_shape sh) in
       let nctxt =
         pan_to_crep_context_vars_fupd
           (K (pan_to_crep_context_vars ctxt |+ (v,sh,nvars)))
           (pan_to_crep_context_vmax_fupd
              (K (pan_to_crep_context_vmax ctxt + size_of_shape sh)) ctxt) in
       if size_of_shape sh = LENGTH es
       then nested_decs nvars es (pan_to_crep_compile nctxt p)
       else crep_Skip) /\
    (pan_to_crep_compile ctxt (panLang_Assign panLang_Local v e) =
       let (es,sh) = pan_to_crep_compile_exp ctxt e in
       match FLOOKUP (pan_to_crep_context_vars ctxt) v with
         SOME (vshp,ns) ->
           if LENGTH ns = LENGTH es
           then if distinct_lists ns (FLAT (MAP var_cexp es))
                then crep_nested_seq (MAP2 crep_Assign ns es)
                else let vmax = pan_to_crep_context_vmax ctxt in
                     let temps = list_of_seq (\x. vmax + SUC x) (LENGTH ns) in
                     nested_decs temps es
                       (crep_nested_seq
                          (MAP2 crep_Assign ns (MAP crep_Var temps)))
           else crep_Skip
       | NONE -> crep_Skip) /\
    (pan_to_crep_compile ctxt (panLang_Assign panLang_Global v e) =
       crep_Skip) /\
    (pan_to_crep_compile ctxt (Primitive v pop es) =
       let cexps = MAP (pan_to_crep_compile_exp ctxt) es in
       let ces = FLAT (MAP FST cexps) in
       match FLOOKUP (pan_to_crep_context_vars ctxt) v with
         NONE -> crep_Skip
       | SOME (vshp,ns) ->
           let vmax = pan_to_crep_context_vmax ctxt in
           let temps = list_of_seq (\x. vmax + SUC x) (LENGTH ces) in
           nested_decs temps ces (crep_Primitive ns pop temps))`;
   `(pan_to_crep_compile (ctxt:(A)pan_to_crep_context)
       (panLang_Store ad v:(A)panLang_prog) =
       match pan_to_crep_compile_exp ctxt ad with
         (CONS e es',sh') ->
           let (es,sh) = pan_to_crep_compile_exp ctxt v in
           let adv = pan_to_crep_context_vmax ctxt + 1 in
           let temps = list_of_seq (\x. adv + SUC x) (size_of_shape sh) in
           if size_of_shape sh = LENGTH es
           then nested_decs (CONS adv temps) (CONS e es)
                  (crep_nested_seq
                     (stores (crep_Var adv) (MAP crep_Var temps) (word 0)))
           else crep_Skip:(A)crep_prog
       | (_,_) -> crep_Skip) /\
    (pan_to_crep_compile ctxt (panLang_Store32 dest src) =
       match (pan_to_crep_compile_exp ctxt dest,
              pan_to_crep_compile_exp ctxt src) with
         ((CONS ad ads,_),(CONS e es,_)) -> crep_Store32 ad e
       | _ -> crep_Skip) /\
    (pan_to_crep_compile ctxt (StoreByte dest src) =
       match (pan_to_crep_compile_exp ctxt dest,
              pan_to_crep_compile_exp ctxt src) with
         ((CONS ad ads,_),(CONS e es,_)) -> crep_StoreByte ad e
       | _ -> crep_Skip) /\
    (pan_to_crep_compile ctxt (panLang_Return rt) =
       let (ces,sh) = pan_to_crep_compile_exp ctxt rt in
       if size_of_shape sh = 0 then crep_Return [] else crep_Return ces) /\
    (pan_to_crep_compile ctxt (panLang_Raise eid excp) =
       match FLOOKUP (pan_to_crep_context_eids ctxt) eid with
         SOME n ->
           let (ces,sh) = pan_to_crep_compile_exp ctxt excp in
           let temps = list_of_seq (\x. pan_to_crep_context_vmax ctxt + SUC x)
                                   (size_of_shape sh) in
           if size_of_shape sh = LENGTH ces
           then crep_Seq
                  (nested_decs temps ces
                     (crep_nested_seq
                        (store_globals (word 0) (MAP crep_Var temps))))
                  (crep_Raise n)
           else crep_Skip
       | NONE -> crep_Skip) /\
    (pan_to_crep_compile ctxt (panLang_Seq p p') =
       crep_Seq (pan_to_crep_compile ctxt p) (pan_to_crep_compile ctxt p')) /\
    (pan_to_crep_compile ctxt (panLang_If e p p') =
       match pan_to_crep_compile_exp ctxt e with
         (CONS ce ces,_) ->
           crep_If ce (pan_to_crep_compile ctxt p) (pan_to_crep_compile ctxt p')
       | _ -> crep_Skip) /\
    (pan_to_crep_compile ctxt (While e p) =
       match pan_to_crep_compile_exp ctxt e with
         (CONS ce ces,_) -> crep_While ce (pan_to_crep_compile ctxt p)
       | _ -> crep_Skip) /\
    (pan_to_crep_compile ctxt panLang_Break = crep_Break 0) /\
    (pan_to_crep_compile ctxt panLang_Continue = crep_Continue 0)`;
   `(pan_to_crep_compile (ctxt:(A)pan_to_crep_context)
       (panLang_Call rtyp ce es:(A)panLang_prog) =
       let cexps = MAP (pan_to_crep_compile_exp ctxt) es in
       let args = FLAT (MAP FST cexps) in
       match rtyp with
         NONE -> crep_Call NONE ce args
       | SOME (NONE,hdl) ->
           let rts =
             (match FLOOKUP (pan_to_crep_context_funcs ctxt) ce with
                NONE -> []
              | SOME (args,rshape) ->
                  list_of_seq (\x. pan_to_crep_context_vmax ctxt + SUC x)
                              (size_of_shape rshape)) in
           (match hdl with
              NONE ->
                nested_decs rts (REPLICATE (LENGTH rts) (crep_Const (word 0)))
                  (crep_Call (SOME (rts,NONE)) ce args)
            | SOME (eid,evar,p) ->
                (match FLOOKUP (pan_to_crep_context_eids ctxt) eid with
                   NONE ->
                     nested_decs rts
                       (REPLICATE (LENGTH rts) (crep_Const (word 0)))
                       (crep_Call (SOME (rts,NONE)) ce args)
                 | SOME neid ->
                     let comp_hdl = pan_to_crep_compile ctxt p in
                     let hndlr =
                       crep_Seq (exp_hdl (pan_to_crep_context_vars ctxt) evar)
                                comp_hdl in
                     nested_decs rts
                       (REPLICATE (LENGTH rts) (crep_Const (word 0)))
                       (crep_Call (SOME (rts,SOME (neid,hndlr))) ce args)))
       | SOME (SOME (rk,rt),hdl) ->
           (match wrap_rt (FLOOKUP (pan_to_crep_context_vars ctxt) rt) with
              NONE ->
                (match hdl with
                   NONE -> crep_Call NONE ce args
                 | SOME (eid,evar,p) ->
                     (match FLOOKUP (pan_to_crep_context_eids ctxt) eid with
                        NONE -> crep_Call NONE ce args
                      | SOME neid ->
                          let comp_hdl = pan_to_crep_compile ctxt p in
                          let hndlr =
                            crep_Seq
                              (exp_hdl (pan_to_crep_context_vars ctxt) evar)
                              comp_hdl in
                          crep_Call (SOME ([],SOME (neid,hndlr))) ce args))
            | SOME (sh,ns) ->
                (match hdl with
                   NONE -> crep_Call (SOME (ns,NONE)) ce args
                 | SOME (eid,evar,p) ->
                     (match FLOOKUP (pan_to_crep_context_eids ctxt) eid with
                        NONE -> crep_Call (SOME (ns,NONE)) ce args
                      | SOME neid ->
                          let comp_hdl = pan_to_crep_compile ctxt p in
                          let hndlr =
                            crep_Seq
                              (exp_hdl (pan_to_crep_context_vars ctxt) evar)
                              comp_hdl in
                          crep_Call (SOME (ns,SOME (neid,hndlr))) ce args)))) /\
    (pan_to_crep_compile ctxt (DecCall v s ce es p) =
       let cexps = MAP (pan_to_crep_compile_exp ctxt) es in
       let args = FLAT (MAP FST cexps) in
       let vmax = pan_to_crep_context_vmax ctxt in
       let nvars = list_of_seq (\x. vmax + SUC x) (size_of_shape s) in
       let nctxt =
         pan_to_crep_context_vars_fupd
           (K (pan_to_crep_context_vars ctxt |+ (v,s,nvars)))
           (pan_to_crep_context_vmax_fupd
              (K (pan_to_crep_context_vmax ctxt + size_of_shape s)) ctxt) in
       let ret_dec =
         nested_decs nvars (REPLICATE (LENGTH nvars) (crep_Const (word 0))) in
       let p' = pan_to_crep_compile nctxt p in
       ret_dec (crep_Seq (crep_Call (SOME (nvars,NONE)) ce args) p'))`;
   `(pan_to_crep_compile (ctxt:(A)pan_to_crep_context)
       (panLang_ExtCall f ptr1 len1 ptr2 len2:(A)panLang_prog) =
       let (ptr1',sh1) = pan_to_crep_compile_exp ctxt ptr1 in
       let (len1',sh2) = pan_to_crep_compile_exp ctxt len1 in
       let (ptr2',sh3) = pan_to_crep_compile_exp ctxt ptr2 in
       let (len2',sh4) = pan_to_crep_compile_exp ctxt len2 in
       let n = ITLIST MAX (FLAT (MAP var_cexp
                                 (FLAT [ptr1'; len1'; ptr2'; len2']))) 0 in
       match ((sh1,ptr1'),(sh2,len1'),(sh3,ptr2'),(sh4,len2')) with
         ((One,CONS pc pcs),(One,CONS lc lcs),(One,CONS pc' pcs'),
          (One,CONS lc' lcs')) ->
           crep_Dec (n + 1) pc
             (crep_Dec (n + 2) lc
                (crep_Dec (n + 3) pc'
                   (crep_Dec (n + 4) lc'
                      (crep_ExtCall f (n + 1) (n + 2) (n + 3) (n + 4)))))
       | _ -> crep_Skip) /\
    (pan_to_crep_compile ctxt (ShMemStore op r ad) =
       match (pan_to_crep_compile_exp ctxt r,pan_to_crep_compile_exp ctxt ad)
       with
         ((CONS e _,_),(CONS a _,_)) ->
           let n = ITLIST MAX (var_cexp e) 0 in
           crep_Dec (n + 1) a (crep_ShMem (store_op op) (n + 1) e)
       | _ -> crep_Skip)`;
   `(pan_to_crep_compile (ctxt:(A)pan_to_crep_context)
       (ShMemLoad op panLang_Local r ad:(A)panLang_prog) =
       match pan_to_crep_compile_exp ctxt ad with
         (CONS a _,_) ->
           (match FLOOKUP (pan_to_crep_context_vars ctxt) r with
              SOME (_,CONS r' _) -> crep_ShMem (load_op op) r' a
            | _ -> crep_Skip)
       | _ -> crep_Skip:(A)crep_prog) /\
    (pan_to_crep_compile ctxt (ShMemLoad op panLang_Global r ad) =
       crep_Skip) /\
    (pan_to_crep_compile ctxt panLang_Tick = crep_Tick) /\
    (pan_to_crep_compile _ (Annot _ _) = crep_Skip)`];;
cake_let_cong := false;;

let pan_to_crep_compile_ind = REWRITE_RULE[] (cake_ind "pan_to_crep_compile");;

let () = cake_ind_store :=
  ("pan_to_crep_compile",pan_to_crep_compile_ind) :: !cake_ind_store;;

let pan_to_crep_mk_ctxt_def = cake_def
  `pan_to_crep_mk_ctxt vmap fs m (es:(eid,A word)fmap) =
     pan_to_crep_context_REC vmap fs es m`;;

(* params : (varname # shape) list *)

let pan_to_crep_make_vmap_def = cake_def
  `pan_to_crep_make_vmap (params:(B#shape)list) =
     let pvars = MAP FST params in
     let shs = MAP SND params in
     let ns = list_of_seq I (size_of_shape (Comb shs)) in
     let cvars = ZIP shs (with_shape shs ns) in
     FEMPTY |++ ZIP pvars cvars`;;

let pan_to_crep_comp_func_def = cake_def
  `pan_to_crep_comp_func fs (eids:(eid,A word)fmap) params body =
     let vmap = pan_to_crep_make_vmap params in
     let shapes = MAP SND params in
     let vmax = size_of_shape (Comb shapes) - 1 in
     pan_to_crep_compile (pan_to_crep_mk_ctxt vmap fs vmax eids) body`;;

(* extract eids from exception declarations *)

let get_eids_from_decls_def = cake_def
  `get_eids_from_decls (decls:((A)decl)list) =
     let eids = MAP FST (exceptions decls) in
     let ns = list_of_seq (\x. (word x):A word) (LENGTH eids) in
     let es = MAP2 (\x y. (x,y)) eids ns in
     alist_to_fmap es`;;

let pan_to_crep_make_funcs_def = cake_def
  `pan_to_crep_make_funcs (prog:(B#C#D#E)list) =
     let fnames = MAP FST prog in
     let params = MAP (FST o SND) prog in
     let returns = MAP (SND o SND o SND) prog in
     let fs = MAP3 (\x y z. (x,y,z)) fnames params returns in
     alist_to_fmap fs`;;

let crep_vars_def = cake_def
  `crep_vars (params:(B#shape)list) =
     let shapes = MAP SND params in
     let len = size_of_shape (Comb shapes) in
     list_of_seq I len`;;

let compile_to_crep_def = cake_def
  `compile_to_crep (decls:((A)decl)list) =
     let prog = functions decls in
     let comp = pan_to_crep_comp_func (pan_to_crep_make_funcs prog)
                                      (get_eids_from_decls decls) in
     MAP (\(name,params,body,return).
            (name,crep_vars params,comp params body)) prog`;;

let pan_to_crep_compile_prog_def = cake_def
  `pan_to_crep_compile_prog (prog:((A)decl)list) =
     let inl_fs_names = MAP FST (functions (FILTER inlinable prog)) in
     let to_crep = compile_to_crep prog in
     compile_inl_top inl_fs_names to_crep`;;
