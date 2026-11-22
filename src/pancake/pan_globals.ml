(* ========================================================================= *)
(* pan_globals: port of HOL4 pancake/pan_globalsScript.sml (CakeML v3479).   *)
(* Allocate globals at the end of heap.                                      *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as notes/naming/names.tsv says: the record context is            *)
(*   pan_globals_context (fields pan_globals_context_globals, ..._size,     *)
(*   ..._max_globals_size); compile_exp, compile, compile_decs and          *)
(*   compile_top get the prefix pan_globals_.                               *)
(* - The definitions with a catch-all clause over exp or prog (compile_exp, *)
(*   compile, fperm) are made with sem1aux_def(_wf) (HOL4's TFL completion  *)
(*   of catch-all clauses; semantics/sem1aux_tfl.ml), as panLang does.      *)
(* - strlit s is implode s, s1 ^ s2 is strcat s1 s2; n2w is word; ++ is     *)
(*   APPEND (left associative); TailCall is panLang_Call NONE.              *)
(* - HOL4's sequential let x = a; y = b in t is written as nested lets.     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "pancake/panLang.ml";;
needs "compiler/backend/backend_common.ml";;

prioritize_num();;
type_invention_error := true;;

let pan_globals_context_INFO = cake_record "pan_globals_context"
  ["globals","(mlstring,shape#A word)fmap";
   "globals_size","A word";
   "max_globals_size","A word"];;

let pan_globals_context_component_equality =
  (record_info "pan_globals_context").ri_component_equality;;

(* HOL4 Termination: measure (\e. exp_size ARB (SND e)), then MEM_IMP_exp_size *)

let pan_globals_compile_exp_def = sem1aux_def_wf
  `measure (\e:(A)pan_globals_context#(A)panLang_exp.
              panLang_exp_size ARB (SND e))`
  SEM1AUX_TC_TAC
  (list_mk_conj
   [`(pan_globals_compile_exp (ctxt:(A)pan_globals_context)
        (panLang_Var panLang_Local vname:(A)panLang_exp) =
        panLang_Var panLang_Local vname) /\
     (pan_globals_compile_exp ctxt (panLang_Var panLang_Global vname) =
        match FLOOKUP (pan_globals_context_globals ctxt) vname with
          NONE -> panLang_Const (word 0)
        | SOME (sh,addr) ->
            panLang_Load sh (panLang_Op asm_Sub [TopAddr; panLang_Const addr])) /\
     (pan_globals_compile_exp ctxt (RStruct es) =
        RStruct (MAP (pan_globals_compile_exp ctxt) es)) /\
     (pan_globals_compile_exp ctxt (RField index e) =
        RField index (pan_globals_compile_exp ctxt e)) /\
     (pan_globals_compile_exp ctxt (NStruct nm flds) = panLang_Const (word 0)) /\
     (pan_globals_compile_exp ctxt (NField fld e) = panLang_Const (word 0)) /\
     (pan_globals_compile_exp ctxt (panLang_Load sh e) =
        panLang_Load sh (pan_globals_compile_exp ctxt e)) /\
     (pan_globals_compile_exp ctxt (LoadByte e) =
        LoadByte (pan_globals_compile_exp ctxt e)) /\
     (pan_globals_compile_exp ctxt (panLang_Load32 e) =
        panLang_Load32 (pan_globals_compile_exp ctxt e)) /\
     (pan_globals_compile_exp ctxt (panLang_Op bop es) =
        panLang_Op bop (MAP (pan_globals_compile_exp ctxt) es)) /\
     (pan_globals_compile_exp ctxt (Panop pop es) =
        Panop pop (MAP (pan_globals_compile_exp ctxt) es)) /\
     (pan_globals_compile_exp ctxt (Cmp cmp e e') =
        Cmp cmp (pan_globals_compile_exp ctxt e)
                (pan_globals_compile_exp ctxt e'))`;
    `(pan_globals_compile_exp (ctxt:(A)pan_globals_context)
        (panLang_Shift sh e e') =
        panLang_Shift sh (pan_globals_compile_exp ctxt e)
                         (pan_globals_compile_exp ctxt e')) /\
     (pan_globals_compile_exp ctxt TopAddr =
        panLang_Op asm_Sub
          [TopAddr; panLang_Const (pan_globals_context_max_globals_size ctxt)]) /\
     (pan_globals_compile_exp ctxt e = e)`]);;

let pan_globals_compile_exp_ind = cake_ind "pan_globals_compile_exp";;

(* HOL4 Termination: measure (\(name,names). 1 + MAX_SET (IMAGE strlen (set *)
(* names)) - strlen name), with MAX_SET_PROPERTY (here X_LE_MAX_SET)       *)

let fresh_name_def = cake_def_wf
  `measure (\(name:mlstring,names:mlstring list).
              (1 + MAX_SET (IMAGE strlen (set_of_list names))) - strlen name)`
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `strlen name <= MAX_SET (IMAGE strlen (set_of_list names))`
     MP_TAC THENL
    [MP_TAC(ISPEC `IMAGE strlen (set_of_list (names:mlstring list))`
                   X_LE_MAX_SET) THEN
     SIMP_TAC[FINITE_IMAGE; FINITE_SET_OF_LIST; IN_IMAGE; IN_SET_OF_LIST] THEN
     ASM_MESON_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[measure_THM] THEN
   CONV_TAC(TOP_DEPTH_CONV(BETA_CONV ORELSEC GEN_BETA_CONV)) THEN
   REWRITE_TAC[strlen_strcat; strlen_implode; LENGTH] THEN ARITH_TAC)
  `fresh_name name names =
     if MEM name names then fresh_name (strcat name (implode "'")) names
     else name`;;

let fresh_name_ind = cake_ind "fresh_name";;

(* the clauses are parsed in groups: v is a variable name in Dec and an     *)
(* expression in Store, e an expression in Dec and a function name in Call, *)
(* r an expression in ShMemStore and a variable name in ShMemLoad            *)

let pan_globals_compile_def = sem1aux_def
  (list_mk_conj
   [`(pan_globals_compile (ctxt:(A)pan_globals_context) (Dec v s e p) =
        Dec v s (pan_globals_compile_exp ctxt e) (pan_globals_compile ctxt p)) /\
     (pan_globals_compile ctxt (panLang_Assign vk v e) =
        match vk with
          panLang_Global ->
            (match FLOOKUP (pan_globals_context_globals ctxt) v with
               NONE -> panLang_Skip
             | SOME (sh,addr) ->
                 panLang_Store (panLang_Op asm_Sub [TopAddr; panLang_Const addr])
                               (pan_globals_compile_exp ctxt e))
        | _ -> panLang_Assign panLang_Local v (pan_globals_compile_exp ctxt e)) /\
     (pan_globals_compile ctxt (Primitive v pop es) =
        Primitive v pop (MAP (pan_globals_compile_exp ctxt) es))`;
    `(pan_globals_compile (ctxt:(A)pan_globals_context) (panLang_Store ad v) =
        panLang_Store (pan_globals_compile_exp ctxt ad)
                      (pan_globals_compile_exp ctxt v)) /\
     (pan_globals_compile ctxt (panLang_Store32 ad v) =
        panLang_Store32 (pan_globals_compile_exp ctxt ad)
                        (pan_globals_compile_exp ctxt v)) /\
     (pan_globals_compile ctxt (StoreByte dest src) =
        StoreByte (pan_globals_compile_exp ctxt dest)
                  (pan_globals_compile_exp ctxt src)) /\
     (pan_globals_compile ctxt (panLang_Return rt) =
        panLang_Return (pan_globals_compile_exp ctxt rt)) /\
     (pan_globals_compile ctxt (panLang_Raise eid excp) =
        panLang_Raise eid (pan_globals_compile_exp ctxt excp)) /\
     (pan_globals_compile ctxt (panLang_Seq p p') =
        panLang_Seq (pan_globals_compile ctxt p) (pan_globals_compile ctxt p')) /\
     (pan_globals_compile ctxt (panLang_If e p p') =
        panLang_If (pan_globals_compile_exp ctxt e) (pan_globals_compile ctxt p)
                   (pan_globals_compile ctxt p')) /\
     (pan_globals_compile ctxt (While e p) =
        While (pan_globals_compile_exp ctxt e) (pan_globals_compile ctxt p))`;
    `pan_globals_compile (ctxt:(A)pan_globals_context) (panLang_Call rtyp e es) =
       let cexps = MAP (pan_globals_compile_exp ctxt) es in
       match rtyp with
         NONE -> panLang_Call NONE e cexps
       | SOME (SOME (panLang_Global,vn),hdl) ->
           (match FLOOKUP (pan_globals_context_globals ctxt) vn with
              NONE ->
                panLang_Call
                  (SOME (NONE,
                         match hdl with
                           NONE -> NONE
                         | SOME (eid,evar,p) ->
                             SOME (eid,evar,pan_globals_compile ctxt p)))
                  e cexps
            | SOME (sh,addr) ->
                (match hdl with
                   NONE ->
                     DecCall (implode "") sh e cexps
                       (panLang_Store
                          (panLang_Op asm_Sub [TopAddr; panLang_Const addr])
                          (panLang_Var panLang_Local (implode "")))
                 | SOME (eid,evar,p) ->
                     let p' = pan_globals_compile ctxt p in
                     let names = APPEND (CONS evar (free_var_ids p'))
                                        (FLAT (MAP var_exp cexps)) in
                     let vn' = fresh_name (implode "") names in
                     let flag = fresh_name (implode "vn'") (CONS vn' names) in
                     Dec vn' sh (shape_val sh)
                       (Dec flag One (panLang_Const (word 0))
                          (panLang_Seq
                             (panLang_Call
                                (SOME (SOME (panLang_Local,vn'),
                                       SOME (eid,evar,
                                             panLang_Seq p'
                                               (panLang_Assign panLang_Local flag
                                                  (panLang_Const (word 1))))))
                                e cexps)
                             (panLang_If (panLang_Var panLang_Local flag) panLang_Skip
                                (panLang_Store
                                   (panLang_Op asm_Sub [TopAddr; panLang_Const addr])
                                   (panLang_Var panLang_Local vn')))))))
       | SOME (tl,hdl) ->
           panLang_Call
             (SOME (tl,
                    match hdl with
                      NONE -> NONE
                    | SOME (eid,evar,p) -> SOME (eid,evar,pan_globals_compile ctxt p)))
             e cexps`;
    `(pan_globals_compile (ctxt:(A)pan_globals_context) (DecCall v s e es p) =
        DecCall v s e (MAP (pan_globals_compile_exp ctxt) es)
                (pan_globals_compile ctxt p)) /\
     (pan_globals_compile ctxt (panLang_ExtCall f ptr1 len1 ptr2 len2) =
        panLang_ExtCall f
          (pan_globals_compile_exp ctxt ptr1)
          (pan_globals_compile_exp ctxt len1)
          (pan_globals_compile_exp ctxt ptr2)
          (pan_globals_compile_exp ctxt len2)) /\
     (pan_globals_compile ctxt (ShMemStore op r ad) =
        ShMemStore op (pan_globals_compile_exp ctxt r)
                      (pan_globals_compile_exp ctxt ad))`;
    `(pan_globals_compile (ctxt:(A)pan_globals_context)
        (ShMemLoad op panLang_Local r ad) =
        ShMemLoad op panLang_Local r (pan_globals_compile_exp ctxt ad)) /\
     (pan_globals_compile ctxt (ShMemLoad op panLang_Global r ad) =
        match FLOOKUP (pan_globals_context_globals ctxt) r with
          SOME (One,addr) ->
            (let r' = strcat r (implode "'") in
             Dec r One (pan_globals_compile_exp ctxt ad)
               (Dec r' One (panLang_Const (word 0))
                  (panLang_Seq (ShMemLoad op panLang_Local r'
                                  (panLang_Var panLang_Local r))
                     (panLang_Store
                        (panLang_Op asm_Sub [TopAddr; panLang_Const addr])
                        (panLang_Var panLang_Local r')))))
        | _ -> panLang_Skip) /\
     (pan_globals_compile _ p = p)`]);;

let pan_globals_compile_ind = cake_ind "pan_globals_compile";;

(* HOL4 ctxt with <| globals := g; globals_size := s |> is                   *)
(* pan_globals_context_globals_fupd (K g)                                   *)
(*   (pan_globals_context_globals_size_fupd (K s) ctxt)                     *)

let pan_globals_compile_decs_def = cake_def
  `(pan_globals_compile_decs (ctxt:(A)pan_globals_context) [] =
      ([],[]:((A)decl)list,[]:((A)decl)list,ctxt)) /\
   (pan_globals_compile_decs ctxt (CONS (Decl sh v e) ds) =
      let s = word_add (pan_globals_context_globals_size ctxt)
                       (word_mul bytes_in_word (word (size_of_shape sh))) in
      let ctxt' = pan_globals_context_globals_fupd
                    (K (pan_globals_context_globals ctxt |+ (v,sh,s)))
                    (pan_globals_context_globals_size_fupd (K s) ctxt) in
      let (decs,funs,exns,ctxt'') = pan_globals_compile_decs ctxt' ds in
      (CONS (panLang_Store (panLang_Op asm_Sub [TopAddr; panLang_Const s])
                           (pan_globals_compile_exp ctxt e)) decs,
       funs,exns,ctxt'')) /\
   (pan_globals_compile_decs ctxt (CONS (Function fi) ds) =
      let (decs,funs,exns,ctxt'') = pan_globals_compile_decs ctxt ds in
      (decs,
       CONS (Function (fun_decl_body_fupd
                         (K (pan_globals_compile ctxt (fun_decl_body fi))) fi))
            funs,
       exns,ctxt'')) /\
   (pan_globals_compile_decs ctxt (CONS (ExnDecl eid sh) ds) =
      let (decs,funs,exns,ctxt'') = pan_globals_compile_decs ctxt ds in
      (decs,funs,CONS (ExnDecl eid sh) exns,ctxt'')) /\
   (pan_globals_compile_decs ctxt (CONS (Name nm flds) ds) =
      pan_globals_compile_decs ctxt ds)`;;

let pan_globals_compile_decs_ind = cake_ind "pan_globals_compile_decs";;

let resort_decls_def = cake_def
  `resort_decls (decs:((A)decl)list) =
     APPEND (APPEND (APPEND (FILTER is_name decs) (FILTER is_exn_decl decs))
                    (FILTER is_decl decs))
            (FILTER is_function decs)`;;

let fperm_name_def = cake_def
  `fperm_name (f:A) g h = if f = h then g else if g = h then f else h`;;

(* e is an expression in Dec, If, While and a function name in Call, DecCall *)

let fperm_def = sem1aux_def
  (list_mk_conj
   [`(fperm (f:mlstring) (g:mlstring) (Dec v s (e:(A)panLang_exp) p) =
        Dec v s e (fperm f g p)) /\
     (fperm f g (panLang_Seq p p') = panLang_Seq (fperm f g p) (fperm f g p')) /\
     (fperm f g (panLang_If e p p') =
        panLang_If e (fperm f g p) (fperm f g p')) /\
     (fperm f g (While e p) = While e (fperm f g p))`;
    `(fperm f g (panLang_Call rtyp e (es:((A)panLang_exp)list)) =
        panLang_Call
          (match rtyp with
             NONE -> NONE
           | SOME (tl,hdl) ->
               SOME (tl,
                     match hdl with
                       NONE -> NONE
                     | SOME (eid,evar,p) -> SOME (eid,evar,fperm f g p)))
          (fperm_name f g e) es) /\
     (fperm f g (DecCall v s e es p) =
        DecCall v s (fperm_name f g e) es (fperm f g p)) /\
     (fperm _ _ p = p)`]);;

let fperm_ind = cake_ind "fperm";;

let fperm_decs_def = cake_def
  `(fperm_decs f g ([]:((A)decl)list) = []) /\
   (fperm_decs f g (CONS (Function fi) decs) =
      CONS (Function (fun_decl_name_fupd (K (fperm_name f g (fun_decl_name fi)))
                        (fun_decl_body_fupd (K (fperm f g (fun_decl_body fi))) fi)))
           (fperm_decs f g decs)) /\
   (fperm_decs f g (CONS d decs) = CONS d (fperm_decs f g decs))`;;

let fperm_decs_ind = cake_ind "fperm_decs";;

let new_main_name_def = cake_def
  `new_main_name (decls:((A)decl)list) =
     fresh_name (implode "main") (MAP FST (functions decls))`;;

let dec_shapes_def = cake_def
  `(dec_shapes (CONS (Function _) ds) = dec_shapes ds) /\
   (dec_shapes (CONS (Decl sh _ _) ds) = CONS sh (dec_shapes ds)) /\
   (dec_shapes (CONS (Name _ _) ds) = dec_shapes ds) /\
   (dec_shapes (CONS (ExnDecl _ _) ds) = dec_shapes ds) /\
   (dec_shapes ([]:((A)decl)list) = [])`;;

let dec_shapes_ind = cake_ind "dec_shapes";;

(* HOL4 record literals: <| globals := FEMPTY; globals_size := 0w;          *)
(* max_globals_size := m |> is pan_globals_context_REC FEMPTY (word 0) m,    *)
(* and the fun_decl literal fun_decl_REC name inline export params body     *)
(* return; TailCall start' params is panLang_Call NONE start' params         *)

let pan_globals_compile_top_def = cake_def
  `pan_globals_compile_top (decs:((A)decl)list) start =
     match ALOOKUP (functions decs) start with
       NONE -> []
     | SOME (args,body,rshape) ->
         let nds = resort_decls decs in
         let start' = new_main_name decs in
         let nds' = fperm_decs start start' nds in
         let (decls,funs,exns,ctxt) =
           pan_globals_compile_decs
             (pan_globals_context_REC FEMPTY (word 0)
                (word_mul bytes_in_word
                   (word (SUM (MAP size_of_shape (dec_shapes nds'))))))
             nds' in
         let params = MAP (panLang_Var panLang_Local o FST) args in
         let new_main =
           Function (fun_decl_REC start F F args
                       (panLang_Seq (nested_seq decls)
                                    (panLang_Call NONE start' params))
                       rshape) in
         APPEND exns (CONS new_main funs)`;;
