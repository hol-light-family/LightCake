(* ========================================================================= *)
(* pan_passes: port of HOL4 pancake/pan_passesScript.sml (CakeML v3479).     *)
(* Reformulates compile definition to expose the result of each internal    *)
(* compiler pass.                                                            *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: the any_pan_prog constructors             *)
(*   Pan, Crep, pan_passes_Loop and Cake; the local lemma MAP2_MAP is       *)
(*   pan_passes_MAP2_MAP.                                                    *)
(* - mlstring literals are implode "..."; HOL4's Overloads list_to_display *)
(*   and option_to_display (presLang) are written out where they are used, *)
(*   as presLang.ml does; o is function composition.                        *)
(* - HOL4's paired lambdas in recursive positions are written              *)
(*   \p. match p with (a,b) -> t (pair_CASE, HOL4's UNCURRY); the others    *)
(*   are HOL Light paired lambdas.                                           *)
(* - The termination measures are HOL4's in effect (the program sizes),     *)
(*   written with SND and FST instead of paired lambdas.                     *)
(* - HOL4's MAP2 and ZIP truncate the longer list; HOL Light's take the     *)
(*   length of the first list (HD/TL of the second).  pan_to_target_all     *)
(*   uses them on lists of equal lengths (GENLIST of LENGTH prog_b; the     *)
(*   function numbers and names, see pan_to_target.ml), so the definition   *)
(*   is HOL4's.  The local lemma MAP2_MAP gets the hypothesis                *)
(*   LENGTH xs <= LENGTH ys (its use has equal lengths).                     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mllist.ml";;
needs "pancake/pan_to_target.ml";;
needs "compiler/backend/backend_passes.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/presLang.ml";;

prioritize_num();;
type_invention_error := true;;

let any_pan_prog_INDUCT,any_pan_prog_RECURSION = cake_type
  "any_pan_prog = Pan (((A)decl)list)
                | Crep ((mlstring # num list # (A)crep_prog) list)
                | pan_passes_Loop ((num # num list # (A)loop_prog) list) (mlstring spt)
                | Cake ((A)any_prog)";;

let pan_to_target_all_def = cake_def
  `pan_to_target_all (asm_conf:(A)asm_config) (c:backend_config) (prog:((A)decl)list) =
     let prog1 =
       (match SPLITP (\x. match x with
                            Function fi -> fun_decl_name fi = implode "main"
                          | _ -> F) prog with
          ([],ys) -> ys
        | (xs,[]) ->
            CONS (Function (fun_decl_REC (implode "main") F F []
                              (panLang_Return (panLang_Const (word 0))) One)) xs
        | (xs,CONS y ys) -> APPEND (CONS y xs) ys) in
     let ps = [(implode "initial pancake program",Pan prog1)] in
     let prog_a0 = pan_simp_compile_prog prog1 in
     let ps = APPEND ps [(implode "after pan_simp",Pan prog_a0)] in
     let prog_a1 = pan_structs_compile_top prog_a0 in
     let ps = APPEND ps [(implode "after pan_structs",Pan prog_a1)] in
     let prog_a = pan_globals_compile_top prog_a1 (implode "main") in
     let ps = APPEND ps [(implode "after pan_globals",Pan prog_a)] in
     let prog_b0 = compile_to_crep prog_a in
     let ps = APPEND ps [(implode "after pan_to_crep",Crep prog_b0)] in
     let inl_fs_names = MAP FST (functions (FILTER inlinable prog_a)) in
     let prog_bi = compile_inl_top inl_fs_names prog_b0 in
     let ps = APPEND ps [(implode "after crep_inline",Crep prog_bi)] in
     let prog_b = MAP (\(n,ps,e). (n,ps,simp_prog e)) prog_bi in
     let ps = APPEND ps [(implode "after crep_arith",Crep prog_b)] in
     let fnums = list_of_seq (\n. n + first_name) (LENGTH prog_b) in
     let funcs = crep_to_loop_make_funcs prog_b in
     let target = asm_config_ISA asm_conf in
     let comp = crep_to_loop_comp_func target funcs in
     let prog_b1 = MAP2 (\n (name,params,body).
                           (n,(list_of_seq I o LENGTH) params,comp params body))
                        fnums prog_b in
     let prog_c = MAP (\(name,params,body). (name,params,optimise body)) prog_b1 in
     let prog2 = loop_to_word_compile_prog prog_c in
     let names = fromAList (ZIP (sort (<) (MAP FST prog2))
                                (CONS (implode "generated_main")
                                      (MAP FST (functions prog1)))) in
     let names = sptree_union (fromAList (APPEND (APPEND (word_to_stack_stub_names one)
                                                  (stack_alloc_stub_names one))
                                          (stack_remove_stub_names one))) names in
     let ps = APPEND ps [(implode "after crep_to_loop",pan_passes_Loop prog_b1 names)] in
     let ps = APPEND ps [(implode "after loop_optimise",pan_passes_Loop prog_c names)] in
     let ps = APPEND ps [(implode "after loop_to_word",
                          Cake (backend_passes_Word prog2 names))] in
     let c = backend_config_exported_fupd (K (exports prog)) c in
     let (ps1,out) = from_word_0_all [] asm_conf c names prog2 in
     (APPEND ps (MAP (\(n,p). (n,Cake p)) ps1),out)`;;

(* HOL4: MAP2_MAP (local).  HOL Light's MAP2 takes HD and TL of its second *)
(* list: the hypothesis LENGTH xs <= LENGTH ys (equal lengths at its use).  *)

let pan_passes_MAP2_MAP = prove
 (`!(g:A->B->C) (f:D->B) xs ys.
     LENGTH xs <= LENGTH ys ==>
     MAP2 g xs (MAP f ys) = MAP2 (\x y. g x (f y)) xs ys`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP2_DEF] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; MAP; HD; TL; LE_SUC; ARITH_RULE `~(SUC n <= 0)`] THEN
  ASM_SIMP_TAC[]);;

(* HOL4: MAP_MAP2 (local) *)

let MAP_MAP2 = prove
 (`!(f:C->D) (g:A->B->C) xs ys.
     MAP f (MAP2 g xs ys) = MAP2 (\x y. f (g x y)) xs ys`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP2_DEF; MAP]);;

(* HOL4: make_funcs_MAP (local) *)

let make_funcs_MAP = prove
 (`!(f:(A)crep_prog->(A)crep_prog) xs.
     crep_to_loop_make_funcs (MAP (\(n,ps,e). (n,ps,f e)) xs) =
     crep_to_loop_make_funcs xs`,
  REWRITE_TAC[crep_to_loop_make_funcs_def; LENGTH_MAP; MAP_MAP_o] THEN
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `(FST o (\(n,ps,e). n,ps,(f:(A)crep_prog->(A)crep_prog) e)) =
      (FST:mlstring#num list#(A)crep_prog->mlstring) /\
    ((LENGTH o FST o SND) o (\(n,ps,e). n,ps,(f:(A)crep_prog->(A)crep_prog) e)) =
      ((LENGTH o FST o SND):mlstring#num list#(A)crep_prog->num)`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]);;

(* helpers of compile_prog_eq_pan_to_target_all: the program prog1 of both *)
(* sides made a variable, the SND of the last pass, the function of the    *)
(* MAP2 of crep_to_loop_compile_prog                                       *)

let PTOPAUX_GEN_LET_TAC : tactic = fun (asl,w as g) ->
  let t = find_term is_let w in
  let (v,e) = hd (fst (dest_let t)) in
  SPEC_TAC(e, v) g;;

let PTOPAUX_SND_pair_CASE = prove
 (CASE_TERM `!(x:A#B) (f:A->C). SND (match x with (a,b) -> (f a,b)) = SND x`,
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; SND]);;

let PTOPAUX_MAP2_FUN_EQ = prove
 (`!(comp:num list->(A)crep_prog->(A)loop_prog).
     (\(n:num) (name:mlstring,params,body).
        (n,(list_of_seq I o LENGTH) params, optimise (comp params (simp_prog body)))) =
     (\(x:num) y. (\(name,params,body). (name,params,optimise body))
              ((\(name,params,body). (x,(list_of_seq I o LENGTH) params, comp params body))
               ((\(n,ps,e). (n,ps,simp_prog e)) y)))`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let compile_prog_eq_pan_to_target_all = prove
 (`!(asm_conf:(A)asm_config) c p.
     pan_to_target_compile_prog asm_conf c p = SND (pan_to_target_all asm_conf c p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_prog_eq; pan_to_target_all_def] THEN
  PTOPAUX_GEN_LET_TAC THEN GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PTOPAUX_SND_pair_CASE; from_word_0_thm] THEN
  REWRITE_TAC[pan_to_word_compile_prog_def; loop_to_word_compile_def;
              crep_to_loop_compile_prog_def; pan_to_crep_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MAP_MAP2; LENGTH_MAP; make_funcs_MAP] THEN
  SIMP_TAC[pan_passes_MAP2_MAP; LENGTH_MAP; LENGTH_LIST_OF_SEQ; LE_REFL] THEN
  REWRITE_TAC[PTOPAUX_MAP2_FUN_EQ]);;

(* pan *)

let opsize_to_display_def = cake_def
  `(opsize_to_display Op8 = empty_item (implode "byte")) /\
   (opsize_to_display Op16 = empty_item (implode "word16")) /\
   (opsize_to_display OpW = empty_item (implode "word")) /\
   (opsize_to_display Op32 = empty_item (implode "word32"))`;;

let insert_es_def = cake_def
  `(insert_es (displayLang_String n) xs = Item NONE n xs) /\
   (insert_es x (_:sExp list) = x)`;;

let varkind_to_str_def = cake_def
  `varkind_to_str vk =
     match vk with
       panLang_Global -> implode "global"
     | panLang_Local -> implode "local"`;;

let primop_to_display_def = cake_def
  `primop_to_display panLang_AddCarry = displayLang_String (implode "AddCarry")`;;

let pan_exp_to_display_def = sem1aux_def_wf
  `MEASURE (\e:(A)panLang_exp. panLang_exp_size ARB e)`
  SEM1AUX_TC_TAC
  `(pan_exp_to_display (panLang_Const (v:A word)) = item_with_word (implode "Const") v) /\
   (pan_exp_to_display (panLang_Var vk n) =
      Item NONE (implode "Var")
        [displayLang_String (varkind_to_str vk); displayLang_String n]) /\
   (pan_exp_to_display BaseAddr = Item NONE (implode "BaseAddr") []) /\
   (pan_exp_to_display TopAddr = Item NONE (implode "TopAddr") []) /\
   (pan_exp_to_display BytesInWord = Item NONE (implode "BytesInWord") []) /\
   (pan_exp_to_display (panLang_Load shape exp2) =
      Item NONE (implode "MemLoad")
        [displayLang_String (shape_to_str shape); pan_exp_to_display exp2]) /\
   (pan_exp_to_display (panLang_Load32 exp2) =
      Item NONE (implode "MemLoad32") [pan_exp_to_display exp2]) /\
   (pan_exp_to_display (LoadByte exp2) =
      Item NONE (implode "MemLoadByte") [pan_exp_to_display exp2]) /\
   (pan_exp_to_display (RStruct xs) =
      Item NONE (implode "RawStruct") (MAP pan_exp_to_display xs)) /\
   (pan_exp_to_display (NStruct nm fxs) =
      Item NONE (implode "NamedStruct")
        (CONS (displayLang_String nm)
           (MAP (\p. match p with
                       (f,x) -> displayLang_Tuple
                                  [displayLang_String f;
                                   displayLang_String (implode ":=");
                                   pan_exp_to_display x]) fxs))) /\
   (pan_exp_to_display (Cmp cmp x1 x2) =
      insert_es (asm_cmp_to_display cmp)
        [pan_exp_to_display x1; pan_exp_to_display x2]) /\
   (pan_exp_to_display (panLang_Op b xs) =
      insert_es (asm_binop_to_display b) (MAP pan_exp_to_display xs)) /\
   (pan_exp_to_display (Panop p xs) =
      match p with
        panLang_Mul -> Item NONE (implode "Mul") (MAP pan_exp_to_display xs)) /\
   (pan_exp_to_display (RField i e) =
      Item NONE (implode "RawField") [num_to_display i; pan_exp_to_display e]) /\
   (pan_exp_to_display (NField f e) =
      Item NONE (implode "NamedField") [displayLang_String f; pan_exp_to_display e]) /\
   (pan_exp_to_display (panLang_Shift sh e e') =
      insert_es (shift_to_display sh) [pan_exp_to_display e; pan_exp_to_display e'])`;;

let dest_annot_def = sem1aux_def
  `(dest_annot (Annot k str:(A)panLang_prog) = SOME (k,str)) /\
   (dest_annot (_:(A)panLang_prog) = NONE)`;;

(* treat (Seq (Annot _) _) as a special case, and don't flatten it *)

let pan_seqs_def = cake_def_wf
  `MEASURE (\z:(A)panLang_prog. panLang_prog_size ARB z)`
  TERM_TAC
  `pan_seqs (z:(A)panLang_prog) =
     match z with
       panLang_Seq x y ->
         (match dest_annot x with
            SOME _ -> misc_List [z]
          | _ -> misc_Append (pan_seqs x) (pan_seqs y))
     | _ -> misc_List [z]`;;

(* HOL4: MEM_append_pan_seqs (local) *)

let MEM_append_pan_seqs = prove
 (`!prog1 (a:(A)panLang_prog).
     MEM a (append (pan_seqs prog1)) ==>
     panLang_prog_size ARB a <= panLang_prog_size ARB prog1`,
  REC_IND_TAC (cake_ind "pan_seqs") THEN GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[pan_seqs_def] THEN
  QCASES_ON "z:(A)panLang_prog" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[append_thm; MEM] THEN
  TRY (DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LE_REFL] THEN NO_TAC) THEN
  RENAME1 "dest_annot x" THEN QCASES_ON "dest_annot (x:(A)panLang_prog)" THEN
  CASE_REWRITE_TAC[append_thm; MEM; MEM_APPEND] THEN
  TRY (DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LE_REFL] THEN NO_TAC) THEN
  FS[] THEN STRIP_TAC THEN RES_TAC THEN
  REWRITE_TAC[type_size_def "panLang_prog"] THEN ASM_ARITH_TAC);;

(* The display functions of the three languages are defined by mutual       *)
(* recursion on the programs and their handlers.  HOL4 writes their Seq      *)
(* clauses as let xs = append (Append (seqs p1) (seqs p2)) in                *)
(* separate_lines "seq" (MAP f xs); the kit's recursion package does not     *)
(* keep the binding of xs in the termination conditions of the induction     *)
(* theorem, so the functions are defined with the let unfolded and          *)
(* PTOPAUX_RELET_RULE restates the Seq clause with HOL4's let (the          *)
(* theorems NAME_def are HOL4's; NAME_ind is the induction theorem of the   *)
(* definition, with the context MEM a (append ..) for the calls under MAP). *)

let PTOPAUX_RELET_RULE (th:thm) : thm =
  let name t = try fst(dest_const(fst(strip_comb t))) with Failure _ -> "" in
  let is_target t =
    name t = "separate_lines" &&
    (let args = snd(strip_comb t) in
     length args = 2 && name (el 1 args) = "MAP" &&
     (let margs = snd(strip_comb (el 1 args)) in
      length margs = 2 && name (el 1 margs) = "append")) in
  let t = find_term is_target (concl th) in
  let h,args = strip_comb t in
  let mh,margs = strip_comb (el 1 args) in
  let e = el 1 margs in
  let xs = mk_var("xs",type_of e) in
  let lt = mk_let([xs,e],
                  list_mk_comb(h,[hd args; list_mk_comb(mh,[hd margs; xs])])) in
  let eq = prove(mk_eq(t,lt), CONV_TAC(RAND_CONV let_CONV) THEN REFL_TAC) in
  PURE_ONCE_REWRITE_RULE[GEN_ALL eq] th;;

(* the termination conditions of the Seq clauses: the members of the       *)
(* flattened sequence are smaller than the sequence                         *)

let PTOPAUX_MEM_append_pan_seqs_LT = prove
 (`!(a:(A)panLang_prog) x y.
     MEM a (append (misc_Append (pan_seqs x) (pan_seqs y))) ==>
     panLang_prog_size ARB a < panLang_prog_size ARB (panLang_Seq x y)`,
  REWRITE_TAC[append_thm; MEM_APPEND; type_size_def "panLang_prog"] THEN
  REPEAT STRIP_TAC THEN IMP_RES_TAC MEM_append_pan_seqs THEN ASM_ARITH_TAC);;

let PTOPAUX_PAN_DISP_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN RVEQ_TAC THEN
  REPEAT (FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP PTOPAUX_MEM_append_pan_seqs_LT)) THEN
  TERM_TAC;;

(* HOL4 Termination: the program size; for a handler HOL4 measures          *)
(* option_size (\(_,_,p). prog_size ARB p), here the size of the handler     *)
(* as a part of a Call (option_size of the tuple size), which bounds it.     *)

let pan_prog_to_display_def = PTOPAUX_RELET_RULE (sem1aux_def_wf
  `MEASURE (\x:(A)panLang_prog + ((eid#varname#(A)panLang_prog)option).
              sum_CASE x (\p. panLang_prog_size ARB p)
                (\h. option_size (pair_size mlstring_size
                                     (pair_size mlstring_size (panLang_prog_size ARB))) h))`
  PTOPAUX_PAN_DISP_TC_TAC
  `(pan_prog_to_display (panLang_Skip:(A)panLang_prog) = empty_item (implode "skip")) /\
   (pan_prog_to_display (ShMemLoad s vk v e) =
      Item NONE (implode "shared_mem_load")
        [opsize_to_display s; displayLang_String (varkind_to_str vk);
         displayLang_String v; pan_exp_to_display e]) /\
   (pan_prog_to_display (ShMemStore s e1 e2) =
      Item NONE (implode "shared_mem_store")
        [opsize_to_display s; pan_exp_to_display e1; pan_exp_to_display e2]) /\
   (pan_prog_to_display (panLang_ExtCall f e1 e2 e3 e4) =
      Item NONE (implode "ext_call")
        [displayLang_String f; pan_exp_to_display e1; pan_exp_to_display e2;
         pan_exp_to_display e3; pan_exp_to_display e4]) /\
   (pan_prog_to_display (panLang_If e p1 p2) =
      Item NONE (implode "if")
        [pan_exp_to_display e; pan_prog_to_display p1; pan_prog_to_display p2]) /\
   (pan_prog_to_display (While e p) =
      Item NONE (implode "while") [pan_exp_to_display e; pan_prog_to_display p]) /\
   (pan_prog_to_display (Dec n shape e p) =
      Item NONE (implode "dec")
        [displayLang_Tuple [displayLang_String (implode "local");
                            displayLang_String (shape_to_str shape);
                            displayLang_String n;
                            displayLang_String (implode ":=");
                            pan_exp_to_display e];
         pan_prog_to_display p]) /\
   (pan_prog_to_display (panLang_Assign vk n exp) =
      displayLang_Tuple [displayLang_String (varkind_to_str vk);
                         displayLang_String n;
                         displayLang_String (implode ":=");
                         pan_exp_to_display exp]) /\
   (pan_prog_to_display (Primitive v pop es) =
      displayLang_Tuple [displayLang_String v;
                         displayLang_String (implode ":=");
                         insert_es (primop_to_display pop)
                           (MAP pan_exp_to_display es)]) /\
   (pan_prog_to_display (panLang_Store e1 e2) =
      displayLang_Tuple [displayLang_String (implode "mem"); pan_exp_to_display e1;
                         displayLang_String (implode ":="); pan_exp_to_display e2]) /\
   (pan_prog_to_display (panLang_Store32 e1 e2) =
      displayLang_Tuple [displayLang_String (implode "mem"); pan_exp_to_display e1;
                         displayLang_String (implode ":=");
                         displayLang_String (implode "32bit"); pan_exp_to_display e2]) /\
   (pan_prog_to_display (StoreByte e1 e2) =
      displayLang_Tuple [displayLang_String (implode "mem"); pan_exp_to_display e1;
                         displayLang_String (implode ":=");
                         displayLang_String (implode "byte"); pan_exp_to_display e2]) /\
   (pan_prog_to_display (Annot k str) =
      Item NONE (implode "annot")
        [displayLang_String (escape_str k); displayLang_String (escape_str str)]) /\
   (pan_prog_to_display panLang_Tick = empty_item (implode "tick")) /\
   (pan_prog_to_display panLang_Break = empty_item (implode "break")) /\
   (pan_prog_to_display panLang_Continue = empty_item (implode "continue")) /\
   (pan_prog_to_display (panLang_Return e) =
      Item NONE (implode "return") [pan_exp_to_display e]) /\
   (pan_prog_to_display (panLang_Raise n e) =
      Item NONE (implode "raise") [displayLang_String n; pan_exp_to_display e]) /\
   (pan_prog_to_display (panLang_Seq prog1 prog2) =
      separate_lines (implode "seq")
        (MAP pan_prog_to_display
           (append (misc_Append (pan_seqs prog1) (pan_seqs prog2))))) /\
   (pan_prog_to_display (panLang_Call ret_opt f args) =
      match ret_opt with
        NONE ->
          Item NONE (implode "tail_call")
            [displayLang_String f; displayLang_Tuple (MAP pan_exp_to_display args)]
      | SOME (NONE,handler) ->
          Item NONE (implode "call")
            [displayLang_String f; displayLang_Tuple (MAP pan_exp_to_display args);
             pan_prog_to_display_handler handler]
      | SOME (SOME (vk,v),handler) ->
          displayLang_Tuple
            [displayLang_String v; displayLang_String (implode ":=");
             Item NONE (implode "call")
               [displayLang_String f; displayLang_Tuple (MAP pan_exp_to_display args);
                pan_prog_to_display_handler handler]]) /\
   (pan_prog_to_display (DecCall v shape f args p) =
      Item NONE (implode "dec")
        [displayLang_Tuple [displayLang_String (shape_to_str shape);
                            displayLang_String v;
                            displayLang_String (implode ":=");
                            Item NONE (implode "call")
                              [displayLang_String f;
                               displayLang_Tuple (MAP pan_exp_to_display args)]];
         pan_prog_to_display p]) /\
   (pan_prog_to_display_handler NONE = empty_item (implode "no_handler")) /\
   (pan_prog_to_display_handler (SOME (v1,v2,p)) =
      Item NONE (implode "handler")
        [displayLang_Tuple [displayLang_String v1; displayLang_String v2;
                            pan_prog_to_display p]])`);;

let pan_prog_to_display_ind = cake_ind "pan_prog_to_display";;

let pan_fun_to_display_def = cake_def
  `pan_fun_to_display (decl:(A)decl) =
     match decl with
       Function fi ->
         displayLang_Tuple
           [displayLang_String (implode "func");
            displayLang_String (shape_to_str (fun_decl_return fi));
            displayLang_String (fun_decl_name fi);
            displayLang_Tuple
              (MAP (\(s,shape). displayLang_Tuple
                                  [displayLang_String s;
                                   displayLang_String (implode ":");
                                   displayLang_String (shape_to_str shape)])
                   (fun_decl_params fi));
            pan_prog_to_display (fun_decl_body fi)]
     | Decl sh nm exp ->
         displayLang_Tuple
           [displayLang_String (implode "global");
            displayLang_String (shape_to_str sh);
            displayLang_String nm;
            displayLang_String (implode ":=");
            pan_exp_to_display exp]
     | Name nm flds ->
         displayLang_Tuple
           [displayLang_String (implode "struct");
            displayLang_String nm;
            displayLang_Tuple
              (MAP (\(fld,shape). displayLang_Tuple
                                    [displayLang_String fld;
                                     displayLang_String (implode ":");
                                     displayLang_String (shape_to_str shape)]) flds)]
     | ExnDecl nm sh ->
         displayLang_Tuple
           [displayLang_String (implode "exception");
            displayLang_String nm;
            displayLang_String (implode ":");
            displayLang_String (shape_to_str sh)]`;;

let pan_to_strs_def = cake_def
  `pan_to_strs (xs:((A)decl)list) =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    pan_fun_to_display) xs`;;

(* crep *)

let crep_exp_to_display_def = sem1aux_def_wf
  `MEASURE (\e:(A)crep_exp. crep_exp_size ARB e)`
  SEM1AUX_TC_TAC
  (list_mk_conj
   [`(crep_exp_to_display (crep_Const (v:A word)) = item_with_word (implode "Const") v) /\
     (crep_exp_to_display (LoadGlob (w:5 word):(A)crep_exp) =
        item_with_word (implode "LoadGlob") w) /\
     (crep_exp_to_display (crep_Var n:(A)crep_exp) =
        Item NONE (implode "Var") [num_to_display n]) /\
     (crep_exp_to_display (crep_BaseAddr:(A)crep_exp) =
        Item NONE (implode "BaseAddr") []) /\
     (crep_exp_to_display (crep_TopAddr:(A)crep_exp) = Item NONE (implode "TopAddr") []) /\
     (crep_exp_to_display (crep_Load exp2:(A)crep_exp) =
        Item NONE (implode "MemLoad") [crep_exp_to_display exp2]) /\
     (crep_exp_to_display (crep_Load32 exp2:(A)crep_exp) =
        Item NONE (implode "MemLoad32") [crep_exp_to_display exp2]) /\
     (crep_exp_to_display (crep_LoadByte exp2:(A)crep_exp) =
        Item NONE (implode "MemLoadByte") [crep_exp_to_display exp2]) /\
     (crep_exp_to_display (crep_Cmp cmp x1 x2:(A)crep_exp) =
        insert_es (asm_cmp_to_display cmp)
          [crep_exp_to_display x1; crep_exp_to_display x2]) /\
     (crep_exp_to_display (crep_Op b xs:(A)crep_exp) =
        insert_es (asm_binop_to_display b) (MAP crep_exp_to_display xs)) /\
     (crep_exp_to_display (Crepop p xs:(A)crep_exp) =
        match p with
          crep_Mul -> Item NONE (implode "Mul") (MAP crep_exp_to_display xs)) /\
     (crep_exp_to_display (crep_Shift sh e e':(A)crep_exp) =
        insert_es (shift_to_display sh)
          [crep_exp_to_display e; crep_exp_to_display e'])`]);;

let crep_seqs_def = cake_def_wf
  `MEASURE (\z:(A)crep_prog. crep_prog_size ARB z)`
  TERM_TAC
  `crep_seqs (z:(A)crep_prog) =
     match z with
       crep_Seq x y -> misc_Append (crep_seqs x) (crep_seqs y)
     | _ -> misc_List [z]`;;

(* HOL4: MEM_append_crep_seqs (local) *)

let MEM_append_crep_seqs = prove
 (`!prog1 (a:(A)crep_prog).
     MEM a (append (crep_seqs prog1)) ==>
     crep_prog_size ARB a <= crep_prog_size ARB prog1`,
  REC_IND_TAC (cake_ind "crep_seqs") THEN GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[crep_seqs_def] THEN
  QCASES_ON "z:(A)crep_prog" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[append_thm; MEM; MEM_APPEND] THEN
  TRY (DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LE_REFL] THEN NO_TAC) THEN
  FS[] THEN STRIP_TAC THEN RES_TAC THEN
  REWRITE_TAC[type_size_def "crep_prog"] THEN ASM_ARITH_TAC);;

let PTOPAUX_MEM_append_crep_seqs_LT = prove
 (`!(a:(A)crep_prog) x y.
     MEM a (append (misc_Append (crep_seqs x) (crep_seqs y))) ==>
     crep_prog_size ARB a < crep_prog_size ARB (crep_Seq x y)`,
  REWRITE_TAC[append_thm; MEM_APPEND; type_size_def "crep_prog"] THEN
  REPEAT STRIP_TAC THEN IMP_RES_TAC MEM_append_crep_seqs THEN ASM_ARITH_TAC);;

let PTOPAUX_CREP_DISP_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN RVEQ_TAC THEN
  REPEAT (FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP PTOPAUX_MEM_append_crep_seqs_LT)) THEN
  TERM_TAC;;

(* HOL4 Termination: crep_prog_size ARB, and for a handler                    *)
(* option_size (pair_size w2n (prog_size ARB)); here the word is measured 0    *)
(* (the size of the handler as a part of a Call).                            *)

let crep_prog_to_display_def = PTOPAUX_RELET_RULE (sem1aux_def_wf
  `MEASURE (\x:(A)crep_prog + ((A word # (A)crep_prog)option).
              sum_CASE x (\p. crep_prog_size ARB p)
                (\h. option_size (pair_size (\w:A word. 0) (crep_prog_size ARB)) h))`
  PTOPAUX_CREP_DISP_TC_TAC
  (list_mk_conj
   [`(crep_prog_to_display (crep_Skip:(A)crep_prog) = empty_item (implode "skip")) /\
     (crep_prog_to_display (crep_ShMem mop v e:(A)crep_prog) =
        let prefix =
          (match mop with
             asm_Load -> [displayLang_String (implode "load");
                          displayLang_String (implode "word")]
           | Load8 -> [displayLang_String (implode "load");
                       displayLang_String (implode "byte")]
           | Load16 -> [displayLang_String (implode "load");
                        displayLang_String (implode "word16")]
           | asm_Load32 -> [displayLang_String (implode "load");
                            displayLang_String (implode "word32")]
           | asm_Store -> [displayLang_String (implode "store");
                           displayLang_String (implode "word")]
           | Store8 -> [displayLang_String (implode "store");
                        displayLang_String (implode "byte")]
           | Store16 -> [displayLang_String (implode "store");
                         displayLang_String (implode "word16")]
           | asm_Store32 -> [displayLang_String (implode "store");
                             displayLang_String (implode "word32")]) in
        Item NONE (implode "shared_mem")
          (APPEND prefix [num_to_display v; crep_exp_to_display e]))`;
    `crep_prog_to_display (crep_ExtCall f e1 e2 e3 e4:(A)crep_prog) =
        Item NONE (implode "ext_call")
          [displayLang_String f; num_to_display e1; num_to_display e2;
           num_to_display e3; num_to_display e4]`;
    `crep_prog_to_display (StoreGlob (w:5 word) e:(A)crep_prog) =
        Item NONE (implode "store_glob") [word_to_display w; crep_exp_to_display e]`;
    `(crep_prog_to_display (crep_If e p1 p2:(A)crep_prog) =
        Item NONE (implode "if")
          [crep_exp_to_display e; crep_prog_to_display p1; crep_prog_to_display p2]) /\
     (crep_prog_to_display (crep_While e p) =
        Item NONE (implode "while") [crep_exp_to_display e; crep_prog_to_display p]) /\
     (crep_prog_to_display (crep_Dec n e p) =
        Item NONE (implode "dec")
          [displayLang_Tuple [num_to_display n; displayLang_String (implode ":=");
                              crep_exp_to_display e];
           crep_prog_to_display p]) /\
     (crep_prog_to_display (crep_Assign n exp) =
        displayLang_Tuple [num_to_display n; displayLang_String (implode ":=");
                           crep_exp_to_display exp]) /\
     (crep_prog_to_display (crep_Primitive lhss pop rhss) =
        displayLang_Tuple
          [displayLang_Tuple (MAP num_to_display lhss);
           displayLang_String (implode ":=");
           insert_es (primop_to_display pop) (MAP num_to_display rhss)]) /\
     (crep_prog_to_display (crep_Store e1 e2) =
        displayLang_Tuple [displayLang_String (implode "mem"); crep_exp_to_display e1;
                           displayLang_String (implode ":="); crep_exp_to_display e2]) /\
     (crep_prog_to_display (crep_Store32 e1 e2) =
        displayLang_Tuple [displayLang_String (implode "mem"); crep_exp_to_display e1;
                           displayLang_String (implode ":=");
                           displayLang_String (implode "32bit");
                           crep_exp_to_display e2]) /\
     (crep_prog_to_display (crep_StoreByte e1 e2) =
        displayLang_Tuple [displayLang_String (implode "mem"); crep_exp_to_display e1;
                           displayLang_String (implode ":=");
                           displayLang_String (implode "byte");
                           crep_exp_to_display e2]) /\
     (crep_prog_to_display crep_Tick = empty_item (implode "tick")) /\
     (crep_prog_to_display (crep_Break n) = item_with_num (implode "break") n) /\
     (crep_prog_to_display (crep_Continue n) = item_with_num (implode "continue") n) /\
     (crep_prog_to_display (crep_Return es) =
        Item NONE (implode "return") (MAP crep_exp_to_display es)) /\
     (crep_prog_to_display (crep_Raise w) = item_with_word (implode "raise") w) /\
     (crep_prog_to_display (crep_Seq prog1 prog2) =
        separate_lines (implode "seq")
          (MAP crep_prog_to_display
             (append (misc_Append (crep_seqs prog1) (crep_seqs prog2))))) /\
     (crep_prog_to_display (crep_Call ret_opt f args) =
        match ret_opt with
          NONE ->
            Item NONE (implode "tail_call")
              [displayLang_String f; displayLang_Tuple (MAP crep_exp_to_display args)]
        | SOME ([],handler) ->
            Item NONE (implode "call")
              [displayLang_String f; displayLang_Tuple (MAP crep_exp_to_display args);
               crep_prog_to_display_handler handler]
        | SOME (vs,handler) ->
            displayLang_Tuple
              [displayLang_Tuple (MAP num_to_display vs);
               displayLang_String (implode ":=");
               Item NONE (implode "call")
                 [displayLang_String f; displayLang_Tuple (MAP crep_exp_to_display args);
                  crep_prog_to_display_handler handler]]) /\
     (crep_prog_to_display_handler NONE = empty_item (implode "no_handler")) /\
     (crep_prog_to_display_handler (SOME (w,p)) =
        Item NONE (implode "handler")
          [displayLang_Tuple [word_to_display w; crep_prog_to_display p]])`]));;

let crep_prog_to_display_ind = cake_ind "crep_prog_to_display";;

let crep_fun_to_display_def = cake_def
  `crep_fun_to_display (nm,args,body:(A)crep_prog) =
     displayLang_Tuple
       [displayLang_String (implode "func"); displayLang_String nm;
        displayLang_Tuple (MAP num_to_display args);
        crep_prog_to_display body]`;;

let crep_to_strs_def = cake_def
  `crep_to_strs (xs:(mlstring # num list # (A)crep_prog)list) =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    crep_fun_to_display) xs`;;

(* loop *)

let loop_exp_to_display_def = sem1aux_def_wf
  `MEASURE (\e:(A)loop_exp. loop_exp_size ARB e)`
  SEM1AUX_TC_TAC
  `(loop_exp_to_display (loop_Const (v:A word)) = item_with_word (implode "Const") v) /\
   (loop_exp_to_display (loop_Var n) = item_with_num (implode "Var") n) /\
   (loop_exp_to_display loop_BaseAddr = Item NONE (implode "BaseAddr") []) /\
   (loop_exp_to_display loop_TopAddr = Item NONE (implode "TopAddr") []) /\
   (loop_exp_to_display (loop_Lookup st) = item_with_word (implode "Lookup") st) /\
   (loop_exp_to_display (loop_Load exp2) =
      Item NONE (implode "MemLoad") [loop_exp_to_display exp2]) /\
   (loop_exp_to_display (loop_Op bop exs) =
      Item NONE (implode "Op")
        (CONS (asm_binop_to_display bop) (MAP loop_exp_to_display exs))) /\
   (loop_exp_to_display (loop_Shift sh exp exp') =
      Item NONE (implode "Shift")
        [shift_to_display sh; loop_exp_to_display exp; loop_exp_to_display exp'])`;;

let loop_seqs_def = cake_def_wf
  `MEASURE (\z:(A)loop_prog. loop_prog_size ARB z)`
  TERM_TAC
  `loop_seqs (z:(A)loop_prog) =
     match z with
       loop_Seq x y -> misc_Append (loop_seqs x) (loop_seqs y)
     | _ -> misc_List [z]`;;

(* HOL4: MEM_append_loop_seqs (local) *)

let MEM_append_loop_seqs = prove
 (`!prog1 (a:(A)loop_prog).
     MEM a (append (loop_seqs prog1)) ==>
     loop_prog_size ARB a <= loop_prog_size ARB prog1`,
  REC_IND_TAC (cake_ind "loop_seqs") THEN GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[loop_seqs_def] THEN
  QCASES_ON "z:(A)loop_prog" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[append_thm; MEM; MEM_APPEND] THEN
  TRY (DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LE_REFL] THEN NO_TAC) THEN
  FS[] THEN STRIP_TAC THEN RES_TAC THEN
  REWRITE_TAC[type_size_def "loop_prog"] THEN ASM_ARITH_TAC);;

let PTOPAUX_MEM_append_loop_seqs_LT = prove
 (`!(a:(A)loop_prog) x y.
     MEM a (append (misc_Append (loop_seqs x) (loop_seqs y))) ==>
     loop_prog_size ARB a < loop_prog_size ARB (loop_Seq x y)`,
  REWRITE_TAC[append_thm; MEM_APPEND; type_size_def "loop_prog"] THEN
  REPEAT STRIP_TAC THEN IMP_RES_TAC MEM_append_loop_seqs THEN ASM_ARITH_TAC);;

let PTOPAUX_LOOP_DISP_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN RVEQ_TAC THEN
  REPEAT (FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP PTOPAUX_MEM_append_loop_seqs_LT)) THEN
  TERM_TAC;;

(* HOL4 Termination: loop_prog_size ARB of the program, and for a handler    *)
(* option_size (\(a,b,c,d). a + prog_size ARB b + prog_size ARB c +            *)
(* spt_size one_size d); here the size of the handler as a part of a Call.   *)

let loop_prog_to_display_def = PTOPAUX_RELET_RULE (sem1aux_def_wf
  `MEASURE (\x:(mlstring spt # (A)loop_prog) +
               (mlstring spt # ((num # (A)loop_prog # (A)loop_prog # num_set)option)).
              sum_CASE x (\p. loop_prog_size ARB (SND p))
                (\p. option_size (pair_size (\n:num. n)
                                   (pair_size (loop_prog_size ARB)
                                      (pair_size (loop_prog_size ARB)
                                         (spt_size (\u:1. 0))))) (SND p)))`
  PTOPAUX_LOOP_DISP_TC_TAC
  (list_mk_conj
   [`(loop_prog_to_display (ns:mlstring spt) (loop_Skip:(A)loop_prog) = empty_item (implode "skip")) /\
     (loop_prog_to_display ns (loop_Arith a:(A)loop_prog) =
        match a with
          LLongMul n1 n2 n3 n4 ->
            item_with_nums (implode "long_mul") [n1; n2; n3; n4]
        | LLongDiv n1 n2 n3 n4 n5 ->
            item_with_nums (implode "long_div") [n1; n2; n3; n4; n5]
        | LDiv n1 n2 n3 ->
            item_with_nums (implode "div") [n1; n2; n3])`;
    `(loop_prog_to_display (ns:mlstring spt) (loop_Assign n exp:(A)loop_prog) =
        displayLang_Tuple [num_to_display n; displayLang_String (implode ":=");
                           loop_exp_to_display exp]) /\
     (loop_prog_to_display ns (loop_Primitive lhss pop rhss) =
        displayLang_Tuple
          [displayLang_Tuple (MAP num_to_display lhss);
           displayLang_String (implode ":=");
           insert_es (primop_to_display pop) (MAP num_to_display rhss)]) /\
     (loop_prog_to_display ns (loop_SetGlobal w exp) =
        Item NONE (implode "set_global") [word_to_display w; loop_exp_to_display exp]) /\
     (loop_prog_to_display ns (loop_Seq prog1 prog2) =
        separate_lines (implode "seq")
          (MAP (loop_prog_to_display ns)
             (append (misc_Append (loop_seqs prog1) (loop_seqs prog2))))) /\
     (loop_prog_to_display ns (loop_FFI nm n1 n2 n3 n4 ms) =
        Item NONE (implode "ffi")
          (APPEND (CONS (string_imp nm) (MAP num_to_display [n1; n2; n3; n4]))
             [num_set_to_display ms])) /\
     (loop_prog_to_display ns (loop_Raise n) = item_with_num (implode "raise") n) /\
     (loop_prog_to_display ns (loop_Return ns0) = item_with_nums (implode "return") ns0) /\
     (loop_prog_to_display ns loop_Tick = empty_item (implode "tick")) /\
     (loop_prog_to_display ns (loop_Break n) = item_with_num (implode "break") n) /\
     (loop_prog_to_display ns (loop_Continue n) = item_with_num (implode "continue") n) /\
     (loop_prog_to_display ns loop_Fail = empty_item (implode "fail")) /\
     (loop_prog_to_display ns (loop_Load32 n1 n2) =
        item_with_nums (implode "load_32") [n1; n2]) /\
     (loop_prog_to_display ns (loop_LoadByte n1 n2) =
        item_with_nums (implode "load_byte") [n1; n2]) /\
     (loop_prog_to_display ns (loop_Store32 n1 n2) =
        item_with_nums (implode "store_32") [n1; n2]) /\
     (loop_prog_to_display ns (loop_StoreByte n1 n2) =
        item_with_nums (implode "store_byte") [n1; n2]) /\
     (loop_prog_to_display ns (LocValue n1 n2) =
        Item NONE (implode "loc_value")
          [displayLang_String (attach_name ns (SOME n1)); num_to_display n2]) /\
     (loop_prog_to_display ns (loop_ShMem mop n e) =
        displayLang_Tuple
          [displayLang_String (implode "share_mem"); asm_memop_to_display mop;
           num_to_display n; loop_exp_to_display e]) /\
     (loop_prog_to_display ns (loop_If cmp n reg p1 p2 ms) =
        Item NONE (implode "if")
          [displayLang_Tuple [asm_cmp_to_display cmp; num_to_display n;
                              asm_reg_imm_to_display reg];
           loop_prog_to_display ns p1; loop_prog_to_display ns p2;
           num_set_to_display ms]) /\
     (loop_prog_to_display ns (loop_Loop ms1 p ms2) =
        Item NONE (implode "loop")
          [num_set_to_display ms1; loop_prog_to_display ns p; num_set_to_display ms2]) /\
     (loop_prog_to_display ns (Mark prog) =
        Item NONE (implode "mark") [loop_prog_to_display ns prog]) /\
     (loop_prog_to_display ns (loop_Store exp n) =
        displayLang_Tuple [displayLang_String (implode "mem"); loop_exp_to_display exp;
                           displayLang_String (implode ":="); num_to_display n])`;
    `(loop_prog_to_display (ns:mlstring spt) (loop_Call a b c d:(A)loop_prog) =
        match a with
          NONE ->
            Item NONE (implode "tail_call")
              [(match b with
                  NONE -> empty_item (implode "none")
                | SOME n ->
                    Item NONE (implode "some")
                      [displayLang_String (attach_name ns (SOME n))]);
               displayLang_Tuple (MAP num_to_display c)]
        | SOME (ns0,ms) ->
            displayLang_Tuple
              [displayLang_Tuple (MAP num_to_display ns0);
               displayLang_String (implode ":=");
               Item NONE (implode "call")
                 [(match b with
                     NONE -> empty_item (implode "none")
                   | SOME n ->
                       Item NONE (implode "some")
                         [displayLang_String (attach_name ns (SOME n))]);
                  displayLang_Tuple (MAP num_to_display c);
                  num_set_to_display ms;
                  loop_prog_to_display_handler ns d]]) /\
     (loop_prog_to_display_handler ns NONE = empty_item (implode "no_handler")) /\
     (loop_prog_to_display_handler ns (SOME (n1,p1,p2,ms)) =
        Item NONE (implode "handler")
          [displayLang_Tuple
             [num_to_display n1;
              loop_prog_to_display ns p1;
              loop_prog_to_display ns p2;
              num_set_to_display ms]])`]));;

let loop_prog_to_display_ind = cake_ind "loop_prog_to_display";;

let loop_fun_to_display_def = cake_def
  `loop_fun_to_display names (n,args,body:(A)loop_prog) =
     displayLang_Tuple
       [displayLang_String (implode "func");
        displayLang_String (attach_name names (SOME n));
        displayLang_Tuple (MAP num_to_display args);
        loop_prog_to_display names body]`;;

let loop_to_strs_def = cake_def
  `loop_to_strs names (xs:(num # num list # (A)loop_prog)list) =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    loop_fun_to_display names) xs`;;

let any_pan_prog_pp_def = cake_def
  `any_pan_prog_pp (x:(A)any_pan_prog) =
     match x with
       Pan p -> pan_to_strs p
     | Crep p -> crep_to_strs p
     | pan_passes_Loop p ns -> loop_to_strs ns p
     | Cake p -> any_prog_pp p`;;

let pan_compile_tap_def = cake_def
  `pan_compile_tap (asm_conf:(A)asm_config) (c:backend_config) (p:((A)decl)list) =
     if tap_config_explore_flag (backend_config_tap_conf c) then
       let (ps,out) = pan_to_target_all asm_conf c p in
       (out,ITLIST (pp_with_title any_pan_prog_pp) ps Nil)
     else (pan_to_target_compile_prog asm_conf c p,Nil)`;;

let compile_alt = prove
 (`!(asm_conf:(A)asm_config) c p.
     pan_to_target_compile_prog asm_conf c p = FST (pan_compile_tap asm_conf c p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pan_compile_tap_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[compile_prog_eq_pan_to_target_all] THEN
  SPEC_TAC(`pan_to_target_all (asm_conf:(A)asm_config) c p`,`q:(mlstring#(A)any_pan_prog)list#((byte list#(A word)list#backend_config)option)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[pair_CASE; FST; SND]);;
