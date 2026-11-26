(* ========================================================================= *)
(* pan_to_target: port of HOL4 pancake/pan_to_targetScript.sml (CakeML      *)
(* v3479).                                                                   *)
(* Compiler from Pancake to machine code.                                    *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: compile_prog is                           *)
(*   pan_to_target_compile_prog; exports and compile_prog_eq keep theirs.   *)
(* - The record literal <| name := ..; ...; return := One |> of fun_decl is  *)
(*   fun_decl_REC with the fields in order; strlit s is implode s; 0w is     *)
(*   word 0; sort $< is sort (<); () is one; sptree's union and fromAList    *)
(*   are union and fromAList; ++ is APPEND (left associative).              *)
(* - HOL4's ZIP truncates the longer list, HOL Light's ZIP l1 l2 has the    *)
(*   length of l1.  In compile_prog the two lists have equal lengths: if   *)
(*   prog1 has a function main (the case expression puts one first unless   *)
(*   prog is []), pan_globals_compile_top adds one function (the new main)  *)
(*   to the functions of prog1 and the other passes keep their number, so   *)
(*   LENGTH prog2 = 1 + LENGTH (functions prog1); if prog1 is [] then      *)
(*   prog2 is [].  So HOL Light's ZIP gives HOL4's value.                   *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mllist.ml";;
needs "pancake/pan_to_word.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/word_depth.ml";;
needs "compiler/backend/word_to_word.ml";;

prioritize_num();;
type_invention_error := true;;

let exports_def = cake_def
  `(exports (CONS (Function (fi:(A)fun_decl)) ds) =
      if fun_decl_export fi then CONS (fun_decl_name fi) (exports ds)
      else exports ds) /\
   (exports (CONS (_:(A)decl) ds) = exports ds) /\
   (exports ([]:((A)decl)list) = [])`;;

(* Ensure either user-written main or new main that does nothing is first   *)
(* in func list                                                             *)

let pan_to_target_compile_prog_def = cake_def
  `pan_to_target_compile_prog (asm_conf:(A)asm_config) (c:backend_config)
       (prog:((A)decl)list) =
     let prog1 =
       (match SPLITP (\x. match x with
                            Function fi -> fun_decl_name fi = implode "main"
                          | _ -> F) prog with
          ([],ys) -> ys
        | (xs,[]) ->
            CONS (Function (fun_decl_REC (implode "main") F F []
                              (panLang_Return (panLang_Const (word 0))) One)) xs
        | (xs,CONS y ys) -> APPEND (CONS y xs) ys) in
     let prog2 = pan_to_word_compile_prog (asm_config_ISA asm_conf) prog1 in
     let (col,prog3) =
       word_to_word_compile (backend_config_word_to_word_conf c) asm_conf prog2 in
     let c = backend_config_word_to_word_conf_fupd
               (\c. word_to_word_config_col_oracle_fupd (combin_K col) c) c in
     let names = fromAList (ZIP (sort (<) (MAP FST prog2))
                                (CONS (implode "generated_main")
                                      (MAP FST (functions prog1)))) : mlstring spt in
     let names = sptree_union (fromAList (APPEND (APPEND (word_to_stack_stub_names one)
                                                  (stack_alloc_stub_names one))
                                          (stack_remove_stub_names one))) names in
     let c = backend_config_exported_fupd (combin_K (exports prog)) c in
     from_word asm_conf c names prog3`;;

(* TODO (HOL4): evaluate max_depth ... (full_call_graph dest (fromAList prog)) *)

let compile_prog_eq = prove
 (CASE_TERM
  `pan_to_target_compile_prog (asm_conf:(A)asm_config) c prog =
     let prog1 =
       (match SPLITP (\x. match x with
                            Function fi -> fun_decl_name fi = implode "main"
                          | _ -> F) prog with
          ([],ys) -> ys
        | (xs,[]) ->
            CONS (Function (fun_decl_REC (implode "main") F F []
                              (panLang_Return (panLang_Const (word 0))) One)) xs
        | (xs,CONS y ys) -> APPEND (CONS y xs) ys) in
     let prog2 = pan_to_word_compile_prog (asm_config_ISA asm_conf) prog1 in
     let names = fromAList (ZIP (sort (<) (MAP FST prog2))
                                (CONS (implode "generated_main")
                                      (MAP FST (functions prog1)))) : mlstring spt in
     let names = sptree_union (fromAList (APPEND (APPEND (word_to_stack_stub_names one)
                                                  (stack_alloc_stub_names one))
                                          (stack_remove_stub_names one))) names in
     let c = backend_config_exported_fupd (combin_K (exports prog)) c in
     from_word_0 asm_conf c names prog2`,
  REWRITE_TAC[pan_to_target_compile_prog_def; from_word_0_def] THEN SIMP[] THEN
  BACKDEFAUX_LETS_TAC THEN SIMP[]);;
