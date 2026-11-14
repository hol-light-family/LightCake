(* ========================================================================= *)
(* backend: port of HOL4 compiler/backend/backendScript.sml (CakeML v3479). *)
(* Composes all of the compiler phases within the compiler backend into a   *)
(* single compile function which is connected (in ../compilerScript.sml) to *)
(* the front-end, i.e. parsing and type inference.                          *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as notes/naming/names.tsv says: backend_config (fields           *)
(*   backend_config_source_conf, ...), backend_compile, backend_to_word_thm, *)
(*   backend_from_data_thm, backend_ZIP_MAP_MAP; the passes are called by    *)
(*   their port names (source_to_flat_compile, clos_to_bvl_compile, ...;     *)
(*   HOL4 data_to_word$compile_0 is compile_0, word_simp$compile_exp is     *)
(*   word_simp_compile_exp, clos_to_bvl_compile_inc and                      *)
(*   bvl_to_bvi_compile_inc_all keep their names).                           *)
(* - A HOL4 record update r with <| f1 := v1; f2 := v2 |> is                 *)
(*   f1_fupd (K v1) (f2_fupd (K v2) r); r with f updated_by g is f_fupd g r; *)
(*   a partial record literal <| f := v |> is f_fupd (K v) ARB (HOL4's       *)
(*   meaning).                                                               *)
(* - HOL4 () is one; the mlstring literal of s is implode s; ++ is APPEND    *)
(*   (left-associative as in HOL4); ZIP (l1,l2) is ZIP l1 l2 (HOL Light's     *)
(*   ZIP has the length of l1: from_livesets zips lists of the same length   *)
(*   when it is applied to the result of to_livesets).                       *)
(* - max_heap_limit (:'a) takes the universe (:A) (data_to_word.ml).          *)
(* - HOL4 keep_progs k ps = (case k of T => ps | _ => []) is the same as     *)
(*   if k then ps else [].                                                   *)
(* - The local Overloads of backendScript (bvl_inline_compile_prog, ...) are *)
(*   abbreviations for names that the port has anyway.                      *)
(* - BACKDEFAUX_ names are local helpers of this file.                       *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/source_to_source.ml";;
needs "compiler/backend/source_to_flat.ml";;
needs "compiler/backend/flat_to_clos.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/bvi_to_data.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/word_to_stack.ml";;
needs "compiler/backend/stack_to_lab.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "compiler/backend/presLang.ml";;
needs "semantics/primTypes.ml";;

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Local proof helpers (BACKDEFAUX_): the HOL4 proofs of this file are       *)
(* unfold + pairarg_tac + simp; here BACKDEFAUX_PAIRARG_TAC splits the       *)
(* innermost pair_CASE e f of the goal whose scrutinee e is free (no bound   *)
(* variable, no case constant inside), replacing e by (a,b) everywhere       *)
(* and keeping e = (a,b) as an assumption (after bvl_handle.ml's            *)
(* BVLPAUX_PAIRARG_TAC: the kit's PAIRARG_TAC can pick an outer nested      *)
(* scrutinee first); BACKDEFAUX_LETS_RW_TAC rws unfolds the lets, reduces   *)
(* the cases of explicit tuples, rewrites with rws and splits the pairs of a *)
(* goal made of let-chains (BACKDEFAUX_LETS_TAC: no rws).                    *)
(* ------------------------------------------------------------------------- *)

let BACKDEFAUX_PAIRARG_TAC : tactic =
  fun (asl,w as gl) ->
    let rec go bvs t =
      let here =
        is_case_app t &&
        (let c,x,_ = dest_case_app t in
         fst(dest_const c) = "pair_CASE" && not (is_pair x) &&
         not (can (find_term is_case_app) x) &&
         intersect (frees x) bvs = []) in
      if here then t else
      match t with
        Comb(f,a) -> (try go bvs f with Failure _ -> go bvs a)
      | Abs(v,b) -> go (v::bvs) b
      | _ -> failwith "BACKDEFAUX_PAIRARG_TAC" in
    let _,x,_ = dest_case_app (go [] w) in
    let v = genvar (type_of x) in
    let lemma = mk_forall(v,mk_imp(mk_eq(x,v),subst [v,x] w)) in
    (SUBGOAL_THEN lemma (fun th -> ACCEPT_TAC (MP (SPEC x th) (REFL x))) THEN
     REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
     CASE_REWRITE_TAC[]) gl;;

let BACKDEFAUX_LETS_RW_TAC rws : tactic =
  REPEAT (CHANGED_TAC (CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
                       REWRITE_TAC rws) ORELSE
          BACKDEFAUX_PAIRARG_TAC);;

let BACKDEFAUX_LETS_TAC : tactic = BACKDEFAUX_LETS_RW_TAC [];;

(* exported: field for Pancake entry points - empty for CakeML *)

let backend_config_INFO = cake_record "backend_config"
  ["source_conf","source_to_flat_config";
   "clos_conf","clos_to_bvl_config";
   "bvl_conf","bvl_to_bvi_config";
   "data_conf","data_to_word_config";
   "word_to_word_conf","word_to_word_config";
   "word_conf","word_to_stack_config";
   "stack_conf","stack_to_lab_config";
   "lab_conf","lab_to_target_config";
   "symbols","(mlstring#num#num)list";
   "tap_conf","tap_config";
   "exported","mlstring list"];;

(* HOL4: config_component_equality *)

let backend_config_component_equality =
  backend_config_INFO.ri_component_equality;;

let attach_bitmaps_def = cake_def
  `(attach_bitmaps (names:mlstring spt) (c:backend_config) (bm:B)
      (SOME (bytes:byte list,c':lab_to_target_config)) =
      SOME (bytes,bm,
            backend_config_lab_conf_fupd (K c')
              (backend_config_symbols_fupd
                 (K (MAP (\(n,p,l). (lookup_any n names (implode "NOTFOUND"),p,l))
                       (lab_to_target_config_sec_pos_len c'))) c))) /\
   (attach_bitmaps names c bm NONE = NONE)`;;

let backend_compile_def = cake_def
  `backend_compile (asm_conf:(A)asm_config) (c:backend_config) p =
     let p = source_to_source_compile p in
     let _ = empty_ffi (implode "finished: source_to_source") in
     let (c',p) = source_to_flat_compile (backend_config_source_conf c) p in
     let _ = empty_ffi (implode "finished: source_to_flat") in
     let c = backend_config_source_conf_fupd (K c') c in
     let p = flat_to_clos_compile_prog p in
     let _ = empty_ffi (implode "finished: flat_to_clos") in
     let (c',p,names) = clos_to_bvl_compile (backend_config_clos_conf c) p in
     let c = backend_config_clos_conf_fupd (K c') c in
     let _ = empty_ffi (implode "finished: clos_to_bvl") in
     let (s,p,l,bl,n1,n2,n3,names) =
       bvl_to_bvi_compile (clos_to_bvl_config_start (backend_config_clos_conf c))
         (backend_config_bvl_conf c) names p in
     let c = backend_config_clos_conf_fupd
               (\c. clos_to_bvl_config_start_fupd (K s) c) c in
     let c = backend_config_bvl_conf_fupd
               (\c. bvl_to_bvi_config_inlines_fupd (K l)
                      (bvl_to_bvi_config_bvi_inlines_fupd (K bl)
                         (bvl_to_bvi_config_next_name1_fupd (K n1)
                            (bvl_to_bvi_config_next_name2_fupd (K n2)
                               (bvl_to_bvi_config_next_name3_fupd (K n3) c))))) c in
     let _ = empty_ffi (implode "finished: bvl_to_bvi") in
     let p = bvi_to_data_compile_prog p in
     let _ = empty_ffi (implode "finished: bvi_to_data") in
     let (col,p) = data_to_word_compile (backend_config_data_conf c)
                     (backend_config_word_to_word_conf c) asm_conf p in
     let c = backend_config_word_to_word_conf_fupd
               (\c. word_to_word_config_col_oracle_fupd (K col) c) c in
     let names = union (fromAList (APPEND (APPEND (APPEND
                   (data_to_word_stub_names one) (word_to_stack_stub_names one))
                   (stack_alloc_stub_names one)) (stack_remove_stub_names one))) names in
     let _ = empty_ffi (implode "finished: data_to_word") in
     let (bm,c',fs,p) =
       word_to_stack_compile asm_conf
         (stack_to_lab_config_perf_calls (backend_config_stack_conf c)) p in
     let c = backend_config_word_conf_fupd (K c') c in
     let _ = empty_ffi (implode "finished: word_to_stack") in
     let p = stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
               (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
               (asm_config_reg_count asm_conf -
                (LENGTH (asm_config_avoid_regs asm_conf) + 3))
               (asm_config_addr_offset asm_conf) p in
     let _ = empty_ffi (implode "finished: stack_to_lab") in
     let res = attach_bitmaps names c bm
                 (lab_to_target_compile asm_conf (backend_config_lab_conf c)
                    (p:((A)sec)list)) in
     let _ = empty_ffi (implode "finished: lab_to_target") in
     res`;;

let to_flat_def = cake_def
  `to_flat (c:backend_config) p =
     let p = source_to_source_compile p in
     let (c',p) = source_to_flat_compile (backend_config_source_conf c) p in
     let c = backend_config_source_conf_fupd (K c') c in
     (c,p)`;;

let to_clos_def = cake_def
  `to_clos (c:backend_config) p =
     let (c,p) = to_flat c p in
     let p = flat_to_clos_compile_prog p in
     (c,p)`;;

let to_bvl_def = cake_def
  `to_bvl (c:backend_config) p =
     let (c,p) = to_clos c p in
     let (c',p,names) = clos_to_bvl_compile (backend_config_clos_conf c) p in
     let c = backend_config_clos_conf_fupd (K c') c in
     (c,p,names)`;;

let to_bvi_def = cake_def
  `to_bvi (c:backend_config) p =
     let (c,p,names) = to_bvl c p in
     let (s,p,l,bl,n1,n2,n3,names) =
       bvl_to_bvi_compile (clos_to_bvl_config_start (backend_config_clos_conf c))
         (backend_config_bvl_conf c) names p in
     let names = union (fromAList (APPEND (APPEND (APPEND
                   (data_to_word_stub_names one) (word_to_stack_stub_names one))
                   (stack_alloc_stub_names one)) (stack_remove_stub_names one))) names in
     let c = backend_config_clos_conf_fupd
               (\c. clos_to_bvl_config_start_fupd (K s) c) c in
     let c = backend_config_bvl_conf_fupd
               (\c. bvl_to_bvi_config_inlines_fupd (K l)
                      (bvl_to_bvi_config_bvi_inlines_fupd (K bl)
                         (bvl_to_bvi_config_next_name1_fupd (K n1)
                            (bvl_to_bvi_config_next_name2_fupd (K n2)
                               (bvl_to_bvi_config_next_name3_fupd (K n3) c))))) c in
     (c,p,names)`;;

let to_data_def = cake_def
  `to_data (c:backend_config) p =
     let (c,p,names) = to_bvi c p in
     let p = bvi_to_data_compile_prog p in
     (c,p,names)`;;

let to_word_0_def = cake_def
  `to_word_0 (asm_conf:(A)asm_config) (c:backend_config) p =
     let (c,p,names) = to_data c p in
     let p = compile_0 (backend_config_data_conf c) asm_conf p in
     (c,p,names)`;;

let to_word_def = cake_def
  `to_word (asm_conf:(A)asm_config) (c:backend_config) p =
     let (c,p,names) = to_data c p in
     let (col,p) = data_to_word_compile (backend_config_data_conf c)
                     (backend_config_word_to_word_conf c) asm_conf p in
     let c = backend_config_word_to_word_conf_fupd
               (\c. word_to_word_config_col_oracle_fupd (K col) c) c in
     (c,p,names)`;;

(* HOL4: to_word_thm *)

let backend_to_word_thm = prove
 (CASE_TERM
  `to_word (asm_conf:(A)asm_config) c p =
     let (c,p,names) = to_word_0 asm_conf c p in
     let (col,p) = word_to_word_compile (backend_config_word_to_word_conf c) asm_conf p in
     let c = backend_config_word_to_word_conf_fupd
               (\c. word_to_word_config_col_oracle_fupd (K col) c) c in
     (c,p,names)`,
  REWRITE_TAC[to_word_def; to_word_0_def; compile_0_def; data_to_word_compile_def] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[]);;

let to_stack_def = cake_def
  `to_stack (asm_conf:(A)asm_config) (c:backend_config) p =
     let (c,p,names) = to_word asm_conf c p in
     let (bm,c',fs,p) =
       word_to_stack_compile asm_conf
         (stack_to_lab_config_perf_calls (backend_config_stack_conf c)) p in
     let c = backend_config_word_conf_fupd (K c') c in
     (bm,c,p,names)`;;

let to_lab_def = cake_def
  `to_lab (asm_conf:(A)asm_config) (c:backend_config) p =
     let (bm,c,p,names) = to_stack asm_conf c p in
     let p = stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
               (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
               (asm_config_reg_count asm_conf -
                (LENGTH (asm_config_avoid_regs asm_conf) + 3))
               (asm_config_addr_offset asm_conf) p in
     (bm,c,p:((A)sec)list,names)`;;

let to_target_def = cake_def
  `to_target (asm_conf:(A)asm_config) (c:backend_config) p =
     let (bm,c,p,names) = to_lab asm_conf c p in
     attach_bitmaps names c bm
       (lab_to_target_compile asm_conf (backend_config_lab_conf c) p)`;;

let compile_eq_to_target = prove
 (`backend_compile =
   (to_target:(A)asm_config->backend_config->dec list->
              (byte list#(A word)list#backend_config)option)`,
  REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[backend_compile_def; to_target_def; to_lab_def; to_stack_def; to_word_def;
              to_data_def; to_bvi_def; to_bvl_def; to_clos_def; to_flat_def] THEN
  BACKDEFAUX_LETS_TAC THEN SIMP[]);;

let prim_src_config_def = cake_def
  `prim_src_config =
     let (n0,next,env,envs,ds) =
       source_to_flat_compile_decs [] 1 (source_to_flat_config_next empty_config)
         source_to_flat_empty_env ARB prim_types_program in
     source_to_flat_config_next_fupd (K next)
       (source_to_flat_config_mod_env_fupd (K env) empty_config)`;;

(* HOL4 prim_src_config_eq (EVAL of prim_src_config) is not ported (an    *)
(* evaluation for HOL4 automation); the same for prim_config_eq below      *)

let prim_config_def = cake_def
  `prim_config =
     FST (to_flat (backend_config_source_conf_fupd (K empty_config) ARB)
            prim_types_program)`;;

let from_lab_def = cake_def
  `from_lab (asm_conf:(A)asm_config) (c:backend_config) names (p:((A)sec)list) (bm:B) =
     attach_bitmaps names c bm
       (lab_to_target_compile asm_conf (backend_config_lab_conf c) p)`;;

let from_stack_def = cake_def
  `from_stack (asm_conf:(A)asm_config) (c:backend_config) names p (bm:B) =
     let p = stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
               (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
               (asm_config_reg_count asm_conf -
                (LENGTH (asm_config_avoid_regs asm_conf) + 3))
               (asm_config_addr_offset asm_conf) p in
     from_lab asm_conf c names (p:((A)sec)list) bm`;;

let from_word_def = cake_def
  `from_word (asm_conf:(A)asm_config) (c:backend_config) names p =
     let (bm,c',fs,p) =
       word_to_stack_compile asm_conf
         (stack_to_lab_config_perf_calls (backend_config_stack_conf c)) p in
     let c = backend_config_word_conf_fupd (K c') c in
     from_stack asm_conf c names p bm`;;

let from_word_0_def = cake_def
  `from_word_0 (asm_conf:(A)asm_config) (c:backend_config) names p =
     let (col,prog) =
       word_to_word_compile (backend_config_word_to_word_conf c) asm_conf p in
     let c = backend_config_word_to_word_conf_fupd
               (\c. word_to_word_config_col_oracle_fupd (K col) c) c in
     from_word asm_conf c names prog`;;

let from_data_def = cake_def
  `from_data (asm_conf:(A)asm_config) (c:backend_config) names p =
     let (col,p) = data_to_word_compile (backend_config_data_conf c)
                     (backend_config_word_to_word_conf c) asm_conf p in
     let c = backend_config_word_to_word_conf_fupd
               (\c. word_to_word_config_col_oracle_fupd (K col) c) c in
     from_word asm_conf c names p`;;

(* HOL4: from_data_thm *)

let backend_from_data_thm = prove
 (`from_data (asm_conf:(A)asm_config) c names p =
     let p = compile_0 (backend_config_data_conf c) asm_conf p in
     from_word_0 asm_conf c names p`,
  REWRITE_TAC[from_data_def; compile_0_def; data_to_word_compile_def; from_word_0_def] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[]);;

let from_bvi_def = cake_def
  `from_bvi (asm_conf:(A)asm_config) (c:backend_config) names p =
     let p = bvi_to_data_compile_prog p in
     from_data asm_conf c names p`;;

let from_bvl_def = cake_def
  `from_bvl (asm_conf:(A)asm_config) (c:backend_config) names p =
     let (s,p,l,bl,n1,n2,n3,names) =
       bvl_to_bvi_compile (clos_to_bvl_config_start (backend_config_clos_conf c))
         (backend_config_bvl_conf c) names p in
     let names = union (fromAList (APPEND (APPEND (APPEND
                   (data_to_word_stub_names one) (word_to_stack_stub_names one))
                   (stack_alloc_stub_names one)) (stack_remove_stub_names one))) names in
     let c = backend_config_clos_conf_fupd
               (\c. clos_to_bvl_config_start_fupd (K s) c) c in
     let c = backend_config_bvl_conf_fupd
               (\c. bvl_to_bvi_config_inlines_fupd (K l)
                      (bvl_to_bvi_config_bvi_inlines_fupd (K bl)
                         (bvl_to_bvi_config_next_name1_fupd (K n1)
                            (bvl_to_bvi_config_next_name2_fupd (K n2)
                               (bvl_to_bvi_config_next_name3_fupd (K n3) c))))) c in
     from_bvi asm_conf c names p`;;

let from_clos_def = cake_def
  `from_clos (asm_conf:(A)asm_config) (c:backend_config) e =
     let (c',p,names) = clos_to_bvl_compile (backend_config_clos_conf c) e in
     let c = backend_config_clos_conf_fupd (K c') c in
     from_bvl asm_conf c names p`;;

let from_flat_def = cake_def
  `from_flat (asm_conf:(A)asm_config) (c:backend_config) p =
     let p = flat_to_clos_compile_prog p in
     from_clos asm_conf c p`;;

let from_source_def = cake_def
  `from_source (asm_conf:(A)asm_config) (c:backend_config) p =
     let p = source_to_source_compile p in
     let (c',p) = source_to_flat_compile (backend_config_source_conf c) p in
     let c = backend_config_source_conf_fupd (K c') c in
     from_flat asm_conf c p`;;

let compile_eq_from_source = prove
 (`backend_compile =
   (from_source:(A)asm_config->backend_config->dec list->
                (byte list#(A word)list#backend_config)option)`,
  REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[backend_compile_def; from_source_def; from_lab_def; from_stack_def;
              from_word_def; from_data_def; from_bvi_def; from_bvl_def; from_clos_def;
              from_flat_def] THEN
  BACKDEFAUX_LETS_TAC THEN SIMP[]);;

let to_livesets_0_def = cake_def
  `to_livesets_0 (asm_conf:(A)asm_config) (c:backend_config,p,names:mlstring spt) =
     let word_conf = backend_config_word_to_word_conf c in
     let alg = word_to_word_config_reg_alg word_conf in
     let p =
       MAP (\(name_num,arg_count,prog).
              let prog = word_simp_compile_exp prog in
              let maxv = max_var prog + 1 in
              let inst_prog = inst_select asm_conf maxv prog in
              let ssa_prog = full_ssa_cc_trans arg_count inst_prog in
              let rm_ssa_prog = remove_dead_prog ssa_prog in
              let cse_prog = word_common_subexp_elim rm_ssa_prog in
              let cp_prog = copy_prop cse_prog in
              let two_prog = three_to_two_reg_prog (asm_config_two_reg_arith asm_conf)
                               cp_prog in
              let unreach_prog = remove_unreach two_prog in
              let rm_prog = remove_dead_prog unreach_prog in
              (name_num,arg_count,rm_prog)) p in
     let data =
       MAP (\(name_num,arg_count,prog).
              let (heu_moves,spillcosts) = get_heuristics alg name_num prog in
              (get_clash_tree prog [],heu_moves,spillcosts,
               get_forced asm_conf prog [],get_stack_only prog)) p in
     ((asm_config_reg_count asm_conf - (5 + LENGTH (asm_config_avoid_regs asm_conf)),data),
      c,names,p)`;;

let to_livesets_def = cake_def
  `to_livesets (asm_conf:(A)asm_config) (c:backend_config) p =
     to_livesets_0 asm_conf (to_word_0 asm_conf c p)`;;

let to_data_conf_inv = prove
 (`to_data c p = (c',p',names) ==>
   backend_config_data_conf c' = backend_config_data_conf c /\
   backend_config_word_conf c' = backend_config_word_conf c /\
   backend_config_word_to_word_conf c' = backend_config_word_to_word_conf c /\
   backend_config_stack_conf c' = backend_config_stack_conf c /\
   backend_config_lab_conf c' = backend_config_lab_conf c`,
  REWRITE_TAC[to_data_def; to_bvi_def; to_bvl_def; to_clos_def; to_flat_def] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

let from_livesets_def = cake_def
  `from_livesets (asm_conf:(A)asm_config) ((k,data),c:backend_config,names,p) =
     let word_conf = backend_config_word_to_word_conf c in
     let (n_oracles,col) =
       next_n_oracle (LENGTH p) (word_to_word_config_col_oracle word_conf) in
     let alg = word_to_word_config_reg_alg word_conf in
     let prog_with_oracles = ZIP n_oracles (ZIP data p) in
     let p =
       MAP (\(col_opt,((tree,heu_moves,spillcosts,forced,fs),name_num,arg_count,prog)).
              match oracle_colour_ok k col_opt tree prog forced with
                NONE ->
                  let cp =
                    (match select_reg_alloc alg spillcosts k heu_moves tree forced fs with
                       M_success col -> apply_colour (total_colour col) prog
                     | M_failure _ -> prog) in
                  (name_num,arg_count,remove_must_terminate cp)
              | SOME col_prog -> (name_num,arg_count,remove_must_terminate col_prog))
         prog_with_oracles in
     let c = backend_config_word_to_word_conf_fupd
               (\c. word_to_word_config_col_oracle_fupd (K col) c) c in
     from_word asm_conf c names p`;;

(* HOL4: ZIP_MAP_MAP (local) *)

let backend_ZIP_MAP_MAP = prove
 (`!xs. ZIP (MAP (f:A->B) xs) (MAP (g:A->C) xs) = MAP (\x. (f x,g x)) xs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ZIP]);;

(* HOL4: EL_ZIP_MAP (local) *)

let EL_ZIP_MAP = prove
 (`!p q x. x < LENGTH q /\ x < LENGTH p
           ==> EL x (ZIP (q:B list) (MAP (f:A->C) p)) =
               (\(y,x). (x,f y)) (EL x (ZIP p q))`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; LT]; ALL_TAC] THEN
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `q:B list` list_CASES) THEN
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `x:num` num_CASES) THEN
  REWRITE_TAC[LENGTH; LT; LT_SUC; MAP; ZIP; EL; HD; TL] THEN
  ASM_MESON_TAC[]);;

(* helpers: the oracles of next_n_oracle n are n; a MAP over a ZIP          *)

let BACKDEFAUX_LENGTH_next_n_oracle = prove
 (`!n col (a:((num spt)option)list) b. next_n_oracle n col = (a,b) ==> LENGTH a = n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[next_n_oracle_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
  ASM_SIMP_TAC[LENGTH_TAKE; LENGTH_REPLICATE]);;

let BACKDEFAUX_MAP_ZIP = prove
 (`!(f:A#B->C) (g:B#(D#E)->C) (h:E->D) (s:A->E) (l1:A list) (l2:B list).
     LENGTH l2 = LENGTH l1 /\ (!x y. f (x,y) = g (y,(h (s x),s x)))
     ==> MAP f (ZIP l1 l2) = MAP g (ZIP l2 (ZIP (MAP h (MAP s l1)) (MAP s l1)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  SPEC_TAC(`l2:B list`,`l2:B list`) THEN SPEC_TAC(`l1:A list`,`l1:A list`) THEN
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `l2:B list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; MAP; ZIP] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[]);;

let from_word_0_to_livesets_0 = prove
 (`from_word_0 (asm_conf:(A)asm_config) c names p =
   from_livesets asm_conf (to_livesets_0 asm_conf (c,p,names))`,
  REWRITE_TAC[from_word_0_def; to_livesets_0_def; word_to_word_compile_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[from_livesets_def; LENGTH_MAP] THEN
  BACKDEFAUX_LETS_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC BACKDEFAUX_MAP_ZIP THEN CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP BACKDEFAUX_LENGTH_next_n_oracle); ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[full_compile_single_def; word_to_word_compile_single_def; word_alloc_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN BACKDEFAUX_LETS_TAC THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[]);;

(* HOL4 proves compile_oracle by unfolding everything; here: compile is     *)
(* from_source, which runs from_data on the result of to_data              *)

let BACKDEFAUX_from_source_to_data = prove
 (CASE_TERM
  `from_source (asm_conf:(A)asm_config) c p =
     let (c',p',names) = to_data c p in from_data asm_conf c' names p'`,
  REWRITE_TAC[from_source_def; from_flat_def; from_clos_def; from_bvl_def; from_bvi_def;
              to_data_def; to_bvi_def; to_bvl_def; to_clos_def; to_flat_def] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[]);;

let compile_oracle = prove
 (`from_livesets (asm_conf:(A)asm_config) (to_livesets asm_conf c p) =
   backend_compile asm_conf c p`,
  REWRITE_TAC[compile_eq_from_source; BACKDEFAUX_from_source_to_data; to_livesets_def;
              to_word_0_def; backend_from_data_thm; from_word_0_to_livesets_0] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[]);;

let compile_oracle_word_0 = prove
 (CASE_TERM
  `backend_compile (asm_conf:(A)asm_config) c p =
     let (c,p,names) = to_word_0 asm_conf c p in
     from_word_0 asm_conf c names p`,
  REWRITE_TAC[GSYM compile_oracle; from_word_0_to_livesets_0; to_livesets_def] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[]);;

(* HOL4 has to_livesets_invariant and to_livesets_0_invariant in a comment *)
(* (TODO delete?)                                                            *)

(* BACKDEFAUX_ASM_LETS_TAC: BACKDEFAUX_LETS_TAC that also simplifies record *)
(* accessors with the assumptions                                           *)

let BACKDEFAUX_ASM_LETS_TAC : tactic =
  let rws = [(record_info "backend_config").ri_accfupds; K_THM] in
  REPEAT (CHANGED_TAC (CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC rws) ORELSE
          BACKDEFAUX_PAIRARG_TAC);;

let to_data_change_config = prove
 (`to_data c1 prog = (c1',prog') ==>
   backend_config_source_conf c2 = backend_config_source_conf c1 /\
   backend_config_clos_conf c2 = backend_config_clos_conf c1 /\
   backend_config_bvl_conf c2 = backend_config_bvl_conf c1
   ==> to_data c2 prog =
       (backend_config_source_conf_fupd (K (backend_config_source_conf c1'))
          (backend_config_clos_conf_fupd (K (backend_config_clos_conf c1'))
             (backend_config_bvl_conf_fupd (K (backend_config_bvl_conf c1')) c2)),
        prog')`,
  DISCH_TAC THEN STRIP_TAC THEN UNDISCH_TAC `to_data c1 prog = (c1',prog')` THEN
  REWRITE_TAC[to_data_def; to_bvi_def; to_bvl_def; to_clos_def; to_flat_def] THEN
  BACKDEFAUX_ASM_LETS_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN REWRITE_TAC[] THEN
  REWRITE_TAC[backend_config_component_equality] THEN
  ASM_REWRITE_TAC[(record_info "backend_config").ri_accfupds; K_THM]);;

let ensure_fp_conf_ok_def = cake_def
  `ensure_fp_conf_ok (asm_c:(A)asm_config) (c:data_to_word_config) =
     data_to_word_config_has_fp_ops_fupd (K (1 < asm_config_fp_reg_count asm_c))
       (data_to_word_config_has_fp_tern_fupd
          (K (asm_config_ISA asm_c = ARMv7 /\ 2 < asm_config_fp_reg_count asm_c)) c)`;;

let backend_progs_INFO = cake_record "backend_progs"
  ["env_id","num#num";
   "source_prog","dec list";
   "flat_prog","flat_exp list";
   "clos_prog","clos_exp list#(num#num#clos_exp)list";
   "bvl_prog","(num#num#bvl_exp)list";
   "bvi_prog","(num#num#bvi_exp)list";
   "data_prog","(num#num#data_prog)list";
   "word_prog","(num#num#(A)wl_prog)list";
   "stack_prog","(num#(A)stack_prog)list";
   "cur_bm","(A word)list";
   "lab_prog","((A)sec)list";
   "target_prog","(byte list#(A word)list)option"];;

let empty_progs_def = cake_def
  `empty_progs =
     backend_progs_REC (0,0) [] [] ([],[]) [] [] [] [] [] [] [] (SOME ([],[]))
     :(A)backend_progs`;;

let keep_progs_def = cake_def
  `keep_progs k (ps:B list) = if k then ps else []`;;

let compile_inc_progs_def = cake_def
  `compile_inc_progs k (asm_conf:(A)asm_config) (c:backend_config) p_tup =
     let (env_id,p) = p_tup in
     let ps = backend_progs_env_id_fupd (K env_id)
                (backend_progs_source_prog_fupd (K p) (empty_progs:(A)backend_progs)) in
     let p = source_to_source_compile p in
     let (c',p) = inc_compile env_id (backend_config_source_conf c) p in
     let ps = backend_progs_flat_prog_fupd (K (keep_progs k p)) ps in
     let c = backend_config_source_conf_fupd (K c') c in
     let p = inc_compile_decs p in
     let ps = backend_progs_clos_prog_fupd (K ((keep_progs k ## keep_progs k) p)) ps in
     let (c',p) = clos_to_bvl_compile_inc (backend_config_clos_conf c) p in
     let c = backend_config_clos_conf_fupd (K c') c in
     let ps = backend_progs_bvl_prog_fupd (K (keep_progs k p)) ps in
     let (c',p) = bvl_to_bvi_compile_inc_all (backend_config_bvl_conf c) p in
     let c = backend_config_bvl_conf_fupd (K c') c in
     let ps = backend_progs_bvi_prog_fupd (K (keep_progs k p)) ps in
     let p = bvi_to_data_compile_prog p in
     let ps = backend_progs_data_prog_fupd (K (keep_progs k p)) ps in
     let dc = ensure_fp_conf_ok asm_conf (backend_config_data_conf c) in
     let p = MAP (data_to_word_compile_part dc) p in
     let reg_count1 = asm_config_reg_count asm_conf -
                      (5 + LENGTH (asm_config_avoid_regs asm_conf)) in
     let p = MAP (\p. full_compile_single (asm_config_two_reg_arith asm_conf) reg_count1
                        (word_to_word_config_reg_alg (backend_config_word_to_word_conf c))
                        asm_conf (p,NONE)) p in
     let ps = backend_progs_word_prog_fupd (K (keep_progs k p)) ps in
     let bm0 = word_to_stack_config_bitmaps_length (backend_config_word_conf c) in
     let (p,fs,bm) =
       compile_word_to_stack asm_conf
         (stack_to_lab_config_perf_calls (backend_config_stack_conf c)) reg_count1 p
         (Nil,bm0) in
     let cur_bm = append (FST bm) in
     let c = backend_config_word_conf_fupd
               (K (word_to_stack_config_bitmaps_length_fupd (K (SND bm))
                     (backend_config_word_conf c))) c in
     let ps = backend_progs_stack_prog_fupd (K (keep_progs k p))
                (backend_progs_cur_bm_fupd (K cur_bm) ps) in
     let reg_count2 = asm_config_reg_count asm_conf -
                      (3 + LENGTH (asm_config_avoid_regs asm_conf)) in
     let p = compile_no_stubs
               (stack_to_lab_config_reg_names (backend_config_stack_conf c))
               (stack_to_lab_config_jump (backend_config_stack_conf c))
               (asm_config_addr_offset asm_conf) reg_count2 p in
     let ps = backend_progs_lab_prog_fupd (K (keep_progs k p)) ps in
     let target = lab_to_target_compile asm_conf (backend_config_lab_conf c)
                    (p:((A)sec)list) in
     let ps = backend_progs_target_prog_fupd
                (K (OPTION_MAP (\(bytes,c'). (bytes,cur_bm)) target)) ps in
     let c = backend_config_lab_conf_fupd
               (match target with NONE -> I | SOME (bytes,c') -> K c') c in
     (c,ps)`;;

let compile_inc_progs_for_eval_def = cake_def
  `compile_inc_progs_for_eval (asm_conf:(A)asm_config) x =
     let (env_id,c',decs) = x in
     let (c'',ps) = compile_inc_progs T asm_conf c' (env_id,decs) in
     OPTION_MAP (\(bs,ws). (c'',bs,MAP upper_w2w ws))
       (backend_progs_target_prog ps)`;;

let to_word_0_invariant = prove
 (CASE_TERM
  `word_to_word_config_reg_alg wc =
   word_to_word_config_reg_alg (backend_config_word_to_word_conf c)
   ==> to_word_0 (asm_conf:(A)asm_config) (backend_config_word_to_word_conf_fupd (K wc) c) p =
       let (c,p,names) = to_word_0 asm_conf c p in
       (backend_config_word_to_word_conf_fupd (K wc) c,p,names)`,
  DISCH_TAC THEN
  REWRITE_TAC[to_word_0_def; to_data_def; to_bvi_def; to_bvl_def; to_clos_def;
              to_flat_def] THEN
  BACKDEFAUX_ASM_LETS_TAC THEN REWRITE_TAC[PAIR_EQ; backend_config_component_equality] THEN
  REWRITE_TAC[(record_info "backend_config").ri_accfupds; K_THM]);;

let compile_inc_progs_for_eval_eq = prove
 (CASE_TERM
  `compile_inc_progs_for_eval (asm_conf:(A)asm_config) (env_id,c,p) =
     let p = source_to_source_compile p in
     let (c',p) = inc_compile env_id (backend_config_source_conf c) p in
     let _ = empty_ffi (implode "finished: source_to_flat") in
     let c = backend_config_source_conf_fupd (K c') c in
     let p = inc_compile_decs p in
     let _ = empty_ffi (implode "finished: flat_to_clos") in
     let (c',p) = clos_to_bvl_compile_inc (backend_config_clos_conf c) p in
     let _ = empty_ffi (implode "finished: clos_to_bvl") in
     let c = backend_config_clos_conf_fupd (K c') c in
     let (c',p) = bvl_to_bvi_compile_inc_all (backend_config_bvl_conf c) p in
     let _ = empty_ffi (implode "finished: bvl_to_bvi") in
     let c = backend_config_bvl_conf_fupd (K c') c in
     let p = bvi_to_data_compile_prog p in
     let _ = empty_ffi (implode "finished: bvi_to_data") in
     let dc = ensure_fp_conf_ok asm_conf (backend_config_data_conf c) in
     let p = MAP (data_to_word_compile_part dc) p in
     let reg_count1 = asm_config_reg_count asm_conf -
                      (5 + LENGTH (asm_config_avoid_regs asm_conf)) in
     let p = MAP (\p. full_compile_single_for_eval (asm_config_two_reg_arith asm_conf)
                        reg_count1
                        (word_to_word_config_reg_alg (backend_config_word_to_word_conf c))
                        asm_conf (p,NONE)) p in
     let _ = empty_ffi (implode "finished: data_to_word") in
     let bm0 = word_to_stack_config_bitmaps_length (backend_config_word_conf c) in
     let (p,fs,bm) =
       compile_word_to_stack asm_conf
         (stack_to_lab_config_perf_calls (backend_config_stack_conf c)) reg_count1 p
         (Nil,bm0) in
     let _ = empty_ffi (implode "finished: word_to_stack") in
     let cur_bm = append (FST bm) in
     let c = backend_config_word_conf_fupd
               (K (word_to_stack_config_bitmaps_length_fupd (K (SND bm))
                     (backend_config_word_conf c))) c in
     let reg_count2 = asm_config_reg_count asm_conf -
                      (3 + LENGTH (asm_config_avoid_regs asm_conf)) in
     let p = compile_no_stubs
               (stack_to_lab_config_reg_names (backend_config_stack_conf c))
               (stack_to_lab_config_jump (backend_config_stack_conf c))
               (asm_config_addr_offset asm_conf) reg_count2 p in
     let _ = empty_ffi (implode "finished: stack_to_lab") in
     let target = lab_to_target_compile asm_conf (backend_config_lab_conf c)
                    (p:((A)sec)list) in
     let _ = empty_ffi (implode "finished: lab_to_target") in
     let c = backend_config_lab_conf_fupd
               (match target with NONE -> I | SOME (_,c') -> K c') c in
     OPTION_MAP (\x. (c,FST x,MAP upper_w2w cur_bm)) target`,
  let rws = [(record_info "backend_config").ri_accfupds;
             (record_info "backend_progs").ri_accfupds; K_THM] in
  REWRITE_TAC[compile_inc_progs_for_eval_def; compile_inc_progs_def;
              full_compile_single_for_eval_eq] THEN
  BACKDEFAUX_LETS_RW_TAC rws THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[OPTION_MAP_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let ffinames_to_string_list_def = cake_def
  `(ffinames_to_string_list [] = []) /\
   (ffinames_to_string_list (CONS (ExtCall s) rest) =
      CONS s (ffinames_to_string_list rest)) /\
   (ffinames_to_string_list (CONS (SharedMem _) rest) =
      ffinames_to_string_list rest)`;;

let set_oracle_def = cake_def
  `set_oracle (c:backend_config) oracle =
     backend_config_word_to_word_conf_fupd
       (K (word_to_word_config_col_oracle_fupd (K oracle)
             (backend_config_word_to_word_conf c))) c`;;
