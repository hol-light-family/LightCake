(* ========================================================================= *)
(* backend_passes: port of HOL4 compiler/backend/backend_passesScript.sml    *)
(* (CakeML v3479).                                                           *)
(* Reformulates compile definition to expose the result of each internal    *)
(* compiler pass.                                                            *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as notes/naming/names.tsv says: the any_prog constructors        *)
(*   backend_passes_Clos, backend_passes_Data, backend_passes_Word,          *)
(*   backend_passes_Lab (the others keep their names), the theorems          *)
(*   backend_passes_to_word_thm, backend_passes_from_data_thm,               *)
(*   backend_passes_compile_alt.                                             *)
(* - The passes are called by their port names (source_let_compile_decs,    *)
(*   clos_mti_compile, bvl_inline_remove_ticks, ...); HOL4 stubs (:'a) is    *)
(*   data_to_word_stubs (:A); FOLDR f e l is ITLIST f l e; ++ is APPEND; the  *)
(*   mlstring literal of s is implode s; ZIP (l1,l2) is ZIP l1 l2.           *)
(* ========================================================================= *)

needs "compiler/backend/backend.ml";;
needs "compiler/backend/presLang.ml";;

prioritize_num();;
type_invention_error := true;;

let any_prog_INDUCT,any_prog_RECURSION = cake_type
  "any_prog = Source (dec list)
            | Flat (flat_exp list)
            | backend_passes_Clos (clos_exp list) ((num#num#clos_exp)list)
            | Bvl ((num#num#bvl_exp)list) (mlstring spt)
            | Bvi ((num#num#bvi_exp)list) (mlstring spt)
            | backend_passes_Data ((num#num#data_prog)list) (mlstring spt)
            | backend_passes_Word ((num#num#(A)wl_prog)list) (mlstring spt)
            | Stack ((num#(A)stack_prog)list) (mlstring spt)
            | backend_passes_Lab (((A)sec)list) (mlstring spt)";;

let to_flat_all_def = cake_def
  `to_flat_all (c:backend_config) p =
     let ps = [] in
     let ps = APPEND ps [(implode "original source code",Source p)] in
     let p = source_let_compile_decs p in
     let ps = APPEND ps [(implode "after source_let",Source p)] in
     let (c',p) = source_to_flat_compile_prog (backend_config_source_conf c) p in
     let ps = APPEND ps [(implode "after source_to_flat",Flat p)] in
     let p = remove_flat_prog p in
     let ps = APPEND ps [(implode "after remove_flat",Flat p)] in
     let p = MAP (compile_dec (source_to_flat_config_pattern_cfg c')) p in
     let ps = APPEND ps [(implode "after flat_pattern",Flat p)] in
     let c = backend_config_source_conf_fupd (K c') c in
     (ps:(mlstring#(A)any_prog)list,c,p)`;;

let to_flat_thm = prove
 (`SND (to_flat_all c p:(mlstring#(A)any_prog)list#backend_config#flat_exp list) =
   to_flat c p`,
  REWRITE_TAC[to_flat_all_def; to_flat_def; source_to_source_compile_def;
              source_to_flat_compile_def; compile_flat_def; o_THM] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[]);;

let to_clos_all_def = cake_def
  `to_clos_all (c:backend_config) p =
     let (ps,c,p) = to_flat_all c p in
     let p = flat_to_clos_compile_prog p in
     let ps = APPEND ps [(implode "after flat_to_clos",backend_passes_Clos p [])] in
     (ps:(mlstring#(A)any_prog)list,c,p)`;;

let to_clos_thm = prove
 (`SND (to_clos_all c p:(mlstring#(A)any_prog)list#backend_config#clos_exp list) =
   to_clos c p`,
  REWRITE_TAC[to_clos_all_def; to_clos_def; GSYM (GEN_ALL to_flat_thm)] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[]);;

let to_bvl_all_def = cake_def
  `to_bvl_all (c:backend_config) p =
     let (ps,c,es0) = to_clos_all c p in
     let c0 = backend_config_clos_conf c in
     let es = clos_mti_compile (clos_to_bvl_config_do_mti c0)
                (clos_to_bvl_config_max_app c0) es0 in
     let ps = APPEND ps [(implode "after clos_mti",backend_passes_Clos es [])] in
     let loc = clos_to_bvl_config_next_loc c0 + MAX 1 (LENGTH es) in
     let loc = if loc MOD 2 = 0 then loc else loc + 1 in
     let (n,es) = renumber_code_locs_list loc es in
     let ps = APPEND ps [(implode "after clos_number",backend_passes_Clos es [])] in
     let (kc,es) = clos_known_compile (clos_to_bvl_config_known_conf c0) es in
     let ps = APPEND ps [(implode "after clos_known",backend_passes_Clos es [])] in
     let (es,g,aux) = clos_call_compile (clos_to_bvl_config_do_call c0) es in
     let ps = APPEND ps [(implode "after clos_call",backend_passes_Clos es aux)] in
     let prog = APPEND (chain_exps (clos_to_bvl_config_next_loc c0) es) aux in
     let prog = clos_annotate_compile prog in
     let ps = APPEND ps [(implode "after clos_annotate",backend_passes_Clos [] prog)] in
     let c1 = clos_to_bvl_config_start_fupd (K (clos_to_bvl_config_next_loc c0))
                (clos_to_bvl_config_next_loc_fupd (K n)
                   (clos_to_bvl_config_known_conf_fupd (K kc)
                      (clos_to_bvl_config_call_state_fupd (K (g,aux)) c0))) in
     let init_stubs = toAList (clos_to_bvl_init_code (clos_to_bvl_config_max_app c1)) in
     let init_globs =
       [(num_stubs (clos_to_bvl_config_max_app c1) - 2,2,force_thunk_code);
        (num_stubs (clos_to_bvl_config_max_app c1) - 1,0,
         init_globals (clos_to_bvl_config_max_app c1)
           (num_stubs (clos_to_bvl_config_max_app c1) + clos_to_bvl_config_start c1))] in
     let comp_progs = clos_to_bvl_compile_prog (clos_to_bvl_config_max_app c1) prog in
     let prog' = APPEND (APPEND init_stubs init_globs) comp_progs in
     let func_names =
       make_name_alist (MAP FST prog') prog (num_stubs (clos_to_bvl_config_max_app c1))
         (clos_to_bvl_config_next_loc c0) (LENGTH es0) in
     let ps = APPEND ps [(implode "after clos_to_bvl",Bvl prog' func_names)] in
     let c2 = clos_to_bvl_config_start_fupd
                (K (num_stubs (clos_to_bvl_config_max_app c1) - 1)) c1 in
     let p = code_sort prog' in
     let c = backend_config_clos_conf_fupd (K c2) c in
     (ps:(mlstring#(A)any_prog)list,c,p,func_names)`;;

let to_bvl_thm = prove
 (`SND (to_bvl_all c p:(mlstring#(A)any_prog)list#backend_config#(num#num#bvl_exp)list#
                       mlstring spt) =
   to_bvl c p`,
  REWRITE_TAC[to_bvl_all_def; to_bvl_def; GSYM (GEN_ALL to_clos_thm);
              clos_to_bvl_compile_def; compile_common_def] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[(record_info "clos_to_bvl_config").ri_accfupds;
              (record_info "backend_config").ri_accfupds; K_THM]);;

let to_bvi_all_def = cake_def
  `to_bvi_all (c:backend_config) p =
     let (ps,c,p,names) = to_bvl_all c p in
     let start = clos_to_bvl_config_start (backend_config_clos_conf c) in
     let c0 = backend_config_bvl_conf c in
     let limit = bvl_to_bvi_config_inline_size_limit c0 in
     let split_seq = bvl_to_bvi_config_split_main_at_seq c0 in
     let cut_size = bvl_to_bvi_config_exp_cut c0 in
     let (inlines,prog1) = tick_compile_prog limit LN p in
     let prog = MAP (\(name,arity,exp). (name,arity,HD (bvl_inline_remove_ticks [exp])))
                  prog1 in
     let ps = APPEND ps [(implode "after bvl_inline and remove_ticks",Bvl prog names)] in
     let prog = MAP (\(name,arity,exp). (name,arity,bvl_inline_let_op_sing exp)) prog in
     let ps = APPEND ps [(implode "after let_op_sing",Bvl prog names)] in
     let prog = MAP (\(name,arity,exp).
                       (name,arity,compile_any split_seq cut_size arity exp)) prog in
     let ps = APPEND ps [(implode "after bvl_handle",Bvl prog names)] in
     let (loc,code,n1) = bvl_to_bvi_compile_prog start 0 prog in
     let (n2,code2) = bvi_tailrec_compile_prog (bvl_to_bvi_config_do_tailrec c0)
                        (bvl_num_stubs + 2) code in
     let (n3,code3) = bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc c0)
                        (bvl_num_stubs + 3) code2 in
     let (bvi_inlines,code') = bvi_inline_compile_prog code3 in
     let (s,p,l,bl,n1,n2,n3,names) =
       (loc,code',inlines,bvi_inlines,n1,n2,n3,
        bvl_to_bvi_get_names (MAP FST code') names) in
     let names = union (fromAList (APPEND (APPEND (APPEND
                   (data_to_word_stub_names one) (word_to_stack_stub_names one))
                   (stack_alloc_stub_names one)) (stack_remove_stub_names one))) names in
     let ps = APPEND ps [(implode "after bvl_to_bvi",Bvi code names)] in
     let ps = APPEND ps [(implode "after bvi_tailrec",Bvi code2 names)] in
     let ps = APPEND ps [(implode "after bvi_tmc",Bvi code3 names)] in
     let ps = APPEND ps [(implode "after bvi_inline",Bvi code' names)] in
     let c = backend_config_clos_conf_fupd
               (\c. clos_to_bvl_config_start_fupd (K s) c) c in
     let c = backend_config_bvl_conf_fupd
               (\c. bvl_to_bvi_config_inlines_fupd (K l)
                      (bvl_to_bvi_config_bvi_inlines_fupd (K bl)
                         (bvl_to_bvi_config_next_name1_fupd (K n1)
                            (bvl_to_bvi_config_next_name2_fupd (K n2)
                               (bvl_to_bvi_config_next_name3_fupd (K n3) c))))) c in
     (ps:(mlstring#(A)any_prog)list,c,p,names)`;;

(* the bvl passes of to_bvi_all are bvl_inline_optimise (local helper) *)

let BACKDEFAUX_bvl_optimise_MAP = prove
 (`!split_seq cut_size (l:(num#num#bvl_exp)list).
     MAP (\(name,arity,exp). (name,arity,compile_any split_seq cut_size arity exp))
       (MAP (\(name,arity,exp). (name,arity,bvl_inline_let_op_sing exp))
          (MAP (\(name,arity,exp). (name,arity,HD (bvl_inline_remove_ticks [exp]))) l)) =
     MAP (bvl_inline_optimise split_seq cut_size) l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAP_MAP_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; bvl_inline_optimise_def]);;

let to_bvi_thm = prove
 (`SND (to_bvi_all c p:(mlstring#(A)any_prog)list#backend_config#(num#num#bvi_exp)list#
                       mlstring spt) =
   to_bvi c p`,
  REWRITE_TAC[to_bvi_all_def; to_bvi_def; GSYM (GEN_ALL to_bvl_thm);
              bvl_to_bvi_compile_def; bvl_inline_compile_prog_def;
              bvl_inline_compile_inc_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[BACKDEFAUX_bvl_optimise_MAP] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[(record_info "backend_config").ri_accfupds; K_THM]);;

let to_data_all_def = cake_def
  `to_data_all (c:backend_config) p =
     let (ps,c,p,names) = to_bvi_all c p in
     let p = MAP (\(a,n,e). (a,n,FST (bvi_to_data_compile n (COUNT_LIST n) T [] [e]))) p in
     let ps = APPEND ps [(implode "after bvi_to_data",backend_passes_Data p names)] in
     let p = MAP (\(a,n,e). (a,n,FST (data_live_compile e LN))) p in
     let ps = APPEND ps [(implode "after data_live",backend_passes_Data p names)] in
     let p = MAP (\(a,n,e). (a,n,simp e data_Skip)) p in
     let ps = APPEND ps [(implode "after data_simp",backend_passes_Data p names)] in
     let p = MAP (\(a,n,e). (a,n,data_space_compile e)) p in
     let ps = APPEND ps [(implode "after data_space",backend_passes_Data p names)] in
     (ps:(mlstring#(A)any_prog)list,c,p,names)`;;

(* the data passes of to_data_all are bvi_to_data_compile_prog (local     *)
(* helper)                                                                   *)

let BACKDEFAUX_data_compile_MAP = prove
 (`!(l:(num#num#bvi_exp)list).
     MAP (\(a,n,e). (a,n,data_space_compile e))
       (MAP (\(a,n,e). (a,n,simp e data_Skip))
          (MAP (\(a,n,e). (a,n,FST (data_live_compile e LN)))
             (MAP (\(a,n,e). (a,n,FST (bvi_to_data_compile n (COUNT_LIST n) T [] [e]))) l))) =
     bvi_to_data_compile_prog l`,
  GEN_TAC THEN REWRITE_TAC[MAP_MAP_o; bvi_to_data_compile_prog_def] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; bvi_to_data_compile_part_def;
              bvi_to_data_compile_exp_def; bvi_to_data_optimise_def]);;

let to_data_thm = prove
 (`SND (to_data_all (c:backend_config) p:(mlstring#(A)any_prog)list#backend_config#
                       (num#num#data_prog)list#mlstring spt) =
   to_data c p`,
  REWRITE_TAC[to_data_all_def; to_data_def; GSYM (GEN_ALL to_bvi_thm)] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[BACKDEFAUX_data_compile_MAP] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[]);;

(* NOTE: this definition is meant to minimize code duplication in the      *)
(* explorer pretty printing.                                                 *)

let word_internal_all_def = cake_def
  `word_internal_all (asm_conf:(A)asm_config) (ps:(mlstring#(A)any_prog)list) names
       (p:(num#num#(A)wl_prog)list) =
     let two_reg_arith = asm_config_two_reg_arith asm_conf in
     let p = MAP (\(name_num,arg_count,prog).
                    (name_num,arg_count,word_simp_compile_exp prog)) p in
     let ps = APPEND ps [(implode "after word_simp",backend_passes_Word p names)] in
     let p = MAP (\(name_num,arg_count,prog).
                    (name_num,arg_count,inst_select asm_conf (max_var prog + 1) prog)) p in
     let ps = APPEND ps [(implode "after word_inst",backend_passes_Word p names)] in
     let p = MAP (\(name_num,arg_count,prog).
                    (name_num,arg_count,full_ssa_cc_trans arg_count prog)) p in
     let ps = APPEND ps [(implode "after word_ssa",backend_passes_Word p names)] in
     let p = MAP (\(name_num,arg_count,prog).
                    (name_num,arg_count,remove_dead_prog prog)) p in
     let ps = APPEND ps [(implode "after remove_dead in word_ssa",
                          backend_passes_Word p names)] in
     let p = MAP (\(name_num,arg_count,prog).
                    (name_num,arg_count,word_common_subexp_elim prog)) p in
     let ps = APPEND ps [(implode "after word_cse",backend_passes_Word p names)] in
     let p = MAP (\(name_num,arg_count,prog).
                    (name_num,arg_count,copy_prop prog)) p in
     let ps = APPEND ps [(implode "after word_copy",backend_passes_Word p names)] in
     let p = MAP (\(name_num,arg_count,prog).
                    (name_num,arg_count,three_to_two_reg_prog two_reg_arith prog)) p in
     let ps = APPEND ps [(implode "after three_to_two_reg from word_inst",
                          backend_passes_Word p names)] in
     let p = MAP (\(name_num,arg_count,prog).
                    (name_num,arg_count,remove_unreach prog)) p in
     let ps = APPEND ps [(implode "after word_unreach",backend_passes_Word p names)] in
     let p = MAP (\(name_num,arg_count,prog).
                    (name_num,arg_count,remove_dead_prog prog)) p in
     let ps = APPEND ps [(implode "after remove_dead in word_alloc",
                          backend_passes_Word p names)] in
     (p,ps)`;;

let to_word_all_def = cake_def
  `to_word_all (asm_conf:(A)asm_config) (c:backend_config) p =
     let (ps,c,p,names) = to_data_all c p in
     let word_conf = backend_config_word_to_word_conf c in
     let data_conf = backend_config_data_conf c in
     let data_conf =
       data_to_word_config_has_fp_ops_fupd (K (1 < asm_config_fp_reg_count asm_conf))
         (data_to_word_config_has_fp_tern_fupd
            (K (asm_config_ISA asm_conf = ARMv7 /\ 2 < asm_config_fp_reg_count asm_conf))
            data_conf) in
     let p = APPEND (data_to_word_stubs (:A) data_conf)
                    (MAP (data_to_word_compile_part data_conf) p) in
     let ps = APPEND ps [(implode "after data_to_word",backend_passes_Word p names)] in
     let (p,ps) = word_internal_all asm_conf ps names p in
     let reg_count = asm_config_reg_count asm_conf -
                     (5 + LENGTH (asm_config_avoid_regs asm_conf)) in
     let alg = word_to_word_config_reg_alg word_conf in
     let (n_oracles,col) =
       next_n_oracle (LENGTH p) (word_to_word_config_col_oracle word_conf) in
     let p = MAP (\((name_num,arg_count,prog),col_opt).
                    (name_num,arg_count,
                     remove_must_terminate
                       (word_alloc name_num asm_conf alg reg_count prog col_opt)))
               (ZIP p n_oracles) in
     let ps = APPEND ps [(implode "after word_alloc (and remove_must_terminate)",
                          backend_passes_Word p names)] in
     let c = backend_config_word_to_word_conf_fupd
               (\c. word_to_word_config_col_oracle_fupd (K col) c) c in
     (ps:(mlstring#(A)any_prog)list,c,p,names)`;;

let LENGTH_next_n_oracle = prove
 (`next_n_oracle n col = (a,b) ==> LENGTH a = n`,
  MATCH_ACCEPT_TAC BACKDEFAUX_LENGTH_next_n_oracle);;

(* HOL4: ZIP_MAP_1 (local); f2 is unused, as in HOL4 *)

let ZIP_MAP_1 = prove
 (`!(l1:A list) (l2:B list) (f1:A->C) (f2:B->D).
     LENGTH l1 = LENGTH l2
     ==> ZIP (MAP f1 l1) l2 = MAP (\p. (f1 (FST p),SND p)) (ZIP l1 l2)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `l2:B list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; MAP; ZIP] THEN
  ASM_SIMP_TAC[]);;

(* a MAP over a ZIP of a MAP (local helper; HOL4 uses ZIP_MAP_1 and         *)
(* MAP_MAP_o)                                                                *)

let BACKDEFAUX_MAP_ZIP_MAP = prove
 (`!(f:A->B) (g:B#C->D) (h:A#C->D) (l:A list) (no:C list).
     LENGTH no = LENGTH l /\ (!x y. g (f x,y) = h (x,y))
     ==> MAP g (ZIP (MAP f l) no) = MAP h (ZIP l no)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  SPEC_TAC(`no:C list`,`no:C list`) THEN SPEC_TAC(`l:A list`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `no:C list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; MAP; ZIP] THEN ASM_SIMP_TAC[]);;

(* HOL4: to_word_thm *)

let backend_passes_to_word_thm = prove
 (`SND (to_word_all (asm_conf:(A)asm_config) c p) = to_word asm_conf c p`,
  REWRITE_TAC[to_word_all_def; to_word_def; GSYM (GEN_ALL to_data_thm);
              data_to_word_compile_def; word_to_word_compile_def; word_internal_all_def] THEN
  BACKDEFAUX_LETS_RW_TAC[LENGTH_MAP] THEN
  REWRITE_TAC[(record_info "backend_config").ri_accfupds; K_THM; PAIR_EQ] THEN
  REWRITE_TAC[MAP_MAP_o] THEN MATCH_MP_TAC BACKDEFAUX_MAP_ZIP_MAP THEN CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP BACKDEFAUX_LENGTH_next_n_oracle); ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[full_compile_single_def; word_to_word_compile_single_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[]);;

let to_stack_all_def = cake_def
  `to_stack_all (asm_conf:(A)asm_config) (c:backend_config) p =
     let (ps,c,p,names) = to_word_all asm_conf c p in
     let (bm,c',fs,p) =
       word_to_stack_compile asm_conf
         (stack_to_lab_config_perf_calls (backend_config_stack_conf c)) p in
     let ps = APPEND ps [(implode "after word_to_stack",Stack p names)] in
     let c = backend_config_word_conf_fupd (K c') c in
     (ps:(mlstring#(A)any_prog)list,bm,c,p,names)`;;

let to_stack_thm = prove
 (`SND (to_stack_all (asm_conf:(A)asm_config) c p) = to_stack asm_conf c p`,
  REWRITE_TAC[to_stack_all_def; to_stack_def; GSYM (GEN_ALL backend_passes_to_word_thm)] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[]);;

let to_lab_all_def = cake_def
  `to_lab_all (asm_conf:(A)asm_config) (c:backend_config) p =
     let (ps,bm,c,p,names) = to_stack_all asm_conf c p in
     let stack_conf = backend_config_stack_conf c in
     let data_conf = backend_config_data_conf c in
     let max_heap = 2 * max_heap_limit (:A) (backend_config_data_conf c) - 1 in
     let sp = asm_config_reg_count asm_conf -
              (LENGTH (asm_config_avoid_regs asm_conf) + 3) in
     let offset = asm_config_addr_offset asm_conf in
     let prog = stack_rawcall_compile p in
     let ps = APPEND ps [(implode "after stack_rawcall",Stack prog names)] in
     let prog = stack_alloc_compile data_conf prog in
     let ps = APPEND ps [(implode "after stack_alloc",Stack prog names)] in
     let prog = stack_remove_compile (stack_to_lab_config_jump stack_conf) offset
                  (is_gen_gc (data_to_word_config_gc_kind data_conf))
                  max_heap sp InitGlobals_location prog in
     let ps = APPEND ps [(implode "after stack_remove",Stack prog names)] in
     let prog = stack_names_compile (stack_to_lab_config_reg_names stack_conf) prog in
     let ps = APPEND ps [(implode "after stack_names",Stack prog names)] in
     let p = MAP prog_to_section prog in
     let ps = APPEND ps [(implode "after stack_to_lab",backend_passes_Lab p names)] in
     (ps:(mlstring#(A)any_prog)list,bm:(A word)list,c,p:((A)sec)list,names)`;;

let to_lab_thm = prove
 (`SND (to_lab_all (asm_conf:(A)asm_config) c p) = to_lab asm_conf c p`,
  REWRITE_TAC[to_lab_all_def; to_lab_def; stack_to_lab_compile_def;
              GSYM (GEN_ALL to_stack_thm)] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[]);;

let to_target_all_def = cake_def
  `to_target_all (asm_conf:(A)asm_config) (c:backend_config) p =
     let (ps,bm,c,p,names) = to_lab_all asm_conf c p in
     let p = filter_skip p in
     let ps = APPEND ps [(implode "after filter_skip",backend_passes_Lab p names)] in
     let p = compile_lab asm_conf (backend_config_lab_conf c) p in
     (ps:(mlstring#(A)any_prog)list,attach_bitmaps names c bm p)`;;

let to_target_thm = prove
 (`SND (to_target_all (asm_conf:(A)asm_config) c p) = to_target asm_conf c p`,
  REWRITE_TAC[to_target_all_def; to_target_def; lab_to_target_compile_def;
              GSYM (GEN_ALL to_lab_thm)] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[]);;

let from_lab_all_def = cake_def
  `from_lab_all (ps:(mlstring#(A)any_prog)list) (asm_conf:(A)asm_config)
       (c:backend_config) names p (bm:(A word)list) =
     let p = filter_skip p in
     let ps = APPEND ps [(implode "after filter_skip",backend_passes_Lab p names)] in
     let p = compile_lab asm_conf (backend_config_lab_conf c) p in
     (ps:(mlstring#(A)any_prog)list,attach_bitmaps names c bm p)`;;

let from_lab_thm = prove
 (`SND (from_lab_all ps (asm_conf:(A)asm_config) c names p bm) =
   from_lab asm_conf c names p bm`,
  REWRITE_TAC[from_lab_all_def; from_lab_def; lab_to_target_compile_def] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[]);;

let from_stack_all_def = cake_def
  `from_stack_all (ps:(mlstring#(A)any_prog)list) (asm_conf:(A)asm_config)
       (c:backend_config) names p bm =
     let stack_conf = backend_config_stack_conf c in
     let data_conf = backend_config_data_conf c in
     let max_heap = 2 * max_heap_limit (:A) (backend_config_data_conf c) - 1 in
     let sp = asm_config_reg_count asm_conf -
              (LENGTH (asm_config_avoid_regs asm_conf) + 3) in
     let offset = asm_config_addr_offset asm_conf in
     let prog = stack_rawcall_compile p in
     let ps = APPEND ps [(implode "after stack_rawcall",Stack prog names)] in
     let prog = stack_alloc_compile data_conf prog in
     let ps = APPEND ps [(implode "after stack_alloc",Stack prog names)] in
     let prog = stack_remove_compile (stack_to_lab_config_jump stack_conf) offset
                  (is_gen_gc (data_to_word_config_gc_kind data_conf))
                  max_heap sp InitGlobals_location prog in
     let ps = APPEND ps [(implode "after stack_remove",Stack prog names)] in
     let prog = stack_names_compile (stack_to_lab_config_reg_names stack_conf) prog in
     let ps = APPEND ps [(implode "after stack_names",Stack prog names)] in
     let p = MAP prog_to_section prog in
     let ps = APPEND ps [(implode "after stack_to_lab",backend_passes_Lab p names)] in
     from_lab_all ps asm_conf c names p bm`;;

let from_stack_thm = prove
 (`SND (from_stack_all ps (asm_conf:(A)asm_config) c names p bm) =
   from_stack asm_conf c names p bm`,
  REWRITE_TAC[from_stack_all_def; from_stack_def; stack_to_lab_compile_def] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[GEN_ALL from_lab_thm]);;

let from_word_all_def = cake_def
  `from_word_all (ps:(mlstring#(A)any_prog)list) (asm_conf:(A)asm_config)
       (c:backend_config) names p =
     let (bm,c',fs,p) =
       word_to_stack_compile asm_conf
         (stack_to_lab_config_perf_calls (backend_config_stack_conf c)) p in
     let ps = APPEND ps [(implode "after word_to_stack",Stack p names)] in
     let c = backend_config_word_conf_fupd (K c') c in
     from_stack_all ps asm_conf c names p bm`;;

let from_word_thm = prove
 (`SND (from_word_all ps (asm_conf:(A)asm_config) c names p) =
   from_word asm_conf c names p`,
  REWRITE_TAC[from_word_all_def; from_word_def] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[GEN_ALL from_stack_thm]);;

let from_word_0_all_def = cake_def
  `from_word_0_all (ps:(mlstring#(A)any_prog)list) (asm_conf:(A)asm_config)
       (c:backend_config) names p =
     let word_conf = backend_config_word_to_word_conf c in
     let (p,ps) = word_internal_all asm_conf ps names p in
     let reg_count = asm_config_reg_count asm_conf -
                     (5 + LENGTH (asm_config_avoid_regs asm_conf)) in
     let alg = word_to_word_config_reg_alg word_conf in
     let (n_oracles,col) =
       next_n_oracle (LENGTH p) (word_to_word_config_col_oracle word_conf) in
     let p = MAP (\((name_num,arg_count,prog),col_opt).
                    (name_num,arg_count,
                     remove_must_terminate
                       (word_alloc name_num asm_conf alg reg_count prog col_opt)))
               (ZIP p n_oracles) in
     let ps = APPEND ps [(implode "after word_alloc (and remove_must_terminate)",
                          backend_passes_Word p names)] in
     let c = backend_config_word_to_word_conf_fupd
               (\c. word_to_word_config_col_oracle_fupd (K col) c) c in
     from_word_all ps asm_conf c names p`;;

let from_word_0_thm = prove
 (`SND (from_word_0_all ps (asm_conf:(A)asm_config) c names p) =
   from_word_0 asm_conf c names p`,
  REWRITE_TAC[from_word_0_all_def; from_word_0_def; word_to_word_compile_def;
              word_internal_all_def] THEN
  BACKDEFAUX_LETS_RW_TAC[LENGTH_MAP] THEN
  REWRITE_TAC[GEN_ALL from_word_thm] THEN AP_TERM_TAC THEN
  REWRITE_TAC[MAP_MAP_o] THEN MATCH_MP_TAC BACKDEFAUX_MAP_ZIP_MAP THEN CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP BACKDEFAUX_LENGTH_next_n_oracle); ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[full_compile_single_def; word_to_word_compile_single_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[]);;

let from_data_all_def = cake_def
  `from_data_all (ps:(mlstring#(A)any_prog)list) (asm_conf:(A)asm_config)
       (c:backend_config) names p =
     let data_conf = backend_config_data_conf c in
     let word_conf = backend_config_word_to_word_conf c in
     let data_conf =
       data_to_word_config_has_fp_ops_fupd (K (1 < asm_config_fp_reg_count asm_conf))
         (data_to_word_config_has_fp_tern_fupd
            (K (asm_config_ISA asm_conf = ARMv7 /\ 2 < asm_config_fp_reg_count asm_conf))
            data_conf) in
     let p = APPEND (data_to_word_stubs (:A) data_conf)
                    (MAP (data_to_word_compile_part data_conf) p) in
     let ps = APPEND ps [(implode "after data_to_word",backend_passes_Word p names)] in
     from_word_0_all ps asm_conf c names p`;;

(* HOL4: from_data_thm *)

let backend_passes_from_data_thm = prove
 (`SND (from_data_all ps (asm_conf:(A)asm_config) c names p) =
   from_data asm_conf c names p`,
  REWRITE_TAC[from_data_all_def; from_data_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[GEN_ALL from_word_0_thm] THEN
  REWRITE_TAC[from_word_0_def; data_to_word_compile_def] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[]);;

let to_data_all_from_data_all_correctness = prove
 (CASE_TERM
  `to_target_all (asm_conf:(A)asm_config) c p =
     let (ps,c',p,ns) = to_data_all c p in
     from_data_all ps asm_conf c' ns p`,
  REWRITE_TAC[to_target_all_def; to_lab_all_def; to_stack_all_def; to_word_all_def] THEN
  REWRITE_TAC[from_data_all_def; from_word_0_all_def; from_word_all_def;
              from_stack_all_def; from_lab_all_def] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[]);;

let compile_eq_to_target_all = prove
 (`backend_compile (asm_conf:(A)asm_config) c p = SND (to_target_all asm_conf c p)`,
  REWRITE_TAC[compile_eq_to_target; to_target_thm]);;

let number_of_passes = prove
 (`LENGTH (FST (to_target_all (asm_conf:(A)asm_config) c p)) = 41`,
  REWRITE_TAC[to_target_all_def; to_lab_all_def; to_stack_all_def; word_internal_all_def;
              to_word_all_def; to_data_all_def; to_bvi_all_def; to_bvl_all_def;
              to_clos_all_def; to_flat_all_def] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let any_prog_pp_def = cake_def
  `any_prog_pp (p:(A)any_prog) =
     match p with
       Source p -> source_to_strs p
     | Flat p -> flat_to_strs p
     | backend_passes_Clos decs funs -> clos_to_strs (decs,funs)
     | Bvl p names -> bvl_to_strs names p
     | Bvi p names -> bvi_to_strs names p
     | backend_passes_Data p names -> data_to_strs names p
     | backend_passes_Word p names -> word_to_strs names p
     | Stack p names -> stack_to_strs names p
     | backend_passes_Lab p names -> lab_to_strs names p`;;

let pp_with_title_def = cake_def
  `pp_with_title (pp:B->(mlstring)app_list) (title,p) acc =
     misc_Append (misc_List [implode "# "; title; implode "\n\n"])
       (misc_Append (pp p) acc)`;;

let compile_tap_def = cake_def
  `compile_tap (asm_conf:(A)asm_config) (c:backend_config) p =
     if tap_config_explore_flag (backend_config_tap_conf c) then
       let (ps,out) = to_target_all asm_conf c p in
       (out,ITLIST (pp_with_title any_prog_pp) ps Nil)
     else (backend_compile asm_conf c p,Nil)`;;

(* HOL4: compile_alt *)

let backend_passes_compile_alt = prove
 (`backend_compile (asm_conf:(A)asm_config) c p = FST (compile_tap asm_conf c p)`,
  REWRITE_TAC[compile_tap_def] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[compile_eq_to_target_all] THEN BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[]);;
