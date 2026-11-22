(* ========================================================================= *)
(* pan_to_wordProof: port of HOL4 pancake/proofs/pan_to_wordProofScript.sml  *)
(* (CakeML v3479).                                                           *)
(* Correctness proof for combined pan_to_word compilation.                   *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as notes/naming/names.tsv says; HOL4's local Type prog is         *)
(*   (A)panLang_prog written out.  The records of the semantics are          *)
(*   pan_state, crep_state, loop_state and wl_state (fields                  *)
(*   pan_state_locals, ...); HOL4 <| f1 := v1; ... |> is the REC constructor *)
(*   with the fields in order.                                               *)
(* - HOL4's MAP2 truncates the longer list, HOL Light's MAP2 takes the       *)
(*   length of the first list: map_map2_fst_lemma gets the hypothesis       *)
(*   LENGTH xs <= LENGTH ys (DEVIATION, see the theorem).                    *)
(* - Free variables of the HOL4 statements are quantified (the asm_config  *)
(*   c of the every_inst lemmas about crep_to_loop stays free, as in        *)
(*   HOL4); the unused quantified variables of HOL4's                       *)
(*   every_inst_ok_less_pan_to_crep_compile (e) and                         *)
(*   every_inst_ok_less_pan_structs_compile_top (ctxt) are dropped.          *)
(* - PTOPAUX_state_rel_imp_semantics is HOL4's state_rel_imp_semantics with *)
(*   the three theorems of pan_to_crepProof that its proof uses as          *)
(*   hypotheses; pan_to_wordProof_state_rel_imp_semantics follows from it.  *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/proofs/stack_removeProof.ml";;
needs "pancake/crep_inline.ml";;
needs "pancake/pan_to_word.ml";;
needs "pancake/semantics/panProps.ml";;
needs "pancake/semantics/crepProps.ml";;
needs "pancake/semantics/loopProps.ml";;
needs "pancake/proofs/pan_simpProof.ml";;
needs "pancake/proofs/pan_to_crepProof.ml";;
needs "pancake/proofs/crep_to_loopProof.ml";;
needs "pancake/proofs/loop_to_wordProof.ml";;
needs "pancake/proofs/pan_globalsProof.ml";;
needs "pancake/proofs/pan_structsProof.ml";;
needs "pancake/proofs/crep_inlineProof.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4: Type prog[local] = ``:'a panLang$prog`` (pan_to_wordProof_prog in    *)
(* names.tsv), written out as (A)panLang_prog                                 *)

let crep_state_def = cake_def
  `crep_state (s:(A,B)pan_state) (pan_code:((A)decl)list) mem =
     crep_state_REC FEMPTY FEMPTY (alist_to_fmap (pan_to_crep_compile_prog pan_code)) mem
       (pan_state_memaddrs s) (pan_state_sh_memaddrs s) (pan_state_clock s)
       (pan_state_be s) (pan_state_ffi s) (pan_state_base_addr s) (pan_state_top_addr s)`;;

let wloc_wlab_def = cake_def
  `wloc_wlab (wl_Word (w:A word)) = Word w`;;

let wloc_wlab_wlab_wloc = prove
 (`!w:(A)word_lab. wloc_wlab (wlab_wloc w) = w`,
  GEN_TAC THEN QCASES_ON "w:(A)word_lab" THEN REWRITE_TAC[wlab_wloc_def; wloc_wlab_def]);;

let _ = cake_add_simps [wloc_wlab_wlab_wloc];;

let no_labels_def = cake_def
  `no_labels (mem:A word->(A)word_loc) dom <=> (!a. a IN dom ==> ?w. mem a = wl_Word w)`;;

let loop_state_def = cake_def
  `loop_state (s:(A,B)crep_state) c (crep_code:(mlstring#num list#(A)crep_prog)list) ck
              mem =
     loop_state_REC LN FEMPTY mem (crep_state_memaddrs s) (crep_state_sh_memaddrs s) ck
       (fromAList (crep_to_loop_compile_prog c crep_code)) (crep_state_be s)
       (crep_state_ffi s) (crep_state_base_addr s) (crep_state_top_addr s)`;;

let distinct_params_def = cake_def
  `distinct_params (prog:(A#(B)list#C)list) <=>
     ALL (\(name,params,body). ALL_DISTINCT params) prog`;;


let lookup_first_name_compile_prog_main = prove
 (`!(crep_code:(mlstring#num list#(A)crep_prog)list) c.
     FLOOKUP (crep_to_loop_make_funcs crep_code) (implode "main") = SOME (first_name,0) ==>
     ?prog. lookup first_name (fromAList (crep_to_loop_compile_prog c crep_code)) =
            SOME ([],prog)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (ISPECL [`crep_code:(mlstring#num list#(A)crep_prog)list`; `implode "main"`; `0`]
                 initial_prog_make_funcs_el) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  STRUCT_CASES_TAC (ISPEC `crep_code:(mlstring#num list#(A)crep_prog)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; LT_REFL; EL; HD] THEN
  PAIR_CASES_ON `h:mlstring#num list#(A)crep_prog` THEN
  REWRITE_TAC[PAIR_EQ; o_THM] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[crep_to_loop_compile_prog_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP[lookup_fromAList; LENGTH; GENLIST_CONS; MAP2_DEF; ALOOKUP_def; HD; TL; o_THM;
       CONJUNCT1 list_of_seq;
       ADD_CLAUSES]);;

let loop_state_simps = prove
 (`!(s:(A,B)crep_state) c (crep_code:(mlstring#num list#(A)crep_prog)list) ck
    (mem:A word->(A)word_loc).
     loop_state_memory (loop_state s c crep_code ck mem) = mem /\
     loop_state_mdomain (loop_state s c crep_code ck mem) = crep_state_memaddrs s /\
     loop_state_sh_mdomain (loop_state s c crep_code ck mem) = crep_state_sh_memaddrs s /\
     loop_state_clock (loop_state s c crep_code ck mem) = ck /\
     (loop_state_be (loop_state s c crep_code ck mem) <=> crep_state_be s) /\
     loop_state_ffi (loop_state s c crep_code ck mem) = crep_state_ffi s /\
     loop_state_base_addr (loop_state s c crep_code ck mem) = crep_state_base_addr s /\
     loop_state_top_addr (loop_state s c crep_code ck mem) = crep_state_top_addr s /\
     loop_state_globals (loop_state s c crep_code ck mem) = FEMPTY /\
     loop_state_locals (loop_state s c crep_code ck mem) = LN /\
     loop_state_code (loop_state s c crep_code ck mem) =
       fromAList (crep_to_loop_compile_prog c crep_code)`,
  REWRITE_TAC[loop_state_def] THEN SIMP[]);;

let _ = cake_add_simps [loop_state_simps];;

let pan_to_wordProof_first_compile_prog_all_distinct = prove
 (`!c (prog:((A)decl)list).
     ALL_DISTINCT (MAP FST (functions prog)) ==>
     ALL_DISTINCT (MAP FST (pan_to_word_compile_prog c prog))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[pan_to_word_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MATCH_MP_TAC first_compile_all_distinct THEN
  REWRITE_TAC[crep_to_loopProof_first_compile_prog_all_distinct]);;

(* exceptions are kept by pan_simp *)
let PTOPAUX_exceptions_pan_simp = prove
 (`!prog:((A)decl)list. exceptions (pan_simp_compile_prog prog) = exceptions prog`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[pan_simp_compile_prog_def; MAP; exceptions_def] THEN
  QCASES_ON "h:(A)decl" THEN
  FIRST_X_ASSUM (MP_TAC o REWRITE_RULE[pan_simp_compile_prog_def]) THEN
  SIMP[exceptions_def]);;

let get_eids_pan_simp_compile_eq = prove
 (`!prog:((A)decl)list.
     FDOM (get_eids_from_decls prog) = FDOM (get_eids_from_decls (pan_simp_compile_prog prog))`,
  REWRITE_TAC[get_eids_from_decls_def; PTOPAUX_exceptions_pan_simp]);;

(* HOL4's MAP2 truncates the longer list; HOL Light's MAP2 xs ys has the   *)
(* length of xs (HD and TL of ys): the hypothesis LENGTH xs <= LENGTH ys   *)
(* (DEVIATION; the theorem is unused)                                       *)
let map_map2_fst_lemma = prove
 (`!(xs:A list) (ys:B list).
     LENGTH xs <= LENGTH ys ==>
     MAP FST (MAP2 (\x y. x,y) xs ys) = TAKE (MIN (LENGTH xs) (LENGTH ys)) xs`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ARITH_RULE `a <= b ==> MIN a b = a`] THEN
  REWRITE_TAC[TAKE_LENGTH_ID] THEN
  SPEC_TAC(`ys:B list`,`ys:B list`) THEN SPEC_TAC(`xs:A list`,`xs:A list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP2_DEF; MAP]);;

let exp_ids_nested_seq = prove
 (`!ps:((A)panLang_prog)list. exp_ids (nested_seq ps) = FLAT (MAP exp_ids ps)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[nested_seq_def; exp_ids_def; MAP; FLAT]);;

let exp_ids_compile_globals = prove
 (`!ctxt (p:(A)panLang_prog). exp_ids (pan_globals_compile ctxt p) = exp_ids p`,
  REC_IND_TAC pan_globals_compile_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[pan_globals_compile_def] THEN
  RW[ELIM_UNCURRY; exp_ids_def] THEN
  REPEAT (TOP_CASE_TAC THEN GVS[exp_ids_def]));;

let exp_ids_fperm = prove
 (`!f g (p:(A)panLang_prog). exp_ids (fperm f g p) = exp_ids p`,
  REC_IND_TAC fperm_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[fperm_def] THEN
  RW[ELIM_UNCURRY; exp_ids_def] THEN
  REPEAT (TOP_CASE_TAC THEN GVS[exp_ids_def]));;

let compile_decs_exp_ids = prove
 (`!ctxt (pan_code:((A)decl)list).
     MAP (exp_ids o FST o SND o SND)
         (functions (FST (SND (pan_globals_compile_decs ctxt pan_code)))) =
     MAP (exp_ids o FST o SND o SND) (functions pan_code)`,
  REC_IND_TAC pan_globals_compile_decs_ind THEN
  RW[pan_globals_compile_decs_def; ELIM_UNCURRY; exp_ids_def; functions_def;
     exp_ids_compile_globals] THEN
  REPEAT (PAIRARG_TAC THEN FS[]) THEN FS[functions_def; MAP; o_THM; exp_ids_compile_globals]);;

let fperm_exp_ids = prove
 (`!f g (pan_code:((A)decl)list).
     MAP (exp_ids o FST o SND o SND) (functions (fperm_decs f g pan_code)) =
     MAP (exp_ids o FST o SND o SND) (functions pan_code)`,
  REC_IND_TAC fperm_decs_ind THEN
  RW[fperm_decs_def; ELIM_UNCURRY; exp_ids_def; functions_def; exp_ids_fperm] THEN
  FS[MAP; o_THM; exp_ids_fperm]);;

let compile_decs_no_exp_ids_main = prove
 (`!ctxt (prog:((A)decl)list).
     ALL (\x. exp_ids x = []) (FST (pan_globals_compile_decs ctxt prog))`,
  REC_IND_TAC pan_globals_compile_decs_ind THEN
  RW[pan_globals_compile_decs_def; ELIM_UNCURRY; exp_ids_def] THEN
  REPEAT (PAIRARG_TAC THEN FS[]) THEN FS[ALL; exp_ids_def]);;

let functions_resort_decls = prove
 (`!xs:((A)decl)list. functions (resort_decls xs) = functions xs`,
  GEN_TAC THEN
  REWRITE_TAC[resort_decls_def; functions_eq_FILTER; FILTER_APPEND; FILTER_FILTER] THEN
  SUBGOAL_THEN
   `FILTER (\x:(A)decl. is_function x /\ is_name x) xs = [] /\
    FILTER (\x:(A)decl. is_function x /\ is_exn_decl x) xs = [] /\
    FILTER (\x:(A)decl. is_function x /\ is_decl x) xs = [] /\
    FILTER (\x:(A)decl. is_function x /\ is_function x) xs = FILTER is_function xs`
   (fun th -> REWRITE_TAC[th; APPEND]) THEN
  REWRITE_TAC[FILTER_EQ_NIL; EVERY_MEM; ETA_AX] THEN
  MESON_TAC[not_is_function]);;

(* the domain of the exception map *)
let PTOPAUX_FDOM_get_eids = prove
 (`!decls:((A)decl)list.
     FDOM (get_eids_from_decls decls) = set_of_list (MAP FST (exceptions decls))`,
  GEN_TAC THEN REWRITE_TAC[get_eids_from_decls_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FDOM_alist_to_fmap] THEN
  AP_TERM_TAC THEN
  SPEC_TAC(`list_of_seq (\x. (word x):A word)
              (LENGTH (MAP FST (exceptions (decls:((A)decl)list))))`,
           `ys:(A word)list`) THEN
  SPEC_TAC(`MAP FST (exceptions (decls:((A)decl)list))`,`xs:mlstring list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP2_DEF; MAP]);;

let PTOPAUX_exceptions_fperm_decs = prove
 (`!f g decs:((A)decl)list. exceptions (fperm_decs f g decs) = exceptions decs`,
  REC_IND_TAC fperm_decs_ind THEN RW[fperm_decs_def; exceptions_def]);;

let PTOPAUX_exceptions_functions = prove
 (`!fs:((A)decl)list. ALL is_function fs ==> exceptions fs = []`,
  REC_IND_TAC (cake_ind "exceptions") THEN RW[exceptions_def; ALL; is_function_def]);;

let FDOM_get_eids_pan_globals_compile_eq = prove
 (`!pan_code main args body rshape.
     ALOOKUP (functions (pan_code:((A)decl)list)) main = SOME (args,body,rshape) ==>
     FDOM (get_eids_from_decls (pan_globals_compile_top pan_code main)) =
     FDOM (get_eids_from_decls pan_code)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PTOPAUX_FDOM_get_eids] THEN
  ASM_REWRITE_TAC[pan_globals_compile_top_def] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  PAIR_CASES_ON `pan_globals_compile_decs
     (pan_globals_context_REC FEMPTY (word 0)
        (word_mul bytes_in_word
          (word (SUM (MAP size_of_shape
             (dec_shapes (fperm_decs main (new_main_name pan_code)
                                      (resort_decls pan_code))))))))
     (fperm_decs main (new_main_name pan_code) (resort_decls (pan_code:((A)decl)list)))` THEN
  CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP compile_decs_EVERY_is_function) THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP compile_decs_exns_are_exns) THEN
  ASM_SIMP_TAC[exceptions_append; exceptions_def; PTOPAUX_exceptions_functions;
               APPEND_NIL; exceptions_FILTER_is_function; PTOPAUX_exceptions_fperm_decs] THEN
  REWRITE_TAC[resort_decls_def; exceptions_append; exceptions_FILTER_is_function; APPEND;
              APPEND_NIL]);;

let globals_allocatable_def = cake_def
  `globals_allocatable (s:(A,FFI)pan_state) (pan_code:((A)decl)list) <=>
     let dec_shs = dec_shapes pan_code in
     let struct_ctxt = decs_stcnames [] pan_code in
     let sz = SUM (MAP (size_of_sh_with_ctxt (THE struct_ctxt)) dec_shs) in
     ~(struct_ctxt = NONE) /\
     DISJOINT (pan_state_memaddrs s) (addresses (pan_state_top_addr s) sz) /\
     ~(word_add (pan_state_top_addr s) (word_mul (bytes_in_word:A word) (word sz)) IN
       pan_state_memaddrs s) /\
     sz * val (bytes_in_word:A word) < dimword (:A)`;;

let dec_shapes_compile_prog = prove
 (`!pan_code:((A)decl)list. dec_shapes (pan_simp_compile_prog pan_code) = dec_shapes pan_code`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[pan_simp_compile_prog_def; MAP; dec_shapes_def] THEN
  QCASES_ON "h:(A)decl" THEN
  FIRST_X_ASSUM (MP_TAC o REWRITE_RULE[pan_simp_compile_prog_def]) THEN
  SIMP[dec_shapes_def]);;

let function_names_compile_prog = prove
 (`!pan_code:((A)decl)list.
     MAP FST (functions (pan_simp_compile_prog pan_code)) = MAP FST (functions pan_code)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[pan_simp_compile_prog_def; MAP; functions_def] THEN
  QCASES_ON "h:(A)decl" THEN
  FIRST_X_ASSUM (MP_TAC o REWRITE_RULE[pan_simp_compile_prog_def]) THEN
  SIMP[functions_def]);;

(* HOL4 [local] *)
let function_names_structs_compile_decs = prove
 (`!ctxt pan_code:((A)decl)list.
     MAP FST (functions (FST (pan_structs_compile_decs ctxt pan_code))) =
     MAP FST (functions pan_code)`,
  REC_IND_TAC pan_structs_compile_decs_ind THEN REPEAT STRIP_TAC THEN
  SIMP[pan_structs_compile_decs_def; functions_def] THEN
  REPEAT (PAIRARG_TAC THEN FS[functions_def]));;

(* HOL4 [local] *)
let exp_ids_structs_compile = prove
 (`!ctxt (prog:(A)panLang_prog). exp_ids (pan_structs_compile ctxt prog) = exp_ids prog`,
  REC_IND_TAC pan_structs_compile_ind THEN
  SIMP[pan_structs_compile_def; exp_ids_def] THEN RW[] THEN
  EVERY_CASE_TAC THEN SIMP[pan_structs_compile_def; exp_ids_def]);;

(* the names of the exceptions are kept by pan_structs *)
let PTOPAUX_exceptions_structs_compile_decs = prove
 (`!ctxt prog:((A)decl)list.
     MAP FST (exceptions (FST (pan_structs_compile_decs ctxt prog))) =
     MAP FST (exceptions prog)`,
  REC_IND_TAC pan_structs_compile_decs_ind THEN REPEAT STRIP_TAC THEN
  SIMP[pan_structs_compile_decs_def; exceptions_def] THEN
  REPEAT (PAIRARG_TAC THEN FS[exceptions_def]));;

(* HOL4 [local] (the first of two theorems of this name) *)
let FDOM_get_eids_structs_compile_decs_eq = prove
 (`!ctxt prog:((A)decl)list.
     FDOM (get_eids_from_decls prog) =
     FDOM (get_eids_from_decls (FST (pan_structs_compile_decs ctxt prog)))`,
  REWRITE_TAC[PTOPAUX_FDOM_get_eids; PTOPAUX_exceptions_structs_compile_decs]);;

(* HOL4 [local] *)
let FDOM_get_eids_structs_compile_eq = prove
 (`!prog:((A)decl)list.
     FDOM (get_eids_from_decls (pan_structs_compile_top prog)) =
     FDOM (get_eids_from_decls prog)`,
  GEN_TAC THEN REWRITE_TAC[pan_structs_compile_top_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM FDOM_get_eids_structs_compile_decs_eq]);;

(* HOL4 [local] (the second theorem of this name, about size_of_eids) *)
let FDOM_get_eids_structs_compile_decs_eq = prove
 (`!ctxt prog:((A)decl)list.
     size_of_eids prog = size_of_eids (FST (pan_structs_compile_decs ctxt prog))`,
  REWRITE_TAC[size_of_eids_def] THEN
  REC_IND_TAC pan_structs_compile_decs_ind THEN REPEAT STRIP_TAC THEN
  SIMP[pan_structs_compile_decs_def; is_exn_decl_def; FILTER] THEN
  REPEAT (PAIRARG_TAC THEN FS[is_exn_decl_def; FILTER; LENGTH]));;

(* HOL4 [local] *)
let size_of_eids_structs_compile_eq = prove
 (`!prog:((A)decl)list. size_of_eids (pan_structs_compile_top prog) = size_of_eids prog`,
  GEN_TAC THEN REWRITE_TAC[pan_structs_compile_top_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM FDOM_get_eids_structs_compile_decs_eq]);;

let function_names_structs_compile_top = prove
 (`!pan_code:((A)decl)list.
     MAP FST (functions (pan_structs_compile_top pan_code)) = MAP FST (functions pan_code)`,
  GEN_TAC THEN REWRITE_TAC[pan_structs_compile_top_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[function_names_structs_compile_decs]);;

let no_names_compile_prog = prove
 (`!pan_code:((A)decl)list.
     ALL (\d. is_function d \/ is_decl d \/ is_exn_decl d) pan_code ==>
     ALL (\d. is_function d \/ is_decl d \/ is_exn_decl d) (pan_simp_compile_prog pan_code)`,
  REWRITE_TAC[pan_simp_compile_prog_def; ALL_MAP] THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_ALL THEN GEN_TAC THEN QCASES_ON "x:(A)decl" THEN
  SIMP[is_function_def; is_decl_def; is_exn_decl_def; o_THM]);;

let pan_to_wordProof_semantics_decls_has_main' = prove
 (`!(s:(A,FFI)pan_state) start (code:((A)decl)list).
     pan_state_code s = FEMPTY /\
     ALL_DISTINCT (MAP FST (functions code)) /\
     ~(semantics_decls s start code = Fail) ==>
     ?body rshape. ALOOKUP (functions code) start = SOME ([],body,rshape)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP pan_semantics_decls_has_main') THEN
  ASM_SIMP_TAC[flookup_fupdate_list; alookup_distinct_reverse; FLOOKUP_EMPTY] THEN
  QCASES_ON "ALOOKUP (functions (code:((A)decl)list)) start" THEN SIMP[]);;

(* HOL4 [local] *)
let semantics_decls_has_main'' = prove
 (`!(s:(A,FFI)pan_state) start (code:((A)decl)list) v.
     semantics_decls s start code = v /\
     pan_state_code s = FEMPTY /\
     ALL_DISTINCT (MAP FST (functions code)) /\
     ~(v = Fail) ==>
     ?body rshape. ALOOKUP (functions code) start = SOME ([],body,rshape)`,
  MESON_TAC[pan_to_wordProof_semantics_decls_has_main']);;

let compile_decs_fun_names = prove
 (`!ctxt code:((A)decl)list.
     MAP FST (functions (FST (SND (pan_globals_compile_decs ctxt code)))) =
     MAP FST (functions code)`,
  REC_IND_TAC pan_globals_compile_decs_ind THEN REPEAT STRIP_TAC THEN
  SIMP[pan_globals_compile_decs_def; functions_def] THEN
  REPEAT (PAIRARG_TAC THEN FS[functions_def]));;

(* the exception declarations of fperm_decs and of resort_decls *)
let PTOPAUX_FILTER_exn_fperm_decs = prove
 (`!f g decs:((A)decl)list.
     FILTER is_exn_decl (fperm_decs f g decs) = FILTER is_exn_decl decs`,
  REC_IND_TAC fperm_decs_ind THEN RW[fperm_decs_def; FILTER; is_exn_decl_def]);;

let PTOPAUX_FILTER_exn_resort_decls = prove
 (`!decs:((A)decl)list.
     FILTER is_exn_decl (resort_decls decs) = FILTER is_exn_decl decs`,
  GEN_TAC THEN REWRITE_TAC[resort_decls_def; FILTER_APPEND; FILTER_FILTER] THEN
  SUBGOAL_THEN
   `FILTER (\x:(A)decl. is_exn_decl x /\ is_name x) decs = [] /\
    FILTER (\x:(A)decl. is_exn_decl x /\ is_exn_decl x) decs = FILTER is_exn_decl decs /\
    FILTER (\x:(A)decl. is_exn_decl x /\ is_decl x) decs = [] /\
    FILTER (\x:(A)decl. is_exn_decl x /\ is_function x) decs = []`
   (fun th -> REWRITE_TAC[th; APPEND; APPEND_NIL]) THEN
  REWRITE_TAC[FILTER_EQ_NIL; EVERY_MEM; ETA_AX] THEN REPEAT CONJ_TAC THEN
  GEN_TAC THEN QCASES_ON "e:(A)decl" THEN
  REWRITE_TAC[is_exn_decl_def; is_name_def; is_decl_def; is_function_def]);;

let PTOPAUX_FILTER_exn_functions = prove
 (`!fs:((A)decl)list. ALL is_function fs ==> FILTER is_exn_decl fs = []`,
  REWRITE_TAC[FILTER_EQ_NIL] THEN GEN_TAC THEN MATCH_MP_TAC MONO_ALL THEN
  GEN_TAC THEN QCASES_ON "x:(A)decl" THEN
  REWRITE_TAC[is_exn_decl_def; is_function_def]);;

let size_of_eids_compile_top = prove
 (`!pan_code main args body rshape.
     ALOOKUP (functions (pan_code:((A)decl)list)) main = SOME (args,body,rshape) ==>
     size_of_eids (pan_globals_compile_top pan_code main) = size_of_eids pan_code`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[size_of_eids_def] THEN
  ASM_REWRITE_TAC[pan_globals_compile_top_def] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  PAIR_CASES_ON `pan_globals_compile_decs
     (pan_globals_context_REC FEMPTY (word 0)
        (word_mul bytes_in_word
          (word (SUM (MAP size_of_shape
             (dec_shapes (fperm_decs main (new_main_name pan_code)
                                      (resort_decls pan_code))))))))
     (fperm_decs main (new_main_name pan_code) (resort_decls (pan_code:((A)decl)list)))` THEN
  CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP compile_decs_EVERY_is_function) THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP compile_decs_exns_are_exns) THEN
  ASM_SIMP_TAC[FILTER_APPEND; FILTER; is_exn_decl_def; PTOPAUX_FILTER_exn_functions;
               FILTER_IDEM; PTOPAUX_FILTER_exn_fperm_decs; PTOPAUX_FILTER_exn_resort_decls;
               APPEND_NIL]);;

(* TODO: move (HOL4) *)
let functions_FILTER_nil = prove
 (`!xs:((A)decl)list. functions (FILTER is_exn_decl xs) = []`,
  REC_IND_TAC (cake_ind "functions") THEN
  RW[functions_def; is_exn_decl_def; FILTER]);;

let FLOOKUP_make_funcs_main = prove
 (`!pan_code main body rshape.
     ALOOKUP (functions (pan_code:((A)decl)list)) main = SOME ([],body,rshape) ==>
     FLOOKUP (crep_to_loop_make_funcs
                (pan_to_crep_compile_prog (pan_globals_compile_top pan_code main))) main =
     SOME (first_name,0)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[pan_globals_compile_top_def] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  PAIR_CASES_ON `pan_globals_compile_decs
     (pan_globals_context_REC FEMPTY (word 0)
        (word_mul bytes_in_word
          (word (SUM (MAP size_of_shape
             (dec_shapes (fperm_decs main (new_main_name pan_code)
                                      (resort_decls pan_code))))))))
     (fperm_decs main (new_main_name pan_code) (resort_decls (pan_code:((A)decl)list)))` THEN
  CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP compile_decs_exns_are_exns) THEN
  ASM_REWRITE_TAC[pan_to_crep_compile_prog_def; compile_to_crep_def; compile_inl_top_def;
                  compile_inl_prog_def; crep_to_loop_make_funcs_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP[functions_append; functions_def; functions_FILTER_nil; APPEND; MAP; LENGTH;
       GENLIST_CONS; MAP2_DEF; crep_vars_def; size_of_shape_def; alist_to_fmap_thm;
       FLOOKUP_UPDATE; o_THM; ADD_CLAUSES]);;

let pan_to_wordProof_compile_shape_no_name = prove
 (`!(ctxt:(stcname#((B#shape)list))list) n sh.
     is_wf_shape ([]:(mlstring#struct_info)list) (compile_shape_n ctxt n sh)`,
  REC_IND_TAC compile_shape_n_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[compile_shape_n_def] THEN
  REWRITE_TAC[is_wf_shape_def; ALL_MAP; GSYM ALL_MEM; o_THM] THEN
  TRY (ASM_MESON_TAC[]) THEN
  TOP_CASE_TAC THEN REWRITE_TAC[is_wf_shape_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN PAIRARG_TAC THEN
  REWRITE_TAC[is_wf_shape_def; ALL_MAP; GSYM ALL_MEM; o_THM] THEN
  ASM_MESON_TAC[MEM_MAP]);;

let size_decs_stcnames_compile_decs_structs = prove
 (CASE_TERM
  `!(s:(A,FFI)pan_state) (pan_code:((A)decl)list) ctxt s' code' ctxt'.
     evaluate_decls s pan_code = SOME s' /\
     pan_structs_compile_decs ctxt pan_code = (code',ctxt') /\
     struct_infos_ok (pan_state_structs s) /\
     FEVERY (\p. match p with (nm,v) -> is_wf_shape_v (pan_state_structs s) v)
            (pan_state_globals s) /\
     pan_structs_context_structs ctxt =
       MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info))
           (pan_state_structs s) ==>
     MAP size_of_shape (dec_shapes code') =
     MAP (size_of_sh_with_ctxt (pan_state_structs s)) (dec_shapes pan_code)`,
  REC_IND_TAC evaluate_decls_ind THEN
  RW[evaluate_decls_def; pan_structs_compile_decs_def; dec_shapes_def] THEN
  FS[option_case_eq] THEN
  REPEAT (PAIRARG_TAC THEN FS[]) THEN
  GVS[dec_shapes_def] THEN
  TRY (ASM_MESON_TAC[]) THEN
  (* Decl *)
  SUBGOAL_THEN `is_wf_shape_v (pan_state_structs (s:(A,FFI)pan_state)) (a:(A)pan_v)`
    ASSUME_TAC THENL
   [MP_TAC (ISPECL [`pan_state_locals_fupd (K FEMPTY) (s:(A,FFI)pan_state)`;
                    `e:(A)panLang_exp`; `a:(A)pan_v`] eval_is_wf_shape_v) THEN
    SIMP[FEVERY_FEMPTY];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC size_of_shape_compile_pass_eq THEN
    ASM_MESON_TAC[is_wf_shape_of_v];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`pan_structs_context_globals_fupd
       (K (CONS (v,shape_of (a:(A)pan_v)) (pan_structs_context_globals ctxt))) ctxt`;
    `ctxt':pan_structs_context`] THEN
  SIMP[FEVERY_FUPDATE; fevery_to_drestrict] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[]);;

let semantics_size_decs_stcnames_compile_structs = prove
 (`!(s:(A,FFI)pan_state) nm (pan_code:((A)decl)list).
     ~(semantics_decls s nm pan_code = Fail) /\ pan_state_globals s = FEMPTY ==>
     MAP size_of_shape (dec_shapes (pan_structs_compile_top pan_code)) =
     MAP (size_of_sh_with_ctxt (THE (decs_stcnames [] pan_code))) (dec_shapes pan_code)`,
  RW[semantics_decls_def; pan_structs_compile_top_def] THEN
  EVERY_CASE_TAC THEN FS[] THEN
  MP_TAC (ISPECL [`[]:(stcname#struct_info)list`; `pan_code:((A)decl)list`;
                  `a:(stcname#struct_info)list`; `pan_structs_context_REC [] [] []`]
                 decs_stcnames_to_get_names) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MAP] THEN SIMP[]; DISCH_TAC] THEN
  MP_TAC (ISPECL [`[]:(stcname#struct_info)list`; `pan_code:((A)decl)list`;
                  `a:(stcname#struct_info)list`] decs_stcnames_infos_ok) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[struct_infos_ok_def; ALL; MAP; ALL_DISTINCT; LENGTH; LT];
    DISCH_TAC] THEN
  MP_TAC (ISPECL
   [`pan_state_structs_fupd (K (a:(stcname#struct_info)list)) (s:(A,FFI)pan_state)`;
    `pan_code:((A)decl)list`;
    `get_names (pan_structs_context_REC [] [] []) (pan_code:((A)decl)list)`;
    `a':(A,FFI)pan_state`;
    `FST (pan_structs_compile_decs
            (get_names (pan_structs_context_REC [] [] []) pan_code) (pan_code:((A)decl)list))`;
    `SND (pan_structs_compile_decs
            (get_names (pan_structs_context_REC [] [] []) pan_code) (pan_code:((A)decl)list))`]
   size_decs_stcnames_compile_decs_structs) THEN
  ASM_SIMP_TAC[FEVERY_FEMPTY] THEN SIMP[FEVERY_FEMPTY]);;

let semantics_decls_decl_structs = prove
 (`!(s:(A,FFI)pan_state) start (pan_code:((A)decl)list).
     ~(semantics_decls s start pan_code = Fail) ==>
     ?s_ctxt. decs_stcnames [] pan_code = SOME s_ctxt`,
  REPEAT GEN_TAC THEN REWRITE_TAC[semantics_decls_def] THEN
  QCASES_ON "decs_stcnames [] (pan_code:((A)decl)list)" THEN SIMP[]);;

(* HOL4 [local]: ALL_DISTINCT_MAP_INJ for MAP FST xs, with MAP_MAP_o and o_DEF *)
let ALL_DISTINCT_MAP_INJ_o = prove
 (`!(f:A->B) (xs:(A#E)list).
     (!x y. MEM x (MAP FST xs) /\ MEM y (MAP FST xs) /\ f x = f y ==> x = y) /\
     ALL_DISTINCT (MAP FST xs) ==> ALL_DISTINCT (MAP (\x. f (FST x)) xs)`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPECL [`MAP FST (xs:(A#E)list)`; `f:A->B`] ALL_DISTINCT_MAP_INJ) THEN
  REWRITE_TAC[MAP_MAP_o; o_DEF]);;

let functions_compile_decs_exns = prove
 (`!(ctxt:(A)pan_globals_context) (prog:((A)decl)list).
     functions (FST (SND (SND (pan_globals_compile_decs ctxt prog)))) = []`,
  REPEAT GEN_TAC THEN
  PAIR_CASES_ON `pan_globals_compile_decs (ctxt:(A)pan_globals_context) (prog:((A)decl)list)` THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP compile_decs_exns_are_exns) THEN
  ASM_REWRITE_TAC[FST; SND; functions_FILTER_nil]);;

(* HOL4 state_rel_imp_semantics, with the three theorems of pan_to_crepProof   *)
(* that its proof uses (state_rel_imp_semantics_decls,                        *)
(* first_compile_prog_all_distinct and compile_prog_distinct_params) as       *)
(* hypotheses (the steps of the proof: pan_simp, pan_structs, pan_globals,    *)
(* pan_to_crep, crep_to_loop, loop_to_word)                                   *)
let PTOPAUX_state_rel_imp_semantics = prove
 (`(!(s:(A,FFI)pan_state) (t:(A,FFI)crep_state) (pan_code:((A)decl)list) start.
      pan_to_crepProof_state_rel (pan_state_structs_fupd (K []) s) t /\
      ALL_DISTINCT (MAP FST (functions pan_code)) /\
      pan_state_code s = FEMPTY /\
      crep_state_code t = alist_to_fmap (pan_to_crep_compile_prog pan_code) /\
      pan_state_locals s = FEMPTY /\
      pan_state_eshapes s = FEMPTY /\
      ALL (localised_prog o FST o SND o SND) (functions pan_code) /\
      ALL (\x. is_function x \/ is_exn_decl x) pan_code /\
      size_of_eids pan_code < dimword (:A) /\
      ~(semantics_decls s start pan_code = Fail) ==>
      crep_semantics t start = semantics_decls s start pan_code) /\
   (!prog:((A)decl)list.
      ALL_DISTINCT (MAP FST (functions prog)) ==>
      ALL_DISTINCT (MAP FST (pan_to_crep_compile_prog prog))) /\
   (!prog:((A)decl)list.
      ALL (\(name,params,body). ALL_DISTINCT params) (pan_to_crep_compile_prog prog))
   ==>
   !(s:(A,FFI)pan_state) (t:(A,B,FFI)wl_state) start globals_size
    (pan_code:((A)decl)list) heap_len (c:architecture).
     (!addr'. addr' IN pan_state_memaddrs s ==>
              wl_state_memory t addr' = wlab_wloc (pan_state_memory s addr')) /\
     no_labels (wl_state_memory t) (wl_state_mdomain t) /\
     start = implode "main" /\
     globals_size = (let dec_shs = dec_shapes pan_code in
                     let struct_ctxt = decs_stcnames [] pan_code in
                     SUM (MAP (size_of_sh_with_ctxt (THE struct_ctxt)) dec_shs)) /\
     distinct_params (functions pan_code) /\
     wl_state_mdomain t =
       pan_state_memaddrs s UNION addresses (pan_state_top_addr s) globals_size /\
     wl_state_sh_mdomain t = pan_state_sh_memaddrs s /\
     (wl_state_be t <=> pan_state_be s) /\
     wl_state_ffi t = pan_state_ffi s /\
     ALOOKUP (fmap_to_alist (wl_state_store t)) CurrHeap =
       SOME (wl_Word (pan_state_base_addr s)) /\
     ALOOKUP (fmap_to_alist (wl_state_store t)) HeapLength = SOME (wl_Word heap_len) /\
     pan_state_top_addr s =
       word_sub (word_add (pan_state_base_addr s) (word_mul (word 2) heap_len))
                (word_mul bytes_in_word (word globals_size)) /\
     ALL_DISTINCT (MAP FST (functions pan_code)) /\
     byte_aligned (pan_state_top_addr s) /\
     globals_allocatable s pan_code /\
     pan_state_code s = FEMPTY /\
     wl_state_code t = fromAList (pan_to_word_compile_prog c pan_code) /\
     pan_state_globals s = FEMPTY /\
     pan_state_locals s = FEMPTY /\ size_of_eids pan_code < dimword (:A) /\
     pan_state_eshapes s = FEMPTY /\
     lookup 0 (wl_state_locals t) = SOME (wl_Loc 1 0) /\ good_dimindex (:A) /\
     ~(semantics_decls s start pan_code = Fail)
     ==> wl_semantics t first_name = semantics_decls s start pan_code`,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "p2c")
    (CONJUNCTS_THEN2 (LABEL_TAC "p2cd") (LABEL_TAC "p2cp"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    try lhs(concl th) = `start:mlstring` with Failure _ -> false)) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  (* the equations of globals_size and of the top address, oriented to fold *)
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    try lhs(concl th) = `globals_size:num` with Failure _ -> false)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    try lhs(concl th) = `pan_state_top_addr (s:(A,FFI)pan_state)` with Failure _ -> false)) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `s_ctxt:(stcname#struct_info)list` o
              MATCH_MP semantics_decls_decl_structs) THEN
  (* pan_simp *)
  SUBGOAL_THEN
   `semantics_decls s (implode "main") pan_code =
    semantics_decls (s:(A,FFI)pan_state) (implode "main") (pan_simp_compile_prog pan_code)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC pan_simpProof_state_rel_imp_semantics_decls THEN
    ASM_REWRITE_TAC[pan_simpProof_state_rel_def; FLOOKUP_EMPTY; option_DISTINCT] THEN
    REWRITE_TAC[pan_state_component_equality; pan_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (* pan_structs *)
  SUBGOAL_THEN `pan_state_eshapes_fupd (K FEMPTY) (s:(A,FFI)pan_state) = s` ASSUME_TAC THENL
   [REWRITE_TAC[pan_state_component_equality; pan_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `semantics_decls s (implode "main") (pan_simp_compile_prog pan_code) =
    semantics_decls (s:(A,FFI)pan_state) (implode "main")
      (pan_structs_compile_top (pan_simp_compile_prog pan_code))`
   ASSUME_TAC THENL
   [MP_TAC (INST [`pan_simp_compile_prog (pan_code:((A)decl)list)`,`code:((A)decl)list`;
                  `implode "main"`,`start:mlstring`]
                 pan_structsProof_compile_top_semantics_decls) THEN
    ASM_REWRITE_TAC[FMAP_MAP2_FEMPTY] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the size of the globals *)
  SUBGOAL_THEN
   `SUM (MAP size_of_shape (dec_shapes (pan_structs_compile_top
      (pan_simp_compile_prog (pan_code:((A)decl)list))))) = globals_size`
   ASSUME_TAC THENL
   [MP_TAC (ISPECL [`s:(A,FFI)pan_state`; `implode "main"`;
                    `pan_simp_compile_prog (pan_code:((A)decl)list)`]
                   semantics_size_decs_stcnames_compile_structs) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[decs_stcnames_compile_prog; dec_shapes_compile_prog] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN

  (* pan_globals *)
  SUBGOAL_THEN
   `semantics_decls s (implode "main")
      (pan_structs_compile_top (pan_simp_compile_prog pan_code)) =
    semantics_decls
      (pan_state_top_addr_fupd
         (K (word_add (pan_state_top_addr s) (word_mul bytes_in_word (word globals_size))))
         (pan_state_memaddrs_fupd
            (K (pan_state_memaddrs s UNION addresses (pan_state_top_addr s) globals_size))
            (pan_state_memory_fupd (K (wloc_wlab o wl_state_memory (t:(A,B,FFI)wl_state)))
               (pan_state_locals_fupd (K (pan_state_locals s)) (s:(A,FFI)pan_state)))))
      (implode "main")
      (pan_globals_compile_top (pan_structs_compile_top (pan_simp_compile_prog pan_code))
         (implode "main"))`
   ASSUME_TAC THENL
   [MP_TAC (INST
      [`pan_structs_compile_top (pan_simp_compile_prog (pan_code:((A)decl)list))`,
         `code:((A)decl)list`;
       `implode "main"`,`start:mlstring`;
       `wloc_wlab o wl_state_memory (t:(A,B,FFI)wl_state)`,`tmem:A word->(A)word_lab`;
       `pan_state_locals (s:(A,FFI)pan_state)`,`tlocals:(mlstring,(A)pan_v)fmap`;
       `word_mul bytes_in_word (word globals_size):A word`,`mgs:A word`;
       `addresses (pan_state_top_addr (s:(A,FFI)pan_state)) globals_size`,
         `free_addrs:A word->bool`;
       `pan_state_top_addr_fupd
         (K (word_add (pan_state_top_addr s) (word_mul bytes_in_word (word globals_size))))
         (pan_state_memaddrs_fupd
            (K (pan_state_memaddrs s UNION addresses (pan_state_top_addr s) globals_size))
            (pan_state_memory_fupd (K (wloc_wlab o wl_state_memory (t:(A,B,FFI)wl_state)))
               (pan_state_locals_fupd (K (pan_state_locals s)) (s:(A,FFI)pan_state))))`,
         `t:(A,FFI)pan_state`]
      pan_globalsProof_compile_top_semantics_decls) THEN
    REWRITE_TAC[function_names_structs_compile_top; function_names_compile_prog;
                compile_top_no_names; o_THM] THEN
    REWRITE_TAC[ASSUME `SUM (MAP size_of_shape (dec_shapes (pan_structs_compile_top
      (pan_simp_compile_prog (pan_code:((A)decl)list))))) = globals_size`] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC (ASSUME `globals_allocatable (s:(A,FFI)pan_state) pan_code`) THEN
    REWRITE_TAC[globals_allocatable_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[ASSUME `SUM (MAP (size_of_sh_with_ctxt (THE (decs_stcnames [] pan_code)))
      (dec_shapes (pan_code:((A)decl)list))) = globals_size`] THEN
    STRIP_TAC THEN
    REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
    TRY (ONCE_REWRITE_TAC[MULT_SYM] THEN FIRST_ASSUM ACCEPT_TAC) THEN
    TRY (REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[wloc_wlab_wlab_wloc] THEN
         NO_TAC) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN

  (* the main function of the program after pan_structs *)
  SUBGOAL_THEN
   `?body rshape. ALOOKUP (functions (pan_structs_compile_top
       (pan_simp_compile_prog (pan_code:((A)decl)list)))) (implode "main") =
       SOME ([],body,rshape)`
   STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC pan_to_wordProof_semantics_decls_has_main' THEN
    EXISTS_TAC `s:(A,FFI)pan_state` THEN
    REWRITE_TAC[function_names_structs_compile_top; function_names_compile_prog] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* pan_to_crep *)
  USE_THEN "p2c" (MP_TAC o SPECL
   [`pan_state_top_addr_fupd
       (K (word_add (pan_state_top_addr s) (word_mul bytes_in_word (word globals_size))))
       (pan_state_memaddrs_fupd
          (K (pan_state_memaddrs s UNION addresses (pan_state_top_addr s) globals_size))
          (pan_state_memory_fupd (K (wloc_wlab o wl_state_memory (t:(A,B,FFI)wl_state)))
             (pan_state_locals_fupd (K (pan_state_locals s)) (s:(A,FFI)pan_state))))`;
    `crep_state
       (pan_state_top_addr_fupd
         (K (word_add (pan_state_top_addr s) (word_mul bytes_in_word (word globals_size))))
         (pan_state_memaddrs_fupd
            (K (pan_state_memaddrs s UNION addresses (pan_state_top_addr s) globals_size))
            (pan_state_memory_fupd (K (wloc_wlab o wl_state_memory (t:(A,B,FFI)wl_state)))
               (pan_state_locals_fupd (K (pan_state_locals s)) (s:(A,FFI)pan_state)))))
       (pan_globals_compile_top (pan_structs_compile_top (pan_simp_compile_prog pan_code))
          (implode "main"))
       (wloc_wlab o wl_state_memory t)`;
    `pan_globals_compile_top (pan_structs_compile_top
       (pan_simp_compile_prog (pan_code:((A)decl)list))) (implode "main")`;
    `implode "main"`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[pan_to_crepProof_state_rel_def; crep_state_def; crep_state_INFO.ri_accessors;
                pan_state_INFO.ri_accfupds; K_THM; FMAP_MAP2_FEMPTY;
                compile_top_localised; compile_top_only_functions_or_exns] THEN
    REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
     [MATCH_MP_TAC ALL_DISTINCT_compile_top THEN
      REWRITE_TAC[function_names_structs_compile_top; function_names_compile_prog] THEN
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP size_of_eids_compile_top th]) THEN
      REWRITE_TAC[size_of_eids_structs_compile_eq; size_of_eids_compile_eq] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ASM_MESON_TAC[]];
    DISCH_TAC] THEN

  (* crep_to_loop *)
  SUBGOAL_THEN
   `~(crep_semantics
       (crep_state
         (pan_state_top_addr_fupd
           (K (word_add (pan_state_top_addr s) (word_mul bytes_in_word (word globals_size))))
           (pan_state_memaddrs_fupd
              (K (pan_state_memaddrs s UNION addresses (pan_state_top_addr s) globals_size))
              (pan_state_memory_fupd (K (wloc_wlab o wl_state_memory (t:(A,B,FFI)wl_state)))
                 (pan_state_locals_fupd (K (pan_state_locals s)) (s:(A,FFI)pan_state)))))
         (pan_globals_compile_top (pan_structs_compile_top (pan_simp_compile_prog pan_code))
            (implode "main"))
         (wloc_wlab o wl_state_memory t)) (implode "main") = Fail)`
   ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC (ISPECL
   [`crep_state
       (pan_state_top_addr_fupd
         (K (word_add (pan_state_top_addr s) (word_mul bytes_in_word (word globals_size))))
         (pan_state_memaddrs_fupd
            (K (pan_state_memaddrs s UNION addresses (pan_state_top_addr s) globals_size))
            (pan_state_memory_fupd (K (wloc_wlab o wl_state_memory (t:(A,B,FFI)wl_state)))
               (pan_state_locals_fupd (K (pan_state_locals s)) (s:(A,FFI)pan_state)))))
       (pan_globals_compile_top (pan_structs_compile_top (pan_simp_compile_prog pan_code))
          (implode "main"))
       (wloc_wlab o wl_state_memory t)`;
    `loop_state
      (crep_state
       (pan_state_top_addr_fupd
         (K (word_add (pan_state_top_addr s) (word_mul bytes_in_word (word globals_size))))
         (pan_state_memaddrs_fupd
            (K (pan_state_memaddrs s UNION addresses (pan_state_top_addr s) globals_size))
            (pan_state_memory_fupd (K (wloc_wlab o wl_state_memory (t:(A,B,FFI)wl_state)))
               (pan_state_locals_fupd (K (pan_state_locals s)) (s:(A,FFI)pan_state)))))
       (pan_globals_compile_top (pan_structs_compile_top (pan_simp_compile_prog pan_code))
          (implode "main"))
       (wloc_wlab o wl_state_memory t))
      (c:architecture)
      (pan_to_crep_compile_prog (pan_globals_compile_top
         (pan_structs_compile_top (pan_simp_compile_prog pan_code)) (implode "main")))
      (wl_state_clock t) (wl_state_memory t)`;
    `pan_to_crep_compile_prog (pan_globals_compile_top
       (pan_structs_compile_top (pan_simp_compile_prog (pan_code:((A)decl)list)))
       (implode "main"))`;
    `implode "main"`; `first_name`; `c:architecture`]
   crep_to_loopProof_state_rel_imp_semantics) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[loop_state_simps; crep_state_def; crep_state_INFO.ri_accessors;
                pan_state_INFO.ri_accfupds; K_THM; mem_rel_def;
                crep_to_loopProof_globals_rel_def; FLOOKUP_EMPTY; option_DISTINCT] THEN
    TRY (MATCH_MP_TAC FLOOKUP_make_funcs_main THEN ASM_MESON_TAC[]) THEN
    TRY (USE_THEN "p2cd" MATCH_MP_TAC THEN MATCH_MP_TAC ALL_DISTINCT_compile_top THEN
         REWRITE_TAC[function_names_structs_compile_top; function_names_compile_prog] THEN
         FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[o_THM] THEN X_GEN_TAC `ad:A word` THEN DISCH_TAC THEN
    UNDISCH_TAC `no_labels (wl_state_memory (t:(A,B,FFI)wl_state)) (wl_state_mdomain t)` THEN
    REWRITE_TAC[no_labels_def] THEN DISCH_THEN(MP_TAC o SPEC `ad:A word`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[wloc_wlab_def; wlab_wloc_def];
    DISCH_TAC] THEN

  (* loop_to_word *)
  SUBGOAL_THEN
   `FLOOKUP (crep_to_loop_make_funcs (pan_to_crep_compile_prog (pan_globals_compile_top
       (pan_structs_compile_top (pan_simp_compile_prog (pan_code:((A)decl)list)))
       (implode "main")))) (implode "main") = SOME (first_name,0)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC FLOOKUP_make_funcs_main THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(loop_semantics
      (loop_state
       (crep_state
        (pan_state_top_addr_fupd
          (K (word_add (pan_state_top_addr s) (word_mul bytes_in_word (word globals_size))))
          (pan_state_memaddrs_fupd
             (K (pan_state_memaddrs s UNION addresses (pan_state_top_addr s) globals_size))
             (pan_state_memory_fupd (K (wloc_wlab o wl_state_memory (t:(A,B,FFI)wl_state)))
                (pan_state_locals_fupd (K (pan_state_locals s)) (s:(A,FFI)pan_state)))))
        (pan_globals_compile_top (pan_structs_compile_top (pan_simp_compile_prog pan_code))
           (implode "main"))
        (wloc_wlab o wl_state_memory t))
       (c:architecture)
       (pan_to_crep_compile_prog (pan_globals_compile_top
          (pan_structs_compile_top (pan_simp_compile_prog pan_code)) (implode "main")))
       (wl_state_clock t) (wl_state_memory t)) first_name = Fail)`
   ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC (ISPECL
   [`loop_state
      (crep_state
       (pan_state_top_addr_fupd
         (K (word_add (pan_state_top_addr s) (word_mul bytes_in_word (word globals_size))))
         (pan_state_memaddrs_fupd
            (K (pan_state_memaddrs s UNION addresses (pan_state_top_addr s) globals_size))
            (pan_state_memory_fupd (K (wloc_wlab o wl_state_memory (t:(A,B,FFI)wl_state)))
               (pan_state_locals_fupd (K (pan_state_locals s)) (s:(A,FFI)pan_state)))))
       (pan_globals_compile_top (pan_structs_compile_top (pan_simp_compile_prog pan_code))
          (implode "main"))
       (wloc_wlab o wl_state_memory t))
      (c:architecture)
      (pan_to_crep_compile_prog (pan_globals_compile_top
         (pan_structs_compile_top (pan_simp_compile_prog pan_code)) (implode "main")))
      (wl_state_clock t) (wl_state_memory t)`;
    `t:(A,B,FFI)wl_state`; `first_name`]
   loop_to_wordProof_state_rel_imp_semantics) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
    TRY (REWRITE_TAC[loop_state_simps] THEN NO_TAC) THEN
    TRY (REWRITE_TAC[loop_state_simps] THEN
         MATCH_MP_TAC lookup_first_name_compile_prog_main THEN FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[loop_to_wordProof_state_rel_def; loop_state_simps; crep_state_def;
                crep_state_INFO.ri_accessors; pan_state_INFO.ri_accfupds; K_THM] THEN
    EXISTS_TAC `heap_len:A word` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SYM(ASSUME `word_sub (word_add (pan_state_base_addr (s:(A,FFI)pan_state))
                                (word_mul (word 2) heap_len))
                              (word_mul bytes_in_word (word globals_size)) =
                            pan_state_top_addr s`)] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[loop_to_wordProof_globals_rel_def; FLOOKUP_EMPTY; option_DISTINCT];
      REWRITE_TAC[loop_to_wordProof_code_rel_def; pan_to_word_compile_prog_def;
                  loop_to_word_compile_def] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC lookup_prog_some_lookup_compile_prog THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM o REWRITE_RULE[lookup_fromAList]) THEN
        MP_TAC (ISPECL
          [`pan_to_crep_compile_prog (pan_globals_compile_top
             (pan_structs_compile_top (pan_simp_compile_prog (pan_code:((A)decl)list)))
             (implode "main"))`; `c:architecture`]
          crep_to_loopProof_compile_prog_distinct_params) THEN
        ANTS_TAC THENL [USE_THEN "p2cp" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
        REWRITE_TAC[GSYM ALL_MEM] THEN
        DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
        CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]]];
    DISCH_TAC] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 529: PTOPAUX_state_rel_imp_semantics with the three theorems *)
(* of pan_to_crepProof that it takes as hypotheses                        *)
let pan_to_wordProof_state_rel_imp_semantics = prove
 (`!(s:(A,FFI)pan_state) (t:(A,B,FFI)wl_state) start globals_size
    (pan_code:((A)decl)list) heap_len (c:architecture).
     (!addr'. addr' IN pan_state_memaddrs s ==>
              wl_state_memory t addr' = wlab_wloc (pan_state_memory s addr')) /\
     no_labels (wl_state_memory t) (wl_state_mdomain t) /\
     start = implode "main" /\
     globals_size = (let dec_shs = dec_shapes pan_code in
                     let struct_ctxt = decs_stcnames [] pan_code in
                     SUM (MAP (size_of_sh_with_ctxt (THE struct_ctxt)) dec_shs)) /\
     distinct_params (functions pan_code) /\
     wl_state_mdomain t =
       pan_state_memaddrs s UNION addresses (pan_state_top_addr s) globals_size /\
     wl_state_sh_mdomain t = pan_state_sh_memaddrs s /\
     (wl_state_be t <=> pan_state_be s) /\
     wl_state_ffi t = pan_state_ffi s /\
     ALOOKUP (fmap_to_alist (wl_state_store t)) CurrHeap =
       SOME (wl_Word (pan_state_base_addr s)) /\
     ALOOKUP (fmap_to_alist (wl_state_store t)) HeapLength = SOME (wl_Word heap_len) /\
     pan_state_top_addr s =
       word_sub (word_add (pan_state_base_addr s) (word_mul (word 2) heap_len))
                (word_mul bytes_in_word (word globals_size)) /\
     ALL_DISTINCT (MAP FST (functions pan_code)) /\
     byte_aligned (pan_state_top_addr s) /\
     globals_allocatable s pan_code /\
     pan_state_code s = FEMPTY /\
     wl_state_code t = fromAList (pan_to_word_compile_prog c pan_code) /\
     pan_state_globals s = FEMPTY /\
     pan_state_locals s = FEMPTY /\ size_of_eids pan_code < dimword (:A) /\
     pan_state_eshapes s = FEMPTY /\
     lookup 0 (wl_state_locals t) = SOME (wl_Loc 1 0) /\ good_dimindex (:A) /\
     ~(semantics_decls s start pan_code = Fail)
     ==> wl_semantics t first_name = semantics_decls s start pan_code`,
  MATCH_ACCEPT_TAC (MATCH_MP PTOPAUX_state_rel_imp_semantics
    (CONJ pan_to_crepProof_state_rel_imp_semantics_decls
      (CONJ pan_to_crepProof_first_compile_prog_all_distinct
            pan_to_crepProof_compile_prog_distinct_params))));;

let pan_to_word_compile_prog_no_install_code = prove
 (`!c (prog:((A)decl)list) prog'.
     pan_to_word_compile_prog c prog = prog' ==> no_install_code (fromAList prog')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pan_to_word_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[loop_compile_no_install_code]);;

let pan_to_word_compile_prog_no_alloc_code = prove
 (`!c (prog:((A)decl)list) prog'.
     pan_to_word_compile_prog c prog = prog' ==> no_alloc_code (fromAList prog')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pan_to_word_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[loop_compile_no_alloc_code]);;

let pan_to_word_compile_prog_no_mt_code = prove
 (`!c (prog:((A)decl)list) prog'.
     pan_to_word_compile_prog c prog = prog' ==> no_mt_code (fromAList prog')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pan_to_word_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[loop_compile_no_mt_code]);;

(* pan_to_word good_handlers (HOL4) *)

let pan_to_word_good_handlers = prove
 (`!c (prog:((A)decl)list) prog'.
     pan_to_word_compile_prog c prog = prog' ==>
     ALL (\(n,m,pp). good_handlers n pp) prog'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pan_to_word_compile_prog_def; loop_to_word_compile_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN MATCH_ACCEPT_TAC loop_to_word_good_handlers);;

(* lab_pres (HOL4) *)

let pan_to_word_compile_lab_pres = prove
 (`!c (prog:((A)decl)list) prog'.
     pan_to_word_compile_prog c prog = prog' ==>
     ALL (\(n,m,p).
            let labs = wordConvs_extract_labels p in
            ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) labs /\
            ALL_DISTINCT labs) prog'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pan_to_word_compile_prog_def; loop_to_word_compile_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MATCH_ACCEPT_TAC (CONV_RULE (TOP_DEPTH_CONV let_CONV) loop_to_word_compile_prog_lab_pres));;

(* first_name offset : lab_min (HOL4) *)

let pan_to_word_compile_prog_lab_min = prove
 (`!c (pprog:((A)decl)list) wprog.
     pan_to_word_compile_prog c pprog = wprog ==> ALL (\prog. 60 <= FST prog) wprog`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pan_to_word_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN DISCH_TAC THEN
  FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] loop_to_word_compile_lab_min)) THEN
  MATCH_MP_TAC (GEN_ALL crep_to_loop_compile_prog_lab_min) THEN MESON_TAC[]);;

(* inst_ok_less (HOL4) *)

let every_inst_ok_loop_call = prove
 (`!(c:(A)asm_config) l (prog:(B)loop_prog).
     every_prog (loop_inst_ok c) prog ==>
     every_prog (loop_inst_ok c) (FST (loop_call_comp l prog))`,
  GEN_TAC THEN REC_IND_TAC loop_call_comp_ind THEN
  RW[every_prog_def; loop_call_comp_def; loop_inst_ok_def] THEN
  REPEAT (PAIRARG_TAC THEN GVS[]) THEN
  RW[every_prog_def; loop_call_comp_def; loop_inst_ok_def] THEN
  EVERY_CASE_TAC THEN
  RW[every_prog_def; loop_call_comp_def; loop_inst_ok_def]);;

(* the clauses of loop_live_shrink without the one of fixedpoint *)
let PTOPAUX_shrink_rws = end_itlist CONJ (butlast (CONJUNCTS loop_live_shrink_def));;

(* HOL4: the first by-subgoal of every_inst_ok_loop_live *)
let PTOPAUX_every_inst_ok_shrink = prove
 (`!(c:(A)asm_config).
     (!lt (prog:(B)loop_prog) l.
        every_prog (loop_inst_ok c) prog ==>
        every_prog (loop_inst_ok c) (FST (loop_live_shrink lt prog l))) /\
     (!lt live_in l1 l2 (body:(B)loop_prog).
        every_prog (loop_inst_ok c) body ==>
        OPTION_ALL (every_prog (loop_inst_ok c) o FST) (fixedpoint lt live_in l1 l2 body))`,
  GEN_TAC THEN
  MP_TAC (ISPECL
   [`\lt (prog:(B)loop_prog) l.
       every_prog (loop_inst_ok (c:(A)asm_config)) prog ==>
       every_prog (loop_inst_ok c) (FST (loop_live_shrink lt prog l))`;
    `\lt live_in l1 l2 (body:(B)loop_prog).
       every_prog (loop_inst_ok (c:(A)asm_config)) body ==>
       OPTION_ALL (every_prog (loop_inst_ok c) o FST) (fixedpoint lt live_in l1 l2 body)`]
   loop_live_shrink_ind) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[every_prog_def; loop_inst_ok_def]) THEN
  TRY (GEN_REWRITE_TAC RAND_CONV [PLOOPAUX_fixedpoint_eq]) THEN
  REWRITE_TAC[PTOPAUX_shrink_rws] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT PAIRARG_TAC THEN EVERY_CASE_TAC THEN REPEAT PAIRARG_TAC THEN
  ASM_REWRITE_TAC[FST; every_prog_def; loop_inst_ok_def; OPTION_ALL_def; o_THM;
                  case_def "option"; case_def "prod"] THEN
  ASM_MESON_TAC[FST; OPTION_ALL_def; o_THM]);;

(* HOL4: the second by-subgoal of every_inst_ok_loop_live *)
let PTOPAUX_every_inst_ok_mark_all = prove
 (`!(c:(A)asm_config) (prog:(B)loop_prog).
     every_prog (loop_inst_ok c) prog ==>
     every_prog (loop_inst_ok c) (FST (mark_all prog))`,
  GEN_TAC THEN REC_IND_TAC mark_all_ind THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[every_prog_def; loop_inst_ok_def]) THEN
  REWRITE_TAC[mark_all_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT PAIRARG_TAC THEN EVERY_CASE_TAC THEN REPEAT PAIRARG_TAC THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[FST; every_prog_def; loop_inst_ok_def; case_def "option"; case_def "prod"] THEN
  ASM_MESON_TAC[FST]);;

let every_inst_ok_loop_live = prove
 (`!(c:(A)asm_config) (prog:(B)loop_prog).
     every_prog (loop_inst_ok c) prog ==>
     every_prog (loop_inst_ok c) (loop_live_comp prog)`,
  REWRITE_TAC[loop_live_comp_def] THEN
  MESON_TAC[PTOPAUX_every_inst_ok_shrink; PTOPAUX_every_inst_ok_mark_all]);;

let every_inst_ok_less_optimise = prove
 (`!(c:(A)asm_config) (prog:(B)loop_prog).
     every_prog (loop_inst_ok c) prog ==>
     every_prog (loop_inst_ok c) (optimise prog)`,
  REWRITE_TAC[optimise_def; o_THM] THEN
  MESON_TAC[every_inst_ok_loop_call; every_inst_ok_loop_live]);;

(* the clauses of crep_to_loop_compile_exp (without the one of compile_exps) *)
let PTOPAUX_c2l_exp_rws =
  end_itlist CONJ (butlast (CONJUNCTS crep_to_loop_compile_exp_def));;

(* compile_exps gives one loop expression for each expression *)
let PTOPAUX_c2l_exps_length = prove
 (`!(es:((A)crep_exp)list) ctxt tmp l p les tmp' l'.
     crep_to_loop_compile_exps ctxt tmp l es = (p,les,tmp',l') ==> LENGTH les = LENGTH es`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[compile_exps_alt] THENL
   [REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[LENGTH];
    REPEAT GEN_TAC THEN REPEAT (PAIRARG_TAC THEN ASM_REWRITE_TAC[]) THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    RVEQ_TAC THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN ASM_MESON_TAC[]]);;

let every_inst_ok_less_crep_to_loop_compile_exp = prove
 (`(!ctxt n ns (e:(A)crep_exp).
      crep_to_loop_context_target ctxt = asm_config_ISA (c:(B)asm_config) /\
      crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2) e
      ==> ALL (every_prog (loop_inst_ok c)) (FST (crep_to_loop_compile_exp ctxt n ns e))) /\
   (!ctxt n ns (es:((A)crep_exp)list).
      crep_to_loop_context_target ctxt = asm_config_ISA c /\
      ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2)) es
      ==> ALL (every_prog (loop_inst_ok c)) (FST (crep_to_loop_compile_exps ctxt n ns es)))`,
  MP_TAC (ISPECL
   [`\ctxt n ns (e:(A)crep_exp).
      crep_to_loop_context_target ctxt = asm_config_ISA (c:(B)asm_config) /\
      crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2) e
      ==> ALL (every_prog (loop_inst_ok c)) (FST (crep_to_loop_compile_exp ctxt n ns e))`;
    `\ctxt n ns (es:((A)crep_exp)list).
      crep_to_loop_context_target ctxt = asm_config_ISA (c:(B)asm_config) /\
      ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2)) es
      ==> ALL (every_prog (loop_inst_ok c)) (FST (crep_to_loop_compile_exps ctxt n ns es))`]
   crep_to_loop_compile_exp_ind) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY (STRUCT_CASES_TAC (ISPEC `cps:((A)crep_exp)list` list_CASES)) THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[crep_every_exp_def; ALL]) THEN
  REWRITE_TAC[PTOPAUX_c2l_exp_rws; compile_exps_alt] THEN
  REPEAT (PAIRARG_TAC THEN GVS[]) THEN
  REWRITE_TAC[ALL; ALL_APPEND; prog_if_def; every_prog_def; loop_inst_ok_def] THEN
  ASM_REWRITE_TAC[] THEN
  (* Crepop *)
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PTOPAUX_c2l_exps_length) THEN
  (CONJ_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM; MEM_MAPi] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[every_prog_def; loop_inst_ok_def];
    QPAT_X_ASSUM "compile_crepop _ _ _ _ _ _ = _" MP_TAC THEN QCASES_ON "cop" THEN
    REWRITE_TAC[compile_crepop_def] THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN SIMP[ALL; every_prog_def; loop_inst_ok_def] THEN
    TRY ARITH_TAC THEN REPEAT DISCH_TAC THEN
    UNDISCH_TAC `LENGTH (les:((A)loop_exp)list) = LENGTH (es:((A)crep_exp)list)` THEN
    ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC]));;

let every_prog_loop_inst_ok_nested_seq = prove
 (`!(c:(B)asm_config) (ps:((A)loop_prog)list).
     (every_prog (loop_inst_ok c) (loop_nested_seq ps) <=>
      ALL (every_prog (loop_inst_ok c)) ps)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[every_prog_def; loop_nested_seq_def; loop_inst_ok_def; ALL]);;

(* every loop_Assign is fine *)
let PTOPAUX_every_prog_MAP2_Assign = prove
 (`!(c:(B)asm_config) (ns:num list) (es:((A)loop_exp)list).
     ALL (every_prog (loop_inst_ok c)) (MAP2 loop_Assign ns es)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP2_DEF; ALL; every_prog_def; loop_inst_ok_def]);;

(* every_inst_ok_less_crep_to_loop_compile_exp for a compile_exp(s) result *)
let PTOPAUX_c2l_exp_ok = prove
 (`(!ctxt n ns (e:(A)crep_exp) p le tmp l'.
      crep_to_loop_compile_exp ctxt n ns e = (p,le,tmp,l') /\
      crep_to_loop_context_target ctxt = asm_config_ISA (c:(B)asm_config) /\
      crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2) e
      ==> ALL (every_prog (loop_inst_ok c)) p) /\
   (!ctxt n ns (es:((A)crep_exp)list) p les tmp l'.
      crep_to_loop_compile_exps ctxt n ns es = (p,les,tmp,l') /\
      crep_to_loop_context_target ctxt = asm_config_ISA (c:(B)asm_config) /\
      ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2)) es
      ==> ALL (every_prog (loop_inst_ok c)) p)`,
  MESON_TAC[every_inst_ok_less_crep_to_loop_compile_exp; FST]);;

let every_inst_ok_less_crep_to_loop_compile = prove
 (`!ctxt ns (body:(A)crep_prog).
     crep_to_loop_context_target ctxt = asm_config_ISA (c:(B)asm_config) /\
     ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2)) (crep_exps_of body)
     ==> every_prog (loop_inst_ok c) (crep_to_loop_compile ctxt ns body)`,
  REC_IND_TAC crep_to_loop_compile_ind THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[crep_exps_of_def; ALL; ALL_APPEND]) THEN
  REWRITE_TAC[crep_to_loop_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT (PAIRARG_TAC THEN GVS[]) THEN
  IMP_RES_TAC PTOPAUX_c2l_exp_ok THEN
  REPEAT (TOP_CASE_TAC THEN
          ASM_REWRITE_TAC[every_prog_def; loop_inst_ok_def; every_prog_loop_inst_ok_nested_seq;
                          ALL; ALL_APPEND; PTOPAUX_every_prog_MAP2_Assign]) THEN
  ASM_REWRITE_TAC[every_prog_def; loop_inst_ok_def; every_prog_loop_inst_ok_nested_seq;
                  ALL; ALL_APPEND; PTOPAUX_every_prog_MAP2_Assign] THEN
  TRY (ASM_MESON_TAC[]) THEN
  (* Call *)
  QCASES_ON "call_type" THEN GVS[crep_exps_of_def] THEN
  EVERY_CASE_TAC THEN GVS[crep_exps_of_def; ALL_APPEND; every_prog_def; loop_inst_ok_def]);;

let every_inst_ok_less_comp_func = prove
 (`!(prog:(mlstring#(num list)#(A)crep_prog)list) params (body:(A)crep_prog).
     ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2)) (crep_exps_of body)
     ==> every_prog (loop_inst_ok (c:(B)asm_config))
           (crep_to_loop_comp_func (asm_config_ISA c) (crep_to_loop_make_funcs prog) params body)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[crep_to_loop_comp_func_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MATCH_MP_TAC every_inst_ok_less_crep_to_loop_compile THEN
  ASM_REWRITE_TAC[crep_to_loop_mk_ctxt_def; crep_to_loop_context_INFO.ri_accessors]);;

let every_inst_ok_arith_simp_exp = prove
 (`!exp:(A)crep_exp.
     crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2) exp ==>
     crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2) (simp_exp exp)`,
  REC_IND_TAC simp_exp_ind THEN
  SIMP[simp_exp_def; crep_every_exp_def] THEN
  RW[mul_const_def] THEN EVERY_CASE_TAC THEN FS[] THEN
  GVS[MAP_EQ_CONS; LIST_LENGTH_1] THEN FS[crep_every_exp_def] THEN SIMP[ALL_MAP] THEN
  FS[GSYM ALL_MEM]);;

let every_inst_ok_arith_simp_prog = prove
 (`!prog:(A)crep_prog.
     ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2))
         (crep_exps_of prog) ==>
     ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2))
         (crep_exps_of (simp_prog prog))`,
  REC_IND_TAC simp_prog_ind THEN
  SIMP[simp_prog_def; crep_exps_of_def] THEN
  SIMP[every_inst_ok_arith_simp_exp] THEN RW[] THEN
  EVERY_CASE_TAC THEN FS[] THEN
  FS[crep_exps_of_def; every_inst_ok_arith_simp_exp] THEN
  FS[ALL_MAP] THEN FS[GSYM ALL_MEM; every_inst_ok_arith_simp_exp; ALL_APPEND]);;

let every_inst_ok_nested_decs = prove
 (`!ns es (p:(A)crep_prog).
     LENGTH ns = LENGTH es ==>
     (ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2))
          (crep_exps_of (nested_decs ns es p)) <=>
      ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2)) es /\
      ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2))
          (crep_exps_of p))`,
  REC_IND_TAC nested_decs_ind THEN
  RW[nested_decs_def; crep_exps_of_def; ALL; LENGTH; SUC_INJ] THEN
  REWRITE_TAC[CONJ_ASSOC]);;

let every_inst_ok_less_pan_to_crep_comp_field = prove
 (`!index shapes (es:((A)crep_exp)list) es' sh.
     ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2)) es /\
     comp_field index shapes es = (es',sh) ==>
     ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2)) es'`,
  REC_IND_TAC (cake_ind "comp_field") THEN
  RW[comp_field_def; crep_every_exp_def; ALL; EVERY_TAKE] THEN
  RES_TAC THEN GVS[EVERY_DROP; EVERY_TAKE]);;

let every_inst_ok_less_pan_to_crep_load_shape = prove
 (`!(w:A word) n (e:(A)crep_exp).
     crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2) e ==>
     ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2))
         (load_shape w n e)`,
  REC_IND_TAC (cake_ind "load_shape") THEN
  RW[load_shape_def; crep_every_exp_def; ALL]);;

let every_inst_ok_less_pan_to_crep_cexp_heads = prove
 (`!(ces:(((A)crep_exp)list)list) es.
     ALL (ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2))) ces /\
     cexp_heads ces = SOME es ==>
     ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2)) es`,
  LIST_INDUCT_TAC THEN RW[cexp_heads_def; ALL] THEN
  EVERY_CASE_TAC THEN GVS[ALL]);;

(* the expressions of compile_exp: FST form *)
let PTOPAUX_p2c_exp_ok = prove
 (`!(ctxt:(B)pan_to_crep_context) (e:(A)panLang_exp).
     pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2) e ==>
     ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2))
         (FST (pan_to_crep_compile_exp ctxt e))`,
  REC_IND_TAC pan_to_crep_compile_exp_ind THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pan_every_exp_def]) THEN
  ONCE_REWRITE_TAC[pan_to_crep_compile_exp_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT (PAIRARG_TAC THEN GVS[]) THEN
  EVERY_CASE_TAC THEN GVS[] THEN
  SIMP[ALL; crep_every_exp_def; ALL_MAP; o_DEF] THENL
   [(* RStruct *)
    REWRITE_TAC[EVERY_FLAT; ALL_MAP; o_THM; GSYM ALL_MEM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN ASM_MESON_TAC[];
    (* RField *)
    MATCH_MP_TAC every_inst_ok_less_pan_to_crep_comp_field THEN
    MAP_EVERY EXISTS_TAC [`index:num`; `a:shape list`; `cexp:((A)crep_exp)list`;
      `SND (comp_field index (a:shape list) (cexp:((A)crep_exp)list))`] THEN
    ASM_REWRITE_TAC[PAIR];
    (* Load *)
    MATCH_MP_TAC every_inst_ok_less_pan_to_crep_load_shape THEN ASM_REWRITE_TAC[];
    (* Op *)
    MATCH_MP_TAC every_inst_ok_less_pan_to_crep_cexp_heads THEN
    EXISTS_TAC `MAP FST (MAP (pan_to_crep_compile_exp (ctxt:(B)pan_to_crep_context))
                          (es:((A)panLang_exp)list))` THEN
    ASM_REWRITE_TAC[ALL_MAP; o_THM; GSYM ALL_MEM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN ASM_MESON_TAC[];
    (* Panop *)
    CONJ_TAC THENL
     [UNDISCH_TAC `cexp_heads (MAP FST (MAP (pan_to_crep_compile_exp
                     (ctxt:(B)pan_to_crep_context)) (es:((A)panLang_exp)list))) =
                   SOME (a:((A)crep_exp)list)` THEN
      REWRITE_TAC[cexp_heads_eq; cexp_heads_simp_def] THEN COND_CASES_TAC THEN
      REWRITE_TAC[option_INJ; option_DISTINCT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[LENGTH_MAP];
      MATCH_MP_TAC every_inst_ok_less_pan_to_crep_cexp_heads THEN
      EXISTS_TAC `MAP FST (MAP (pan_to_crep_compile_exp (ctxt:(B)pan_to_crep_context))
                            (es:((A)panLang_exp)list))` THEN
      ASM_REWRITE_TAC[ALL_MAP; o_THM; GSYM ALL_MEM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN ASM_MESON_TAC[]]]);;

let every_inst_ok_less_pan_to_crep_compile_exp = prove
 (`!(ctxt:(B)pan_to_crep_context) (e:(A)panLang_exp) es sh.
     pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2) e /\
     pan_to_crep_compile_exp ctxt e = (es,sh) ==>
     ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2)) es`,
  MESON_TAC[PTOPAUX_p2c_exp_ok; FST]);;

let exps_of_nested_seq = prove
 (`!es:((A)crep_prog)list. crep_exps_of (crep_nested_seq es) = FLAT (MAP crep_exps_of es)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[crep_nested_seq_def; crep_exps_of_def; MAP; FLAT]);;

let pan_exps_of_nested_seq = prove
 (`!es:((A)panLang_prog)list. pan_exps_of (nested_seq es) = FLAT (MAP pan_exps_of es)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[nested_seq_def; pan_exps_of_def; MAP; FLAT]);;

let every_inst_ok_less_stores = prove
 (`!(e:(A)crep_exp) es (a:A word).
     (ALL (\x. ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2))
                   (crep_exps_of x))
          (stores e es a) <=>
      (~(es = []) ==> crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2) e) /\
      ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2)) es)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  RW[stores_def; crep_exps_of_def; crep_every_exp_def; ALL] THEN
  ASM_MESON_TAC[]);;

let every_inst_ok_less_store_globals = prove
 (`!(w:5 word) (es:((A)crep_exp)list).
     (ALL (\x. ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2))
                   (crep_exps_of x))
          (store_globals w es) <=>
      ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2)) es)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  RW[store_globals_def; crep_exps_of_def; crep_every_exp_def; ALL]);;

let load_globals_alt = prove
 (`!(ad:5 word) n.
     load_globals ad n =
     list_of_seq (\n. LoadGlob (word_add ad (word n))) n:((A)crep_exp)list`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[load_globals_def; GENLIST_CONS; CONJUNCT1 list_of_seq; o_DEF] THEN
  GEN_TAC THEN REWRITE_TAC[CONS_11] THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[ADD1; GSYM WORD_ADD] THEN CONV_TAC WORD_RULE]);;

(* helpers for every_inst_ok_less_pan_to_crep_compile *)
let PTOPAUX_exps_of_MAP2_Assign = prove
 (`!(ns:num list) (es:((A)crep_exp)list).
     LENGTH ns = LENGTH es ==> FLAT (MAP crep_exps_of (MAP2 crep_Assign ns es)) = es`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; NOT_SUC; MAP2_DEF; MAP; FLAT; crep_exps_of_def; HD; TL; SUC_INJ;
               APPEND]);;

let PTOPAUX_load_globals_ok = prove
 (`!n (ad:5 word).
     ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2))
         (load_globals ad n:((A)crep_exp)list)`,
  INDUCT_TAC THEN SIMP[load_globals_def; ALL; crep_every_exp_def]);;

let PTOPAUX_p2c_exps_ok = prove
 (`!(ctxt:(B)pan_to_crep_context) (es:((A)panLang_exp)list).
     ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2)) es ==>
     ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2))
         (FLAT (MAP FST (MAP (pan_to_crep_compile_exp ctxt) es)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EVERY_FLAT; ALL_MAP; o_DEF] THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[PTOPAUX_p2c_exp_ok]);;

(* the same after EVERY_FLAT, ALL_MAP and o_DEF *)
let PTOPAUX_p2c_exps_ok' = REWRITE_RULE[EVERY_FLAT; ALL_MAP; o_DEF] PTOPAUX_p2c_exps_ok;;

let PTOPAUX_exp_hdl_ok = prove
 (`!(fm:(B,C#num list)fmap) v.
     ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2))
         (crep_exps_of (exp_hdl fm v:(A)crep_prog))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[exp_hdl_def] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[crep_exps_of_def; ALL] THEN
  PAIRARG_TAC THEN
  SIMP[exps_of_nested_seq; PTOPAUX_exps_of_MAP2_Assign; length_load_globals_eq_read_size;
       PTOPAUX_load_globals_ok]);;

let every_inst_ok_less_pan_to_crep_compile = prove
 (`!(ctxt:(A)pan_to_crep_context) (body:(A)panLang_prog).
     ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2)) (pan_exps_of body) ==>
     ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2))
         (crep_exps_of (pan_to_crep_compile ctxt body))`,
  REC_IND_TAC pan_to_crep_compile_ind THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pan_exps_of_def; ALL; ALL_APPEND]) THEN
  ONCE_REWRITE_TAC[pan_to_crep_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT (PAIRARG_TAC THEN GVS[]) THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
          GVS[crep_exps_of_def; ALL; ALL_APPEND]) THEN
  IMP_RES_TAC every_inst_ok_less_pan_to_crep_compile_exp THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; pan_exps_of_def; ALL_APPEND]) THEN
  SIMP[PTOPAUX_p2c_exps_ok'; PTOPAUX_exp_hdl_ok; crep_exps_of_def; ALL; ALL_APPEND;
       crep_every_exp_def; every_inst_ok_nested_decs;
       LENGTH_LIST_OF_SEQ; LENGTH_REPLICATE; LENGTH; exps_of_nested_seq;
       PTOPAUX_exps_of_MAP2_Assign; LENGTH_MAP; PTOPAUX_load_globals_ok; EVERY_REPLICATE;
       every_inst_ok_less_stores; every_inst_ok_less_store_globals; PTOPAUX_p2c_exps_ok;
       EVERY_FLAT; ALL_MAP; o_DEF] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN ASM_MESON_TAC[]);;

let good_panops_def = cake_def
  `(good_panops (Function (fi:(A)fun_decl)) <=>
      ALL (pan_every_exp (\x:(A)panLang_exp. !op es. x = Panop op es ==> LENGTH es = 2))
          (pan_exps_of (fun_decl_body fi))) /\
   (good_panops (Decl sh v exp) <=>
      pan_every_exp (\x:(A)panLang_exp. !op es. x = Panop op es ==> LENGTH es = 2) exp) /\
   (good_panops (_:(A)decl) <=> T)`;;

(* the bodies of the functions of a program with good_panops *)
let PTOPAUX_good_panops_functions = prove
 (`!code:((A)decl)list.
     ALL good_panops code ==>
     ALL (\(name,params,body,rshape).
            ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2))
                (pan_exps_of body))
         (functions code)`,
  REC_IND_TAC (cake_ind "functions") THEN
  RW[functions_def; good_panops_def; ALL] THEN FS[]);;

let every_inst_ok_less_pan_to_crep_compile_to_crep = prove
 (`!pan_code:((A)decl)list.
     ALL good_panops pan_code ==>
     ALL (\(name,params,body).
            ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2))
                (crep_exps_of body))
         (compile_to_crep pan_code)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PTOPAUX_good_panops_functions) THEN
  REWRITE_TAC[compile_to_crep_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ALL_MAP] THEN MATCH_MP_TAC MONO_ALL THEN
  REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[pan_to_crep_comp_func_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MATCH_MP_TAC every_inst_ok_less_pan_to_crep_compile THEN ASM_REWRITE_TAC[]);;

let every_inst_w_inline = prove
 (`!pan_code:((A)decl)list.
     ALL (\(name,params,body).
            ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2))
                (crep_exps_of body))
         (compile_to_crep pan_code) ==>
     ALL (\(name,params,body).
            ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2))
                (crep_exps_of body))
         (pan_to_crep_compile_prog pan_code)`,
  GEN_TAC THEN REWRITE_TAC[pan_to_crep_compile_prog_def; compile_inl_top_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_TAC THEN
  MATCH_MP_TAC every_inst_crep_inline THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBMAP_FLOOKUP_EQN; CONJUNCT1 ALOOKUP_EQ_FLOOKUP; ALOOKUP_FILTER] THEN
  MESON_TAC[option_DISTINCT]);;

let every_inst_ok_less_pan_to_crep_compile_prog = prove
 (`!pan_code:((A)decl)list.
     ALL good_panops pan_code ==>
     ALL (\(name,params,body).
            ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2))
                (crep_exps_of body))
         (pan_to_crep_compile_prog pan_code)`,
  MESON_TAC[every_inst_ok_less_pan_to_crep_compile_to_crep; every_inst_w_inline]);;

let every_inst_ok_less_ret_to_tail = prove
 (`!p:(A)panLang_prog.
     (ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2))
          (pan_exps_of (ret_to_tail p)) <=>
      ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2)) (pan_exps_of p))`,
  REC_IND_TAC ret_to_tail_ind THEN
  RW[pan_exps_of_def; ret_to_tail_def; seq_call_ret_def; pan_every_exp_def; ALL; ALL_APPEND] THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
          GVS[pan_exps_of_def; ret_to_tail_def; seq_call_ret_def; pan_every_exp_def; ALL;
              ALL_APPEND]) THEN
  ASM_MESON_TAC[]);;

let every_inst_ok_less_seq_assoc = prove
 (`!p (q:(A)panLang_prog).
     (ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2))
          (pan_exps_of (seq_assoc p q)) <=>
      ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2))
          (APPEND (pan_exps_of p) (pan_exps_of q)))`,
  REC_IND_TAC seq_assoc_ind THEN
  RW[pan_exps_of_def; seq_assoc_def; pan_every_exp_def; ALL; ALL_APPEND] THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
          GVS[pan_exps_of_def; seq_assoc_def; pan_every_exp_def; ALL; ALL_APPEND]) THEN
  ASM_MESON_TAC[]);;

let every_inst_ok_less_pan_simp_compile = prove
 (`!body:(A)panLang_prog.
     ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2)) (pan_exps_of body) ==>
     ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2))
         (pan_exps_of (pan_simp_compile body))`,
  REWRITE_TAC[pan_simp_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[every_inst_ok_less_ret_to_tail; every_inst_ok_less_seq_assoc; pan_exps_of_def;
              APPEND]);;

let every_inst_ok_less_crep_to_loop_compile_prog = prove
 (`!(crep_code:(mlstring#(num list)#(A)crep_prog)list).
     ALL (\(name,params,body).
            ALL (crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2))
                (crep_exps_of body)) crep_code ==>
     ALL (\(name,params,body). every_prog (loop_inst_ok (c:(B)asm_config)) body)
         (crep_to_loop_compile_prog (asm_config_ISA c) crep_code)`,
  GEN_TAC THEN REWRITE_TAC[crep_to_loop_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP_TAC[MAP2_ZIP; LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[ALL_MAP; GSYM ALL_MEM; MEM_ZIP; LENGTH_LIST_OF_SEQ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[o_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `EL n (crep_code:(mlstring#(num list)#(A)crep_prog)list)`) THEN
  ASM_SIMP_TAC[MEM_EL] THEN
  PAIR_CASES_ON `EL n (crep_code:(mlstring#(num list)#(A)crep_prog)list)` THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[UNCURRY_DEF] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_TAC THEN
  MATCH_MP_TAC every_inst_ok_less_optimise THEN
  MATCH_MP_TAC every_inst_ok_less_comp_func THEN
  MATCH_MP_TAC every_inst_ok_arith_simp_prog THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM]);;

let every_inst_ok_less_pan_simp_compile_prog = prove
 (`!pan_code:((A)decl)list.
     ALL good_panops pan_code ==> ALL good_panops (pan_simp_compile_prog pan_code)`,
  REWRITE_TAC[pan_simp_compile_prog_def; ALL_MAP] THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_ALL THEN GEN_TAC THEN QCASES_ON "x:(A)decl" THEN
  SIMP[good_panops_def; o_THM; every_inst_ok_less_pan_simp_compile]);;

let every_inst_ok_less_pan_structs_compile_exp = prove
 (`(!ctxt (e:(A)panLang_exp).
      pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2) e ==>
      pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2)
        (pan_structs_compile_exp ctxt e)) /\
   (!ctxt (es:((A)panLang_exp)list).
      ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2)) es ==>
      ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2))
        (pan_structs_compile_exps ctxt es) /\
      LENGTH (pan_structs_compile_exps ctxt es) = LENGTH es) /\
   (!ctxt (flds:(fldname#(A)panLang_exp)list).
      ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2)) (MAP SND flds) ==>
      ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2))
        (MAP SND (compile_fields ctxt flds)))`,
  MP_TAC (ISPECL
   [`\ctxt (e:(A)panLang_exp).
      pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2) e ==>
      pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2)
        (pan_structs_compile_exp ctxt e)`;
    `\ctxt (es:((A)panLang_exp)list).
      ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2)) es ==>
      ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2))
        (pan_structs_compile_exps ctxt es) /\
      LENGTH (pan_structs_compile_exps ctxt es) = LENGTH es`;
    `\ctxt (flds:(fldname#(A)panLang_exp)list).
      ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2)) (MAP SND flds) ==>
      ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2))
        (MAP SND (compile_fields ctxt flds))`]
   pan_structs_compile_exp_ind) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pan_every_exp_def; ALL; MAP]) THEN
  ONCE_REWRITE_TAC[pan_structs_compile_exp_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP[pan_every_exp_def; ALL; MAP; LENGTH] THEN
  (* NStruct *)
  TOP_CASE_TAC THEN REWRITE_TAC[ALL; EVERY_FLAT; ALL_MAP; o_DEF] THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `p:fldname#shape` THEN DISCH_TAC THEN
  PAIR_CASES_ON `p:fldname#shape` THEN CASE_REWRITE_TAC[] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[ALL; MEM] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  ASM_MESON_TAC[MEM_MAP; SND]);;

let every_inst_ok_less_pan_structs_compile = prove
 (`!ctxt (p:(A)panLang_prog).
     ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2)) (pan_exps_of p) ==>
     ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2))
         (pan_exps_of (pan_structs_compile ctxt p))`,
  REC_IND_TAC pan_structs_compile_ind THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pan_exps_of_def; ALL; ALL_APPEND]) THEN
  ONCE_REWRITE_TAC[pan_structs_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT (PAIRARG_TAC THEN GVS[]) THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
          GVS[pan_exps_of_def; ALL; ALL_APPEND]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pan_exps_of_def; ALL; ALL_APPEND]) THEN
  SIMP[pan_exps_of_def; ALL; ALL_APPEND; every_inst_ok_less_pan_structs_compile_exp]);;

let every_inst_ok_less_pan_structs_compile_decs = prove
 (`!ctxt (pan_code:((A)decl)list).
     ALL good_panops pan_code ==>
     ALL good_panops (FST (pan_structs_compile_decs ctxt pan_code))`,
  REC_IND_TAC pan_structs_compile_decs_ind THEN REPEAT STRIP_TAC THEN
  SIMP[pan_structs_compile_decs_def; good_panops_def; ALL] THEN
  REPEAT (PAIRARG_TAC THEN FS[good_panops_def; ALL]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[good_panops_def; ALL]) THEN
  SIMP[good_panops_def; ALL; every_inst_ok_less_pan_structs_compile_exp;
       every_inst_ok_less_pan_structs_compile]);;

(* HOL4 quantifies a variable ctxt that the statement does not use *)
let every_inst_ok_less_pan_structs_compile_top = prove
 (`!pan_code:((A)decl)list.
     ALL good_panops pan_code ==> ALL good_panops (pan_structs_compile_top pan_code)`,
  REWRITE_TAC[pan_structs_compile_top_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[every_inst_ok_less_pan_structs_compile_decs]);;

let every_inst_ok_less_pan_globals_compile_exp = prove
 (`!ctxt (e:(A)panLang_exp).
     pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2) e ==>
     pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2)
       (pan_globals_compile_exp ctxt e)`,
  REC_IND_TAC pan_globals_compile_exp_ind THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pan_every_exp_def; ALL]) THEN
  ONCE_REWRITE_TAC[pan_globals_compile_exp_def] THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN GVS[]) THEN
  SIMP[pan_every_exp_def; ALL; ALL_MAP; LENGTH_MAP; o_DEF] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  ASM_MESON_TAC[]);;

let every_inst_ok_less_shape_val = prove
 (`(!sh. pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2)
           (shape_val sh:(A)panLang_exp)) /\
   (!shs. ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2))
           (shape_vals shs:((A)panLang_exp)list))`,
  MATCH_MP_TAC (cake_ind "shape_val") THEN
  REWRITE_TAC[shape_val_def; pan_every_exp_def; ALL] THEN SIMP[]);;

let every_inst_ok_less_pan_globals_compile = prove
 (`!ctxt (code:(A)panLang_prog).
     ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2)) (pan_exps_of code) ==>
     ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2))
         (pan_exps_of (pan_globals_compile ctxt code))`,
  REC_IND_TAC pan_globals_compile_ind THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pan_exps_of_def; ALL; ALL_APPEND]) THEN
  ONCE_REWRITE_TAC[pan_globals_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT (PAIRARG_TAC THEN GVS[]) THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
          GVS[pan_exps_of_def; ALL; ALL_APPEND]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pan_exps_of_def; ALL; ALL_APPEND]) THEN
  SIMP[pan_exps_of_def; ALL; ALL_APPEND; pan_every_exp_def; every_inst_ok_less_shape_val;
       ALL_MAP; o_DEF; every_inst_ok_less_pan_globals_compile_exp] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  ASM_MESON_TAC[every_inst_ok_less_pan_globals_compile_exp]);;

let every_inst_ok_less_pan_globals_compile_decs = prove
 (`!ctxt (pan_code:((A)decl)list).
     ALL good_panops pan_code ==>
     ALL good_panops (FST (SND (pan_globals_compile_decs ctxt pan_code)))`,
  REC_IND_TAC pan_globals_compile_decs_ind THEN REPEAT STRIP_TAC THEN
  SIMP[pan_globals_compile_decs_def; good_panops_def; ALL] THEN
  REPEAT (PAIRARG_TAC THEN FS[good_panops_def; ALL]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[good_panops_def; ALL]) THEN
  SIMP[good_panops_def; ALL; every_inst_ok_less_pan_globals_compile]);;

let every_inst_ok_less_pan_globals_compile_decs_init = prove
 (`!ctxt (pan_code:((A)decl)list).
     ALL good_panops pan_code ==>
     ALL (ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2)))
         (MAP pan_exps_of (FST (pan_globals_compile_decs ctxt pan_code)))`,
  REC_IND_TAC pan_globals_compile_decs_ind THEN REPEAT STRIP_TAC THEN
  SIMP[pan_globals_compile_decs_def; good_panops_def; ALL; MAP] THEN
  REPEAT (PAIRARG_TAC THEN FS[good_panops_def; ALL; MAP]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[good_panops_def; ALL]) THEN
  SIMP[good_panops_def; ALL; MAP; pan_exps_of_def; pan_every_exp_def;
       every_inst_ok_less_pan_globals_compile_exp]);;

let every_inst_ok_less_fperm = prove
 (`!f g (code:(A)panLang_prog).
     ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2)) (pan_exps_of code) ==>
     ALL (pan_every_exp (\x. !op es. x = Panop op es ==> LENGTH es = 2))
         (pan_exps_of (fperm f g code))`,
  REC_IND_TAC fperm_ind THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pan_exps_of_def; ALL; ALL_APPEND]) THEN
  ONCE_REWRITE_TAC[fperm_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT (PAIRARG_TAC THEN GVS[]) THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
          GVS[pan_exps_of_def; ALL; ALL_APPEND]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pan_exps_of_def; ALL; ALL_APPEND]) THEN
  SIMP[pan_exps_of_def; ALL; ALL_APPEND]);;

let every_inst_ok_less_fperm_decs = prove
 (`!f g (pan_code:((A)decl)list).
     ALL good_panops pan_code ==> ALL good_panops (fperm_decs f g pan_code)`,
  REC_IND_TAC fperm_decs_ind THEN
  RW[good_panops_def; fperm_decs_def; ALL; every_inst_ok_less_fperm]);;

(* good_panops survives resort_decls *)
let PTOPAUX_good_panops_resort_decls = prove
 (`!pan_code:((A)decl)list.
     ALL good_panops pan_code ==> ALL good_panops (resort_decls pan_code)`,
  REWRITE_TAC[resort_decls_def; GSYM ALL_MEM; MEM_APPEND; MEM_FILTER] THEN MESON_TAC[]);;

let every_inst_ok_less_pan_globals_compile_top = prove
 (`!(pan_code:((A)decl)list) main.
     ALL good_panops pan_code ==> ALL good_panops (pan_globals_compile_top pan_code main)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pan_globals_compile_top_def] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[ALL] THEN
  PAIRARG_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  PAIR_CASES_ON `pan_globals_compile_decs
     (pan_globals_context_REC FEMPTY (word 0)
        (word_mul bytes_in_word
          (word (SUM (MAP size_of_shape
             (dec_shapes (fperm_decs main (new_main_name pan_code)
                                      (resort_decls pan_code))))))))
     (fperm_decs main (new_main_name pan_code) (resort_decls (pan_code:((A)decl)list)))` THEN
  CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ALL good_panops (fperm_decs main (new_main_name pan_code)
                  (resort_decls (pan_code:((A)decl)list)))` ASSUME_TAC THENL
   [MATCH_MP_TAC every_inst_ok_less_fperm_decs THEN
    MATCH_MP_TAC PTOPAUX_good_panops_resort_decls THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP compile_decs_exns_are_exns) THEN
  MP_TAC (ISPECL
   [`pan_globals_context_REC FEMPTY (word 0)
        (word_mul bytes_in_word
          (word (SUM (MAP size_of_shape
             (dec_shapes (fperm_decs main (new_main_name pan_code)
                                      (resort_decls (pan_code:((A)decl)list))))))))
      :(A)pan_globals_context`;
    `fperm_decs main (new_main_name pan_code) (resort_decls (pan_code:((A)decl)list))`]
   every_inst_ok_less_pan_globals_compile_decs) THEN
  MP_TAC (ISPECL
   [`pan_globals_context_REC FEMPTY (word 0)
        (word_mul bytes_in_word
          (word (SUM (MAP size_of_shape
             (dec_shapes (fperm_decs main (new_main_name pan_code)
                                      (resort_decls (pan_code:((A)decl)list))))))))
      :(A)pan_globals_context`;
    `fperm_decs main (new_main_name pan_code) (resort_decls (pan_code:((A)decl)list))`]
   every_inst_ok_less_pan_globals_compile_decs_init) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  PAIRARG_TAC THEN
  ASM_REWRITE_TAC[ALL_APPEND; ALL; good_panops_def] THEN
  SIMP[pan_exps_of_def; pan_exps_of_nested_seq; ALL_APPEND; EVERY_FLAT; ALL_MAP; o_DEF;
       pan_every_exp_def] THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN GEN_TAC THEN QCASES_ON "x:(A)decl" THEN
  REWRITE_TAC[is_exn_decl_def; good_panops_def]);;

let pan_to_word_every_inst_ok_less = prove
 (`!(c:(A)asm_config) (pan_code:((A)decl)list) wprog0.
     pan_to_word_compile_prog (asm_config_ISA c) pan_code = wprog0 /\
     asm_offset_ok 0 (asm_config_byte_offset c) (word 0) /\
     asm_offset_ok 0 (asm_config_addr_offset c) (word 0) /\
     ALL good_panops pan_code ==>
     ALL (\(n,m,p). every_inst (inst_ok_less c) p) wprog0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pan_to_word_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  MATCH_MP_TAC (GEN_ALL loop_to_word_every_inst_ok_less) THEN
  EXISTS_TAC `crep_to_loop_compile_prog (asm_config_ISA (c:(A)asm_config))
     (pan_to_crep_compile_prog (pan_globals_compile_top
        (pan_structs_compile_top (pan_simp_compile_prog (pan_code:((A)decl)list)))
        (implode "main")))` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC every_inst_ok_less_crep_to_loop_compile_prog THEN
  MATCH_MP_TAC every_inst_ok_less_pan_to_crep_compile_prog THEN
  MATCH_MP_TAC every_inst_ok_less_pan_globals_compile_top THEN
  MATCH_MP_TAC every_inst_ok_less_pan_structs_compile_top THEN
  MATCH_MP_TAC every_inst_ok_less_pan_simp_compile_prog THEN
  ASM_REWRITE_TAC[]);;
