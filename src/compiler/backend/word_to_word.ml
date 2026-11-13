(* ========================================================================= *)
(* word_to_word: port of HOL4 compiler/backend/word_to_wordScript.sml        *)
(* (CakeML v3479).  This compiler phase composes the phases internal to     *)
(* wordLang: 1) word_simp; 2) inst_select; 3) SSA; 4) remove_dead;          *)
(* 5) word_cse; 6) copy_prop; 7) three-to-two reg; 8) remove_unreach;       *)
(* 9) remove_dead; 10) word_alloc.                                          *)
(*                                                                           *)
(* Notes on the rendering: the record config is word_to_word_config; HOL4   *)
(* word_simp$compile_exp is word_simp_compile_exp; HOL4 ZIP (l1,l2) is      *)
(* ZIP l1 l2 and MAP2 f l1 l2 is MAP2 f l1 l2; the mlstring literal of s is *)
(* implode "s"; paired lambdas are lambdas over a match.                    *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_alloc.ml";;
needs "compiler/backend/word_remove.ml";;
needs "compiler/backend/word_simp.ml";;
needs "compiler/backend/word_cse.ml";;
needs "compiler/backend/word_unreach.ml";;
needs "compiler/backend/word_copy.ml";;
needs "compiler/backend/word_inst.ml";;
needs "basis/pure/mlstring.ml";;

prioritize_num();;
type_invention_error := true;;

(*reg_alg = choice of register allocator*)
let word_to_word_config_INFO = cake_record "word_to_word_config"
  ["reg_alg","num";
   "col_oracle","((num spt)option)list"];;

let word_to_word_config_component_equality =
  word_to_word_config_INFO.ri_component_equality;;

(* HOL4: compile_single *)
let word_to_word_compile_single_def = cake_def
  `word_to_word_compile_single two_reg_arith reg_count alg (c:(A)asm_config)
     ((name_num:num,arg_count,prog:(A)wl_prog),col_opt) =
     let prog = word_simp_compile_exp prog in
     let maxv = max_var prog + 1 in
     let inst_prog = inst_select c maxv prog in
     let ssa_prog = full_ssa_cc_trans arg_count inst_prog in
     let rm_ssa_prog = remove_dead_prog ssa_prog in
     let cse_prog = word_common_subexp_elim rm_ssa_prog in
     let cp_prog = copy_prop cse_prog in
     let two_prog = three_to_two_reg_prog two_reg_arith cp_prog in
     let unreach_prog = remove_unreach two_prog in
     let rm_prog = remove_dead_prog unreach_prog in
     let reg_prog = word_alloc name_num c alg reg_count rm_prog col_opt in
     (name_num,arg_count,reg_prog)`;;

let full_compile_single_def = cake_def
  `full_compile_single two_reg_arith reg_count alg (c:(A)asm_config) p =
     let (name_num,arg_count,reg_prog) =
       word_to_word_compile_single two_reg_arith reg_count alg c p in
     (name_num,arg_count,remove_must_terminate reg_prog)`;;

let next_n_oracle_def = cake_def
  `next_n_oracle n (col:((num spt)option)list) =
     if n <= LENGTH col then (TAKE n col,DROP n col)
     else (REPLICATE n NONE,[])`;;

(* HOL4: compile *)
let word_to_word_compile_def = cake_def
  `word_to_word_compile word_conf (asm_conf:(A)asm_config) progs =
     let (two_reg_arith,reg_count) =
       (asm_config_two_reg_arith asm_conf,
        asm_config_reg_count asm_conf - (5 + LENGTH (asm_config_avoid_regs asm_conf))) in
     let (n_oracles,col) =
       next_n_oracle (LENGTH progs) (word_to_word_config_col_oracle word_conf) in
     let progs = ZIP progs n_oracles in
     (col,MAP (full_compile_single two_reg_arith reg_count
                 (word_to_word_config_reg_alg word_conf) asm_conf) progs)`;;

let full_compile_single_for_eval_def = cake_def
  `full_compile_single_for_eval two_reg_arith reg_count alg (c:(A)asm_config)
     (p:(num#num#(A)wl_prog)#(num spt)option) =
     let ((name_num,arg_count,prog),col_opt) = p in
     let prog = word_simp_compile_exp prog in
     let _ = empty_ffi (implode "finished: word_simp") in
     let maxv = max_var prog + 1 in
     let inst_prog = inst_select c maxv prog in
     let _ = empty_ffi (implode "finished: word_inst") in
     let ssa_prog = full_ssa_cc_trans arg_count inst_prog in
     let _ = empty_ffi (implode "finished: word_ssa") in
     let rm_ssa_prog = remove_dead_prog ssa_prog in
     let _ = empty_ffi (implode "finished: word_remove_dead after word_ssa") in
     let cse_prog = word_common_subexp_elim rm_ssa_prog in
     let _ = empty_ffi (implode "finished: word_cse") in
     let cp_prog = copy_prop cse_prog in
     let _ = empty_ffi (implode "finished: word_copy") in
     let two_prog = three_to_two_reg_prog two_reg_arith cp_prog in
     let _ = empty_ffi (implode "finished: word_two_reg") in
     let unreach_prog = remove_unreach two_prog in
     let _ = empty_ffi (implode "finished: word_unreach") in
     let rm_prog = remove_dead_prog unreach_prog in
     let _ = empty_ffi (implode "finished: word_remove_dead") in
     let reg_prog = word_alloc name_num c alg reg_count rm_prog col_opt in
     let _ = empty_ffi (implode "finished: word_alloc") in
     let rmt_prog = remove_must_terminate reg_prog in
     let _ = empty_ffi (implode "finished: word_remove") in
     (name_num,arg_count,rmt_prog)`;;

let full_compile_single_for_eval_eq = prove
 (`!two_reg_arith reg_count alg (c:(A)asm_config) p.
     full_compile_single two_reg_arith reg_count alg c p =
     full_compile_single_for_eval two_reg_arith reg_count alg c p`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[full_compile_single_for_eval_def; full_compile_single_def;
              word_to_word_compile_single_def] THEN
  SIMP[LET_DEF; LET_END_DEF]);;

(* WW2AUX_compile_alt_map: the list part of compile_alt, by induction on the *)
(* programs (os: the oracles, as many as the programs)                       *)
let WW2AUX_compile_alt_map = prove
 (CASE_TERM
  `!(progs:(num#num#(A)wl_prog)list) (os:((num spt)option)list) tra rc alg
     (asm_conf:(A)asm_config).
     LENGTH os = LENGTH progs
     ==> MAP (full_compile_single tra rc alg asm_conf) (ZIP progs os) =
         ZIP (MAP (\xyz. match xyz with (x,y,z) -> x) progs)
           (ZIP (MAP (\xyz. match xyz with (x,y,z) -> y) progs)
              (MAP remove_must_terminate
                 (MAP2 (\c np. match np with
                                 (n,p) -> word_alloc n asm_conf alg rc p c) os
                    (ZIP (MAP (\xyz. match xyz with (x,y,z) -> x) progs)
                       (MAP remove_dead_prog
                          (MAP remove_unreach
                             (MAP (three_to_two_reg_prog tra)
                                (MAP copy_prop
                                   (MAP word_common_subexp_elim
                                      (MAP remove_dead_prog
                                         (MAP2 (\a p. full_ssa_cc_trans a p)
                                            (MAP (\xyz. match xyz with (x,y,z) -> y)
                                                 progs)
                                            (MAP (\p. inst_select asm_conf
                                                        (max_var p + 1) p)
                                               (MAP word_simp_compile_exp
                                                  (MAP (\xyz. match xyz with
                                                                (x,y,z) -> z)
                                                       progs))))))))))))))`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ] THEN
  REWRITE_TAC[ZIP; MAP; MAP2_DEF; HD; TL] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[CONS_11] THEN
  SPEC_TAC(`h:num#num#(A)wl_prog`,`h:num#num#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  SIMP[full_compile_single_def; word_to_word_compile_single_def; LET_DEF;
       LET_END_DEF]);;

(* used for bootstrap translation *)
(* HOL4: compile_alt *)
let word_to_word_compile_alt = prove
 (CASE_TERM
  `!word_conf (asm_conf:(A)asm_config) progs.
     word_to_word_compile word_conf asm_conf progs =
     let (two_reg_arith,reg_count) =
       (asm_config_two_reg_arith asm_conf,
        asm_config_reg_count asm_conf - (5 + LENGTH (asm_config_avoid_regs asm_conf))) in
     let (n_oracles,col) =
       next_n_oracle (LENGTH progs) (word_to_word_config_col_oracle word_conf) in
     let alg = word_to_word_config_reg_alg word_conf in
     let names = MAP (\xyz. match xyz with (x,y,z) -> x) progs in
     let args = MAP (\xyz. match xyz with (x,y,z) -> y) progs in
     let ps = MAP (\xyz. match xyz with (x,y,z) -> z) progs in
     let simp_ps = MAP word_simp_compile_exp ps in
     let _ = empty_ffi (implode "finished: word_simp") in
     let inst_ps = MAP (\p. inst_select asm_conf (max_var p + 1) p) simp_ps in
     let _ = empty_ffi (implode "finished: word_inst") in
     let ssa_ps = MAP2 (\a p. full_ssa_cc_trans a p) args inst_ps in
     let _ = empty_ffi (implode "finished: word_ssa") in
     let rm_ssa_ps = MAP remove_dead_prog ssa_ps in
     let _ = empty_ffi (implode "finished: word_remove_dead after word_ssa") in
     let cse_ps = MAP word_common_subexp_elim rm_ssa_ps in
     let _ = empty_ffi (implode "finished: word_cse") in
     let cp_ps = MAP copy_prop cse_ps in
     let _ = empty_ffi (implode "finished: word_copy") in
     let two_ps = MAP (three_to_two_reg_prog two_reg_arith) cp_ps in
     let _ = empty_ffi (implode "finished: word_two_reg") in
     let unreach_ps = MAP remove_unreach two_ps in
     let _ = empty_ffi (implode "finished: word_unreach") in
     let dead_ps = MAP remove_dead_prog unreach_ps in
     let _ = empty_ffi (implode "finished: word_remove_dead") in
     let reg_ps = MAP2 (\c np. match np with
                                 (n,p) -> word_alloc n asm_conf alg reg_count p c)
                       n_oracles (ZIP names dead_ps) in
     let _ = empty_ffi (implode "finished: word_alloc") in
     let rmt_ps = MAP remove_must_terminate reg_ps in
     let _ = empty_ffi (implode "finished: word_remove") in
     (col,ZIP names (ZIP args rmt_ps))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_to_word_compile_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  SUBGOAL_THEN
   `LENGTH (FST (next_n_oracle (LENGTH (progs:(num#num#(A)wl_prog)list))
                   (word_to_word_config_col_oracle word_conf))) = LENGTH progs`
   MP_TAC THENL
   [REWRITE_TAC[next_n_oracle_def] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[LENGTH_TAKE; LENGTH_REPLICATE];
    ALL_TAC] THEN
  SPEC_TAC(`next_n_oracle (LENGTH (progs:(num#num#(A)wl_prog)list))
              (word_to_word_config_col_oracle word_conf)`,
           `nc:((num spt)option)list#((num spt)option)list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN REPEAT STRIP_TAC THEN
  SIMP[PAIR_EQ] THEN MATCH_MP_TAC WW2AUX_compile_alt_map THEN
  ASM_REWRITE_TAC[]);;
