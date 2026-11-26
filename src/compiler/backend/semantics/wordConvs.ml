(* ========================================================================= *)
(* wordConvs: port of HOL4 compiler/backend/semantics/wordConvsScript.sml    *)
(* (CakeML v3479).                                                           *)
(* Syntactic properties used by wordLang across passes.                     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - wordLang names carry the prefix wl_ where names.tsv says so (wl_Inst,   *)
(*   wl_every_var, ...); asm constructors asm_ (asm_Arith, asm_Shift, ...).  *)
(* - EVERY is ALL, set is set_of_list, BIGUNION is UNIONS, GENLIST f n is    *)
(*   list_of_seq f n, w2n is val, c.f is asm_config_f c.                     *)
(* - HOL4 set enumerations {a; b} are written {a, b}; the asm Overloads      *)
(*   addr_offset_ok, hw_offset_ok, byte_offset_ok are written out (as        *)
(*   asm.ml does): asm_offset_ok 0 (asm_config_addr_offset c) and so on.     *)
(* - The constants extract_labels, get_code_labels, good_code_labels and     *)
(*   no_install carry the prefix wordConvs_ (names.tsv); the HOL4 Overloads  *)
(*   word_get_code_labels, word_good_handlers, word_good_code_labels are     *)
(*   these constants.                                                        *)
(* - HOL4 temp_delsimps ["misc.max3_def"] has no counterpart (the kit's     *)
(*   cake_del_simps is global): the proofs below do not rely on it.          *)

(* Mono and conj lemmas for every_var/every_stack_var *)

let every_var_inst_mono = prove
 (`!P (inst:(A)inst) Q.
     (!x. P x ==> Q x) /\ every_var_inst P inst ==> every_var_inst Q inst`,
  MATCH_MP_TAC every_var_inst_ind THEN RW[every_var_inst_def] THEN
  CASES_ON `ri:(A)reg_imm` THEN FS[every_var_imm_def]);;

let every_var_exp_mono = prove
 (`!P (exp:(A)wl_exp) Q.
     (!x. P x ==> Q x) /\ every_var_exp P exp ==> every_var_exp Q exp`,
  MATCH_MP_TAC every_var_exp_ind THEN RW[every_var_exp_def] THEN
  FS[GSYM ALL_MEM] THEN ASM_MESON_TAC[]);;

let every_name_mono = prove
 (`!P (names:cutsets) Q.
     (!x. P x ==> Q x) /\ every_name P names ==> every_name Q names`,
  RW[every_name_def] THEN ASM_MESON_TAC[MONO_ALL]);;

let every_var_mono = prove
 (`!P (prog:(A)wl_prog) Q.
     (!x. P x ==> Q x) /\ wl_every_var P prog ==> wl_every_var Q prog`,
  SUBGOAL_THEN `!P (ri:(A)reg_imm) Q.
     (!x. P x ==> Q x) /\ every_var_imm P ri ==> every_var_imm Q ri`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN CASES_ON `ri:(A)reg_imm` THEN
    REWRITE_TAC[every_var_imm_def] THEN MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC wl_every_var_ind THEN REWRITE_TAC[wl_every_var_def] THEN
  REPEAT STRIP_TAC THEN EVERY_CASE_TAC THEN FS[] THEN REPEAT CONJ_TAC THEN
  FIRST [MATCH_MP_TAC every_var_inst_mono; MATCH_MP_TAC every_var_exp_mono;
         MATCH_MP_TAC every_name_mono;
         MATCH_MP_TAC(GEN_ALL(REWRITE_RULE[IMP_IMP] MONO_ALL));
         FIRST_ASSUM MATCH_MP_TAC] THEN
  EXISTS_TAC `P:num->bool` THEN ASM_REWRITE_TAC[]);;

(* Conjunct *)

let every_var_inst_conj = prove
 (`!P (inst:(A)inst) Q.
     every_var_inst P inst /\ every_var_inst Q inst <=>
     every_var_inst (\x. P x /\ Q x) inst`,
  MATCH_MP_TAC every_var_inst_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY(CASES_ON `ri:(A)reg_imm`) THEN
  REWRITE_TAC[every_var_inst_def; every_var_imm_def] THEN
  TRY COND_CASES_TAC THEN CONV_TAC TAUT);;

let every_var_exp_conj = prove
 (`!P (exp:(A)wl_exp) Q.
     every_var_exp P exp /\ every_var_exp Q exp <=>
     every_var_exp (\x. P x /\ Q x) exp`,
  MATCH_MP_TAC every_var_exp_ind THEN REWRITE_TAC[every_var_exp_def] THEN
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM; GSYM FORALL_AND_THM] THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    ASM_CASES_TAC `MEM (x:(A)wl_exp) ls` THEN ASM_SIMP_TAC[];
    REPEAT(FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th])) THEN CONV_TAC TAUT]);;

let every_name_conj = prove
 (`!P (names:cutsets) Q.
     every_name P names /\ every_name Q names <=>
     every_name (\x. P x /\ Q x) names`,
  REWRITE_TAC[every_name_def; GSYM AND_ALL] THEN CONV_TAC TAUT);;

let every_var_conj = prove
 (`!P (prog:(A)wl_prog) Q.
     wl_every_var P prog /\ wl_every_var Q prog <=>
     wl_every_var (\x. P x /\ Q x) prog`,
  SUBGOAL_THEN `!P (ri:(A)reg_imm) Q.
     every_var_imm P ri /\ every_var_imm Q ri <=>
     every_var_imm (\x. P x /\ Q x) ri`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN CASES_ON `ri:(A)reg_imm` THEN
    REWRITE_TAC[every_var_imm_def]; ALL_TAC] THEN
  MATCH_MP_TAC wl_every_var_ind THEN REWRITE_TAC[wl_every_var_def] THEN
  REPEAT STRIP_TAC THEN EVERY_CASE_TAC THEN FS[] THEN
  REWRITE_TAC[GSYM AND_ALL; GSYM every_var_inst_conj; GSYM every_var_exp_conj;
              GSYM every_name_conj] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th])) THEN
  CONV_TAC TAUT);;

(* Similar lemmas about every_stack_var *)

let every_var_imp_every_stack_var = prove
 (`!P (prog:(A)wl_prog). wl_every_var P prog ==> every_stack_var P prog`,
  MATCH_MP_TAC every_stack_var_ind THEN
  REWRITE_TAC[every_stack_var_def; wl_every_var_def] THEN
  REPEAT STRIP_TAC THEN EVERY_CASE_TAC THEN FS[]);;

let every_stack_var_mono = prove
 (`!P (prog:(A)wl_prog) Q.
     (!x. P x ==> Q x) /\ every_stack_var P prog ==> every_stack_var Q prog`,
  MATCH_MP_TAC every_stack_var_ind THEN REWRITE_TAC[every_stack_var_def] THEN
  REPEAT STRIP_TAC THEN EVERY_CASE_TAC THEN FS[] THEN REPEAT CONJ_TAC THEN
  FIRST [MATCH_MP_TAC every_name_mono; FIRST_ASSUM MATCH_MP_TAC] THEN
  EXISTS_TAC `P:num->bool` THEN ASM_REWRITE_TAC[]);;

let every_stack_var_conj = prove
 (`!P (prog:(A)wl_prog) Q.
     every_stack_var P prog /\ every_stack_var Q prog <=>
     every_stack_var (\x. P x /\ Q x) prog`,
  MATCH_MP_TAC every_stack_var_ind THEN REWRITE_TAC[every_stack_var_def] THEN
  REPEAT STRIP_TAC THEN EVERY_CASE_TAC THEN FS[] THEN
  REWRITE_TAC[GSYM every_name_conj] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th])) THEN
  CONV_TAC TAUT);;

(* labels_rel *)

let labels_rel_def = cake_def
  `labels_rel (old_labs:A list) new_labs <=>
     (ALL_DISTINCT old_labs ==> ALL_DISTINCT new_labs) /\
     set_of_list new_labs SUBSET set_of_list old_labs`;;

let labels_rel_refl = prove
 (`!xs:A list. labels_rel xs xs`,
  FS[labels_rel_def; SUBSET_REFL]);;

let _ = cake_add_simps [labels_rel_refl];;

let labels_rel_APPEND = prove
 (`!(xs:A list) xs1 ys ys1.
     labels_rel xs xs1 /\ labels_rel ys ys1
     ==> labels_rel (APPEND xs ys) (APPEND xs1 ys1)`,
  FS[labels_rel_def; ALL_DISTINCT_APPEND; SUBSET; IN_SET_OF_LIST;
     MEM_APPEND] THEN
  MESON_TAC[]);;

(* HOL4: labels_rel_APPEND |> Q.GENL [xs, xs1] |> Q.SPECL [[x], [x1]]      *)
(* |> SIMP_RULE std_ss [APPEND]                                              *)

let labels_rel_CONS = prove
 (`!(x:A) x1 ys ys1.
     labels_rel [x] [x1] /\ labels_rel ys ys1
     ==> labels_rel (CONS x ys) (CONS x1 ys1)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`[x:A]`; `[x1:A]`; `ys:A list`; `ys1:A list`]
                labels_rel_APPEND) THEN
  REWRITE_TAC[APPEND]);;

let PERM_IMP_labels_rel = prove
 (`!xs ys:A list. PERM xs ys ==> labels_rel ys xs`,
  REWRITE_TAC[labels_rel_def] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[ALL_DISTINCT_PERM];
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST] THEN ASM_MESON_TAC[MEM_PERM]]);;

let labels_rel_TRANS = prove
 (`!xs ys zs:A list.
     labels_rel xs ys /\ labels_rel ys zs ==> labels_rel xs zs`,
  REWRITE_TAC[labels_rel_def] THEN MESON_TAC[SUBSET_TRANS]);;

(* Expressions in ShareInst must be Var or Op Add; no other expressions     *)
(* occur except in Set, where it must be a Var expr.  Assign and Store      *)
(* should be converted to Insts; Set is the only place where top level      *)
(* (expression) vars are allowed.  The clauses are parsed apart (v, c and   *)
(* p have different types in different clauses).                            *)

let flat_exp_conventions_def = sem1aux_def (list_mk_conj
 [`flat_exp_conventions (wl_Assign v exp:(A)wl_prog) <=> F`;
  `flat_exp_conventions (wl_Store exp num:(A)wl_prog) <=> F`;
  `flat_exp_conventions (wl_Set store_name (wl_Var r):(A)wl_prog) <=> T`;
  `flat_exp_conventions (wl_Set store_name _:(A)wl_prog) <=> F`;
  `flat_exp_conventions (ShareInst op v (wl_Var r):(A)wl_prog) <=> T`;
  `flat_exp_conventions
     (ShareInst op v (wl_Op asm_Add [wl_Var r; wl_Const c]):(A)wl_prog) <=> T`;
  `flat_exp_conventions (ShareInst op v _:(A)wl_prog) <=> F`;
  `flat_exp_conventions (wl_Seq p1 p2:(A)wl_prog) <=>
     flat_exp_conventions p1 /\ flat_exp_conventions p2`;
  `flat_exp_conventions (wl_Loop names c exit_names:(A)wl_prog) <=>
     flat_exp_conventions c`;
  `flat_exp_conventions (wl_If cmp r1 ri e2 e3:(A)wl_prog) <=>
     flat_exp_conventions e2 /\ flat_exp_conventions e3`;
  `flat_exp_conventions (MustTerminate p:(A)wl_prog) <=>
     flat_exp_conventions p`;
  `flat_exp_conventions (wl_Call ret dest args h:(A)wl_prog) <=>
     (match ret with
        NONE -> T
      | SOME (v,cutset,ret_handler,l1,l2) ->
          flat_exp_conventions ret_handler) /\
     (match h with
        NONE -> T
      | SOME (v,prog,l1,l2) -> flat_exp_conventions prog)`;
  `flat_exp_conventions (_:(A)wl_prog) <=> T`]);;

let flat_exp_conventions_ind = cake_ind "flat_exp_conventions";;

(* Well-formed instructions. This also includes the FP conditions since we  *)
(* do not allocate them.                                                     *)

let inst_ok_less_def = sem1aux_def (list_mk_conj
 [`(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (asm_Arith (Binop b r1 r2 (Imm w))) <=>
     asm_config_valid_imm c (INL b) w`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (asm_Arith (asm_Shift l r1 r2 (Imm i))) <=>
     ((i = word 0) ==> (l = Lsl)) /\ val i < dimindex(:A)`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (asm_Arith (asm_Div r1 r2 r3)) <=>
     asm_config_ISA c IN {ARMv8, MIPS, RISC_V}`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (asm_Arith (LongMul r1 r2 r3 r4)) <=>
     (asm_config_ISA c = ARMv7 ==> ~(r1 = r2)) /\
     (asm_config_ISA c = ARMv8 \/ asm_config_ISA c = RISC_V \/
      asm_config_ISA c = Ag32 ==> ~(r1 = r3) /\ ~(r1 = r4))`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (asm_Arith (LongDiv r1 r2 r3 r4 r5)) <=>
     asm_config_ISA c = x86_64`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (asm_Arith (asm_AddCarry r1 r2 r3 r4)) <=>
     ((asm_config_ISA c = MIPS) \/ (asm_config_ISA c = RISC_V)
      ==> ~(r1 = r3) /\ ~(r1 = r4))`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (asm_Arith (AddOverflow r1 r2 r3 r4)) <=>
     ((asm_config_ISA c = MIPS) \/ (asm_config_ISA c = RISC_V)
      ==> ~(r1 = r3))`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (asm_Arith (SubOverflow r1 r2 r3 r4)) <=>
     ((asm_config_ISA c = MIPS) \/ (asm_config_ISA c = RISC_V)
      ==> ~(r1 = r3))`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (Mem m r (Addr r' w)) <=>
     if m IN {asm_Load, asm_Store, Load16, Store16, asm_Load32, asm_Store32}
     then asm_offset_ok 0 (asm_config_addr_offset c) w
     else if m IN {Load16, Store16}
     then asm_offset_ok 0 (asm_config_hw_offset c) w
     else asm_offset_ok 0 (asm_config_byte_offset c) w`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (FP (FPLess r d1 d2)) <=>
     fp_reg_ok d1 c /\ fp_reg_ok d2 c`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (FP (FPLessEqual r d1 d2)) <=>
     fp_reg_ok d1 c /\ fp_reg_ok d2 c`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (FP (FPEqual r d1 d2)) <=>
     fp_reg_ok d1 c /\ fp_reg_ok d2 c`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (FP (FPAbs d1 d2)) <=>
     (asm_config_two_reg_arith c ==> ~(d1 = d2)) /\
     fp_reg_ok d1 c /\ fp_reg_ok d2 c`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (FP (FPNeg d1 d2)) <=>
     (asm_config_two_reg_arith c ==> ~(d1 = d2)) /\
     fp_reg_ok d1 c /\ fp_reg_ok d2 c`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (FP (FPSqrt d1 d2)) <=>
     fp_reg_ok d1 c /\ fp_reg_ok d2 c`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (FP (FPAdd d1 d2 d3)) <=>
     (asm_config_two_reg_arith c ==> (d1 = d2)) /\
     fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (FP (FPSub d1 d2 d3)) <=>
     (asm_config_two_reg_arith c ==> (d1 = d2)) /\
     fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (FP (FPMul d1 d2 d3)) <=>
     (asm_config_two_reg_arith c ==> (d1 = d2)) /\
     fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (FP (FPDiv d1 d2 d3)) <=>
     (asm_config_two_reg_arith c ==> (d1 = d2)) /\
     fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (FP (FPFma d1 d2 d3)) <=>
     (asm_config_ISA c = ARMv7) /\
     2 < asm_config_fp_reg_count c /\
     fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (FP (FPMov d1 d2)) <=>
     fp_reg_ok d1 c /\ fp_reg_ok d2 c`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (FP (FPMovToReg r1 r2 d)) <=>
     ((dimindex(:A) = 32) ==> ~(r1 = r2)) /\ fp_reg_ok d c`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (FP (FPMovFromReg d r1 r2)) <=>
     ((dimindex(:A) = 32) ==> ~(r1 = r2)) /\ fp_reg_ok d c`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (FP (FPToInt d1 d2)) <=>
     fp_reg_ok d1 c /\ fp_reg_ok d2 c`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) c
     (FP (FPFromInt d1 d2)) <=>
     fp_reg_ok d1 c /\ fp_reg_ok d2 c`;
  `(inst_ok_less:(A)asm_config->(A)inst->bool) _ _ <=> T`]);;

(* Instructions have distinct targets and read vars -- set by SSA form *)

let distinct_tar_reg_def = sem1aux_def
  `(distinct_tar_reg (asm_Arith (Binop bop r1 r2 ri):(A)inst) <=>
      ~(ri = Reg r1)) /\
   (distinct_tar_reg (asm_Arith (asm_Shift l r1 r2 ri)) <=> ~(ri = Reg r1)) /\
   (distinct_tar_reg (asm_Arith (asm_AddCarry r1 r2 r3 r4)) <=>
      ~(r1 = r3) /\ ~(r1 = r4)) /\
   (distinct_tar_reg (asm_Arith (AddOverflow r1 r2 r3 r4)) <=> ~(r1 = r3)) /\
   (distinct_tar_reg (asm_Arith (SubOverflow r1 r2 r3 r4)) <=> ~(r1 = r3)) /\
   (distinct_tar_reg _ <=> T)`;;

(* Instructions are 2 register code for arith ok; currently no two_reg for  *)
(* Mul and Div                                                               *)

let two_reg_inst_def = sem1aux_def
  `(two_reg_inst (asm_Arith (Binop bop r1 r2 ri):(A)inst) <=> (r1 = r2)) /\
   (two_reg_inst (asm_Arith (asm_Shift l r1 r2 ri)) <=> (r1 = r2)) /\
   (two_reg_inst (asm_Arith (asm_AddCarry r1 r2 r3 r4)) <=> (r1 = r2)) /\
   (two_reg_inst (asm_Arith (AddOverflow r1 r2 r3 r4)) <=> (r1 = r2)) /\
   (two_reg_inst (asm_Arith (SubOverflow r1 r2 r3 r4)) <=> (r1 = r2)) /\
   (two_reg_inst _ <=> T)`;;

(* Recursor over instructions *)

let every_inst_def = sem1aux_def (list_mk_conj
 [`(every_inst:((A)inst->bool)->(A)wl_prog->bool)
     P (wl_Inst i:(A)wl_prog) <=> P i`;
  `(every_inst:((A)inst->bool)->(A)wl_prog->bool)
     P (wl_Seq p1 p2:(A)wl_prog) <=>
     every_inst P p1 /\ every_inst P p2`;
  `(every_inst:((A)inst->bool)->(A)wl_prog->bool)
     P (wl_Loop names c exit_names:(A)wl_prog) <=> every_inst P c`;
  `(every_inst:((A)inst->bool)->(A)wl_prog->bool)
     P (wl_If cmp r1 ri c1 c2:(A)wl_prog) <=>
     every_inst P c1 /\ every_inst P c2`;
  `(every_inst:((A)inst->bool)->(A)wl_prog->bool)
     (P:(A)inst->bool) (wl_OpCurrHeap bop r1 r2:(A)wl_prog) <=>
     P (asm_Arith (Binop bop r1 r2 (Reg r2)))`;
  `(every_inst:((A)inst->bool)->(A)wl_prog->bool)
     P (MustTerminate p:(A)wl_prog) <=> every_inst P p`;
  `(every_inst:((A)inst->bool)->(A)wl_prog->bool)
     P (wl_Call ret dest args handler:(A)wl_prog) <=>
     (match ret with
        NONE -> T
      | SOME (n,names,ret_handler,l1,l2) ->
          every_inst P ret_handler /\
          (match handler with
             NONE -> T
           | SOME (n,h,l1,l2) -> every_inst P h))`;
  `(every_inst:((A)inst->bool)->(A)wl_prog->bool)
     (P:(A)inst->bool) (prog:(A)wl_prog) <=> T`]);;

let every_inst_ind = cake_ind "every_inst";;

(* Every instruction is well-formed *)

let full_inst_ok_less_def = sem1aux_def (list_mk_conj
 [`(full_inst_ok_less:(A)asm_config->(A)wl_prog->bool)
     (c:(A)asm_config) (wl_Inst i) <=> inst_ok_less c i`;
  `(full_inst_ok_less:(A)asm_config->(A)wl_prog->bool)
     (c:(A)asm_config) (wl_Seq p1 p2) <=>
     full_inst_ok_less c p1 /\ full_inst_ok_less c p2`;
  `(full_inst_ok_less:(A)asm_config->(A)wl_prog->bool)
     (c:(A)asm_config) (wl_Loop names p exit_names) <=>
     full_inst_ok_less c p`;
  `(full_inst_ok_less:(A)asm_config->(A)wl_prog->bool)
     (c:(A)asm_config) (wl_If cmp r1 ri c1 c2) <=>
     full_inst_ok_less c c1 /\ full_inst_ok_less c c2`;
  `(full_inst_ok_less:(A)asm_config->(A)wl_prog->bool)
     (c:(A)asm_config) (MustTerminate p) <=>
     full_inst_ok_less c p`;
  `(full_inst_ok_less:(A)asm_config->(A)wl_prog->bool)
     (c:(A)asm_config) (wl_Call ret dest args handler) <=>
     (match ret with
        NONE -> T
      | SOME (n,names,ret_handler,l1,l2) ->
          full_inst_ok_less c ret_handler /\
          (match handler with
             NONE -> T
           | SOME (n,h,l1,l2) -> full_inst_ok_less c h))`;
  `(full_inst_ok_less:(A)asm_config->(A)wl_prog->bool)
     (c:(A)asm_config) (ShareInst op r ad) <=>
     match exp_to_addr ad with
       SOME (Addr _ w) ->
         if op IN {asm_Load, asm_Store, asm_Load32, asm_Store32}
         then asm_offset_ok 0 (asm_config_addr_offset c) w
         else if op IN {Load16, Store16}
         then asm_offset_ok 0 (asm_config_hw_offset c) w
         else asm_offset_ok 0 (asm_config_byte_offset c) w
     | NONE -> F`;
  `(full_inst_ok_less:(A)asm_config->(A)wl_prog->bool)
     (c:(A)asm_config) (prog:(A)wl_prog) <=> T`]);;

let full_inst_ok_less_ind = cake_ind "full_inst_ok_less";;

(* All cutsets are well-formed *)

let wf_names_def = cake_def
  `wf_names (t:A spt#B spt) <=> sptree_wf (FST t) /\ sptree_wf (SND t)`;;

let wf_cutsets_def = sem1aux_def (list_mk_conj
 [`wf_cutsets (wl_Alloc n s:(A)wl_prog) <=> wf_names s`;
  `wf_cutsets (wl_Install _ _ _ _ s:(A)wl_prog) <=> wf_names s`;
  `wf_cutsets (wl_Call ret dest args h:(A)wl_prog) <=>
     (match ret with
        NONE -> T
      | SOME (v,cutset,ret_handler,l1,l2) ->
          wf_names cutset /\
          wf_cutsets ret_handler /\
          (match h with
             NONE -> T
           | SOME (v,prog,l1,l2) -> wf_cutsets prog))`;
  `wf_cutsets (wl_FFI x1 y1 x2 y2 z args:(A)wl_prog) <=> wf_names args`;
  `wf_cutsets (MustTerminate s:(A)wl_prog) <=> wf_cutsets s`;
  `wf_cutsets (wl_Seq s1 s2:(A)wl_prog) <=> wf_cutsets s1 /\ wf_cutsets s2`;
  `wf_cutsets (wl_Loop names p exit_names:(A)wl_prog) <=>
     sptree_wf names /\ sptree_wf exit_names /\ wf_cutsets p`;
  `wf_cutsets (wl_If cmp r1 ri e2 e3:(A)wl_prog) <=>
     wf_cutsets e2 /\ wf_cutsets e3`;
  `wf_cutsets (_:(A)wl_prog) <=> T`]);;

let wf_cutsets_ind = cake_ind "wf_cutsets";;

(* Conventions for args to instructions (the AddOverflow and SubOverflow   *)
(* ones are not necessary); LongDiv follows conventions for x86 as it is   *)
(* the only possibility                                                     *)

let inst_arg_convention_def = sem1aux_def
  `(inst_arg_convention (asm_Arith (asm_AddCarry r1 r2 r3 r4):(A)inst) <=>
      r4 = 0) /\
   (inst_arg_convention (asm_Arith (asm_Shift _ _ _ (Reg r))) <=> r = 8) /\
   (inst_arg_convention (asm_Arith (AddOverflow r1 r2 r3 r4)) <=> r4 = 0) /\
   (inst_arg_convention (asm_Arith (SubOverflow r1 r2 r3 r4)) <=> r4 = 0) /\
   (inst_arg_convention (asm_Arith (LongMul r1 r2 r3 r4)) <=>
      r1 = 6 /\ r2 = 0 /\ r3 = 0 /\ r4 = 4) /\
   (inst_arg_convention (asm_Arith (LongDiv r1 r2 r3 r4 r5)) <=>
      r1 = 0 /\ r2 = 6 /\ r3 = 6 /\ r4 = 0) /\
   (inst_arg_convention _ <=> T)`;;

(* Calling conventions; the Call case does not check the case where Calls  *)
(* are ill-formed                                                           *)

let call_arg_convention_def = sem1aux_def (list_mk_conj
 [`call_arg_convention (wl_Inst i:(A)wl_prog) <=> inst_arg_convention i`;
  `call_arg_convention (wl_Return x ys:(A)wl_prog) <=>
     ys = list_of_seq (\x. 2 * (x + 1)) (LENGTH ys)`;
  `call_arg_convention (wl_Raise y:(A)wl_prog) <=> y = 2`;
  `call_arg_convention (wl_Install ptr len _ _ _:(A)wl_prog) <=>
     ptr = 2 /\ len = 4`;
  `call_arg_convention (wl_FFI x ptr len ptr2 len2 args:(A)wl_prog) <=>
     ptr = 2 /\ len = 4 /\ ptr2 = 6 /\ len2 = 8`;
  `call_arg_convention (wl_Alloc n s:(A)wl_prog) <=> n = 2`;
  `call_arg_convention (wl_StoreConsts a b c d ws:(A)wl_prog) <=>
     a = 0 /\ b = 2 /\ c = 4 /\ d = 6`;
  `call_arg_convention (wl_Call ret dest args h:(A)wl_prog) <=>
     (match ret with
        NONE -> args = list_of_seq (\x. 2 * x) (LENGTH args)
      | SOME (vs,cutset,ret_handler,l1,l2) ->
          args = list_of_seq (\x. 2 * (x + 1)) (LENGTH args) /\
          (vs = list_of_seq (\x. 2 * (x + 1)) (LENGTH vs)) /\
          call_arg_convention ret_handler /\
          (match h with
             NONE -> T
           | SOME (v,prog,l1,l2) -> (v = 2) /\ call_arg_convention prog))`;
  `call_arg_convention (MustTerminate s1:(A)wl_prog) <=>
     call_arg_convention s1`;
  `call_arg_convention (wl_Seq s1 s2:(A)wl_prog) <=>
     call_arg_convention s1 /\ call_arg_convention s2`;
  `call_arg_convention (wl_Loop names p exit_names:(A)wl_prog) <=>
     call_arg_convention p`;
  `call_arg_convention (wl_If cmp r1 ri e2 e3:(A)wl_prog) <=>
     call_arg_convention e2 /\ call_arg_convention e3`;
  `call_arg_convention (p:(A)wl_prog) <=> T`]);;

let call_arg_convention_ind = cake_ind "call_arg_convention";;

(* Before allocation, generated by SSA CC *)

let pre_alloc_conventions_def = cake_def
  `pre_alloc_conventions (p:(A)wl_prog) <=>
     every_stack_var is_stack_var p /\ call_arg_convention p`;;

(* After allocation, generated by allocator and/or the oracles *)

let post_alloc_conventions_def = cake_def
  `post_alloc_conventions k (prog:(A)wl_prog) <=>
     wl_every_var is_phy_var prog /\
     every_stack_var (\x. x >= 2 * k) prog /\
     call_arg_convention prog`;;

(* This is for label preservation -- wordLang should not need to inspect   *)
(* the labels explicitly.                                                   *)

let wordConvs_extract_labels_def = sem1aux_def (list_mk_conj
 [`(wordConvs_extract_labels:(A)wl_prog->(num#num)list)
     (wl_Call ret dest args h:(A)wl_prog) =
     match ret with
       NONE -> []
     | SOME (v,cutset,ret_handler,l1,l2) ->
         let ret_rest = wordConvs_extract_labels ret_handler in
         (match h with
            NONE -> APPEND [(l1,l2)] ret_rest
          | SOME (v,prog,l1',l2') ->
              let h_rest = wordConvs_extract_labels prog in
              APPEND (APPEND [(l1,l2); (l1',l2')] ret_rest) h_rest)`;
  `(wordConvs_extract_labels:(A)wl_prog->(num#num)list)
     (MustTerminate s1:(A)wl_prog) =
     wordConvs_extract_labels s1`;
  `(wordConvs_extract_labels:(A)wl_prog->(num#num)list)
     (wl_Seq s1 s2:(A)wl_prog) =
     APPEND (wordConvs_extract_labels s1) (wordConvs_extract_labels s2)`;
  `(wordConvs_extract_labels:(A)wl_prog->(num#num)list)
     (wl_Loop names p exit_names:(A)wl_prog) =
     wordConvs_extract_labels p`;
  `(wordConvs_extract_labels:(A)wl_prog->(num#num)list)
     (wl_If cmp r1 ri e2 e3:(A)wl_prog) =
     APPEND (wordConvs_extract_labels e2) (wordConvs_extract_labels e3)`;
  `(wordConvs_extract_labels:(A)wl_prog->(num#num)list)
     (_:(A)wl_prog) = []:(num#num) list`]);;

let wordConvs_extract_labels_ind = cake_ind "wordConvs_extract_labels";;

(* Property on max_var *)

(* HOL4 max_var_exp_IMP is [local] *)

let max_var_exp_IMP = prove
 (`!exp:(A)wl_exp. P 0 /\ every_var_exp P exp ==> P (max_var_exp exp)`,
  MATCH_MP_TAC max_var_exp_ind THEN
  REWRITE_TAC[max_var_exp_def; every_var_exp_def] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THENL
   [MATCH_MP_TAC MAX_LIST_intro THEN
    ASM_REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM ALL_MEM]) THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[MAX] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]]);;

(* helpers of max_var_intro (HOL4 uses MAX_DEF, max3_def and rpt           *)
(* TOP_CASE_TAC): P is closed under MAX and max3                            *)

let WORDP2AUX_MAX_P = prove
 (`!P a b. P a /\ P b ==> P (MAX a b)`,
  REWRITE_TAC[MAX] THEN MESON_TAC[]);;

let WORDP2AUX_max3_P = prove
 (`!P a b c. P a /\ P b /\ P c ==> P (max3 a b c)`,
  REWRITE_TAC[max3_def] THEN MESON_TAC[]);;

let WORDP2AUX_MAX_TAC =
  REPEAT(FIRST [MATCH_MP_TAC WORDP2AUX_max3_P THEN REPEAT CONJ_TAC;
                MATCH_MP_TAC WORDP2AUX_MAX_P THEN CONJ_TAC]);;

let max_var_intro = prove
 (`!prog:(A)wl_prog. P 0 /\ wl_every_var P prog ==> P (max_var prog)`,
  SUBGOAL_THEN
   `!P (i:(A)inst). P 0 /\ every_var_inst P i ==> P (max_var_inst i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC every_var_inst_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    TRY(CASES_ON `ri:(A)reg_imm`) THEN
    REWRITE_TAC[every_var_inst_def; max_var_inst_def; every_var_imm_def] THEN
    CAKE_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN WORDP2AUX_MAX_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC max_var_ind THEN
  REWRITE_TAC[max_var_def; wl_every_var_def; cutsets_max_def; every_name_def] THEN
  REPEAT STRIP_TAC THEN EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[every_var_imm_def]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT(FIRST [FIRST_ASSUM ACCEPT_TAC;
                MATCH_MP_TAC WORDP2AUX_max3_P THEN REPEAT CONJ_TAC;
                MATCH_MP_TAC WORDP2AUX_MAX_P THEN CONJ_TAC;
                MATCH_MP_TAC MAX_LIST_intro THEN CONJ_TAC;
                CHANGED_TAC(REWRITE_TAC[ALL; ALL_APPEND]) THEN REPEAT CONJ_TAC;
                MATCH_MP_TAC max_var_exp_IMP THEN CONJ_TAC;
                FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN CONJ_TAC)]) THEN
  ASM_MESON_TAC[]);;

(* code_labels *)

let wordConvs_get_code_labels_def = sem1aux_def (list_mk_conj
 [`(wordConvs_get_code_labels:(A)wl_prog->num->bool)
     (wl_Call r d a h:(A)wl_prog) =
     ((match d with SOME x -> {x} | _ -> {}) UNION
      (match r with
         SOME (_,_,x,_,_) -> wordConvs_get_code_labels x
       | _ -> {})) UNION
     (match h with
        SOME (_,x,l1,l2) -> wordConvs_get_code_labels x
      | _ -> {})`;
  `(wordConvs_get_code_labels:(A)wl_prog->num->bool)
     (wl_Seq p1 p2:(A)wl_prog) =
     wordConvs_get_code_labels p1 UNION wordConvs_get_code_labels p2`;
  `(wordConvs_get_code_labels:(A)wl_prog->num->bool)
     (wl_Loop names p exit_names:(A)wl_prog) =
     wordConvs_get_code_labels p`;
  `(wordConvs_get_code_labels:(A)wl_prog->num->bool)
     (wl_If _ _ _ p1 p2:(A)wl_prog) =
     wordConvs_get_code_labels p1 UNION wordConvs_get_code_labels p2`;
  `(wordConvs_get_code_labels:(A)wl_prog->num->bool)
     (MustTerminate p:(A)wl_prog) =
     wordConvs_get_code_labels p`;
  `(wordConvs_get_code_labels:(A)wl_prog->num->bool)
     (wl_LocValue _ l1:(A)wl_prog) = {l1}`;
  `(wordConvs_get_code_labels:(A)wl_prog->num->bool)
     (_:(A)wl_prog) = {}:num->bool`]);;

let wordConvs_get_code_labels_ind = cake_ind "wordConvs_get_code_labels";;

let _ = cake_add_simps [wordConvs_get_code_labels_def];;

(* TODO: This seems like it must have been established before handler     *)
(* labels point only within the current table entry                        *)

let good_handlers_def = sem1aux_def (list_mk_conj
 [`(good_handlers:num->(A)wl_prog->bool)
     n (wl_Call r d a h:(A)wl_prog) <=>
     match r with
       NONE -> T
     | SOME (_,_,x,_,_) ->
         good_handlers n x /\
         (match h with
            SOME (_,x,l1,_) -> l1 = n /\ good_handlers n x
          | _ -> T)`;
  `(good_handlers:num->(A)wl_prog->bool)
     n (wl_Seq p1 p2:(A)wl_prog) <=>
     good_handlers n p1 /\ good_handlers n p2`;
  `(good_handlers:num->(A)wl_prog->bool)
     n (wl_Loop names p exit_names:(A)wl_prog) <=>
     good_handlers n p`;
  `(good_handlers:num->(A)wl_prog->bool)
     n (wl_If _ _ _ p1 p2:(A)wl_prog) <=>
     good_handlers n p1 /\ good_handlers n p2`;
  `(good_handlers:num->(A)wl_prog->bool)
     n (MustTerminate p:(A)wl_prog) <=> good_handlers n p`;
  `(good_handlers:num->(A)wl_prog->bool)
     (n:num) (_:(A)wl_prog) <=> T`]);;

let good_handlers_ind = cake_ind "good_handlers";;

let _ = cake_add_simps [good_handlers_def];;

let wordConvs_good_code_labels_def = cake_def
  `wordConvs_good_code_labels (p:(num#num#(A)wl_prog) list) elabs <=>
     ALL (\(n,m,pp). good_handlers n pp) p /\
     UNIONS (set_of_list (MAP (\(n,m,pp). wordConvs_get_code_labels pp) p))
       SUBSET (set_of_list (MAP FST p) UNION elabs)`;;

(* not_created_subprogs: examines various syntactic elements within        *)
(* programs that some phases are expected to possibly remove but not       *)
(* create.                                                                  *)

let not_created_subprogs_def = sem1aux_def (list_mk_conj
 [`(not_created_subprogs:((A)wl_prog->bool)->(A)wl_prog->bool)
     P (MustTerminate p:(A)wl_prog) <=>
     P (MustTerminate (wl_Skip:(A)wl_prog)) /\ not_created_subprogs P p`;
  `(not_created_subprogs:((A)wl_prog->bool)->(A)wl_prog->bool)
     P (wl_Seq p1 p2:(A)wl_prog) <=>
     not_created_subprogs P p1 /\ not_created_subprogs P p2`;
  `(not_created_subprogs:((A)wl_prog->bool)->(A)wl_prog->bool)
     P (wl_Loop names c exit_names:(A)wl_prog) <=>
     not_created_subprogs P c`;
  `(not_created_subprogs:((A)wl_prog->bool)->(A)wl_prog->bool)
     P (wl_If _ _ _ p1 p2:(A)wl_prog) <=>
     not_created_subprogs P p1 /\ not_created_subprogs P p2`;
  `(not_created_subprogs:((A)wl_prog->bool)->(A)wl_prog->bool)
     P (wl_Call r dest args h:(A)wl_prog) <=>
     P (wl_Call NONE dest [] NONE:(A)wl_prog) /\
     (match r with
        NONE -> T
      | SOME (_,_,p,_) -> not_created_subprogs P p) /\
     (match h with
        NONE -> T
      | SOME (_,p,h1,_) ->
          P (wl_Call NONE NONE [] (SOME (0,wl_Skip,h1,0)):(A)wl_prog) /\
          not_created_subprogs P p)`;
  `(not_created_subprogs:((A)wl_prog->bool)->(A)wl_prog->bool)
     P (wl_Alloc _ _:(A)wl_prog) <=>
     P (wl_Alloc 0 (LN,LN):(A)wl_prog)`;
  `(not_created_subprogs:((A)wl_prog->bool)->(A)wl_prog->bool)
     P (wl_LocValue _ l:(A)wl_prog) <=>
     P (wl_LocValue 0 l:(A)wl_prog)`;
  `(not_created_subprogs:((A)wl_prog->bool)->(A)wl_prog->bool)
     P (ShareInst _ _ _:(A)wl_prog) <=>
     P (ShareInst ARB 0 (wl_Var 0):(A)wl_prog)`;
  `(not_created_subprogs:((A)wl_prog->bool)->(A)wl_prog->bool)
     P (wl_Install _ _ _ _ _:(A)wl_prog) <=>
     P (wl_Install 0 0 0 0 (LN,LN):(A)wl_prog)`;
  `(not_created_subprogs:((A)wl_prog->bool)->(A)wl_prog->bool)
     (_:(A)wl_prog->bool) (_:(A)wl_prog) <=> T`]);;

let not_created_subprogs_ind = cake_ind "not_created_subprogs";;

(* HOL4: not_created_subprogs_def |> BODY_CONJUNCTS |> map (GEN of the     *)
(* first argument) |> map (Q.SPEC P) |> LIST_CONJ |> Q.GEN P: every clause *)
(* with its first argument named P                                         *)

let not_created_subprogs_P_def =
  let p = `P:(A)wl_prog->bool` in
  let f th =
    let vs,_ = strip_forall(concl th) in
    let th1 = SPEC_ALL th in
    let a = hd(snd(strip_comb(lhs(concl th1)))) in
    GENL (filter (fun v -> v <> a) vs) (INST [p,a] th1) in
  GEN p (end_itlist CONJ (map f (CONJUNCTS not_created_subprogs_def)));;

(* no_alloc specialisation; HOL4 (<>) x is \q. ~(x = q) *)

let no_alloc_subprogs_def = cake_def
  `no_alloc (p:(A)wl_prog) <=>
     not_created_subprogs (\q. ~(wl_Alloc 0 (LN,LN) = q)) p`;;

let no_alloc_def = REWRITE_RULE[GSYM no_alloc_subprogs_def]
  (ISPEC `\q:(A)wl_prog. ~(wl_Alloc 0 (LN,LN) = q)` not_created_subprogs_P_def);;

let wordConvs_no_install_subprogs_def = cake_def
  `wordConvs_no_install (p:(A)wl_prog) <=>
     not_created_subprogs (\q. ~(wl_Install 0 0 0 0 (LN,LN) = q)) p`;;

let wordConvs_no_install_def = REWRITE_RULE[GSYM wordConvs_no_install_subprogs_def]
  (ISPEC `\q:(A)wl_prog. ~(wl_Install 0 0 0 0 (LN,LN) = q)`
         not_created_subprogs_P_def);;

(* no_mt : no MustTerminate *)

let no_mt_subprogs_def = cake_def
  `no_mt (p:(A)wl_prog) <=>
     not_created_subprogs (\q. ~(MustTerminate wl_Skip = q)) p`;;

let no_mt_def = REWRITE_RULE[GSYM no_mt_subprogs_def]
  (ISPEC `\q:(A)wl_prog. ~(MustTerminate wl_Skip = q)`
         not_created_subprogs_P_def);;

(* no_share_inst: no ShareInst *)

let no_share_inst_subprogs_def = cake_def
  `no_share_inst (p:(A)wl_prog) <=>
     not_created_subprogs (\q. ~(ShareInst ARB 0 (wl_Var 0) = q)) p`;;

let no_share_inst_def = REWRITE_RULE[GSYM no_share_inst_subprogs_def]
  (ISPEC `\q:(A)wl_prog. ~(ShareInst ARB 0 (wl_Var 0) = q)`
         not_created_subprogs_P_def);;

(* HOL4 Overloads word_get_code_labels, word_good_handlers and             *)
(* word_good_code_labels: the constants wordConvs_get_code_labels,          *)
(* good_handlers and wordConvs_good_code_labels.                           *)
