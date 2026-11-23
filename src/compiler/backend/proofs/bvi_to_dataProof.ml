(* ========================================================================= *)
(* bvi_to_dataProof: port of HOL4 compiler/backend/proofs/                   *)
(* bvi_to_dataProofScript.sml (CakeML v3479).  Correctness proof for         *)
(* bvi_to_data.  DATAPAUX_ names are local helpers (not HOL4 names).         *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - this script's code_rel and state_rel are bvi_to_dataProof_code_rel and  *)
(*   bvi_to_dataProof_state_rel; bvi_to_data's compile, compile_exp,         *)
(*   compile_part, compile_prog, optimise are bvi_to_data_compile ...;       *)
(*   bviSem values are bvlSem's bvl_v and refs bvl_ref, dataSem values       *)
(*   data_v (data_Block takes a time stamp first).                           *)
(* - HOL4 find_code of a bvi state is bvlSem's bvl_find_code; dest_thunk of *)
(*   a bvi state is bviSem's bvi_dest_thunk.                                 *)
(* - The Overloads isException, isReturn and isResult are written out;      *)
(*   dataSem's Block_nil is data_Block 0 nil_tag [].                         *)
(* - HOL4's unused binders are left out (isBool_simps b, data_to_bvi_v_eq n *)
(*   in its first four conjuncts and the derived theorems, the existentials  *)
(*   prog vs next_var of compile_exp_correct).                               *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/bvi_to_data.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/proofs/data_simpProof.ml";;
needs "compiler/backend/proofs/data_liveProof.ml";;
needs "compiler/backend/proofs/data_spaceProof.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4 lines 11-12: simpset settings (temp_delsimps, hide "tail") *)

(* HOL4 line 16 *)
let bvi_to_dataProof_code_rel_def = cake_def
  `bvi_to_dataProof_code_rel (bvi_code:(num # bvi_exp) spt)
                             (data_code:(num # data_prog) spt) <=>
     sptree_wf bvi_code /\ sptree_wf data_code /\
     domain bvi_code = domain data_code /\
     (!n exp arg_count.
        lookup n bvi_code = SOME (arg_count,exp)
        ==> lookup n data_code = SOME (arg_count,bvi_to_data_compile_exp arg_count exp))`;;

(* HOL4 line 30 (Termination: measure v_size) *)
let data_to_bvi_v_def = cake_def_wf
  `MEASURE data_v_size`
  TERM_TAC
  `(data_to_bvi_v (data_Number i) = bvl_Number i) /\
   (data_to_bvi_v (data_Word64 w) = bvl_Word64 w) /\
   (data_to_bvi_v (data_CodePtr p) = bvl_CodePtr p) /\
   (data_to_bvi_v (data_RefPtr b r) = bvl_RefPtr b r) /\
   (data_to_bvi_v (data_Block _ tag l) = bvl_Block tag (MAP data_to_bvi_v l))`;;
let _ = cake_add_simps [data_to_bvi_v_def];;

let data_to_bvi_v_ind = cake_ind "data_to_bvi_v";;

(* HOL4 line 51 *)
let data_to_bvi_v_Unit = prove
 (`data_to_bvi_v data_Unit = bvl_Unit`,
  REWRITE_TAC[data_Unit_def; bvl_Unit_def; data_to_bvi_v_def; MAP]);;
let _ = cake_add_simps [data_to_bvi_v_Unit];;

(* HOL4 line 58 *)
let data_to_bvi_v_Boolv = prove
 (`!b. data_to_bvi_v (data_Boolv b) = bvl_Boolv b`,
  REWRITE_TAC[data_Boolv_def; bvl_Boolv_def; data_to_bvi_v_def; MAP]);;
let _ = cake_add_simps [data_to_bvi_v_Boolv];;

(* HOL4 line 65 *)
let data_to_bvi_ref_def = cake_def
  `(data_to_bvi_ref (bvl_ValueArray l) = bvl_ValueArray (MAP data_to_bvi_v l)) /\
   (data_to_bvi_ref (bvl_ByteArray b bl) = bvl_ByteArray b bl) /\
   (data_to_bvi_ref (bvl_Thunk m v) = bvl_Thunk m (data_to_bvi_v v)) /\
   (data_to_bvi_ref (MutBlock tg fin ls c rs) =
      MutBlock tg fin (MAP data_to_bvi_v ls) (data_to_bvi_v c) (MAP data_to_bvi_v rs))`;;
let _ = cake_add_simps [data_to_bvi_ref_def];;

(* HOL4 line 74 *)
let bvi_to_dataProof_state_rel_def = cake_def
  `bvi_to_dataProof_state_rel (s:(C,FFI)bvi_state) (t:(C,FFI)data_state) <=>
     bvi_state_clock s = data_state_clock t /\
     bvi_to_dataProof_code_rel (bvi_state_code s) (data_state_code t) /\
     data_state_compile_oracle t =
       ((I ## bvi_to_data_compile_prog) o bvi_state_compile_oracle s) /\
     bvi_state_compile s =
       (\cfg prog. data_state_compile t cfg (bvi_to_data_compile_prog prog)) /\
     (!n. FLOOKUP (bvi_state_refs s) n =
          lookup n (sptree_map data_to_bvi_ref (data_state_refs t))) /\
     bvi_state_ffi s = data_state_ffi t /\
     bvi_state_global s = data_state_global t`;;

(* HOL4 lines 87-88: find_code_def is bvlSem's (an alias), and bvlSem's     *)
(* find_code is brought to the front of the overloads                         *)

(* HOL4 line 90 *)
let bvi_to_dataProof_find_code_lemma = prove
 (`!r t2 dest a args exp.
     bvi_to_dataProof_state_rel (r:(C,FFI)bvi_state) (t2:(C,FFI)data_state) /\
     bvl_find_code dest (MAP data_to_bvi_v a) (bvi_state_code r) = SOME (args,exp)
     ==> ?args' ss.
           args = MAP data_to_bvi_v args' /\
           data_find_code dest a (data_state_code t2) (data_state_stack_frame_sizes t2) =
             SOME (args',bvi_to_data_compile_exp (LENGTH args') exp,ss)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_to_dataProof_state_rel_def; bvi_to_dataProof_code_rel_def] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `bvl_find_code dest (MAP data_to_bvi_v a) (bvi_state_code (r:(C,FFI)bvi_state)) =
               SOME (args,exp)` THEN
  STRUCT_CASES_TAC(ISPEC `dest:num option` (cases "option")) THEN
  REWRITE_TAC[bvl_find_code_def; data_find_code_def] THENL
   [ASM_CASES_TAC `a:data_v list = []` THEN ASM_REWRITE_TAC[MAP; option_DISTINCT; MAP_EQ_NIL] THEN
    ASM_SIMP_TAC[LAST_MAP] THEN
    CASES_ON `LAST (a:data_v list)` THEN
    ASM_REWRITE_TAC[data_to_bvi_v_def] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `lookup a' (bvi_state_code (r:(C,FFI)bvi_state))` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `a'':num#bvi_exp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `e:bvi_exp` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[LENGTH_MAP] THEN
    ASM_CASES_TAC `LENGTH (a:data_v list) = arity + 1` THEN
    ASM_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ; COND_ID] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`BUTLAST (a:data_v list)`;
                          `lookup a' (data_state_stack_frame_sizes (t2:(C,FFI)data_state))`] THEN
    ASM_SIMP_TAC[MAP_FRONT; LENGTH_FRONT] THEN
    ASM_REWRITE_TAC[ARITH_RULE `PRE (n + 1) = n`];
    MP_TAC(ISPEC `lookup a' (bvi_state_code (r:(C,FFI)bvi_state))` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `a'':num#bvi_exp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `e:bvi_exp` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[LENGTH_MAP] THEN
    ASM_CASES_TAC `LENGTH (a:data_v list) = arity` THEN
    ASM_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ; COND_ID] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`a:data_v list`;
                          `lookup a' (data_state_stack_frame_sizes (t2:(C,FFI)data_state))`] THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 116 *)
let optimise_correct = prove
 (`!c s.
     ~(FST (data_evaluate (c,(s:(C,FFI)data_state))) = SOME (Rerr (Rabort Rtype_error))) /\
     ~(FST (data_evaluate (c,s)) = NONE)
     ==> ?safe peak smx ls.
           data_evaluate (bvi_to_data_optimise c,s) =
           (I ## (\x. data_state_locals_size_fupd (K ls)
                        (data_state_safe_for_space_fupd (K safe)
                           (data_state_peak_heap_length_fupd (K peak)
                              (data_state_stack_max_fupd (K smx) x)))))
             (data_evaluate (c,s))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `data_evaluate (c,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s2:(C,FFI)data_state` ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:data_prog`; `s:(C,FFI)data_state`] data_liveProof_compile_correct) THEN
  ASM_REWRITE_TAC[FST; PAIR_MAP_THM; I_THM] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ls:num option` (X_CHOOSE_THEN `sm:num option`
    (X_CHOOSE_THEN `safe1:bool` (X_CHOOSE_THEN `peak1:num` ASSUME_TAC)))) THEN
  REWRITE_TAC[bvi_to_data_optimise_def] THEN
  MP_TAC(ISPECL [`data_simp_simp (FST (data_live_compile c LN)) data_Skip`; `s:(C,FFI)data_state`]
    data_spaceProof_compile_correct) THEN
  ASM_REWRITE_TAC[simp_correct; FST; PAIR_MAP_THM; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `safe2:bool` (X_CHOOSE_THEN `peak2:num`
    (X_CHOOSE_THEN `smx:num option` SUBST1_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`safe2:bool`; `peak2:num`; `smx:num option`; `ls:num option`] THEN
  REWRITE_TAC[PAIR_EQ; data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 line 134 *)
let compile_RANGE_lemma = prove
 (`!n env tail live xs.
     ALL (\v. v < SND (SND (bvi_to_data_compile n env tail live xs)))
       (FST (SND (bvi_to_data_compile n env tail live xs)))`,
  MATCH_MP_TAC bvi_to_data_compile_ind THEN REPEAT CONJ_TAC THEN
  WORDP3AUX_IND_STEP_TAC ALL_TAC THEN
  TRY (REWRITE_TAC[MAX] THEN ARITH_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP compile_SING_IMP) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP compile_LESS_EQ o
    check (fun th -> can (find_term ((=) `CONS (y:bvi_exp) xs`)) (concl th))) THEN
  UNDISCH_TAC `ALL (\v. v < n1) (v1:num list)` THEN ASM_REWRITE_TAC[ALL; HD] THEN ARITH_TAC);;

(* HOL4 line 150 *)
let compile_RANGE = prove
 (`!n env tail live xs ys vs k.
     bvi_to_data_compile n env tail live xs = (ys,vs,k) ==> ALL (\v. v < k) vs`,
  REPEAT STRIP_TAC THEN MP_TAC (SPEC_ALL compile_RANGE_lemma) THEN ASM_REWRITE_TAC[]);;

(* HOL4 lines 156-158: Overloads isException, isReturn, isResult (written   *)
(* out where used); HOL4 line 160: stack_case_eq_thm is the case equality   *)
(* of :stack (the kit's case_eq "stack"); HOL4 line 162: val RW             *)

(* HOL4 line 164 *)
let compile_part_thm = prove
 (`bvi_to_data_compile_part =
   (\(x,y). (x,(\(a,b). (a,bvi_to_data_compile_exp a b)) y))`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; bvi_to_data_compile_part_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

(* HOL4 line 171 *)
let data_to_bvi_result_def = cake_def
  `(data_to_bvi_result (Rval vs) = Rval (MAP data_to_bvi_v vs)) /\
   (data_to_bvi_result (Rerr (Rraise v)) = Rerr (Rraise (Exn (data_to_bvi_v v)))) /\
   (data_to_bvi_result (Rerr (Rabort err)) = Rerr (Rabort err))`;;
let _ = cake_add_simps [data_to_bvi_result_def];;

(* HOL4 line 178 *)
let isBool_eq = prove
 (`!z b. isBool b z <=> bvl_Boolv b = data_to_bvi_v z`,
  GEN_TAC THEN CASES_ON `z:data_v` THEN
  REWRITE_TAC[isBool_def; data_to_bvi_v_def; bvl_Boolv_def; injectivity "bvl_v";
              distinctness "bvl_v"] THEN
  GEN_TAC THEN CASES_ON `a2:data_v list` THEN
  REWRITE_TAC[isBool_def; MAP; NOT_CONS_NIL] THEN MESON_TAC[]);;

(* HOL4 line 189 *)
let v_to_list_eq = prove
 (`!x. bvl_v_to_list (data_to_bvi_v x) =
       OPTION_MAP (MAP data_to_bvi_v) (data_v_to_list x)`,
  MATCH_MP_TAC data_v_to_list_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_bvi_v_def; MAP; bvl_v_to_list_def; data_v_to_list_def; OPTION_MAP_DEF] THEN
  TRY (COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; MAP] THEN NO_TAC) THEN
  DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
  FIRST_X_ASSUM(SUBST1_TAC o C MP (ASSUME `tag = cons_tag`)) THEN
  MP_TAC(ISPEC `data_v_to_list bt` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; MAP] THEN CASE_REWRITE_TAC[OPTION_MAP_DEF; MAP]);;
let _ = cake_add_simps [v_to_list_eq];;

(* HOL4 line 198 *)
let data_to_bvi_number_eq = prove
 (`!ns. MAP data_to_bvi_v (MAP (data_Number o int_of_num o val) (ns:(A word)list)) =
        MAP (bvl_Number o int_of_num o val) ns`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; o_THM; data_to_bvi_v_def]);;

(* HOL4 line 207 *)
let data_to_bvi_word_eq = prove
 (`!ns. MAP data_to_bvi_v (MAP data_Word64 ns) = MAP bvl_Word64 ns`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; o_THM; data_to_bvi_v_def]);;

(* HOL4 line 216 *)
let MAP_data_to_bvi_Number = prove
 (`!xs ws. MAP data_to_bvi_v (MAP data_Number xs) = MAP data_to_bvi_v ws <=>
           MAP data_Number xs = ws`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11] THEN
  CASES_ON `h':data_v` THEN
  REWRITE_TAC[data_to_bvi_v_def; injectivity "bvl_v"; distinctness "bvl_v";
              injectivity "data_v"; distinctness "data_v"]);;

(* HOL4 line 226 *)
let MAP_data_to_bvi_Word64 = prove
 (`!xs ws. MAP data_to_bvi_v (MAP data_Word64 xs) = MAP data_to_bvi_v ws <=>
           MAP data_Word64 xs = ws`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11] THEN
  CASES_ON `h':data_v` THEN
  REWRITE_TAC[data_to_bvi_v_def; injectivity "bvl_v"; distinctness "bvl_v";
              injectivity "data_v"; distinctness "data_v"]);;

(* HOL4 line 236 *)
let bvi_to_dataProof_v_to_bytes_eq = prove
 (`!x. bvl_v_to_bytes (data_to_bvi_v x) = data_v_to_bytes x`,
  GEN_TAC THEN REWRITE_TAC[bvl_v_to_bytes_def; data_v_to_bytes_def; v_to_list_eq] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  MP_TAC(ISPEC `data_v_to_list x` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
  REWRITE_TAC[GSYM data_to_bvi_number_eq; MAP_o] THEN
  GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
  REWRITE_TAC[GSYM MAP_o; MAP_data_to_bvi_Number] THEN MESON_TAC[]);;
let _ = cake_add_simps [bvi_to_dataProof_v_to_bytes_eq];;

(* HOL4 line 246 *)
let bvi_to_dataProof_v_to_words_eq = prove
 (`!x. bvl_v_to_words (data_to_bvi_v x) = data_v_to_words x`,
  GEN_TAC THEN REWRITE_TAC[bvl_v_to_words_def; data_v_to_words_def; v_to_list_eq] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  MP_TAC(ISPEC `data_v_to_list x` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
  REWRITE_TAC[GSYM data_to_bvi_word_eq] THEN
  GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
  REWRITE_TAC[MAP_data_to_bvi_Word64] THEN MESON_TAC[]);;
let _ = cake_add_simps [bvi_to_dataProof_v_to_words_eq];;

(* HOL4 line 256 (HOL4's unused binder b of both conjuncts is left out) *)
let isBool_simps = prove
 (`(!z. isBool T (z:data_v) ==> ~isBool F z) /\
   (!z. isBool F (z:data_v) ==> ~isBool T z)`,
  CONJ_TAC THEN GEN_TAC THEN CASES_ON `z:data_v` THEN REWRITE_TAC[isBool_def] THEN
  CASES_ON `a2:data_v list` THEN
  REWRITE_TAC[isBool_def; bool_to_tag_def; true_tag_def; false_tag_def] THEN
  ARITH_TAC);;

(* HOL4 line 272: val [isBool_T_F, isBool_F_T] = CONJUNCTS isBool_simps *)
let isBool_T_F = prove
 (`!z. isBool T (z:data_v) ==> ~isBool F z`,
  REWRITE_TAC[isBool_simps]);;

let isBool_F_T = prove
 (`!z. isBool F (z:data_v) ==> ~isBool T z`,
  REWRITE_TAC[isBool_simps]);;

(* HOL4 line 278 *)
let get_vars_lift_thm = prove
 (`!vs a t2.
     var_corr a vs (sptree_map data_to_bvi_v t2)
     ==> ?z. data_get_vars vs t2 = SOME z /\ a = MAP data_to_bvi_v z`,
  LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[var_corr_def; ALL2; data_get_vars_def; MAP] THEN
    EXISTS_TAC `[]:data_v list` THEN REWRITE_TAC[MAP];
    ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[var_corr_def; ALL2] THEN
  POP_ASSUM(K ALL_TAC) THEN
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t':bvl_v list`; `t2:data_v spt`]) THEN
  ASM_REWRITE_TAC[var_corr_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:data_v list` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `data_get_var h (sptree_map data_to_bvi_v t2) = SOME (h':bvl_v)` THEN
  REWRITE_TAC[data_get_var_def; lookup_map] THEN
  MP_TAC(ISPEC `lookup h (t2:data_v spt)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN DISCH_TAC THEN
  EXISTS_TAC `CONS (a:data_v) z` THEN
  ASM_REWRITE_TAC[data_get_vars_def; data_get_var_def; MAP] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 291 *)
let var_corr_inter = prove
 (`!t p vs z. var_corr z vs (sptree_inter (p:A spt) (t:B spt)) ==> var_corr z vs p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[var_corr_def] THEN
  MATCH_MP_TAC MONO_ALL2 THEN
  REWRITE_TAC[data_get_var_def; lookup_inter_alt] THEN MESON_TAC[option_DISTINCT]);;

(* HOL4 line 302 *)
let get_vars_mk_wf = prove
 (`!vs t z. data_get_vars vs (mk_wf (t:A spt)) = SOME z <=> data_get_vars vs t = SOME z`,
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EVERY_get_vars THEN REWRITE_TAC[GSYM ALL_MEM; lookup_mk_wf]);;
let _ = cake_add_simps [get_vars_mk_wf];;

(* HOL4 line 313 *)
let get_vars_inter = prove
 (`!vs p t z. data_get_vars vs (sptree_inter (p:A spt) (t:B spt)) = SOME z
              ==> data_get_vars vs p = SOME z`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC EVERY_get_vars THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `x IN domain (sptree_inter (p:A spt) (t:B spt))` MP_TAC THENL
   [ASM_MESON_TAC[data_get_vars_IMP_domain]; ALL_TAC] THEN
  REWRITE_TAC[domain_inter; IN_INTER; lookup_inter_alt] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 328 *)
let var_corr_map = prove
 (`!p (f:A->B) vs z. var_corr z vs p ==> var_corr (MAP f z) vs (sptree_map f p)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  CASES_ON `z:A list` THEN
  REWRITE_TAC[var_corr_def; ALL2; MAP; data_get_var_def; lookup_map] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[var_corr_def; data_get_var_def; lookup_map]) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 340 (the unused binder n of the first four conjuncts is left  *)
(* out)                                                                      *)
let data_to_bvi_v_eq = prove
 (`(!v i. data_to_bvi_v v = bvl_Number i <=> v = data_Number i) /\
   (!v w. data_to_bvi_v v = bvl_Word64 w <=> v = data_Word64 w) /\
   (!v p. data_to_bvi_v v = bvl_CodePtr p <=> v = data_CodePtr p) /\
   (!v r b. data_to_bvi_v v = bvl_RefPtr b r <=> v = data_RefPtr b r) /\
   (!v n l. data_to_bvi_v v = bvl_Block n l <=>
            ?ts l'. v = data_Block ts n l' /\ l = MAP data_to_bvi_v l')`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN CASES_ON `v:data_v` THEN
  REWRITE_TAC[data_to_bvi_v_def; injectivity "bvl_v"; distinctness "bvl_v";
              injectivity "data_v"; distinctness "data_v"] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [data_to_bvi_v_eq];;

(* HOL4 line 351: data_to_bvi_v_eq with each left side turned around       *)
(* (CONV_RULE ... LHS_CONV SYM_CONV)                                         *)
let data_to_bvi_v_eq' = prove
 (`(!v i. bvl_Number i = data_to_bvi_v v <=> v = data_Number i) /\
   (!v w. bvl_Word64 w = data_to_bvi_v v <=> v = data_Word64 w) /\
   (!v p. bvl_CodePtr p = data_to_bvi_v v <=> v = data_CodePtr p) /\
   (!v r b. bvl_RefPtr b r = data_to_bvi_v v <=> v = data_RefPtr b r) /\
   (!v n l. bvl_Block n l = data_to_bvi_v v <=>
            ?ts l'. v = data_Block ts n l' /\ l = MAP data_to_bvi_v l')`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN CASES_ON `v:data_v` THEN
  REWRITE_TAC[data_to_bvi_v_def; injectivity "bvl_v"; distinctness "bvl_v";
              injectivity "data_v"; distinctness "data_v"] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [data_to_bvi_v_eq'];;

(* HOL4 line 355: the conjuncts of data_to_bvi_v_eq, saved under the names *)
(* data_to_bvi_eq_Number ... data_to_bvi_eq_Block                            *)
let data_to_bvi_eq_Number = prove
 (`!v i. data_to_bvi_v v = bvl_Number i <=> v = data_Number i`,
  REWRITE_TAC[data_to_bvi_v_eq]);;

let data_to_bvi_eq_Word64 = prove
 (`!v w. data_to_bvi_v v = bvl_Word64 w <=> v = data_Word64 w`,
  REWRITE_TAC[data_to_bvi_v_eq]);;

let data_to_bvi_eq_CodePtr = prove
 (`!v p. data_to_bvi_v v = bvl_CodePtr p <=> v = data_CodePtr p`,
  REWRITE_TAC[data_to_bvi_v_eq]);;

let data_to_bvi_eq_RefPtr = prove
 (`!v r b. data_to_bvi_v v = bvl_RefPtr b r <=> v = data_RefPtr b r`,
  REWRITE_TAC[data_to_bvi_v_eq]);;

let data_to_bvi_eq_Block = prove
 (`!v n l. data_to_bvi_v v = bvl_Block n l <=>
           ?ts l'. v = data_Block ts n l' /\ l = MAP data_to_bvi_v l'`,
  REWRITE_TAC[data_to_bvi_v_eq]);;

(* HOL4 line 363 *)
let data_to_bvi_ref_eq = prove
 (`(!v fl ds. data_to_bvi_ref v = bvl_ByteArray fl ds <=> v = bvl_ByteArray fl ds) /\
   (!v l. data_to_bvi_ref v = bvl_ValueArray l <=>
          ?l'. v = bvl_ValueArray l' /\ l = MAP data_to_bvi_v l') /\
   (!v m w. data_to_bvi_ref v = bvl_Thunk m w <=>
            ?w'. v = bvl_Thunk m w' /\ w = data_to_bvi_v w') /\
   (!v tg fin ls c rs.
      data_to_bvi_ref v = MutBlock tg fin ls c rs <=>
      ?ls' c' rs'. v = MutBlock tg fin ls' c' rs' /\
                   ls = MAP data_to_bvi_v ls' /\ c = data_to_bvi_v c' /\
                   rs = MAP data_to_bvi_v rs')`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN CASES_ON `v:(data_v)bvl_ref` THEN
  REWRITE_TAC[data_to_bvi_ref_def; injectivity "bvl_ref"; distinctness "bvl_ref"] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [data_to_bvi_ref_eq];;

(* HOL4 line 377: data_to_bvi_ref_eq with each left side turned around *)
let data_to_bvi_ref_eq' = prove
 (`(!v fl ds. bvl_ByteArray fl ds = data_to_bvi_ref v <=> v = bvl_ByteArray fl ds) /\
   (!v l. bvl_ValueArray l = data_to_bvi_ref v <=>
          ?l'. v = bvl_ValueArray l' /\ l = MAP data_to_bvi_v l') /\
   (!v m w. bvl_Thunk m w = data_to_bvi_ref v <=>
            ?w'. v = bvl_Thunk m w' /\ w = data_to_bvi_v w') /\
   (!v tg fin ls c rs.
      MutBlock tg fin ls c rs = data_to_bvi_ref v <=>
      ?ls' c' rs'. v = MutBlock tg fin ls' c' rs' /\
                   ls = MAP data_to_bvi_v ls' /\ c = data_to_bvi_v c' /\
                   rs = MAP data_to_bvi_v rs')`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN CASES_ON `v:(data_v)bvl_ref` THEN
  REWRITE_TAC[data_to_bvi_ref_def; injectivity "bvl_ref"; distinctness "bvl_ref"] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [data_to_bvi_ref_eq'];;

(* HOL4 line 381: the conjuncts of data_to_bvi_ref_eq, saved under the     *)
(* names data_to_bvi_eq_ByteArray ... data_to_bvi_eq_MutBlock                *)
let data_to_bvi_eq_ByteArray = prove
 (`!v fl ds. data_to_bvi_ref v = bvl_ByteArray fl ds <=> v = bvl_ByteArray fl ds`,
  REWRITE_TAC[data_to_bvi_ref_eq]);;

let data_to_bvi_eq_ValueArray = prove
 (`!v l. data_to_bvi_ref v = bvl_ValueArray l <=>
         ?l'. v = bvl_ValueArray l' /\ l = MAP data_to_bvi_v l'`,
  REWRITE_TAC[data_to_bvi_ref_eq]);;

let data_to_bvi_eq_Thunk = prove
 (`!v m w. data_to_bvi_ref v = bvl_Thunk m w <=>
           ?w'. v = bvl_Thunk m w' /\ w = data_to_bvi_v w'`,
  REWRITE_TAC[data_to_bvi_ref_eq]);;

let data_to_bvi_eq_MutBlock = prove
 (`!v tg fin ls c rs.
     data_to_bvi_ref v = MutBlock tg fin ls c rs <=>
     ?ls' c' rs'. v = MutBlock tg fin ls' c' rs' /\
                  ls = MAP data_to_bvi_v ls' /\ c = data_to_bvi_v c' /\
                  rs = MAP data_to_bvi_v rs'`,
  REWRITE_TAC[data_to_bvi_ref_eq]);;

(* HOL4 line 388 *)
let data_to_bvi_result_eq = prove
 (`!x v. data_to_bvi_result x = Rerr (Rraise v) <=>
         ?z. x = Rerr (Rraise z) /\ Exn (data_to_bvi_v z) = v`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `x:(data_v list,data_v)result` (cases "result")) THEN
  REWRITE_TAC[data_to_bvi_result_def; injectivity "result"; distinctness "result"] THEN
  STRUCT_CASES_TAC(ISPEC `a:(data_v)error_result` (cases "error_result")) THEN
  REWRITE_TAC[data_to_bvi_result_def; injectivity "result"; distinctness "result";
              injectivity "error_result"; distinctness "error_result"] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [data_to_bvi_result_eq];;

(* HOL4 line 397 *)
let data_to_bvi_v_list_to_v_Nil = prove
 (`!z ts. data_to_bvi_v (data_list_to_v ts (data_Block 0 nil_tag []) z) =
          bvl_list_to_v (MAP data_to_bvi_v z)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[data_list_to_v_def; bvl_list_to_v_def; data_to_bvi_v_def; MAP]);;

(* HOL4 line 406 *)
let data_to_bvi_do_eq = prove
 (`(!t v1 v2 r.
      (!n. FLOOKUP r n = lookup n (sptree_map data_to_bvi_ref t))
      ==> bvl_do_eq r (data_to_bvi_v v1) (data_to_bvi_v v2) = data_do_eq t v1 v2) /\
   (!t l1 l2 r.
      (!n. FLOOKUP r n = lookup n (sptree_map data_to_bvi_ref t))
      ==> bvl_do_eq_list r (MAP data_to_bvi_v l1) (MAP data_to_bvi_v l2) =
          data_do_eq_list t l1 l2)`,
  MATCH_MP_TAC data_do_eq_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[data_to_bvi_v_def; MAP; data_do_eq_def; bvl_do_eq_def] THEN
  ASM_REWRITE_TAC[lookup_map] THENL
   [(* RefPtr *)
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    CASES_ON `lookup n1 (refs:((data_v)bvl_ref)spt)` THEN
    CASES_ON `lookup n2 (refs:((data_v)bvl_ref)spt)` THEN
    REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN
    REPEAT ((fun (asl,w as g) ->
      let v = find_term (fun t -> is_var t && type_of t = `:(data_v)bvl_ref`) w in
      CASES_ON v g) THEN
      REWRITE_TAC[data_to_bvi_ref_def] THEN CASE_REWRITE_TAC[]);
    (* Block *)
    REWRITE_TAC[bvl_isClos_def; data_isClos_def; MAP_EQ_NIL; LENGTH_MAP] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[data_isClos_def]) THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    (* CONS *)
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPEC `data_do_eq (refs:((data_v)bvl_ref)spt) v1 v2` (cases "eq_result")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* HOL4 line 429 *)
let data_to_bvi_v_list_to_v_APPEND = prove
 (`!l vl v ts.
     data_v_to_list v = SOME vl
     ==> data_to_bvi_v (data_list_to_v ts v l) =
         data_to_bvi_v (data_list_to_v ts (data_Block 0 nil_tag []) (APPEND l vl))`,
  SUBGOAL_THEN
   `!vl v ts. data_v_to_list v = SOME vl
              ==> data_to_bvi_v v =
                  data_to_bvi_v (data_list_to_v ts (data_Block 0 nil_tag []) vl)`
   ASSUME_TAC THENL
   [LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
     [REWRITE_TAC[v_to_list_SOME_NIL_IFF] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[data_list_to_v_def; data_to_bvi_v_def; MAP];
      DISCH_THEN(MP_TAC o MATCH_MP v_to_list_SOME_CONS_IMP) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[data_list_to_v_def; data_to_bvi_v_def; MAP; CONS_11;
                      injectivity "bvl_v"] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; data_list_to_v_def] THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[APPEND; data_list_to_v_def; data_to_bvi_v_def; MAP; CONS_11;
              injectivity "bvl_v"] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 454 *)
let refs_rel_LEAST_eq = prove
 (`!s1 s2.
     (!n. FLOOKUP s1 n = lookup n (sptree_map data_to_bvi_ref s2))
     ==> (minimal ptr. ~(ptr IN FDOM s1)) = (minimal ptr. ~(ptr IN domain s2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN FDOM (s1:(num,(bvl_v)bvl_ref)fmap) <=>
                    x IN domain (s2:((data_v)bvl_ref)spt)`
    (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN ASM_REWRITE_TAC[FDOM_FLOOKUP; domain_lookup; lookup_map] THEN
  CASES_ON `lookup x (s2:((data_v)bvl_ref)spt)` THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

(* local helper for do_build_thm: one part *)
let DATAPAUX_B2D_do_part = prove
 (`!p m1 m2 r t ts.
     (!n. FLOOKUP r n = OPTION_MAP data_to_bvi_ref (lookup n t)) /\
     (!n. m1 n = data_to_bvi_v (m2 n))
     ==> FST (bvl_do_part m1 p r) = data_to_bvi_v (FST (data_do_part m2 p t ts)) /\
         (!n. FLOOKUP (SND (bvl_do_part m1 p r)) n =
              OPTION_MAP data_to_bvi_ref (lookup n (FST (SND (data_do_part m2 p t ts)))))`,
  GEN_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `m1 = data_to_bvi_v o (m2:num->data_v)` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  CASES_ON `p:const_part` THEN
  REWRITE_TAC[bvl_do_part_def; data_do_part_def; LET_DEF; LET_END_DEF; FST; SND] THEN
  ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[FST; SND; MAP; data_to_bvi_v_def] THEN
    CASES_ON `ts:num option` THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[FST; SND; data_to_bvi_v_def; MAP_o];
    REWRITE_TAC[data_to_bvi_v_def];
    SUBGOAL_THEN `(minimal ptr. ~(ptr IN FDOM (r:(num,(bvl_v)bvl_ref)fmap))) =
                  (minimal ptr. ~(ptr IN domain (t:((data_v)bvl_ref)spt)))`
      SUBST1_TAC THENL
     [MATCH_MP_TAC refs_rel_LEAST_eq THEN ASM_REWRITE_TAC[lookup_map]; ALL_TAC] THEN
    REWRITE_TAC[data_to_bvi_v_def; FLOOKUP_UPDATE; lookup_insert] THEN
    GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[OPTION_MAP_DEF; data_to_bvi_ref_def] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[data_to_bvi_v_def]]);;

(* HOL4 line 465 *)
let do_build_thm = prove
 (`!parts m1 m2 k ts r t q rs.
     bvl_do_build m1 k parts r = (q,rs) /\
     (!n. FLOOKUP r n = OPTION_MAP data_to_bvi_ref (lookup n t)) /\
     (!n. m1 n = data_to_bvi_v (m2 n))
     ==> ?pres s1 ts1.
           data_do_build m2 k parts t ts = (pres,s1,ts1) /\
           q = data_to_bvi_v pres /\
           (!n. FLOOKUP rs n = OPTION_MAP data_to_bvi_ref (lookup n s1))`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[bvl_do_build_def; data_do_build_def; PAIR_EQ] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`(m2:num->data_v) (k - 1)`; `t:((data_v)bvl_ref)spt`;
                          `ts:num option`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`h:const_part`; `m1:num->bvl_v`; `m2:num->data_v`;
                 `r:(num,(bvl_v)bvl_ref)fmap`; `t':((data_v)bvl_ref)spt`; `ts:num option`]
                DATAPAUX_B2D_do_part) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `bvl_do_part m1 h (r:(num,(bvl_v)bvl_ref)fmap)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:bvl_v` (X_CHOOSE_THEN `refs1:(num,(bvl_v)bvl_ref)fmap`
    ASSUME_TAC)) THEN
  MP_TAC(ISPEC `data_do_part m2 h (t':((data_v)bvl_ref)spt) ts` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `x':data_v` (X_CHOOSE_THEN `y:((data_v)bvl_ref)spt # num option`
    ASSUME_TAC)) THEN
  MP_TAC(ISPEC `y:((data_v)bvl_ref)spt # num option` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:((data_v)bvl_ref)spt` (X_CHOOSE_THEN `ts1:num option`
    SUBST_ALL_TAC)) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  UNDISCH_TAC `bvl_do_build m1 k (CONS h t) (r:(num,(bvl_v)bvl_ref)fmap) = (q,rs)` THEN
  ASM_REWRITE_TAC[bvl_do_build_def; data_do_build_def; LET_DEF; LET_END_DEF; pair_CASE] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(k =+ x) (m1:num->bvl_v)`; `(k =+ x') (m2:num->data_v)`;
    `k + 1`; `ts1:num option`; `refs1:(num,(bvl_v)bvl_ref)fmap`;
    `s1:((data_v)bvl_ref)spt`; `q:bvl_v`; `rs:(num,(bvl_v)bvl_ref)fmap`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[APPLY_UPDATE_THM] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[];
    REWRITE_TAC[]]);;

(* HOL4 line 496 *)
let data_to_bvi_v_Boolv_IMP = prove
 (`!x0 b. data_to_bvi_v x0 = bvl_Boolv b ==> dest_Boolv x0 = SOME b`,
  REPEAT GEN_TAC THEN CASES_ON `x0:data_v` THEN
  REWRITE_TAC[data_to_bvi_v_def; bvl_Boolv_def; injectivity "bvl_v"; distinctness "bvl_v";
              dest_Boolv_def; MAP_EQ_NIL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[bool_to_tag_def; true_tag_def; false_tag_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* local tactic: for a goal ?x1 ... xn. body where body has a conjunct     *)
(* t = x1 or x1 = t (t free of x1 ... xn), supply t as the witness for x1 *)
let DATAPAUX_EXISTS_EQ_TAC : tactic = fun (asl,w as g) ->
  let xs,bod = strip_exists w in
  let x = hd xs in
  let rec conjs t = if is_conj t then conjs (lhand t) @ conjs (rand t) else [t] in
  let ok t = not (exists (fun v -> free_in v t) xs) in
  let pick c =
    if is_eq c then
      let l,r = dest_eq c in
      if r = x && ok l then l else if l = x && ok r then r else failwith "pick"
    else failwith "pick" in
  let t = tryfind pick (conjs bod) in
  EXISTS_TAC t g;;

(* HOL4 line 505 *)
let data_to_bvi_finalise_cons = prove
 (`!v refs ts brefs bv brefs'.
     (!n. FLOOKUP brefs n = OPTION_MAP data_to_bvi_ref (lookup n refs)) /\
     bvi_finalise_cons (data_to_bvi_v v) brefs = SOME (bv,brefs')
     ==> ?pv refs' ts'.
           data_finalise_cons v refs ts = SOME (pv,refs',ts') /\
           bv = data_to_bvi_v pv /\
           (!n. FLOOKUP brefs' n = OPTION_MAP data_to_bvi_ref (lookup n refs'))`,
  let nonmut_tac =
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    REPEAT DATAPAUX_EXISTS_EQ_TAC THEN ASM_REWRITE_TAC[data_to_bvi_v_def] THEN NO_TAC in
  let mut_tac =
    ASM_CASES_TAC `a1:bool` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
    SUBGOAL_THEN `!n. FLOOKUP ((brefs:(num,(bvl_v)bvl_ref)fmap) \\ ptr) n =
                      OPTION_MAP data_to_bvi_ref
                        (lookup n (delete ptr (refs:((data_v)bvl_ref)spt)))`
      ASSUME_TAC THENL
     [GEN_TAC THEN ASM_REWRITE_TAC[DOMSUB_FLOOKUP_THM; lookup_delete] THEN
      REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `bvi_finalise_cons (data_to_bvi_v a3)
                    ((brefs:(num,(bvl_v)bvl_ref)fmap) \\ ptr)` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2
      (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[option_DISTINCT])
      (X_CHOOSE_THEN `p:bvl_v#(num,(bvl_v)bvl_ref)fmap` ASSUME_TAC)) THEN
    MP_TAC(ISPEC `p:bvl_v#(num,(bvl_v)bvl_ref)fmap` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `c1:bvl_v`
      (X_CHOOSE_THEN `brefs1:(num,(bvl_v)bvl_ref)fmap` SUBST_ALL_TAC)) THEN
    REMOVE_THEN "ih" (MP_TAC o SPECL [`a0:num`; `a2:data_v list`; `a4:data_v list`;
      `a1:bool`; `a3:data_v`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`(brefs:(num,(bvl_v)bvl_ref)fmap) \\ ptr`; `c1:bvl_v`;
      `brefs1:(num,(bvl_v)bvl_ref)fmap`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `pv:data_v` (X_CHOOSE_THEN `refs1:((data_v)bvl_ref)spt`
      (X_CHOOSE_THEN `ts1:num option` STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_INJ; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    REPEAT DATAPAUX_EXISTS_EQ_TAC THEN
    REWRITE_TAC[data_to_bvi_v_def; MAP_APPEND; MAP] THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN REWRITE_TAC[FLOOKUP_UPDATE; lookup_insert] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; data_to_bvi_ref_def] THEN
    ASM_MESON_TAC[] in
  MATCH_MP_TAC data_finalise_cons_ind THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC[data_to_bvi_v_def] THEN
    ONCE_REWRITE_TAC[bvi_finalise_cons_def] THEN
    ONCE_REWRITE_TAC[data_finalise_cons_def] THEN
    ASM_REWRITE_TAC[] THEN
    CASES_ON `lookup ptr (refs:((data_v)bvl_ref)spt)` THEN
    REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
    CASES_ON `a:(data_v)bvl_ref` THEN REWRITE_TAC[data_to_bvi_ref_def] THEN
    CASE_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
    FIRST [nonmut_tac; mut_tac];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[data_to_bvi_v_def; bvi_finalise_cons_def; data_finalise_cons_def;
              option_INJ; PAIR_EQ] THEN
  nonmut_tac);;

(* HOL4 line 527: fun cases_on_op (a tactic) *)

(* local tactic: split the first case expression of the goal, preferring  *)
(* a scrutinee data_to_bvi_v x, MAP data_to_bvi_v l or data_to_bvi_ref x    *)
(* (x, l variables), split by a case analysis on x or l, or a scrutinee     *)
(* OPTION_MAP data_to_bvi_ref y, split by a case analysis on y (only      *)
(* scrutinees free in the goal)                                              *)
let DATAPAUX_B2D_SPLIT_TAC : tactic = fun (asl,w as g) ->
  let scrs = filter (fun s -> free_in s w)
                    (mapfilter scrutinee_of (find_terms is_case_app w)) in
  let pick s =
    if is_comb s && is_var (rand s) &&
       (rator s = `data_to_bvi_v` || rator s = `MAP data_to_bvi_v` ||
        rator s = `data_to_bvi_ref`)
    then rand s
    else if is_comb s && rator s = `OPTION_MAP data_to_bvi_ref` then rand s
    else failwith "pick" in
  (try CASES_ON (tryfind pick scrs) g
   with Failure _ -> TOP_CASE_TAC g);;

(* local helpers for data_to_bvi_do_app: the integer and word operations *)
let DATAPAUX_B2D_int_app = prove
 (`!op vs. ~(?n. op = clos_Const n)
           ==> bvl_do_int_app op (MAP data_to_bvi_v vs) =
               OPTION_MAP data_to_bvi_v (data_do_int_app op vs)`,
  MATCH_MP_TAC (CLOSSEMAUX_cases_ind data_do_int_app_def) THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MAP; data_to_bvi_v_def; data_do_int_app_def; bvl_do_int_app_def;
              OPTION_MAP_DEF; injectivity "int_op"; distinctness "int_op";
              data_to_bvi_v_Boolv] THEN
  TRY COND_CASES_TAC THEN
  REWRITE_TAC[OPTION_MAP_DEF; data_to_bvi_v_def; data_to_bvi_v_Boolv] THEN
  MESON_TAC[]);;

let DATAPAUX_B2D_word_app = prove
 (`!op vs. ~(op = WordTest W8 (Compare Gt)) /\ ~(op = WordTest W8 (Compare Geq))
           ==> bvl_do_word_app op (MAP data_to_bvi_v vs) =
               OPTION_MAP data_to_bvi_v (data_do_word_app op vs)`,
  let rws = [MAP; data_to_bvi_v_def; OPTION_MAP_DEF; data_to_bvi_v_Boolv;
             injectivity "word_op"; distinctness "word_op"; int_cmp_def] in
  MATCH_MP_TAC (CLOSSEMAUX_cases_ind data_do_word_app_def) THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC(data_do_word_app_def :: bvl_do_word_app_def :: rws) THEN
  REPEAT (DATAPAUX_B2D_SPLIT_TAC THEN REWRITE_TAC rws THEN CASE_REWRITE_TAC rws));;

(* local helper: the refs relation after an update of one reference *)
let DATAPAUX_B2D_FLOOKUP_insert = prove
 (`!(rr:(num,(bvl_v)bvl_ref)fmap) (tr:((data_v)bvl_ref)spt) p x y.
     (!n. FLOOKUP rr n = OPTION_MAP data_to_bvi_ref (lookup n tr)) /\
     y = data_to_bvi_ref x
     ==> !n. FLOOKUP (rr |+ (p,y)) n = OPTION_MAP data_to_bvi_ref (lookup n (insert p x tr))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[FLOOKUP_UPDATE; lookup_insert] THEN
  ASM_CASES_TAC `(n:num) = p` THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* local helpers for data_to_bvi_do_app *)
let DATAPAUX_B2D_Boolv_eq = prove
 (`!x b. data_to_bvi_v x = bvl_Boolv b <=> dest_Boolv x = SOME b`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `x:data_v` THEN
  REWRITE_TAC[data_to_bvi_v_def; bvl_Boolv_def; injectivity "bvl_v"; distinctness "bvl_v";
              dest_Boolv_def; MAP_EQ_NIL; option_DISTINCT] THEN
  ASM_CASES_TAC `a2:data_v list = []` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[bool_to_tag_def; true_tag_def; false_tag_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN ASM_ARITH_TAC);;

let DATAPAUX_B2D_do_eq_rw = prove
 (`!(rr:(num,(bvl_v)bvl_ref)fmap) (tr:((data_v)bvl_ref)spt) v1 v2.
     (!n. FLOOKUP rr n = OPTION_MAP data_to_bvi_ref (lookup n tr))
     ==> bvl_do_eq rr (data_to_bvi_v v1) (data_to_bvi_v v2) = data_do_eq tr v1 v2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC (CONJUNCT1 data_to_bvi_do_eq) THEN
  ASM_REWRITE_TAC[lookup_map]);;

let DATAPAUX_B2D_bad_thunk = prove
 (`!(rr:(num,(bvl_v)bvl_ref)fmap) (tr:((data_v)bvl_ref)spt) m v.
     (!n. FLOOKUP rr n = OPTION_MAP data_to_bvi_ref (lookup n tr))
     ==> (bvl_bad_thunk_update m (data_to_bvi_v v) rr <=>
          data_bad_thunk_update m v tr)`,
  let rws = [bvl_dest_thunk_def; data_dest_thunk_def; data_to_bvi_v_def; data_to_bvi_ref_def;
             OPTION_MAP_DEF; distinctness "bvl_dest_thunk_ret";
             distinctness "data_dest_thunk_ret"] in
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bvl_bad_thunk_update_def; data_bad_thunk_update_def] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CASES_ON `v:data_v` THEN
  ASM_REWRITE_TAC rws THEN
  REPEAT (DATAPAUX_B2D_SPLIT_TAC THEN ASM_REWRITE_TAC rws THEN CASE_REWRITE_TAC rws));;

(* local helpers for data_to_bvi_do_app: the generic proof of one         *)
(* operation (PRE_TAC unfolds the semantics, STEP_TAC splits the case      *)
(* expressions of both sides in parallel, LEAF_TAC proves a successful      *)
(* result, NORM_TAC and CLOSE_TAC clean up assumptions)                     *)
let DATAPAUX_B2D_RWS = [MAP; data_to_bvi_v_def; data_to_bvi_ref_def; bvi_bvi_to_bvl_refs;
               bvi_to_bvl_ffi; OPTION_MAP_DEF; injectivity "result"; distinctness "result";
               PAIR_EQ; injectivity "error_result"; distinctness "error_result";
               LENGTH_MAP; LET_DEF; LET_END_DEF; v_to_list_eq; DATAPAUX_B2D_Boolv_eq;
               bvl_Boolv_11; NULL_EQ; MAP_EQ_NIL; data_to_bvi_v_Boolv; data_to_bvi_v_Unit;
               with_fresh_ts_def; option_DISTINCT; option_INJ];;
let DATAPAUX_B2D_SPLIT2_TAC : tactic = fun (asl,w as g) ->
  let scrs = filter (fun s -> free_in s w)
                    (mapfilter scrutinee_of (find_terms is_case_app w)) in
  let pick s =
    if is_comb s && is_var (rand s) &&
       (rator s = `data_to_bvi_v` || rator s = `MAP data_to_bvi_v` ||
        rator s = `data_to_bvi_ref`)
    then rand s
    else if is_comb s && (rator s = `OPTION_MAP data_to_bvi_ref` ||
                          rator s = `OPTION_MAP data_to_bvi_v` ||
                          rator s = `OPTION_MAP (MAP data_to_bvi_v)`) then rand s
    else failwith "pick" in
  (try CASES_ON (tryfind pick scrs) g
   with Failure _ -> CASE_TAC g);;
let DATAPAUX_B2D_STEP_TAC =
  DATAPAUX_B2D_SPLIT2_TAC THEN ASM_REWRITE_TAC DATAPAUX_B2D_RWS THEN
  CASE_REWRITE_TAC DATAPAUX_B2D_RWS;;

(* ASM_MESON_TAC[option_CASES; option_DISTINCT] for the liveness goals         *)
(* (!x. MEM x live ==> ~(lookup x (locals t1) = NONE)) ==> (.. t2 ..): MESON    *)
(* with the facts about lookup only, not the induction hypotheses (12 s with   *)
(* all the assumptions)                                                         *)
let DATAPAUX_LOOKUP_MESON_TAC : tactic =
  let has c tm = can (find_term (fun t -> is_const t && fst(dest_const t) = c)) tm in
  (fun (asl,w as gl) ->
     MESON_TAC(option_CASES :: option_DISTINCT ::
               filter (fun th -> has "lookup" (concl th) && not (has "bvi_evaluate" (concl th)))
                      (map snd asl)) gl) ORELSE
  ASM_MESON_TAC[option_CASES; option_DISTINCT];;

(* ASM_MESON_TAC thl on each conjunct, after two cheap closings of the frame   *)
(* goals of the calls (ASM_MESON_TAC took 2-108 s on them): the conjunct from   *)
(* the assumptions by modus ponens (after discharging its antecedents), or a    *)
(* conjunct Q ==> R from an assumption P \/ Q ==> R                             *)
let DATAPAUX_FAST_MESON_TAC thl : tactic =
  let mp_sat : tactic = fun (asl,w as gl) ->
    let rec go facts =
      let news = mapfilter (fun th ->
          let c = concl th in
          if is_imp c && not (exists (fun f -> aconv (concl f) (rand c)) facts) then
            MP th (find (fun f -> aconv (concl f) (lhand c)) facts)
          else failwith "") facts in
      if news = [] then facts else go (news @ facts) in
    let facts = go (flat (map (CONJUNCTS o snd) asl)) in
    ACCEPT_TAC (find (fun f -> aconv (concl f) w) facts) gl in
  let disch_imp : tactic = fun (asl,w as gl) ->
    if is_imp w then DISCH_TAC gl else failwith "disch_imp" in
  REPEAT CONJ_TAC THEN
  FIRST [REPEAT disch_imp THEN mp_sat;
         FIRST_X_ASSUM(fun th -> if is_imp (concl th) && is_disj (lhand (concl th))
                                 then MP_TAC th THEN MESON_TAC[] else NO_TAC);
         ASM_MESON_TAC thl];;

(* the theorem CASE x (\a. e) .. (\b c. e) = e of a case constant (all arms the *)
(* same term, independent of the constructor arguments), memoised             *)
let DATAPAUX_case_const_thms = ref ([] : (string * thm) list);;
let DATAPAUX_case_const_thm (c:term) =
  let n = fst(dest_const c) in
  try assoc n !DATAPAUX_case_const_thms with Failure _ ->
  let ci = case_info_of_const c in
  let cc = ci.ci_case in
  let tys,rty = splitlist dest_fun_ty (type_of cc) in
  let x = mk_var("x",hd tys) and e = mk_var("e",rty) in
  let arms = map (fun (vs,_) -> list_mk_abs(vs,e)) ci.ci_pats in
  let th = prove(mk_eq(list_mk_comb(cc,x::arms),e),
                 MP_TAC(SPEC x ci.ci_nchotomy) THEN STRIP_TAC THEN
                 ASM_REWRITE_TAC[ci.ci_def]) in
  DATAPAUX_case_const_thms := (n,th) :: !DATAPAUX_case_const_thms; th;;

(* the case expressions of the goal whose arms are all the same: the arm *)
let DATAPAUX_CASE_CONST_TAC : tactic = fun (asl,w as gl) ->
  let cs = setify (map (fun t -> let h,_,_ = dest_case_app t in h)
                     (find_terms is_case_app w)) in
  let ths = mapfilter DATAPAUX_case_const_thm cs in
  if ths = [] then ALL_TAC gl else REWRITE_TAC ths gl;;

(* STEP_TAC that also drops the case splits whose arms are all the same (on *)
(* the error cases of a do_app, STEP_TAC split up to 1234 goals)             *)
let DATAPAUX_B2D_STEP2_TAC =
  DATAPAUX_B2D_STEP_TAC THEN DATAPAUX_CASE_CONST_TAC;;
let DATAPAUX_B2D_CLOSE_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE DATAPAUX_B2D_RWS) THEN
  (fun g -> (FIRST_ASSUM CONTR_TAC ORELSE ALL_TAC) g);;
let DATAPAUX_B2D_LEAF_TAC =
  TRY (DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM))) THEN
  REPEAT DATAPAUX_EXISTS_EQ_TAC THEN
  RULE_ASSUM_TAC(fun th -> try REWRITE_RULE[GSYM DATAPAUX_B2D_Boolv_eq] th with _ -> th) THEN
  REWRITE_TAC[data_to_bvi_v_Unit; data_to_bvi_v_Boolv; data_to_bvi_v_def; MAP;
              bvl_to_bvi_with_refs; bvl_to_bvi_with_ffi; bvl_to_bvi_id] THEN
  REWRITE_TAC[bvi_to_dataProof_state_rel_def; bvi_state_INFO.ri_accfupds;
              data_state_INFO.ri_accfupds; K_THM; lookup_map; check_lim_def] THEN
  ASM_REWRITE_TAC[bvl_Boolv_11] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GE; NOT_LE]) THEN
  ASM_SIMP_TAC[EL_MAP; BASICAUX_num_of_int_lt; MAP_TAKE; MAP_DROP; MAP_APPEND;
               LUPDATE_MAP; map_replicate] THEN
  TRY (FIRST_ASSUM (fun th -> REWRITE_TAC[MATCH_MP data_to_bvi_v_list_to_v_APPEND th;
                                          data_to_bvi_v_list_to_v_Nil; MAP_APPEND]) THEN
       NO_TAC) THEN
  TRY (MATCH_MP_TAC DATAPAUX_B2D_FLOOKUP_insert THEN
       ASM_REWRITE_TAC[data_to_bvi_ref_def; LUPDATE_MAP; map_replicate; MAP_TAKE;
                       MAP_DROP; MAP_APPEND; MAP]);;
let DATAPAUX_B2D_PRE_TAC =
  REWRITE_TAC[distinctness "clos_op"; injectivity "clos_op"; distinctness "int_op";
              distinctness "block_op"; distinctness "glob_op"; distinctness "mem_op";
              distinctness "thunk_op"; injectivity "mem_op";
              MESON[] `(!b:bool. ~(c = b)) <=> F`] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  REPEAT (DISCH_THEN(fun th -> if is_neg (concl th) then ASSUME_TAC th else failwith "")) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[bvi_to_dataProof_state_rel_def; lookup_map]) THEN
  SUBGOAL_THEN `domain (bvi_state_code (r:(C,FFI)bvi_state)) =
                domain (data_state_code (t:(C,FFI)data_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[bvi_to_dataProof_code_rel_def]; ALL_TAC] THEN
  SUBGOAL_THEN `!v1 v2. bvl_do_eq (bvi_state_refs (r:(C,FFI)bvi_state))
                          (data_to_bvi_v v1) (data_to_bvi_v v2) =
                        data_do_eq (data_state_refs (t:(C,FFI)data_state)) v1 v2`
    ASSUME_TAC THENL [ASM_MESON_TAC[DATAPAUX_B2D_do_eq_rw]; ALL_TAC] THEN
  SUBGOAL_THEN `!m v. bvl_bad_thunk_update m (data_to_bvi_v v)
                        (bvi_state_refs (r:(C,FFI)bvi_state)) <=>
                      data_bad_thunk_update m v (data_state_refs (t:(C,FFI)data_state))`
    ASSUME_TAC THENL [ASM_MESON_TAC[DATAPAUX_B2D_bad_thunk]; ALL_TAC] THEN
  SUBGOAL_THEN `(minimal ptr. ~(ptr IN FDOM (bvi_state_refs (r:(C,FFI)bvi_state)))) =
                (minimal ptr. ~(ptr IN domain (data_state_refs (t:(C,FFI)data_state))))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC refs_rel_LEAST_eq THEN ASM_REWRITE_TAC[lookup_map]; ALL_TAC] THEN
  REWRITE_TAC[bvi_do_app_def; bvi_do_app_aux_def; bvl_do_app_def; data_do_app_aux_def;
              distinctness "clos_op"] THEN
  CASE_REWRITE_TAC[distinctness "clos_op"] THEN
  ASM_SIMP_TAC[DATAPAUX_B2D_int_app; DATAPAUX_B2D_word_app; distinctness "int_op"];;
let DATAPAUX_B2D_NORM_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                   else failwith "")) THEN
  GVS (data_do_int_app_def :: DATAPAUX_B2D_RWS);;
let DATAPAUX_B2D_SUBOP_TAC : tactic = fun (asl,w as g) ->
  let v = find_term (fun t -> is_var t &&
            mem (type_of t) [`:int_op`; `:block_op`; `:glob_op`; `:mem_op`; `:thunk_op`]) w in
  CASES_ON v g;;

(* local helper: data_to_bvi_do_app for Build (do_build_thm) *)
let DATAPAUX_B2D_do_app_Build = prove
 (`!parts t r z res s1.
     bvi_to_dataProof_state_rel (r:(C,FFI)bvi_state) (t:(C,FFI)data_state) /\
     bvi_do_app (BlockOp (Build parts)) (MAP data_to_bvi_v z) r = Rval (res,s1)
     ==> ?s2 pres.
           data_do_app_aux (BlockOp (Build parts)) z t = Rval (pres,s2) /\
           res = data_to_bvi_v pres /\
           bvi_to_dataProof_state_rel s1 s2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_do_app_def; bvi_do_app_aux_def; bvl_do_app_def; data_do_app_aux_def;
              distinctness "clos_op"] THEN
  CASE_REWRITE_TAC[distinctness "clos_op"] THEN
  CASES_ON `z:data_v list` THEN REWRITE_TAC[MAP] THEN
  CASE_REWRITE_TAC[distinctness "result"] THEN
  REWRITE_TAC[bvl_do_build_const_def; data_do_build_const_def; bvi_bvi_to_bvl_refs] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPEC `bvl_do_build (\x:num. bvl_Number (&0)) 0 parts
                  (bvi_state_refs (r:(C,FFI)bvi_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:bvl_v` (X_CHOOSE_THEN `rs:(num,(bvl_v)bvl_ref)fmap`
    ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`parts:const_part list`; `\x:num. bvl_Number (&0)`;
                 `\x:num. data_Number (&0)`; `0`; `data_state_tstamps (t:(C,FFI)data_state)`;
                 `bvi_state_refs (r:(C,FFI)bvi_state)`; `data_state_refs (t:(C,FFI)data_state)`;
                 `q:bvl_v`; `rs:(num,(bvl_v)bvl_ref)fmap`] do_build_thm) THEN
  ASSUME_TAC(REWRITE_RULE[bvi_to_dataProof_state_rel_def; lookup_map]
    (ASSUME `bvi_to_dataProof_state_rel (r:(C,FFI)bvi_state) (t:(C,FFI)data_state)`)) THEN
  ASM_REWRITE_TAC[data_to_bvi_v_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `pres:data_v` (X_CHOOSE_THEN `s2:((data_v)bvl_ref)spt`
    (X_CHOOSE_THEN `ts1:num option` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REPEAT DATAPAUX_EXISTS_EQ_TAC THEN
  REWRITE_TAC[bvl_to_bvi_with_refs; bvl_to_bvi_id] THEN
  REWRITE_TAC[bvi_to_dataProof_state_rel_def; bvi_state_INFO.ri_accfupds;
              data_state_INFO.ri_accfupds; K_THM; lookup_map] THEN
  ASM_REWRITE_TAC[]);;

(* local helper: data_to_bvi_do_app for FinaliseCons *)
let DATAPAUX_B2D_do_app_FinaliseCons = prove
 (`!t r z res s1.
     bvi_to_dataProof_state_rel (r:(C,FFI)bvi_state) (t:(C,FFI)data_state) /\
     bvi_do_app (MemOp FinaliseCons) (MAP data_to_bvi_v z) r = Rval (res,s1)
     ==> ?s2 pres.
           data_do_app_aux (MemOp FinaliseCons) z t = Rval (pres,s2) /\
           res = data_to_bvi_v pres /\
           bvi_to_dataProof_state_rel s1 s2`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[bvi_do_app_def; bvi_do_app_aux_def; bvl_do_app_def; data_do_app_aux_def;
              distinctness "clos_op"] THEN
  CASE_REWRITE_TAC[distinctness "clos_op"] THEN
  CASES_ON `z:data_v list` THEN REWRITE_TAC[MAP] THEN
  CASE_REWRITE_TAC[distinctness "result"] THEN
  CASES_ON `a1:data_v list` THEN REWRITE_TAC[MAP] THEN
  CASE_REWRITE_TAC[distinctness "result"] THEN
  MP_TAC(ISPEC `bvi_finalise_cons (data_to_bvi_v a0) (bvi_state_refs (r:(C,FFI)bvi_state))`
           (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN
      CASE_REWRITE_TAC[distinctness "result"])
    (X_CHOOSE_THEN `p:bvl_v#(num,(bvl_v)bvl_ref)fmap` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `p:bvl_v#(num,(bvl_v)bvl_ref)fmap` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `bv:bvl_v` (X_CHOOSE_THEN `brefs:(num,(bvl_v)bvl_ref)fmap`
    SUBST_ALL_TAC)) THEN
  MP_TAC(ISPECL [`a0:data_v`; `data_state_refs (t:(C,FFI)data_state)`;
                 `data_state_tstamps (t:(C,FFI)data_state)`;
                 `bvi_state_refs (r:(C,FFI)bvi_state)`; `bv:bvl_v`;
                 `brefs:(num,(bvl_v)bvl_ref)fmap`] data_to_bvi_finalise_cons) THEN
  ASSUME_TAC(REWRITE_RULE[bvi_to_dataProof_state_rel_def; lookup_map]
    (ASSUME `bvi_to_dataProof_state_rel (r:(C,FFI)bvi_state) (t:(C,FFI)data_state)`)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `pv:data_v` (X_CHOOSE_THEN `refs1:((data_v)bvl_ref)spt`
    (X_CHOOSE_THEN `ts1:num option` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REPEAT DATAPAUX_EXISTS_EQ_TAC THEN
  REWRITE_TAC[bvi_to_dataProof_state_rel_def; bvi_state_INFO.ri_accfupds;
              data_state_INFO.ri_accfupds; K_THM; lookup_map] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 532 *)
let data_to_bvi_do_app = prove
 (`!op t r z res s1.
     ~(op = clos_Install) /\
     ~(op = IntOp Greater) /\
     ~(op = IntOp GreaterEq) /\
     ~(op = WordOp (WordTest W8 (Compare Gt))) /\
     ~(op = WordOp (WordTest W8 (Compare Geq))) /\
     (!b. ~(op = MemOp (CopyByte b))) /\
     ~(op = clos_ThunkOp ForceThunk) /\
     bvi_to_dataProof_state_rel (r:(C,FFI)bvi_state) (t:(C,FFI)data_state) /\
     bvi_do_app op (MAP data_to_bvi_v z) r = Rval (res,s1)
     ==> ?s2 pres.
           data_do_app_aux op z t = Rval (pres,s2) /\
           res = data_to_bvi_v pres /\
           bvi_to_dataProof_state_rel s1 s2`,
  GEN_TAC THEN CASES_ON `op:clos_op` THEN TRY DATAPAUX_B2D_SUBOP_TAC THEN
  FIRST
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DATAPAUX_B2D_do_app_Build THEN
    EXISTS_TAC `r:(C,FFI)bvi_state` THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC DATAPAUX_B2D_do_app_FinaliseCons THEN
    EXISTS_TAC `r:(C,FFI)bvi_state` THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    DATAPAUX_B2D_PRE_TAC THEN REPEAT DATAPAUX_B2D_STEP2_TAC THEN
    TRY DATAPAUX_B2D_NORM_TAC THEN TRY DATAPAUX_B2D_LEAF_TAC THEN
    TRY DATAPAUX_B2D_CLOSE_TAC THEN NO_TAC]);;

(* HOL4 line 687 *)
let state_rel_peak_safe = prove
 (`!s s' safe peak ls smx.
     bvi_to_dataProof_state_rel (s:(C,FFI)bvi_state) (s':(C,FFI)data_state) =
     bvi_to_dataProof_state_rel s
       (data_state_locals_size_fupd (K ls)
          (data_state_safe_for_space_fupd (K safe)
             (data_state_peak_heap_length_fupd (K peak)
                (data_state_stack_max_fupd (K smx) s'))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_to_dataProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 line 698 *)
let jump_exc_peak_safe = prove
 (`!s t safe peak ls smx.
     data_jump_exc (s:(C,FFI)data_state) = SOME t
     ==> data_jump_exc
           (data_state_safe_for_space_fupd (K safe)
              (data_state_peak_heap_length_fupd (K peak)
                 (data_state_locals_size_fupd (K ls)
                    (data_state_stack_max_fupd (K smx) s)))) =
         SOME (data_state_safe_for_space_fupd (K safe)
                 (data_state_peak_heap_length_fupd (K peak)
                    (data_state_stack_max_fupd (K smx) t)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_jump_exc_def; data_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 line 712 *)
let jump_exc_sfs_lss_peak_safe = prove
 (`!s t safe peak ls sfs smx.
     data_jump_exc (s:(C,FFI)data_state) = SOME t
     ==> data_jump_exc
           (data_state_safe_for_space_fupd (K safe)
              (data_state_peak_heap_length_fupd (K peak)
                 (data_state_locals_size_fupd (K ls)
                    (data_state_stack_frame_sizes_fupd (K sfs)
                       (data_state_stack_max_fupd (K smx) s))))) =
         SOME (data_state_safe_for_space_fupd (K safe)
                 (data_state_peak_heap_length_fupd (K peak)
                    (data_state_stack_frame_sizes_fupd (K sfs)
                       (data_state_stack_max_fupd (K smx) t))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_jump_exc_def; data_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 line 728 *)
let jump_exc_lss = prove
 (`!s t ls. data_jump_exc (s:(C,FFI)data_state) = SOME t
            ==> data_jump_exc (data_state_locals_size_fupd (K ls) s) = SOME t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_jump_exc_def; data_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 line 736 *)
let state_rel_dest_thunk = prove
 (`!s t z ev v.
     bvi_to_dataProof_state_rel (s:(C,FFI)bvi_state) (t:(C,FFI)data_state) /\
     bvi_dest_thunk (data_to_bvi_v z) (bvi_state_refs s) = bvi_IsThunk ev v
     ==> ?v'. data_dest_thunk z (data_state_refs t) = data_IsThunk ev v' /\
              data_to_bvi_v v' = v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_to_dataProof_state_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  CASES_ON `z:data_v` THEN
  REWRITE_TAC[data_to_bvi_v_def; bvi_dest_thunk_def; data_dest_thunk_def;
              distinctness "bvi_dest_thunk_ret"] THEN
  ASM_REWRITE_TAC[lookup_map] THEN
  CASES_ON `lookup a1 (data_state_refs (t:(C,FFI)data_state))` THEN
  REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[distinctness "bvi_dest_thunk_ret"] THEN
  CASES_ON `a:(data_v)bvl_ref` THEN REWRITE_TAC[data_to_bvi_ref_def] THEN
  CASE_REWRITE_TAC[distinctness "bvi_dest_thunk_ret"] THEN
  CASES_ON `a0':thunk_mode` THEN CASE_REWRITE_TAC[distinctness "bvi_dest_thunk_ret"] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "bvi_dest_thunk_ret"; injectivity "bvi_dest_thunk_ret";
              distinctness "data_dest_thunk_ret"; injectivity "data_dest_thunk_ret"] THEN
  STRIP_TAC THEN REPEAT DATAPAUX_EXISTS_EQ_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 747 *)
let domain_list_insert2 = prove
 (`!xs t. domain (list_insert xs (t:1 spt)) = set_of_list xs UNION domain t`,
  REWRITE_TAC[EXTENSION; domain_list_insert; IN_UNION; IN_SET_OF_LIST]);;

(* HOL4 line 753 *)
let domain_list_to_num_set2 = prove
 (`!xs. domain (list_to_num_set xs) = set_of_list xs`,
  REWRITE_TAC[EXTENSION; domain_list_to_num_set; IN_SET_OF_LIST]);;

(* HOL4 line 759 *)
let list_insert_list_to_num_set = prove
 (`!xs ys zs.
     list_insert xs (list_to_num_set (APPEND (APPEND xs ys) zs)) =
     list_to_num_set (APPEND (APPEND xs ys) zs)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!xs (t:1 spt). sptree_wf t ==> sptree_wf (list_insert xs t)` ASSUME_TAC THENL
   [LIST_INDUCT_TAC THEN ASM_SIMP_TAC[list_insert_def; wf_insert]; ALL_TAC] THEN
  W(fun (asl,w) -> MP_TAC(ISPECL [lhs w; rhs w] num_set_domain_eq)) THEN
  ASM_SIMP_TAC[wf_list_to_num_set] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[domain_list_insert2; domain_list_to_num_set2; SET_OF_LIST_APPEND] THEN
  SET_TAC[]);;
let _ = cake_add_simps [list_insert_list_to_num_set];;

(* HOL4 line 777 *)
let state_rel_do_app_FFI_err = prove
 (`!i z r t x.
     bvi_to_dataProof_state_rel (r:(C,FFI)bvi_state) (t:(C,FFI)data_state) /\
     bvi_do_app (clos_FFI i) (MAP data_to_bvi_v z) r = Rerr (Rabort (Rffi_error x))
     ==> data_do_app (clos_FFI i) z t = Rerr (Rabort (Rffi_error x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[bvi_to_dataProof_state_rel_def; lookup_map]) THEN
  REWRITE_TAC[bvi_do_app_def; bvi_do_app_aux_def; bvl_do_app_def; data_do_app_def;
              data_do_app_aux_def; do_space_def; op_space_reset_def; op_space_req_def;
              do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF; distinctness "clos_op"; MEM] THEN
  CASE_REWRITE_TAC[distinctness "clos_op"] THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT DATAPAUX_B2D_STEP_TAC
);;

(* HOL4 line 805 *)
let evaluate_Return_GENLIST_Var = prove
 (`!rets ret_vs env s'.
     LENGTH ret_vs = rets
     ==> bvi_evaluate ([bvi_Return (list_of_seq bvi_Var rets)],APPEND ret_vs env,
                       (s':(C,FFI)bvi_state)) =
         (Rerr (Rraise (Ret ret_vs)),s')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvi_evaluate_def] THEN
  MP_TAC(ISPECL [`0`; `APPEND (ret_vs:bvl_v list) env`; `rets:num`;
                 `s':(C,FFI)bvi_state`] bvi_evaluate_genlist_vars) THEN
  REWRITE_TAC[ADD_CLAUSES; ETA_AX; DROP_0; LENGTH_APPEND] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[TAKE_LENGTH_APPEND] THEN
  CASE_REWRITE_TAC[]);;

(* HOL4 line 817: fun note_tac (a tactic) *)

(* local tactic: for a goal ?x1 ... xn. body where body has a conjunct     *)
(* t = xi or xi = t (t free of x1 ... xn) for some i, move xi to the front *)
(* and supply t as its witness                                              *)
let DATAPAUX_EXISTS_PERMUTE_CONV (vs:term list) (tm:term) : thm =
  let xs,bod = strip_exists tm in
  let tm' = list_mk_exists(vs,bod) in
  let dir a b = prove(mk_imp(a,b),
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC (fst(strip_exists b)) THEN FIRST_ASSUM ACCEPT_TAC) in
  IMP_ANTISYM_RULE (dir tm tm') (dir tm' tm);;

let DATAPAUX_EXISTS_EQ_ANY_TAC : tactic = fun (asl,w as g) ->
  let xs,bod = strip_exists w in
  let rec conjs t = if is_conj t then conjs (lhand t) @ conjs (rand t) else [t] in
  let ok t = not (exists (fun v -> free_in v t) xs) in
  let pick c =
    if is_eq c then
      let l,r = dest_eq c in
      if mem r xs && ok l then (r,l) else if mem l xs && ok r then (l,r)
      else failwith "pick"
    else failwith "pick" in
  let x,t = tryfind pick (conjs bod) in
  (CONV_TAC (DATAPAUX_EXISTS_PERMUTE_CONV (x :: filter ((<>) x) xs)) THEN
   EXISTS_TAC t) g;;

(* local helpers for compile_correct *)
let DATAPAUX_B2D_var_corr_EL = prove
 (`!env corr (t:A spt) n.
     var_corr env corr t /\ n < LENGTH env
     ==> n < LENGTH corr /\ data_get_var (EL n corr) t = SOME (EL n env)`,
  REWRITE_TAC[var_corr_def; LIST_REL_EL_EQN] THEN MESON_TAC[]);;

let DATAPAUX_B2D_state_rel_fupds = prove
 (`!(s:(C,FFI)bvi_state) (t:(C,FFI)data_state) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 b.
     (bvi_to_dataProof_state_rel s (data_state_locals_fupd (K x1) t) <=>
      bvi_to_dataProof_state_rel s t) /\
     (bvi_to_dataProof_state_rel s (data_state_locals_size_fupd (K x2) t) <=>
      bvi_to_dataProof_state_rel s t) /\
     (bvi_to_dataProof_state_rel s (data_state_stack_fupd (K x3) t) <=>
      bvi_to_dataProof_state_rel s t) /\
     (bvi_to_dataProof_state_rel s (data_state_stack_max_fupd (K x4) t) <=>
      bvi_to_dataProof_state_rel s t) /\
     (bvi_to_dataProof_state_rel s (data_state_stack_frame_sizes_fupd (K x5) t) <=>
      bvi_to_dataProof_state_rel s t) /\
     (bvi_to_dataProof_state_rel s (data_state_handler_fupd (K x6) t) <=>
      bvi_to_dataProof_state_rel s t) /\
     (bvi_to_dataProof_state_rel s (data_state_space_fupd (K x7) t) <=>
      bvi_to_dataProof_state_rel s t) /\
     (bvi_to_dataProof_state_rel s (data_state_tstamps_fupd (K x8) t) <=>
      bvi_to_dataProof_state_rel s t) /\
     (bvi_to_dataProof_state_rel s (data_state_limits_fupd (K x9) t) <=>
      bvi_to_dataProof_state_rel s t) /\
     (bvi_to_dataProof_state_rel s (data_state_safe_for_space_fupd (K x10) t) <=>
      bvi_to_dataProof_state_rel s t) /\
     (bvi_to_dataProof_state_rel s (data_state_peak_heap_length_fupd (K x11) t) <=>
      bvi_to_dataProof_state_rel s t) /\
     (bvi_to_dataProof_state_rel s (data_flush_state b t) <=>
      bvi_to_dataProof_state_rel s t)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[bvi_to_dataProof_state_rel_def; data_flush_state_def;
              data_state_INFO.ri_accfupds; K_THM]);;

(* the statement of compile_correct and the instance of bviSem's          *)
(* evaluate_ind for it (conclusion !p. P p over triples (xs,env,s1)): its   *)
(* antecedent conjuncts are the cases of HOL4's recInduct proof (the        *)
(* Resume blocks NIL ... LetCall), proved below as separate theorems        *)
let DATAPAUX_B2D_CC_GOAL = CASE_TERM
  `!xs env (s1:(C,FFI)bvi_state) res s2 (t1:(C,FFI)data_state) n corr tail live.
     bvi_evaluate (xs,env,s1) = (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error)) /\
     var_corr env corr (sptree_map data_to_bvi_v (data_state_locals t1)) /\
     (~(LENGTH xs = 1) ==> ~tail) /\
     (!k. n <= k ==> lookup k (data_state_locals t1) = NONE) /\
     bvi_to_dataProof_state_rel s1 t1 /\
     ALL (\n. ~(lookup n (data_state_locals t1) = NONE)) live /\
     ((?v. res = Rerr (Rraise (Exn v))) ==> ~(data_jump_exc t1 = NONE))
     ==> ?t2 prog pres vs next_var ls.
           bvi_to_data_compile n corr tail live xs = (prog,vs,next_var) /\
           data_evaluate (prog,t1) = (pres,t2) /\
           bvi_to_dataProof_state_rel s2 t2 /\
           (match pres with
              SOME r ->
                ((~(?vs. res = Rerr (Rraise (Ret vs))) ==> data_to_bvi_result r = res) /\
                 ((?vs. res = Rerr (Rraise (Ret vs)))
                  ==> ?vs'. r = Rval vs' /\
                            res = Rerr (Rraise (Ret (MAP data_to_bvi_v vs')))) /\
                 (((?v. res = Rval v) \/ (?vs. res = Rerr (Rraise (Ret vs))))
                  ==> data_state_stack t1 = data_state_stack t2 /\
                      data_state_handler t1 = data_state_handler t2) /\
                 ((?v. res = Rval v) ==> tail) /\
                 ((?v. res = Rerr (Rraise (Exn v)))
                  ==> data_jump_exc
                        (data_state_stack_fupd (K (data_state_stack t1))
                           (data_state_handler_fupd (K (data_state_handler t1)) t2)) =
                      SOME (data_state_locals_size_fupd (K ls) t2)))
            | NONE ->
                ~tail /\ n <= next_var /\
                ALL (\v. v < next_var) vs /\
                (!k. next_var <= k ==> lookup k (data_state_locals t2) = NONE) /\
                var_corr env corr (sptree_map data_to_bvi_v (data_state_locals t2)) /\
                (!k x. lookup k (data_state_locals t2) = SOME x ==> k < next_var) /\
                (!k x. lookup k (data_state_locals t1) = SOME x /\
                       (~MEM k live ==> MEM k corr)
                       ==> lookup k (data_state_locals t2) = SOME x) /\
                data_state_stack t1 = data_state_stack t2 /\
                data_state_handler t1 = data_state_handler t2 /\
                (~(data_jump_exc t1 = NONE) ==> ~(data_jump_exc t2 = NONE)) /\
                (match res with
                   Rval xs -> var_corr xs vs (sptree_map data_to_bvi_v (data_state_locals t2))
                 | _ -> F))`;;

let DATAPAUX_B2D_IND_INST3 (goal:term) (ind:thm) =
  let xs,b1 = dest_forall goal in
  let env,b2 = dest_forall b1 in
  let s,b = dest_forall b2 in
  let ty = mk_type("prod",[type_of xs; mk_type("prod",[type_of env; type_of s])]) in
  let p = mk_var("p",ty) in
  let fstp = mk_icomb(mk_const("FST",[]),p)
  and sndp = mk_icomb(mk_const("SND",[]),p) in
  let fsndp = mk_icomb(mk_const("FST",[]),sndp)
  and ssndp = mk_icomb(mk_const("SND",[]),sndp) in
  let pred = mk_abs(p,vsubst [fstp,xs; fsndp,env; ssndp,s] b) in
  CONV_RULE (DEPTH_CONV BETA_CONV THENC REWRITE_CONV[FST; SND]) (ISPEC pred ind);;

let DATAPAUX_B2D_CC_IND = DATAPAUX_B2D_IND_INST3 DATAPAUX_B2D_CC_GOAL bvi_evaluate_ind;;
let DATAPAUX_B2D_CC_CASES = conjuncts (lhand (concl DATAPAUX_B2D_CC_IND));;

(* local helpers for the cases of compile_correct *)
let DATAPAUX_B2D_Seq_SOME = prove
 (`!c1 c2 (t:(C,FFI)data_state) r t2.
     data_evaluate (c1,t) = (SOME r,t2)
     ==> data_evaluate (data_Seq c1 c2,t) = (SOME r,t2)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[data_evaluate_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; option_DISTINCT] THEN CASE_REWRITE_TAC[option_DISTINCT]);;

(* rewrite data_evaluate (Seq c1 c2,t) with an assumption about c1 *)
let DATAPAUX_B2D_SEQ_NONE_TAC : tactic =
  FIRST_ASSUM(fun th -> CHANGED_TAC(PURE_REWRITE_TAC[MATCH_MP DSEMAUX_Seq_NONE th]));;
let DATAPAUX_B2D_SEQ_SOME_TAC : tactic =
  FIRST_ASSUM(fun th -> CHANGED_TAC(PURE_REWRITE_TAC[MATCH_MP DATAPAUX_B2D_Seq_SOME th]));;

(* destructure an existential theorem: a bound variable named a (or a',   *)
(* a'', ...) is renamed b if (a,b) is in names, and made fresh if needed    *)
let DATAPAUX_B2D_CHOOSE_TAC (names:(string*string) list) : thm_tactic =
  let rec go th (asl,w as g) =
    if is_exists (concl th) then
      let v = fst(dest_exists(concl th)) in
      let rec base s = let n = String.length s in
        if n > 1 && s.[n-1] = '\'' then base (String.sub s 0 (n-1)) else s in
      let nm = try assoc (base(fst(dest_var v))) names
               with Failure _ -> fst(dest_var v) in
      let avoid = itlist (union o thm_frees o snd) asl
                         (union (frees w) (thm_frees th)) in
      let v' = mk_primed_var avoid (mk_var(nm,type_of v)) in
      X_CHOOSE_THEN v' go th g
    else STRIP_ASSUME_TAC th g in
  go;;

let DATAPAUX_B2D_RES_RWS =
  [injectivity "result"; distinctness "result"; injectivity "error_result";
   distinctness "error_result"; injectivity "exn_or_ret"; distinctness "exn_or_ret";
   option_DISTINCT; option_INJ; EXISTS_REFL; MESON[] `!a:A. ?x. a = x`;
   MESON[] `!P (a:A). (?x. a = x /\ P x) <=> P a`; UNWIND_THM1; UNWIND_THM2];;

(* case split on a pres variable and simplify the assumptions *)
let DATAPAUX_B2D_PRES_TAC (pres:term) : tactic =
  CASES_ON pres THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE DATAPAUX_B2D_RES_RWS) THEN
  RULE_ASSUM_TAC(REWRITE_RULE DATAPAUX_B2D_RES_RWS) THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                   else failwith "")) THEN
  (fun g -> (FIRST_ASSUM CONTR_TAC ORELSE ALL_TAC) g);;


let DATAPAUX_B2D_jump_exc_restore = prove
 (`!(t2:(C,FFI)data_state) t3 st h.
     data_jump_exc t2 = SOME t3 /\ data_state_stack t2 = st /\ data_state_handler t2 = h
     ==> data_jump_exc (data_state_stack_fupd (K st) (data_state_handler_fupd (K h) t3)) =
         SOME (data_state_locals_size_fupd (K (data_state_locals_size t3)) t3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t2:(C,FFI)data_state`;
                 `data_state_stack_fupd (K st) (data_state_handler_fupd (K h) t3)
                    :(C,FFI)data_state`] DSEMAUX_jump_exc_cong) THEN
  ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP jump_exc_IMP) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

let DATAPAUX_B2D_state_rel_jump_exc = prove
 (`!(s:(C,FFI)bvi_state) (t:(C,FFI)data_state) t'.
     data_jump_exc t = SOME t'
     ==> (bvi_to_dataProof_state_rel s t' <=> bvi_to_dataProof_state_rel s t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP jump_exc_IMP) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[DATAPAUX_B2D_state_rel_fupds]);;

let DATAPAUX_B2D_Seq_Tick = prove
 (`!c (t:(C,FFI)data_state).
     data_evaluate (data_Seq data_Tick c,t) =
     if data_state_clock t = 0
     then (SOME (Rerr (Rabort Rtimeout_error)),data_flush_state T t)
     else data_evaluate (c,data_dec_clock t)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [data_evaluate_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; data_evaluate_def] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT]);;

let DATAPAUX_B2D_var_corr_insert = prove
 (`!env corr (t:data_v spt) m k z.
     var_corr env corr (sptree_map data_to_bvi_v t) /\
     (!j x. lookup j t = SOME x ==> j < m) /\ m <= k
     ==> var_corr env corr (sptree_map data_to_bvi_v (insert k z t))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[var_corr_def; LIST_REL_EL_EQN; data_get_var_def; lookup_map; lookup_insert] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "el"))
    (CONJUNCTS_THEN2 (LABEL_TAC "bd") ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REMOVE_THEN "el" (MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `lookup (EL i corr) (t:data_v spt)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `y:data_v` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(EL i corr = (k:num))`
    (fun th -> REWRITE_TAC[th] THEN ASM_REWRITE_TAC[OPTION_MAP_DEF]) THEN
  REMOVE_THEN "bd" (MP_TAC o SPECL [`EL i (corr:num list)`; `y:data_v`]) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* local helper for compile_correct[If]: the NONE-branch facts after the  *)
(* Move n3 that follows a branch                                          *)
let DATAPAUX_B2D_IF_MOVE = prove
 (`!(t1:(C,FFI)data_state) (t2:(C,FFI)data_state) (t3:(C,FFI)data_state)
      n n1 nv n3 env corr live z2.
     (!k. n <= k ==> lookup k (data_state_locals t1) = NONE) /\
     n <= n1 /\ n1 <= nv /\ nv <= n3 /\
     (!k x. lookup k (data_state_locals t1) = SOME x /\ (~MEM k live ==> MEM k corr)
            ==> lookup k (data_state_locals t2) = SOME x) /\
     data_state_stack t1 = data_state_stack t2 /\
     data_state_handler t1 = data_state_handler t2 /\
     (~(data_jump_exc t1 = NONE) ==> ~(data_jump_exc t2 = NONE)) /\
     (!k. nv <= k ==> lookup k (data_state_locals t3) = NONE) /\
     var_corr env corr (sptree_map data_to_bvi_v (data_state_locals t3)) /\
     (!k x. lookup k (data_state_locals t3) = SOME x ==> k < nv) /\
     (!k x. lookup k (data_state_locals t2) = SOME x /\ (~MEM k live ==> MEM k corr)
            ==> lookup k (data_state_locals t3) = SOME x) /\
     data_state_stack t2 = data_state_stack t3 /\
     data_state_handler t2 = data_state_handler t3 /\
     (~(data_jump_exc t2 = NONE) ==> ~(data_jump_exc t3 = NONE))
     ==> n <= n3 + 1 /\
         ALL (\v. v < n3 + 1) [n3] /\
         (!k. n3 + 1 <= k
              ==> lookup k (data_state_locals (data_set_var n3 z2 t3)) = NONE) /\
         var_corr env corr
           (sptree_map data_to_bvi_v (data_state_locals (data_set_var n3 z2 t3))) /\
         (!k x. lookup k (data_state_locals (data_set_var n3 z2 t3)) = SOME x
                ==> k < n3 + 1) /\
         (!k x. lookup k (data_state_locals t1) = SOME x /\ (~MEM k live ==> MEM k corr)
                ==> lookup k (data_state_locals (data_set_var n3 z2 t3)) = SOME x) /\
         data_state_stack t1 = data_state_stack (data_set_var n3 z2 t3) /\
         data_state_handler t1 = data_state_handler (data_set_var n3 z2 t3) /\
         (~(data_jump_exc t1 = NONE) ==> ~(data_jump_exc (data_set_var n3 z2 t3) = NONE)) /\
         var_corr [data_to_bvi_v z2] [n3]
           (sptree_map data_to_bvi_v (data_state_locals (data_set_var n3 z2 t3)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `var_corr env corr
    (sptree_map data_to_bvi_v (data_state_locals (data_set_var n3 z2 (t3:(C,FFI)data_state))))`
    ASSUME_TAC THENL
   [REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM] THEN
    MATCH_MP_TAC DATAPAUX_B2D_var_corr_insert THEN EXISTS_TAC `nv:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM; jump_exc_NONE] THEN
  ASM_REWRITE_TAC[ALL; lookup_insert; var_corr_def; ALL2; data_get_var_def; lookup_map;
                  OPTION_MAP_DEF] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ARITH_TAC;
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REPEAT GEN_TAC THEN COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `n3 < (n:num)` MP_TAC THENL
       [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
        UNDISCH_TAC `!k. n <= k ==> lookup k (data_state_locals (t1:(C,FFI)data_state)) = NONE` THEN
        DISCH_THEN(MP_TAC o SPEC `n3:num`) THEN ASM_REWRITE_TAC[option_DISTINCT];
        ASM_ARITH_TAC];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let DATAPAUX_B2D_var_corr_APPEND = prove
 (`!a vs env corr (t:A spt).
     var_corr a vs t /\ var_corr env corr t
     ==> var_corr (APPEND a env) (APPEND vs corr) t`,
  REWRITE_TAC[var_corr_def] THEN MESON_TAC[LIST_REL_APPEND_suff]);;

let DATAPAUX_B2D_var_corr_APPEND_IMP = prove
 (`!a vs env corr (t:A spt).
     var_corr (APPEND a env) (APPEND vs corr) t /\ LENGTH a = LENGTH vs
     ==> var_corr env corr t`,
  REWRITE_TAC[var_corr_def] THEN MESON_TAC[LIST_REL_APPEND_IMP]);;

let DATAPAUX_B2D_var_corr_LENGTH = prove
 (`!a vs (t:A spt). var_corr a vs t ==> LENGTH a = LENGTH vs`,
  REWRITE_TAC[var_corr_def] THEN MESON_TAC[LIST_REL_LENGTH]);;

(* prove a goal ~(jump_exc t = NONE) ==> ~(jump_exc t' = NONE) from the    *)
(* assumptions of that form                                                *)
let DATAPAUX_B2D_JUMP_TAC : tactic = fun (asl,w as g) ->
  let is_je t = can (find_term (fun u -> is_const u && fst(dest_const u) = "data_jump_exc")) t in
  let ok th = let c = concl th in
    is_imp c && (let a,b = dest_imp c in is_neg a && is_neg b && is_je a && is_je b) in
  MESON_TAC (map snd (filter (fun (_,th) -> ok th) asl)) g;;

(* local copy of state_rel_dec_clock (HOL4 states it after compile_correct) *)
let DATAPAUX_B2D_state_rel_dec_clock = prove
 (`!s1 t1. bvi_to_dataProof_state_rel (s1:(C,FFI)bvi_state) (t1:(C,FFI)data_state)
           ==> bvi_to_dataProof_state_rel (bvi_dec_clock 1 s1) (data_dec_clock t1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_to_dataProof_state_rel_def; bvi_dec_clock_def; data_dec_clock_def;
              bvi_state_INFO.ri_accfupds; data_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* local tactic: for a goal ?x1 ... xn. body where a conjunct of body is   *)
(* l = r with r an instance pattern in x1 ... xn of l, supply the witnesses *)
(* found by matching r against l                                            *)
let DATAPAUX_EXISTS_MATCH_TAC : tactic = fun (asl,w as g) ->
  let xs,bod = strip_exists w in
  let rec conjs t = if is_conj t then conjs (lhand t) @ conjs (rand t) else [t] in
  let try_conj c =
    let l,r = dest_eq c in
    if not (exists (fun v -> free_in v r) xs) then failwith "no var" else
    let avoid = subtract (frees r) xs in
    let _,inst,_ = term_match avoid r l in
    if exists (fun (t,v) -> not (mem v xs)) inst then failwith "bad" else
    inst in
  let inst = tryfind try_conj (conjs bod) in
  let rec prefix l = match l with
      [] -> []
    | x::t -> (try let v = rev_assoc x inst in v :: prefix t with Failure _ -> []) in
  let wits = prefix xs in
  if wits = [] then failwith "DATAPAUX_EXISTS_MATCH_TAC" else
  MAP_EVERY EXISTS_TAC wits g;;

let DATAPAUX_B2D_do_app_frame = prove
 (`!op xs (s:(C,FFI)data_state).
     ~(op = clos_Install) /\ ~(op = IntOp Greater) /\ ~(op = IntOp GreaterEq) /\
     (op_space_reset op \/ op_space_req op (LENGTH xs) <= data_state_space s)
     ==> ?s'. data_do_app op xs s = data_do_app_aux op xs s' /\
              (!r:(C,FFI)bvi_state.
                 bvi_to_dataProof_state_rel r s' <=> bvi_to_dataProof_state_rel r s) /\
              data_state_locals s' = data_state_locals s /\
              data_state_stack s' = data_state_stack s /\
              data_state_handler s' = data_state_handler s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_do_app_def; MEM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_space_def; consume_space_def] THEN ASM_REWRITE_TAC[] THEN
  REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY (FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN ASM_ARITH_TAC) THEN
  CASE_REWRITE_TAC[] THEN DATAPAUX_EXISTS_MATCH_TAC THEN
  REWRITE_TAC[do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF;
              data_state_INFO.ri_accfupds; K_THM; DATAPAUX_B2D_state_rel_fupds]);;

let DATAPAUX_B2D_var_corr_transfer = prove
 (`!env corr (t:A spt) t'.
     var_corr env corr t /\ (!k. MEM k corr ==> lookup k t' = lookup k t)
     ==> var_corr env corr t'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[var_corr_def; LIST_REL_EL_EQN; data_get_var_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lookup (EL n corr) (t':A spt) = lookup (EL n corr) t` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[MEM_EL]; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

let DATAPAUX_B2D_get_vars_inter_names = prove
 (`!args (t:A spt) (names:B spt) zs.
     data_get_vars args t = SOME zs /\ set_of_list args SUBSET domain names
     ==> data_get_vars args (mk_wf (sptree_inter t names)) = SOME zs`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC EVERY_get_vars THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  REWRITE_TAC[lookup_mk_wf; lookup_inter_alt] THEN
  SUBGOAL_THEN `(a:num) IN domain (names:B spt)` (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `set_of_list args SUBSET domain (names:B spt)` THEN
  REWRITE_TAC[SUBSET; IN_SET_OF_LIST] THEN ASM_MESON_TAC[]);;

(* local helper for compile_correct[Op]: the NONE-branch facts after the  *)
(* assignment of n1 in a state t3 whose locals are a part of those of t2  *)
let DATAPAUX_B2D_OP_FACTS = prove
 (`!(t1:(C,FFI)data_state) (t2:(C,FFI)data_state) (t3:(C,FFI)data_state)
      n n1 env corr live pv.
     (!k. n <= k ==> lookup k (data_state_locals t1) = NONE) /\ n <= n1 /\
     (!k x. lookup k (data_state_locals t1) = SOME x /\ (~MEM k live ==> MEM k corr)
            ==> lookup k (data_state_locals t2) = SOME x) /\
     data_state_stack t1 = data_state_stack t2 /\
     data_state_handler t1 = data_state_handler t2 /\
     (~(data_jump_exc t1 = NONE) ==> ~(data_jump_exc t2 = NONE)) /\
     (!k. n1 <= k ==> lookup k (data_state_locals t2) = NONE) /\
     var_corr env corr (sptree_map data_to_bvi_v (data_state_locals t2)) /\
     (!k x. lookup k (data_state_locals t3) = SOME x
            ==> lookup k (data_state_locals t2) = SOME x) /\
     (!k. MEM k live \/ MEM k corr
          ==> lookup k (data_state_locals t3) = lookup k (data_state_locals t2)) /\
     data_state_stack t3 = data_state_stack t2 /\
     data_state_handler t3 = data_state_handler t2
     ==> n <= n1 + 1 /\
         ALL (\v. v < n1 + 1) [n1] /\
         (!k. n1 + 1 <= k
              ==> lookup k (data_state_locals (data_set_var n1 pv t3)) = NONE) /\
         var_corr env corr
           (sptree_map data_to_bvi_v (data_state_locals (data_set_var n1 pv t3))) /\
         (!k x. lookup k (data_state_locals (data_set_var n1 pv t3)) = SOME x
                ==> k < n1 + 1) /\
         (!k x. lookup k (data_state_locals t1) = SOME x /\ (~MEM k live ==> MEM k corr)
                ==> lookup k (data_state_locals (data_set_var n1 pv t3)) = SOME x) /\
         data_state_stack t1 = data_state_stack (data_set_var n1 pv t3) /\
         data_state_handler t1 = data_state_handler (data_set_var n1 pv t3) /\
         (~(data_jump_exc t1 = NONE) ==> ~(data_jump_exc (data_set_var n1 pv t3) = NONE)) /\
         var_corr [data_to_bvi_v pv] [n1]
           (sptree_map data_to_bvi_v (data_state_locals (data_set_var n1 pv t3)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k x. lookup k (data_state_locals (t3:(C,FFI)data_state)) = SOME x ==> k < n1`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `!k. n1 <= k ==> lookup k (data_state_locals (t2:(C,FFI)data_state)) = NONE` THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `x:data_v`] o
      check (fun th -> can (find_term ((=) `t3:(C,FFI)data_state`)) (concl th) &&
                       is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[option_DISTINCT];
    ALL_TAC] THEN
  SUBGOAL_THEN `var_corr env corr
    (sptree_map data_to_bvi_v (data_state_locals (data_set_var n1 pv (t3:(C,FFI)data_state))))`
    ASSUME_TAC THENL
   [REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM] THEN
    MATCH_MP_TAC DATAPAUX_B2D_var_corr_insert THEN EXISTS_TAC `n1:num` THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    MATCH_MP_TAC DATAPAUX_B2D_var_corr_transfer THEN
    EXISTS_TAC `sptree_map data_to_bvi_v (data_state_locals (t2:(C,FFI)data_state))` THEN
    ASM_SIMP_TAC[lookup_map];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM; jump_exc_NONE] THEN
  ASM_REWRITE_TAC[ALL; lookup_insert; var_corr_def; ALL2; data_get_var_def; lookup_map;
                  OPTION_MAP_DEF] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ARITH_TAC;
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `lookup k (data_state_locals (t3:(C,FFI)data_state))` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `a:data_v`] o
      check (fun th -> can (find_term ((=) `n1:num`)) (concl th) && is_forall (concl th) &&
                       can (find_term ((=) `t3:(C,FFI)data_state`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    REPEAT GEN_TAC THEN COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `x:data_v`] o
      check (fun th -> can (find_term ((=) `n1:num`)) (concl th) && is_forall (concl th) &&
                       can (find_term ((=) `t3:(C,FFI)data_state`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `k < (n:num)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
      UNDISCH_TAC `!k. n <= k ==> lookup k (data_state_locals (t1:(C,FFI)data_state)) = NONE` THEN
      DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[option_DISTINCT];
      ALL_TAC] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `lookup k (data_state_locals (t3:(C,FFI)data_state)) =
                  lookup k (data_state_locals (t2:(C,FFI)data_state))` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o
      check (fun th -> can (find_term ((=) `t1:(C,FFI)data_state`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`t2:(C,FFI)data_state`; `t3:(C,FFI)data_state`] DSEMAUX_jump_exc_cong) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[OPTION_MAP_EQ_NONE] THEN ASM_MESON_TAC[]]);;

let DATAPAUX_B2D_iAssign_Rval = prove
 (`!n1 op args live env (t2:(C,FFI)data_state) (r:(C,FFI)bvi_state) zs v r'.
     ~(op = clos_Install) /\ ~(op = IntOp Greater) /\ ~(op = IntOp GreaterEq) /\
     ~(op = WordOp (WordTest W8 (Compare Gt))) /\
     ~(op = WordOp (WordTest W8 (Compare Geq))) /\
     (!b. ~(op = MemOp (CopyByte b))) /\ ~(op = clos_ThunkOp ForceThunk) /\
     bvi_to_dataProof_state_rel r t2 /\
     data_get_vars args (data_state_locals t2) = SOME zs /\
     domain (list_to_num_set (APPEND (APPEND args live) env)) SUBSET
       domain (data_state_locals t2) /\
     bvi_do_app op (MAP data_to_bvi_v zs) r = Rval (v,r')
     ==> ?pv t3. data_evaluate (iAssign n1 op args live env,t2) =
                   (NONE,data_set_var n1 pv t3) /\
                 v = data_to_bvi_v pv /\ bvi_to_dataProof_state_rel r' t3 /\
                 (data_state_locals t3 = data_state_locals t2 \/
                  data_state_locals t3 =
                    mk_wf (sptree_inter (data_state_locals t2)
                                 (list_to_num_set (APPEND (APPEND args live) env)))) /\
                 data_state_stack t3 = data_state_stack t2 /\
                 data_state_handler t3 = data_state_handler t2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP data_spaceProof_get_vars_IMP_LENGTH) THEN
  REWRITE_TAC[iAssign_def; LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `nms = list_to_num_set (APPEND (APPEND args live) env)` THEN
  SUBGOAL_THEN `set_of_list args SUBSET domain (nms:num_set)` ASSUME_TAC THENL
   [EXPAND_TAC "nms" THEN
    REWRITE_TAC[domain_list_to_num_set2; SET_OF_LIST_APPEND] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `data_get_vars args (mk_wf (sptree_inter (data_state_locals (t2:(C,FFI)data_state))
                  (nms:num_set))) = SOME zs` ASSUME_TAC THENL
   [MATCH_MP_TAC DATAPAUX_B2D_get_vars_inter_names THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  let finish_tac =
    DISCH_THEN(X_CHOOSE_THEN `s1:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`op:clos_op`; `s1:(C,FFI)data_state`; `r:(C,FFI)bvi_state`;
                   `zs:data_v list`; `v:bvl_v`; `r':(C,FFI)bvi_state`] data_to_bvi_do_app) THEN
    ASM_REWRITE_TAC[DATAPAUX_B2D_state_rel_fupds; add_space_def] THEN
    DISCH_THEN(X_CHOOSE_THEN `s3:(C,FFI)data_state` (X_CHOOSE_THEN `pres:data_v`
      STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP data_do_app_aux_const) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_MATCH_TAC THEN
    ASM_REWRITE_TAC[install_sfs_def; DATAPAUX_B2D_state_rel_fupds;
                    data_state_INFO.ri_accfupds; K_THM; add_space_def] in
  COND_CASES_TAC THENL
   [REWRITE_TAC[data_evaluate_def; IS_NONE_DEF; data_cut_state_opt_def; data_cut_state_def;
                data_cut_env_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`op:clos_op`; `zs:data_v list`;
      `data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals t2) (nms:num_set))))
         (t2:(C,FFI)data_state)`] DATAPAUX_B2D_do_app_frame) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `op_requires_names op` THEN REWRITE_TAC[op_requires_names_def] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[op_space_req_def; LE_0] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    finish_tac;
    COND_CASES_TAC THENL
     [REWRITE_TAC[data_evaluate_def; IS_NONE_DEF; data_cut_state_opt_def] THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`op:clos_op`; `zs:data_v list`; `t2:(C,FFI)data_state`]
                    DATAPAUX_B2D_do_app_frame) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[LE_0]; ALL_TAC] THEN
      finish_tac;
      REWRITE_TAC[data_evaluate_def; IS_NONE_DEF; data_cut_state_opt_def; data_cut_env_def;
                  LET_DEF; LET_END_DEF] THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
      REWRITE_TAC[add_space_def; data_state_INFO.ri_accfupds; K_THM] THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      W(fun (asl,w) ->
        let t = find_term (fun t -> is_comb t &&
                  (try fst(dest_const(fst(strip_comb t))) = "data_do_app" with _ -> false)) w in
        MP_TAC(ISPECL [`op:clos_op`; `zs:data_v list`; rand t] DATAPAUX_B2D_do_app_frame)) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; LE_REFL]; ALL_TAC] THEN
      finish_tac]]);;

let DATAPAUX_B2D_iAssign_Rerr = prove
 (`!n1 op args live env (t2:(C,FFI)data_state) (r:(C,FFI)bvi_state) zs e.
     bvi_to_dataProof_state_rel r t2 /\
     data_get_vars args (data_state_locals t2) = SOME zs /\
     domain (list_to_num_set (APPEND (APPEND args live) env)) SUBSET
       domain (data_state_locals t2) /\
     bvi_do_app op (MAP data_to_bvi_v zs) r = Rerr e /\ ~(e = Rabort Rtype_error)
     ==> ?x t3. e = Rabort (Rffi_error x) /\
                data_evaluate (iAssign n1 op args live env,t2) =
                  (SOME (Rerr (Rabort (Rffi_error x))),t3) /\
                bvi_to_dataProof_state_rel r t3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP bvi_do_app_err) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:mlstring` (X_CHOOSE_THEN `x:final_event`
    STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN EXISTS_TAC `x:final_event` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[iAssign_def; LET_DEF; LET_END_DEF; op_requires_names_def;
              distinctness "clos_op"; injectivity "clos_op"] THEN
  REWRITE_TAC[MESON[] `!a:A. ?x. a = x`] THEN
  REWRITE_TAC[data_evaluate_def; IS_NONE_DEF; data_cut_state_opt_def; data_cut_state_def;
              data_cut_env_def; op_requires_names_def; distinctness "clos_op";
              injectivity "clos_op"; MESON[] `!a:A. ?x. a = x`] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`i:mlstring`; `zs:data_v list`; `r:(C,FFI)bvi_state`;
    `data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals t2)
       (list_to_num_set (APPEND (APPEND args live) env))))) (t2:(C,FFI)data_state)`;
    `x:final_event`] state_rel_do_app_FFI_err) THEN
  ASM_REWRITE_TAC[DATAPAUX_B2D_state_rel_fupds] THEN DISCH_THEN SUBST1_TAC THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  DATAPAUX_EXISTS_EQ_ANY_TAC THEN
  REWRITE_TAC[install_sfs_def; DATAPAUX_B2D_state_rel_fupds] THEN ASM_REWRITE_TAC[]);;

let DATAPAUX_B2D_cut_facts = prove
 (`!(t3:(C,FFI)data_state) (t2:(C,FFI)data_state) args live env.
     (data_state_locals t3 = data_state_locals t2 \/
      data_state_locals t3 =
        mk_wf (sptree_inter (data_state_locals t2)
                     (list_to_num_set (APPEND (APPEND args live) env))))
     ==> (!k x. lookup k (data_state_locals t3) = SOME x
                ==> lookup k (data_state_locals t2) = SOME x) /\
         (!k. MEM k live \/ MEM k env
              ==> lookup k (data_state_locals t3) = lookup k (data_state_locals t2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[lookup_mk_wf; lookup_inter_alt; domain_list_to_num_set; MEM_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT]);;

let DATAPAUX_B2D_int_app_len = prove
 (`!op (l:bvl_v list).
     (op = Greater \/ op = GreaterEq \/ op = clos_Less \/ op = LessEq) /\ ~(LENGTH l = 2)
     ==> bvl_do_int_app op l = NONE`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) MP_TAC) THEN
  CASES_ON `l:bvl_v list` THEN REWRITE_TAC[LENGTH; bvl_do_int_app_def] THEN
  CASES_ON `a1:bvl_v list` THEN REWRITE_TAC[LENGTH; bvl_do_int_app_def] THEN
  CASES_ON `a0:bvl_v` THEN REWRITE_TAC[bvl_do_int_app_def] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC (SUC n) = 2) <=> ~(n = 0)`; LENGTH_EQ_NIL] THEN
  CASES_ON `a1':bvl_v list` THEN REWRITE_TAC[] THEN
  CASES_ON `a0':bvl_v` THEN REWRITE_TAC[bvl_do_int_app_def]);;

let DATAPAUX_B2D_int_swap = prove
 (`!vs. bvl_do_int_app Greater vs = bvl_do_int_app clos_Less (REVERSE vs) /\
        bvl_do_int_app GreaterEq vs = bvl_do_int_app LessEq (REVERSE vs)`,
  GEN_TAC THEN ASM_CASES_TAC `LENGTH (vs:bvl_v list) = 2` THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[LENGTH_EQ_CONS; ONE; TWO; LENGTH_EQ_NIL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[REVERSE; APPEND] THEN
    CASES_ON `h:bvl_v` THEN CASES_ON `h':bvl_v` THEN
    REWRITE_TAC[bvl_do_int_app_def; INT_GT; INT_GE];
    ASM_SIMP_TAC[DATAPAUX_B2D_int_app_len; LENGTH_REVERSE]]);;

let DATAPAUX_B2D_word_app_len = prove
 (`!op (l:bvl_v list).
     (op = WordTest W8 (Compare Gt) \/ op = WordTest W8 (Compare Geq) \/
      op = WordTest W8 (Compare Lt) \/ op = WordTest W8 (Compare Leq)) /\ ~(LENGTH l = 2)
     ==> bvl_do_word_app op l = NONE`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) MP_TAC) THEN
  CASES_ON `l:bvl_v list` THEN REWRITE_TAC[LENGTH; bvl_do_word_app_def] THEN
  CASES_ON `a1:bvl_v list` THEN REWRITE_TAC[LENGTH; bvl_do_word_app_def] THEN
  CASES_ON `a0:bvl_v` THEN REWRITE_TAC[bvl_do_word_app_def] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC (SUC n) = 2) <=> ~(n = 0)`; LENGTH_EQ_NIL] THEN
  CASES_ON `a1':bvl_v list` THEN REWRITE_TAC[] THEN
  CASES_ON `a0':bvl_v` THEN REWRITE_TAC[bvl_do_word_app_def]);;

let DATAPAUX_B2D_word_swap = prove
 (`!vs. bvl_do_word_app (WordTest W8 (Compare Gt)) vs =
        bvl_do_word_app (WordTest W8 (Compare Lt)) (REVERSE vs) /\
        bvl_do_word_app (WordTest W8 (Compare Geq)) vs =
        bvl_do_word_app (WordTest W8 (Compare Leq)) (REVERSE vs)`,
  GEN_TAC THEN ASM_CASES_TAC `LENGTH (vs:bvl_v list) = 2` THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[LENGTH_EQ_CONS; ONE; TWO; LENGTH_EQ_NIL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[REVERSE; APPEND] THEN
    CASES_ON `h:bvl_v` THEN CASES_ON `h':bvl_v` THEN
    REWRITE_TAC[bvl_do_word_app_def] THEN CASE_REWRITE_TAC[int_cmp_def] THEN
    REWRITE_TAC[INT_GT; INT_GE; CONJ_ACI];
    ASM_SIMP_TAC[DATAPAUX_B2D_word_app_len; LENGTH_REVERSE]]);;

let DATAPAUX_B2D_bvi_swap = prove
 (`!vs (r:(C,FFI)bvi_state).
     bvi_do_app (IntOp Greater) vs r = bvi_do_app (IntOp clos_Less) (REVERSE vs) r /\
     bvi_do_app (IntOp GreaterEq) vs r = bvi_do_app (IntOp LessEq) (REVERSE vs) r /\
     bvi_do_app (WordOp (WordTest W8 (Compare Gt))) vs r =
     bvi_do_app (WordOp (WordTest W8 (Compare Lt))) (REVERSE vs) r /\
     bvi_do_app (WordOp (WordTest W8 (Compare Geq))) vs r =
     bvi_do_app (WordOp (WordTest W8 (Compare Leq))) (REVERSE vs) r`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_do_app_def; bvi_do_app_aux_def; bvl_do_app_def; distinctness "clos_op"] THEN
  CASE_REWRITE_TAC[distinctness "clos_op"] THEN
  REWRITE_TAC[DATAPAUX_B2D_int_swap; DATAPAUX_B2D_word_swap]);;

let DATAPAUX_B2D_Assign_Rval = prove
 (`!n1 op args nopt (t2:(C,FFI)data_state) (r:(C,FFI)bvi_state) zs v r'.
     ~(op = clos_Install) /\ ~(op = IntOp Greater) /\ ~(op = IntOp GreaterEq) /\
     ~(op = WordOp (WordTest W8 (Compare Gt))) /\
     ~(op = WordOp (WordTest W8 (Compare Geq))) /\
     (!b. ~(op = MemOp (CopyByte b))) /\ ~(op = clos_ThunkOp ForceThunk) /\
     op_requires_names op = IS_SOME nopt /\
     (op_space_reset op \/ op_space_req op (LENGTH zs) = 0) /\
     (!nms. nopt = SOME nms ==> domain nms SUBSET domain (data_state_locals t2)) /\
     bvi_to_dataProof_state_rel r t2 /\
     data_get_vars args (data_state_locals t2) = SOME zs /\
     bvi_do_app op (MAP data_to_bvi_v zs) r = Rval (v,r')
     ==> ?pv t3. data_evaluate (data_Assign n1 op args nopt,t2) =
                   (NONE,data_set_var n1 pv t3) /\
                 v = data_to_bvi_v pv /\ bvi_to_dataProof_state_rel r' t3 /\
                 data_state_locals t3 =
                   option_CASE nopt (data_state_locals t2)
                     (\nms. mk_wf (sptree_inter (data_state_locals t2) nms)) /\
                 data_state_stack t3 = data_state_stack t2 /\
                 data_state_handler t3 = data_state_handler t2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let finish_tac =
    DISCH_THEN(X_CHOOSE_THEN `s1:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`op:clos_op`; `s1:(C,FFI)data_state`; `r:(C,FFI)bvi_state`;
                   `zs:data_v list`; `v:bvl_v`; `r':(C,FFI)bvi_state`] data_to_bvi_do_app) THEN
    ASM_REWRITE_TAC[DATAPAUX_B2D_state_rel_fupds] THEN
    DISCH_THEN(X_CHOOSE_THEN `s3:(C,FFI)data_state` (X_CHOOSE_THEN `pres:data_v`
      STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP data_do_app_aux_const) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_MATCH_TAC THEN
    ASM_REWRITE_TAC[install_sfs_def; DATAPAUX_B2D_state_rel_fupds; option_CASE;
                    data_state_INFO.ri_accfupds; K_THM] in
  MP_TAC(ISPEC `nopt:num_set option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `nms:num_set` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF; option_DISTINCT; option_INJ;
                              MESON[] `!a:A P. (!x. a = x ==> P x) <=> P a`]) THENL
   [REWRITE_TAC[data_evaluate_def; IS_NONE_DEF; data_cut_state_opt_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`op:clos_op`; `zs:data_v list`; `t2:(C,FFI)data_state`]
                  DATAPAUX_B2D_do_app_frame) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_0]; ALL_TAC] THEN
    finish_tac;
    REWRITE_TAC[data_evaluate_def; IS_NONE_DEF; data_cut_state_opt_def; data_cut_state_def;
                data_cut_env_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`op:clos_op`; `zs:data_v list`;
      `data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals t2) (nms:num_set))))
         (t2:(C,FFI)data_state)`] DATAPAUX_B2D_do_app_frame) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_0]; ALL_TAC] THEN
    finish_tac]);;

let DATAPAUX_B2D_iAssign_swap_Rval = prove
 (`!n1 op args live env (t2:(C,FFI)data_state) (r:(C,FFI)bvi_state) zs v r'.
     (op = IntOp Greater \/ op = IntOp GreaterEq \/
      op = WordOp (WordTest W8 (Compare Gt)) \/ op = WordOp (WordTest W8 (Compare Geq))) /\
     bvi_to_dataProof_state_rel r t2 /\
     data_get_vars args (data_state_locals t2) = SOME zs /\
     domain (list_to_num_set (APPEND (APPEND args live) env)) SUBSET
       domain (data_state_locals t2) /\
     bvi_do_app op (MAP data_to_bvi_v zs) r = Rval (v,r')
     ==> ?pv t3. data_evaluate (iAssign n1 op args live env,t2) =
                   (NONE,data_set_var n1 pv t3) /\
                 v = data_to_bvi_v pv /\ bvi_to_dataProof_state_rel r' t3 /\
                 (data_state_locals t3 = data_state_locals t2 \/
                  data_state_locals t3 =
                    mk_wf (sptree_inter (data_state_locals t2)
                                 (list_to_num_set (APPEND (APPEND args live) env)))) /\
                 data_state_stack t3 = data_state_stack t2 /\
                 data_state_handler t3 = data_state_handler t2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP get_vars_reverse) THEN
  REWRITE_TAC[iAssign_def; LET_DEF; LET_END_DEF; op_requires_names_def; op_space_reset_def;
              op_space_req_def; distinctness "clos_op"; injectivity "clos_op";
              distinctness "int_op"; distinctness "word_op"; injectivity "word_op"] THEN
  CASE_REWRITE_TAC[] THEN
  W(fun (asl,w) ->
     let t = find_term (fun t -> is_comb t &&
               (try fst(dest_const(fst(strip_comb t))) = "data_Assign" with _ -> false)) w in
     let _,args' = strip_comb t in
     let op' = el 1 args' and nopt = el 3 args' in
     MP_TAC(ISPECL [`n1:num`; op'; `REVERSE args:num list`; nopt; `t2:(C,FFI)data_state`;
                    `r:(C,FFI)bvi_state`; `REVERSE zs:data_v list`; `v:bvl_v`;
                    `r':(C,FFI)bvi_state`] DATAPAUX_B2D_Assign_Rval)) THEN
  ASM_REWRITE_TAC[GSYM MAP_REVERSE; GSYM DATAPAUX_B2D_bvi_swap; op_requires_names_def;
                  op_space_reset_def; op_space_req_def; distinctness "clos_op";
                  injectivity "clos_op"; distinctness "int_op"; distinctness "word_op";
                  injectivity "word_op"; IS_SOME_DEF; option_INJ; option_DISTINCT;
                  injectivity "test"; distinctness "opb";
                  MESON[] `!a:A P. (!x. a = x ==> P x) <=> P a`] THEN
  REWRITE_TAC[option_CASE] THEN
  DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN ASM_REWRITE_TAC[] THEN
  REPEAT DATAPAUX_EXISTS_MATCH_TAC THEN ASM_REWRITE_TAC[]);;

let DATAPAUX_B2D_ForceThunk_err = prove
 (`!vs (r:(C,FFI)bvi_state).
     bvi_do_app (clos_ThunkOp ForceThunk) vs r = Rerr (Rabort Rtype_error) /\
     bvi_do_app (MemOp (CopyByte T)) vs r = Rerr (Rabort Rtype_error)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_do_app_def; bvi_do_app_aux_def; bvl_do_app_def; distinctness "clos_op"] THEN
  CASE_REWRITE_TAC[distinctness "clos_op"] THEN
  REPEAT (DATAPAUX_B2D_SPLIT_TAC THEN CASE_REWRITE_TAC[]));;


let DATAPAUX_B2D_do_app_CopyByte = prove
 (`!t r z res s1.
     bvi_to_dataProof_state_rel (r:(C,FFI)bvi_state) (t:(C,FFI)data_state) /\
     bvi_do_app (MemOp (CopyByte F)) (MAP data_to_bvi_v z) r = Rval (res,s1)
     ==> ?s2 pres.
           data_do_app_aux (MemOp (CopyByte F)) z t = Rval (pres,s2) /\
           res = data_to_bvi_v pres /\
           bvi_to_dataProof_state_rel s1 s2`,
  DATAPAUX_B2D_PRE_TAC THEN DATAPAUX_CASE_CONST_TAC THEN REPEAT DATAPAUX_B2D_STEP2_TAC THEN
  TRY DATAPAUX_B2D_NORM_TAC THEN TRY DATAPAUX_B2D_LEAF_TAC THEN TRY DATAPAUX_B2D_CLOSE_TAC);;

let DATAPAUX_B2D_Assign_Rval_gen = prove
 (`!n1 op args nopt (t2:(C,FFI)data_state) (r:(C,FFI)bvi_state) zs v r'.
     ~(op = clos_Install) /\ ~(op = IntOp Greater) /\ ~(op = IntOp GreaterEq) /\
     (!t r z res s1.
        bvi_to_dataProof_state_rel (r:(C,FFI)bvi_state) (t:(C,FFI)data_state) /\
        bvi_do_app op (MAP data_to_bvi_v z) r = Rval (res,s1)
        ==> ?s2 pres. data_do_app_aux op z t = Rval (pres,s2) /\
                      res = data_to_bvi_v pres /\ bvi_to_dataProof_state_rel s1 s2) /\
     op_requires_names op = IS_SOME nopt /\
     (op_space_reset op \/ op_space_req op (LENGTH zs) = 0) /\
     (!nms. nopt = SOME nms ==> domain nms SUBSET domain (data_state_locals t2)) /\
     bvi_to_dataProof_state_rel r t2 /\
     data_get_vars args (data_state_locals t2) = SOME zs /\
     bvi_do_app op (MAP data_to_bvi_v zs) r = Rval (v,r')
     ==> ?pv t3. data_evaluate (data_Assign n1 op args nopt,t2) =
                   (NONE,data_set_var n1 pv t3) /\
                 v = data_to_bvi_v pv /\ bvi_to_dataProof_state_rel r' t3 /\
                 data_state_locals t3 =
                   option_CASE nopt (data_state_locals t2)
                     (\nms. mk_wf (sptree_inter (data_state_locals t2) nms)) /\
                 data_state_stack t3 = data_state_stack t2 /\
                 data_state_handler t3 = data_state_handler t2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let finish_tac =
    DISCH_THEN(X_CHOOSE_THEN `s1:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s1:(C,FFI)data_state`; `r:(C,FFI)bvi_state`;
                   `zs:data_v list`; `v:bvl_v`; `r':(C,FFI)bvi_state`] o
                   check (fun th -> is_forall (concl th) &&
                      can (find_term (fun t -> is_const t &&
                        fst(dest_const t) = "data_do_app_aux")) (concl th))) THEN
    ASM_REWRITE_TAC[DATAPAUX_B2D_state_rel_fupds] THEN
    DISCH_THEN(X_CHOOSE_THEN `s3:(C,FFI)data_state` (X_CHOOSE_THEN `pres:data_v`
      STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP data_do_app_aux_const) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_MATCH_TAC THEN
    ASM_REWRITE_TAC[install_sfs_def; DATAPAUX_B2D_state_rel_fupds; option_CASE;
                    data_state_INFO.ri_accfupds; K_THM] in
  MP_TAC(ISPEC `nopt:num_set option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `nms:num_set` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF; option_DISTINCT; option_INJ;
                              MESON[] `!a:A P. (!x. a = x ==> P x) <=> P a`]) THENL
   [REWRITE_TAC[data_evaluate_def; IS_NONE_DEF; data_cut_state_opt_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`op:clos_op`; `zs:data_v list`; `t2:(C,FFI)data_state`]
                  DATAPAUX_B2D_do_app_frame) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_0]; ALL_TAC] THEN
    finish_tac;
    REWRITE_TAC[data_evaluate_def; IS_NONE_DEF; data_cut_state_opt_def; data_cut_state_def;
                data_cut_env_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`op:clos_op`; `zs:data_v list`;
      `data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals t2) (nms:num_set))))
         (t2:(C,FFI)data_state)`] DATAPAUX_B2D_do_app_frame) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_0]; ALL_TAC] THEN
    finish_tac]);;

(* local copy of MAP_FST_compile_prog (HOL4 states it after compile_correct) *)
let DATAPAUX_B2D_MAP_FST_compile_prog = prove
 (`!prog. MAP FST (bvi_to_data_compile_prog prog) = MAP FST prog`,
  REWRITE_TAC[bvi_to_data_compile_prog_def; GSYM MAP_o] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; o_THM; CONS_11] THEN
  MP_TAC(ISPEC `h:num#num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `b:num#bvi_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `b:num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_THEN `d:bvi_exp` SUBST1_TAC)) THEN
  REWRITE_TAC[bvi_to_data_compile_part_def; FST]);;

let DATAPAUX_B2D_code_rel_union = prove
 (`!c1 c2 progs.
     bvi_to_dataProof_code_rel c1 c2
     ==> bvi_to_dataProof_code_rel (sptree_union c1 (fromAList progs))
           (sptree_union c2 (fromAList (bvi_to_data_compile_prog progs)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_to_dataProof_code_rel_def] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[wf_union; wf_fromAList; domain_union; domain_fromAList;
               DATAPAUX_B2D_MAP_FST_compile_prog] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_union; lookup_fromAList] THEN
  MP_TAC(ISPEC `lookup n (c1:(num#bvi_exp)spt)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:num#bvi_exp` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[option_CASE; option_INJ] THENL
   [SUBGOAL_THEN `lookup n (c2:(num#data_prog)spt) = NONE` SUBST1_TAC THENL
     [REWRITE_TAC[lookup_NONE_domain] THEN
      UNDISCH_TAC `domain (c1:(num#bvi_exp)spt) = domain (c2:(num#data_prog)spt)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[GSYM lookup_NONE_domain];
      ALL_TAC] THEN
    REWRITE_TAC[option_CASE; bvi_to_data_compile_prog_def; compile_part_thm; ALOOKUP_MAP;
                o_THM] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
    CONV_TAC(DEPTH_CONV(BETA_CONV ORELSEC GEN_BETA_CONV)) THEN REWRITE_TAC[];
    DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `exp:bvi_exp`; `arg_count:num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_CASE]]);;

let DATAPAUX_B2D_do_install = prove
 (`!zs (r:(C,FFI)bvi_state) (t:(C,FFI)data_state) v r'.
     bvi_to_dataProof_state_rel r t /\
     bvi_do_install (MAP data_to_bvi_v zs) r =
       (Rval (v,r'):(bvl_v # (C,FFI)bvi_state,exn_or_ret)result)
     ==> ?pv t'. data_do_install zs t =
                   (Rval (pv,t'):(data_v # (C,FFI)data_state,data_v)result) /\
                 v = data_to_bvi_v pv /\
                 bvi_to_dataProof_state_rel r' t' /\
                 data_state_locals t' = data_state_locals t /\
                 data_state_stack t' = data_state_stack t /\
                 data_state_handler t' = data_state_handler t`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bvi_to_dataProof_state_rel_def]) THEN
  REWRITE_TAC[bvi_do_install_def; data_do_install_def] THEN
  let rws = [MAP; data_to_bvi_v_def; bvi_to_dataProof_v_to_bytes_eq;
             bvi_to_dataProof_v_to_words_eq; data_to_bvi_eq_Number; LET_DEF; LET_END_DEF;
             PAIR_EQ; injectivity "result"; distinctness "result"; option_DISTINCT;
             option_INJ; o_THM; PAIR_MAP_THM; FST_PAIR_MAP; SND_PAIR_MAP; I_THM;
             shift_seq_def; bvi_to_data_compile_prog_def; compile_part_thm] in
  ASM_REWRITE_TAC rws THEN
  REPEAT (DATAPAUX_B2D_SPLIT2_TAC THEN ASM_REWRITE_TAC rws THEN CASE_REWRITE_TAC rws) THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
  REWRITE_TAC[data_to_bvi_v_def; bvi_to_dataProof_state_rel_def;
              bvi_state_INFO.ri_accfupds; data_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [W(fun (asl,w) ->
      let t = find_term (fun t -> is_comb t && is_comb (rator t) &&
                (try fst(dest_const(rator(rator t))) = "sptree_union" with _ -> false) &&
                (try fst(dest_const(fst(strip_comb(rand t)))) = "fromAList" with _ -> false) &&
                (try type_of t = `:(num#bvi_exp)spt` with _ -> false)) w in
      let progs = rand(rand t) in
      MP_TAC(ISPECL [`bvi_state_code (r:(C,FFI)bvi_state)`;
                     `data_state_code (t:(C,FFI)data_state)`; progs]
                    DATAPAUX_B2D_code_rel_union)) THEN
    ASM_REWRITE_TAC[bvi_to_data_compile_prog_def; compile_part_thm; MAP];
    REWRITE_TAC[FUN_EQ_THM; o_THM]]);;

let DATAPAUX_B2D_iAssign_Install_Rval = prove
 (`!n1 args live env (t2:(C,FFI)data_state) (r:(C,FFI)bvi_state) zs v r'.
     bvi_to_dataProof_state_rel r t2 /\
     data_get_vars args (data_state_locals t2) = SOME zs /\
     domain (list_to_num_set (APPEND (APPEND args live) env)) SUBSET
       domain (data_state_locals t2) /\
     bvi_do_app clos_Install (MAP data_to_bvi_v zs) r = Rval (v,r')
     ==> ?pv t3. data_evaluate (iAssign n1 clos_Install args live env,t2) =
                   (NONE,data_set_var n1 pv t3) /\
                 v = data_to_bvi_v pv /\ bvi_to_dataProof_state_rel r' t3 /\
                 (data_state_locals t3 = data_state_locals t2 \/
                  data_state_locals t3 =
                    mk_wf (sptree_inter (data_state_locals t2)
                                 (list_to_num_set (APPEND (APPEND args live) env)))) /\
                 data_state_stack t3 = data_state_stack t2 /\
                 data_state_handler t3 = data_state_handler t2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_do_app_def] THEN STRIP_TAC THEN
  REWRITE_TAC[iAssign_def; LET_DEF; LET_END_DEF; op_requires_names_def;
              distinctness "clos_op"] THEN
  REWRITE_TAC[data_evaluate_def; IS_NONE_DEF; data_cut_state_opt_def; data_cut_state_def;
              data_cut_env_def; op_requires_names_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_do_app_def] THEN
  W(fun (asl,w) ->
     let t = find_term (fun t -> is_comb t &&
               (try fst(dest_const(fst(strip_comb t))) = "data_do_install" with _ -> false)) w in
     MP_TAC(ISPECL [`zs:data_v list`; `r:(C,FFI)bvi_state`; rand t; `v:bvl_v`;
                    `r':(C,FFI)bvi_state`] DATAPAUX_B2D_do_install)) THEN
  ASM_REWRITE_TAC[DATAPAUX_B2D_state_rel_fupds] THEN
  DISCH_THEN(X_CHOOSE_THEN `pv:data_v` (X_CHOOSE_THEN `t3:(C,FFI)data_state`
    STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  REPEAT DATAPAUX_EXISTS_MATCH_TAC THEN
  ASM_REWRITE_TAC[install_sfs_def; DATAPAUX_B2D_state_rel_fupds;
                  data_state_INFO.ri_accfupds; K_THM]);;

let DATAPAUX_B2D_iAssign_CopyByte_Rval = prove
 (`!n1 args live env (t2:(C,FFI)data_state) (r:(C,FFI)bvi_state) zs v r'.
     bvi_to_dataProof_state_rel r t2 /\
     data_get_vars args (data_state_locals t2) = SOME zs /\
     domain (list_to_num_set (APPEND (APPEND args live) env)) SUBSET
       domain (data_state_locals t2) /\
     bvi_do_app (MemOp (CopyByte F)) (MAP data_to_bvi_v zs) r = Rval (v,r')
     ==> ?pv t3. data_evaluate (iAssign n1 (MemOp (CopyByte F)) args live env,t2) =
                   (NONE,data_set_var n1 pv t3) /\
                 v = data_to_bvi_v pv /\ bvi_to_dataProof_state_rel r' t3 /\
                 (data_state_locals t3 = data_state_locals t2 \/
                  data_state_locals t3 =
                    mk_wf (sptree_inter (data_state_locals t2)
                                 (list_to_num_set (APPEND (APPEND args live) env)))) /\
                 data_state_stack t3 = data_state_stack t2 /\
                 data_state_handler t3 = data_state_handler t2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[iAssign_def; LET_DEF; LET_END_DEF; op_requires_names_def;
              distinctness "clos_op"; injectivity "clos_op"; distinctness "mem_op";
              injectivity "mem_op"; MESON[] `!a:A. ?x. a = x`; MESON[] `?b:bool. ~b`] THEN
  MP_TAC(ISPECL [`n1:num`; `MemOp (CopyByte F)`; `args:num list`;
    `SOME (list_to_num_set (APPEND (APPEND args live) env))`; `t2:(C,FFI)data_state`;
    `r:(C,FFI)bvi_state`; `zs:data_v list`; `v:bvl_v`; `r':(C,FFI)bvi_state`]
    DATAPAUX_B2D_Assign_Rval_gen) THEN
  ASM_REWRITE_TAC[DATAPAUX_B2D_do_app_CopyByte; distinctness "clos_op"; op_requires_names_def;
                  injectivity "clos_op"; injectivity "mem_op"; distinctness "mem_op";
                  op_space_req_def; IS_SOME_DEF; option_INJ;
                  MESON[] `!a:A. ?x. a = x`;
                  MESON[] `!a:A P. (!x. a = x ==> P x) <=> P a`;
                  MESON[] `?b:bool. ~b`] THEN
  REWRITE_TAC[option_CASE] THEN
  DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN ASM_REWRITE_TAC[] THEN
  REPEAT DATAPAUX_EXISTS_MATCH_TAC THEN ASM_REWRITE_TAC[]);;

let DATAPAUX_B2D_iAssign_any_Rval = prove
 (`!n1 op args live env (t2:(C,FFI)data_state) (r:(C,FFI)bvi_state) zs v r'.
     bvi_to_dataProof_state_rel r t2 /\
     data_get_vars args (data_state_locals t2) = SOME zs /\
     domain (list_to_num_set (APPEND (APPEND args live) env)) SUBSET
       domain (data_state_locals t2) /\
     bvi_do_app op (MAP data_to_bvi_v zs) r = Rval (v,r')
     ==> ?pv t3. data_evaluate (iAssign n1 op args live env,t2) =
                   (NONE,data_set_var n1 pv t3) /\
                 v = data_to_bvi_v pv /\ bvi_to_dataProof_state_rel r' t3 /\
                 (data_state_locals t3 = data_state_locals t2 \/
                  data_state_locals t3 =
                    mk_wf (sptree_inter (data_state_locals t2)
                                 (list_to_num_set (APPEND (APPEND args live) env)))) /\
                 data_state_stack t3 = data_state_stack t2 /\
                 data_state_handler t3 = data_state_handler t2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let use th = MP_TAC(SPECL [`n1:num`; `args:num list`; `live:num list`; `env:num list`;
                   `t2:(C,FFI)data_state`; `r:(C,FFI)bvi_state`; `zs:data_v list`; `v:bvl_v`;
                   `r':(C,FFI)bvi_state`] th) THEN ASM_REWRITE_TAC[] in
  ASM_CASES_TAC `op = clos_Install` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN use DATAPAUX_B2D_iAssign_Install_Rval; ALL_TAC] THEN
  ASM_CASES_TAC `op = IntOp Greater \/ op = IntOp GreaterEq \/
                 op = WordOp (WordTest W8 (Compare Gt)) \/
                 op = WordOp (WordTest W8 (Compare Geq))` THENL
   [MP_TAC(SPECL [`n1:num`; `op:clos_op`; `args:num list`; `live:num list`; `env:num list`;
                  `t2:(C,FFI)data_state`; `r:(C,FFI)bvi_state`; `zs:data_v list`; `v:bvl_v`;
                  `r':(C,FFI)bvi_state`] DATAPAUX_B2D_iAssign_swap_Rval) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `?b. op = MemOp (CopyByte b)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `b:bool` SUBST_ALL_TAC) THEN
    MP_TAC(SPEC `b:bool` BOOL_CASES_AX) THEN DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [UNDISCH_TAC `bvi_do_app (MemOp (CopyByte T)) (MAP data_to_bvi_v zs) (r:(C,FFI)bvi_state) =
                   Rval (v,r')` THEN
      REWRITE_TAC[DATAPAUX_B2D_ForceThunk_err; distinctness "result"];
      use DATAPAUX_B2D_iAssign_CopyByte_Rval];
    ALL_TAC] THEN
  ASM_CASES_TAC `op = clos_ThunkOp ForceThunk` THENL
   [UNDISCH_TAC `bvi_do_app op (MAP data_to_bvi_v zs) (r:(C,FFI)bvi_state) = Rval (v,r')` THEN
    ASM_REWRITE_TAC[DATAPAUX_B2D_ForceThunk_err; distinctness "result"];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_EXISTS_THM]) THEN
  MP_TAC(SPECL [`n1:num`; `op:clos_op`; `args:num list`; `live:num list`; `env:num list`;
                `t2:(C,FFI)data_state`; `r:(C,FFI)bvi_state`; `zs:data_v list`; `v:bvl_v`;
                `r':(C,FFI)bvi_state`] DATAPAUX_B2D_iAssign_Rval) THEN
  ASM_REWRITE_TAC[]);;

let DATAPAUX_B2D_var_corr_domain = prove
 (`!env corr (t:data_v spt).
     var_corr env corr (sptree_map data_to_bvi_v t) ==> set_of_list corr SUBSET domain t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[var_corr_def; LIST_REL_EL_EQN; data_get_var_def; lookup_map; SUBSET;
              IN_SET_OF_LIST; MEM_EXISTS_EL] THEN
  STRIP_TAC THEN X_GEN_TAC `x:num` THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[domain_lookup] THEN
  MP_TAC(ISPEC `lookup (EL i corr) (t:data_v spt)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT] THEN MESON_TAC[]);;

let DATAPAUX_B2D_ALL_domain = prove
 (`!live (t:A spt). ALL (\n. ~(lookup n t = NONE)) live ==> set_of_list live SUBSET domain t`,
  REWRITE_TAC[GSYM ALL_MEM; SUBSET; IN_SET_OF_LIST; domain_lookup] THEN
  MESON_TAC[option_CASES; option_DISTINCT]);;

(* local helpers for the Force, Call and LetCall cases of compile_correct *)
let DATAPAUX_B2D_jump_transfer = prove
 (`!(a:(C,FFI)data_state) j (b:(C,FFI)data_state).
     data_jump_exc a = SOME j
     ==> data_state_handler b = data_state_handler a /\
         (data_state_stack b = data_state_stack a \/
          (?l e. data_state_stack a = CONS (data_Env l e) (data_state_stack b)))
     ==> data_jump_exc b =
         SOME (data_state_handler_fupd (K (data_state_handler j))
                (data_state_locals_fupd (K (data_state_locals j))
                   (data_state_stack_fupd (K (data_state_stack j))
                      (data_state_locals_size_fupd (K (data_state_locals_size j)) b))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IMP_CONJ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP jump_exc_IMP) STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `nn:num` (X_CHOOSE_THEN `ee:data_v spt`
    (X_CHOOSE_THEN `lss:num option` (X_CHOOSE_THEN `xs:(stack)list` STRIP_ASSUME_TAC))))) THEN
  ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[data_jump_exc_def] THEN ASM_REWRITE_TAC[] THENL
   [CASE_REWRITE_TAC[];
    SUBGOAL_THEN `data_state_handler (a:(C,FFI)data_state) <
                  LENGTH (data_state_stack (b:(C,FFI)data_state))` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
      UNDISCH_TAC `LASTN (data_state_handler (a:(C,FFI)data_state) + 1)
                     (data_state_stack a) = CONS (Exc lss ee nn) xs` THEN
      UNDISCH_TAC `data_state_handler (a:(C,FFI)data_state) < LENGTH (data_state_stack a)` THEN
      ASM_REWRITE_TAC[LENGTH] THEN DISCH_TAC THEN
      SUBGOAL_THEN `data_state_handler (a:(C,FFI)data_state) + 1 =
                    LENGTH (CONS (data_Env l e) (data_state_stack (b:(C,FFI)data_state)))`
        SUBST1_TAC THENL [REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[LASTN_LENGTH_ID; injectivity "list"; distinctness "stack"];
      ALL_TAC] THEN
    UNDISCH_TAC `LASTN (data_state_handler (a:(C,FFI)data_state) + 1)
                   (data_state_stack a) = CONS (Exc lss ee nn) xs` THEN
    ASM_SIMP_TAC[LASTN_TL] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]]);;

let DATAPAUX_B2D_jump_fupds = prove
 (`!(t2:(C,FFI)data_state) st h ls a b c d.
     data_jump_exc (data_state_stack_fupd (K st) (data_state_handler_fupd (K h) t2)) =
       SOME (data_state_locals_size_fupd (K ls) t2)
     ==> data_jump_exc (data_state_stack_fupd (K st) (data_state_handler_fupd (K h)
           (data_state_locals_size_fupd (K a) (data_state_safe_for_space_fupd (K b)
              (data_state_peak_heap_length_fupd (K c) (data_state_stack_max_fupd (K d) t2)))))) =
         SOME (data_state_locals_size_fupd (K ls)
           (data_state_locals_size_fupd (K a) (data_state_safe_for_space_fupd (K b)
              (data_state_peak_heap_length_fupd (K c) (data_state_stack_max_fupd (K d) t2)))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP DATAPAUX_B2D_jump_transfer) THEN
  DISCH_THEN(fun th -> W(fun (_,w) -> MP_TAC(SPEC (rand(lhand w)) th))) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[option_INJ; data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

let DATAPAUX_B2D_jump_Env = prove
 (`!(t2:(C,FFI)data_state) st h ls l e.
     data_jump_exc (data_state_stack_fupd (K (CONS (data_Env l e) st))
                      (data_state_handler_fupd (K h) t2)) =
       SOME (data_state_locals_size_fupd (K ls) t2)
     ==> data_jump_exc (data_state_stack_fupd (K st) (data_state_handler_fupd (K h) t2)) =
         SOME (data_state_locals_size_fupd (K ls) t2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP DATAPAUX_B2D_jump_transfer) THEN
  DISCH_THEN(fun th -> W(fun (_,w) -> MP_TAC(SPEC (rand(lhand w)) th))) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; injectivity "list"] THEN
  ANTS_TAC THENL [MESON_TAC[]; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[option_INJ; data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

let DATAPAUX_B2D_state_rel_call_push = prove
 (`!(s:(C,FFI)bvi_state) (t:(C,FFI)data_state) a ss e b.
     (bvi_to_dataProof_state_rel s (data_call_env a ss t) <=>
      bvi_to_dataProof_state_rel s t) /\
     (bvi_to_dataProof_state_rel s (data_push_env e b t) <=>
      bvi_to_dataProof_state_rel s t)`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF; DATAPAUX_B2D_state_rel_fupds];
    BOOL_CASES_TAC `b:bool` THEN
    REWRITE_TAC[data_push_env_def; LET_DEF; LET_END_DEF; DATAPAUX_B2D_state_rel_fupds]]);;

let DATAPAUX_B2D_var_corr_fromList = prove
 (`!args:data_v list.
     var_corr (MAP data_to_bvi_v args) (COUNT_LIST (LENGTH args))
       (sptree_map data_to_bvi_v (fromList args))`,
  GEN_TAC THEN
  REWRITE_TAC[var_corr_def; data_get_var_def; lookup_map; COUNT_LIST_GENLIST; LIST_REL_EL_EQN;
              LENGTH_LIST_OF_SEQ; LENGTH_MAP] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; EL_MAP; I_THM; lookup_fromList; OPTION_MAP_DEF]);;

let DATAPAUX_B2D_cut_live_corr = prove
 (`!(t1:(C,FFI)data_state) env corr live.
     var_corr env corr (sptree_map data_to_bvi_v (data_state_locals t1)) /\
     ALL (\n. ~(lookup n (data_state_locals t1) = NONE)) live
     ==> data_cut_env (list_to_num_set (APPEND live corr)) (data_state_locals t1) =
         SOME (mk_wf (sptree_inter (data_state_locals t1) (list_to_num_set (APPEND live corr))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[data_cut_env_def] THEN
  SUBGOAL_THEN `domain (list_to_num_set (APPEND live corr)) SUBSET
                domain (data_state_locals (t1:(C,FFI)data_state))`
    (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[domain_list_to_num_set2; SET_OF_LIST_APPEND; UNION_SUBSET] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DATAPAUX_B2D_ALL_domain THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC DATAPAUX_B2D_var_corr_domain THEN EXISTS_TAC `env:bvl_v list` THEN
    ASM_REWRITE_TAC[]]);;

let DATAPAUX_B2D_FORCE_FACTS = prove
 (`!(t1:(C,FFI)data_state) (t3:(C,FFI)data_state) n env corr live pv.
     (!k. n <= k ==> lookup k (data_state_locals t1) = NONE) /\
     var_corr env corr (sptree_map data_to_bvi_v (data_state_locals t1)) /\
     data_state_locals t3 =
       mk_wf (sptree_inter (data_state_locals t1) (list_to_num_set (APPEND live corr))) /\
     data_state_stack t3 = data_state_stack t1 /\
     data_state_handler t3 = data_state_handler t1
     ==> n <= n + 1 /\
         ALL (\v. v < n + 1) [n] /\
         (!k. n + 1 <= k
              ==> lookup k (data_state_locals (data_set_var n pv t3)) = NONE) /\
         var_corr env corr
           (sptree_map data_to_bvi_v (data_state_locals (data_set_var n pv t3))) /\
         (!k x. lookup k (data_state_locals (data_set_var n pv t3)) = SOME x
                ==> k < n + 1) /\
         (!k x. lookup k (data_state_locals t1) = SOME x /\ (~MEM k live ==> MEM k corr)
                ==> lookup k (data_state_locals (data_set_var n pv t3)) = SOME x) /\
         data_state_stack t1 = data_state_stack (data_set_var n pv t3) /\
         data_state_handler t1 = data_state_handler (data_set_var n pv t3) /\
         (~(data_jump_exc t1 = NONE) ==> ~(data_jump_exc (data_set_var n pv t3) = NONE)) /\
         var_corr [data_to_bvi_v pv] [n]
           (sptree_map data_to_bvi_v (data_state_locals (data_set_var n pv t3)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC DATAPAUX_B2D_OP_FACTS THEN EXISTS_TAC `t1:(C,FFI)data_state` THEN
  MP_TAC(ISPECL [`t3:(C,FFI)data_state`; `t1:(C,FFI)data_state`; `[]:num list`;
                 `live:num list`; `corr:num list`] DATAPAUX_B2D_cut_facts) THEN
  ASM_REWRITE_TAC[APPEND] THEN STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN MESON_TAC[]);;

(* the callee of a Force, Call or LetCall: compile_correct for the body,    *)
(* compiled with tail = T and then optimised (its hypothesis is the         *)
(* conclusion of compile_correct for xs = [exp] and tail = T)               *)
let DATAPAUX_B2D_CALLEE = prove
 (let _,b = strip_forall DATAPAUX_B2D_CC_GOAL in
  let hyp = vsubst [`[exp:bvi_exp]`,`xs:bvi_exp list`; `T`,`tail:bool`] (rand b) in
  list_mk_forall([`exp:bvi_exp`; `env:bvl_v list`; `res:bvi_result`;
                  `s2:(C,FFI)bvi_state`; `t1:(C,FFI)data_state`; `n:num`;
                  `corr:num list`; `live:num list`],
   mk_imp(hyp,
   `~(res:bvi_result = Rerr (Rabort Rtype_error))
    ==> ?r (t2:(C,FFI)data_state) ls.
          data_evaluate (bvi_to_data_optimise (FST (bvi_to_data_compile n corr T live [exp])),
                         (t1:(C,FFI)data_state)) = (SOME r,t2) /\
          bvi_to_dataProof_state_rel (s2:(C,FFI)bvi_state) t2 /\
          (~(?vs. res = Rerr (Rraise (Ret vs))) ==> data_to_bvi_result r = res) /\
          ((?vs. res = Rerr (Rraise (Ret vs)))
           ==> ?vs'. r = Rval vs' /\ res = Rerr (Rraise (Ret (MAP data_to_bvi_v vs')))) /\
          ((?v. res = Rval v) \/ (?vs. res = Rerr (Rraise (Ret vs)))
           ==> data_state_stack t1 = data_state_stack t2 /\
               data_state_handler t1 = data_state_handler t2) /\
          ((?v. res = Rerr (Rraise (Exn v)))
           ==> data_jump_exc (data_state_stack_fupd (K (data_state_stack t1))
                                (data_state_handler_fupd (K (data_state_handler t1)) t2)) =
               SOME (data_state_locals_size_fupd (K ls) t2))`)),
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)data_state` (X_CHOOSE_THEN `prog:data_prog`
    (X_CHOOSE_THEN `pres:((data_v list,data_v)result)option` (X_CHOOSE_THEN `vs:num list`
    (X_CHOOSE_THEN `next_var:num` (X_CHOOSE_THEN `ls:num option` STRIP_ASSUME_TAC)))))) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[FST] THEN
  MP_TAC(ISPEC `pres:((data_v list,data_v)result)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `r:(data_v list,data_v)result` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THENL
   [FIRST_ASSUM CONTR_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_conj (concl th) && not (is_eq (concl th)) then
                            STRIP_ASSUME_TAC th else failwith "") THEN
  MP_TAC(ISPECL [`prog:data_prog`; `t1:(C,FFI)data_state`] optimise_correct) THEN
  ASM_REWRITE_TAC[FST; option_DISTINCT; option_INJ] THEN
  ANTS_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[data_to_bvi_result_def]) THEN
    ASM_MESON_TAC[distinctness "result"];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `safe:bool` (X_CHOOSE_THEN `peak:num` (X_CHOOSE_THEN `smx:num option`
    (X_CHOOSE_THEN `ls2:num option` SUBST1_TAC)))) THEN
  REWRITE_TAC[PAIR_MAP_THM; I_THM; PAIR_EQ; option_INJ] THEN
  REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls:num option` THEN
  ASM_REWRITE_TAC[GSYM state_rel_peak_safe; data_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC DATAPAUX_B2D_jump_fupds THEN ASM_MESON_TAC[]);;

(* close a goal with an assumption ~(x = x) *)
let DATAPAUX_B2D_NEQ_REFL_TAC : tactic =
  FIRST_ASSUM(fun th -> let c = concl th in
    if is_neg c && is_eq (rand c) && lhs(rand c) = rhs(rand c)
    then CONTR_TAC (MP (NOT_ELIM th) (REFL (lhs(rand c)))) else failwith "NEQ_REFL");;

(* the bvi result is (res,s2) = (Rerr (Rabort Rtype_error),_): contradiction *)
let DATAPAUX_B2D_TERR_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  DATAPAUX_B2D_NEQ_REFL_TAC;;

(* the result of a forced thunk body: a Ret raise would be a type error *)
let DATAPAUX_B2D_force_res = prove
 (CASE_TERM `!(p:bvi_result # (C,FFI)bvi_state) res s2.
     (match p with (Rerr (Rraise (Ret _)),s1) -> (Rerr (Rabort Rtype_error),s1) | x -> x) =
       (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error))
     ==> p = (res,s2) /\ ~(?vs. res = Rerr (Rraise (Ret vs)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `p:bvi_result # (C,FFI)bvi_state` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:bvi_result` (X_CHOOSE_THEN `s3:(C,FFI)bvi_state`
    SUBST1_TAC)) THEN
  MP_TAC(ISPEC `r1:bvi_result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:bvl_v list` SUBST1_TAC)
                              (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THENL
   [ALL_TAC;
    MP_TAC(ISPEC `e:(exn_or_ret)error_result` (cases "error_result")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `ex:exn_or_ret` SUBST1_TAC)
                                (X_CHOOSE_THEN `ab:abort` SUBST1_TAC)) THEN
    CASE_REWRITE_TAC[] THENL
     [MP_TAC(ISPEC `ex:exn_or_ret` (cases "exn_or_ret")) THEN
      DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `w:bvl_v` SUBST1_TAC)
                                  (X_CHOOSE_THEN `ws:bvl_v list` SUBST1_TAC)) THEN
      CASE_REWRITE_TAC[];
      ALL_TAC]] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC DATAPAUX_B2D_RES_RWS);;

(* pushing an environment frame keeps an exception handler reachable *)
let DATAPAUX_B2D_jump_push = prove
 (`!(t1:(C,FFI)data_state) a ss env.
     ~(data_jump_exc t1 = NONE)
     ==> ~(data_jump_exc (data_call_env a ss (data_push_env env F (data_dec_clock t1))) =
           NONE)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF; jump_exc_NONE] THEN
  MP_TAC(ISPEC `data_jump_exc (t1:(C,FFI)data_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `j:(C,FFI)data_state` ASSUME_TAC)) THEN
  REWRITE_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(ISPECL [`t1:(C,FFI)data_state`;
                 `data_push_env env F (data_dec_clock (t1:(C,FFI)data_state))`;
                 `data_state_locals_size (t1:(C,FFI)data_state)`; `env:data_v spt`;
                 `j:(C,FFI)data_state`] DSEMAUX_jump_exc_Env_cons3) THEN
  REWRITE_TAC[data_push_env_def; data_dec_clock_def; LET_DEF; LET_END_DEF;
              data_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]);;

(* HOL4: compile_correct[NIL] *)
let DATAPAUX_B2D_CC_NIL = prove
 (el 0 DATAPAUX_B2D_CC_CASES,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_evaluate_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[bvi_to_data_compile_def; PAIR_EQ] THEN
  MAP_EVERY EXISTS_TAC [`t1:(C,FFI)data_state`; `data_Skip`; `NONE:((data_v list,data_v)result)option`;
                        `[]:num list`; `n:num`; `NONE:num option`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; ARITH_RULE `~(0 = 1)`]) THEN
  ASM_REWRITE_TAC[data_evaluate_def; ALL; LE_REFL; var_corr_def; ALL2] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[ALL2] THEN
  ASM_MESON_TAC[NOT_LT; option_DISTINCT]
);;

(* HOL4: compile_correct[CONS] *)
let DATAPAUX_B2D_CC_CONS = prove
 (el 1 DATAPAUX_B2D_CC_CASES,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~tail` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  MP_TAC(ISPEC `bvi_evaluate ([x],env,s:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:bvi_result` (X_CHOOSE_THEN `s1:(C,FFI)bvi_state`
    ASSUME_TAC)) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `bvi_to_data_compile n corr F live [x]` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:data_prog` (X_CHOOSE_THEN `y1:num list # num` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `y1:num list # num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:num list` (X_CHOOSE_THEN `n1:num` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `bvi_to_data_compile n1 corr F (CONS (HD v1) live) (CONS y xs)`
           PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:data_prog` (X_CHOOSE_THEN `y2:num list # num` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `y2:num list # num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `v2:num list` (X_CHOOSE_THEN `n2:num` SUBST_ALL_TAC)) THEN
  ONCE_REWRITE_TAC[bvi_to_data_compile_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  MP_TAC(ISPEC `r1:bvi_result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:bvl_v list` SUBST_ALL_TAC)
                              (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_SING_IMP) THEN
    DISCH_THEN(X_CHOOSE_THEN `w:bvl_v` SUBST_ALL_TAC) THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`Rval [w]:bvi_result`; `s1:(C,FFI)bvi_state`;
      `t1:(C,FFI)data_state`; `n:num`; `corr:num list`; `F`; `live:num list`]) THEN
    ASM_REWRITE_TAC[LENGTH; PAIR_EQ; distinctness "result"] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN RVEQ_TAC THEN
    DATAPAUX_B2D_PRES_TAC `pres:((data_v list,data_v)result)option` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP compile_SING_IMP) THEN
    DISCH_THEN(X_CHOOSE_THEN `tv:num` SUBST_ALL_TAC) THEN
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`[w]:bvl_v list`; `s1:(C,FFI)bvi_state`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ih2") THEN
    MP_TAC(ISPEC `bvi_evaluate (CONS y xs,env,s1:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r2:bvi_result` (X_CHOOSE_THEN `s3:(C,FFI)bvi_state`
      ASSUME_TAC)) THEN ASM_REWRITE_TAC[HD] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HD]) THEN
    SUBGOAL_THEN `ALL (\n. ~(lookup n (data_state_locals (t2:(C,FFI)data_state)) = NONE))
                      (CONS tv live)` ASSUME_TAC THENL
     [REWRITE_TAC[ALL] THEN CONJ_TAC THENL
       [UNDISCH_TAC `var_corr [w] [tv]
          (sptree_map data_to_bvi_v (data_state_locals (t2:(C,FFI)data_state)))` THEN
        REWRITE_TAC[var_corr_def; ALL2; data_get_var_def; lookup_map] THEN
        MESON_TAC[OPTION_MAP_DEF; option_DISTINCT];
        UNDISCH_TAC `ALL (\n. ~(lookup n (data_state_locals (t1:(C,FFI)data_state)) = NONE))
                       live` THEN
        REWRITE_TAC[GSYM ALL_MEM] THEN DATAPAUX_LOOKUP_MESON_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPEC `r2:bvi_result` (cases "result")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a2:bvl_v list` SUBST_ALL_TAC)
                                (X_CHOOSE_THEN `e2:(exn_or_ret)error_result` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THENL
     [REMOVE_THEN "ih2" (MP_TAC o SPECL [`Rval a2:bvi_result`; `s3:(C,FFI)bvi_state`;
        `t2:(C,FFI)data_state`; `next_var:num`; `corr:num list`; `F`;
        `CONS (tv:num) live`]) THEN
      ASM_REWRITE_TAC[distinctness "result"; PAIR_EQ] THEN
      DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC [("t2","t3"); ("prog","prog2"); ("pres","pres2"); ("vs","vs2"); ("next_var","nv2"); ("ls","ls2")]) THEN RVEQ_TAC THEN
      DATAPAUX_B2D_PRES_TAC `pres2:((data_v list,data_v)result)option` THEN
      REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
      DATAPAUX_B2D_SEQ_NONE_TAC THEN
      ASM_REWRITE_TAC[PAIR_EQ] THEN
      REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN TRY (EXISTS_TAC `ls:num option`) THEN
      CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC DATAPAUX_B2D_RES_RWS THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN ASM_REWRITE_TAC[ALL] THEN
      REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC;
        ASM_ARITH_TAC;
        REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[MEM; DE_MORGAN_THM] THEN CONJ_TAC THENL
         [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `var_corr [w] [tv]
          (sptree_map data_to_bvi_v (data_state_locals (t2:(C,FFI)data_state)))` THEN
        REWRITE_TAC[var_corr_def; ALL2; data_get_var_def; lookup_map] THEN
        MP_TAC(ISPEC `lookup tv (data_state_locals (t2:(C,FFI)data_state))`
                 (cases "option")) THEN
        DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC `z:data_v`)) THEN
        ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `lookup tv (data_state_locals (t3:(C,FFI)data_state)) = SOME z`
          ASSUME_TAC THENL
         [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM]; ALL_TAC] THEN
        REWRITE_TAC[var_corr_def; ALL2; data_get_var_def; lookup_map] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[var_corr_def; data_get_var_def; lookup_map]) THEN
        ASM_REWRITE_TAC[OPTION_MAP_DEF]];
      SUBGOAL_THEN `(?v. e2 = Rraise (Exn v))
                    ==> ~(data_jump_exc (t2:(C,FFI)data_state) = NONE)` ASSUME_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE DATAPAUX_B2D_RES_RWS) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      REMOVE_THEN "ih2" (MP_TAC o SPECL [`Rerr e2:bvi_result`; `s3:(C,FFI)bvi_state`;
        `t2:(C,FFI)data_state`; `next_var:num`; `corr:num list`; `F`;
        `CONS (tv:num) live`]) THEN
      ASM_REWRITE_TAC(PAIR_EQ :: DATAPAUX_B2D_RES_RWS) THEN
      DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC [("t2","t3"); ("prog","prog2"); ("pres","pres2"); ("vs","vs2"); ("next_var","nv2"); ("ls","ls2")]) THEN RVEQ_TAC THEN
      DATAPAUX_B2D_PRES_TAC `pres2:((data_v list,data_v)result)option` THEN
      REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
      DATAPAUX_B2D_SEQ_NONE_TAC THEN
      ASM_REWRITE_TAC[PAIR_EQ] THEN
      REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN TRY (EXISTS_TAC `ls2:num option`) THEN
      CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC DATAPAUX_B2D_RES_RWS];
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`Rerr e:bvi_result`; `s1:(C,FFI)bvi_state`;
      `t1:(C,FFI)data_state`; `n:num`; `corr:num list`; `F`; `live:num list`]) THEN
    ASM_REWRITE_TAC[LENGTH; PAIR_EQ] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN RVEQ_TAC THEN
    DATAPAUX_B2D_PRES_TAC `pres:((data_v list,data_v)result)option` THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
    DATAPAUX_B2D_SEQ_SOME_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls:num option` THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC DATAPAUX_B2D_RES_RWS]
);;

(* HOL4: compile_correct[Var] *)
let DATAPAUX_B2D_CC_VAR = prove
 (el 2 DATAPAUX_B2D_CC_CASES,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ; bvi_evaluate_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`env:bvl_v list`; `corr:num list`;
                 `sptree_map data_to_bvi_v (data_state_locals (t1:(C,FFI)data_state))`; `n:num`]
                DATAPAUX_B2D_var_corr_EL) THEN
  ASM_REWRITE_TAC[data_get_var_def; lookup_map] THEN
  MP_TAC(ISPEC `lookup (EL n corr) (data_state_locals (t1:(C,FFI)data_state))`
           (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN
  REWRITE_TAC[bvi_to_data_compile_def; LET_DEF; LET_END_DEF; any_el_ALT] THEN
  ASM_REWRITE_TAC[] THEN
  BOOL_CASES_TAC `tail:bool` THEN REWRITE_TAC[PAIR_EQ] THEN
  REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC
 THEN
  REWRITE_TAC[data_evaluate_def; data_get_vars_def; data_get_var_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
  REWRITE_TAC[data_to_bvi_result_def; MAP; distinctness "result"; injectivity "result";
              distinctness "error_result"; CONS_11] THEN
  ASM_REWRITE_TAC[]
 THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[DATAPAUX_B2D_state_rel_fupds; data_flush_state_def; data_to_bvi_result_def;
              MAP; CONS_11; injectivity "result"; data_state_INFO.ri_accfupds; K_THM;
              var_corr_def; ALL2; ALL; data_get_var_def; lookup_map; MAX] THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
  REPEAT CONJ_TAC THEN TRY COND_CASES_TAC THEN REPEAT STRIP_TAC THEN
  TRY ASM_ARITH_TAC THEN
  TRY (FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC) THEN
  ASM_MESON_TAC[NOT_LT; option_DISTINCT; LE_TRANS; LT_IMP_LE]
);;

(* HOL4: compile_correct[If] *)
let DATAPAUX_B2D_CC_IF = prove
 (el 3 DATAPAUX_B2D_CC_CASES,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1")
    (CONJUNCTS_THEN2 (LABEL_TAC "ih2") (LABEL_TAC "ih3"))) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  MP_TAC(ISPEC `bvi_evaluate ([x1],env,s:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:bvi_result` (X_CHOOSE_THEN `s1:(C,FFI)bvi_state`
    ASSUME_TAC)) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `bvi_to_data_compile n corr F live [x1]` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:data_prog` (X_CHOOSE_THEN `y1:num list # num` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `y1:num list # num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:num list` (X_CHOOSE_THEN `n1:num` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `bvi_to_data_compile n1 corr tail live [x2]` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:data_prog` (X_CHOOSE_THEN `y2:num list # num` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `y2:num list # num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `v2:num list` (X_CHOOSE_THEN `n2:num` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `bvi_to_data_compile n2 corr tail live [x3]` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c3:data_prog` (X_CHOOSE_THEN `y3:num list # num` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `y3:num list # num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `v3:num list` (X_CHOOSE_THEN `n3:num` SUBST_ALL_TAC)) THEN
  ONCE_REWRITE_TAC[bvi_to_data_compile_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r1:bvi_result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:bvl_v list` SUBST_ALL_TAC)
                              (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_SING_IMP) THEN
    DISCH_THEN(X_CHOOSE_THEN `w:bvl_v` SUBST_ALL_TAC) THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`Rval [w]:bvi_result`; `s1:(C,FFI)bvi_state`;
      `t1:(C,FFI)data_state`; `n:num`; `corr:num list`; `F`; `live:num list`]) THEN
    ASM_REWRITE_TAC[LENGTH; PAIR_EQ; distinctness "result"] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN RVEQ_TAC THEN
    DATAPAUX_B2D_PRES_TAC `pres:((data_v list,data_v)result)option` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP compile_SING_IMP o
                check (fun th -> free_in `x1:bvi_exp` (concl th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `tv:num` SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `?z. lookup tv (data_state_locals (t2:(C,FFI)data_state)) = SOME z /\
                      data_to_bvi_v z = w` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `var_corr [w] [tv]
        (sptree_map data_to_bvi_v (data_state_locals (t2:(C,FFI)data_state)))` THEN
      REWRITE_TAC[var_corr_def; ALL2; data_get_var_def; lookup_map] THEN
      MP_TAC(ISPEC `lookup tv (data_state_locals (t2:(C,FFI)data_state))`
               (cases "option")) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check ((=) `data_to_bvi_v z = w` o concl)) THEN
    SUBGOAL_THEN `ALL (\n. ~(lookup n (data_state_locals (t2:(C,FFI)data_state)) = NONE))
                      live` ASSUME_TAC THENL
     [UNDISCH_TAC `ALL (\n. ~(lookup n (data_state_locals (t1:(C,FFI)data_state)) = NONE))
                     live` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN DATAPAUX_LOOKUP_MESON_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(?v. (res:bvi_result) = Rerr (Rraise (Exn v)))
                  ==> ~(data_jump_exc (t2:(C,FFI)data_state) = NONE)` ASSUME_TAC THENL
     [DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[HD] THEN
    ASM_CASES_TAC `bvl_Boolv T = data_to_bvi_v z` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `isBool T z` ASSUME_TAC THENL [ASM_REWRITE_TAC[isBool_eq]; ALL_TAC] THEN
      REMOVE_THEN "ih2" (MP_TAC o SPECL [`[data_to_bvi_v z]`; `s1:(C,FFI)bvi_state`]) THEN
      ASM_REWRITE_TAC[HD] THEN DISCH_THEN(LABEL_TAC "ih2") THEN DISCH_TAC THEN
      MP_TAC(SPEC `tail:bool` BOOL_CASES_AX) THEN
      DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[PAIR_EQ] THEN
      REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
      DATAPAUX_B2D_SEQ_NONE_TAC THEN
      REWRITE_TAC[data_evaluate_def; data_get_var_def] THEN ASM_REWRITE_TAC[] THEN
      CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THENL
       [REMOVE_THEN "ih2" (MP_TAC o SPECL [`res:bvi_result`; `s2:(C,FFI)bvi_state`;
          `t2:(C,FFI)data_state`; `next_var:num`; `corr:num list`; `T`; `live:num list`]) THEN
        ASM_REWRITE_TAC[LENGTH; ONE; PAIR_EQ] THEN
        DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC [("t2","t3"); ("prog","prog2"); ("pres","pres2"); ("vs","vs2"); ("next_var","nv2"); ("ls","ls2")]) THEN RVEQ_TAC THEN
        DATAPAUX_B2D_PRES_TAC `pres2:((data_v list,data_v)result)option` THEN
        ASM_REWRITE_TAC[PAIR_EQ] THEN
        REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls2:num option` THEN
        CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC DATAPAUX_B2D_RES_RWS;
        MP_TAC(ISPEC `res:bvi_result` (cases "result")) THEN
        DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a2:bvl_v list` SUBST_ALL_TAC)
          (X_CHOOSE_THEN `e2:(exn_or_ret)error_result` SUBST_ALL_TAC)) THENL
         [FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_SING_IMP o
                      check (fun th -> free_in `x2:bvi_exp` (concl th))) THEN
          DISCH_THEN(X_CHOOSE_THEN `w2:bvl_v` SUBST_ALL_TAC) THEN
          REMOVE_THEN "ih2" (MP_TAC o SPECL [`Rval [w2]:bvi_result`; `s2:(C,FFI)bvi_state`;
            `t2:(C,FFI)data_state`; `next_var:num`; `corr:num list`; `F`;
            `live:num list`]) THEN
          ASM_REWRITE_TAC[LENGTH; PAIR_EQ; distinctness "result"] THEN
          DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC [("t2","t3"); ("prog","prog2"); ("pres","pres2"); ("vs","vs2"); ("next_var","nv2"); ("ls","ls2")]) THEN RVEQ_TAC THEN
          DATAPAUX_B2D_PRES_TAC `pres2:((data_v list,data_v)result)option` THEN
          FIRST_ASSUM(MP_TAC o MATCH_MP compile_SING_IMP o
                      check (fun th -> free_in `x2:bvi_exp` (concl th))) THEN
          DISCH_THEN(X_CHOOSE_THEN `tv2:num` SUBST_ALL_TAC) THEN
          SUBGOAL_THEN `?z2. lookup tv2 (data_state_locals (t3:(C,FFI)data_state)) = SOME z2 /\
                             data_to_bvi_v z2 = w2` STRIP_ASSUME_TAC THENL
           [UNDISCH_TAC `var_corr [w2] [tv2]
              (sptree_map data_to_bvi_v (data_state_locals (t3:(C,FFI)data_state)))` THEN
            REWRITE_TAC[var_corr_def; ALL2; data_get_var_def; lookup_map] THEN
            MP_TAC(ISPEC `lookup tv2 (data_state_locals (t3:(C,FFI)data_state))`
                     (cases "option")) THEN
            STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
            MESON_TAC[];
            ALL_TAC] THEN
          FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
            check ((=) `data_to_bvi_v z2 = w2` o concl)) THEN
          ASM_REWRITE_TAC[HD] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
          ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
          REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN TRY (EXISTS_TAC `ls:num option`) THEN
          CASE_REWRITE_TAC[] THEN
          FIRST_ASSUM(ASSUME_TAC o MATCH_MP compile_LESS_EQ o
                      check (fun th -> free_in `x3:bvi_exp` (concl th))) THEN
          MP_TAC(SPECL [`t1:(C,FFI)data_state`; `t2:(C,FFI)data_state`;
            `t3:(C,FFI)data_state`; `n:num`; `next_var:num`; `nv2:num`; `n3:num`;
            `env:bvl_v list`; `corr:num list`; `live:num list`; `z2:data_v`]
            DATAPAUX_B2D_IF_MOVE) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          STRIP_TAC THEN
          ASM_REWRITE_TAC[data_set_var_def; DATAPAUX_B2D_state_rel_fupds] THEN
          REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM];
          REMOVE_THEN "ih2" (MP_TAC o SPECL [`Rerr e2:bvi_result`; `s2:(C,FFI)bvi_state`;
            `t2:(C,FFI)data_state`; `next_var:num`; `corr:num list`; `F`;
            `live:num list`]) THEN
          ASM_REWRITE_TAC[LENGTH; PAIR_EQ] THEN
          DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC [("t2","t3"); ("prog","prog2"); ("pres","pres2"); ("vs","vs2"); ("next_var","nv2"); ("ls","ls2")]) THEN RVEQ_TAC THEN
          DATAPAUX_B2D_PRES_TAC `pres2:((data_v list,data_v)result)option` THEN
          ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN
          REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls2:num option` THEN
          CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC DATAPAUX_B2D_RES_RWS]];
      ASM_CASES_TAC `bvl_Boolv F = data_to_bvi_v z` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `isBool F z /\ ~isBool T z` STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[isBool_eq]; ALL_TAC] THEN
      REMOVE_THEN "ih3" (MP_TAC o SPECL [`[data_to_bvi_v z]`; `s1:(C,FFI)bvi_state`]) THEN
      ASM_REWRITE_TAC[HD] THEN DISCH_THEN(LABEL_TAC "ihx") THEN DISCH_TAC THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP compile_LESS_EQ o
                  check (fun th -> free_in `x2:bvi_exp` (concl th))) THEN
      SUBGOAL_THEN `n <= (n2:num)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `!k. n2 <= k ==> lookup k (data_state_locals (t2:(C,FFI)data_state)) = NONE`
        ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `tail:bool` BOOL_CASES_AX) THEN
      DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[PAIR_EQ] THEN
      REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
      DATAPAUX_B2D_SEQ_NONE_TAC THEN
      REWRITE_TAC[data_evaluate_def; data_get_var_def] THEN ASM_REWRITE_TAC[] THEN
      CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THENL
       [REMOVE_THEN "ihx" (MP_TAC o SPECL [`res:bvi_result`; `s2:(C,FFI)bvi_state`;
          `t2:(C,FFI)data_state`; `n2:num`; `corr:num list`; `T`; `live:num list`]) THEN
        ASM_REWRITE_TAC[LENGTH; ONE; PAIR_EQ] THEN
        DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC [("t2","t3"); ("prog","prog2"); ("pres","pres2"); ("vs","vs2"); ("next_var","nv2"); ("ls","ls2")]) THEN RVEQ_TAC THEN
        DATAPAUX_B2D_PRES_TAC `pres2:((data_v list,data_v)result)option` THEN
        ASM_REWRITE_TAC[PAIR_EQ] THEN
        REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls2:num option` THEN
        CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC DATAPAUX_B2D_RES_RWS;
        MP_TAC(ISPEC `res:bvi_result` (cases "result")) THEN
        DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a2:bvl_v list` SUBST_ALL_TAC)
          (X_CHOOSE_THEN `e2:(exn_or_ret)error_result` SUBST_ALL_TAC)) THENL
         [FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_SING_IMP o
                      check (fun th -> free_in `x3:bvi_exp` (concl th))) THEN
          DISCH_THEN(X_CHOOSE_THEN `w2:bvl_v` SUBST_ALL_TAC) THEN
          REMOVE_THEN "ihx" (MP_TAC o SPECL [`Rval [w2]:bvi_result`; `s2:(C,FFI)bvi_state`;
            `t2:(C,FFI)data_state`; `n2:num`; `corr:num list`; `F`;
            `live:num list`]) THEN
          ASM_REWRITE_TAC[LENGTH; PAIR_EQ; distinctness "result"] THEN
          DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC [("t2","t3"); ("prog","prog2"); ("pres","pres2"); ("vs","vs2"); ("next_var","nv2"); ("ls","ls2")]) THEN RVEQ_TAC THEN
          DATAPAUX_B2D_PRES_TAC `pres2:((data_v list,data_v)result)option` THEN
          FIRST_ASSUM(MP_TAC o MATCH_MP compile_SING_IMP o
                      check (fun th -> free_in `x3:bvi_exp` (concl th))) THEN
          DISCH_THEN(X_CHOOSE_THEN `tv2:num` SUBST_ALL_TAC) THEN
          SUBGOAL_THEN `?z2. lookup tv2 (data_state_locals (t3:(C,FFI)data_state)) = SOME z2 /\
                             data_to_bvi_v z2 = w2` STRIP_ASSUME_TAC THENL
           [UNDISCH_TAC `var_corr [w2] [tv2]
              (sptree_map data_to_bvi_v (data_state_locals (t3:(C,FFI)data_state)))` THEN
            REWRITE_TAC[var_corr_def; ALL2; data_get_var_def; lookup_map] THEN
            MP_TAC(ISPEC `lookup tv2 (data_state_locals (t3:(C,FFI)data_state))`
                     (cases "option")) THEN
            STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
            MESON_TAC[];
            ALL_TAC] THEN
          FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
            check ((=) `data_to_bvi_v z2 = w2` o concl)) THEN
          ASM_REWRITE_TAC[HD] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
          ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
          REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN TRY (EXISTS_TAC `ls:num option`) THEN
          CASE_REWRITE_TAC[] THEN
          MP_TAC(SPECL [`t1:(C,FFI)data_state`; `t2:(C,FFI)data_state`;
            `t3:(C,FFI)data_state`; `n:num`; `n2:num`; `nv2:num`; `nv2:num`;
            `env:bvl_v list`; `corr:num list`; `live:num list`; `z2:data_v`]
            DATAPAUX_B2D_IF_MOVE) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
          STRIP_TAC THEN
          ASM_REWRITE_TAC[data_set_var_def; DATAPAUX_B2D_state_rel_fupds] THEN
          REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM];
          REMOVE_THEN "ihx" (MP_TAC o SPECL [`Rerr e2:bvi_result`; `s2:(C,FFI)bvi_state`;
            `t2:(C,FFI)data_state`; `n2:num`; `corr:num list`; `F`;
            `live:num list`]) THEN
          ASM_REWRITE_TAC[LENGTH; PAIR_EQ] THEN
          DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC [("t2","t3"); ("prog","prog2"); ("pres","pres2"); ("vs","vs2"); ("next_var","nv2"); ("ls","ls2")]) THEN RVEQ_TAC THEN
          DATAPAUX_B2D_PRES_TAC `pres2:((data_v list,data_v)result)option` THEN
          ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN
          REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls2:num option` THEN
          CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC DATAPAUX_B2D_RES_RWS]];
      DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o REWRITE_RULE[PAIR_EQ]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC]];
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`Rerr e:bvi_result`; `s1:(C,FFI)bvi_state`;
      `t1:(C,FFI)data_state`; `n:num`; `corr:num list`; `F`; `live:num list`]) THEN
    ASM_REWRITE_TAC[LENGTH; PAIR_EQ] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN RVEQ_TAC THEN
    DATAPAUX_B2D_PRES_TAC `pres:((data_v list,data_v)result)option` THEN
    BOOL_CASES_TAC `tail:bool` THEN REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
    DATAPAUX_B2D_SEQ_SOME_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls:num option` THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC DATAPAUX_B2D_RES_RWS]
);;

(* HOL4: compile_correct[Let] *)
let DATAPAUX_B2D_CC_LET = prove
 (el 4 DATAPAUX_B2D_CC_CASES,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih2") (LABEL_TAC "ih1")) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  MP_TAC(ISPEC `bvi_evaluate (xs,env,s:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:bvi_result` (X_CHOOSE_THEN `s1:(C,FFI)bvi_state`
    ASSUME_TAC)) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `bvi_to_data_compile n corr F live xs` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:data_prog` (X_CHOOSE_THEN `y1:num list # num` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `y1:num list # num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:num list` (X_CHOOSE_THEN `n1:num` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `bvi_to_data_compile n1 (APPEND v1 corr) tail live [x2]` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:data_prog` (X_CHOOSE_THEN `y2:num list # num` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `y2:num list # num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `v2:num list` (X_CHOOSE_THEN `n2:num` SUBST_ALL_TAC)) THEN
  ONCE_REWRITE_TAC[bvi_to_data_compile_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  MP_TAC(ISPEC `r1:bvi_result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:bvl_v list` SUBST_ALL_TAC)
                              (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THENL
   [REMOVE_THEN "ih1" (MP_TAC o SPECL [`Rval a:bvi_result`; `s1:(C,FFI)bvi_state`;
      `t1:(C,FFI)data_state`; `n:num`; `corr:num list`; `F`; `live:num list`]) THEN
    ASM_REWRITE_TAC[LENGTH; PAIR_EQ; distinctness "result"] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN RVEQ_TAC THEN
    DATAPAUX_B2D_PRES_TAC `pres:((data_v list,data_v)result)option` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `ALL (\n. ~(lookup n (data_state_locals (t2:(C,FFI)data_state)) = NONE))
                      live` ASSUME_TAC THENL
     [UNDISCH_TAC `ALL (\n. ~(lookup n (data_state_locals (t1:(C,FFI)data_state)) = NONE))
                     live` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN DATAPAUX_LOOKUP_MESON_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(?v. (res:bvi_result) = Rerr (Rraise (Exn v)))
                  ==> ~(data_jump_exc (t2:(C,FFI)data_state) = NONE)` ASSUME_TAC THENL
     [DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `var_corr (APPEND a env) (APPEND vs corr)
                    (sptree_map data_to_bvi_v (data_state_locals (t2:(C,FFI)data_state)))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC DATAPAUX_B2D_var_corr_APPEND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DATAPAUX_B2D_var_corr_LENGTH o
      check ((=) `var_corr a vs
        (sptree_map data_to_bvi_v (data_state_locals (t2:(C,FFI)data_state)))` o concl)) THEN
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`a:bvl_v list`; `s1:(C,FFI)bvi_state`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`res:bvi_result`; `s2:(C,FFI)bvi_state`;
      `t2:(C,FFI)data_state`; `next_var:num`; `APPEND vs corr:num list`; `tail:bool`;
      `live:num list`]) THEN
    ASM_REWRITE_TAC[LENGTH; ONE; PAIR_EQ] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC [("t2","t3"); ("prog","prog2"); ("pres","pres2"); ("vs","vs2"); ("next_var","nv2"); ("ls","ls2")]) THEN RVEQ_TAC THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
    DATAPAUX_B2D_SEQ_NONE_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls2:num option` THEN
    DATAPAUX_B2D_PRES_TAC `pres2:((data_v list,data_v)result)option` THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FIRST [ASM_ARITH_TAC;
           MATCH_MP_TAC DATAPAUX_B2D_var_corr_APPEND_IMP THEN
           MAP_EVERY EXISTS_TAC [`a:bvl_v list`; `vs:num list`] THEN ASM_REWRITE_TAC[];
           REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
           ASM_REWRITE_TAC[MEM_APPEND] THEN CONJ_TAC THENL
            [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
             STRIP_TAC THEN DISJ2_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
             ASM_REWRITE_TAC[]];
           DATAPAUX_B2D_JUMP_TAC];
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`Rerr e:bvi_result`; `s1:(C,FFI)bvi_state`;
      `t1:(C,FFI)data_state`; `n:num`; `corr:num list`; `F`; `live:num list`]) THEN
    ASM_REWRITE_TAC[LENGTH; PAIR_EQ] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN RVEQ_TAC THEN
    DATAPAUX_B2D_PRES_TAC `pres:((data_v list,data_v)result)option` THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
    DATAPAUX_B2D_SEQ_SOME_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls:num option` THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC DATAPAUX_B2D_RES_RWS]
);;

(* HOL4: compile_correct[Raise] *)
let DATAPAUX_B2D_CC_RAISE = prove
 (el 5 DATAPAUX_B2D_CC_CASES,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  MP_TAC(ISPEC `bvi_evaluate ([x1],env,s:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:bvi_result` (X_CHOOSE_THEN `s0:(C,FFI)bvi_state`
    ASSUME_TAC)) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r0:bvi_result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:bvl_v list` SUBST_ALL_TAC)
                              (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN REPEAT DISCH_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_SING_IMP) THEN
    DISCH_THEN(X_CHOOSE_THEN `w:bvl_v` SUBST_ALL_TAC) THEN
    REMOVE_THEN "ih" (MP_TAC o SPECL [`Rval [w]:bvi_result`; `s0:(C,FFI)bvi_state`;
      `t1:(C,FFI)data_state`; `n:num`; `corr:num list`; `F`; `live:num list`]) THEN
    ASM_REWRITE_TAC[distinctness "result"; LENGTH] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN
    DATAPAUX_B2D_PRES_TAC `pres:((data_v list,data_v)result)option` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP compile_SING_IMP) THEN
    DISCH_THEN(X_CHOOSE_THEN `tv:num` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `var_corr [w] [tv] (sptree_map data_to_bvi_v (data_state_locals (t2:(C,FFI)data_state)))` THEN
    REWRITE_TAC[var_corr_def; ALL2; data_get_var_def; lookup_map] THEN
    MP_TAC(ISPEC `lookup tv (data_state_locals (t2:(C,FFI)data_state))` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    SUBGOAL_THEN `?t3. data_jump_exc (t2:(C,FFI)data_state) = SOME t3` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[option_CASES]; ALL_TAC] THEN
    REWRITE_TAC[bvi_to_data_compile_def; LET_DEF; LET_END_DEF] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
    DATAPAUX_B2D_SEQ_NONE_TAC THEN
    REWRITE_TAC[data_evaluate_def; HD; data_get_var_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
    EXISTS_TAC `data_state_locals_size (t3:(C,FFI)data_state)` THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC(data_to_bvi_result_def :: DATAPAUX_B2D_RES_RWS) THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[DATAPAUX_B2D_state_rel_jump_exc];
      MATCH_MP_TAC DATAPAUX_B2D_jump_exc_restore THEN
      EXISTS_TAC `t2:(C,FFI)data_state` THEN ASM_REWRITE_TAC[]];
    REMOVE_THEN "ih" (MP_TAC o SPECL [`Rerr e:bvi_result`; `s0:(C,FFI)bvi_state`;
      `t1:(C,FFI)data_state`; `n:num`; `corr:num list`; `F`; `live:num list`]) THEN
    ASM_REWRITE_TAC[LENGTH] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN
    DATAPAUX_B2D_PRES_TAC `pres:((data_v list,data_v)result)option` THEN
    REWRITE_TAC[bvi_to_data_compile_def; LET_DEF; LET_END_DEF] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
    DATAPAUX_B2D_SEQ_SOME_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls:num option` THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC DATAPAUX_B2D_RES_RWS]
);;

(* HOL4: compile_correct[Return] *)
let DATAPAUX_B2D_CC_RETURN = prove
 (el 6 DATAPAUX_B2D_CC_CASES,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  MP_TAC(ISPEC `bvi_evaluate (xs,env,s:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:bvi_result` (X_CHOOSE_THEN `s0:(C,FFI)bvi_state`
    ASSUME_TAC)) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r0:bvi_result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:bvl_v list` SUBST_ALL_TAC)
                              (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN REPEAT DISCH_TAC
 THENL
   [REMOVE_THEN "ih" (MP_TAC o SPECL [`Rval a:bvi_result`; `s0:(C,FFI)bvi_state`;
      `t1:(C,FFI)data_state`; `n:num`; `corr:num list`; `F`; `live:num list`]) THEN
    ASM_REWRITE_TAC[distinctness "result"] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN
    DATAPAUX_B2D_PRES_TAC `pres:((data_v list,data_v)result)option` THEN
    REWRITE_TAC[bvi_to_data_compile_def; LET_DEF; LET_END_DEF] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    MP_TAC(ISPECL [`vs:num list`; `a:bvl_v list`;
                   `data_state_locals (t2:(C,FFI)data_state)`] get_vars_lift_thm) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z:data_v list` STRIP_ASSUME_TAC) THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
    DATAPAUX_B2D_SEQ_NONE_TAC THEN
    REWRITE_TAC[data_evaluate_def] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC(DATAPAUX_B2D_state_rel_fupds :: data_flush_state_def ::
                    data_state_INFO.ri_accfupds :: K_THM :: DATAPAUX_B2D_RES_RWS);
    REMOVE_THEN "ih" (MP_TAC o SPECL [`Rerr e:bvi_result`; `s0:(C,FFI)bvi_state`;
      `t1:(C,FFI)data_state`; `n:num`; `corr:num list`; `F`; `live:num list`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN
    DATAPAUX_B2D_PRES_TAC `pres:((data_v list,data_v)result)option` THEN
    REWRITE_TAC[bvi_to_data_compile_def; LET_DEF; LET_END_DEF] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
    DATAPAUX_B2D_SEQ_SOME_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls:num option` THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC DATAPAUX_B2D_RES_RWS]
);;

(* HOL4: compile_correct[Op] *)
let DATAPAUX_B2D_CC_OP = prove
 (el 7 DATAPAUX_B2D_CC_CASES,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih1") THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  MP_TAC(ISPEC `bvi_evaluate (xs,env,s:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:bvi_result` (X_CHOOSE_THEN `s1:(C,FFI)bvi_state`
    ASSUME_TAC)) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `bvi_to_data_compile n corr F live xs` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:data_prog` (X_CHOOSE_THEN `y1:num list # num` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `y1:num list # num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:num list` (X_CHOOSE_THEN `n1:num` SUBST_ALL_TAC)) THEN
  ONCE_REWRITE_TAC[bvi_to_data_compile_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r1:bvi_result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:bvl_v list` SUBST_ALL_TAC)
                              (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THENL
   [REMOVE_THEN "ih1" (MP_TAC o SPECL [`Rval a:bvi_result`; `s1:(C,FFI)bvi_state`;
      `t1:(C,FFI)data_state`; `n:num`; `corr:num list`; `F`; `live:num list`]) THEN
    ASM_REWRITE_TAC[LENGTH; PAIR_EQ; distinctness "result"] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN RVEQ_TAC THEN
    DATAPAUX_B2D_PRES_TAC `pres:((data_v list,data_v)result)option` THEN
    MP_TAC(ISPECL [`vs:num list`; `a:bvl_v list`; `data_state_locals (t2:(C,FFI)data_state)`]
                  get_vars_lift_thm) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `zz:data_v list` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP get_vars_reverse) THEN
    SUBGOAL_THEN `domain (list_to_num_set (APPEND (APPEND (REVERSE vs) live) corr)) SUBSET
                  domain (data_state_locals (t2:(C,FFI)data_state))` ASSUME_TAC THENL
     [REWRITE_TAC[domain_list_to_num_set2; SET_OF_LIST_APPEND; UNION_SUBSET;
                  LIST_TO_SET_REVERSE] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC DATAPAUX_B2D_var_corr_domain THEN
        EXISTS_TAC `MAP data_to_bvi_v zz` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC DATAPAUX_B2D_ALL_domain THEN
        UNDISCH_TAC `ALL (\n. ~(lookup n (data_state_locals (t1:(C,FFI)data_state)) = NONE))
                       live` THEN
        REWRITE_TAC[GSYM ALL_MEM] THEN DATAPAUX_LOOKUP_MESON_TAC;
        MATCH_MP_TAC DATAPAUX_B2D_var_corr_domain THEN
        EXISTS_TAC `env:bvl_v list` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[MAP_REVERSE] THEN
    MP_TAC(ISPEC `bvi_do_app op (MAP data_to_bvi_v (REVERSE zz)) (s1:(C,FFI)bvi_state)`
             (cases "result")) THEN
    DISCH_THEN(DISJ_CASES_THEN2
      (X_CHOOSE_THEN `vr:bvl_v#(C,FFI)bvi_state` ASSUME_TAC)
      (X_CHOOSE_THEN `err:(exn_or_ret)error_result` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
     [MP_TAC(ISPEC `vr:bvl_v#(C,FFI)bvi_state` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `v:bvl_v` (X_CHOOSE_THEN `r':(C,FFI)bvi_state`
        SUBST_ALL_TAC)) THEN
      CASE_REWRITE_TAC[PAIR_EQ] THEN
      DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      MP_TAC(SPECL [`next_var:num`; `op:clos_op`; `REVERSE vs:num list`; `live:num list`;
                    `corr:num list`; `t2:(C,FFI)data_state`; `s1:(C,FFI)bvi_state`;
                    `REVERSE zz:data_v list`; `v:bvl_v`; `r':(C,FFI)bvi_state`]
                   DATAPAUX_B2D_iAssign_any_Rval) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `pv:data_v` (X_CHOOSE_THEN `t3:(C,FFI)data_state`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
            (STRIP_ASSUME_TAC o MATCH_MP DATAPAUX_B2D_cut_facts) STRIP_ASSUME_TAC)))))) THEN
      MP_TAC(SPEC `tail:bool` BOOL_CASES_AX) THEN
      DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[] THEN
      REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THENL
       [SUBGOAL_THEN `data_evaluate (data_Seq prog (iAssign next_var op (REVERSE vs) live corr),
                        t1:(C,FFI)data_state) = (NONE,data_set_var next_var pv t3)`
          ASSUME_TAC THENL
         [DATAPAUX_B2D_SEQ_NONE_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DATAPAUX_B2D_SEQ_NONE_TAC THEN
        REWRITE_TAC[data_evaluate_def; data_get_vars_def; data_get_var_def; data_set_var_def;
                    data_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN
        CASE_REWRITE_TAC[PAIR_EQ] THEN
        REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN TRY (EXISTS_TAC `ls:num option`) THEN
        CASE_REWRITE_TAC[] THEN
        ASM_REWRITE_TAC(DATAPAUX_B2D_state_rel_fupds :: data_flush_state_def ::
                        data_state_INFO.ri_accfupds :: K_THM :: data_to_bvi_result_def :: MAP ::
                        DATAPAUX_B2D_RES_RWS);
        DATAPAUX_B2D_SEQ_NONE_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
        REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls:num option` THEN
        CASE_REWRITE_TAC[] THEN
        MP_TAC(SPECL [`t1:(C,FFI)data_state`; `t2:(C,FFI)data_state`; `t3:(C,FFI)data_state`;
                      `n:num`; `next_var:num`; `env:bvl_v list`; `corr:num list`;
                      `live:num list`; `pv:data_v`] DATAPAUX_B2D_OP_FACTS) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[DATAPAUX_B2D_state_rel_fupds]];
      CASE_REWRITE_TAC[PAIR_EQ] THEN
      DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[injectivity "result"]) THEN
      MP_TAC(SPECL [`next_var:num`; `op:clos_op`; `REVERSE vs:num list`; `live:num list`;
                    `corr:num list`; `t2:(C,FFI)data_state`; `s1:(C,FFI)bvi_state`;
                    `REVERSE zz:data_v list`; `err:(exn_or_ret)error_result`]
                   DATAPAUX_B2D_iAssign_Rerr) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:final_event` (X_CHOOSE_THEN `t3:(C,FFI)data_state`
        (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THEN
      SUBGOAL_THEN `data_evaluate (data_Seq prog (iAssign next_var op (REVERSE vs) live corr),
                      t1:(C,FFI)data_state) = (SOME (Rerr (Rabort (Rffi_error x))),t3)`
        ASSUME_TAC THENL
       [DATAPAUX_B2D_SEQ_NONE_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(SPEC `tail:bool` BOOL_CASES_AX) THEN
      DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[] THEN
      REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
      TRY DATAPAUX_B2D_SEQ_SOME_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
      REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls:num option` THEN
      CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC(data_to_bvi_result_def :: DATAPAUX_B2D_RES_RWS)];
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`Rerr e:bvi_result`; `s1:(C,FFI)bvi_state`;
      `t1:(C,FFI)data_state`; `n:num`; `corr:num list`; `F`; `live:num list`]) THEN
    ASM_REWRITE_TAC[LENGTH; PAIR_EQ] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN RVEQ_TAC THEN
    DATAPAUX_B2D_PRES_TAC `pres:((data_v list,data_v)result)option` THEN
    FIRST_ASSUM(ASSUME_TAC o SPEC `iAssign next_var op (REVERSE vs) live corr` o
                MATCH_MP DATAPAUX_B2D_Seq_SOME) THEN
    MP_TAC(SPEC `tail:bool` BOOL_CASES_AX) THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
    TRY DATAPAUX_B2D_SEQ_SOME_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls:num option` THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC DATAPAUX_B2D_RES_RWS]);;

(* HOL4: compile_correct[Tick] *)
let DATAPAUX_B2D_CC_TICK = prove
 (el 8 DATAPAUX_B2D_CC_CASES,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  MP_TAC(ISPEC `bvi_to_data_compile n corr tail live [x]` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:data_prog` (X_CHOOSE_THEN `y:num list # num` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `y:num list # num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:num list` (X_CHOOSE_THEN `n1:num` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[bvi_to_data_compile_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  ASM_CASES_TAC `bvi_state_clock (s:(C,FFI)bvi_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    SUBGOAL_THEN `data_state_clock (t1:(C,FFI)data_state) = 0` ASSUME_TAC THENL
     [ASM_MESON_TAC[bvi_to_dataProof_state_rel_def]; ALL_TAC] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN REWRITE_TAC[DATAPAUX_B2D_Seq_Tick] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
    CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC(DATAPAUX_B2D_state_rel_fupds :: data_to_bvi_result_def ::
                    DATAPAUX_B2D_RES_RWS);
    DISCH_TAC THEN
    SUBGOAL_THEN `~(data_state_clock (t1:(C,FFI)data_state) = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[bvi_to_dataProof_state_rel_def]; ALL_TAC] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN REWRITE_TAC[DATAPAUX_B2D_Seq_Tick] THEN
    ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "ih" (MP_TAC o SPECL [`res:bvi_result`; `s2:(C,FFI)bvi_state`;
      `data_dec_clock (t1:(C,FFI)data_state)`; `n:num`; `corr:num list`; `tail:bool`;
      `live:num list`] o C MP (ASSUME `~(bvi_state_clock (s:(C,FFI)bvi_state) = 0)`)) THEN
    ASM_SIMP_TAC[DATAPAUX_B2D_state_rel_dec_clock; LENGTH] THEN
    REWRITE_TAC[data_dec_clock_def; data_state_INFO.ri_accfupds; K_THM; jump_exc_NONE] THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
    EXISTS_TAC `ls:num option` THEN ASM_REWRITE_TAC[]]
);;

(* HOL4: compile_correct[Force] *)
let DATAPAUX_B2D_CC_FORCE = prove
 (el 9 DATAPAUX_B2D_CC_CASES,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `n < LENGTH (env:bvl_v list)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; DATAPAUX_B2D_TERR_TAC] THEN
  MP_TAC(ISPECL [`env:bvl_v list`; `corr:num list`;
                 `sptree_map data_to_bvi_v (data_state_locals (t1:(C,FFI)data_state))`; `n:num`]
                DATAPAUX_B2D_var_corr_EL) THEN
  ASM_REWRITE_TAC[data_get_var_def; lookup_map] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?z. lookup (EL n corr) (data_state_locals (t1:(C,FFI)data_state)) = SOME z /\
                    EL n env = data_to_bvi_v z` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `lookup (EL n corr) (data_state_locals (t1:(C,FFI)data_state))`
            (cases "option")) THEN
    STRIP_TAC THEN
    UNDISCH_TAC `OPTION_MAP data_to_bvi_v (lookup (EL n corr)
                   (data_state_locals (t1:(C,FFI)data_state))) = SOME (EL n env)` THEN
    ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `bvi_dest_thunk (data_to_bvi_v z) (bvi_state_refs (s:(C,FFI)bvi_state))`
           (cases "bvi_dest_thunk_ret")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  TRY (DATAPAUX_B2D_TERR_TAC THEN NO_TAC) THEN
  MP_TAC(ISPECL [`s:(C,FFI)bvi_state`; `t1:(C,FFI)data_state`; `z:data_v`; `a0:thunk_mode`;
                 `a1:bvl_v`] state_rel_dest_thunk) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v':data_v` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rand(concl th) = `a1:bvl_v`)) THEN
  SUBGOAL_THEN `EL n corr < n'` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `!k. n' <= k ==> lookup k (data_state_locals (t1:(C,FFI)data_state)) = NONE` THEN
    DISCH_THEN(MP_TAC o SPEC `EL n (corr:num list)`) THEN ASM_REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  SUBGOAL_THEN `MAX (n' + 1) (EL n corr + 1) = n' + 1` ASSUME_TAC THENL
   [REWRITE_TAC[MAX] THEN COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bvi_to_data_compile_def; LET_DEF; LET_END_DEF; any_el_ALT] THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN
  MP_TAC(ISPEC `a0:thunk_mode` (cases "thunk_mode")) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
    REWRITE_TAC[data_evaluate_def; data_get_var_def] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(SPEC `tail:bool` BOOL_CASES_AX) THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC(DATAPAUX_B2D_state_rel_fupds :: data_flush_state_def ::
                      data_state_INFO.ri_accfupds :: K_THM :: data_to_bvi_result_def :: MAP ::
                      DATAPAUX_B2D_RES_RWS);
      MP_TAC(ISPECL [`t1:(C,FFI)data_state`; `env:bvl_v list`; `corr:num list`; `live:num list`]
                    DATAPAUX_B2D_cut_live_corr) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
      REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN CASE_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`t1:(C,FFI)data_state`;
        `data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals t1)
            (list_to_num_set (APPEND live corr))))) (t1:(C,FFI)data_state)`;
        `n':num`; `env:bvl_v list`; `corr:num list`; `live:num list`; `v':data_v`]
        DATAPAUX_B2D_FORCE_FACTS) THEN
      ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[data_set_var_def; DATAPAUX_B2D_state_rel_fupds] THEN
      ALL_TAC];
    MP_TAC(ISPEC `bvl_find_code (SOME force_loc) [data_to_bvi_v z; data_to_bvi_v v']
                    (bvi_state_code (s:(C,FFI)bvi_state))` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2
      (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[] THEN DATAPAUX_B2D_TERR_TAC)
      (X_CHOOSE_THEN `ae:bvl_v list # bvi_exp` ASSUME_TAC)) THEN
    MP_TAC(ISPEC `ae:bvl_v list # bvi_exp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `args:bvl_v list` (X_CHOOSE_THEN `exp:bvi_exp` SUBST_ALL_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:(C,FFI)bvi_state`; `t1:(C,FFI)data_state`; `SOME (force_loc:num)`;
                   `[z; v']:data_v list`; `args:bvl_v list`; `exp:bvi_exp`]
                  bvi_to_dataProof_find_code_lemma) THEN
    ASM_REWRITE_TAC[MAP] THEN
    DISCH_THEN(X_CHOOSE_THEN `args':data_v list` (X_CHOOSE_THEN `ss:num option`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
    SUBGOAL_THEN `data_state_clock (t1:(C,FFI)data_state) = bvi_state_clock (s:(C,FFI)bvi_state)`
      ASSUME_TAC THENL
     [UNDISCH_TAC `bvi_to_dataProof_state_rel (s:(C,FFI)bvi_state) (t1:(C,FFI)data_state)` THEN
      SIMP_TAC[bvi_to_dataProof_state_rel_def];
      ALL_TAC] THEN
    SUBGOAL_THEN `bvi_to_dataProof_state_rel (bvi_dec_clock 1 s) (data_dec_clock t1:(C,FFI)data_state)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC DATAPAUX_B2D_state_rel_dec_clock THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `bvi_state_clock (s:(C,FFI)bvi_state) = 0` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
      SUBGOAL_THEN `bvi_state_clock_fupd (K 0) s = (s:(C,FFI)bvi_state)` SUBST1_TAC THENL
       [REWRITE_TAC[bvi_state_component_equality; bvi_state_INFO.ri_accfupds; K_THM] THEN
        ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `data_dec_clock t1 = (t1:(C,FFI)data_state)` ASSUME_TAC THENL
       [REWRITE_TAC[data_dec_clock_def; data_state_component_equality;
                    data_state_INFO.ri_accfupds; K_THM] THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      REWRITE_TAC[data_evaluate_def; data_get_var_def] THEN ASM_REWRITE_TAC[] THEN
      CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      MP_TAC(SPEC `tail:bool` BOOL_CASES_AX) THEN
      DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
       [REWRITE_TAC[PAIR_EQ] THEN REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN CASE_REWRITE_TAC[] THEN
        ASM_REWRITE_TAC(DATAPAUX_B2D_state_rel_fupds :: data_to_bvi_result_def ::
                        DATAPAUX_B2D_RES_RWS);
        MP_TAC(ISPECL [`t1:(C,FFI)data_state`; `env:bvl_v list`; `corr:num list`;
                       `live:num list`] DATAPAUX_B2D_cut_live_corr) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[PAIR_EQ] THEN REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN CASE_REWRITE_TAC[] THEN
        ASM_REWRITE_TAC(DATAPAUX_B2D_state_rel_fupds :: DATAPAUX_B2D_state_rel_call_push ::
                        data_to_bvi_result_def :: DATAPAUX_B2D_RES_RWS)];
      DISCH_THEN(MP_TAC o C CONJ (ASSUME `~(res:bvi_result = Rerr (Rabort Rtype_error))`)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP DATAPAUX_B2D_force_res) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
      REMOVE_THEN "ih" (MP_TAC o SPECL [`data_to_bvi_v z`; `data_to_bvi_v v'`; `exp:bvi_exp`;
                                        `MAP data_to_bvi_v args'`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(SPEC `tail:bool` BOOL_CASES_AX) THEN
      DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[] THENL
       [DISCH_THEN(MP_TAC o SPECL [`res:bvi_result`; `s2:(C,FFI)bvi_state`;
          `data_call_env args' ss (data_dec_clock (t1:(C,FFI)data_state))`;
          `LENGTH (args':data_v list)`; `COUNT_LIST (LENGTH (args':data_v list))`; `T`;
          `[]:num list`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[DATAPAUX_B2D_state_rel_call_push; LENGTH; ONE; ALL] THEN
          REWRITE_TAC[data_call_env_def; data_dec_clock_def; LET_DEF; LET_END_DEF;
                      data_state_INFO.ri_accfupds; K_THM; jump_exc_NONE;
                      DATAPAUX_B2D_var_corr_fromList] THEN
          ASM_SIMP_TAC[lookup_fromList_outside];
          ALL_TAC] THEN
        DISCH_THEN(MP_TAC o MATCH_MP DATAPAUX_B2D_CALLEE) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `r:(data_v list,data_v)result`
          (X_CHOOSE_THEN `t3:(C,FFI)data_state`
          (X_CHOOSE_THEN `ls3:num option` STRIP_ASSUME_TAC))) THEN
        REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
        REWRITE_TAC[data_evaluate_def; data_get_var_def] THEN ASM_REWRITE_TAC[] THEN
        CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
        ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
        ASM_REWRITE_TAC[bvi_to_data_compile_exp_def] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
        REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls3:num option` THEN
        CASE_REWRITE_TAC[] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[data_call_env_def; data_dec_clock_def; LET_DEF; LET_END_DEF;
                                    data_state_INFO.ri_accfupds; K_THM]) THEN
        ASM_REWRITE_TAC[] THEN DATAPAUX_FAST_MESON_TAC[];
        DISCH_THEN(MP_TAC o SPECL [`res:bvi_result`; `s2:(C,FFI)bvi_state`;
          `data_call_env args' ss (data_push_env (mk_wf (sptree_inter (data_state_locals t1)
             (list_to_num_set (APPEND live corr)))) F (data_dec_clock (t1:(C,FFI)data_state)))`;
          `LENGTH (args':data_v list)`; `COUNT_LIST (LENGTH (args':data_v list))`; `T`;
          `[]:num list`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[DATAPAUX_B2D_state_rel_call_push; LENGTH; ONE; ALL] THEN
          REPEAT CONJ_TAC THENL
           [REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF;
                        data_state_INFO.ri_accfupds; K_THM; DATAPAUX_B2D_var_corr_fromList];
            REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF;
                        data_state_INFO.ri_accfupds; K_THM] THEN
            SIMP_TAC[lookup_fromList_outside];
            DISCH_TAC THEN MATCH_MP_TAC DATAPAUX_B2D_jump_push THEN
            UNDISCH_TAC `(?v. (res:bvi_result) = Rerr (Rraise (Exn v)))
                         ==> ~(data_jump_exc (t1:(C,FFI)data_state) = NONE)` THEN
            ASM_REWRITE_TAC[]];
          ALL_TAC] THEN
        DISCH_THEN(MP_TAC o MATCH_MP DATAPAUX_B2D_CALLEE) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `r:(data_v list,data_v)result`
          (X_CHOOSE_THEN `t3:(C,FFI)data_state`
          (X_CHOOSE_THEN `ls3:num option` STRIP_ASSUME_TAC))) THEN
        REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
        MP_TAC(ISPECL [`t1:(C,FFI)data_state`; `env:bvl_v list`; `corr:num list`;
                       `live:num list`] DATAPAUX_B2D_cut_live_corr) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        REWRITE_TAC[data_evaluate_def; data_get_var_def] THEN ASM_REWRITE_TAC[] THEN
        CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
        ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
        ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
        REWRITE_TAC[data_fix_clock_evaluate; bvi_to_data_compile_exp_def] THEN
        ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
        SUBGOAL_THEN `data_to_bvi_result r = (res:bvi_result)` ASSUME_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[data_call_env_def; data_push_env_def; data_dec_clock_def;
                                    LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM]) THEN
        MP_TAC(ISPEC `r:(data_v list,data_v)result` (cases "result")) THEN
        DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `xs:data_v list` SUBST_ALL_TAC)
                                    (X_CHOOSE_THEN `e:(data_v)error_result` SUBST_ALL_TAC)) THEN
        CASE_REWRITE_TAC[] THENL
         [RULE_ASSUM_TAC(REWRITE_RULE[data_to_bvi_result_def]) THEN
          FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rand(concl th) = `res:bvi_result`)) THEN
          FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_SING_IMP) THEN
          REWRITE_TAC[MAP_EQ_SING] THEN
          DISCH_THEN(X_CHOOSE_THEN `w:bvl_v` (X_CHOOSE_THEN `x:data_v`
            (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC))) THEN
          SUBGOAL_THEN `data_state_stack (t3:(C,FFI)data_state) =
                        CONS (data_Env (data_state_locals_size (t1:(C,FFI)data_state))
                          (mk_wf (sptree_inter (data_state_locals t1)
                                    (list_to_num_set (APPEND live corr)))))
                          (data_state_stack t1) /\
                        data_state_handler t3 = data_state_handler t1` STRIP_ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
                                                    is_disj (lhand (concl th)))) THEN
            REWRITE_TAC(MAP :: DATAPAUX_B2D_RES_RWS) THEN MESON_TAC[];
            ALL_TAC] THEN
          REWRITE_TAC[LENGTH; HD; data_pop_env_def; ARITH_RULE `SUC 0 = 1`] THEN
          ASM_REWRITE_TAC[] THEN
          CASE_REWRITE_TAC[PAIR_EQ] THEN
          REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN CASE_REWRITE_TAC[] THEN
          MP_TAC(ISPECL [`t1:(C,FFI)data_state`;
            `data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals (t1:(C,FFI)data_state))
                (list_to_num_set (APPEND live corr)))))
             (data_state_stack_fupd (K (data_state_stack t1))
               (data_state_locals_size_fupd (K (data_state_locals_size t1))
                  (t3:(C,FFI)data_state)))`;
            `n':num`; `env:bvl_v list`; `corr:num list`; `live:num list`; `x:data_v`]
            DATAPAUX_B2D_FORCE_FACTS) THEN
          ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[MAP] THEN
          REWRITE_TAC[data_set_var_def; DATAPAUX_B2D_state_rel_fupds;
                      data_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[PAIR_EQ] THEN REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
          EXISTS_TAC `ls3:num option` THEN CASE_REWRITE_TAC[] THEN
          MP_TAC(ISPEC `e:(data_v)error_result` (cases "error_result")) THEN
          DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `ev:data_v` SUBST_ALL_TAC)
                                      (X_CHOOSE_THEN `ab:abort` SUBST_ALL_TAC)) THEN
          RULE_ASSUM_TAC(REWRITE_RULE[data_to_bvi_result_def]) THEN
          FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rand(concl th) = `res:bvi_result`)) THEN
          ASM_REWRITE_TAC(data_to_bvi_result_def :: DATAPAUX_B2D_RES_RWS) THEN
          MATCH_MP_TAC DATAPAUX_B2D_jump_Env THEN
          MAP_EVERY EXISTS_TAC [`data_state_locals_size (t1:(C,FFI)data_state)`;
            `mk_wf (sptree_inter (data_state_locals (t1:(C,FFI)data_state))
                          (list_to_num_set (APPEND live corr)))`] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp (concl th) &&
             can (find_term (fun t -> try fst(dest_const t) = "data_jump_exc" with _ -> false))
                 (rand (concl th)))) THEN
          REWRITE_TAC DATAPAUX_B2D_RES_RWS]]]]);;

let DATAPAUX_B2D_state_rel_ticks = prove
 (`!(s:(C,FFI)bvi_state) (t:(C,FFI)data_state) k.
     bvi_to_dataProof_state_rel s t
     ==> bvi_to_dataProof_state_rel (bvi_dec_clock (k + 1) s)
           (data_dec_clock (ITER k data_dec_clock t))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_to_dataProof_state_rel_def; bvi_dec_clock_def; data_dec_clock_def;
              funpow_dec_clock_clock; bvi_state_INFO.ri_accfupds; data_state_INFO.ri_accfupds;
              K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let DATAPAUX_B2D_state_rel_clock = prove
 (`!(s:(C,FFI)bvi_state) (t:(C,FFI)data_state) c.
     bvi_to_dataProof_state_rel s t
     ==> bvi_to_dataProof_state_rel (bvi_state_clock_fupd (K c) s)
           (data_state_clock_fupd (K c) t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_to_dataProof_state_rel_def; bvi_state_INFO.ri_accfupds;
              data_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let DATAPAUX_B2D_set_vars_sing = prove
 (`!n x (t:(C,FFI)data_state). data_set_vars [n] [x] t = data_set_var n x t`,
  REWRITE_TAC[data_set_vars_def; data_set_var_def; ZIP; fromAList_def; union_insert_LN]);;

(* a call (or a call followed by c3) whose clock runs out before the callee *)
let DATAPAUX_B2D_call_timeout = prove
 (`!(s0:(C,FFI)bvi_state) (t2:(C,FFI)data_state) ticks ret dest vs h zs args' prog ss.
     bvi_to_dataProof_state_rel s0 t2 /\ bvi_state_clock s0 < ticks + 1 /\
     data_get_vars vs (data_state_locals t2) = SOME zs /\
     data_find_code dest zs (data_state_code t2) (data_state_stack_frame_sizes t2) =
       SOME (args',prog,ss) /\
     (ret = NONE /\ h = NONE \/
      (?ns names. ret = SOME (ns,names) /\ ALL_DISTINCT ns /\
                  domain names SUBSET domain (data_state_locals t2)))
     ==> !c3. ?t3.
           data_evaluate (mk_ticks ticks (data_Call ret dest vs h),t2) =
             (SOME (Rerr (Rabort Rtimeout_error)),t3) /\
           data_evaluate (mk_ticks ticks (data_Seq (data_Call ret dest vs h) c3),t2) =
             (SOME (Rerr (Rabort Rtimeout_error)),t3) /\
           bvi_to_dataProof_state_rel (bvi_state_clock_fupd (K 0) s0) t3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN `data_state_clock (t2:(C,FFI)data_state) = bvi_state_clock (s0:(C,FFI)bvi_state)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_to_dataProof_state_rel (s0:(C,FFI)bvi_state) (t2:(C,FFI)data_state)` THEN
    SIMP_TAC[bvi_to_dataProof_state_rel_def]; ALL_TAC] THEN
  REWRITE_TAC[evaluate_mk_ticks] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC DATAPAUX_B2D_state_rel_clock THEN
    ASM_REWRITE_TAC[DATAPAUX_B2D_state_rel_fupds];
    ALL_TAC] THEN
  SUBGOAL_THEN `ITER ticks data_dec_clock t2 = data_state_clock_fupd (K 0) (t2:(C,FFI)data_state)`
    SUBST1_TAC THENL
   [REWRITE_TAC[funpow_dec_clock_clock] THEN ASM_REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?t3. data_evaluate (data_Call ret dest vs h,
                       data_state_clock_fupd (K 0) (t2:(C,FFI)data_state)) =
                     (SOME (Rerr (Rabort Rtimeout_error)),t3) /\
                     bvi_to_dataProof_state_rel (bvi_state_clock_fupd (K 0) s0) t3`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[data_evaluate_def] THEN
    ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[data_cut_env_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
    REWRITE_TAC[DATAPAUX_B2D_state_rel_fupds; DATAPAUX_B2D_state_rel_call_push] THENL
     [MATCH_MP_TAC DATAPAUX_B2D_state_rel_clock THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[data_dec_clock_def; data_state_INFO.ri_accfupds; K_THM;
                  data_state_INFO.ri_fupdfupds; DSEMAUX_K_o; ARITH_RULE `0 - 1 = 0`] THEN
      MATCH_MP_TAC DATAPAUX_B2D_state_rel_clock THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `t3:(C,FFI)data_state` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DATAPAUX_B2D_Seq_SOME THEN ASM_REWRITE_TAC[]);;

let DATAPAUX_B2D_ALL_live = prove
 (`!(t1:(C,FFI)data_state) (t2:(C,FFI)data_state) live corr.
     ALL (\n. ~(lookup n (data_state_locals t1) = NONE)) live /\
     (!k x. lookup k (data_state_locals t1) = SOME x /\ (~MEM k live ==> MEM k corr)
            ==> lookup k (data_state_locals t2) = SOME x)
     ==> ALL (\n. ~(lookup n (data_state_locals t2) = NONE)) live`,
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[option_CASES; option_DISTINCT]);;

let DATAPAUX_B2D_domain_live_corr = prove
 (`!(t:(C,FFI)data_state) env corr live.
     var_corr env corr (sptree_map data_to_bvi_v (data_state_locals t)) /\
     ALL (\n. ~(lookup n (data_state_locals t) = NONE)) live
     ==> domain (list_to_num_set (APPEND live corr)) SUBSET domain (data_state_locals t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[domain_list_to_num_set2; SET_OF_LIST_APPEND; UNION_SUBSET] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DATAPAUX_B2D_ALL_domain THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC DATAPAUX_B2D_var_corr_domain THEN EXISTS_TAC `env:bvl_v list` THEN
    ASM_REWRITE_TAC[]]);;

(* the result of a call without handler: a Ret raise would be a type error *)
let DATAPAUX_B2D_call_res = prove
 (CASE_TERM `!(p:bvi_result # (C,FFI)bvi_state) res s2.
     (match p with
        (Rerr (Rraise (Exn v)),s) -> (Rerr (Rraise (Exn v)),s)
      | (Rerr (Rraise _),s) -> (Rerr (Rabort Rtype_error),s)
      | x -> x) = (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error))
     ==> p = (res,s2) /\ ~(?vs. res = Rerr (Rraise (Ret vs)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `p:bvi_result # (C,FFI)bvi_state` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:bvi_result` (X_CHOOSE_THEN `s3:(C,FFI)bvi_state`
    SUBST1_TAC)) THEN
  MP_TAC(ISPEC `r1:bvi_result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:bvl_v list` SUBST1_TAC)
                              (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THENL
   [ALL_TAC;
    MP_TAC(ISPEC `e:(exn_or_ret)error_result` (cases "error_result")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `ex:exn_or_ret` SUBST1_TAC)
                                (X_CHOOSE_THEN `ab:abort` SUBST1_TAC)) THEN
    CASE_REWRITE_TAC[] THENL
     [MP_TAC(ISPEC `ex:exn_or_ret` (cases "exn_or_ret")) THEN
      DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `w:bvl_v` SUBST1_TAC)
                                  (X_CHOOSE_THEN `ws:bvl_v list` SUBST1_TAC)) THEN
      CASE_REWRITE_TAC[];
      ALL_TAC]] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC DATAPAUX_B2D_RES_RWS);;

let DATAPAUX_B2D_var_corr_CONS = prove
 (`!a env k corr (t:A spt).
     var_corr (CONS a env) (CONS k corr) t <=>
     data_get_var k t = SOME a /\ var_corr env corr t`,
  REWRITE_TAC[var_corr_def; ALL2]);;

let DATAPAUX_B2D_jump_NONE_cong = prove
 (`!(a:(C,FFI)data_state) (b:(C,FFI)data_state).
     data_state_stack a = data_state_stack b /\ data_state_handler a = data_state_handler b
     ==> (data_jump_exc a = NONE <=> data_jump_exc b = NONE)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`b:(C,FFI)data_state`; `a:(C,FFI)data_state`] DSEMAUX_jump_exc_cong) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPEC `data_jump_exc (b:(C,FFI)data_state)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT]);;

(* the frame of a call with handler: an exception returns to it *)
let DATAPAUX_B2D_jump_push_T = prove
 (`!(t:(C,FFI)data_state) a ss env (t3:(C,FFI)data_state) ls.
     data_jump_exc
       (data_state_stack_fupd
          (K (data_state_stack (data_call_env a ss (data_push_env env T t))))
          (data_state_handler_fupd
             (K (data_state_handler (data_call_env a ss (data_push_env env T t)))) t3)) =
       SOME (data_state_locals_size_fupd (K ls) t3)
     ==> data_state_locals t3 = env /\ data_state_stack t3 = data_state_stack t /\
         data_state_handler t3 = data_state_handler t /\ ls = data_state_locals_size t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_call_env_def; data_push_env_def; LET_DEF; LET_END_DEF;
              data_state_INFO.ri_accfupds; K_THM; data_jump_exc_def; LENGTH;
              ARITH_RULE `n < SUC n`; LASTN_LEMMA] THEN
  CASE_REWRITE_TAC[option_INJ] THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM] THEN
  MESON_TAC[]);;

let DATAPAUX_B2D_jump_push_T_ne = prove
 (`!(t:(C,FFI)data_state) a ss env.
     ~(data_jump_exc (data_call_env a ss (data_push_env env T t)) = NONE)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_call_env_def; data_push_env_def; LET_DEF; LET_END_DEF;
              data_state_INFO.ri_accfupds; K_THM; data_jump_exc_def; LENGTH;
              ARITH_RULE `n < SUC n`; LASTN_LEMMA] THEN
  CASE_REWRITE_TAC[option_DISTINCT]);;

(* the state in which the handler of a call starts: the frame of the call  *)
(* with the exception value bound to n1                                     *)
let DATAPAUX_B2D_HANDLER_START = prove
 (`!(t2:(C,FFI)data_state) (t3:(C,FFI)data_state) n1 env corr live xv.
     var_corr env corr (sptree_map data_to_bvi_v (data_state_locals t2)) /\
     (!k. n1 <= k ==> lookup k (data_state_locals t2) = NONE) /\
     ALL (\n. ~(lookup n (data_state_locals t2) = NONE)) live /\
     data_state_locals t3 =
       mk_wf (sptree_inter (data_state_locals t2) (list_to_num_set (APPEND live corr))) /\
     data_state_stack t3 = data_state_stack t2 /\
     data_state_handler t3 = data_state_handler t2
     ==> var_corr (CONS (data_to_bvi_v xv) env) (CONS n1 corr)
           (sptree_map data_to_bvi_v (data_state_locals (data_set_var n1 xv t3))) /\
         (!k. n1 + 1 <= k ==> lookup k (data_state_locals (data_set_var n1 xv t3)) = NONE) /\
         ALL (\n. ~(lookup n (data_state_locals (data_set_var n1 xv t3)) = NONE)) live /\
         (data_jump_exc (data_set_var n1 xv t3) = NONE <=> data_jump_exc t2 = NONE) /\
         data_state_stack (data_set_var n1 xv t3) = data_state_stack t2 /\
         data_state_handler (data_set_var n1 xv t3) = data_state_handler t2 /\
         (!k x. lookup k (data_state_locals t2) = SOME x /\ (MEM k live \/ MEM k corr)
                ==> lookup k (data_state_locals (data_set_var n1 xv t3)) = SOME x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t3:(C,FFI)data_state`; `t2:(C,FFI)data_state`; `[]:num list`;
                 `live:num list`; `corr:num list`] DATAPAUX_B2D_cut_facts) THEN
  ASM_REWRITE_TAC[APPEND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k x. lookup k (data_state_locals (t3:(C,FFI)data_state)) = SOME x ==> k < n1`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `lookup k (data_state_locals (t2:(C,FFI)data_state)) = SOME x` MP_TAC THENL
     [ASM_MESON_TAC[]; ASM_SIMP_TAC[option_DISTINCT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `var_corr env corr (sptree_map data_to_bvi_v (data_state_locals (t3:(C,FFI)data_state)))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC DATAPAUX_B2D_var_corr_transfer THEN
    EXISTS_TAC `sptree_map data_to_bvi_v (data_state_locals (t2:(C,FFI)data_state))` THEN
    ASM_SIMP_TAC[lookup_map];
    ALL_TAC] THEN
  REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM; jump_exc_NONE] THEN
  SUBGOAL_THEN `!k. n1 <= k ==> lookup k (data_state_locals (t3:(C,FFI)data_state)) = NONE`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `lookup k (data_state_locals (t3:(C,FFI)data_state))` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[NOT_LE];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[DATAPAUX_B2D_var_corr_CONS; data_get_var_def; lookup_map; lookup_insert;
                OPTION_MAP_DEF] THEN
    MATCH_MP_TAC DATAPAUX_B2D_var_corr_insert THEN EXISTS_TAC `n1:num` THEN
    ASM_REWRITE_TAC[LE_REFL];
    REPEAT STRIP_TAC THEN REWRITE_TAC[lookup_insert] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    UNDISCH_TAC `ALL (\n. ~(lookup n (data_state_locals (t2:(C,FFI)data_state)) = NONE)) live` THEN
    REWRITE_TAC[GSYM ALL_MEM; lookup_insert] THEN DISCH_TAC THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC DATAPAUX_B2D_jump_NONE_cong THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[lookup_insert] THEN
    (COND_CASES_TAC THENL
      [FIRST_X_ASSUM(SUBST_ALL_TAC) THEN
       UNDISCH_TAC `lookup n1 (data_state_locals (t2:(C,FFI)data_state)) = SOME x` THEN
       ASM_SIMP_TAC[LE_REFL; option_DISTINCT];
       ASM_SIMP_TAC[]])]);;

(* after the handler of a call returned normally and its result was moved  *)
(* to n2: the NONE-branch facts of compile_correct for the whole call       *)
let DATAPAUX_B2D_HANDLER_END = prove
 (`!(t1:(C,FFI)data_state) (t2:(C,FFI)data_state) (th:(C,FFI)data_state)
    (t5:(C,FFI)data_state) n n1 n2 env corr live w pv.
     (!k. n <= k ==> lookup k (data_state_locals t1) = NONE) /\ n <= n1 /\
     (!k x. lookup k (data_state_locals t1) = SOME x /\ (~MEM k live ==> MEM k corr)
            ==> lookup k (data_state_locals t2) = SOME x) /\
     data_state_stack t1 = data_state_stack t2 /\
     data_state_handler t1 = data_state_handler t2 /\
     (~(data_jump_exc t1 = NONE) ==> ~(data_jump_exc t2 = NONE)) /\
     (!k x. lookup k (data_state_locals t2) = SOME x /\ (MEM k live \/ MEM k corr)
            ==> lookup k (data_state_locals th) = SOME x) /\
     (data_jump_exc th = NONE <=> data_jump_exc t2 = NONE) /\
     data_state_stack th = data_state_stack t2 /\
     data_state_handler th = data_state_handler t2 /\
     n1 + 1 <= n2 /\
     (!k. n2 <= k ==> lookup k (data_state_locals t5) = NONE) /\
     var_corr (CONS w env) (CONS n1 corr) (sptree_map data_to_bvi_v (data_state_locals t5)) /\
     (!k x. lookup k (data_state_locals th) = SOME x /\
            (~MEM k live ==> MEM k (CONS n1 corr))
            ==> lookup k (data_state_locals t5) = SOME x) /\
     data_state_stack th = data_state_stack t5 /\
     data_state_handler th = data_state_handler t5 /\
     (~(data_jump_exc th = NONE) ==> ~(data_jump_exc t5 = NONE))
     ==> n <= n2 + 1 /\ ALL (\v. v < n2 + 1) [n2] /\
         (!k. n2 + 1 <= k
              ==> lookup k (data_state_locals (data_set_var n2 pv t5)) = NONE) /\
         var_corr env corr
           (sptree_map data_to_bvi_v (data_state_locals (data_set_var n2 pv t5))) /\
         (!k x. lookup k (data_state_locals (data_set_var n2 pv t5)) = SOME x
                ==> k < n2 + 1) /\
         (!k x. lookup k (data_state_locals t1) = SOME x /\ (~MEM k live ==> MEM k corr)
                ==> lookup k (data_state_locals (data_set_var n2 pv t5)) = SOME x) /\
         data_state_stack t1 = data_state_stack (data_set_var n2 pv t5) /\
         data_state_handler t1 = data_state_handler (data_set_var n2 pv t5) /\
         (~(data_jump_exc t1 = NONE)
          ==> ~(data_jump_exc (data_set_var n2 pv t5) = NONE)) /\
         var_corr [data_to_bvi_v pv] [n2]
           (sptree_map data_to_bvi_v (data_state_locals (data_set_var n2 pv t5)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k x. lookup k (data_state_locals (t5:(C,FFI)data_state)) = SOME x ==> k < n2`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `lookup k (data_state_locals (t5:(C,FFI)data_state)) = SOME x` THEN
    ASM_SIMP_TAC[option_DISTINCT];
    ALL_TAC] THEN
  REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM; jump_exc_NONE] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    REWRITE_TAC[ALL] THEN ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[lookup_insert] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> try
      rand(concl th) = `lookup k (data_state_locals (t5:(C,FFI)data_state)) = NONE` ||
      rand(snd(dest_forall(concl th))) =
        `lookup k (data_state_locals (t5:(C,FFI)data_state)) = NONE`
      with _ -> false)) THEN ASM_ARITH_TAC;
    MATCH_MP_TAC DATAPAUX_B2D_var_corr_insert THEN EXISTS_TAC `n2:num` THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    UNDISCH_TAC `var_corr (CONS w env) (CONS n1 corr)
                   (sptree_map data_to_bvi_v (data_state_locals (t5:(C,FFI)data_state)))` THEN
    SIMP_TAC[DATAPAUX_B2D_var_corr_CONS];
    REPEAT GEN_TAC THEN REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THENL
     [DISCH_TAC THEN ASM_ARITH_TAC; DISCH_TAC THEN MATCH_MP_TAC(ARITH_RULE `k < n2 ==> k < n2 + 1`) THEN
      ASM_MESON_TAC[]];
    REPEAT STRIP_TAC THEN REWRITE_TAC[lookup_insert] THEN
    SUBGOAL_THEN `k < (n:num)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
      UNDISCH_TAC `lookup k (data_state_locals (t1:(C,FFI)data_state)) = SOME x` THEN
      ASM_SIMP_TAC[option_DISTINCT];
      ALL_TAC] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> try
      rand(snd(strip_forall(concl th))) =
        `lookup k (data_state_locals (t5:(C,FFI)data_state)) = SOME x`
      with _ -> false)) THEN
    REWRITE_TAC[MEM] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> try
      rand(snd(strip_forall(concl th))) =
        `lookup k (data_state_locals (th:(C,FFI)data_state)) = SOME x`
      with _ -> false)) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[DATAPAUX_B2D_jump_NONE_cong];
    REWRITE_TAC[var_corr_def; ALL2; data_get_var_def; lookup_map; lookup_insert;
                OPTION_MAP_DEF]]);;

let DATAPAUX_B2D_state_rel_set_var = prove
 (`!(s:(C,FFI)bvi_state) (t:(C,FFI)data_state) n v.
     bvi_to_dataProof_state_rel s (data_set_var n v t) <=> bvi_to_dataProof_state_rel s t`,
  REWRITE_TAC[data_set_var_def; DATAPAUX_B2D_state_rel_fupds]);;

let DATAPAUX_B2D_var_corr_SING = prove
 (`!l k (t:data_v spt).
     var_corr l [k] (sptree_map data_to_bvi_v t) <=>
     ?v. l = [data_to_bvi_v v] /\ lookup k t = SOME v`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `l:bvl_v list` list_CASES) THEN
  REWRITE_TAC[var_corr_def; ALL2; NOT_CONS_NIL] THEN
  STRUCT_CASES_TAC(ISPEC `t:bvl_v list` list_CASES) THEN
  REWRITE_TAC[ALL2; NOT_CONS_NIL; CONS_11; data_get_var_def; lookup_map] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `lookup k (t:data_v spt)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

(* the Call case of compile_correct split on the handler: the statement of *)
(* the case with handler replaced by h                                      *)
let DATAPAUX_B2D_CALL_SPEC (h:term) =
  let vs,b = strip_forall (el 10 DATAPAUX_B2D_CC_CASES) in
  let hv = el 3 vs in
  let vs' = filter ((<>) hv) vs in
  list_mk_forall(vs' @ filter (fun v -> not (mem v vs')) (frees h), vsubst [h,hv] b);;

let DATAPAUX_B2D_CALL_NONE = prove
 (DATAPAUX_B2D_CALL_SPEC `NONE:bvi_exp option`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "ihc") (LABEL_TAC "iha"))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF]) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN REWRITE_TAC[IS_SOME_DEF; bvi_fix_clock_evaluate] THEN
  MP_TAC(ISPEC `bvi_evaluate (xs,env,s1:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:bvi_result` (X_CHOOSE_THEN `s0:(C,FFI)bvi_state`
    ASSUME_TAC)) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `bvi_to_data_compile n corr F live xs` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:data_prog` (X_CHOOSE_THEN `y1:num list # num` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `y1:num list # num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:num list` (X_CHOOSE_THEN `n1:num` SUBST_ALL_TAC)) THEN
  ONCE_REWRITE_TAC[bvi_to_data_compile_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r0:bvi_result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:bvl_v list` SUBST_ALL_TAC)
                              (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THENL
   [REMOVE_THEN "iha" (MP_TAC o SPECL [`Rval a:bvi_result`; `s0:(C,FFI)bvi_state`;
      `t1:(C,FFI)data_state`; `n:num`; `corr:num list`; `F`; `live:num list`]) THEN
    ASM_REWRITE_TAC[LENGTH; PAIR_EQ; distinctness "result"] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN RVEQ_TAC THEN
    DATAPAUX_B2D_PRES_TAC `pres:((data_v list,data_v)result)option` THEN
    MP_TAC(ISPECL [`vs:num list`; `a:bvl_v list`; `data_state_locals (t2:(C,FFI)data_state)`]
                  get_vars_lift_thm) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `zz:data_v list` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`t1:(C,FFI)data_state`; `t2:(C,FFI)data_state`; `live:num list`;
                   `corr:num list`] DATAPAUX_B2D_ALL_live) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `bvl_find_code dest (MAP data_to_bvi_v zz)
                    (bvi_state_code (s0:(C,FFI)bvi_state))` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2
      (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[] THEN DATAPAUX_B2D_TERR_TAC)
      (X_CHOOSE_THEN `ae:bvl_v list # bvi_exp` ASSUME_TAC)) THEN
    MP_TAC(ISPEC `ae:bvl_v list # bvi_exp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `args:bvl_v list` (X_CHOOSE_THEN `exp:bvi_exp` SUBST_ALL_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s0:(C,FFI)bvi_state`; `t2:(C,FFI)data_state`; `dest:num option`;
                   `zz:data_v list`; `args:bvl_v list`; `exp:bvi_exp`]
                  bvi_to_dataProof_find_code_lemma) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `args':data_v list` (X_CHOOSE_THEN `ss:num option`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
    SUBGOAL_THEN `data_state_clock (t2:(C,FFI)data_state) = bvi_state_clock (s0:(C,FFI)bvi_state)`
      ASSUME_TAC THENL
     [UNDISCH_TAC `bvi_to_dataProof_state_rel (s0:(C,FFI)bvi_state) (t2:(C,FFI)data_state)` THEN
      SIMP_TAC[bvi_to_dataProof_state_rel_def];
      ALL_TAC] THEN
    ASM_CASES_TAC `bvi_state_clock (s0:(C,FFI)bvi_state) < ticks + 1` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      MP_TAC(ISPECL [`s0:(C,FFI)bvi_state`; `t2:(C,FFI)data_state`; `ticks:num`;
        `if tail then NONE else SOME ([next_var:num],list_to_num_set (APPEND live corr))`;
        `dest:num option`; `vs:num list`; `NONE:(num # data_prog)option`; `zz:data_v list`;
        `args':data_v list`; `bvi_to_data_compile_exp (LENGTH (args':data_v list)) exp`;
        `ss:num option`] DATAPAUX_B2D_call_timeout) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN BOOL_CASES_TAC `tail:bool` THEN REWRITE_TAC[] THEN
        DISJ2_TAC THEN REWRITE_TAC[option_INJ; PAIR_EQ] THEN
        REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
        REWRITE_TAC[ALL_DISTINCT; MEM] THEN MATCH_MP_TAC DATAPAUX_B2D_domain_live_corr THEN
        EXISTS_TAC `env:bvl_v list` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)data_state` STRIP_ASSUME_TAC o SPEC `data_Skip`) THEN
      REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN DATAPAUX_B2D_SEQ_NONE_TAC THEN
      ASM_REWRITE_TAC[PAIR_EQ] THEN
      REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC(data_to_bvi_result_def :: DATAPAUX_B2D_RES_RWS);
      DISCH_THEN(MP_TAC o C CONJ (ASSUME `~(res:bvi_result = Rerr (Rabort Rtype_error))`)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP DATAPAUX_B2D_call_res) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
      SUBGOAL_THEN `~(bvi_state_clock (s0:(C,FFI)bvi_state) < ticks) /\
                    ~(bvi_state_clock (s0:(C,FFI)bvi_state) - ticks = 0)` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `bvi_to_dataProof_state_rel (bvi_dec_clock (ticks + 1) s0)
                      (data_dec_clock (ITER ticks data_dec_clock (t2:(C,FFI)data_state)))`
        ASSUME_TAC THENL
       [MATCH_MP_TAC DATAPAUX_B2D_state_rel_ticks THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REMOVE_THEN "ihc" (MP_TAC o SPECL [`MAP data_to_bvi_v zz`; `exp:bvi_exp`;
                                        `MAP data_to_bvi_v args'`; `s0:(C,FFI)bvi_state`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(SPEC `tail:bool` BOOL_CASES_AX) THEN
      DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[] THENL
       [DISCH_THEN(MP_TAC o SPECL [`res:bvi_result`; `s2:(C,FFI)bvi_state`;
          `data_call_env args' ss (data_dec_clock (ITER ticks data_dec_clock
             (t2:(C,FFI)data_state)))`;
          `LENGTH (args':data_v list)`; `COUNT_LIST (LENGTH (args':data_v list))`; `T`;
          `[]:num list`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[DATAPAUX_B2D_state_rel_call_push; LENGTH; ONE; ALL] THEN
          REWRITE_TAC[data_call_env_def; data_dec_clock_def; funpow_dec_clock_clock;
                      LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM; jump_exc_NONE;
                      DATAPAUX_B2D_var_corr_fromList] THEN
          ASM_SIMP_TAC[lookup_fromList_outside] THEN ASM_MESON_TAC[];
          ALL_TAC] THEN
        DISCH_THEN(MP_TAC o MATCH_MP DATAPAUX_B2D_CALLEE) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `r:(data_v list,data_v)result`
          (X_CHOOSE_THEN `t3:(C,FFI)data_state`
          (X_CHOOSE_THEN `ls3:num option` STRIP_ASSUME_TAC))) THEN
        REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
        DATAPAUX_B2D_SEQ_NONE_TAC THEN
        REWRITE_TAC[evaluate_mk_ticks] THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[data_evaluate_def; FUNPOW_dec_clock_code] THEN ASM_REWRITE_TAC[] THEN
        CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[bvi_to_data_compile_exp_def] THEN
        CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
        REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls3:num option` THEN
        CASE_REWRITE_TAC[] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[data_call_env_def; data_dec_clock_def; funpow_dec_clock_clock;
                                    LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM]) THEN
        ASM_REWRITE_TAC[] THEN DATAPAUX_FAST_MESON_TAC[];
        DISCH_THEN(MP_TAC o SPECL [`res:bvi_result`; `s2:(C,FFI)bvi_state`;
          `data_call_env args' ss (data_push_env (mk_wf (sptree_inter
             (data_state_locals (t2:(C,FFI)data_state)) (list_to_num_set (APPEND live corr))))
             F (data_dec_clock (ITER ticks data_dec_clock t2)))`;
          `LENGTH (args':data_v list)`; `COUNT_LIST (LENGTH (args':data_v list))`; `T`;
          `[]:num list`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[DATAPAUX_B2D_state_rel_call_push; LENGTH; ONE; ALL] THEN
          REPEAT CONJ_TAC THENL
           [REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF;
                        data_state_INFO.ri_accfupds; K_THM; DATAPAUX_B2D_var_corr_fromList];
            REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF;
                        data_state_INFO.ri_accfupds; K_THM] THEN
            SIMP_TAC[lookup_fromList_outside];
            DISCH_TAC THEN MATCH_MP_TAC DATAPAUX_B2D_jump_push THEN
            REWRITE_TAC[funpow_dec_clock_clock; jump_exc_NONE] THEN ASM_MESON_TAC[]];
          ALL_TAC] THEN
        DISCH_THEN(MP_TAC o MATCH_MP DATAPAUX_B2D_CALLEE) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `r:(data_v list,data_v)result`
          (X_CHOOSE_THEN `t3:(C,FFI)data_state`
          (X_CHOOSE_THEN `ls3:num option` STRIP_ASSUME_TAC))) THEN
        REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
        MP_TAC(ISPECL [`t2:(C,FFI)data_state`; `env:bvl_v list`; `corr:num list`;
                       `live:num list`] DATAPAUX_B2D_cut_live_corr) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        DATAPAUX_B2D_SEQ_NONE_TAC THEN
        REWRITE_TAC[evaluate_mk_ticks] THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[data_evaluate_def; FUNPOW_dec_clock_code] THEN ASM_REWRITE_TAC[] THEN
        CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[ALL_DISTINCT; MEM; IS_SOME_DEF] THEN
        CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
        REWRITE_TAC[data_fix_clock_evaluate; bvi_to_data_compile_exp_def] THEN
        ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
        SUBGOAL_THEN `data_to_bvi_result r = (res:bvi_result)` ASSUME_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[data_call_env_def; data_push_env_def; data_dec_clock_def;
                                    funpow_dec_clock_clock; LET_DEF; LET_END_DEF;
                                    data_state_INFO.ri_accfupds; K_THM]) THEN
        MP_TAC(ISPEC `r:(data_v list,data_v)result` (cases "result")) THEN
        DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `xs:data_v list` SUBST_ALL_TAC)
                                    (X_CHOOSE_THEN `e:(data_v)error_result` SUBST_ALL_TAC)) THEN
        CASE_REWRITE_TAC[] THENL
         [RULE_ASSUM_TAC(REWRITE_RULE[data_to_bvi_result_def]) THEN
          FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rand(concl th) = `res:bvi_result`)) THEN
          FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_SING_IMP) THEN
          REWRITE_TAC[MAP_EQ_SING] THEN
          DISCH_THEN(X_CHOOSE_THEN `w:bvl_v` (X_CHOOSE_THEN `x:data_v`
            (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC))) THEN
          SUBGOAL_THEN `data_state_stack (t3:(C,FFI)data_state) =
                        CONS (data_Env (data_state_locals_size (t2:(C,FFI)data_state))
                          (mk_wf (sptree_inter (data_state_locals t2)
                                    (list_to_num_set (APPEND live corr)))))
                          (data_state_stack t2) /\
                        data_state_handler t3 = data_state_handler t2` STRIP_ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
                                                    is_disj (lhand (concl th)))) THEN
            REWRITE_TAC(MAP :: DATAPAUX_B2D_RES_RWS) THEN MESON_TAC[];
            ALL_TAC] THEN
          REWRITE_TAC[LENGTH; HD; data_pop_env_def; DATAPAUX_B2D_set_vars_sing] THEN
          ASM_REWRITE_TAC[] THEN
          CASE_REWRITE_TAC[PAIR_EQ] THEN
          REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN CASE_REWRITE_TAC[] THEN
          MP_TAC(ISPECL [`data_state_locals_fupd (K (mk_wf (sptree_inter
                (data_state_locals (t2:(C,FFI)data_state)) (list_to_num_set (APPEND live corr)))))
             (data_state_stack_fupd (K (data_state_stack t2))
               (data_state_locals_size_fupd (K (data_state_locals_size t2))
                  (t3:(C,FFI)data_state)))`; `t2:(C,FFI)data_state`; `[]:num list`;
            `live:num list`; `corr:num list`] DATAPAUX_B2D_cut_facts) THEN
          REWRITE_TAC[APPEND; data_state_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN
          MP_TAC(ISPECL [`t1:(C,FFI)data_state`; `t2:(C,FFI)data_state`;
            `data_state_locals_fupd (K (mk_wf (sptree_inter
                (data_state_locals (t2:(C,FFI)data_state)) (list_to_num_set (APPEND live corr)))))
             (data_state_stack_fupd (K (data_state_stack t2))
               (data_state_locals_size_fupd (K (data_state_locals_size t2))
                  (t3:(C,FFI)data_state)))`;
            `n:num`; `next_var:num`; `env:bvl_v list`; `corr:num list`; `live:num list`;
            `x:data_v`] DATAPAUX_B2D_OP_FACTS) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[MAP] THEN
          REWRITE_TAC[data_set_var_def; DATAPAUX_B2D_state_rel_fupds;
                      data_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[];
          MP_TAC(ISPEC `e:(data_v)error_result` (cases "error_result")) THEN
          DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `ev:data_v` SUBST_ALL_TAC)
                                      (X_CHOOSE_THEN `ab:abort` SUBST_ALL_TAC)) THEN
          CASE_REWRITE_TAC[PAIR_EQ] THEN REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
          EXISTS_TAC `ls3:num option` THEN CASE_REWRITE_TAC[] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[data_to_bvi_result_def]) THEN
          FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rand(concl th) = `res:bvi_result`)) THEN
          ASM_REWRITE_TAC(data_to_bvi_result_def :: DATAPAUX_B2D_RES_RWS) THEN
          MATCH_MP_TAC DATAPAUX_B2D_jump_Env THEN
          MAP_EVERY EXISTS_TAC [`data_state_locals_size (t2:(C,FFI)data_state)`;
            `mk_wf (sptree_inter (data_state_locals (t2:(C,FFI)data_state))
                          (list_to_num_set (APPEND live corr)))`] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp (concl th) &&
             can (find_term (fun t -> try fst(dest_const t) = "data_jump_exc" with _ -> false))
                 (rand (concl th)))) THEN
          REWRITE_TAC DATAPAUX_B2D_RES_RWS]]];
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REMOVE_THEN "iha" (MP_TAC o SPECL [`Rerr e:bvi_result`; `s0:(C,FFI)bvi_state`;
      `t1:(C,FFI)data_state`; `n:num`; `corr:num list`; `F`; `live:num list`]) THEN
    ASM_REWRITE_TAC[LENGTH; PAIR_EQ] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN RVEQ_TAC THEN
    DATAPAUX_B2D_PRES_TAC `pres:((data_v list,data_v)result)option` THEN
    MP_TAC(SPEC `tail:bool` BOOL_CASES_AX) THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
    DATAPAUX_B2D_SEQ_SOME_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls:num option` THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC DATAPAUX_B2D_RES_RWS]);;

let DATAPAUX_B2D_CALL_SOME = prove
 (DATAPAUX_B2D_CALL_SPEC `SOME (hx:bvi_exp)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihh")
    (CONJUNCTS_THEN2 (LABEL_TAC "ihc") (LABEL_TAC "iha"))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF]) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN REWRITE_TAC[IS_SOME_DEF; bvi_fix_clock_evaluate] THEN
  ASM_CASES_TAC `IS_NONE (dest:num option)` THEN ASM_REWRITE_TAC[] THENL
   [DATAPAUX_B2D_TERR_TAC; ALL_TAC] THEN
  REMOVE_THEN "iha" (MP_TAC o C MP (ASSUME `~IS_NONE (dest:num option)`)) THEN
  DISCH_THEN(LABEL_TAC "iha") THEN
  MP_TAC(ISPEC `bvi_evaluate (xs,env,s1:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:bvi_result` (X_CHOOSE_THEN `s0:(C,FFI)bvi_state`
    ASSUME_TAC)) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `bvi_to_data_compile n corr F live xs` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:data_prog` (X_CHOOSE_THEN `y1:num list # num` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `y1:num list # num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:num list` (X_CHOOSE_THEN `n1:num` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `bvi_to_data_compile (n1 + 1) (CONS n1 corr) F live [hx]` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:data_prog` (X_CHOOSE_THEN `y2:num list # num` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `y2:num list # num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `v2:num list` (X_CHOOSE_THEN `n2:num` SUBST_ALL_TAC)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP compile_SING_IMP) THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:num` SUBST_ALL_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP compile_LESS_EQ o
    check (fun th -> free_in `hx:bvi_exp` (concl th))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP compile_RANGE o
    check (fun th -> free_in `hx:bvi_exp` (concl th))) THEN
  ONCE_REWRITE_TAC[bvi_to_data_compile_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r0:bvi_result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:bvl_v list` SUBST_ALL_TAC)
                              (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THENL
   [REMOVE_THEN "iha" (MP_TAC o SPECL [`Rval a:bvi_result`; `s0:(C,FFI)bvi_state`;
      `t1:(C,FFI)data_state`; `n:num`; `corr:num list`; `F`; `live:num list`]) THEN
    ASM_REWRITE_TAC[LENGTH; PAIR_EQ; distinctness "result"] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN RVEQ_TAC THEN
    DATAPAUX_B2D_PRES_TAC `pres:((data_v list,data_v)result)option` THEN
    MP_TAC(ISPECL [`vs:num list`; `a:bvl_v list`; `data_state_locals (t2:(C,FFI)data_state)`]
                  get_vars_lift_thm) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `zz:data_v list` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`t1:(C,FFI)data_state`; `t2:(C,FFI)data_state`; `live:num list`;
                   `corr:num list`] DATAPAUX_B2D_ALL_live) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `bvl_find_code dest (MAP data_to_bvi_v zz)
                    (bvi_state_code (s0:(C,FFI)bvi_state))` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2
      (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[] THEN DATAPAUX_B2D_TERR_TAC)
      (X_CHOOSE_THEN `ae:bvl_v list # bvi_exp` ASSUME_TAC)) THEN
    MP_TAC(ISPEC `ae:bvl_v list # bvi_exp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `args:bvl_v list` (X_CHOOSE_THEN `exp:bvi_exp` SUBST_ALL_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s0:(C,FFI)bvi_state`; `t2:(C,FFI)data_state`; `dest:num option`;
                   `zz:data_v list`; `args:bvl_v list`; `exp:bvi_exp`]
                  bvi_to_dataProof_find_code_lemma) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `args':data_v list` (X_CHOOSE_THEN `ss:num option`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
    SUBGOAL_THEN `data_state_clock (t2:(C,FFI)data_state) = bvi_state_clock (s0:(C,FFI)bvi_state)`
      ASSUME_TAC THENL
     [UNDISCH_TAC `bvi_to_dataProof_state_rel (s0:(C,FFI)bvi_state) (t2:(C,FFI)data_state)` THEN
      SIMP_TAC[bvi_to_dataProof_state_rel_def];
      ALL_TAC] THEN
    REWRITE_TAC[HD] THEN
    ASM_CASES_TAC `bvi_state_clock (s0:(C,FFI)bvi_state) < ticks + 1` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      MP_TAC(ISPECL [`s0:(C,FFI)bvi_state`; `t2:(C,FFI)data_state`; `ticks:num`;
        `SOME ([n2:num],list_to_num_set (APPEND live corr))`;
        `dest:num option`; `vs:num list`; `SOME (next_var:num,data_Seq c2 (data_Move n2 vv))`;
        `zz:data_v list`;
        `args':data_v list`; `bvi_to_data_compile_exp (LENGTH (args':data_v list)) exp`;
        `ss:num option`] DATAPAUX_B2D_call_timeout) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[option_DISTINCT] THEN REWRITE_TAC[option_INJ; PAIR_EQ] THEN
        REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
        REWRITE_TAC[ALL_DISTINCT; MEM] THEN MATCH_MP_TAC DATAPAUX_B2D_domain_live_corr THEN
        EXISTS_TAC `env:bvl_v list` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)data_state` STRIP_ASSUME_TAC o
        SPEC `if tail then data_Return [n2] else data_Skip`) THEN
      REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN DATAPAUX_B2D_SEQ_NONE_TAC THEN
      ASM_REWRITE_TAC[PAIR_EQ] THEN
      REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC(data_to_bvi_result_def :: DATAPAUX_B2D_RES_RWS);
      MP_TAC(ISPEC `bvi_evaluate ([exp],MAP data_to_bvi_v args',
                       bvi_dec_clock (ticks + 1) (s0:(C,FFI)bvi_state))` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `r4:bvi_result` (X_CHOOSE_THEN `s4:(C,FFI)bvi_state`
        ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(r4 = Rerr (Rabort Rtype_error)) /\
                    ~(?vs. (r4:bvi_result) = Rerr (Rraise (Ret vs)))` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [DISCH_THEN SUBST_ALL_TAC;
          DISCH_THEN(X_CHOOSE_THEN `ws:bvl_v list` SUBST_ALL_TAC)] THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
           rand(concl th) = `(res:bvi_result),(s2:(C,FFI)bvi_state)`)) THEN
        CASE_REWRITE_TAC[] THEN DATAPAUX_B2D_TERR_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `~(bvi_state_clock (s0:(C,FFI)bvi_state) < ticks) /\
                    ~(bvi_state_clock (s0:(C,FFI)bvi_state) - ticks = 0)` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `bvi_to_dataProof_state_rel (bvi_dec_clock (ticks + 1) s0)
                      (data_dec_clock (ITER ticks data_dec_clock (t2:(C,FFI)data_state)))`
        ASSUME_TAC THENL
       [MATCH_MP_TAC DATAPAUX_B2D_state_rel_ticks THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REMOVE_THEN "ihc" (MP_TAC o SPECL [`MAP data_to_bvi_v zz`; `exp:bvi_exp`;
                                        `MAP data_to_bvi_v args'`; `s0:(C,FFI)bvi_state`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`r4:bvi_result`; `s4:(C,FFI)bvi_state`;
          `data_call_env args' ss (data_push_env (mk_wf (sptree_inter
             (data_state_locals (t2:(C,FFI)data_state)) (list_to_num_set (APPEND live corr))))
             T (data_dec_clock (ITER ticks data_dec_clock t2)))`;
          `LENGTH (args':data_v list)`; `COUNT_LIST (LENGTH (args':data_v list))`; `T`;
          `[]:num list`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[DATAPAUX_B2D_state_rel_call_push; LENGTH; ONE; ALL;
                        DATAPAUX_B2D_jump_push_T_ne] THEN
        CONJ_TAC THENL
         [REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF;
                      data_state_INFO.ri_accfupds; K_THM; DATAPAUX_B2D_var_corr_fromList];
          REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF;
                      data_state_INFO.ri_accfupds; K_THM] THEN
          SIMP_TAC[lookup_fromList_outside]];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP DATAPAUX_B2D_CALLEE) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:(data_v list,data_v)result`
        (X_CHOOSE_THEN `t3:(C,FFI)data_state`
        (X_CHOOSE_THEN `ls3:num option` STRIP_ASSUME_TAC))) THEN
      SUBGOAL_THEN `data_to_bvi_result r = (r4:bvi_result)` ASSUME_TAC THENL
       [UNDISCH_TAC `~(?vs. (r4:bvi_result) = Rerr (Rraise (Ret vs)))
                     ==> data_to_bvi_result (r:(data_v list,data_v)result) = r4` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`t2:(C,FFI)data_state`; `env:bvl_v list`; `corr:num list`;
                     `live:num list`] DATAPAUX_B2D_cut_live_corr) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
      DATAPAUX_B2D_SEQ_NONE_TAC THEN
      REWRITE_TAC[evaluate_mk_ticks] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `r:(data_v list,data_v)result` (cases "result")) THEN
      DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `xs:data_v list` SUBST_ALL_TAC)
                                  (X_CHOOSE_THEN `e:(data_v)error_result` SUBST_ALL_TAC)) THENL
       [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o REWRITE_RULE[data_to_bvi_result_def] o
          check (fun th -> rand(concl th) = `r4:bvi_result`)) THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
           rand(concl th) = `(res:bvi_result),(s2:(C,FFI)bvi_state)`)) THEN
        CASE_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_SING_IMP o
          check (fun th -> free_in `exp:bvi_exp` (concl th) && is_eq (concl th))) THEN
        REWRITE_TAC[MAP_EQ_SING] THEN
        DISCH_THEN(X_CHOOSE_THEN `w:bvl_v` (X_CHOOSE_THEN `x:data_v`
          (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC))) THEN
        SUBGOAL_THEN `data_state_stack (t3:(C,FFI)data_state) =
                      CONS (Exc (data_state_locals_size (t2:(C,FFI)data_state))
                        (mk_wf (sptree_inter (data_state_locals t2) (list_to_num_set (APPEND live corr))))
                        (data_state_handler t2)) (data_state_stack t2)` ASSUME_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
                                                  is_disj (lhand (concl th)))) THEN
          REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def;
                      funpow_dec_clock_clock; LET_DEF; LET_END_DEF;
                      data_state_INFO.ri_accfupds; K_THM] THEN
          REWRITE_TAC(MAP :: DATAPAUX_B2D_RES_RWS) THEN MESON_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `data_evaluate (data_Call (SOME ([n2],list_to_num_set (APPEND live corr))) dest vs
                         (SOME (next_var,data_Seq c2 (data_Move n2 vv))),
                         ITER ticks data_dec_clock (t2:(C,FFI)data_state)) = (NONE, data_set_var n2 x (data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals (t2:(C,FFI)data_state))
                (list_to_num_set (APPEND live corr)))))
             (data_state_stack_fupd (K (data_state_stack t2))
               (data_state_locals_size_fupd (K (data_state_locals_size t2))
                 (data_state_handler_fupd (K (data_state_handler t2))
                   (t3:(C,FFI)data_state))))))` ASSUME_TAC THENL
         [REWRITE_TAC[data_evaluate_def] THEN REWRITE_TAC[FUNPOW_dec_clock_code] THEN ASM_REWRITE_TAC[] THEN
            CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[ALL_DISTINCT; MEM; IS_SOME_DEF] THEN
            CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
            REWRITE_TAC[data_fix_clock_evaluate; bvi_to_data_compile_exp_def] THEN
            ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
          REWRITE_TAC[LENGTH; data_pop_env_def; DATAPAUX_B2D_set_vars_sing] THEN
          ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
          ALL_TAC] THEN
        DATAPAUX_B2D_SEQ_NONE_TAC THEN
        MP_TAC(SPEC `tail:bool` BOOL_CASES_AX) THEN
        DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[] THENL
         [REWRITE_TAC[data_evaluate_def; data_get_vars_def; data_get_var_def; data_set_var_def;
                      data_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN
          CASE_REWRITE_TAC[PAIR_EQ] THEN
          REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN CASE_REWRITE_TAC[] THEN
          ASM_REWRITE_TAC(DATAPAUX_B2D_state_rel_fupds :: data_flush_state_def ::
                          data_state_INFO.ri_accfupds :: K_THM :: data_to_bvi_result_def :: MAP ::
                          DATAPAUX_B2D_RES_RWS);
          REWRITE_TAC[data_evaluate_def; PAIR_EQ] THEN
          REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN CASE_REWRITE_TAC[] THEN
          MP_TAC(ISPECL [`data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals (t2:(C,FFI)data_state))
                (list_to_num_set (APPEND live corr)))))
             (data_state_stack_fupd (K (data_state_stack t2))
               (data_state_locals_size_fupd (K (data_state_locals_size t2))
                 (data_state_handler_fupd (K (data_state_handler t2))
                   (t3:(C,FFI)data_state))))`; `t2:(C,FFI)data_state`; `[]:num list`;
            `live:num list`; `corr:num list`] DATAPAUX_B2D_cut_facts) THEN
          REWRITE_TAC[APPEND; data_state_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN
          SUBGOAL_THEN `!k. n2 <= k ==> lookup k (data_state_locals (t2:(C,FFI)data_state)) = NONE`
            ASSUME_TAC THENL
           [REPEAT STRIP_TAC THEN
            FIRST_X_ASSUM(MATCH_MP_TAC o check ((=) `!k. next_var <= k ==> lookup k (data_state_locals (t2:(C,FFI)data_state)) = NONE` o concl)) THEN
            MATCH_MP_TAC(ARITH_RULE `!nv n2 k. nv + 1 <= n2 /\ n2 <= k ==> nv <= k`) THEN
            EXISTS_TAC `n2:num` THEN ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          MP_TAC(ISPECL [`t1:(C,FFI)data_state`; `t2:(C,FFI)data_state`; `data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals (t2:(C,FFI)data_state))
                (list_to_num_set (APPEND live corr)))))
             (data_state_stack_fupd (K (data_state_stack t2))
               (data_state_locals_size_fupd (K (data_state_locals_size t2))
                 (data_state_handler_fupd (K (data_state_handler t2))
                   (t3:(C,FFI)data_state))))`;
            `n:num`; `n2:num`; `env:bvl_v list`; `corr:num list`; `live:num list`;
            `x:data_v`] DATAPAUX_B2D_OP_FACTS) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
            MATCH_MP_TAC(ARITH_RULE `!n nv n2. n <= nv /\ nv + 1 <= n2 ==> n <= n2`) THEN
            EXISTS_TAC `next_var:num` THEN ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[MAP] THEN
          REWRITE_TAC[data_set_var_def; DATAPAUX_B2D_state_rel_fupds;
                      data_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[]];
        MP_TAC(ISPEC `e:(data_v)error_result` (cases "error_result")) THEN
        DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `xv:data_v` SUBST_ALL_TAC)
                                    (X_CHOOSE_THEN `ab:abort` SUBST_ALL_TAC)) THENL
         [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o REWRITE_RULE[data_to_bvi_result_def] o
            check (fun th -> rand(concl th) = `r4:bvi_result`)) THEN
          FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
             rand(concl th) = `(res:bvi_result),(s2:(C,FFI)bvi_state)`)) THEN
          CASE_REWRITE_TAC[] THEN
          DISCH_THEN(MP_TAC o C CONJ (ASSUME `~(res:bvi_result = Rerr (Rabort Rtype_error))`)) THEN
          DISCH_THEN(MP_TAC o MATCH_MP DATAPAUX_B2D_force_res) THEN
          DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
          FIRST_X_ASSUM(MP_TAC o REWRITE_RULE DATAPAUX_B2D_RES_RWS o
            check (fun th -> is_imp (concl th) &&
             can (find_term (fun t -> try fst(dest_const t) = "data_jump_exc" with _ -> false))
               (rand (concl th)) &&
             can (find_term (fun t -> try fst(dest_const t) = "data_push_env" with _ -> false))
               (concl th))) THEN
          DISCH_THEN(STRIP_ASSUME_TAC o
            REWRITE_RULE[data_dec_clock_def; funpow_dec_clock_clock;
                         data_state_INFO.ri_accfupds; K_THM] o
            MATCH_MP DATAPAUX_B2D_jump_push_T) THEN
          MP_TAC(ISPECL [`t2:(C,FFI)data_state`; `t3:(C,FFI)data_state`; `next_var:num`;
                         `env:bvl_v list`; `corr:num list`; `live:num list`; `xv:data_v`]
                        DATAPAUX_B2D_HANDLER_START) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
          REMOVE_THEN "ihh" (MP_TAC o SPECL [`MAP data_to_bvi_v zz`; `exp:bvi_exp`;
             `MAP data_to_bvi_v args'`; `s0:(C,FFI)bvi_state`; `hx:bvi_exp`;
             `data_to_bvi_v xv`; `s4:(C,FFI)bvi_state`]) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          DISCH_THEN(MP_TAC o SPECL [`res:bvi_result`; `s2:(C,FFI)bvi_state`;
             `data_set_var next_var xv (t3:(C,FFI)data_state)`; `next_var + 1`;
             `CONS (next_var:num) corr`; `F`; `live:num list`]) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[LENGTH; DATAPAUX_B2D_state_rel_set_var] THEN DATAPAUX_FAST_MESON_TAC[];
            ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `t5:(C,FFI)data_state` (X_CHOOSE_THEN `pr2:data_prog`
            (X_CHOOSE_THEN `pres2:((data_v list,data_v)result)option`
            (X_CHOOSE_THEN `vs2:num list` (X_CHOOSE_THEN `nv2:num`
            (X_CHOOSE_THEN `ls5:num option` (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC))))))) THEN
          DISCH_THEN(MP_TAC o TRANS (SYM (ASSUME
            `bvi_to_data_compile (next_var + 1) (CONS next_var corr) F live [hx] = c2,[vv],n2`))) THEN
          REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(MAP_EVERY (SUBST_ALL_TAC o SYM) o CONJUNCTS) THEN
          MP_TAC(ISPEC `pres2:((data_v list,data_v)result)option` (cases "option")) THEN
          DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
            (X_CHOOSE_THEN `r2:(data_v list,data_v)result` SUBST_ALL_TAC)) THENL
           [POP_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[] o CASE_REWRITE_RULE[]) THEN
            MP_TAC(ISPEC `res:bvi_result` (cases "result")) THEN
            DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `rv:bvl_v list` SUBST_ALL_TAC)
              (X_CHOOSE_THEN `re:(exn_or_ret)error_result` SUBST_ALL_TAC)) THEN
            POP_ASSUM(MP_TAC o CASE_REWRITE_RULE[]) THENL
             [DISCH_THEN(X_CHOOSE_THEN `pv:data_v` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) o
                REWRITE_RULE[DATAPAUX_B2D_var_corr_SING]) THEN
            SUBGOAL_THEN `data_state_stack (t2:(C,FFI)data_state) =
                            data_state_stack (t5:(C,FFI)data_state) /\
                          data_state_handler t2 = data_state_handler t5` STRIP_ASSUME_TAC THENL
             [UNDISCH_TAC `data_state_stack (data_set_var next_var xv (t3:(C,FFI)data_state)) =
                           data_state_stack (t2:(C,FFI)data_state)` THEN
              UNDISCH_TAC `data_state_handler (data_set_var next_var xv (t3:(C,FFI)data_state)) =
                           data_state_handler (t2:(C,FFI)data_state)` THEN
              UNDISCH_TAC `data_state_stack (data_set_var next_var xv (t3:(C,FFI)data_state)) =
                           data_state_stack (t5:(C,FFI)data_state)` THEN
              UNDISCH_TAC `data_state_handler (data_set_var next_var xv (t3:(C,FFI)data_state)) =
                           data_state_handler (t5:(C,FFI)data_state)` THEN
              MESON_TAC[];
              ALL_TAC] THEN
              SUBGOAL_THEN `data_evaluate (data_Call (SOME ([n2],list_to_num_set (APPEND live corr))) dest vs
                         (SOME (next_var,data_Seq c2 (data_Move n2 vv))),
                         ITER ticks data_dec_clock (t2:(C,FFI)data_state)) = (NONE, data_set_var n2 pv (t5:(C,FFI)data_state))` ASSUME_TAC THENL
               [GEN_REWRITE_TAC LAND_CONV [data_evaluate_def] THEN REWRITE_TAC[FUNPOW_dec_clock_code] THEN ASM_REWRITE_TAC[] THEN
            CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[ALL_DISTINCT; MEM; IS_SOME_DEF] THEN
            CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
            REWRITE_TAC[data_fix_clock_evaluate; bvi_to_data_compile_exp_def] THEN
            ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
                DATAPAUX_B2D_SEQ_NONE_TAC THEN
                REWRITE_TAC[data_evaluate_def; data_get_var_def] THEN ASM_REWRITE_TAC[] THEN
                CASE_REWRITE_TAC[];
                ALL_TAC] THEN
              DATAPAUX_B2D_SEQ_NONE_TAC THEN
              MP_TAC(SPEC `tail:bool` BOOL_CASES_AX) THEN
              DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[] THENL
               [REWRITE_TAC[data_evaluate_def; data_get_vars_def; data_get_var_def; data_set_var_def;
                            data_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN
                CASE_REWRITE_TAC[PAIR_EQ] THEN
                REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN CASE_REWRITE_TAC[] THEN
                RULE_ASSUM_TAC(REWRITE_RULE[data_set_var_def; data_state_INFO.ri_accfupds;
                                            K_THM]) THEN
                ASM_REWRITE_TAC(DATAPAUX_B2D_state_rel_fupds :: data_flush_state_def ::
                                data_state_INFO.ri_accfupds :: K_THM :: data_to_bvi_result_def ::
                                MAP :: DATAPAUX_B2D_RES_RWS);
                REWRITE_TAC[data_evaluate_def; PAIR_EQ] THEN
                REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN CASE_REWRITE_TAC[] THEN
                MP_TAC(ISPECL [`t1:(C,FFI)data_state`; `t2:(C,FFI)data_state`;
                   `data_set_var next_var xv (t3:(C,FFI)data_state)`; `t5:(C,FFI)data_state`;
                   `n:num`; `next_var:num`; `n2:num`; `env:bvl_v list`; `corr:num list`;
                   `live:num list`; `data_to_bvi_v xv`; `pv:data_v`] DATAPAUX_B2D_HANDLER_END) THEN
                ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
                STRIP_TAC THEN ASM_REWRITE_TAC[MAP; DATAPAUX_B2D_state_rel_set_var] THEN
                REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM] THEN
                ASM_REWRITE_TAC[]];
              REWRITE_TAC[]];
            POP_ASSUM(STRIP_ASSUME_TAC o CASE_REWRITE_RULE[]) THEN
            SUBGOAL_THEN `data_evaluate (data_Call (SOME ([n2],list_to_num_set (APPEND live corr))) dest vs
                         (SOME (next_var,data_Seq c2 (data_Move n2 vv))),
                         ITER ticks data_dec_clock (t2:(C,FFI)data_state)) = (SOME r2, (t5:(C,FFI)data_state))` ASSUME_TAC THENL
             [GEN_REWRITE_TAC LAND_CONV [data_evaluate_def] THEN REWRITE_TAC[FUNPOW_dec_clock_code] THEN ASM_REWRITE_TAC[] THEN
            CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[ALL_DISTINCT; MEM; IS_SOME_DEF] THEN
            CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
            REWRITE_TAC[data_fix_clock_evaluate; bvi_to_data_compile_exp_def] THEN
            ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
              DATAPAUX_B2D_SEQ_SOME_TAC THEN REWRITE_TAC[];
              ALL_TAC] THEN
            DATAPAUX_B2D_SEQ_SOME_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
            REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls5:num option` THEN
            CASE_REWRITE_TAC[] THEN
            RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `data_state_stack (data_set_var next_var xv
                                                  (t3:(C,FFI)data_state)) = data_state_stack (t2:(C,FFI)data_state)`;
                                        ASSUME `data_state_handler (data_set_var next_var xv
                                                  (t3:(C,FFI)data_state)) = data_state_handler (t2:(C,FFI)data_state)`]) THEN
            ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC `~(?vs. (res:bvi_result) = Rerr (Rraise (Ret vs)))
                         ==> data_to_bvi_result (r2:(data_v list,data_v)result) = res` THEN
            ASM_REWRITE_TAC[]];
          FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o REWRITE_RULE[data_to_bvi_result_def] o
            check (fun th -> rand(concl th) = `r4:bvi_result`)) THEN
          FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
             rand(concl th) = `(res:bvi_result),(s2:(C,FFI)bvi_state)`)) THEN
          CASE_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
          SUBGOAL_THEN `data_evaluate (data_Call (SOME ([n2],list_to_num_set (APPEND live corr))) dest vs
                         (SOME (next_var,data_Seq c2 (data_Move n2 vv))),
                         ITER ticks data_dec_clock (t2:(C,FFI)data_state)) = (SOME (Rerr (Rabort ab)),t3)` ASSUME_TAC THENL
           [REWRITE_TAC[data_evaluate_def] THEN REWRITE_TAC[FUNPOW_dec_clock_code] THEN ASM_REWRITE_TAC[] THEN
            CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[ALL_DISTINCT; MEM; IS_SOME_DEF] THEN
            CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
            REWRITE_TAC[data_fix_clock_evaluate; bvi_to_data_compile_exp_def] THEN
            ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]; ALL_TAC] THEN
          DATAPAUX_B2D_SEQ_SOME_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
          REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN CASE_REWRITE_TAC[] THEN
          ASM_REWRITE_TAC(data_to_bvi_result_def :: DATAPAUX_B2D_RES_RWS)]]];
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REMOVE_THEN "iha" (MP_TAC o SPECL [`Rerr e:bvi_result`; `s0:(C,FFI)bvi_state`;
      `t1:(C,FFI)data_state`; `n:num`; `corr:num list`; `F`; `live:num list`]) THEN
    ASM_REWRITE_TAC[LENGTH; PAIR_EQ] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN RVEQ_TAC THEN
    DATAPAUX_B2D_PRES_TAC `pres:((data_v list,data_v)result)option` THEN
    REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
    DATAPAUX_B2D_SEQ_SOME_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls:num option` THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC DATAPAUX_B2D_RES_RWS]);;

(* HOL4: compile_correct[Call] *)
let DATAPAUX_B2D_CC_CALL = prove
 (el 10 DATAPAUX_B2D_CC_CASES,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `handler:bvi_exp option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `hx:bvi_exp` SUBST1_TAC)) THEN
  FIRST [MATCH_ACCEPT_TAC DATAPAUX_B2D_CALL_NONE; MATCH_ACCEPT_TAC DATAPAUX_B2D_CALL_SOME]);;

let DATAPAUX_B2D_lookup_set_vars_seq = prove
 (`!n1 (xs:data_v list) (l:data_v spt) k.
     lookup k (sptree_union (fromAList (ZIP (list_of_seq (\i. n1 + i) (LENGTH xs)) xs)) l) =
     if n1 <= k /\ k < n1 + LENGTH xs then SOME (EL (k - n1) xs) else lookup k l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_union; lookup_fromAList] THEN
  SUBGOAL_THEN `LENGTH (list_of_seq (\i. n1 + i) (LENGTH (xs:data_v list))) = LENGTH xs`
    ASSUME_TAC THENL [REWRITE_TAC[LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `ALOOKUP (ZIP (list_of_seq (\i. n1 + i) (LENGTH xs)) xs) k =
                  SOME (EL (k - n1) (xs:data_v list))`
      (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[]) THEN
    MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN
    ASM_SIMP_TAC[MAP_ZIP; MEM_ZIP; ALL_DISTINCT_GENLIST] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `k - n1:num` THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ; PAIR_EQ;
      ARITH_RULE `n1 <= k /\ k < n1 + l ==> k - n1 < l`] THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `ALOOKUP (ZIP (list_of_seq (\i. n1 + i) (LENGTH xs)) (xs:data_v list)) k = NONE`
      (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[]) THEN
    ASM_SIMP_TAC[ALOOKUP_NONE; MAP_ZIP; MEM_GENLIST] THEN ASM_ARITH_TAC]);;

(* the locals after a LetCall returned: the frame with the returned values  *)
(* bound to n1, n1 + 1, ...                                                 *)
let DATAPAUX_B2D_LETCALL_START = prove
 (`!(t2:(C,FFI)data_state) n1 env corr live (xs:data_v list).
     var_corr env corr (sptree_map data_to_bvi_v (data_state_locals t2)) /\
     (!k. n1 <= k ==> lookup k (data_state_locals t2) = NONE) /\
     ALL (\n. ~(lookup n (data_state_locals t2) = NONE)) live
     ==> var_corr (APPEND (MAP data_to_bvi_v xs) env)
           (APPEND (list_of_seq (\i. n1 + i) (LENGTH xs)) corr)
           (sptree_map data_to_bvi_v
              (sptree_union (fromAList (ZIP (list_of_seq (\i. n1 + i) (LENGTH xs)) xs))
                 (mk_wf (sptree_inter (data_state_locals t2)
                           (list_to_num_set (APPEND live corr)))))) /\
         (!k. n1 + LENGTH xs <= k
              ==> lookup k (sptree_union (fromAList (ZIP (list_of_seq (\i. n1 + i) (LENGTH xs)) xs))
                              (mk_wf (sptree_inter (data_state_locals t2)
                                        (list_to_num_set (APPEND live corr))))) = NONE) /\
         ALL (\n. ~(lookup n (sptree_union (fromAList (ZIP (list_of_seq (\i. n1 + i) (LENGTH xs)) xs))
                                (mk_wf (sptree_inter (data_state_locals t2)
                                          (list_to_num_set (APPEND live corr))))) = NONE))
             live /\
         (!k x. lookup k (data_state_locals t2) = SOME x /\ (MEM k live \/ MEM k corr)
                ==> lookup k (sptree_union (fromAList (ZIP (list_of_seq (\i. n1 + i) (LENGTH xs)) xs))
                                (mk_wf (sptree_inter (data_state_locals t2)
                                          (list_to_num_set (APPEND live corr))))) = SOME x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k x. lookup k (data_state_locals (t2:(C,FFI)data_state)) = SOME x ==> k < n1`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `lookup k (data_state_locals (t2:(C,FFI)data_state)) = SOME x` THEN
    ASM_SIMP_TAC[option_DISTINCT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. MEM k corr ==> ?x. lookup k (data_state_locals (t2:(C,FFI)data_state)) = SOME x`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`env:bvl_v list`; `corr:num list`;
                   `data_state_locals (t2:(C,FFI)data_state)`] DATAPAUX_B2D_var_corr_domain) THEN
    ASM_REWRITE_TAC[SUBSET; IN_SET_OF_LIST; domain_lookup] THEN
    MESON_TAC[option_CASES; option_DISTINCT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. MEM k live ==> ?x. lookup k (data_state_locals (t2:(C,FFI)data_state)) = SOME x`
    ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\n. ~(lookup n (data_state_locals (t2:(C,FFI)data_state)) = NONE)) live` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[option_CASES; option_DISTINCT];
    ALL_TAC] THEN
  REWRITE_TAC[DATAPAUX_B2D_lookup_set_vars_seq; lookup_mk_wf; lookup_inter_alt;
              domain_list_to_num_set; MEM_APPEND] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC DATAPAUX_B2D_var_corr_APPEND THEN CONJ_TAC THENL
     [REWRITE_TAC[var_corr_def; LIST_REL_EL_EQN; LENGTH_MAP; LENGTH_LIST_OF_SEQ;
                  data_get_var_def; lookup_map] THEN
      SIMP_TAC[EL_LIST_OF_SEQ; EL_MAP] THEN
      REWRITE_TAC[DATAPAUX_B2D_lookup_set_vars_seq] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[ARITH_RULE `n1 <= n1 + i`; LT_ADD_LCANCEL; ADD_SUB2; OPTION_MAP_DEF];
      MATCH_MP_TAC DATAPAUX_B2D_var_corr_transfer THEN
      EXISTS_TAC `sptree_map data_to_bvi_v (data_state_locals (t2:(C,FFI)data_state))` THEN
      ASM_REWRITE_TAC[lookup_map; DATAPAUX_B2D_lookup_set_vars_seq; lookup_mk_wf;
                      lookup_inter_alt; domain_list_to_num_set; MEM_APPEND] THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_TAC `x:data_v` o C MATCH_MP (ASSUME `MEM (k:num) corr`) o
        check (fun th -> try rand(lhand(snd(dest_forall(concl th)))) = `corr:num list`
                         with _ -> false)) THEN
      SUBGOAL_THEN `k < (n1:num)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[option_DISTINCT];
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN `k < (n1:num)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[]]);;

(* after the continuation of a LetCall returned normally: the NONE-branch   *)
(* facts of compile_correct for the whole LetCall                           *)
let DATAPAUX_B2D_LETCALL_END = prove
 (`!(t1:(C,FFI)data_state) (t2:(C,FFI)data_state) (t4:(C,FFI)data_state)
    (t5:(C,FFI)data_state) n n1 n2 env corr live (a:bvl_v list) rs.
     (!k. n <= k ==> lookup k (data_state_locals t1) = NONE) /\ n <= n1 /\
     (!k x. lookup k (data_state_locals t1) = SOME x /\ (~MEM k live ==> MEM k corr)
            ==> lookup k (data_state_locals t2) = SOME x) /\
     data_state_stack t1 = data_state_stack t2 /\
     data_state_handler t1 = data_state_handler t2 /\
     (~(data_jump_exc t1 = NONE) ==> ~(data_jump_exc t2 = NONE)) /\
     (!k x. lookup k (data_state_locals t2) = SOME x /\ (MEM k live \/ MEM k corr)
            ==> lookup k (data_state_locals t4) = SOME x) /\
     data_state_stack t4 = data_state_stack t2 /\
     data_state_handler t4 = data_state_handler t2 /\
     LENGTH a = LENGTH rs /\ n1 <= n2 /\
     var_corr (APPEND a env) (APPEND rs corr) (sptree_map data_to_bvi_v (data_state_locals t5)) /\
     (!k x. lookup k (data_state_locals t4) = SOME x /\
            (~MEM k live ==> MEM k (APPEND rs corr))
            ==> lookup k (data_state_locals t5) = SOME x) /\
     data_state_stack t4 = data_state_stack t5 /\
     data_state_handler t4 = data_state_handler t5 /\
     (~(data_jump_exc t4 = NONE) ==> ~(data_jump_exc t5 = NONE))
     ==> n <= n2 /\
         var_corr env corr (sptree_map data_to_bvi_v (data_state_locals t5)) /\
         (!k x. lookup k (data_state_locals t1) = SOME x /\ (~MEM k live ==> MEM k corr)
                ==> lookup k (data_state_locals t5) = SOME x) /\
         data_state_stack t1 = data_state_stack t5 /\
         data_state_handler t1 = data_state_handler t5 /\
         (~(data_jump_exc t1 = NONE) ==> ~(data_jump_exc t5 = NONE))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    UNDISCH_TAC `var_corr (APPEND a env) (APPEND rs corr)
                   (sptree_map data_to_bvi_v (data_state_locals (t5:(C,FFI)data_state)))` THEN
    REWRITE_TAC[var_corr_def] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] LIST_REL_APPEND_IMP)) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> try
      rand(snd(strip_forall(concl th))) =
        `lookup k (data_state_locals (t5:(C,FFI)data_state)) = SOME x`
      with _ -> false)) THEN
    REWRITE_TAC[MEM_APPEND] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> try
      rand(snd(strip_forall(concl th))) =
        `lookup k (data_state_locals (t4:(C,FFI)data_state)) = SOME x`
      with _ -> false)) THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[DATAPAUX_B2D_jump_NONE_cong]]);;

let DATAPAUX_B2D_Seq_SOME2 = prove
 (`!c1 (t:(C,FFI)data_state) r t2.
     data_evaluate (c1,t) = (SOME r,t2)
     ==> !c2 c3. data_evaluate (data_Seq (data_Seq c1 c2) c3,t) = (SOME r,t2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DATAPAUX_B2D_Seq_SOME THEN
  MATCH_MP_TAC DATAPAUX_B2D_Seq_SOME THEN ASM_REWRITE_TAC[]);;

let DATAPAUX_B2D_Seq_NONE2 = prove
 (`!c1 (t:(C,FFI)data_state) t2.
     data_evaluate (c1,t) = (NONE,t2)
     ==> !c2 c3. data_evaluate (data_Seq (data_Seq c1 c2) c3,t) =
                 data_evaluate (data_Seq c2 c3,t2)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [data_evaluate_def] THEN
  GEN_REWRITE_TAC RAND_CONV [data_evaluate_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DSEMAUX_Seq_NONE th]) THEN
  REWRITE_TAC[data_fix_clock_evaluate]);;

let DATAPAUX_B2D_SEQ_SOME2_TAC : tactic =
  FIRST_ASSUM(fun th -> CHANGED_TAC(PURE_REWRITE_TAC[MATCH_MP DATAPAUX_B2D_Seq_SOME2 th]));;

let DATAPAUX_B2D_SEQ_NONE2_TAC : tactic =
  FIRST_ASSUM(fun th -> CHANGED_TAC(PURE_REWRITE_TAC[MATCH_MP DATAPAUX_B2D_Seq_NONE2 th]));;

(* the result of the callee of a LetCall *)
let DATAPAUX_B2D_letcall_res = prove
 (CASE_TERM `!(p:bvi_result # (C,FFI)bvi_state) rets (y:bvi_exp) env res s2.
     (match p with
        (Rval _,s) -> (Rerr (Rabort Rtype_error),s)
      | (Rerr (Rraise (Ret ret_vs)),s) ->
          if LENGTH ret_vs = rets then bvi_evaluate ([y],APPEND ret_vs env,s)
          else (Rerr (Rabort Rtype_error),s)
      | x -> x) = (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error))
     ==> ~(FST p = Rerr (Rabort Rtype_error)) /\ ~(?v. FST p = Rval v) /\
         ((?ws. FST p = Rerr (Rraise (Ret ws)) /\ LENGTH ws = rets /\
                bvi_evaluate ([y],APPEND ws env,SND p) = (res,s2)) \/
          (~(?ws. FST p = Rerr (Rraise (Ret ws))) /\ FST p = res /\ SND p = s2))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `p:bvi_result # (C,FFI)bvi_state` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:bvi_result` (X_CHOOSE_THEN `s3:(C,FFI)bvi_state`
    SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND] THEN
  MP_TAC(ISPEC `r1:bvi_result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:bvl_v list` SUBST1_TAC)
                              (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THENL
   [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN DATAPAUX_B2D_TERR_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `e:(exn_or_ret)error_result` (cases "error_result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `ex:exn_or_ret` SUBST1_TAC)
                              (X_CHOOSE_THEN `ab:abort` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THENL
   [MP_TAC(ISPEC `ex:exn_or_ret` (cases "exn_or_ret")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `w:bvl_v` SUBST1_TAC)
                                (X_CHOOSE_THEN `ws:bvl_v list` SUBST1_TAC)) THEN
    CASE_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      REWRITE_TAC DATAPAUX_B2D_RES_RWS;
      COND_CASES_TAC THENL
       [STRIP_TAC THEN REWRITE_TAC DATAPAUX_B2D_RES_RWS THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN DATAPAUX_B2D_TERR_TAC]];
    REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC DATAPAUX_B2D_RES_RWS]);;

(* HOL4: compile_correct[Letcall] *)
let DATAPAUX_B2D_CC_LETCALL = prove
 (el 11 DATAPAUX_B2D_CC_CASES,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihc")
    (CONJUNCTS_THEN2 (LABEL_TAC "ihy") (LABEL_TAC "iha"))) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN REWRITE_TAC[bvi_fix_clock_evaluate] THEN
  MP_TAC(ISPEC `bvi_evaluate (xs,env,s1:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:bvi_result` (X_CHOOSE_THEN `s0:(C,FFI)bvi_state`
    ASSUME_TAC)) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `bvi_to_data_compile n corr F live xs` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:data_prog` (X_CHOOSE_THEN `y1:num list # num` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `y1:num list # num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:num list` (X_CHOOSE_THEN `n1:num` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `bvi_to_data_compile (n1 + rets) (APPEND (list_of_seq (\i. n1 + i) rets) corr)
                  tail live [y]` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:data_prog` (X_CHOOSE_THEN `y2:num list # num` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `y2:num list # num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `v2:num list` (X_CHOOSE_THEN `n2:num` SUBST_ALL_TAC)) THEN
  ONCE_REWRITE_TAC[bvi_to_data_compile_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r0:bvi_result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:bvl_v list` SUBST_ALL_TAC)
                              (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THENL
   [REMOVE_THEN "iha" (MP_TAC o SPECL [`Rval a:bvi_result`; `s0:(C,FFI)bvi_state`;
      `t1:(C,FFI)data_state`; `n:num`; `corr:num list`; `F`; `live:num list`]) THEN
    ASM_REWRITE_TAC[LENGTH; PAIR_EQ; distinctness "result"] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN RVEQ_TAC THEN
    DATAPAUX_B2D_PRES_TAC `pres:((data_v list,data_v)result)option` THEN
    MP_TAC(ISPECL [`vs:num list`; `a:bvl_v list`; `data_state_locals (t2:(C,FFI)data_state)`]
                  get_vars_lift_thm) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `zz:data_v list` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`t1:(C,FFI)data_state`; `t2:(C,FFI)data_state`; `live:num list`;
                   `corr:num list`] DATAPAUX_B2D_ALL_live) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `bvl_find_code (SOME dest) (MAP data_to_bvi_v zz)
                    (bvi_state_code (s0:(C,FFI)bvi_state))` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2
      (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[] THEN DATAPAUX_B2D_TERR_TAC)
      (X_CHOOSE_THEN `ae:bvl_v list # bvi_exp` ASSUME_TAC)) THEN
    MP_TAC(ISPEC `ae:bvl_v list # bvi_exp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `args:bvl_v list` (X_CHOOSE_THEN `exp:bvi_exp` SUBST_ALL_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s0:(C,FFI)bvi_state`; `t2:(C,FFI)data_state`; `SOME (dest:num)`;
                   `zz:data_v list`; `args:bvl_v list`; `exp:bvi_exp`]
                  bvi_to_dataProof_find_code_lemma) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `args':data_v list` (X_CHOOSE_THEN `ss:num option`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
    SUBGOAL_THEN `data_state_clock (t2:(C,FFI)data_state) = bvi_state_clock (s0:(C,FFI)bvi_state)`
      ASSUME_TAC THENL
     [UNDISCH_TAC `bvi_to_dataProof_state_rel (s0:(C,FFI)bvi_state) (t2:(C,FFI)data_state)` THEN
      SIMP_TAC[bvi_to_dataProof_state_rel_def];
      ALL_TAC] THEN
    ASM_CASES_TAC `y = bvi_Return (list_of_seq bvi_Var rets)` THEN ASM_REWRITE_TAC[PAIR_EQ] THENL
     [ASM_CASES_TAC `bvi_state_clock (s0:(C,FFI)bvi_state) < ticks + 1` THEN
      ASM_REWRITE_TAC[] THENL
       [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
        MP_TAC(ISPECL [`s0:(C,FFI)bvi_state`; `t2:(C,FFI)data_state`; `ticks:num`;
          `NONE:(num list # num_set)option`;
          `SOME (dest:num)`; `vs:num list`; `NONE:(num # data_prog)option`; `zz:data_v list`;
          `args':data_v list`; `bvi_to_data_compile_exp (LENGTH (args':data_v list)) exp`;
          `ss:num option`] DATAPAUX_B2D_call_timeout) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)data_state` STRIP_ASSUME_TAC o SPEC `data_Skip`) THEN
        REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN DATAPAUX_B2D_SEQ_NONE_TAC THEN
        ASM_REWRITE_TAC[PAIR_EQ] THEN
        REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN CASE_REWRITE_TAC[] THEN
        ASM_REWRITE_TAC(data_to_bvi_result_def :: DATAPAUX_B2D_RES_RWS);
        MP_TAC(ISPEC `bvi_evaluate ([exp],MAP data_to_bvi_v args',
                         bvi_dec_clock (ticks + 1) (s0:(C,FFI)bvi_state))` PAIR_SURJECTIVE) THEN
        DISCH_THEN(X_CHOOSE_THEN `r4:bvi_result` (X_CHOOSE_THEN `s4:(C,FFI)bvi_state`
          ASSUME_TAC)) THEN
        ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
        SUBGOAL_THEN `(r4:bvi_result) = res /\ (s4:(C,FFI)bvi_state) = s2 /\
                      ~(?v. (res:bvi_result) = Rval v)` STRIP_ASSUME_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
             rand(concl th) = `(res:bvi_result),(s2:(C,FFI)bvi_state)`)) THEN
          MP_TAC(ISPEC `r4:bvi_result` (cases "result")) THEN
          DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a4:bvl_v list` SUBST1_TAC)
                                      (X_CHOOSE_THEN `e4:(exn_or_ret)error_result` SUBST1_TAC)) THEN
          CASE_REWRITE_TAC[] THENL
           [DATAPAUX_B2D_TERR_TAC;
            MP_TAC(ISPEC `e4:(exn_or_ret)error_result` (cases "error_result")) THEN
            DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `ex4:exn_or_ret` SUBST1_TAC)
                                        (X_CHOOSE_THEN `ab4:abort` SUBST1_TAC)) THEN
            CASE_REWRITE_TAC[] THENL
             [MP_TAC(ISPEC `ex4:exn_or_ret` (cases "exn_or_ret")) THEN
              DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `w4:bvl_v` SUBST1_TAC)
                                          (X_CHOOSE_THEN `ws4:bvl_v list` SUBST1_TAC)) THEN
              CASE_REWRITE_TAC[] THENL
               [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
                REWRITE_TAC DATAPAUX_B2D_RES_RWS;
                COND_CASES_TAC THENL
                 [ASM_SIMP_TAC[evaluate_Return_GENLIST_Var] THEN
                  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
                  REWRITE_TAC DATAPAUX_B2D_RES_RWS;
                  DATAPAUX_B2D_TERR_TAC]];
              REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
              REWRITE_TAC DATAPAUX_B2D_RES_RWS]];
          ALL_TAC] THEN
        FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `(r4:bvi_result) = res` o concl)) THEN
        FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `(s4:(C,FFI)bvi_state) = s2` o concl)) THEN
        SUBGOAL_THEN `~(bvi_state_clock (s0:(C,FFI)bvi_state) < ticks) /\
                      ~(bvi_state_clock (s0:(C,FFI)bvi_state) - ticks = 0)` STRIP_ASSUME_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `bvi_to_dataProof_state_rel (bvi_dec_clock (ticks + 1) s0)
                        (data_dec_clock (ITER ticks data_dec_clock (t2:(C,FFI)data_state)))`
          ASSUME_TAC THENL
         [MATCH_MP_TAC DATAPAUX_B2D_state_rel_ticks THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REMOVE_THEN "ihc" (MP_TAC o SPECL [`MAP data_to_bvi_v zz`; `exp:bvi_exp`;
                                          `MAP data_to_bvi_v args'`; `s0:(C,FFI)bvi_state`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPECL [`res:bvi_result`; `s2:(C,FFI)bvi_state`;
          `data_call_env args' ss (data_dec_clock (ITER ticks data_dec_clock
             (t2:(C,FFI)data_state)))`;
          `LENGTH (args':data_v list)`; `COUNT_LIST (LENGTH (args':data_v list))`; `T`;
          `[]:num list`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[DATAPAUX_B2D_state_rel_call_push; LENGTH; ONE; ALL] THEN
          REWRITE_TAC[data_call_env_def; data_dec_clock_def; funpow_dec_clock_clock;
                      LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM; jump_exc_NONE;
                      DATAPAUX_B2D_var_corr_fromList] THEN
          ASM_SIMP_TAC[lookup_fromList_outside] THEN ASM_MESON_TAC[];
          ALL_TAC] THEN
        DISCH_THEN(MP_TAC o MATCH_MP DATAPAUX_B2D_CALLEE) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `r:(data_v list,data_v)result`
          (X_CHOOSE_THEN `t3:(C,FFI)data_state`
          (X_CHOOSE_THEN `ls3:num option` STRIP_ASSUME_TAC))) THEN
        REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
        DATAPAUX_B2D_SEQ_NONE_TAC THEN
        REWRITE_TAC[evaluate_mk_ticks] THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[data_evaluate_def; FUNPOW_dec_clock_code] THEN ASM_REWRITE_TAC[] THEN
        CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[bvi_to_data_compile_exp_def] THEN
        CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
        REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls3:num option` THEN
        CASE_REWRITE_TAC[] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[data_call_env_def; data_dec_clock_def; funpow_dec_clock_clock;
                                    LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM]) THEN
        ASM_REWRITE_TAC[] THEN DATAPAUX_FAST_MESON_TAC[]];
      ASM_CASES_TAC `bvi_state_clock (s0:(C,FFI)bvi_state) < ticks + 1` THEN
      ASM_REWRITE_TAC[] THENL
       [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
        MP_TAC(ISPECL [`s0:(C,FFI)bvi_state`; `t2:(C,FFI)data_state`; `ticks:num`;
          `SOME (list_of_seq (\i. next_var + i) rets,list_to_num_set (APPEND live corr))`;
          `SOME (dest:num)`; `vs:num list`; `NONE:(num # data_prog)option`; `zz:data_v list`;
          `args':data_v list`; `bvi_to_data_compile_exp (LENGTH (args':data_v list)) exp`;
          `ss:num option`] DATAPAUX_B2D_call_timeout) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[option_DISTINCT] THEN REWRITE_TAC[option_INJ; PAIR_EQ] THEN
          REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
          REWRITE_TAC[ALL_DISTINCT_GENLIST] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC DATAPAUX_B2D_domain_live_corr THEN
          EXISTS_TAC `env:bvl_v list` THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)data_state` STRIP_ASSUME_TAC o SPEC `data_Skip`) THEN
        REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN DATAPAUX_B2D_SEQ_NONE2_TAC THEN
        DATAPAUX_B2D_SEQ_SOME_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
        REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN CASE_REWRITE_TAC[] THEN
        ASM_REWRITE_TAC(data_to_bvi_result_def :: DATAPAUX_B2D_RES_RWS);
        DISCH_THEN(MP_TAC o C CONJ (ASSUME `~(res:bvi_result = Rerr (Rabort Rtype_error))`)) THEN
        DISCH_THEN(MP_TAC o MATCH_MP DATAPAUX_B2D_letcall_res) THEN
        MP_TAC(ISPEC `bvi_evaluate ([exp],MAP data_to_bvi_v args',
                         bvi_dec_clock (ticks + 1) (s0:(C,FFI)bvi_state))` PAIR_SURJECTIVE) THEN
        DISCH_THEN(X_CHOOSE_THEN `r4:bvi_result` (X_CHOOSE_THEN `s4:(C,FFI)bvi_state`
          ASSUME_TAC)) THEN
        ASM_REWRITE_TAC[FST; SND] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
        SUBGOAL_THEN `(?v. (r4:bvi_result) = Rerr (Rraise (Exn v))) ==>
                      (?v. (res:bvi_result) = Rerr (Rraise (Exn v)))` ASSUME_TAC THENL
         [FIRST_ASSUM(MP_TAC o check (fun th -> is_disj (concl th))) THEN
          MESON_TAC[distinctness "exn_or_ret"; injectivity "result"; injectivity "error_result"];
          ALL_TAC] THEN
        SUBGOAL_THEN `~(bvi_state_clock (s0:(C,FFI)bvi_state) < ticks) /\
                      ~(bvi_state_clock (s0:(C,FFI)bvi_state) - ticks = 0)` STRIP_ASSUME_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `bvi_to_dataProof_state_rel (bvi_dec_clock (ticks + 1) s0)
                        (data_dec_clock (ITER ticks data_dec_clock (t2:(C,FFI)data_state)))`
          ASSUME_TAC THENL
         [MATCH_MP_TAC DATAPAUX_B2D_state_rel_ticks THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REMOVE_THEN "ihc" (MP_TAC o SPECL [`MAP data_to_bvi_v zz`; `exp:bvi_exp`;
                                          `MAP data_to_bvi_v args'`; `s0:(C,FFI)bvi_state`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPECL [`r4:bvi_result`; `s4:(C,FFI)bvi_state`; `data_call_env args' ss (data_push_env (mk_wf (sptree_inter
             (data_state_locals (t2:(C,FFI)data_state)) (list_to_num_set (APPEND live corr))))
             F (data_dec_clock (ITER ticks data_dec_clock t2)))`;
          `LENGTH (args':data_v list)`; `COUNT_LIST (LENGTH (args':data_v list))`; `T`;
          `[]:num list`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[DATAPAUX_B2D_state_rel_call_push; LENGTH; ONE; ALL] THEN
          REPEAT CONJ_TAC THENL
           [REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF;
                        data_state_INFO.ri_accfupds; K_THM; DATAPAUX_B2D_var_corr_fromList];
            REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF;
                        data_state_INFO.ri_accfupds; K_THM] THEN
            SIMP_TAC[lookup_fromList_outside];
            DISCH_TAC THEN MATCH_MP_TAC DATAPAUX_B2D_jump_push THEN
            REWRITE_TAC[funpow_dec_clock_clock; jump_exc_NONE] THEN
            FIRST_X_ASSUM(MATCH_MP_TAC o check ((=) `~(data_jump_exc (t1:(C,FFI)data_state) = NONE)
               ==> ~(data_jump_exc (t2:(C,FFI)data_state) = NONE)` o concl)) THEN
            FIRST_X_ASSUM(MATCH_MP_TAC o check ((=) `(?v. (res:bvi_result) = Rerr (Rraise (Exn v)))
               ==> ~(data_jump_exc (t1:(C,FFI)data_state) = NONE)` o concl)) THEN
            FIRST_X_ASSUM(MATCH_MP_TAC o check ((=) `(?v. (r4:bvi_result) = Rerr (Rraise (Exn v))) ==>
               (?v. (res:bvi_result) = Rerr (Rraise (Exn v)))` o concl)) THEN
            FIRST_ASSUM ACCEPT_TAC];
          ALL_TAC] THEN
        DISCH_THEN(MP_TAC o MATCH_MP DATAPAUX_B2D_CALLEE) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `r:(data_v list,data_v)result`
          (X_CHOOSE_THEN `t3:(C,FFI)data_state`
          (X_CHOOSE_THEN `ls3:num option` STRIP_ASSUME_TAC))) THEN
        MP_TAC(ISPECL [`t2:(C,FFI)data_state`; `env:bvl_v list`; `corr:num list`;
                       `live:num list`] DATAPAUX_B2D_cut_live_corr) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
        DATAPAUX_B2D_SEQ_NONE2_TAC THEN
        REWRITE_TAC[] THEN
        SUBGOAL_THEN `(?v. (res:bvi_result) = Rerr (Rraise (Exn v))) ==>
                      ~(data_jump_exc (t2:(C,FFI)data_state) = NONE)` ASSUME_TAC THENL
         [UNDISCH_TAC `(?v. (res:bvi_result) = Rerr (Rraise (Exn v)))
                       ==> ~(data_jump_exc (t1:(C,FFI)data_state) = NONE)` THEN
          UNDISCH_TAC `~(data_jump_exc (t1:(C,FFI)data_state) = NONE)
                       ==> ~(data_jump_exc (t2:(C,FFI)data_state) = NONE)` THEN
          MESON_TAC[];
          ALL_TAC] THEN
        FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj (concl th))) THENL
         [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `r4:bvi_result`
                                                         with _ -> false)) THEN
          FIRST_X_ASSUM(MP_TAC o REWRITE_RULE DATAPAUX_B2D_RES_RWS o
            check (fun th -> is_imp (concl th) && is_exists (rand (concl th)) &&
                             is_conj (snd (dest_exists (rand (concl th)))))) THEN
          DISCH_THEN(X_CHOOSE_THEN `vs':data_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC)) THEN
          FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o REWRITE_RULE[LENGTH_MAP] o
            check (fun th -> try rand(concl th) = `rets:num` with _ -> false)) THEN
          SUBGOAL_THEN `data_state_stack (t3:(C,FFI)data_state) =
                        CONS (data_Env (data_state_locals_size (t2:(C,FFI)data_state))
                          (mk_wf (sptree_inter (data_state_locals t2)
                                    (list_to_num_set (APPEND live corr)))))
                          (data_state_stack t2) /\
                        data_state_handler t3 = data_state_handler t2` STRIP_ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
                                                    is_disj (lhand (concl th)))) THEN
            REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def;
                        funpow_dec_clock_clock; LET_DEF; LET_END_DEF;
                        data_state_INFO.ri_accfupds; K_THM] THEN
            REWRITE_TAC DATAPAUX_B2D_RES_RWS THEN MESON_TAC[];
            ALL_TAC] THEN
          SUBGOAL_THEN `ALL_DISTINCT (list_of_seq (\i. next_var + i) (LENGTH (vs':data_v list)))` ASSUME_TAC THENL
           [REWRITE_TAC[ALL_DISTINCT_GENLIST] THEN ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `data_evaluate (mk_ticks ticks (data_Call (SOME (list_of_seq (\i. next_var + i) (LENGTH (vs':data_v list)),list_to_num_set (APPEND live corr)))
                 (SOME dest) vs NONE),t2:(C,FFI)data_state) = (NONE,data_set_vars (list_of_seq (\i. next_var + i) (LENGTH (vs':data_v list))) vs'
               (data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals (t2:(C,FFI)data_state))
                (list_to_num_set (APPEND live corr)))))
             (data_state_stack_fupd (K (data_state_stack t2))
               (data_state_locals_size_fupd (K (data_state_locals_size t2))
                 (t3:(C,FFI)data_state)))))` ASSUME_TAC THENL
           [REWRITE_TAC[evaluate_mk_ticks] THEN ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[data_evaluate_def; FUNPOW_dec_clock_code] THEN ASM_REWRITE_TAC[] THEN
            CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN
            CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
            REWRITE_TAC[data_fix_clock_evaluate; bvi_to_data_compile_exp_def] THEN
            ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
            REWRITE_TAC[LENGTH_LIST_OF_SEQ; data_pop_env_def] THEN ASM_REWRITE_TAC[] THEN
            CASE_REWRITE_TAC[];
            ALL_TAC] THEN
          DATAPAUX_B2D_SEQ_NONE_TAC THEN
          ABBREV_TAC `t4 = data_set_vars (list_of_seq (\i. next_var + i) (LENGTH (vs':data_v list))) vs'
               (data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals (t2:(C,FFI)data_state))
                (list_to_num_set (APPEND live corr)))))
             (data_state_stack_fupd (K (data_state_stack t2))
               (data_state_locals_size_fupd (K (data_state_locals_size t2))
                 (t3:(C,FFI)data_state))))` THEN
          SUBGOAL_THEN `data_state_locals (t4:(C,FFI)data_state) = sptree_union (fromAList (ZIP (list_of_seq (\i. next_var + i) (LENGTH (vs':data_v list))) vs'))
               (mk_wf (sptree_inter (data_state_locals (t2:(C,FFI)data_state))
                         (list_to_num_set (APPEND live corr)))) /\
                        data_state_stack t4 = data_state_stack t2 /\
                        data_state_handler t4 = data_state_handler t2 /\
                        bvi_to_dataProof_state_rel s4 t4 /\
                        (data_jump_exc t4 = NONE <=> data_jump_exc t2 = NONE)`
            STRIP_ASSUME_TAC THENL
           [EXPAND_TAC "t4" THEN
            REWRITE_TAC[data_set_vars_def; data_state_INFO.ri_accfupds; K_THM;
                        DATAPAUX_B2D_state_rel_fupds] THEN
            ASM_REWRITE_TAC[] THEN
            MATCH_MP_TAC DATAPAUX_B2D_jump_NONE_cong THEN
            ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM];
            ALL_TAC] THEN
          MP_TAC(ISPECL [`t2:(C,FFI)data_state`; `next_var:num`; `env:bvl_v list`;
                         `corr:num list`; `live:num list`; `vs':data_v list`]
                        DATAPAUX_B2D_LETCALL_START) THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[GSYM (ASSUME `data_state_locals (t4:(C,FFI)data_state) = sptree_union (fromAList (ZIP (list_of_seq (\i. next_var + i) (LENGTH (vs':data_v list))) vs'))
               (mk_wf (sptree_inter (data_state_locals (t2:(C,FFI)data_state))
                         (list_to_num_set (APPEND live corr))))`)] THEN
          STRIP_TAC THEN
          REMOVE_THEN "ihy" (MP_TAC o SPECL [`MAP data_to_bvi_v zz`; `exp:bvi_exp`;
             `MAP data_to_bvi_v args'`; `s0:(C,FFI)bvi_state`; `MAP data_to_bvi_v vs'`;
             `s4:(C,FFI)bvi_state`]) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
          DISCH_THEN(MP_TAC o SPECL [`res:bvi_result`; `s2:(C,FFI)bvi_state`;
             `t4:(C,FFI)data_state`; `next_var + LENGTH (vs':data_v list)`;
             `APPEND (list_of_seq (\i. next_var + i) (LENGTH (vs':data_v list))) corr`; `tail:bool`; `live:num list`]) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[LENGTH; ONE]; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `t5:(C,FFI)data_state` (X_CHOOSE_THEN `pr2:data_prog`
            (X_CHOOSE_THEN `pres2:((data_v list,data_v)result)option`
            (X_CHOOSE_THEN `vs2:num list` (X_CHOOSE_THEN `nv2:num`
            (X_CHOOSE_THEN `ls5:num option` (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC))))))) THEN
          DISCH_THEN(MP_TAC o TRANS (SYM (ASSUME
            `bvi_to_data_compile (next_var + LENGTH (vs':data_v list))
               (APPEND (list_of_seq (\i. next_var + i) (LENGTH (vs':data_v list))) corr) tail live [y] = c2,v2,n2`))) THEN
          REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(MAP_EVERY (SUBST_ALL_TAC o SYM) o CONJUNCTS) THEN
          ASM_REWRITE_TAC[PAIR_EQ] THEN REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
          EXISTS_TAC `ls5:num option` THEN
          MP_TAC(ISPEC `pres2:((data_v list,data_v)result)option` (cases "option")) THEN
          DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
            (X_CHOOSE_THEN `r2:(data_v list,data_v)result` SUBST_ALL_TAC)) THEN
          POP_ASSUM(STRIP_ASSUME_TAC o CASE_REWRITE_RULE[]) THEN CASE_REWRITE_TAC[] THENL
           [SUBGOAL_THEN `next_var <= (n2:num)` ASSUME_TAC THENL
             [MATCH_MP_TAC(ARITH_RULE `!a b c. a + b <= c ==> a <= (c:num)`) THEN
              EXISTS_TAC `LENGTH (vs':data_v list)` THEN ASM_REWRITE_TAC[];
              ALL_TAC] THEN
            SUBGOAL_THEN `data_state_stack (t2:(C,FFI)data_state) =
                            data_state_stack (t5:(C,FFI)data_state) /\
                          data_state_handler t2 = data_state_handler t5` STRIP_ASSUME_TAC THENL
             [UNDISCH_TAC `data_state_stack (t4:(C,FFI)data_state) =
                           data_state_stack (t2:(C,FFI)data_state)` THEN
              UNDISCH_TAC `data_state_handler (t4:(C,FFI)data_state) =
                           data_state_handler (t2:(C,FFI)data_state)` THEN
              UNDISCH_TAC `data_state_stack (t4:(C,FFI)data_state) =
                           data_state_stack (t5:(C,FFI)data_state)` THEN
              UNDISCH_TAC `data_state_handler (t4:(C,FFI)data_state) =
                           data_state_handler (t5:(C,FFI)data_state)` THEN
              MESON_TAC[];
              ALL_TAC] THEN
            MP_TAC(ISPECL [`t1:(C,FFI)data_state`; `t2:(C,FFI)data_state`;
              `t4:(C,FFI)data_state`; `t5:(C,FFI)data_state`; `n:num`; `next_var:num`;
              `n2:num`; `env:bvl_v list`; `corr:num list`; `live:num list`;
              `MAP data_to_bvi_v vs'`; `list_of_seq (\i. next_var + i) (LENGTH (vs':data_v list))`] DATAPAUX_B2D_LETCALL_END) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
            STRIP_TAC THEN
            ASM_REWRITE_TAC[];
            RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `data_state_stack (t4:(C,FFI)data_state) =
                                                  data_state_stack (t2:(C,FFI)data_state)`;
                                        ASSUME `data_state_handler (t4:(C,FFI)data_state) =
                                                  data_state_handler (t2:(C,FFI)data_state)`]) THEN
            ASM_REWRITE_TAC[]];
          FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `(r4:bvi_result) = res` o concl)) THEN
          FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `(s4:(C,FFI)bvi_state) = s2` o concl)) THEN
          SUBGOAL_THEN `data_to_bvi_result r = (res:bvi_result)` ASSUME_TAC THENL
           [UNDISCH_TAC `~(?vs. (res:bvi_result) = Rerr (Rraise (Ret vs)))
                         ==> data_to_bvi_result (r:(data_v list,data_v)result) = res` THEN
            ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          SUBGOAL_THEN `ALL_DISTINCT (list_of_seq (\i. next_var + i) rets)` ASSUME_TAC THENL
           [REWRITE_TAC[ALL_DISTINCT_GENLIST] THEN ARITH_TAC; ALL_TAC] THEN
          MP_TAC(ISPEC `r:(data_v list,data_v)result` (cases "result")) THEN
          DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `xs:data_v list` SUBST_ALL_TAC)
                                      (X_CHOOSE_THEN `e:(data_v)error_result` SUBST_ALL_TAC)) THENL
           [UNDISCH_TAC `~(?v. (res:bvi_result) = Rval v)` THEN
            FIRST_X_ASSUM(SUBST1_TAC o SYM o REWRITE_RULE[data_to_bvi_result_def] o
              check (fun th -> rand(concl th) = `res:bvi_result`)) THEN
            REWRITE_TAC DATAPAUX_B2D_RES_RWS;
            ALL_TAC] THEN
          MP_TAC(ISPEC `e:(data_v)error_result` (cases "error_result")) THEN
          DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `xv:data_v` SUBST_ALL_TAC)
                                      (X_CHOOSE_THEN `ab:abort` SUBST_ALL_TAC)) THENL
           [SUBGOAL_THEN `data_evaluate (mk_ticks ticks (data_Call (SOME (list_of_seq (\i. next_var + i) rets,list_to_num_set (APPEND live corr)))
                 (SOME dest) vs NONE),t2:(C,FFI)data_state) =
                            (SOME (Rerr (Rraise xv)),t3)` ASSUME_TAC THENL
             [REWRITE_TAC[evaluate_mk_ticks] THEN ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[data_evaluate_def; FUNPOW_dec_clock_code] THEN ASM_REWRITE_TAC[] THEN
            CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN
            CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
            REWRITE_TAC[data_fix_clock_evaluate; bvi_to_data_compile_exp_def] THEN
            ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]; ALL_TAC];
            SUBGOAL_THEN `data_evaluate (mk_ticks ticks (data_Call (SOME (list_of_seq (\i. next_var + i) rets,list_to_num_set (APPEND live corr)))
                 (SOME dest) vs NONE),t2:(C,FFI)data_state) =
                            (SOME (Rerr (Rabort ab)),t3)` ASSUME_TAC THENL
             [REWRITE_TAC[evaluate_mk_ticks] THEN ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[data_evaluate_def; FUNPOW_dec_clock_code] THEN ASM_REWRITE_TAC[] THEN
            CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN
            CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
            REWRITE_TAC[data_fix_clock_evaluate; bvi_to_data_compile_exp_def] THEN
            ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]; ALL_TAC]] THEN
          FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o REWRITE_RULE[data_to_bvi_result_def] o
            check (fun th -> rand(concl th) = `res:bvi_result`)) THEN
          DATAPAUX_B2D_SEQ_SOME_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
          REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls3:num option` THEN
          CASE_REWRITE_TAC[] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[data_call_env_def; data_push_env_def; data_dec_clock_def;
                                      funpow_dec_clock_clock; LET_DEF; LET_END_DEF;
                                      data_state_INFO.ri_accfupds; K_THM]) THEN
          ASM_REWRITE_TAC(data_to_bvi_result_def :: DATAPAUX_B2D_RES_RWS) THEN
          MATCH_MP_TAC DATAPAUX_B2D_jump_Env THEN
          MAP_EVERY EXISTS_TAC [`data_state_locals_size (t2:(C,FFI)data_state)`;
            `mk_wf (sptree_inter (data_state_locals (t2:(C,FFI)data_state))
                          (list_to_num_set (APPEND live corr)))`] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp (concl th) &&
             can (find_term (fun t -> try fst(dest_const t) = "data_jump_exc" with _ -> false))
                 (rand (concl th)) &&
             can (find_term (fun t -> try fst(dest_const t) = "data_Env" with _ -> false))
                 (concl th))) THEN
          REWRITE_TAC DATAPAUX_B2D_RES_RWS]]];
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REMOVE_THEN "iha" (MP_TAC o SPECL [`Rerr e:bvi_result`; `s0:(C,FFI)bvi_state`;
      `t1:(C,FFI)data_state`; `n:num`; `corr:num list`; `F`; `live:num list`]) THEN
    ASM_REWRITE_TAC[LENGTH; PAIR_EQ] THEN
    DISCH_THEN(DATAPAUX_B2D_CHOOSE_TAC []) THEN RVEQ_TAC THEN
    DATAPAUX_B2D_PRES_TAC `pres:((data_v list,data_v)result)option` THEN
    COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN
    (DATAPAUX_B2D_SEQ_SOME2_TAC ORELSE DATAPAUX_B2D_SEQ_SOME_TAC) THEN REWRITE_TAC[PAIR_EQ] THEN
    REPEAT DATAPAUX_EXISTS_EQ_ANY_TAC THEN EXISTS_TAC `ls:num option` THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC DATAPAUX_B2D_RES_RWS]);;

(* HOL4 lines 819-2892: compile_correct (Theorem at HOL4 line 819, proved  *)
(* by the suspend/Resume blocks of HOL4 lines 864-2891, Finalise at line    *)
(* 2892)                                                                     *)
let bvi_to_dataProof_compile_correct = prove
 (CASE_TERM
  `!xs env (s1:(C,FFI)bvi_state) res s2 (t1:(C,FFI)data_state) n corr tail live.
     bvi_evaluate (xs,env,s1) = (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error)) /\
     var_corr env corr (sptree_map data_to_bvi_v (data_state_locals t1)) /\
     (~(LENGTH xs = 1) ==> ~tail) /\
     (!k. n <= k ==> lookup k (data_state_locals t1) = NONE) /\
     bvi_to_dataProof_state_rel s1 t1 /\
     ALL (\n. ~(lookup n (data_state_locals t1) = NONE)) live /\
     ((?v. res = Rerr (Rraise (Exn v))) ==> ~(data_jump_exc t1 = NONE))
     ==> ?t2 prog pres vs next_var ls.
           bvi_to_data_compile n corr tail live xs = (prog,vs,next_var) /\
           data_evaluate (prog,t1) = (pres,t2) /\
           bvi_to_dataProof_state_rel s2 t2 /\
           (match pres with
              SOME r ->
                ((~(?vs. res = Rerr (Rraise (Ret vs))) ==> data_to_bvi_result r = res) /\
                 ((?vs. res = Rerr (Rraise (Ret vs)))
                  ==> ?vs'. r = Rval vs' /\
                            res = Rerr (Rraise (Ret (MAP data_to_bvi_v vs')))) /\
                 (((?v. res = Rval v) \/ (?vs. res = Rerr (Rraise (Ret vs))))
                  ==> data_state_stack t1 = data_state_stack t2 /\
                      data_state_handler t1 = data_state_handler t2) /\
                 ((?v. res = Rval v) ==> tail) /\
                 ((?v. res = Rerr (Rraise (Exn v)))
                  ==> data_jump_exc
                        (data_state_stack_fupd (K (data_state_stack t1))
                           (data_state_handler_fupd (K (data_state_handler t1)) t2)) =
                      SOME (data_state_locals_size_fupd (K ls) t2)))
            | NONE ->
                ~tail /\ n <= next_var /\
                ALL (\v. v < next_var) vs /\
                (!k. next_var <= k ==> lookup k (data_state_locals t2) = NONE) /\
                var_corr env corr (sptree_map data_to_bvi_v (data_state_locals t2)) /\
                (!k x. lookup k (data_state_locals t2) = SOME x ==> k < next_var) /\
                (!k x. lookup k (data_state_locals t1) = SOME x /\
                       (~MEM k live ==> MEM k corr)
                       ==> lookup k (data_state_locals t2) = SOME x) /\
                data_state_stack t1 = data_state_stack t2 /\
                data_state_handler t1 = data_state_handler t2 /\
                (~(data_jump_exc t1 = NONE) ==> ~(data_jump_exc t2 = NONE)) /\
                (match res with
                   Rval xs -> var_corr xs vs (sptree_map data_to_bvi_v (data_state_locals t2))
                 | _ -> F))`,
  MATCH_ACCEPT_TAC
    (REWRITE_RULE[FORALL_PAIR_THM; FST; SND]
       (MP DATAPAUX_B2D_CC_IND
          (end_itlist CONJ
             [DATAPAUX_B2D_CC_NIL; DATAPAUX_B2D_CC_CONS; DATAPAUX_B2D_CC_VAR;
              DATAPAUX_B2D_CC_IF; DATAPAUX_B2D_CC_LET; DATAPAUX_B2D_CC_RAISE;
              DATAPAUX_B2D_CC_RETURN; DATAPAUX_B2D_CC_OP; DATAPAUX_B2D_CC_TICK;
              DATAPAUX_B2D_CC_FORCE; DATAPAUX_B2D_CC_CALL; DATAPAUX_B2D_CC_LETCALL]))));;

(* local tactic: for a goal ?x1 ... xn. body where body has a conjunct     *)
(* t = x1 or x1 = t (t free of x1 ... xn), supply t as the witness for x1 *)
let B2DFINAUX_EXISTS_EQ_TAC : tactic = fun (asl,w as g) ->
  let xs,bod = strip_exists w in
  let x = hd xs in
  let ok t = not (exists (fun v -> free_in v t) xs) in
  let pick c =
    if is_eq c then
      let l,r = dest_eq c in
      if r = x && ok l then l else if l = x && ok r then r else failwith "pick"
    else failwith "pick" in
  EXISTS_TAC (tryfind pick (conjuncts bod)) g;;

(* HOL4 line 2894: val compile_exp_lemma = compile_correct |> Q.SPECL      *)
(* [[exp], env, s1, res, s2, t1, n, GENLIST I n, T, []] |> SIMP_RULE       *)
(* std_ss [LENGTH, GSYM compile_exp_def, option_case_NONE_F, PULL_EXISTS,  *)
(* EVERY_DEF]: the NONE case is impossible (tail = T), so pres = SOME r.    *)
(* Stated with the simplifications made by hand (HOL4's exact placement of  *)
(* the quantifiers may differ)                                               *)
let compile_exp_lemma = prove
 (`!exp env (s1:(C,FFI)bvi_state) res s2 (t1:(C,FFI)data_state) n.
     bvi_evaluate ([exp],env,s1) = (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error)) /\
     var_corr env (list_of_seq I n) (sptree_map data_to_bvi_v (data_state_locals t1)) /\
     (!k. n <= k ==> lookup k (data_state_locals t1) = NONE) /\
     bvi_to_dataProof_state_rel s1 t1 /\
     (!v. res = Rerr (Rraise (Exn v)) ==> ~(data_jump_exc t1 = NONE))
     ==> ?t2 prog vs next_var ls r.
           bvi_to_data_compile n (list_of_seq I n) T [] [exp] = (prog,vs,next_var) /\
           data_evaluate (prog,t1) = (SOME r,t2) /\
           bvi_to_dataProof_state_rel s2 t2 /\
           ((!vs. ~(res = Rerr (Rraise (Ret vs)))) ==> data_to_bvi_result r = res) /\
           (!vs. res = Rerr (Rraise (Ret vs))
                 ==> ?vs'. r = Rval vs' /\
                           res = Rerr (Rraise (Ret (MAP data_to_bvi_v vs')))) /\
           (((?v. res = Rval v) \/ (?vs. res = Rerr (Rraise (Ret vs))))
            ==> data_state_stack t1 = data_state_stack t2 /\
                data_state_handler t1 = data_state_handler t2) /\
           (!v. res = Rerr (Rraise (Exn v))
                ==> data_jump_exc
                      (data_state_stack_fupd (K (data_state_stack t1))
                         (data_state_handler_fupd (K (data_state_handler t1)) t2)) =
                    SOME (data_state_locals_size_fupd (K ls) t2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`[exp:bvi_exp]`; `env:bvl_v list`; `s1:(C,FFI)bvi_state`;
                 `res:bvi_result`; `s2:(C,FFI)bvi_state`; `t1:(C,FFI)data_state`;
                 `n:num`; `list_of_seq I n:num list`; `T`; `[]:num list`]
                bvi_to_dataProof_compile_correct) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ALL; LEFT_IMP_EXISTS_THM; LENGTH; ONE]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t2:(C,FFI)data_state`; `prog:data_prog`;
                       `pres:((data_v list,data_v)result)option`; `vs:num list`;
                       `next_var:num`; `ls:num option`] THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `r:(data_v list,data_v)result` SUBST1_TAC)
    (ISPEC `pres:((data_v list,data_v)result)option` (cases "option")) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t2:(C,FFI)data_state`; `prog:data_prog`; `vs:num list`;
                        `next_var:num`; `ls:num option`; `r:(data_v list,data_v)result`] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 2899: the hypotheses are those of compile_exp_lemma; HOL4's   *)
(* unused existentials prog vs next_var are left out.  As in HOL4: the      *)
(* lemma, then optimise_correct and state_rel_peak_safe                     *)
let compile_exp_correct = prove
 (`!exp env (s1:(C,FFI)bvi_state) res s2 (t1:(C,FFI)data_state) n.
     bvi_evaluate ([exp],env,s1) = (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error)) /\
     var_corr env (list_of_seq I n) (sptree_map data_to_bvi_v (data_state_locals t1)) /\
     (!k. n <= k ==> lookup k (data_state_locals t1) = NONE) /\
     bvi_to_dataProof_state_rel s1 t1 /\
     (!v. res = Rerr (Rraise (Exn v)) ==> ~(data_jump_exc t1 = NONE)) /\
     (!vs. ~(res = Rerr (Rraise (Ret vs))))
     ==> ?t2 r.
           data_evaluate (bvi_to_data_compile_exp n exp,t1) = (SOME r,t2) /\
           bvi_to_dataProof_state_rel s2 t2 /\ data_to_bvi_result r = res`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`exp:bvi_exp`; `env:bvl_v list`; `s1:(C,FFI)bvi_state`; `res:bvi_result`;
                `s2:(C,FFI)bvi_state`; `t1:(C,FFI)data_state`; `n:num`]
               compile_exp_lemma) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)data_state` (X_CHOOSE_THEN `prog:data_prog`
    (X_CHOOSE_THEN `vs:num list` (X_CHOOSE_THEN `next_var:num`
    (X_CHOOSE_THEN `ls:num option` (X_CHOOSE_THEN `r:(data_v list,data_v)result`
      STRIP_ASSUME_TAC)))))) THEN
  ASM_REWRITE_TAC[bvi_to_data_compile_exp_def; COUNT_LIST_GENLIST; FST] THEN
  MP_TAC(ISPECL [`prog:data_prog`; `t1:(C,FFI)data_state`] optimise_correct) THEN
  ASM_REWRITE_TAC[FST; option_INJ; option_DISTINCT] THEN
  ANTS_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `data_to_bvi_result (Rerr (Rabort Rtype_error)) = res` THEN
    ASM_REWRITE_TAC[data_to_bvi_result_def];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `safe:bool` (X_CHOOSE_THEN `peak:num`
    (X_CHOOSE_THEN `smx:num option` (X_CHOOSE_THEN `ls':num option` SUBST1_TAC)))) THEN
  REWRITE_TAC[PAIR_MAP_THM; I_THM; PAIR_EQ; option_INJ] THEN
  REPEAT B2DFINAUX_EXISTS_EQ_TAC THEN
  ASM_REWRITE_TAC[GSYM state_rel_peak_safe]);;

(* HOL4 line 2920 *)
let bvi_to_dataProof_state_rel_dec_clock = prove
 (`!s1 t1. bvi_to_dataProof_state_rel (s1:(C,FFI)bvi_state) (t1:(C,FFI)data_state)
           ==> bvi_to_dataProof_state_rel (bvi_dec_clock 1 s1) (data_dec_clock t1)`,
  REWRITE_TAC[DATAPAUX_B2D_state_rel_dec_clock]);;

(* ------------------------------------------------------------------------- *)
(* helpers for compile_part_evaluate                                         *)
(* ------------------------------------------------------------------------- *)

(* the start call of a BVI program (no arguments, no handler, no ticks) *)
let B2DFINAUX_bvi_call_start = prove
 (`!start (s1:(C,FFI)bvi_state) res s2.
     bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],s1) = (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error))
     ==> ?exp. lookup start (bvi_state_code s1) = SOME (0,exp) /\
               ((bvi_state_clock s1 = 0 /\ res = Rerr (Rabort Rtimeout_error) /\
                 s2 = bvi_state_clock_fupd (K 0) s1) \/
                (~(bvi_state_clock s1 = 0) /\
                 bvi_evaluate ([exp],[],bvi_dec_clock 1 s1) = (res,s2) /\
                 (!vs. ~(res = Rerr (Rraise (Ret vs))))))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  REWRITE_TAC[IS_NONE_DEF; IS_SOME_DEF] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN CASE_REWRITE_TAC[bvl_find_code_def] THEN
  MP_TAC(ISPEC `lookup start (bvi_state_code (s1:(C,FFI)bvi_state))` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `p:num#bvi_exp` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `p:num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `exp:bvi_exp` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[LENGTH] THEN
  ASM_CASES_TAC `arity = 0` THENL
   [POP_ASSUM SUBST1_TAC;
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]] THEN
  REWRITE_TAC[option_INJ; PAIR_EQ; UNWIND_THM1; ARITH_RULE `x < 0 + 1 <=> x = 0`;
              ADD_CLAUSES] THEN
  CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `bvi_evaluate ([exp],[],bvi_dec_clock 1 (s1:(C,FFI)bvi_state))`
           PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:bvi_result` (X_CHOOSE_THEN `s0:(C,FFI)bvi_state`
    SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r0:bvi_result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:bvl_v list` SUBST1_TAC)
                              (X_CHOOSE_THEN `e:(exn_or_ret)error_result` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THENL
   [ALL_TAC;
    MP_TAC(ISPEC `e:(exn_or_ret)error_result` (cases "error_result")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `ex:exn_or_ret` SUBST1_TAC)
                                (X_CHOOSE_THEN `ab:abort` SUBST1_TAC)) THEN
    CASE_REWRITE_TAC[] THENL
     [MP_TAC(ISPEC `ex:exn_or_ret` (cases "exn_or_ret")) THEN
      DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `w:bvl_v` SUBST1_TAC)
                                  (X_CHOOSE_THEN `ws:bvl_v list` SUBST1_TAC)) THEN
      CASE_REWRITE_TAC[];
      ALL_TAC]] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  ASM_REWRITE_TAC[injectivity "result"; distinctness "result"; injectivity "error_result";
                  distinctness "error_result"; injectivity "exn_or_ret";
                  distinctness "exn_or_ret"]);;

(* the data side of the start call, once the code lookup is known *)
let B2DFINAUX_data_call_start = prove
 (CASE_TERM
  `!start (t1:(C,FFI)data_state) exp.
     lookup start (data_state_code t1) = SOME (0,exp)
     ==> data_evaluate (data_Call NONE (SOME start) [] NONE,t1) =
         if data_state_clock t1 = 0
         then (SOME (Rerr (Rabort Rtimeout_error)),data_flush_state T t1)
         else match data_evaluate (exp,data_call_env []
                                    (lookup start (data_state_stack_frame_sizes t1))
                                    (data_dec_clock t1)) with
                (NONE,s) -> (SOME (Rerr (Rabort Rtype_error)),s)
              | (SOME res,s) -> (SOME res,s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[data_evaluate_def] THEN
  ASM_REWRITE_TAC[data_get_vars_def; data_find_code_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH] THEN CASE_REWRITE_TAC[]);;

(* the callee state of a call without arguments from a state without locals *)
let B2DFINAUX_call_env_nil = prove
 (`!ss (t:(C,FFI)data_state).
     data_state_locals t = LN
     ==> ?smx safe.
           data_call_env [] ss t =
           data_state_locals_size_fupd (K ss)
             (data_state_stack_max_fupd (K smx)
               (data_state_safe_for_space_fupd (K safe)
                 (data_state_peak_heap_length_fupd (K (data_state_peak_heap_length t))
                    t)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF; data_state_component_equality;
              data_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT B2DFINAUX_EXISTS_EQ_TAC THEN
  ASM_REWRITE_TAC[fromList_def; FOLDL; SND]);;

(* running a body in the callee state of a call without arguments *)
let B2DFINAUX_evaluate_call_env_nil = prove
 (`!prog (t:(C,FFI)data_state) ss r t2.
     data_state_locals t = LN /\ data_evaluate (prog,t) = (r,t2)
     ==> ?t3. data_evaluate (prog,data_call_env [] ss t) = (r,t3) /\
              !s:(C,FFI)bvi_state. bvi_to_dataProof_state_rel s t3 <=>
                                   bvi_to_dataProof_state_rel s t2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `smx:num option` (X_CHOOSE_THEN `safe:bool` SUBST1_TAC) o
              SPEC `ss:num option` o MATCH_MP B2DFINAUX_call_env_nil) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `smx1:num option` (X_CHOOSE_THEN `safe1:bool`
    (X_CHOOSE_THEN `peak1:num` ASSUME_TAC)) o
    SPECL [`smx:num option`; `safe:bool`; `data_state_peak_heap_length (t:(C,FFI)data_state)`] o
    MATCH_MP evaluate_smx_safe_peak_swap) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `xs:stack list` (X_CHOOSE_THEN `lsz:num option`
    (X_CHOOSE_THEN `sfs:num spt` (X_CHOOSE_THEN `smx2:num option`
    (X_CHOOSE_THEN `safe2:bool` (X_CHOOSE_THEN `peak2:num` STRIP_ASSUME_TAC))))) o
    SPEC `ss:num option` o MATCH_MP evaluate_swap_local_sizes) THEN
  ASM_REWRITE_TAC[PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1; EXISTS_REFL] THEN
  REWRITE_TAC[bvi_to_dataProof_state_rel_def; data_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 line 2926.  As in HOL4: unfold the two calls, look the code up    *)
(* through code_rel, the timeout case, then compile_exp_correct on the      *)
(* states with one tick less, evaluate_smx_safe_peak_swap and               *)
(* evaluate_swap_local_sizes for the callee state of call_env               *)
let compile_part_evaluate = prove
 (`!start s1 res s2 t1.
     bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],(s1:(C,FFI)bvi_state)) =
       (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error)) /\
     bvi_to_dataProof_state_rel s1 (t1:(C,FFI)data_state) /\
     data_state_locals t1 = LN /\
     (!x. res = Rerr (Rraise x) ==> ~(data_jump_exc t1 = NONE))
     ==> ?r t2.
           data_evaluate (data_Call NONE (SOME start) [] NONE,t1) = (SOME r,t2) /\
           bvi_to_dataProof_state_rel s2 t2 /\ data_to_bvi_result r = res`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`start:num`; `s1:(C,FFI)bvi_state`; `res:bvi_result`;
                `s2:(C,FFI)bvi_state`] B2DFINAUX_bvi_call_start) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `exp:bvi_exp` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `lookup start (data_state_code (t1:(C,FFI)data_state)) =
                SOME (0,bvi_to_data_compile_exp 0 exp) /\
                data_state_clock t1 = bvi_state_clock (s1:(C,FFI)bvi_state)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `bvi_to_dataProof_state_rel (s1:(C,FFI)bvi_state) (t1:(C,FFI)data_state)` THEN
    REWRITE_TAC[bvi_to_dataProof_state_rel_def; bvi_to_dataProof_code_rel_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP B2DFINAUX_data_call_start) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ; option_INJ] THEN REPEAT B2DFINAUX_EXISTS_EQ_TAC THEN
    ASM_REWRITE_TAC[data_to_bvi_result_def] THEN
    UNDISCH_TAC `bvi_to_dataProof_state_rel (s1:(C,FFI)bvi_state) (t1:(C,FFI)data_state)` THEN
    REWRITE_TAC[bvi_to_dataProof_state_rel_def; data_flush_state_def;
                bvi_state_INFO.ri_accfupds; data_state_INFO.ri_accfupds; K_THM] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`exp:bvi_exp`; `[]:bvl_v list`; `bvi_dec_clock 1 (s1:(C,FFI)bvi_state)`;
                `res:bvi_result`; `s2:(C,FFI)bvi_state`;
                `data_dec_clock (t1:(C,FFI)data_state)`; `0`] compile_exp_correct) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[list_of_seq; var_corr_def; ALL2; data_dec_clock_def;
                    data_state_INFO.ri_accfupds; K_THM; lookup_rwts; jump_exc_NONE] THEN
    UNDISCH_TAC `bvi_to_dataProof_state_rel (s1:(C,FFI)bvi_state) (t1:(C,FFI)data_state)` THEN
    REWRITE_TAC[bvi_to_dataProof_state_rel_def; bvi_dec_clock_def;
                bvi_state_INFO.ri_accfupds; data_state_INFO.ri_accfupds; K_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)data_state` (X_CHOOSE_THEN
    `r:(data_v list,data_v)result` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`bvi_to_data_compile_exp 0 exp`; `data_dec_clock (t1:(C,FFI)data_state)`;
                `lookup start (data_state_stack_frame_sizes (t1:(C,FFI)data_state))`;
                `SOME (r:(data_v list,data_v)result)`; `t2:(C,FFI)data_state`]
               B2DFINAUX_evaluate_call_env_nil) THEN
  ASM_REWRITE_TAC[data_dec_clock_def; data_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)data_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ; option_INJ] THEN
  REPEAT B2DFINAUX_EXISTS_EQ_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 2984 *)
let bvi_to_dataProof_MAP_FST_compile_prog = prove
 (`!prog. MAP FST (bvi_to_data_compile_prog prog) = MAP FST prog`,
  REWRITE_TAC[bvi_to_data_compile_prog_def; GSYM MAP_o] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; o_THM; CONS_11] THEN
  MP_TAC(ISPEC `h:num#num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `b:num#bvi_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `b:num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_THEN `d:bvi_exp` SUBST1_TAC)) THEN
  REWRITE_TAC[bvi_to_data_compile_part_def; FST]);;
let _ = cake_add_simps [bvi_to_dataProof_MAP_FST_compile_prog];;

(* HOL4 line 2990: compile_part_evaluate on the initial states            *)
let bvi_to_dataProof_compile_prog_evaluate = prove
 (`!start ffi0 prog co cc k r s lims ss.
     bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                   bvi_initial_state (ffi0:(FFI)ffi_state) (fromAList prog)
                     (co:num -> C # (num # num # bvi_exp) list)
                     (\cfg prog. cc cfg (bvi_to_data_compile_prog prog)) k) = (r,s) /\
     ~(r = Rerr (Rabort Rtype_error)) /\ (!x. ~(r = Rerr (Rraise x)))
     ==> ?r2 s2.
           data_evaluate (data_Call NONE (SOME start) [] NONE,
                          data_initial_state ffi0 (fromAList (bvi_to_data_compile_prog prog))
                            ((I ## bvi_to_data_compile_prog) o co) cc T lims ss k) =
             (SOME r2,s2) /\
           bvi_to_dataProof_state_rel s s2 /\ data_to_bvi_result r2 = r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC compile_part_evaluate THEN
  EXISTS_TAC `bvi_initial_state (ffi0:(FFI)ffi_state) (fromAList prog)
                (co:num -> C # (num # num # bvi_exp) list)
                (\cfg prog. cc cfg (bvi_to_data_compile_prog prog)) k` THEN
  ASM_REWRITE_TAC[bvi_initial_state_def; data_initial_state_def;
                  bvi_state_INFO.ri_accessors; data_state_INFO.ri_accessors;
                  bvi_to_dataProof_state_rel_def; bvi_to_dataProof_code_rel_def;
                  wf_fromAList; domain_fromAList; lookup_fromAList; FLOOKUP_EMPTY;
                  sptree_map_def; lookup_rwts] THEN
  REWRITE_TAC[bvi_to_data_compile_prog_def; compile_part_thm] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAP_MAP_o] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[ALOOKUP_MAP; o_THM] THEN
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[OPTION_MAP_DEF]);;

(* HOL4 line 3007 *)
let bvi_to_dataProof_FST_compile_part = prove
 (`!a. FST (bvi_to_data_compile_part a) = FST a`,
  GEN_TAC THEN
  MP_TAC(ISPEC `a:num#num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num` (X_CHOOSE_THEN `b:num#bvi_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `b:num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_THEN `d:bvi_exp` SUBST1_TAC)) THEN
  REWRITE_TAC[bvi_to_data_compile_part_def; FST]);;
let _ = cake_add_simps [bvi_to_dataProof_FST_compile_part];;

(* ------------------------------------------------------------------------- *)
(* helpers for compile_prog_semantics                                        *)
(* ------------------------------------------------------------------------- *)

(* the BVI not-Fail condition, as it appears in bvi_semantics *)
let B2DFINAUX_bvi_cond = prove
 (`!(ffi:(FFI)ffi_state) code (co:num -> C # (num#num#bvi_exp) list) cc start.
     ~(bvi_semantics ffi code co cc start = Fail)
     ==> ~(?k e. FST (bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                                    bvi_initial_state ffi code co cc k)) = Rerr e /\
                 ~(e = Rabort Rtimeout_error) /\ (!f. ~(e = Rabort (Rffi_error f))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_semantics_def; LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* a BVI program whose semantics is not Fail never stops with an error other *)
(* than a timeout or an FFI error                                            *)
let B2DFINAUX_bvi_not_fail = prove
 (`!(ffi:(FFI)ffi_state) code (co:num -> C # (num#num#bvi_exp) list) cc start k e.
     ~(bvi_semantics ffi code co cc start = Fail) /\
     FST (bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                        bvi_initial_state ffi code co cc k)) = Rerr e
     ==> e = Rabort Rtimeout_error \/ (?f. e = Rabort (Rffi_error f))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP B2DFINAUX_bvi_cond) ASSUME_TAC) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`k:num`; `e:(exn_or_ret)error_result`]) THEN
  ASM_REWRITE_TAC[DE_MORGAN_THM; NOT_FORALL_THM] THEN MESON_TAC[]);;

(* the runs of the start call with the same clock, in lock step *)
let B2DFINAUX_sem_step = prove
 (`!(ffi0:(FFI)ffi_state) prog (co:num -> C # (num # num # bvi_exp) list) cc start
    lim ss k.
     ~(bvi_semantics ffi0 (fromAList prog) co
         (\cfg prog. cc cfg (bvi_to_data_compile_prog prog)) start = Fail)
     ==> ?r2 s2.
           data_evaluate (data_Call NONE (SOME start) [] NONE,
                          data_initial_state ffi0 (fromAList (bvi_to_data_compile_prog prog))
                            ((I ## bvi_to_data_compile_prog) o co) cc T lim ss k) =
             (SOME r2,s2) /\
           data_to_bvi_result r2 =
             FST (bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                    bvi_initial_state ffi0 (fromAList prog) co
                      (\cfg prog. cc cfg (bvi_to_data_compile_prog prog)) k)) /\
           data_state_ffi s2 =
             bvi_state_ffi (SND (bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                    bvi_initial_state ffi0 (fromAList prog) co
                      (\cfg prog. cc cfg (bvi_to_data_compile_prog prog)) k)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                    bvi_initial_state (ffi0:(FFI)ffi_state) (fromAList prog)
                      (co:num -> C # (num # num # bvi_exp) list)
                      (\cfg prog. cc cfg (bvi_to_data_compile_prog prog)) k)`
                PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:bvi_result` (X_CHOOSE_THEN `s:(C,FFI)bvi_state`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  MP_TAC(SPECL [`start:num`; `ffi0:(FFI)ffi_state`; `prog:(num#num#bvi_exp)list`;
                `co:num -> C # (num # num # bvi_exp) list`;
                `cc:C -> (num#num#data_prog)list -> (byte list # int64 list # C) option`;
                `k:num`; `r:bvi_result`; `s:(C,FFI)bvi_state`; `lim:limits`; `ss:num spt`]
               bvi_to_dataProof_compile_prog_evaluate) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`ffi0:(FFI)ffi_state`; `fromAList prog:(num#bvi_exp)spt`;
                  `co:num -> C # (num # num # bvi_exp) list`;
                  `\cfg prog. (cc:C -> (num#num#data_prog)list ->
                                   (byte list # int64 list # C) option)
                                 cfg (bvi_to_data_compile_prog prog)`;
                  `start:num`; `k:num`] B2DFINAUX_bvi_not_fail) THEN
    ASM_REWRITE_TAC[FST] THEN
    DISCH_THEN(fun th -> CONJ_TAC THENL
      [DISCH_THEN(MP_TAC o MATCH_MP th); GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP th)]) THEN
    REWRITE_TAC[injectivity "error_result"; distinctness "error_result";
                injectivity "abort"; distinctness "abort"];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(data_v list,data_v)result` (X_CHOOSE_THEN
    `s2:(C,FFI)data_state` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r2:(data_v list,data_v)result`; `s2:(C,FFI)data_state`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `bvi_to_dataProof_state_rel (s:(C,FFI)bvi_state) (s2:(C,FFI)data_state)` THEN
  SIMP_TAC[bvi_to_dataProof_state_rel_def]);;

(* the outcome of a data result and of its BVI image *)
let B2DFINAUX_outcome_eq = prove
 (CASE_TERM
  `!(r:(data_v list,data_v)result) outcome.
     (match data_to_bvi_result r with
        Rerr (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
      | Rval _ -> outcome = Success
      | _ -> F) <=>
     (match r with
        Rerr (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
      | Rval _ -> outcome = Success
      | _ -> F)`,
  GEN_TAC THEN
  MP_TAC(ISPEC `r:(data_v list,data_v)result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:data_v list` SUBST1_TAC)
                              (X_CHOOSE_THEN `e:(data_v)error_result` SUBST1_TAC)) THEN
  REWRITE_TAC[data_to_bvi_result_def] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `e:(data_v)error_result` (cases "error_result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:data_v` SUBST1_TAC)
                              (X_CHOOSE_THEN `ab:abort` SUBST1_TAC)) THEN
  REWRITE_TAC[data_to_bvi_result_def] THEN CASE_REWRITE_TAC[]);;

(* the data side of compile_prog_semantics never fails *)
let B2DFINAUX_data_not_fail = prove
 (CASE_TERM
  `!(ffi0:(FFI)ffi_state) prog (co:num -> C # (num # num # bvi_exp) list) cc start
    lim ss k.
     ~(bvi_semantics ffi0 (fromAList prog) co
         (\cfg prog. cc cfg (bvi_to_data_compile_prog prog)) start = Fail)
     ==> ~(match FST (data_evaluate (data_Call NONE (SOME start) [] NONE,
                        data_initial_state ffi0
                          (fromAList (bvi_to_data_compile_prog prog))
                          ((I ## bvi_to_data_compile_prog) o co) cc T lim ss k)) with
             SOME (Rerr e) -> ~(e = Rabort Rtimeout_error) /\
                              (!f. ~(e = Rabort (Rffi_error f)))
           | NONE -> T
           | _ -> F)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`ffi0:(FFI)ffi_state`; `prog:(num#num#bvi_exp)list`;
                `co:num -> C # (num # num # bvi_exp) list`;
                `cc:C -> (num#num#data_prog)list -> (byte list # int64 list # C) option`;
                `start:num`; `lim:limits`; `ss:num spt`; `k:num`] B2DFINAUX_sem_step) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(data_v list,data_v)result` (X_CHOOSE_THEN
    `s2:(C,FFI)data_state` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`ffi0:(FFI)ffi_state`; `fromAList prog:(num#bvi_exp)spt`;
                `co:num -> C # (num # num # bvi_exp) list`;
                `\cfg prog. (cc:C -> (num#num#data_prog)list ->
                                 (byte list # int64 list # C) option)
                               cfg (bvi_to_data_compile_prog prog)`;
                `start:num`; `k:num`] B2DFINAUX_bvi_not_fail) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) && is_comb (lhs (concl th)) &&
                           fst (strip_comb (lhs (concl th))) = `data_to_bvi_result`
                        then REWRITE_TAC[SYM th] else failwith "not it") THEN
  MP_TAC(ISPEC `r2:(data_v list,data_v)result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:data_v list` SUBST1_TAC)
                              (X_CHOOSE_THEN `e:(data_v)error_result` SUBST1_TAC)) THEN
  REWRITE_TAC[data_to_bvi_result_def] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `e:(data_v)error_result` (cases "error_result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:data_v` SUBST1_TAC)
                              (X_CHOOSE_THEN `ab:abort` SUBST1_TAC)) THEN
  REWRITE_TAC[data_to_bvi_result_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_UNWIND_THM1; FORALL_UNWIND_THM2; injectivity "error_result";
              distinctness "error_result"; injectivity "abort"; distinctness "abort"] THEN
  MESON_TAC[]);;

(* the terminating runs of the two sides of compile_prog_semantics agree   *)
(* clock by clock                                                         *)
let B2DFINAUX_sem_term = prove
 (CASE_TERM
  `!(ffi0:(FFI)ffi_state) prog (co:num -> C # (num # num # bvi_exp) list) cc start
    lim ss k res.
     ~(bvi_semantics ffi0 (fromAList prog) co
         (\cfg prog. cc cfg (bvi_to_data_compile_prog prog)) start = Fail)
     ==> ((?s r outcome.
             data_evaluate (data_Call NONE (SOME start) [] NONE,
                            data_initial_state ffi0
                              (fromAList (bvi_to_data_compile_prog prog))
                              ((I ## bvi_to_data_compile_prog) o co) cc T lim ss k) =
               (SOME r,s) /\
             (match r with
                Rerr (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
              | Rval _ -> outcome = Success
              | _ -> F) /\
             res = Terminate outcome (ffi_state_io_events (data_state_ffi s))) <=>
          (?s' r' outcome.
             bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                           bvi_initial_state ffi0 (fromAList prog) co
                             (\cfg prog. cc cfg (bvi_to_data_compile_prog prog)) k) =
               (r',s') /\
             (match r' with
                Rerr (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
              | Rval _ -> outcome = Success
              | _ -> F) /\
             res = Terminate outcome (ffi_state_io_events (bvi_state_ffi s'))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`ffi0:(FFI)ffi_state`; `prog:(num#num#bvi_exp)list`;
                `co:num -> C # (num # num # bvi_exp) list`;
                `cc:C -> (num#num#data_prog)list -> (byte list # int64 list # C) option`;
                `start:num`; `lim:limits`; `ss:num spt`; `k:num`] B2DFINAUX_sem_step) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(data_v list,data_v)result` (X_CHOOSE_THEN
    `s2:(C,FFI)data_state` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                    bvi_initial_state (ffi0:(FFI)ffi_state) (fromAList prog)
                      (co:num -> C # (num # num # bvi_exp) list)
                      (\cfg prog. (cc:C -> (num#num#data_prog)list ->
                                       (byte list # int64 list # C) option)
                                     cfg (bvi_to_data_compile_prog prog)) k)`
                PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `rb:bvi_result` (X_CHOOSE_THEN `sb:(C,FFI)bvi_state`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; FST; SND]) THEN ASSUME_TAC th))) THEN
  ASM_REWRITE_TAC[PAIR_EQ; option_INJ] THEN SIMP[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
     rhs (concl th) = `rb:bvi_result`)) THEN
  ASM_REWRITE_TAC[B2DFINAUX_outcome_eq]);;

(* the io events of the two sides of compile_prog_semantics agree clock by *)
(* clock                                                                  *)
let B2DFINAUX_sem_ffi = prove
 (`!(ffi0:(FFI)ffi_state) prog (co:num -> C # (num # num # bvi_exp) list) cc start
    lim ss k.
     ~(bvi_semantics ffi0 (fromAList prog) co
         (\cfg prog. cc cfg (bvi_to_data_compile_prog prog)) start = Fail)
     ==> data_state_ffi
           (SND (data_evaluate (data_Call NONE (SOME start) [] NONE,
                   data_initial_state ffi0 (fromAList (bvi_to_data_compile_prog prog))
                     ((I ## bvi_to_data_compile_prog) o co) cc T lim ss k))) =
         bvi_state_ffi (SND (bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                   bvi_initial_state ffi0 (fromAList prog) co
                     (\cfg prog. cc cfg (bvi_to_data_compile_prog prog)) k)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`lim:limits`; `ss:num spt`; `k:num`] o
             MATCH_MP B2DFINAUX_sem_step) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[SND]);;

(* HOL4 line 3015.  HOL4 unfolds both semantics and uses DEEP_INTRO_TAC    *)
(* some_intro on each side, relating runs with different clocks by the     *)
(* clock lemmas; compile_prog_evaluate relates the runs with the same      *)
(* clock, so here both Fail conditions are false and the predicate under   *)
(* some and the io-event chains agree clock by clock (the helpers above).  *)
let bvi_to_dataProof_compile_prog_semantics = prove
 (`!ffi0 prog co cc start lim ss.
     ~(bvi_semantics (ffi0:(FFI)ffi_state) (fromAList prog)
         (co:num -> C # (num # num # bvi_exp) list)
         (\cfg prog. cc cfg (bvi_to_data_compile_prog prog)) start = Fail)
     ==> data_semantics ffi0 (fromAList (bvi_to_data_compile_prog prog))
           ((I ## bvi_to_data_compile_prog) o co) cc lim ss start =
         bvi_semantics ffi0 (fromAList prog) co
           (\cfg prog. cc cfg (bvi_to_data_compile_prog prog)) start`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[data_semantics_def; bvi_semantics_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP B2DFINAUX_bvi_cond th; MATCH_MP B2DFINAUX_data_not_fail th;
                MATCH_MP B2DFINAUX_sem_term th; MATCH_MP B2DFINAUX_sem_ffi th]));;

(* HOL4 line 3124 *)
let get_code_labels_iAssign = prove
 (`!a b c d e. data_get_code_labels (iAssign a b c d e) = assign_get_code_label b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[iAssign_def; LET_DEF; LET_END_DEF] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[data_get_code_labels_def; assign_get_code_label_def; UNION_EMPTY]);;
let _ = cake_add_simps [get_code_labels_iAssign];;

(* local helper: the ticks of mk_ticks have no code labels *)
let DATAPAUX_B2D_labels_mk_ticks = prove
 (`!n m. data_get_code_labels (mk_ticks n m) = data_get_code_labels m`,
  INDUCT_TAC THEN REWRITE_TAC[mk_ticks_def; ITER] THEN
  REWRITE_TAC[GSYM mk_ticks_def; data_get_code_labels_def; UNION_EMPTY] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 3131 *)
let bvi_to_dataProof_get_code_labels_compile = prove
 (`!a b c d e.
     data_get_code_labels (FST (bvi_to_data_compile a b c d e)) SUBSET
     UNIONS (set_of_list (MAP bvi_get_code_labels e))`,
  let keep_subset_tac : tactic = fun (asl,w) ->
    let is_sub th = can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET"))
                        (concl th) in
    let ths = filter (fun (_,th) -> is_sub th) asl in
    (POP_ASSUM_LIST (K ALL_TAC) THEN MAP_EVERY (fun (_,th) -> ASSUME_TAC th) ths) (asl,w) in
  let rws = [data_get_code_labels_def; bvi_get_code_labels_def; MAP; set_of_list;
             UNIONS_INSERT; UNIONS_0; get_code_labels_iAssign;
             DATAPAUX_B2D_labels_mk_ticks; UNION_EMPTY; EMPTY_SUBSET] in
  MATCH_MP_TAC bvi_to_data_compile_ind THEN REPEAT CONJ_TAC THEN
  WORDP3AUX_IND_STEP_TAC ALL_TAC THEN
  REWRITE_TAC rws THEN CASE_REWRITE_TAC rws THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; set_of_list; UNIONS_INSERT; UNIONS_0; UNION_EMPTY]) THEN
  keep_subset_tac THEN ASM SET_TAC[]);;

(* local helper for compile_prog_good_code_labels: one function body *)
let DATAPAUX_B2D_labels_compile_exp = prove
 (`!ac exp. data_get_code_labels (bvi_to_data_compile_exp ac exp) SUBSET
            bvi_get_code_labels exp`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_to_data_compile_exp_def; bvi_to_data_optimise_def;
              data_spaceProof_get_code_labels_compile] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `data_get_code_labels (FST (data_live_compile
                (FST (bvi_to_data_compile ac (COUNT_LIST ac) T [] [exp])) LN)) UNION
              data_get_code_labels data_Skip` THEN
  REWRITE_TAC[get_code_labels_simp] THEN
  REWRITE_TAC[data_get_code_labels_def; UNION_EMPTY] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `data_get_code_labels (FST (bvi_to_data_compile ac (COUNT_LIST ac) T [] [exp]))` THEN
  REWRITE_TAC[data_liveProof_get_code_labels_compile] THEN
  MP_TAC(ISPECL [`ac:num`; `COUNT_LIST ac`; `T`; `[]:num list`; `[exp:bvi_exp]`]
                bvi_to_dataProof_get_code_labels_compile) THEN
  REWRITE_TAC[MAP; set_of_list; UNIONS_INSERT; UNIONS_0; UNION_EMPTY]);;

(* HOL4 line 3150 *)
let bvi_to_dataProof_compile_prog_good_code_labels = prove
 (`!p elabs. bvi_good_code_labels p elabs
             ==> data_good_code_labels (bvi_to_data_compile_prog p) elabs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_good_code_labels_def; data_good_code_labels_def;
              bvi_to_dataProof_MAP_FST_compile_prog] THEN
  MATCH_MP_TAC(SET_RULE `(A:num->bool) SUBSET B ==> B SUBSET C ==> A SUBSET C`) THEN
  REWRITE_TAC[bvi_to_data_compile_prog_def] THEN
  SPEC_TAC(`p:(num#num#bvi_exp)list`,`p:(num#num#bvi_exp)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; set_of_list; UNIONS_INSERT; SUBSET_REFL] THEN
  MP_TAC(ISPEC `h:num#num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `b:num#bvi_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `b:num#bvi_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_THEN `d:bvi_exp` SUBST1_TAC)) THEN
  REWRITE_TAC[bvi_to_data_compile_part_def; o_THM; SND] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  MP_TAC(ISPECL [`c:num`; `d:bvi_exp`] DATAPAUX_B2D_labels_compile_exp) THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;
