(* ========================================================================= *)
(* pan_structsProof: port of HOL4 pancake/proofs/pan_structsProofScript.sml  *)
(* (CakeML v3479).  Correctness proof for pan_structs (named structs to      *)
(* raw structs).                                                             *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says (pan_structsProof_compile_correct,          *)
(*   pan_structsProof_compile_exp_correct, ...); PPASS1AUX_ names are local  *)
(*   helpers (lemmas and the case tactics of compile_correct).               *)
(* - HOL4 paired lambdas are written with match; HOL4 r.f is RECTYPE_f r and *)
(*   r with f := v is RECTYPE_f_fupd (K v) r; the literal <| structs := [] |> *)
(*   is pan_structs_context_structs_fupd (K []) ARB, as HOL4 builds it.      *)
(* - Theorems that HOL4 derives with a rule (shape_of_convert_v_rev,         *)
(*   convert_res_eq_case, convert_res_eq_NONE) are stated as the results.    *)
(* - Binders that do not occur in the HOL4 statement are dropped (n of       *)
(*   shape_of_convert_v, ctxt of decs_stcnames_infos_ok).                    *)
(* - ZIP is HOL Light ZIP; map_uncurry_zip_again keeps HOL4's LENGTH         *)
(*   hypothesis, and every ZIP of the proofs has arguments of equal length.  *)
(* - semantics_eq is proved from compile_correct at equal clocks             *)
(*   (convert_s keeps the clock and the ffi state) with                      *)
(*   PPASS1AUX_pan_semantics_cong2; HOL4 goes through pan_sem_is_wrapper and *)
(*   semantics_wrapper_eq.                                                   *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/libext.ml";;
needs "pancake/semantics/panSem.ml";;
needs "pancake/pan_structs.ml";;
needs "pancake/semantics/pan_commonProps.ml";;
needs "pancake/semantics/panProps.ml";;

type_invention_error := true;;

let compile_exps_eq_map = prove
 (`pan_structs_compile_exps ctxt =
   MAP (pan_structs_compile_exp ctxt:(A)panLang_exp->(A)panLang_exp)`,
  REWRITE_TAC[FUN_EQ_THM] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[pan_structs_compile_exp_def; MAP]);;

let opt_mmap_eq_some_el = prove
 (`!xs ys. OPT_MMAP (f:A->B option) xs = SOME ys <=>
           LENGTH xs = LENGTH ys /\
           (!n. n < LENGTH ys ==> f (EL n xs) = SOME (EL n ys))`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:B list` list_CASES) THEN
  ASM_REWRITE_TAC[OPT_MMAP_def; LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ;
                  OPTION_BIND_EQUALS_OPTION; option_INJ; NOT_CONS_NIL; CONS_11;
                  CONJUNCT1 LT; LISTAUX_FORALL_LT_SUC; EL; HD; TL] THEN
  MESON_TAC[]);;

(* termination of convert_v and v_flds_ok: a call on v for MEM (nm,v) flds; *)
(* panSem's PSEMAUX_MEM_IMP_v_size bounds its size                           *)
let PPASS1AUX_V_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MEM_MAP]) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC)) THEN RVEQ_TAC THEN
  (fun (asl,w as g) ->
     let th0 = ISPEC `ARB:A->num` PSEMAUX_MEM_IMP_v_size in
     MAP_EVERY ASSUME_TAC (mapfilter (fun (_,th) -> MATCH_MP th0 th) asl) g) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SND]) THEN TERM_TAC;;

let convert_v_def = cake_def_wf
  `MEASURE (pan_v_size (ARB:A->num))`
  PPASS1AUX_V_TC_TAC
  `(convert_v (pan_Val x:(A)pan_v) = pan_Val x) /\
   (convert_v (pan_RStruct xs) = pan_RStruct (MAP convert_v xs)) /\
   (convert_v (pan_NStruct nm flds) =
      let vs = MAP (\p. match p with (nm,v) -> convert_v v) flds in
      pan_RStruct vs)`;;

let convert_v_ind = cake_ind "convert_v";;

let v_flds_ok_def = cake_def_wf
  `MEASURE (\p:(mlstring#struct_info)list#(A)pan_v. pan_v_size (ARB:A->num) (SND p))`
  PPASS1AUX_V_TC_TAC
  `(v_flds_ok (_:(mlstring#struct_info)list) (pan_Val x:(A)pan_v) <=> T) /\
   (v_flds_ok ctxt (pan_RStruct vs) <=> ALL (v_flds_ok ctxt) vs) /\
   (v_flds_ok ctxt (pan_NStruct nm flds) <=>
      ALL (\p. match p with (nm,v) -> v_flds_ok ctxt v) flds /\
      (match ALOOKUP ctxt nm with
         NONE -> F
       | SOME info ->
           MAP FST flds = MAP FST (struct_info_fields info) /\
           MAP (shape_of o SND) flds = MAP SND (struct_info_fields info)))`;;

let v_flds_ok_ind = cake_ind "v_flds_ok";;

let convert_eshapes_def = cake_def
  `convert_eshapes (str_ctxt:(mlstring#((B#shape)list))list) =
     FMAP_MAP2 (\p:mlstring#shape. match p with
                  (eid,sh) -> compile_shape str_ctxt sh)`;;

let convert_code_def = cake_def
  `convert_code (ctxt:pan_structs_context) =
     FMAP_MAP2 (\p:mlstring#((mlstring#shape)list#(A)panLang_prog#shape).
       match p with
         (nm,(params,prog,rshape)) ->
           (MAP (I ## compile_shape (pan_structs_context_structs ctxt)) params,
            pan_structs_compile (pan_structs_context_locals_fupd (K params) ctxt) prog,
            compile_shape (pan_structs_context_structs ctxt) rshape))`;;

let convert_s_def = cake_def
  `convert_s (ctxt:pan_structs_context) (s:(A,FFI)pan_state) =
     pan_state_locals_fupd
       (K (FMAP_MAP2 (\p. match p with (nm,v) -> convert_v v) (pan_state_locals s)))
     (pan_state_globals_fupd
       (K (FMAP_MAP2 (\p. match p with (nm,v) -> convert_v v) (pan_state_globals s)))
     (pan_state_structs_fupd (K [])
     (pan_state_code_fupd (K (convert_code ctxt (pan_state_code s)))
     (pan_state_eshapes_fupd
       (K (convert_eshapes (pan_structs_context_structs ctxt) (pan_state_eshapes s))) s))))`;;

let struct_infos_ok_def = cake_def
 `struct_infos_ok (sh_ctxt:(mlstring#struct_info)list) <=>
    ALL (\p. match p with
               (nm,info) -> ALL_DISTINCT (MAP FST (struct_info_fields info))) sh_ctxt /\
    ALL_DISTINCT (MAP FST sh_ctxt) /\
    (!i nm info. i < LENGTH sh_ctxt /\ EL i sh_ctxt = (nm,info) ==>
       ALL (is_wf_shape (DROP (i + 1) sh_ctxt)) (MAP SND (struct_info_fields info))) /\
    ALL (\p. match p with
               (nm,info) ->
                 struct_info_size info =
                 size_of_sh_with_ctxt sh_ctxt (Comb (MAP SND (struct_info_fields info))))
        sh_ctxt`;;

let alookup_drop_helper = prove
 (`ALOOKUP (DROP n xs) k = SOME (v:B) /\ ALL_DISTINCT (MAP FST (xs:(A#B)list)) ==>
   ~MEM k (MAP FST (TAKE n xs)) /\ ALOOKUP xs k = SOME v`,
  STRIP_TAC THEN
  SUBGOAL_THEN `MEM (k:A) (MAP FST (DROP n (xs:(A#B)list)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[ALOOKUP_NONE; option_DISTINCT]; ALL_TAC] THEN
  SUBGOAL_THEN `~MEM (k:A) (MAP FST (TAKE n (xs:(A#B)list)))` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL_DISTINCT (MAP FST (xs:(A#B)list))` THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
      [GSYM(ISPEC `n:num` TAKE_DROP)] THEN
    REWRITE_TAC[MAP_APPEND; ALL_DISTINCT_APPEND] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM(ISPEC `n:num` TAKE_DROP)] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALOOKUP_NONE]) THEN
  ASM_REWRITE_TAC[ALOOKUP_APPEND] THEN CASE_REWRITE_TAC[]);;

let size_of_sh_with_ctxt_drop = prove
 (`!sh_ctxt sh. is_wf_shape (DROP n sh_ctxt) sh /\ ALL_DISTINCT (MAP FST sh_ctxt) ==>
     size_of_sh_with_ctxt (DROP n sh_ctxt) sh = size_of_sh_with_ctxt sh_ctxt sh`,
  REC_IND_TAC (cake_ind "size_of_sh_with_ctxt") THEN
  SIMP[size_of_sh_with_ctxt_def; is_wf_shape_def] THEN
  SIMP[CONGR MAP_CONG; EVERY_MEM] THEN SIMP[ETA_AX] THEN
  RW[] THEN EVERY_CASE_TAC THEN FS[] THEN
  IMP_RES_TAC alookup_drop_helper THEN FS[]);;

let is_wf_shape_drop = prove
 (`!(sh_ctxt:(mlstring#A)list) sh n. is_wf_shape (DROP n sh_ctxt) sh ==>
     is_wf_shape sh_ctxt sh`,
  REC_IND_TAC (cake_ind "is_wf_shape") THEN
  SIMP[is_wf_shape_def; EVERY_MEM] THEN RW[] THENL
   [ASM_MESON_TAC[];
    EVERY_CASE_TAC THEN FS[] THEN
    MP_TAC(ISPECL [`TAKE n (ctxt:(mlstring#A)list)`; `DROP n (ctxt:(mlstring#A)list)`;
                   `nm:mlstring`] ALOOKUP_APPEND) THEN
    ASM_REWRITE_TAC[TAKE_DROP] THEN CASE_REWRITE_TAC[] THEN
    TOP_CASE_TAC THEN SIMP[]]);;

(* size_of_sh_with_ctxt_drop with n = 1 (HOL4: its SPEC x :: xs, n = 1) *)
let PPASS1AUX_size_of_sh_with_ctxt_cons = prove
 (`!x xs sh. is_wf_shape (xs:(mlstring#struct_info)list) sh /\
             ALL_DISTINCT (MAP FST (CONS x xs)) ==>
             size_of_sh_with_ctxt (CONS x xs) sh = size_of_sh_with_ctxt xs sh`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`CONS (x:mlstring#struct_info) xs`; `sh:shape`]
           (INST [`1`,`n:num`] size_of_sh_with_ctxt_drop)) THEN
  ASM_REWRITE_TAC[DROP_DEF; DROP; ARITH] THEN MESON_TAC[]);;

let struct_infos_ok_cons = prove
 (`struct_infos_ok xs /\
   ALL_DISTINCT (MAP FST (struct_info_fields info)) /\
   ~MEM nm (MAP FST xs) /\
   ALL (is_wf_shape xs) (MAP SND (struct_info_fields info)) /\
   struct_info_size info =
   size_of_sh_with_ctxt xs (Comb (MAP SND (struct_info_fields info)))
   ==> struct_infos_ok (CONS (nm,info) xs)`,
  REWRITE_TAC[struct_infos_ok_def; ALL; MAP; ALL_DISTINCT; LENGTH] THEN
  CASE_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
    REWRITE_TAC[EL; HD; TL; LT_SUC; ADD_CLAUSES; DROP; DROP_DEF; ARITH;
                NOT_SUC; SUC_SUB1; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC PPASS1AUX_size_of_sh_with_ctxt_cons THEN
    ASM_REWRITE_TAC[is_wf_shape_def; MAP; ALL_DISTINCT];
    SUBGOAL_THEN
     `!nm' info'. MEM (nm',info') xs ==>
                  ALL (is_wf_shape xs) (MAP SND (struct_info_fields info'))`
    ASSUME_TAC THENL
     [REWRITE_TAC[MEM_EXISTS_EL] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `nm':mlstring`; `info':struct_info`]) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_ALL THEN MESON_TAC[is_wf_shape_drop];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(CASE_REWRITE_RULE[EVERY_MEM; FORALL_PAIR_THM]) THEN
    REWRITE_TAC[EVERY_MEM; FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`nm':mlstring`; `info':struct_info`] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `size_of_sh_with_ctxt (CONS (nm,info) xs)
        (Comb (MAP SND (struct_info_fields info'))) =
      size_of_sh_with_ctxt xs (Comb (MAP SND (struct_info_fields info')))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC PPASS1AUX_size_of_sh_with_ctxt_cons THEN
      ASM_REWRITE_TAC[is_wf_shape_def; MAP; ALL_DISTINCT; EVERY_MEM] THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]]]);;

let struct_infos_ok_drop = prove
 (`struct_infos_ok sh_ctxt ==> struct_infos_ok (DROP n sh_ctxt)`,
  REWRITE_TAC[struct_infos_ok_def] THEN STRIP_TAC THEN
  (* the elements of DROP n l are those of l from index n on *)
  SUBGOAL_THEN
   `!i. i < LENGTH (DROP n (sh_ctxt:(mlstring#struct_info)list)) ==>
        i + n < LENGTH sh_ctxt /\ EL i (DROP n sh_ctxt) = EL (i + n) sh_ctxt`
  ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_DROP] THEN REPEAT STRIP_TAC THENL
     [ASM_ARITH_TAC; MATCH_MP_TAC EL_DROP THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i nm info. i < LENGTH (DROP n (sh_ctxt:(mlstring#struct_info)list)) /\
                EL i (DROP n sh_ctxt) = (nm,info) ==>
      ALL (is_wf_shape (DROP (i + 1) (DROP n sh_ctxt)))
          (MAP SND (struct_info_fields info))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[DROP_DROP_T; ARITH_RULE `(i + 1) + n = (i + n) + 1`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `nm:mlstring` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[EVERY_DROP; MAP_DROP; ALL_DISTINCT_DROP] THEN
  ONCE_REWRITE_TAC[EVERY_EL] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  PAIR_CASES_ON `EL i (DROP n (sh_ctxt:(mlstring#struct_info)list))` THEN
  CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `size_of_sh_with_ctxt (DROP n (sh_ctxt:(mlstring#struct_info)list))
      (Comb (MAP SND (struct_info_fields p1))) =
    size_of_sh_with_ctxt sh_ctxt (Comb (MAP SND (struct_info_fields p1)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC size_of_sh_with_ctxt_drop THEN
    ASM_REWRITE_TAC[is_wf_shape_def] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `p0:mlstring`; `p1:struct_info`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_ALL THEN MESON_TAC[is_wf_shape_drop];
    ALL_TAC] THEN
  UNDISCH_TAC (CASE_TERM
   `ALL (\p. match p with
               (nm,info) ->
                 struct_info_size info =
                 size_of_sh_with_ctxt sh_ctxt (Comb (MAP SND (struct_info_fields info))))
        (sh_ctxt:(mlstring#struct_info)list)`) THEN
  REWRITE_TAC[EVERY_EL] THEN
  DISCH_THEN(MP_TAC o SPEC `i + n:num`) THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `EL (i + n) (sh_ctxt:(mlstring#struct_info)list) = (p0,p1)`
    SUBST1_TAC THENL [ASM_MESON_TAC[]; CASE_REWRITE_TAC[]]);;

let struct_infos_ok_append = prove
 (`struct_infos_ok (APPEND xs ys) ==> struct_infos_ok ys`,
  DISCH_THEN(MP_TAC o INST [`LENGTH (xs:(mlstring#struct_info)list)`,`n:num`] o
             MATCH_MP struct_infos_ok_drop) THEN
  REWRITE_TAC[DROP_LENGTH_APPEND]);;

let compile_exp_correct_mmap_helper = prove
 (`!es vs. OPT_MMAP (pan_eval s) es = SOME vs /\
     (!e. MEM e es ==>
          !v. pan_eval s e = SOME v ==>
              pan_eval (convert_s ctxt (s:(A,FFI)pan_state)) (pan_structs_compile_exp ctxt e) =
              SOME (convert_v v)) ==>
     OPT_MMAP (pan_eval (convert_s ctxt s)) (pan_structs_compile_exps ctxt es) =
     SOME (MAP convert_v vs)`,
  LIST_INDUCT_TAC THEN SIMP[pan_structs_compile_exp_def; OPT_MMAP_def; MEM; MAP] THEN
  REWRITE_TAC[DISJ_IMP_THM; FORALL_AND_THM] THEN RW[] THEN
  FS[OPTION_BIND_EQUALS_OPTION] THEN RVEQ_TAC THEN RES_TAC THEN
  ASM_REWRITE_TAC[OPTION_BIND_def; MAP]);;

let fields_in_order_reorder_noop = prove
 (CASE_TERM
  `!(eflds:(mlstring#(A)panLang_exp)list) (info_fields:(mlstring#B)list).
     MAP FST info_fields = MAP FST eflds /\ ALL_DISTINCT (MAP FST info_fields) ==>
     FLAT (MAP (\p. match p with
                      (nm',sh) -> (match ALOOKUP (compile_fields ctxt eflds) nm' with
                                     NONE -> []
                                   | SOME e -> [e])) info_fields) =
     MAP (pan_structs_compile_exp ctxt o SND) eflds`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `info_fields:(mlstring#B)list` list_CASES) THEN
  REWRITE_TAC[MAP; FLAT; NOT_CONS_NIL; CONS_11; ALL_DISTINCT] THEN
  PAIR_CASES_ON `h:mlstring#(A)panLang_exp` THEN PAIR_CASES_ON `h':mlstring#B` THEN
  REWRITE_TAC[pan_structs_compile_exp_def; ALOOKUP_THM; o_THM] THEN
  CASE_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[APPEND; CONS_11] THEN CASE_REWRITE_TAC[APPEND; CONS_11] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t':(mlstring#B)list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MAP_CONG THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CASE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[MEM_MAP; FST]);;

let alookup_map_structs_ok = prove
 (`ALOOKUP s_ctxt nm = SOME info /\ struct_infos_ok s_ctxt ==>
   ALL_DISTINCT (MAP FST (struct_info_fields info))`,
  RW[] THEN IMP_RES_TAC ALOOKUP_MEM THEN
  FS[struct_infos_ok_def; EVERY_MEM] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `nm:mlstring,info:struct_info`)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN SIMP_TAC[]);;

let opt_mmap_eq_every = prove
 (`OPT_MMAP (f:A->B option) xs = SOME ys /\
   (!x y. MEM x xs /\ f x = SOME y ==> P y) ==>
   ALL P ys`,
  RW[EVERY_EL] THEN IMP_RES_TAC opt_mmap_length_eq THEN
  IMP_RES_TAC opt_mmap_el THEN ASM_MESON_TAC[EL_MEM]);;

let every_convert_v_eq = prove
 (CASE_TERM
  `ALL (\w. match w with pan_Val _ -> T | _ -> F) vs ==>
   MAP convert_v vs = (vs:((A)pan_v)list)`,
  RW[EVERY_EL; LIST_EQ_REWRITE; LENGTH_MAP] THEN RES_TAC THEN
  ASM_SIMP_TAC[EL_MAP] THEN
  POP_ASSUM MP_TAC THEN QCASES_ON "EL x (vs:((A)pan_v)list)" THEN
  CASE_REWRITE_TAC[convert_v_def]);;

let map_fst_eq_alookup = prove
 (`!(xs:(A#B)list) (ys:(A#C)list). MAP FST xs = MAP FST ys /\ ALOOKUP xs nm = SOME v ==>
     ?i. afindi nm xs = SOME i /\ afindi nm ys = SOME i /\
         i < LENGTH xs /\ i < LENGTH ys /\
         v = SND (EL i xs) /\ ALOOKUP ys nm = SOME (SND (EL i ys))`,
  QINDUCT_ON "ys" THENL
   [REWRITE_TAC[MAP; MAP_EQ_NIL] THEN MESON_TAC[ALOOKUP_THM; option_DISTINCT];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `xs:(A#B)list` list_CASES) THEN
  REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11] THEN
  PAIR_CASES_ON `h:A#B` THEN PAIR_CASES_ON `a0:A#C` THEN
  REWRITE_TAC[FST; SND; ALOOKUP_THM; afindi_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `h0:A = a00`)) THEN
  ASM_CASES_TAC `h0:A = nm` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN
    EXISTS_TAC `0` THEN ASM_REWRITE_TAC[EL; HD; LENGTH; LT_0];
    ALL_TAC] THEN
  ASSUME_TAC(ONCE_REWRITE_RULE[EQ_SYM_EQ] (ASSUME `~(h0:A = nm)`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o lhs o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:(A#B)list`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN EXISTS_TAC `1 + i` THEN
  ASM_REWRITE_TAC[LENGTH; ARITH_RULE `1 + i < SUC n <=> i < n`;
                  ARITH_RULE `1 + i = SUC i`; EL; TL; LT_SUC] THEN
  CASE_REWRITE_TAC[]);;

let is_wf_shape_compile_shape = prove
 (`(!(sh_ctxt:(stcname#((fldname#shape)list))list) sh.
      is_wf_shape (str_ctxt:(mlstring#A)list) (compile_shape sh_ctxt sh)) /\
   (!(sh_ctxt:(stcname#((fldname#shape)list))list) shs.
      ALL (is_wf_shape (str_ctxt:(mlstring#A)list)) (compile_shapes sh_ctxt shs))`,
  MATCH_MP_TAC compile_shape_ind THEN
  SIMP[compile_shape_def; is_wf_shape_def; ETA_AX] THEN
  RW[] THEN EVERY_CASE_TAC THEN SIMP[is_wf_shape_def; ETA_AX]);;

let compile_shapes_eq_map = prove
 (`!shs. compile_shapes (sctxt:(mlstring#(B#shape)list)list) shs =
         MAP (compile_shape sctxt) shs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[compile_shape_def; MAP]);;

(* termination of compile_shape_n (HOL4: rw [] >> CCONTR_TAC >> fs              *)
(* [DROP_LENGTH_TOO_LONG, afindi_def]): afindi k (DROP n l) = SOME j gives      *)
(* n < LENGTH l                                                                 *)

let PPASS1AUX_afindi_DROP_LT = prove
 (`!k n (l:(A#B)list) j. afindi k (DROP n l) = SOME j ==> n < LENGTH l`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[DROP_LENGTH_TOO_LONG; afindi_def; option_DISTINCT]);;

let PPASS1AUX_SHAPE_N_TC_TAC : tactic =
  REPEAT BOSS_STRIP_TAC THEN
  (fun (asl,w as g) ->
     MAP_EVERY ASSUME_TAC
       (mapfilter (fun (_,th) -> MATCH_MP PPASS1AUX_afindi_DROP_LT th) asl) g) THEN
  REWRITE_TAC(I_THM :: WF_REL_THMS) THEN TERM_TAC;;

let compile_shape_n_def = cake_def_wf
  `inv_image (MEASURE I LEX MEASURE shape_size)
     (\x:(stcname#((B#shape)list))list#num#shape.
        (LENGTH (FST x) - FST (SND x),SND (SND x)))`
  PPASS1AUX_SHAPE_N_TC_TAC
  `(compile_shape_n (sctxt:(stcname#((B#shape)list))list) n One = One) /\
   (compile_shape_n sctxt n (Comb shs) = Comb (MAP (compile_shape_n sctxt n) shs)) /\
   (compile_shape_n sctxt n (Named nm) =
      match afindi nm (DROP n sctxt) with
        NONE -> One
      | SOME j ->
          let (nm',flds) = EL (n + j) sctxt in
          Comb (MAP (compile_shape_n sctxt ((n + j) + 1)) (MAP SND flds)))`;;

let compile_shape_n_ind = cake_ind "compile_shape_n";;

let dropWhile_afindi = prove
 (CASE_TERM
  `dropWhile (\p. match p with (k,v) -> ~(k = kx)) (xs:(A#B)list) =
   (match afindi kx xs with NONE -> [] | SOME n -> DROP n xs)`,
  (SPEC_TAC(`xs:(A#B)list`,`xs:(A#B)list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[dropWhile_def; afindi_def] THEN CASE_REWRITE_TAC[]) THEN
  (PAIR_CASES_ON `h:A#B` THEN CASE_REWRITE_TAC[afindi_def]) THEN
  (REWRITE_TAC[ISPECL [`kx:A`; `h0:A`] EQ_SYM_EQ] THEN
   ASM_CASES_TAC `(h0:A) = kx` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[DROP] THEN
   TOP_CASE_TAC THEN CASE_REWRITE_TAC[ARITH_RULE `1 + n = SUC n`; DROP]));;

let afindi_less_length = prove
 (`!(xs:(A#B)list) n. afindi kx xs = SOME n ==> n < LENGTH xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[afindi_def; option_DISTINCT] THEN
  PAIR_CASES_ON `h:A#B` THEN REWRITE_TAC[afindi_def; LENGTH] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
   [ARITH_TAC; ALL_TAC] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:num`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let afindi_MAP_eq = prove
 (`!xs:(A#B)list. (!x y. MEM (x,y) xs ==> FST ((f:A#B->A#C) (x,y)) = x) ==>
       afindi kx (MAP f xs) = afindi kx xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[afindi_def; MAP] THEN
  PAIR_CASES_ON `h:A#B` THEN
  PAIR_CASES_ON `(f:A#B->A#C) (h0,h1)` THEN
  ASM_REWRITE_TAC[afindi_def; MEM; PAIR_EQ] THEN DISCH_TAC THEN
  SUBGOAL_THEN `p0:A = h0` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`h0:A`; `h1:B`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_imp(concl th) then MP_TAC th else NO_TAC) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC[]);;

let compile_shape_n_eq = prove
 (`!(sctxt:(stcname#((B#shape)list))list) n sh.
     compile_shape_n sctxt n sh = compile_shape (DROP n sctxt) sh`,
  (MATCH_MP_TAC compile_shape_n_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[compile_shape_n_def; compile_shape_def] THEN DISCH_TAC THENL
   [REWRITE_TAC[compile_shapes_eq_map; injectivity "shape"] THEN
    MATCH_MP_TAC MAP_CONG THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (REWRITE_TAC[dropWhile_afindi] THEN TOP_CASE_TAC THEN CASE_REWRITE_TAC[]) THEN
  (SUBGOAL_THEN `n + a < LENGTH (sctxt:(stcname#((B#shape)list))list)` ASSUME_TAC THENL
    [IMP_RES_TAC afindi_less_length THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_DROP]) THEN
     ASM_ARITH_TAC;
     ALL_TAC] THEN
   REWRITE_TAC[DROP_DROP_T] THEN
   SUBGOAL_THEN `a + n = n + a:num` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
   MP_TAC(ISPECL [`sctxt:(stcname#((B#shape)list))list`; `n + a:num`] DROP_EL_CONS) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   PAIR_CASES_ON `EL (n + a) (sctxt:(stcname#((B#shape)list))list)` THEN
   CASE_REWRITE_TAC[compile_shapes_eq_map; injectivity "shape"] THEN
   MATCH_MP_TAC MAP_CONG THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]));;

(* HOL4: Q.SPECL [sctxt, 0] compile_shape_n_eq |> SIMP_RULE list_ss [] |> GSYM *)
let compile_shape_n_eq_rev = prove
 (`!sh. compile_shape (sctxt:(stcname#((B#shape)list))list) sh =
        compile_shape_n sctxt 0 sh`,
  REWRITE_TAC[compile_shape_n_eq; DROP]);;

(* the clauses of mem_loads and mem_load_flds (HOL4: cj 2, cj 3 .. of mem_load_def) *)
let PPASS1AUX_mem_loads_clauses = end_itlist CONJ (tl (CONJUNCTS pan_mem_load_def));;

let mem_load_flds_eq = prove
 (`!fld_shs vflds (x:A word).
     mem_load_flds fld_shs x madd memry stcs = SOME vflds ==>
     ?vs. mem_loads (MAP SND fld_shs) x madd memry stcs = SOME vs /\
          LENGTH vs = LENGTH fld_shs /\ vflds = ZIP (MAP FST fld_shs) vs`,
  (LIST_INDUCT_TAC THENL
   [SIMP[PPASS1AUX_mem_loads_clauses; MAP; LENGTH; ZIP] THEN MESON_TAC[LENGTH_EQ_NIL];
    ALL_TAC]) THEN
  (PAIR_CASES_ON `h:mlstring#shape` THEN
  REWRITE_TAC[PPASS1AUX_mem_loads_clauses; MAP] THEN REPEAT GEN_TAC THEN
  GVS(all_case_eqs()) THEN STRIP_TAC THEN RVEQ_TAC) THEN
  (FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
   DISCH_THEN(fun ih -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ih)) THEN
   EXISTS_TAC `CONS (a:(A)pan_v) vs` THEN
   ASM_REWRITE_TAC[LENGTH; ZIP; HD; TL; CONS_11] THEN MESON_TAC[]));;

let ALOOKUP_eq_afindi = prove
 (`ALOOKUP (xs:(A#B)list) nm = OPTION_MAP (\i. SND (EL i xs)) (afindi nm xs)`,
  SPEC_TAC(`xs:(A#B)list`,`xs:(A#B)list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALOOKUP_THM; afindi_def; OPTION_MAP_DEF] THEN
  PAIR_CASES_ON `h:A#B` THEN REWRITE_TAC[ALOOKUP_THM; afindi_def] THEN
  REWRITE_TAC[ISPECL [`h0:A`; `nm:A`] EQ_SYM_EQ] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; EL; HD; SND] THEN
  TOP_CASE_TAC THEN
  REWRITE_TAC[OPTION_MAP_DEF; ARITH_RULE `1 + i = SUC i`; EL; TL]);;

let afindi_append = prove
 (CASE_TERM
  `!k (xs:(A#B)list) ys. afindi k (APPEND xs ys) =
     (match afindi k xs with
        NONE -> OPTION_MAP ((+) (LENGTH xs)) (afindi k ys)
      | SOME i -> SOME i)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; afindi_def; LENGTH; ADD_CLAUSES] THEN CASE_REWRITE_TAC[] THENL
   [GEN_TAC THEN QCASES_ON "afindi (k:A) (ys:(A#B)list)" THEN
    REWRITE_TAC[OPTION_MAP_DEF; ADD_CLAUSES];
    PAIR_CASES_ON `h:A#B` THEN REWRITE_TAC[afindi_def] THEN GEN_TAC THEN
    COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    QCASES_ON "afindi (k:A) (t:(A#B)list)" THEN CASE_REWRITE_TAC[] THEN
    QCASES_ON "afindi (k:A) (ys:(A#B)list)" THEN CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
    REWRITE_TAC[option_INJ] THEN ARITH_TAC]);;

let afindi_EL = prove
 (`!(xs:(A#B)list) i. afindi k xs = SOME i ==> FST (EL i xs) = k`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[afindi_def; option_DISTINCT] THEN
  PAIR_CASES_ON `h:A#B` THEN REWRITE_TAC[afindi_def] THEN GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[EL; HD];
    ALL_TAC] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ARITH_RULE `1 + a = SUC a`; EL; TL] THEN ASM_MESON_TAC[]);;

let wf_shape_struct_infos_ok_helper = prove
 (`ALOOKUP (DROP n ctxt) nm = SOME info /\ struct_infos_ok ctxt ==>
   ?i. afindi nm (DROP n ctxt) = SOME i /\
       i + n < LENGTH ctxt /\
       EL (i + n) ctxt = (nm,info) /\
       afindi nm ctxt = SOME (i + n) /\
       (!sh. MEM sh (MAP SND (struct_info_fields info)) ==>
             is_wf_shape (DROP ((i + n) + 1) ctxt) sh)`,
  (REWRITE_TAC[ALOOKUP_eq_afindi] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (is_comb o lhs o concl)) THEN
   QCASES_ON "afindi (nm:mlstring) (DROP n (ctxt:(mlstring#struct_info)list))" THEN
   REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN DISCH_TAC THEN
   EXISTS_TAC `a:num` THEN REWRITE_TAC[] THEN
   IMP_RES_TAC afindi_less_length THEN IMP_RES_TAC afindi_EL THEN
   RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_DROP])) THEN
  (SUBGOAL_THEN `a + n < LENGTH (ctxt:(mlstring#struct_info)list)` ASSUME_TAC THENL
    [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]) THEN
  (SUBGOAL_THEN `EL (a + n) ctxt = (nm:mlstring,info:struct_info)` ASSUME_TAC THENL
    [MP_TAC(ISPECL [`a:num`; `n:num`; `ctxt:(mlstring#struct_info)list`] EL_DROP) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
     ONCE_REWRITE_TAC[PAIR_FST_SND_EQ] THEN ASM_REWRITE_TAC[FST; SND];
     ASM_REWRITE_TAC[]] THEN
   UNDISCH_TAC `struct_infos_ok ctxt` THEN REWRITE_TAC[struct_infos_ok_def] THEN
   STRIP_TAC THEN
   CONJ_TAC THENL
    [ALL_TAC;
     FIRST_X_ASSUM(MP_TAC o SPECL [`a + n:num`; `nm:mlstring`; `info:struct_info`]) THEN
     ASM_REWRITE_TAC[EVERY_MEM]]) THEN
  (SUBGOAL_THEN `ALOOKUP (DROP n (ctxt:(mlstring#struct_info)list)) nm = SOME (info:struct_info)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[ALOOKUP_eq_afindi; OPTION_MAP_DEF]; ALL_TAC] THEN
   MP_TAC(MATCH_MP alookup_drop_helper
     (CONJ (ASSUME `ALOOKUP (DROP n (ctxt:(mlstring#struct_info)list)) nm = SOME (info:struct_info)`)
           (ASSUME `ALL_DISTINCT (MAP FST (ctxt:(mlstring#struct_info)list))`))) THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `afindi nm (TAKE n (ctxt:(mlstring#struct_info)list)) = NONE` ASSUME_TAC
   THENL [ASM_MESON_TAC[ALOOKUP_NONE; ALOOKUP_eq_afindi; OPTION_MAP_EQ_NONE]; ALL_TAC] THEN
   MP_TAC(ISPECL [`nm:mlstring`; `TAKE n (ctxt:(mlstring#struct_info)list)`;
                  `DROP n (ctxt:(mlstring#struct_info)list)`] afindi_append) THEN
   ASM_REWRITE_TAC[TAKE_DROP] THEN CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
   DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_INJ] THEN
   SUBGOAL_THEN `LENGTH (TAKE n (ctxt:(mlstring#struct_info)list)) = n` SUBST1_TAC THENL
    [MATCH_MP_TAC LENGTH_TAKE THEN ASM_ARITH_TAC; ARITH_TAC]));;

let size_of_compile_shape_n = prove
 (CASE_TERM
  `!(sh_ctxt:(stcname#((fldname#shape)list))list) n sh.
     sh_ctxt = MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info)) ctxt /\
     is_wf_shape (DROP n ctxt) sh /\
     struct_infos_ok ctxt ==>
     size_of_sh_with_ctxt [] (compile_shape_n sh_ctxt n sh) =
     size_of_sh_with_ctxt ctxt sh`,
  MATCH_MP_TAC compile_shape_n_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[compile_shape_n_def; size_of_sh_with_ctxt_def; is_wf_shape_def] THEN
   REPEAT DISCH_TAC THEN FIRST_X_ASSUM(CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC) THENL
   [REWRITE_TAC[MAP_MAP_o] THEN AP_TERM_TAC THEN MATCH_MP_TAC MAP_CONG THEN
   REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[EVERY_MEM];
    (QCASES_ON "ALOOKUP (DROP n (ctxt:(mlstring#struct_info)list)) nm" THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN ASM_REWRITE_TAC[] THEN
   TRY(FIRST_X_ASSUM CONTR_TAC) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP wf_shape_struct_infos_ok_helper o
     C CONJ (ASSUME `struct_infos_ok (ctxt:(mlstring#struct_info)list)`)) THEN
   DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `i + n = n + i:num` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
   THENL [ARITH_TAC; ALL_TAC]) THEN
    (SUBGOAL_THEN (CASE_TERM
     `afindi nm (DROP n (MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info))
                             (ctxt:(mlstring#struct_info)list))) = SOME i`) ASSUME_TAC THENL
    [REWRITE_TAC[GSYM MAP_DROP] THEN
     SUBST1_TAC(SYM(ASSUME `afindi nm (DROP n (ctxt:(mlstring#struct_info)list)) = SOME i`)) THEN
     MATCH_MP_TAC afindi_MAP_eq THEN CASE_REWRITE_TAC[FST];
     ALL_TAC] THEN
   SUBGOAL_THEN (CASE_TERM
     `EL (n + i) (MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info))
                      (ctxt:(mlstring#struct_info)list)) =
      (nm,struct_info_fields a)`) ASSUME_TAC THENL
    [REWRITE_TAC[MATCH_MP EL_MAP (ASSUME `n + i < LENGTH (ctxt:(mlstring#struct_info)list)`)] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[ALOOKUP_eq_afindi] THEN CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
   ASM_REWRITE_TAC[SND; size_of_sh_with_ctxt_def] THEN
   SUBGOAL_THEN `struct_info_size a =
                 size_of_sh_with_ctxt ctxt (Comb (MAP SND (struct_info_fields a)))`
     SUBST1_TAC THENL
    [UNDISCH_TAC `struct_infos_ok (ctxt:(mlstring#struct_info)list)` THEN
     REWRITE_TAC[struct_infos_ok_def; EVERY_MEM] THEN
     DISCH_THEN(MP_TAC o SPEC `(nm:mlstring,a:struct_info)` o last o CONJUNCTS) THEN
     ANTS_TAC THENL [ASM_MESON_TAC[MEM_EL]; CASE_REWRITE_TAC[]];
     ALL_TAC] THEN
   CASE_REWRITE_TAC[size_of_sh_with_ctxt_def; MAP_MAP_o] THEN AP_TERM_TAC THEN
   MATCH_MP_TAC MAP_CONG THEN REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`nm:mlstring`; `struct_info_fields a`; `i:num`;
                                 `SND (x:mlstring#shape)`]) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
    [REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   ANTS_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[];
     REWRITE_TAC[]])]);;

let size_of_compile_shape = prove
 (CASE_TERM
  `is_wf_shape ctxt sh /\ struct_infos_ok ctxt ==>
   size_of_sh_with_ctxt []
     (compile_shape
        (MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info)) ctxt) sh) =
   size_of_sh_with_ctxt ctxt sh`,
  REWRITE_TAC[compile_shape_n_eq_rev] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC size_of_compile_shape_n THEN ASM_REWRITE_TAC[DROP]);;

let v_flds_ok_append = prove
 (`!ctxt (v:(A)pan_v). v_flds_ok ctxt v /\ ALL_DISTINCT (APPEND (MAP FST pfx) (MAP FST ctxt)) ==>
     v_flds_ok (APPEND pfx ctxt) v`,
  REC_IND_TAC v_flds_ok_ind THEN SIMP[v_flds_ok_def] THEN RW[] THEN
  FS[EVERY_MEM; FORALL_PAIR_THM] THEN
  FIRST
   [ASM_MESON_TAC[];
    QCASES_ON "ALOOKUP (ctxt:(mlstring#struct_info)list) nm" THEN
    RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN ASM_REWRITE_TAC[] THEN
    TRY(FIRST_ASSUM CONTR_TAC) THEN
    SUBGOAL_THEN `ALOOKUP (pfx:(mlstring#struct_info)list) nm = NONE` ASSUME_TAC THENL
     [REWRITE_TAC[ALOOKUP_NONE] THEN
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[ALL_DISTINCT_APPEND] o
        check (fun th -> try fst(dest_const(rator(concl th))) = "ALL_DISTINCT"
                         with Failure _ -> false)) THEN
      IMP_RES_TAC ALOOKUP_MEM THEN REWRITE_TAC[MEM_MAP] THEN
      ASM_MESON_TAC[FST];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[ALOOKUP_APPEND] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]]);;

let dropWhile_MAP_helper = prove
 (`!xs. dropWhile P xs = ys /\ (!x:A. MEM x xs ==> P x = Q ((f:A->B) x)) ==>
        dropWhile Q (MAP f xs) = MAP f ys`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[dropWhile_def; MAP; MEM] THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[MAP]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(Q:B->bool) (f (h:A)) <=> P h` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(P:A->bool) h` THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[MAP]]);;

(* HOL4: UNCURRY (\x. f) = f o SND; HOL4's \(x,y). f y is written     *)
(* \p. match p with (x,y) -> f y here                                   *)
let UNCURRY_EQ_o_SND = prove
 (CASE_TERM `(\p. match p with (x:A,y:B) -> (f:B->C) y) = f o SND`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM] THEN CASE_REWRITE_TAC[SND]);;

(* HOL4: cj 1 mem_load_def |> Q.SPEC stcs and its instances for the three shapes *)
let mem_load_rec1 = CONJUNCT1 pan_mem_load_def;;

let mem_load_rec = end_itlist CONJ
  (map (fun t -> ISPEC t mem_load_rec1) [`One`; `Comb shs`; `Named nm`]);;

let mem_loads_convert_helper = prove
 (`!shs vs (x:A word).
     mem_loads shs x madd memry stcs = SOME vs /\
     (!sh y v. MEM sh shs /\ pan_mem_load sh y madd memry stcs = SOME v ==>
               size_of_sh_with_ctxt stcs2 (f sh) = size_of_sh_with_ctxt stcs sh /\
               pan_mem_load (f sh) y madd memry stcs2 = SOME (convert_v v)) ==>
     mem_loads (MAP f shs) x madd memry stcs2 = SOME (MAP convert_v vs)`,
  (LIST_INDUCT_TAC THEN REWRITE_TAC[PPASS1AUX_mem_loads_clauses; MAP; MEM] THENL
   [MESON_TAC[option_INJ; MAP]; ALL_TAC]) THEN
  (REWRITE_TAC[DISJ_IMP_THM; FORALL_AND_THM] THEN
   REPEAT GEN_TAC THEN GVS(all_case_eqs()) THEN STRIP_TAC THEN RVEQ_TAC) THEN
  (SUBGOAL_THEN `size_of_sh_with_ctxt stcs2 ((f:shape->shape) h) =
                 size_of_sh_with_ctxt stcs h /\
                 pan_mem_load (f h) (x:A word) madd memry stcs2 = SOME (convert_v (a:(A)pan_v))`
     STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`a':((A)pan_v)list`;
     `word_add (x:A word) (word_mul bytes_in_word (word (size_of_sh_with_ctxt stcs h)))`] o
     check (fun th -> is_forall(concl th) && length (fst(strip_forall(concl th))) = 2)) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   DISCH_TAC THEN ASM_REWRITE_TAC[MAP] THEN MESON_TAC[]));;

let mem_loads_EL = prove
 (`!shs vs (x:A word) i.
     mem_loads shs x madd memry stcs = SOME vs /\ i < LENGTH shs ==>
     ?y. pan_mem_load (EL i shs) y madd memry stcs = SOME (EL i vs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[PPASS1AUX_mem_loads_clauses; LENGTH; CONJUNCT1 LT] THEN
  REPEAT GEN_TAC THEN GVS(all_case_eqs()) THEN STRIP_TAC THEN RVEQ_TAC THEN
  QCASES_ON "i:num" THEN REWRITE_TAC[EL; HD; TL; LT_SUC] THEN FS[LE_SUC_LT] THEN
  ASM_MESON_TAC[]);;

let mem_loads_mem = prove
 (`!shs vs (x:A word).
     mem_loads shs x madd memry stcs = SOME vs /\ MEM v vs ==>
     ?sh y. MEM sh shs /\ pan_mem_load sh y madd memry stcs = SOME v`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[PPASS1AUX_mem_loads_clauses; MEM] THEN
  REPEAT GEN_TAC THEN GVS(all_case_eqs()) THEN STRIP_TAC THEN RVEQ_TAC THEN
  FS[MEM] THEN ASM_MESON_TAC[]);;

(* size_of_compile_shape_n with its context equation substituted *)
let PPASS1AUX_size_of_compile_shape_n = prove
 (CASE_TERM
  `!ctxt n sh. is_wf_shape (DROP n ctxt) sh /\ struct_infos_ok ctxt ==>
     size_of_sh_with_ctxt []
       (compile_shape_n
          (MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info)) ctxt) n sh) =
     size_of_sh_with_ctxt ctxt sh`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC size_of_compile_shape_n THEN ASM_REWRITE_TAC[]);;

let mem_load_conversion = prove
 (CASE_TERM
  `!str2 n shape (x:A word) v.
     pan_mem_load shape x madd memry (DROP n str_ctxt) = SOME v /\
     str2 = MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info)) str_ctxt /\
     is_wf_shape (DROP n str_ctxt) shape /\
     struct_infos_ok str_ctxt ==>
     pan_mem_load (compile_shape_n str2 n shape) x madd memry [] = SOME (convert_v v) /\
     v_flds_ok str_ctxt v`,
  REC_IND_TAC compile_shape_n_ind THEN REPEAT CONJ_TAC THENL
   [(* One *)
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[mem_load_rec]) THEN REWRITE_TAC[compile_shape_n_def; mem_load_rec] THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN CASE_REWRITE_TAC[] THEN
   GVS(all_case_eqs()) THEN REWRITE_TAC[convert_v_def; v_flds_ok_def];
    (* Comb *)
    (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[mem_load_rec; is_wf_shape_def]) THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
   REWRITE_TAC[compile_shape_n_def; mem_load_rec] THEN CASE_REWRITE_TAC[] THEN
   GVS(all_case_eqs())) THEN
    (FIRST_ASSUM((fun th -> DEP_REWRITE_TAC[GEN_ALL(MATCH_MP
     (REWRITE_RULE[IMP_CONJ] (GEN_ALL mem_loads_convert_helper)) th)]) o
     check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "mem_loads"
                      with Failure _ -> false))) THEN
    (FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[struct_infos_ok_def] o
     check (fun th -> try fst(dest_const(rator(concl th))) = "struct_infos_ok"
                      with Failure _ -> false)) THEN
   REPEAT CONJ_TAC THENL
    [REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
     SUBGOAL_THEN `is_wf_shape (DROP n (str_ctxt:(mlstring#struct_info)list)) sh`
       ASSUME_TAC THENL [ASM_MESON_TAC[EVERY_MEM]; ALL_TAC] THEN
     ASM_SIMP_TAC[PPASS1AUX_size_of_compile_shape_n; size_of_sh_with_ctxt_drop] THEN
     ASM_MESON_TAC[];
     REWRITE_TAC[option_INJ; convert_v_def] THEN MESON_TAC[];
     REWRITE_TAC[v_flds_ok_def; EVERY_MEM] THEN X_GEN_TAC `w:(A)pan_v` THEN DISCH_TAC THEN
     FIRST_ASSUM((fun th -> MP_TAC(MATCH_MP mem_loads_mem
         (CONJ th (ASSUME `MEM (w:(A)pan_v) a`)))) o
       check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "mem_loads"
                        with Failure _ -> false)) THEN
     STRIP_TAC THEN ASM_MESON_TAC[EVERY_MEM]]);
    (* Named *)
    (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
   UNDISCH_TAC `pan_mem_load (Named nm) (x:A word) madd memry (DROP n str_ctxt) = SOME v` THEN
   RULE_ASSUM_TAC(REWRITE_RULE[is_wf_shape_def]) THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
   QCASES_ON "ALOOKUP (DROP n (str_ctxt:(mlstring#struct_info)list)) nm" THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP wf_shape_struct_infos_ok_helper o C CONJ
     (ASSUME `struct_infos_ok (str_ctxt:(mlstring#struct_info)list)`)) THEN
   DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `i + n = n + i:num` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[mem_load_rec; dropWhile_afindi] THEN CASE_REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[DROP_DROP_T] THEN CASE_REWRITE_TAC[] THEN
   SUBGOAL_THEN `i + n = n + i:num` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
   MP_TAC(ISPECL [`str_ctxt:(mlstring#struct_info)list`; `n + i:num`] DROP_EL_CONS) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]) THEN
    (QCASES_ON "mem_load_flds (struct_info_fields a) (x:A word) madd memry
                (DROP ((n + i) + 1) (str_ctxt:(mlstring#struct_info)list))" THEN
   CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
   SUBGOAL_THEN (CASE_TERM
     `afindi nm (DROP n (MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info))
                             (str_ctxt:(mlstring#struct_info)list))) = SOME i`) ASSUME_TAC THENL
    [REWRITE_TAC[GSYM MAP_DROP] THEN
     SUBST1_TAC(SYM(ASSUME `afindi nm (DROP n (str_ctxt:(mlstring#struct_info)list)) = SOME i`)) THEN
     MATCH_MP_TAC afindi_MAP_eq THEN CASE_REWRITE_TAC[FST];
     ALL_TAC] THEN
   SUBGOAL_THEN (CASE_TERM
     `EL (n + i) (MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info))
                      (str_ctxt:(mlstring#struct_info)list)) =
      (nm,struct_info_fields a)`) ASSUME_TAC THENL
    [REWRITE_TAC[MATCH_MP EL_MAP (ASSUME `n + i < LENGTH (str_ctxt:(mlstring#struct_info)list)`)] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[compile_shape_n_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[mem_load_rec] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP mem_load_flds_eq) THEN RVEQ_TAC) THEN
    (ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[mem_load_rec]) THEN
    (FIRST_ASSUM((fun th -> DEP_REWRITE_TAC[GEN_ALL(MATCH_MP
     (REWRITE_RULE[IMP_CONJ] (GEN_ALL mem_loads_convert_helper)) th)]) o
     check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "mem_loads"
                      with Failure _ -> false)) THEN
   CASE_REWRITE_TAC[] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[struct_infos_ok_def] o
     check (fun th -> try fst(dest_const(rator(concl th))) = "struct_infos_ok"
                      with Failure _ -> false))) THEN
    (REPEAT CONJ_TAC THENL
    [REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
     SUBGOAL_THEN `is_wf_shape (DROP ((n + i) + 1) (str_ctxt:(mlstring#struct_info)list)) sh`
       ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     CONJ_TAC THENL
      [ASM_SIMP_TAC[PPASS1AUX_size_of_compile_shape_n; size_of_sh_with_ctxt_drop];
       FIRST_X_ASSUM(MP_TAC o SPECL [`nm:mlstring`; `struct_info_fields a`; `i:num`; `sh:shape`] o
         check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 4)) THEN
       ASM_REWRITE_TAC[] THEN
       DISCH_THEN(MP_TAC o SPECL [`y:A word`; `v:(A)pan_v`]) THEN ASM_SIMP_TAC[]];
     REWRITE_TAC[convert_v_def; LET_DEF; LET_END_DEF; UNCURRY_EQ_o_SND] THEN
     REWRITE_TAC[injectivity "pan_v"; MAP_o] THEN
     ASM_SIMP_TAC[MAP_SND_ZIP; LENGTH_MAP];
     ALL_TAC]) THEN
    (REWRITE_TAC[v_flds_ok_def; UNCURRY_EQ_o_SND; GSYM ALL_MAP] THEN
   ASM_SIMP_TAC[MAP_SND_ZIP; MAP_FST_ZIP; LENGTH_MAP] THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP alookup_drop_helper o C CONJ
     (ASSUME `ALL_DISTINCT (MAP FST (str_ctxt:(mlstring#struct_info)list))`) o
     check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "ALOOKUP"
                      with Failure _ -> false)) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[MAP_o] THEN ASM_SIMP_TAC[MAP_SND_ZIP; LENGTH_MAP] THEN
   CONJ_TAC THENL
    [REWRITE_TAC[EVERY_MEM] THEN X_GEN_TAC `w:(A)pan_v` THEN DISCH_TAC THEN
     FIRST_ASSUM((fun th -> MP_TAC(MATCH_MP mem_loads_mem
         (CONJ th (ASSUME `MEM (w:(A)pan_v) vs`)))) o
       check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "mem_loads"
                        with Failure _ -> false)) THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`nm:mlstring`; `struct_info_fields a`; `i:num`; `sh:shape`] o
       check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 4)) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`y:A word`; `w:(A)pan_v`]) THEN
     ASM_SIMP_TAC[];
     MATCH_MP_TAC(CONJUNCT1(CONJUNCT2 mem_loads_some_shape_eq)) THEN
     ASM_MESON_TAC[]])]);;

(* HOL4: mem_load_conversion |> SIMP_RULE bool_ss [] |> Q.SPEC 0 |>         *)
(* SIMP_RULE list_ss [compile_shape_n_eq]                                   *)
let mem_load_conversion_inst = prove
 (CASE_TERM
  `!shape (x:A word) v.
     pan_mem_load shape x madd memry str_ctxt = SOME v /\
     is_wf_shape str_ctxt shape /\
     struct_infos_ok str_ctxt ==>
     pan_mem_load
       (compile_shape
          (MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info)) str_ctxt) shape)
       x madd memry [] = SOME (convert_v v) /\
     v_flds_ok str_ctxt v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[compile_shape_n_eq_rev] THEN
  MATCH_MP_TAC mem_load_conversion THEN ASM_REWRITE_TAC[DROP]);;

let old_exp_shapes_eq = prove
 (`old_exp_shapes ctxt es = MAP (old_exp_shape ctxt) (es:((A)panLang_exp)list)`,
  SPEC_TAC(`es:((A)panLang_exp)list`,`es:((A)panLang_exp)list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[old_exp_shape_def; MAP]);;

(* HOL4's ALOOKUP_MAP_2 for the context of struct fields *)
let PPASS1AUX_ALOOKUP_MAP_fields = prove
 (CASE_TERM
  `!l k. ALOOKUP (MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info)) l) k =
         OPTION_MAP struct_info_fields (ALOOKUP (l:(mlstring#struct_info)list) k)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALOOKUP_THM; OPTION_MAP_DEF] THEN
  PAIR_CASES_ON `h:mlstring#struct_info` THEN CASE_REWRITE_TAC[ALOOKUP_THM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF]);;

(* word_lab has one constructor: (case a of Word w => T) = T, so the pattern *)
(* Val (Word _) of eval's checks is HOL4's Val _ of every_convert_v_eq       *)
let PPASS1AUX_word_lab_case_T = prove
 (CASE_TERM `!a:(A)word_lab. (match a with Word w -> T) = T`,
  GEN_TAC THEN QCASES_ON "a:(A)word_lab" THEN CASE_REWRITE_TAC[]);;

(* compile_exp_correct: tactics for the cases of the induction on eval *)

let PPASS1AUX_EXP_GEN_TAC : tactic =
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  GVS([pan_eval_def; pan_structs_compile_exp_def; convert_v_def; v_flds_ok_def;
       convert_s_def; FLOOKUP_FMAP_MAP2; old_exp_shape_def; shape_of_def] @ all_case_eqs()) THEN
  SIMP[compile_exp_correct_mmap_helper; EL_MAP] THEN
  REWRITE_TAC[GSYM(CONJUNCT1 ALOOKUP_EQ_FLOOKUP)] THEN ASM_REWRITE_TAC[FLOOKUP_FMAP_MAP2] THEN
  CASE_REWRITE_TAC[o_THM; SND; OPTION_MAP_DEF] THEN
  IMP_RES_TAC FEVERY_FLOOKUP THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  FS[] THEN TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let PPASS1AUX_EXP_RSTRUCT0_TAC : tactic = REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  GVS([pan_eval_def; pan_structs_compile_exp_def; convert_v_def; v_flds_ok_def;
       old_exp_shape_def; shape_of_def] @ all_case_eqs());;

let PPASS1AUX_EXP_RSTRUCT_TAC : tactic = PPASS1AUX_EXP_RSTRUCT0_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[old_exp_shapes_eq; LIST_EQ_REWRITE; LENGTH_MAP] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[opt_mmap_eq_some_el] o
      check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "OPT_MMAP"
                       with Failure _ -> false)) THEN
    ASM_SIMP_TAC[EL_MAP] THEN ASM_MESON_TAC[EL_MEM];
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] opt_mmap_eq_every) o
      check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "OPT_MMAP"
                       with Failure _ -> false)) THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC compile_exp_correct_mmap_helper THEN ASM_MESON_TAC[]];;

let PPASS1AUX_EXP_RFIELD_TAC : tactic = REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  GVS([pan_eval_def; pan_structs_compile_exp_def; old_exp_shape_def; shape_of_def;
       LLOOKUP_THM] @ all_case_eqs()) THEN
  FS[EVERY_EL; convert_v_def; EL_MAP; v_flds_ok_def; LENGTH_MAP];;

let PPASS1AUX_EXP_NFIELD_TAC : tactic = REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  GVS([pan_eval_def; pan_structs_compile_exp_def] @ all_case_eqs()) THEN
  REWRITE_TAC[convert_v_def; shape_of_def; old_exp_shape_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[shape_of_def; PPASS1AUX_ALOOKUP_MAP_fields] THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_flds_ok_def]) THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  QCASES_ON "ALOOKUP (pan_state_structs (s:(A,FFI)pan_state)) a0" THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  MP_TAC(INST [`fld:mlstring`,`nm:mlstring`]
           (ISPECL [`a1:(mlstring#(A)pan_v)list`; `struct_info_fields a'`] map_fst_eq_alookup)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `MAP (shape_of o SND) (a1:(mlstring#(A)pan_v)list) =
                 MAP SND (struct_info_fields a')` THEN
    DISCH_THEN(MP_TAC o AP_TERM `EL i:shape list->shape`) THEN
    ASM_SIMP_TAC[EL_MAP; o_THM] THEN MESON_TAC[];
    UNDISCH_TAC (CASE_TERM `ALL (\p. match p with (nm,v) -> v_flds_ok (pan_state_structs (s:(A,FFI)pan_state)) v)
                     (a1:(mlstring#(A)pan_v)list)`) THEN
    REWRITE_TAC[EVERY_EL] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    PAIR_CASES_ON `EL i (a1:(mlstring#(A)pan_v)list)` THEN CASE_REWRITE_TAC[SND];
    SIMP[LENGTH_MAP] THEN ASM_SIMP_TAC[EL_MAP] THEN
    PAIR_CASES_ON `EL i (a1:(mlstring#(A)pan_v)list)` THEN CASE_REWRITE_TAC[SND]];;

let PPASS1AUX_EXP_LOAD_TAC : tactic = REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  GVS([pan_eval_def; pan_structs_compile_exp_def; convert_v_def; old_exp_shape_def] @
      all_case_eqs()) THEN
  REWRITE_TAC[convert_s_def] THEN SIMP[is_wf_shape_compile_shape] THEN
  REWRITE_TAC[GSYM convert_s_def] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP mem_load_conversion_inst o C CONJ
    (CONJ (ASSUME `is_wf_shape (pan_state_structs (s:(A,FFI)pan_state)) shape`)
          (ASSUME `struct_infos_ok (pan_state_structs (s:(A,FFI)pan_state))`)) o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "pan_mem_load"
                     with Failure _ -> false)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  IMP_RES_TAC mem_load_some_shape_eq THEN ASM_REWRITE_TAC[];;

let PPASS1AUX_EXP_OP_TAC : tactic = REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  GVS([pan_eval_def; pan_structs_compile_exp_def; old_exp_shape_def; shape_of_def] @
      all_case_eqs()) THEN
  REWRITE_TAC[convert_v_def; v_flds_ok_def] THEN
  SUBGOAL_THEN `OPT_MMAP (pan_eval (convert_s ctxt (s:(A,FFI)pan_state)))
                  (pan_structs_compile_exps ctxt es) = SOME (MAP convert_v a)` SUBST1_TAC THENL
   [MATCH_MP_TAC compile_exp_correct_mmap_helper THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PPASS1AUX_word_lab_case_T]) THEN
  IMP_RES_TAC every_convert_v_eq THEN ASM_REWRITE_TAC[PPASS1AUX_word_lab_case_T] THEN
  CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[];;

let PPASS1AUX_EXP_NSTRUCT0_TAC : tactic = REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[UNZIP_MAP]) THEN
  GVS([pan_eval_def; UNZIP_MAP; PAIR_EQ] @ all_case_eqs()) THEN
  REWRITE_TAC[pan_structs_compile_exp_def; LET_DEF; LET_END_DEF; convert_v_def;
              shape_of_def; old_exp_shape_def] THEN
  ASM_REWRITE_TAC[PPASS1AUX_ALOOKUP_MAP_fields; OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[];;

let PPASS1AUX_EXP_NSTRUCT1_TAC : tactic = PPASS1AUX_EXP_NSTRUCT0_TAC THEN RENAME1 "ALOOKUP (pan_state_structs s) nm = SOME info" THEN
  SUBGOAL_THEN `LENGTH (a:((A)pan_v)list) = LENGTH (eflds:(mlstring#(A)panLang_exp)list)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP opt_mmap_length_eq o
      check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "OPT_MMAP"
                       with Failure _ -> false)) THEN
    REWRITE_TAC[LENGTH_MAP] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (struct_info_fields info))` ASSUME_TAC THENL
   [ASM_MESON_TAC[alookup_map_structs_ok];
    ALL_TAC] THEN
  REWRITE_TAC[MATCH_MP fields_in_order_reorder_noop
    (CONJ (ASSUME `MAP FST (struct_info_fields info) = MAP FST (eflds:(mlstring#(A)panLang_exp)list)`)
          (ASSUME `ALL_DISTINCT (MAP FST (struct_info_fields info))`))] THEN
  ALL_TAC;;

let PPASS1AUX_EXP_NSTRUCT2_TAC : tactic = PPASS1AUX_EXP_NSTRUCT1_TAC THEN
  REWRITE_TAC[MAP_o; GSYM compile_exps_eq_map; UNCURRY_EQ_o_SND] THEN
  ASM_SIMP_TAC[MAP_SND_ZIP; LENGTH_MAP] THEN
  SUBGOAL_THEN `OPT_MMAP (pan_eval (convert_s ctxt (s:(A,FFI)pan_state)))
                  (pan_structs_compile_exps ctxt (MAP SND (eflds:(mlstring#(A)panLang_exp)list))) =
                SOME (MAP convert_v (a:((A)pan_v)list))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC compile_exp_correct_mmap_helper THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[pan_eval_def] THEN CASE_REWRITE_TAC[];;

let PPASS1AUX_EXP_NSTRUCT_TAC : tactic = PPASS1AUX_EXP_NSTRUCT2_TAC THEN
  REWRITE_TAC[v_flds_ok_def; UNCURRY_EQ_o_SND; GSYM ALL_MAP] THEN
  ASM_SIMP_TAC[MAP_SND_ZIP; MAP_FST_ZIP; LENGTH_MAP] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[MAP_o] THEN
  ASM_SIMP_TAC[MAP_SND_ZIP; LENGTH_MAP] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] opt_mmap_eq_every) o
      check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "OPT_MMAP"
                       with Failure _ -> false)) THEN
    ASM_MESON_TAC[];
    UNDISCH_TAC (CASE_TERM
     `ALL (\p. match p with (s,v) -> s = shape_of v)
          (ZIP (MAP SND (struct_info_fields info)) (a:((A)pan_v)list))`) THEN
    SUBGOAL_THEN `LENGTH (MAP SND (struct_info_fields info)) = LENGTH (a:((A)pan_v)list)`
      ASSUME_TAC THENL
     [UNDISCH_TAC `MAP FST (struct_info_fields info) = MAP FST (eflds:(mlstring#(A)panLang_exp)list)` THEN
      DISCH_THEN(MP_TAC o AP_TERM `LENGTH:mlstring list->num`) THEN
      ASM_REWRITE_TAC[LENGTH_MAP];
      ALL_TAC] THEN
    ASM_SIMP_TAC[EVERY_EL; LIST_EQ_REWRITE; EL_ZIP; LENGTH_ZIP; LENGTH_MAP; EL_MAP] THEN
    CASE_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[]];;

let pan_structsProof_compile_exp_correct = prove
 (CASE_TERM
  `!s e v.
     pan_eval s e = SOME v /\
     alist_to_fmap (pan_structs_context_locals ctxt) =
       FMAP_MAP2 (shape_of o SND) (pan_state_locals (s:(A,FFI)pan_state)) /\
     alist_to_fmap (pan_structs_context_globals ctxt) =
       FMAP_MAP2 (shape_of o SND) (pan_state_globals s) /\
     pan_structs_context_structs ctxt =
       MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info)) (pan_state_structs s) /\
     FEVERY (\p. match p with (nm,v) -> v_flds_ok (pan_state_structs s) v) (pan_state_locals s) /\
     FEVERY (\p. match p with (nm,v) -> v_flds_ok (pan_state_structs s) v) (pan_state_globals s) /\
     struct_infos_ok (pan_state_structs s) ==>
     old_exp_shape ctxt e = shape_of v /\
     v_flds_ok (pan_state_structs s) v /\
     pan_eval (convert_s ctxt s) (pan_structs_compile_exp ctxt e) = SOME (convert_v v)`,
  REC_IND_TAC pan_eval_ind THEN REPEAT CONJ_TAC THENL
   [(* Const *) PPASS1AUX_EXP_GEN_TAC;
    (* Var Local *) PPASS1AUX_EXP_GEN_TAC;
    (* Var Global *) PPASS1AUX_EXP_GEN_TAC;
    (* RStruct *) PPASS1AUX_EXP_RSTRUCT_TAC;
    (* RField *) PPASS1AUX_EXP_RFIELD_TAC;
    (* NStruct *) PPASS1AUX_EXP_NSTRUCT_TAC;
    (* NField *) PPASS1AUX_EXP_NFIELD_TAC;
    (* Load *) PPASS1AUX_EXP_LOAD_TAC;
    (* Load32 *) PPASS1AUX_EXP_GEN_TAC;
    (* LoadByte *) PPASS1AUX_EXP_GEN_TAC;
    (* Op *) PPASS1AUX_EXP_OP_TAC;
    (* Panop *) PPASS1AUX_EXP_OP_TAC;
    (* Cmp *) PPASS1AUX_EXP_GEN_TAC;
    (* Shift *) PPASS1AUX_EXP_GEN_TAC;
    (* BaseAddr *) PPASS1AUX_EXP_GEN_TAC;
    (* TopAddr *) PPASS1AUX_EXP_GEN_TAC;
    (* BytesInWord *) PPASS1AUX_EXP_GEN_TAC]);;

(* uses evaluate_invariants of panProps *)
(* HOL4 [local] *)
let evaluate_structs_code_inv = prove
 (`pan_evaluate (p,s:(A,FFI)pan_state) = (res,s') ==>
   pan_state_structs s' = pan_state_structs s /\ pan_state_code s' = pan_state_code s`,
  DISCH_THEN(MP_TAC o MATCH_MP evaluate_invariants) THEN SIMP_TAC[]);;

(* HOL4 [local] *)
let eval_upd_code_eq2 = prove
 (`pan_eval (pan_state_code_fupd (K code) (t:(A,FFI)pan_state)) = pan_eval t`,
  REWRITE_TAC[FUN_EQ_THM; eval_upd_code_eq]);;

let res_var_FMAP_MAP2 = prove
 (`(!y. x = SOME y ==> (f:mlstring#(A)pan_v->(B)pan_v) (nm,y) = g y) ==>
   pan_res_var (FMAP_MAP2 f fmap) (nm,OPTION_MAP g x) =
   FMAP_MAP2 f (pan_res_var fmap (nm,x))`,
  QCASES_ON "x:((A)pan_v)option" THEN
  SIMP[pan_res_var_def; OPTION_MAP_DEF; DOMSUB_FMAP_MAP2; FMAP_MAP2_FUPDATE] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let res_var_FMAP_MAP2_rev = prove
 (`FMAP_MAP2 (f:mlstring#(A)pan_v->(B)pan_v) (pan_res_var fmap (nm,x)) =
   pan_res_var (FMAP_MAP2 f fmap) (nm,OPTION_MAP (\y. f (nm,y)) x)`,
  QCASES_ON "x:((A)pan_v)option" THEN
  SIMP[pan_res_var_def; OPTION_MAP_DEF; DOMSUB_FMAP_MAP2; FMAP_MAP2_FUPDATE]);;

let FEVERY_res_var = prove
 (`FEVERY P (pan_res_var (fmap:(mlstring,(A)pan_v)fmap) (k,opt_v)) <=>
   FEVERY P (DRESTRICT fmap (COMPL {k})) /\ (!v. opt_v = SOME v ==> P (k,v))`,
  QCASES_ON "opt_v:((A)pan_v)option" THEN
  SIMP[pan_res_var_def; fmap_domsub; FEVERY_FUPDATE; option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

(* HOL4 [local] *)
let shape_of_convert_v_ind = prove
 (CASE_TERM
  `!str_ctxt n sh (v:(A)pan_v).
     struct_infos_ok ctxt /\ is_wf_shape (DROP n ctxt) sh /\ v_flds_ok ctxt v /\
     str_ctxt = MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info)) ctxt /\
     shape_of v = sh ==>
     compile_shape_n str_ctxt n sh = shape_of (convert_v v)`,
  REC_IND_TAC compile_shape_n_ind THEN REPEAT CONJ_TAC THENL
  [(* One *)
   REPEAT GEN_TAC THEN QCASES_ON "v:(A)pan_v" THEN
   REWRITE_TAC[shape_of_def; compile_shape_n_def; convert_v_def; LET_DEF; LET_END_DEF] THEN
   CASE_REWRITE_TAC[distinctness "shape"] THEN QCASES_ON "a:(A)word_lab" THEN
   CASE_REWRITE_TAC[shape_of_def];
   (* Comb *)
   REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN QCASES_ON "v:(A)pan_v" THEN
   REWRITE_TAC[shape_of_val; shape_of_def; distinctness "shape"; injectivity "shape"] THEN
   STRIP_TAC THEN RVEQ_TAC THEN
   REWRITE_TAC[compile_shape_n_def; convert_v_def; shape_of_def; injectivity "shape"; MAP_MAP_o] THEN
   MATCH_MP_TAC MAP_CONG THEN REWRITE_TAC[o_THM] THEN X_GEN_TAC `w:(A)pan_v` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `shape_of (w:(A)pan_v)`) THEN REWRITE_TAC[MEM_MAP] THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[is_wf_shape_def; v_flds_ok_def; EVERY_MEM; MEM_MAP]) THEN
   ASM_MESON_TAC[];
   (* Named *)
   (REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN QCASES_ON "v:(A)pan_v" THEN
   REWRITE_TAC[shape_of_val; shape_of_def; distinctness "shape"; injectivity "shape"] THEN
   STRIP_TAC THEN RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[is_wf_shape_def]) THEN
   QCASES_ON "ALOOKUP (DROP n (ctxt:(mlstring#struct_info)list)) nm" THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
   RENAME1 "ALOOKUP (DROP n ctxt) nm = SOME info" THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP wf_shape_struct_infos_ok_helper o C CONJ
     (ASSUME `struct_infos_ok (ctxt:(mlstring#struct_info)list)`)) THEN
   DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `i + n = n + i:num` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN (CASE_TERM
     `afindi nm (DROP n (MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info))
                             (ctxt:(mlstring#struct_info)list))) = SOME i`) ASSUME_TAC THENL
    [REWRITE_TAC[GSYM MAP_DROP] THEN
     SUBST1_TAC(SYM(ASSUME `afindi nm (DROP n (ctxt:(mlstring#struct_info)list)) = SOME i`)) THEN
     MATCH_MP_TAC afindi_MAP_eq THEN CASE_REWRITE_TAC[FST];
     ALL_TAC] THEN
   SUBGOAL_THEN (CASE_TERM
     `EL (n + i) (MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info))
                      (ctxt:(mlstring#struct_info)list)) =
      (nm,struct_info_fields info)`) ASSUME_TAC THENL
    [REWRITE_TAC[MATCH_MP EL_MAP (ASSUME `n + i < LENGTH (ctxt:(mlstring#struct_info)list)`)] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[compile_shape_n_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[struct_infos_ok_def] o
     check (fun th -> try fst(dest_const(rator(concl th))) = "struct_infos_ok"
                      with Failure _ -> false)) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP alookup_drop_helper o C CONJ
     (ASSUME `ALL_DISTINCT (MAP FST (ctxt:(mlstring#struct_info)list))`) o
     check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "ALOOKUP"
                      with Failure _ -> false)) THEN
   STRIP_TAC THEN
   UNDISCH_TAC `v_flds_ok ctxt (pan_NStruct nm (a1:(mlstring#(A)pan_v)list))` THEN
   ASM_REWRITE_TAC[v_flds_ok_def] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
   FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> try
     rand(rator(rhs(concl th))) = `SND:mlstring#shape->shape` with Failure _ -> false)) THEN
   REWRITE_TAC[convert_v_def; LET_DEF; LET_END_DEF; shape_of_def; injectivity "shape";
               UNCURRY_EQ_o_SND; MAP_MAP_o]) THEN
   (MATCH_MP_TAC MAP_CONG THEN REWRITE_TAC[o_THM] THEN
   X_GEN_TAC `p:mlstring#(A)pan_v` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`nm:mlstring`; `struct_info_fields info`; `i:num`;
                                 `shape_of (SND (p:mlstring#(A)pan_v))`] o
     check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 4)) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
    [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> try
       rand(rator(rhs(concl th))) = `SND:mlstring#shape->shape` with Failure _ -> false)) THEN
     REWRITE_TAC[MEM_MAP; o_THM] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN
     FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> try
       rand(rator(rhs(concl th))) = `SND:mlstring#shape->shape` with Failure _ -> false)) THEN
     REWRITE_TAC[MEM_MAP; o_THM] THEN ASM_MESON_TAC[];
     UNDISCH_TAC (CASE_TERM `ALL (\p. match p with (nm,v) -> v_flds_ok ctxt v)
                                 (a1:(mlstring#(A)pan_v)list)`) THEN
     REWRITE_TAC[EVERY_MEM] THEN DISCH_THEN(MP_TAC o SPEC `p:mlstring#(A)pan_v`) THEN
     ASM_REWRITE_TAC[] THEN PAIR_CASES_ON `p:mlstring#(A)pan_v` THEN CASE_REWRITE_TAC[SND]])]);;

let shape_of_convert_v = prove
 (CASE_TERM
  `!(v:(A)pan_v) str_ctxt.
     v_flds_ok ctxt v /\
     str_ctxt = MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info)) ctxt /\
     is_wf_shape_v ctxt v /\
     struct_infos_ok ctxt ==>
     compile_shape str_ctxt (shape_of v) = shape_of (convert_v v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[compile_shape_n_eq_rev] THEN
  MP_TAC(ISPECL [`str_ctxt:(mlstring#((mlstring#shape)list))list`; `0`;
                 `shape_of (v:(A)pan_v)`; `v:(A)pan_v`] shape_of_convert_v_ind) THEN
  ASM_REWRITE_TAC[DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC is_wf_shape_of_v THEN ASM_REWRITE_TAC[]);;

let shape_of_convert_v_rev = prove
 (CASE_TERM
  `!v:(A)pan_v.
     v_flds_ok ctxt v /\ is_wf_shape_v ctxt v /\ struct_infos_ok ctxt ==>
     shape_of (convert_v v) =
     compile_shape (MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info)) ctxt)
                   (shape_of v)`,
  MESON_TAC[shape_of_convert_v]);;

let flatten_convert_v = prove
 (`!v:(A)pan_v. flatten (convert_v v) = flatten v`,
  REC_IND_TAC convert_v_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[convert_v_def; flatten_def; LET_DEF; LET_END_DEF; MAP_MAP_o] THEN
  DISCH_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MAP_CONG THEN
  REWRITE_TAC[o_THM] THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[SND] THEN
  ASM_MESON_TAC[]);;

let map_uncurry_zip_again = prove
 (CASE_TERM
  `LENGTH (xs:A list) = LENGTH (ys:B list) ==>
   MAP (\p. match p with (x,y) -> ((f:A->C) x,(g:B->D) y)) (ZIP xs ys) =
   ZIP (MAP f xs) (MAP g ys)`,
  SPEC_TAC(`ys:B list`,`ys:B list`) THEN SPEC_TAC(`xs:A list`,`xs:A list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; ZIP; MAP] THEN
  CASE_REWRITE_TAC[injectivity "list"] THEN ASM_MESON_TAC[]);;

let fupdate_elim2 = prove
 (`FLOOKUP (fm:(A,B)fmap) x = SOME y ==> fm |+ (x,y) = fm`,
  REWRITE_TAC[FMAPAUX_FUPDATE_FLOOKUP_ELIM]);;

(* HOL4 [local] *)
let lookup_code_flds_ok = prove
 (CASE_TERM
  `OPT_MMAP (pan_eval s) argexps = SOME args /\
   pan_lookup_code (pan_state_code (s:(A,FFI)pan_state)) fname args =
     SOME (prog,newlocals,rshape) /\
   alist_to_fmap (pan_structs_context_locals ctxt) =
     FMAP_MAP2 (shape_of o SND) (pan_state_locals s) /\
   alist_to_fmap (pan_structs_context_globals ctxt) =
     FMAP_MAP2 (shape_of o SND) (pan_state_globals s) /\
   pan_structs_context_structs ctxt =
     MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info)) (pan_state_structs s) /\
   FEVERY (\p. match p with (nm,v) -> v_flds_ok (pan_state_structs s) v) (pan_state_locals s) /\
   FEVERY (\p. match p with (nm,v) -> v_flds_ok (pan_state_structs s) v) (pan_state_globals s) /\
   FEVERY (\p. match p with (nm,v) -> is_wf_shape_v (pan_state_structs s) v)
          (pan_state_locals s) /\
   FEVERY (\p. match p with (nm,v) -> is_wf_shape_v (pan_state_structs s) v)
          (pan_state_globals s) /\
   struct_infos_ok (pan_state_structs s) ==>
   OPT_MMAP (pan_eval (convert_s ctxt s)) (pan_structs_compile_exps ctxt argexps) =
     SOME (MAP convert_v args) /\
   ALL (\v. v_flds_ok (pan_state_structs s) v) args /\
   (?new_l.
      pan_lookup_code (pan_state_code (convert_s ctxt s)) fname (MAP convert_v args) =
        SOME (pan_structs_compile (pan_structs_context_locals_fupd (K new_l) ctxt) prog,
              FMAP_MAP2 (\p. match p with (nm,v) -> convert_v v) newlocals,
              compile_shape (pan_structs_context_structs ctxt) rshape) /\
      alist_to_fmap new_l = FMAP_MAP2 (shape_of o SND) (newlocals:(mlstring,(A)pan_v)fmap)) /\
   FEVERY (\p. match p with (nm,v) -> v_flds_ok (pan_state_structs s) v) newlocals /\
   FEVERY (\p. match p with (nm,v) -> is_wf_shape_v (pan_state_structs s) v) newlocals`,
  (STRIP_TAC THEN
   SUBGOAL_THEN `ALL (\v. is_wf_shape_v (pan_state_structs (s:(A,FFI)pan_state)) v /\
                          v_flds_ok (pan_state_structs s) v) (args:((A)pan_v)list)`
     ASSUME_TAC THENL
    [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] opt_mmap_eq_every)) THEN
     REPEAT STRIP_TAC THEN BETA_TAC THEN CONJ_TAC THENL
      [MATCH_MP_TAC eval_is_wf_shape_v THEN ASM_MESON_TAC[];
       MP_TAC(ISPECL [`s:(A,FFI)pan_state`; `x:(A)panLang_exp`; `y:(A)pan_v`]
         pan_structsProof_compile_exp_correct) THEN
       ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
    `?vshapes. FLOOKUP (pan_state_code (s:(A,FFI)pan_state)) fname =
                 SOME (vshapes,prog,rshape) /\
               ALL_DISTINCT (MAP FST (vshapes:(mlstring#shape)list)) /\
               ALL2 (\vshape arg. SND vshape = shape_of arg) vshapes (args:((A)pan_v)list) /\
               newlocals = FEMPTY |++ ZIP (MAP FST vshapes) args`
     STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `pan_lookup_code (pan_state_code (s:(A,FFI)pan_state)) fname args =
                    SOME (prog,newlocals,rshape)` THEN
     REWRITE_TAC[pan_lookup_code_def] THEN
     QCASES_ON "FLOOKUP (pan_state_code (s:(A,FFI)pan_state)) fname" THEN
     CASE_REWRITE_TAC[distinctness "option"] THEN
     PAIR_CASES_ON `a:(mlstring#shape)list#(A)panLang_prog#shape` THEN
     CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN
     REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN
     ASM_MESON_TAC[];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `LENGTH (vshapes:(mlstring#shape)list) = LENGTH (args:((A)pan_v)list)`
     ASSUME_TAC THENL [ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC]) THEN
  (SUBGOAL_THEN (CASE_TERM `FEVERY (\p. match p with (nm,v) -> MEM v args)
                              (newlocals:(mlstring,(A)pan_v)fmap)`) ASSUME_TAC THENL
    [ASM_REWRITE_TAC[FEVERY_ALL_FLOOKUP; flookup_fupdate_list; FLOOKUP_EMPTY] THEN
     REPEAT GEN_TAC THEN
     QCASES_ON "ALOOKUP (REVERSE (ZIP (MAP FST (vshapes:(mlstring#shape)list))
                                      (args:((A)pan_v)list))) k" THEN
     CASE_REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
     DISCH_THEN SUBST_ALL_TAC THEN
     FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN REWRITE_TAC[MEM_REVERSE] THEN
     DISCH_TAC THEN
     MP_TAC(ISPECL [`MAP FST (vshapes:(mlstring#shape)list)`; `args:((A)pan_v)list`;
                    `(k:mlstring,v:(A)pan_v)`] MEM_ZIP) THEN
     ASM_REWRITE_TAC[LENGTH_MAP; PAIR_EQ] THEN STRIP_TAC THEN
     ASM_MESON_TAC[EL_MEM; LENGTH_MAP];
     ALL_TAC]) THEN
  (REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC compile_exp_correct_mmap_helper THEN ASM_REWRITE_TAC[] THEN
     REPEAT STRIP_TAC THEN
     MP_TAC(ISPECL [`s:(A,FFI)pan_state`; `e:(A)panLang_exp`; `v:(A)pan_v`]
       pan_structsProof_compile_exp_correct) THEN
     ASM_REWRITE_TAC[] THEN SIMP_TAC[];
     UNDISCH_TAC `ALL (\v. is_wf_shape_v (pan_state_structs (s:(A,FFI)pan_state)) v /\
                           v_flds_ok (pan_state_structs s) v) (args:((A)pan_v)list)` THEN
     MATCH_MP_TAC MONO_ALL THEN SIMP_TAC[];
     EXISTS_TAC `vshapes:(mlstring#shape)list` THEN
     SIMP[pan_lookup_code_def; convert_s_def; convert_code_def; FLOOKUP_FMAP_MAP2] THEN
     REPEAT CONJ_TAC THENL
      [UNDISCH_TAC `ALL2 (\vshape arg. SND vshape = shape_of arg)
                      (vshapes:(mlstring#shape)list) (args:((A)pan_v)list)` THEN
       UNDISCH_TAC `ALL (\v. is_wf_shape_v (pan_state_structs (s:(A,FFI)pan_state)) v /\
                             v_flds_ok (pan_state_structs s) v) (args:((A)pan_v)list)` THEN
       REWRITE_TAC[ALL2_MAP2; LIST_REL_EL_EQN; EVERY_EL] THEN
       DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
       X_GEN_TAC `n:num` THEN DISCH_TAC THEN
       REWRITE_TAC[SND_PAIR_MAP] THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
       DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
       MATCH_MP_TAC shape_of_convert_v_rev THEN ASM_MESON_TAC[];
       REWRITE_TAC[FMAP_MAP2_FUPDATE_LIST; FMAP_MAP2_FEMPTY] THEN AP_TERM_TAC THEN
       MP_TAC(ISPECL [`MAP FST (vshapes:(mlstring#shape)list)`; `args:((A)pan_v)list`;
                      `I:mlstring->mlstring`; `convert_v:(A)pan_v->(A)pan_v`] ZIP_MAP) THEN
       ASM_REWRITE_TAC[LENGTH_MAP] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
       MATCH_MP_TAC MAP_CONG THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
       CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN CASE_REWRITE_TAC[];
       REWRITE_TAC[FMAP_MAP2_FUPDATE_LIST; FMAP_MAP2_FEMPTY] THEN
       MATCH_MP_TAC EQ_TRANS THEN
       EXISTS_TAC `FEMPTY |++ ZIP (MAP FST (vshapes:(mlstring#shape)list))
                                  (MAP shape_of (args:((A)pan_v)list))` THEN
       CONJ_TAC THENL
        [SUBGOAL_THEN `MAP SND (vshapes:(mlstring#shape)list) =
                       MAP shape_of (args:((A)pan_v)list)` (SUBST1_TAC o SYM) THENL
          [UNDISCH_TAC `ALL2 (\vshape arg. SND vshape = shape_of arg)
                          (vshapes:(mlstring#shape)list) (args:((A)pan_v)list)` THEN
           REWRITE_TAC[LIST_REL_EL_EQN; LIST_EQ; LENGTH_MAP] THEN STRIP_TAC THEN
           ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
           ASM_SIMP_TAC[EL_MAP];
           ALL_TAC] THEN
         ASM_SIMP_TAC[fm_empty_zip_alist; LENGTH_MAP; REWRITE_RULE[UNZIP_DEF] ZIP_UNZIP];
         AP_TERM_TAC THEN
         MP_TAC(ISPECL [`MAP FST (vshapes:(mlstring#shape)list)`; `args:((A)pan_v)list`;
                        `I:mlstring->mlstring`; `shape_of:(A)pan_v->shape`] ZIP_MAP) THEN
         ASM_REWRITE_TAC[LENGTH_MAP] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
         MATCH_MP_TAC MAP_CONG THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
         CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[o_THM; SND]]];
     UNDISCH_TAC (CASE_TERM `FEVERY (\p. match p with (nm,v) -> MEM v args)
                              (newlocals:(mlstring,(A)pan_v)fmap)`) THEN
     UNDISCH_TAC `ALL (\v. is_wf_shape_v (pan_state_structs (s:(A,FFI)pan_state)) v /\
                           v_flds_ok (pan_state_structs s) v) (args:((A)pan_v)list)` THEN
     REWRITE_TAC[FEVERY_ALL_FLOOKUP; EVERY_MEM] THEN CASE_REWRITE_TAC[] THEN MESON_TAC[];
     UNDISCH_TAC (CASE_TERM `FEVERY (\p. match p with (nm,v) -> MEM v args)
                              (newlocals:(mlstring,(A)pan_v)fmap)`) THEN
     UNDISCH_TAC `ALL (\v. is_wf_shape_v (pan_state_structs (s:(A,FFI)pan_state)) v /\
                           v_flds_ok (pan_state_structs s) v) (args:((A)pan_v)list)` THEN
     REWRITE_TAC[FEVERY_ALL_FLOOKUP; EVERY_MEM] THEN CASE_REWRITE_TAC[] THEN MESON_TAC[]]));;

(* HOL4: [local, simp] *)
let convert_code_locals_upd = prove
 (`convert_code (pan_structs_context_locals_fupd f ctxt)
                (code:(mlstring,(mlstring#shape)list#(A)panLang_prog#shape)fmap) =
   convert_code ctxt code`,
  SIMP[convert_code_def]);;

let _ = cake_add_simps [convert_code_locals_upd];;

let is_cont_res_def = sem1aux_def
  `(is_cont_res (NONE:((A)pan_result)option) <=> T) /\
   (is_cont_res (SOME pan_Break) <=> T) /\
   (is_cont_res (SOME pan_Continue) <=> T) /\
   (is_cont_res _ <=> F)`;;

let is_cont_res_eq_disj = prove
 (`is_cont_res (res:((A)pan_result)option) <=>
   res = NONE \/ res = SOME pan_Break \/ res = SOME pan_Continue`,
  QCASES_ON "res:((A)pan_result)option" THEN
  REWRITE_TAC[is_cont_res_def; distinctness "option"; injectivity "option"] THEN
  QCASES_ON "a:(A)pan_result" THEN
  REWRITE_TAC[is_cont_res_def; distinctness "pan_result"]);;

let convert_res_def = sem1aux_def
  `(convert_res (SOME pan_Break) = SOME (pan_Break:(A)pan_result)) /\
   (convert_res (SOME (pan_Return v)) = SOME (pan_Return (convert_v v))) /\
   (convert_res (SOME (pan_Exception eid ev)) = SOME (pan_Exception eid (convert_v ev))) /\
   (convert_res res = res)`;;

let convert_res_eq_case1 = prove
 (CASE_TERM
  `convert_res (res:((A)pan_result)option) =
   match res with
     SOME pan_Break -> convert_res (SOME pan_Break)
   | SOME x -> convert_res (SOME x)
   | NONE -> NONE`,
  EVERY_CASE_TAC THEN CASE_REWRITE_TAC[convert_res_def]);;

let convert_res_eq_case = REWRITE_RULE[convert_res_def] convert_res_eq_case1;;

(* HOL4: SIMP_CONV (srw_ss ()) [convert_res_eq_case, option_case_eq,       *)
(* result_case_eq] of convert_res res = NONE                               *)
let convert_res_eq_NONE = prove
 (`convert_res (res:((A)pan_result)option) = NONE <=> res = NONE`,
  ONCE_REWRITE_TAC[convert_res_eq_case] THEN EVERY_CASE_TAC THEN
  CASE_REWRITE_TAC[distinctness "option"]);;

let res_vs_def = sem1aux_def
  `(res_vs (SOME (pan_Return v)) = [v:(A)pan_v]) /\
   (res_vs (SOME (pan_Exception eid ev)) = [ev]) /\
   (res_vs (_:((A)pan_result)option) = [])`;;

(* compile_correct; uses evaluate_invariants and evaluate_is_wf_shape_invariant of panProps *)

(* the values of a finite map satisfy the predicate of its FEVERY *)
let PPASS1AUX_FEVERY_VAL = prove
 (CASE_TERM
  `!(P:D->bool) (m:(C,D)fmap) k x.
     FEVERY (\p. match p with (nm,v) -> P v) m /\ FLOOKUP m k = SOME x ==> P x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [CASE_TERM `\p:C#D. match p with (nm,v) -> (P:D->bool) v`;
                 `m:(C,D)fmap`; `k:C`; `x:D`] FEVERY_FLOOKUP) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let PPASS1AUX_ASG_CLOSE_TAC (fld:term) : tactic =
  SUBGOAL_THEN `v_flds_ok (pan_state_structs (s:(A,FFI)pan_state)) (w:(A)pan_v) /\
                is_wf_shape_v (pan_state_structs s) w` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`v_flds_ok (pan_state_structs (s:(A,FFI)pan_state)):(A)pan_v->bool`;
                           mk_comb(fld,`s:(A,FFI)pan_state`); `v:mlstring`; `w:(A)pan_v`]
                          PPASS1AUX_FEVERY_VAL);
      MATCH_MP_TAC(ISPECL [`is_wf_shape_v (pan_state_structs (s:(A,FFI)pan_state)):(A)pan_v->bool`;
                           mk_comb(fld,`s:(A,FFI)pan_state`); `v:mlstring`; `w:(A)pan_v`]
                          PPASS1AUX_FEVERY_VAL)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `shape_of (convert_v (value:(A)pan_v)) = shape_of (convert_v (w:(A)pan_v))`
    ASSUME_TAC THENL
   [MP_TAC(ISPEC `value:(A)pan_v`
      (INST [`pan_state_structs (s:(A,FFI)pan_state)`,`ctxt:(mlstring#struct_info)list`]
            shape_of_convert_v_rev)) THEN
    MP_TAC(ISPEC `w:(A)pan_v`
      (INST [`pan_state_structs (s:(A,FFI)pan_state)`,`ctxt:(mlstring#struct_info)list`]
            shape_of_convert_v_rev)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pan_structs_compile_def; pan_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[pan_is_valid_value_def; kvar_simps] THEN
  SIMP[convert_s_def; FLOOKUP_FMAP_MAP2; pan_set_var_def; pan_set_global_def;
       FMAP_MAP2_FUPDATE; FEVERY_FUPDATE; convert_res_def; is_cont_res_def; res_vs_def;
       ALL; o_THM] THEN
  ASM_SIMP_TAC[fevery_to_drestrict; fupdate_elim2; FLOOKUP_FMAP_MAP2; o_THM] THEN
  CASE_REWRITE_TAC[] THEN
  TRY(CONV_TAC SYM_CONV THEN MATCH_MP_TAC fupdate_elim2 THEN
      ASM_REWRITE_TAC[FLOOKUP_FMAP_MAP2; OPTION_MAP_DEF; o_THM]);;

let PPASS1AUX_CC_SRC_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
                                              "pan_evaluate" with Failure _ -> false)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [pan_evaluate_def] THEN
  REPEAT(TOP_CASE_TAC THEN CASE_REWRITE_TAC[]) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  TRY(FIRST_X_ASSUM(MP_TAC o check (fun th -> try rand(concl th) = rand(rand(concl th)) && false
                                              with Failure _ -> false)) THEN NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  TRY(FIRST_ASSUM CONTR_TAC);;

(* for every assumption pan_eval s e = SOME v (s the state variable s),    *)
(* the facts of compile_exp_correct and eval_is_wf_shape_v                 *)
let PPASS1AUX_CC_EXPS_TAC : tactic = fun (asl,w as g) ->
  let s0 = `s:(A,FFI)pan_state` in
  let evs = mapfilter (fun (_,th) ->
      let l,r = dest_eq(concl th) in
      let f,args = strip_comb l in
      if fst(dest_const f) = "pan_eval" && length args = 2 && hd args = s0 &&
         fst(dest_const(rator r)) = "SOME"
      then (el 1 args, rand r) else failwith "") asl in
  MAP_EVERY (fun (e,v) ->
      MP_TAC(ISPECL [s0; e; v] pan_structsProof_compile_exp_correct) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [s0; e; v] eval_is_wf_shape_v) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC) evs g;;

let PPASS1AUX_CC_TGT_TAC : tactic =
  REWRITE_TAC[pan_structs_compile_def; pan_evaluate_def] THEN
  ASM_REWRITE_TAC[convert_v_def; flatten_convert_v] THEN CASE_REWRITE_TAC[flatten_convert_v] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SIMP[convert_s_def; convert_res_def; is_cont_res_def; res_vs_def; ALL;
       pan_state_component_equality] THEN
  ASM_REWRITE_TAC[];;

let PPASS1AUX_CC_SIMPLE_TAC : tactic =
  PPASS1AUX_CC_SRC_TAC THEN PPASS1AUX_CC_EXPS_TAC THEN PPASS1AUX_CC_TGT_TAC;;

let PPASS1AUX_CC_SRC2_TAC (ths:thm list) : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
                                              "pan_evaluate" with Failure _ -> false)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [pan_evaluate_def] THEN
  REWRITE_TAC ths THEN
  REPEAT((TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN CASE_REWRITE_TAC ths) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  TRY(FIRST_ASSUM CONTR_TAC);;

let PPASS1AUX_CC_FIN_TAC : tactic =
  SIMP[pan_set_var_def; pan_set_global_def; pan_empty_locals_def; convert_res_def;
       pan_state_component_equality; FMAP_MAP2_FUPDATE; FMAP_MAP2_FEMPTY; FEVERY_FUPDATE;
       FEVERY_FEMPTY; is_cont_res_def; res_vs_def; ALL; v_flds_ok_def; convert_v_def;
       o_THM; shape_of_val; convert_s_def] THEN
  ASM_SIMP_TAC[fevery_to_drestrict] THEN CASE_REWRITE_TAC[] THEN
  TRY(CONV_TAC SYM_CONV THEN MATCH_MP_TAC fupdate_elim2 THEN
      ASM_REWRITE_TAC[FLOOKUP_FMAP_MAP2; OPTION_MAP_DEF; o_THM; shape_of_val]);;

let PPASS1AUX_CC_SHL_TAC : tactic =
  QCASES_ON "vk:varkind" THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  PPASS1AUX_CC_EXPS_TAC THEN
  REWRITE_TAC[pan_structs_compile_def; pan_evaluate_def] THEN
  ASM_REWRITE_TAC[convert_v_def] THEN CASE_REWRITE_TAC[] THEN
  SIMP[convert_s_def; FLOOKUP_FMAP_MAP2; kvar_simps; pan_lookup_kvar_def] THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[convert_v_def] THEN
  REWRITE_TAC[pan_sh_mem_load_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN PPASS1AUX_CC_FIN_TAC;;

let PPASS1AUX_CC_SHS_TAC : tactic =
  PPASS1AUX_CC_EXPS_TAC THEN
  REWRITE_TAC[pan_structs_compile_def; pan_evaluate_def] THEN
  ASM_REWRITE_TAC[convert_v_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[pan_sh_mem_store_def] THEN SIMP[convert_s_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN PPASS1AUX_CC_FIN_TAC;;

let PPASS1AUX_CC_SRC3_TAC (ths:thm list) : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
                                              "pan_evaluate" &&
                                              not (is_var(rand(lhs(concl th)))) &&
                                              is_comb(fst(dest_pair(rand(lhs(concl th)))))
                                          with Failure _ -> false)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [pan_evaluate_def] THEN
  REWRITE_TAC ths THEN
  REPEAT((TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN CASE_REWRITE_TAC ths) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  (DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) ORELSE DISCH_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  TRY(FIRST_ASSUM CONTR_TAC);;

(* the induction hypothesis guarded by pan_eval s e = SOME (pan_Val (Word w)), *)
(* at the w of that assumption                                                *)
let PPASS1AUX_IH_AT_WORD_TAC : tactic =
  FIRST_ASSUM(fun ev ->
    let l,r = dest_eq(concl ev) in
    if fst(dest_const(fst(strip_comb l))) = "pan_eval" &&
       (try fst(dest_const(rator(rand r))) = "pan_Val" with Failure _ -> false) then
      let w = rand(rand(rand r)) in
      FIRST_X_ASSUM(MP_TAC o SPEC w o check (is_forall o concl))
    else NO_TAC) THEN
  ASM_REWRITE_TAC[];;

let PPASS1AUX_CC_IF_TAC : tactic =
  PPASS1AUX_CC_EXPS_TAC THEN
  REWRITE_TAC[pan_structs_compile_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [pan_evaluate_def] THEN
  ASM_REWRITE_TAC[convert_v_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  PPASS1AUX_IH_AT_WORD_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `s':(A,FFI)pan_state`;
                             `ctxt:pan_structs_context`]) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[];;

let PPASS1AUX_convert_s_dec_clock = prove
 (`pan_dec_clock (convert_s ctxt (s:(A,FFI)pan_state)) = convert_s ctxt (pan_dec_clock s)`,
  SIMP[convert_s_def; pan_dec_clock_def; pan_state_component_equality]);;

let PPASS1AUX_convert_s_clock = prove
 (`pan_state_clock (convert_s ctxt (s:(A,FFI)pan_state)) = pan_state_clock s`,
  SIMP[convert_s_def]);;

let PPASS1AUX_CC_WTGT_TAC : tactic =
  REWRITE_TAC[pan_structs_compile_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [pan_evaluate_def] THEN
  ASM_REWRITE_TAC[convert_v_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[PPASS1AUX_convert_s_clock; PPASS1AUX_convert_s_dec_clock];;

let PPASS1AUX_pan_state_accfupds = (record_info "pan_state").ri_accfupds;;

let PPASS1AUX_WORD_OF_EVAL (ev:thm) =
  let l,r = dest_eq(concl ev) in
  if fst(dest_const(fst(strip_comb l))) = "pan_eval" &&
     (try fst(dest_const(rator(rand r))) = "pan_Val" with Failure _ -> false)
  then rand(rand(rand r)) else failwith "PPASS1AUX_WORD_OF_EVAL";;

let PPASS1AUX_IS_BODY_RUN (th:thm) =
  try let l,r = dest_eq(concl th) in
      fst(dest_const(fst(strip_comb l))) = "pan_evaluate" &&
      rand(rand l) = `pan_dec_clock (s:(A,FFI)pan_state)`
  with Failure _ -> false;;

(* the induction hypothesis "ihb" of the loop body at the run            *)
(* pan_evaluate (c,pan_dec_clock s) = R,y of the assumptions, with the     *)
(* invariants of that run                                                  *)
let PPASS1AUX_WHILE_BODY_TAC : tactic =
  FIRST_ASSUM(fun ev -> REMOVE_THEN "ihb" (MP_TAC o SPEC (PPASS1AUX_WORD_OF_EVAL ev))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if PPASS1AUX_IS_BODY_RUN th then
      let rr,yy = dest_pair(rand(concl th)) in
      DISCH_THEN(MP_TAC o SPECL [rr; yy; `ctxt:pan_structs_context`])
    else NO_TAC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SIMP[pan_dec_clock_def] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "option"; distinctness "pan_result"];
    STRIP_TAC] THEN
  FIRST_ASSUM(fun th ->
    if PPASS1AUX_IS_BODY_RUN th then
      let cc = fst(dest_pair(rand(lhs(concl th)))) in
      let rr,yy = dest_pair(rand(concl th)) in
      STRIP_ASSUME_TAC(REWRITE_RULE[pan_dec_clock_def; PPASS1AUX_pan_state_accfupds; K_THM]
                         (MATCH_MP evaluate_structs_code_inv th)) THEN
      MP_TAC(ISPECL [cc; `pan_dec_clock (s:(A,FFI)pan_state)`; rr; yy]
                    evaluate_is_wf_shape_invariant) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMP[pan_dec_clock_def] THEN ASM_REWRITE_TAC[];
                      SIMP[pan_dec_clock_def] THEN STRIP_TAC]
    else NO_TAC);;
(* the run of the loop again, after the body ended in NONE or Continue,    *)
(* with the induction hypothesis lab ("ihw" or "ihc")                       *)
let PPASS1AUX_WHILE_LOOP_TAC (lab:string) : tactic =
  FIRST_ASSUM(fun th ->
    if PPASS1AUX_IS_BODY_RUN th then
      let yy = snd(dest_pair(rand(concl th))) in
      FIRST_ASSUM(fun ev -> REMOVE_THEN lab (MP_TAC o SPECL [PPASS1AUX_WORD_OF_EVAL ev; yy]))
    else NO_TAC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `s':(A,FFI)pan_state`;
                             `ctxt:pan_structs_context`]) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[is_cont_res_def]) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pan_structs_compile_def] THEN SIMP_TAC[] THEN
  TRY(STRIP_TAC THEN ASM_MESON_TAC[]);;

let PPASS1AUX_CC_WLOOP_TAC (lab:string) : tactic =
  PPASS1AUX_CC_EXPS_TAC THEN PPASS1AUX_WHILE_BODY_TAC THEN
  PPASS1AUX_CC_WTGT_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[convert_res_def] THEN
  PPASS1AUX_WHILE_LOOP_TAC lab;;

let PPASS1AUX_CC_WSTOP_TAC : tactic =
  PPASS1AUX_CC_EXPS_TAC THEN PPASS1AUX_WHILE_BODY_TAC THEN
  PPASS1AUX_CC_WTGT_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[convert_res_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[is_cont_res_def]) THEN
  ASM_REWRITE_TAC[convert_res_def; is_cont_res_def; res_vs_def; ALL] THEN
  TRY(ASM_MESON_TAC[]);;

(* for the value of an assumption pan_eval s e = SOME v: the shape of      *)
(* convert_v v and the size of that shape in the empty context            *)
let PPASS1AUX_CC_SIZE_TAC : tactic =
  FIRST_ASSUM(fun ev ->
    let l,r = dest_eq(concl ev) in
    if fst(dest_const(fst(strip_comb l))) = "pan_eval" &&
       el 0 (snd(strip_comb l)) = `s:(A,FFI)pan_state` &&
       fst(dest_const(rator r)) = "SOME" then
      let v = rand r in
      MP_TAC(ISPEC v (INST [`pan_state_structs (s:(A,FFI)pan_state)`,
                             `ctxt:(mlstring#struct_info)list`] shape_of_convert_v_rev)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`pan_state_structs (s:(A,FFI)pan_state)`; v] is_wf_shape_of_v) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(INST [`pan_state_structs (s:(A,FFI)pan_state)`,`ctxt:(mlstring#struct_info)list`;
                   mk_comb(`shape_of:(A)pan_v->shape`,v),`sh:shape`] size_of_compile_shape) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC
    else NO_TAC);;

let PPASS1AUX_convert_s_locals_upd = prove
 (`convert_s (pan_structs_context_locals_fupd f ctxt) (s:(A,FFI)pan_state) = convert_s ctxt s`,
  SIMP[convert_s_def]);;

let PPASS1AUX_convert_s_callee = prove
 (CASE_TERM
  `pan_state_locals_fupd
     (K (FMAP_MAP2 (\p. match p with (nm,v) -> convert_v v) (l:(mlstring,(A)pan_v)fmap)))
     (pan_dec_clock (convert_s ctxt (s:(A,FFI)pan_state))) =
   convert_s ctxt (pan_state_locals_fupd (K l) (pan_dec_clock s))`,
  SIMP[convert_s_def; pan_dec_clock_def; pan_state_component_equality]);;

(* the assumption pan_lookup_code (pan_state_code s) fname args = SOME (prog,nl,rsh) *)
let PPASS1AUX_CALL_LOOKUP (asl:(string*thm) list) =
  let lk = snd(find (fun (_,th) ->
    try let l = lhs(concl th) in
        fst(dest_const(fst(strip_comb l))) = "pan_lookup_code" &&
        el 0 (snd(strip_comb l)) = `pan_state_code (s:(A,FFI)pan_state)`
    with Failure _ -> false) asl) in
  let l,r = dest_eq(concl lk) in
  let fn = el 1 (snd(strip_comb l)) and args = el 2 (snd(strip_comb l)) in
  let prog,rest = dest_pair(rand r) in
  let nl,rsh = dest_pair rest in
  fn,args,prog,nl,rsh;;

(* the call: lookup_code_flds_ok at the arguments and the looked-up code *)
let PPASS1AUX_CALL_LOOKUP_TAC : tactic = fun (asl,w as g) ->
  let fn,args,prog,nl,rsh = PPASS1AUX_CALL_LOOKUP asl in
  let th = INST [args,`args:((A)pan_v)list`; prog,`prog:(A)panLang_prog`;
                 nl,`newlocals:(mlstring,(A)pan_v)fmap`; rsh,`rshape:shape`;
                 fn,`fname:mlstring`] lookup_code_flds_ok in
  (MP_TAC th THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (X_CHOOSE_THEN `new_l:(mlstring#shape)list` STRIP_ASSUME_TAC)
                      STRIP_ASSUME_TAC)))) g;;

let PPASS1AUX_compile_call = prove
 (CASE_TERM
  `pan_structs_compile ctxt (panLang_Call caltyp f (es:((A)panLang_exp)list)) =
   panLang_Call (match caltyp with
                   NONE -> NONE
                 | SOME (tl,hdl) ->
                     SOME (tl,match hdl with
                                NONE -> NONE
                              | SOME (eid,evar,p) ->
                                  SOME (eid,evar,pan_structs_compile ctxt p)))
                f (pan_structs_compile_exps ctxt es)`,
  REWRITE_TAC[pan_structs_compile_def; LET_DEF; LET_END_DEF] THEN
  REPEAT(TOP_CASE_TAC THEN CASE_REWRITE_TAC[]));;

(* the target call up to the run of the callee *)
let PPASS1AUX_CALL_TGT_TAC : tactic =
  REWRITE_TAC[PPASS1AUX_compile_call] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [pan_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[PPASS1AUX_convert_s_clock; PPASS1AUX_convert_s_callee;
                  LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[];;

(* the run of the callee: pan_evaluate (prog,pan_state_locals_fupd (K nl) (pan_dec_clock s)) = R,st *)
let PPASS1AUX_IS_CALLEE_RUN (th:thm) =
  try let l = lhs(concl th) in
      fst(dest_const(fst(strip_comb l))) = "pan_evaluate" &&
      (let st0 = snd(dest_pair(rand l)) in
       fst(dest_const(fst(strip_comb st0))) = "pan_state_locals_fupd" &&
       rand st0 = `pan_dec_clock (s:(A,FFI)pan_state)`)
  with Failure _ -> false;;

(* the induction hypothesis "ihm" at the callee run, with the invariants  *)
(* of that run                                                             *)
let PPASS1AUX_CALL_IH_TAC : tactic = fun (asl,w as g) ->
  let fn,args,prog,nl,rsh = PPASS1AUX_CALL_LOOKUP asl in
  let run = snd(find (fun (_,th) -> PPASS1AUX_IS_CALLEE_RUN th) asl) in
  let l,r = dest_eq(concl run) in
  let st0 = snd(dest_pair(rand l)) in
  let rr,st = dest_pair r in
  (REMOVE_THEN "ihm" (MP_TAC o SPECL [args; rsh; prog; nl]) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o SPECL [rr; st; `pan_structs_context_locals_fupd (K new_l) ctxt`]) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN SIMP[pan_dec_clock_def] THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[distinctness "option"; distinctness "pan_result"];
     ALL_TAC] THEN
   REWRITE_TAC[PPASS1AUX_convert_s_locals_upd] THEN SIMP[] THEN STRIP_TAC THEN
   MP_TAC(ISPECL [prog; st0; rr; st] evaluate_is_wf_shape_invariant) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMP[pan_dec_clock_def] THEN ASM_REWRITE_TAC[];
                   SIMP[pan_dec_clock_def] THEN STRIP_TAC] THEN
   MP_TAC(REWRITE_RULE[pan_dec_clock_def; PPASS1AUX_pan_state_accfupds; K_THM]
                      (MATCH_MP evaluate_structs_code_inv run)) THEN
   DISCH_THEN(CONJUNCTS_THEN2 (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) ASSUME_TAC)) g;;

let PPASS1AUX_CALL_TGT2_TAC : tactic =
  PPASS1AUX_CALL_TGT_TAC THEN REWRITE_TAC[PPASS1AUX_convert_s_callee] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[convert_res_def];;

(* the shape of the converted value of the callee's result Return r / Exception e r *)
let PPASS1AUX_CALL_RESV_TAC : tactic = fun (asl,w as g) ->
  let run = snd(find (fun (_,th) -> PPASS1AUX_IS_CALLEE_RUN th) asl) in
  let rr = fst(dest_pair(rand(concl run))) in
  let r = rand(rand rr) in
  (TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
     try is_var(rhs(concl th)) && fst(dest_const(rator(lhs(concl th)))) = "shape_of"
     with Failure _ -> false))) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[res_vs_def; ALL]) THEN
   MP_TAC(ISPEC r (INST [`pan_state_structs (s:(A,FFI)pan_state)`,
                         `ctxt:(mlstring#struct_info)list`] shape_of_convert_v_rev)) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC) g;;

let PPASS1AUX_CC_CALLR_TAC : tactic =
  PPASS1AUX_CALL_LOOKUP_TAC THEN PPASS1AUX_CALL_IH_TAC THEN PPASS1AUX_CALL_TGT2_TAC THEN
  PPASS1AUX_CALL_RESV_TAC THEN ASM_REWRITE_TAC[] THEN PPASS1AUX_CC_FIN_TAC;;

(* the assignment of the returned value v to rk rt, after the call:       *)
(* the looked-up w, its facts, the shapes of the converted values         *)
let PPASS1AUX_CALL_ASG_KIND_TAC (fld:term) (rt:term) (v:term) : tactic =
  let lk = mk_comb(mk_comb(`FLOOKUP:(mlstring,(A)pan_v)fmap->mlstring->((A)pan_v)option`,
                           mk_comb(fld,`s:(A,FFI)pan_state`)), rt) in
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[])
    (X_CHOOSE_THEN `w:(A)pan_v` (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))
    (ISPEC lk (cases "option")) THEN
  CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `v_flds_ok (pan_state_structs (s:(A,FFI)pan_state)) (w:(A)pan_v) /\
                is_wf_shape_v (pan_state_structs s) w` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`v_flds_ok (pan_state_structs (s:(A,FFI)pan_state)):(A)pan_v->bool`;
                           mk_comb(fld,`s:(A,FFI)pan_state`); rt; `w:(A)pan_v`]
                          PPASS1AUX_FEVERY_VAL);
      MATCH_MP_TAC(ISPECL [`is_wf_shape_v (pan_state_structs (s:(A,FFI)pan_state)):(A)pan_v->bool`;
                           mk_comb(fld,`s:(A,FFI)pan_state`); rt; `w:(A)pan_v`]
                          PPASS1AUX_FEVERY_VAL)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `w:(A)pan_v`
    (INST [`pan_state_structs (s:(A,FFI)pan_state)`,`ctxt:(mlstring#struct_info)list`]
          shape_of_convert_v_rev)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let PPASS1AUX_CALL_ASG_TAC : tactic = fun (asl,w as g) ->
  let iv = snd(find (fun (_,th) ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "pan_is_valid_value" &&
        el 0 (snd(strip_comb(concl th))) = `s:(A,FFI)pan_state`
    with Failure _ -> false) asl) in
  let args = snd(strip_comb(concl iv)) in
  let rk = el 1 args and rt = el 2 args and v = el 3 args in
  (UNDISCH_TAC (concl iv) THEN REWRITE_TAC[pan_is_valid_value_def] THEN
   STRUCT_CASES_TAC (ISPEC rk (cases "varkind")) THEN REWRITE_TAC[kvar_simps] THENL
    [PPASS1AUX_CALL_ASG_KIND_TAC `pan_state_locals:(A,FFI)pan_state->(mlstring,(A)pan_v)fmap` rt v;
     PPASS1AUX_CALL_ASG_KIND_TAC `pan_state_globals:(A,FFI)pan_state->(mlstring,(A)pan_v)fmap` rt v]) g;;

(* FLOOKUP of the shapes of the globals after the call, from those before *)
let PPASS1AUX_GLOBALS_SHAPE_TAC : tactic =
  FIRST_ASSUM(fun eq ->
    let l,r = dest_eq(concl eq) in
    if (try fst(dest_const(fst(strip_comb l))) = "FMAP_MAP2" &&
            rand l = `pan_state_globals (s:(A,FFI)pan_state)` with Failure _ -> false)
    then MP_TAC(AP_TERM `FLOOKUP:(mlstring,shape)fmap->mlstring->(shape)option` eq)
    else NO_TAC) THEN
  REWRITE_TAC[FUN_EQ_THM; FLOOKUP_FMAP_MAP2; o_THM; SND] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF];;

let PPASS1AUX_convert_s_set_var = prove
 (CASE_TERM
  `pan_set_var x (convert_v (v:(A)pan_v))
     (pan_state_locals_fupd (K (pan_state_locals (convert_s ctxt (s:(A,FFI)pan_state))))
        (convert_s ctxt (st:(A,FFI)pan_state))) =
   convert_s ctxt (pan_set_var x v (pan_state_locals_fupd (K (pan_state_locals s)) st))`,
  SIMP[convert_s_def; pan_set_var_def; FMAP_MAP2_FUPDATE; pan_state_component_equality] THEN
  CASE_REWRITE_TAC[]);;

(* the handler: the induction hypothesis "ihh" at the handler run *)
let PPASS1AUX_CALL_HANDLER_IH_TAC : tactic = fun (asl,w as g) ->
  let fn,args,prog,nl,rsh = PPASS1AUX_CALL_LOOKUP asl in
  let run = snd(find (fun (_,th) -> PPASS1AUX_IS_CALLEE_RUN th) asl) in
  let rr,st = dest_pair(rand(concl run)) in
  let exn = rand(rand rr) in
  let ihh = assoc "ihh" asl in
  let vs,body = strip_forall(concl ihh) in
  let guard = fst(dest_imp body) in
  let ceq = find (fun t ->
    try let l,r = dest_eq t in fst(dest_pair(rand r)) = el 4 vs with Failure _ -> false)
    (conjuncts guard) in
  let cl = rand(lhs ceq) in
  let xx,h = dest_pair cl in
  let ee,vp = dest_pair(rand h) in
  let vv,pp = dest_pair vp in
  (REMOVE_THEN "ihh" (MP_TAC o SPECL [args; rsh; prog; nl; xx; ee; pp; vv; exn; st]) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `s':(A,FFI)pan_state`;
                              `ctxt:pan_structs_context`]) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     SIMP[pan_set_var_def; FEVERY_FUPDATE; FMAP_MAP2_FUPDATE; o_THM] THEN
     ASM_SIMP_TAC[fevery_to_drestrict] THEN CASE_REWRITE_TAC[] THEN
     TRY(CONV_TAC SYM_CONV THEN MATCH_MP_TAC fupdate_elim2 THEN
         ASM_REWRITE_TAC[FLOOKUP_FMAP_MAP2; OPTION_MAP_DEF; o_THM]);
     ALL_TAC] THEN
   SIMP[] THEN STRIP_TAC) g;;

let PPASS1AUX_convert_s_fields = prove
 (CASE_TERM
  `pan_state_locals (convert_s ctxt (s:(A,FFI)pan_state)) =
     FMAP_MAP2 (\p. match p with (nm,v) -> convert_v v) (pan_state_locals s) /\
   pan_state_globals (convert_s ctxt s) =
     FMAP_MAP2 (\p. match p with (nm,v) -> convert_v v) (pan_state_globals s) /\
   pan_state_eshapes (convert_s ctxt s) =
     convert_eshapes (pan_structs_context_structs ctxt) (pan_state_eshapes s)`,
  SIMP[convert_s_def]);;

let PPASS1AUX_DCALL_TGT_TAC : tactic =
  REWRITE_TAC[pan_structs_compile_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [pan_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[PPASS1AUX_convert_s_clock; PPASS1AUX_convert_s_callee;
                  LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[];;

let PPASS1AUX_DCALL_TGT2_TAC : tactic =
  PPASS1AUX_DCALL_TGT_TAC THEN REWRITE_TAC[PPASS1AUX_convert_s_callee] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[convert_res_def];;

(* DecCall: the induction hypothesis "ihd" of the continuation prog1 *)
let PPASS1AUX_DCALL_IH2_TAC : tactic = fun (asl,w as g) ->
  let fn,args,prog,nl,rsh = PPASS1AUX_CALL_LOOKUP asl in
  let run = snd(find (fun (_,th) -> PPASS1AUX_IS_CALLEE_RUN th) asl) in
  let rr,st = dest_pair(rand(concl run)) in
  let retv = rand(rand rr) in
  let crun = snd(find (fun (_,th) ->
    try let l = lhs(concl th) in
        fst(dest_const(fst(strip_comb l))) = "pan_evaluate" &&
        fst(dest_const(fst(strip_comb(snd(dest_pair(rand l)))))) = "pan_set_var"
    with Failure _ -> false) asl) in
  let rr2,st2 = dest_pair(rand(concl crun)) in
  let ctxt1 = mk_comb(mk_comb(`pan_structs_context_locals_fupd`,
     mk_comb(`K:(mlstring#shape)list->(mlstring#shape)list->(mlstring#shape)list`,
       mk_comb(mk_comb(`CONS:mlstring#shape->(mlstring#shape)list->(mlstring#shape)list`,
                       mk_pair(`rt:mlstring`,mk_comb(`shape_of:(A)pan_v->shape`,retv))),
               `pan_structs_context_locals ctxt`))), `ctxt:pan_structs_context`) in
  (REMOVE_THEN "ihd" (MP_TAC o SPECL [args; prog; nl; retv; st]) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o SPECL [rr2; st2; ctxt1]) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     SIMP[pan_set_var_def; FEVERY_FUPDATE; FMAP_MAP2_FUPDATE; o_THM; alist_to_fmap_thm] THEN
     ASM_SIMP_TAC[fevery_to_drestrict] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[PPASS1AUX_convert_s_locals_upd] THEN SIMP[alist_to_fmap_thm] THEN STRIP_TAC) g;;

(* HOL4: compile_correct *)

let pan_structsProof_compile_correct = prove
 (CASE_TERM
  `!p (s:(A,FFI)pan_state) res s' ctxt.
     pan_evaluate (p,s) = (res,s') /\
     pan_structs_context_structs ctxt =
       MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info))
           (pan_state_structs s) /\
     FEVERY (\p. match p with (nm,v) -> v_flds_ok (pan_state_structs s) v)
            (pan_state_locals s) /\
     FEVERY (\p. match p with (nm,v) -> v_flds_ok (pan_state_structs s) v)
            (pan_state_globals s) /\
     FEVERY (\p. match p with (nm,v) -> is_wf_shape_v (pan_state_structs s) v)
            (pan_state_locals s) /\
     FEVERY (\p. match p with (nm,v) -> is_wf_shape_v (pan_state_structs s) v)
            (pan_state_globals s) /\
     struct_infos_ok (pan_state_structs s) /\
     alist_to_fmap (pan_structs_context_locals ctxt) =
       FMAP_MAP2 (shape_of o SND) (pan_state_locals s) /\
     alist_to_fmap (pan_structs_context_globals ctxt) =
       FMAP_MAP2 (shape_of o SND) (pan_state_globals s) /\
     ~(res = SOME pan_Error)
     ==>
     pan_evaluate (pan_structs_compile ctxt p,convert_s ctxt s) =
       (convert_res res,convert_s ctxt s') /\
     FEVERY (\p. match p with (nm,v) -> v_flds_ok (pan_state_structs s') v)
            (pan_state_locals s') /\
     FEVERY (\p. match p with (nm,v) -> v_flds_ok (pan_state_structs s') v)
            (pan_state_globals s') /\
     alist_to_fmap (pan_structs_context_globals ctxt) =
       FMAP_MAP2 (shape_of o SND) (pan_state_globals s') /\
     (is_cont_res res ==>
      alist_to_fmap (pan_structs_context_locals ctxt) =
        FMAP_MAP2 (shape_of o SND) (pan_state_locals s')) /\
     ALL (v_flds_ok (pan_state_structs s')) (res_vs res) /\
     ALL (is_wf_shape_v (pan_state_structs s')) (res_vs res)`,
  REC_IND_TAC pan_evaluate_ind THEN REPEAT CONJ_TAC THENL
   [(* Skip *)
    (REPEAT GEN_TAC THEN STRIP_TAC THEN
   FS[pan_evaluate_def; pan_structs_compile_def] THEN RVEQ_TAC THEN
   SIMP[convert_res_def; is_cont_res_def; res_vs_def; ALL; pan_evaluate_def] THEN
   ASM_REWRITE_TAC[]);
    (* Dec *)
    ((REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   UNDISCH_TAC `pan_evaluate (Dec v sh e prog,s:(A,FFI)pan_state) = res,s'` THEN
   GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [pan_evaluate_def] THEN
   QCASES_ON "pan_eval (s:(A,FFI)pan_state) e" THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
   TRY(DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
   RENAME1 "pan_eval s e = SOME value" THEN
   COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
    [ALL_TAC; DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]] THEN
   PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `res':((A)pan_result)option = res`)) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `s':(A,FFI)pan_state`)) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `value:(A)pan_v`) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) THEN
    (SUBGOAL_THEN
     `old_exp_shape ctxt e = shape_of (value:(A)pan_v) /\
      v_flds_ok (pan_state_structs (s:(A,FFI)pan_state)) value /\
      pan_eval (convert_s ctxt s) (pan_structs_compile_exp ctxt e) = SOME (convert_v value)`
     STRIP_ASSUME_TAC THENL
    [MP_TAC(ISPECL [`s:(A,FFI)pan_state`; `e:(A)panLang_exp`; `value:(A)pan_v`]
       pan_structsProof_compile_exp_correct) THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `is_wf_shape_v (pan_state_structs (s:(A,FFI)pan_state)) (value:(A)pan_v)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC eval_is_wf_shape_v THEN EXISTS_TAC `e:(A)panLang_exp` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP evaluate_structs_code_inv o
     check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "pan_evaluate"
                      with Failure _ -> false)) THEN
   FIRST_X_ASSUM(MP_TAC o SPECL
     [`res:((A)pan_result)option`; `st:(A,FFI)pan_state`;
      `pan_structs_context_locals_fupd
         (K (CONS (v,shape_of (value:(A)pan_v)) (pan_structs_context_locals ctxt))) ctxt`])) THEN
    (ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
     SIMP[FEVERY_FUPDATE; alist_to_fmap_thm; FMAP_MAP2_FUPDATE; o_THM] THEN
     ASM_SIMP_TAC[fevery_to_drestrict] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
     NO_TAC;
     STRIP_TAC]) THEN
    (FS[alist_to_fmap_thm]) THEN
    (SUBGOAL_THEN
     `pan_state_locals_fupd
        (K (pan_state_locals (convert_s ctxt (s:(A,FFI)pan_state)) |+ (v,convert_v value)))
        (convert_s ctxt s) =
      convert_s (pan_structs_context_locals_fupd
                   (K (CONS (v,shape_of (value:(A)pan_v)) (pan_structs_context_locals ctxt)))
                   ctxt)
                (pan_state_locals_fupd (K (pan_state_locals s |+ (v,value))) s)`
     ASSUME_TAC THENL
    [SIMP[convert_s_def; FMAP_MAP2_FUPDATE; pan_state_component_equality] THEN
     CASE_REWRITE_TAC[];
     ALL_TAC]) THEN
    (CONJ_TAC THENL
    [REWRITE_TAC[pan_structs_compile_def] THEN
     GEN_REWRITE_TAC LAND_CONV [pan_evaluate_def] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
     SUBGOAL_THEN (CASE_TERM
                   `shape_of (convert_v (value:(A)pan_v)) =
                    compile_shape
                      (MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info))
                           (pan_state_structs (s:(A,FFI)pan_state)))
                      (shape_of value)`) (fun th -> REWRITE_TAC[th]) THENL
      [MATCH_MP_TAC shape_of_convert_v_rev THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN
     SIMP[convert_s_def; res_var_FMAP_MAP2_rev; FLOOKUP_FMAP_MAP2; pan_state_component_equality];
     ALL_TAC] THEN
   CONJ_TAC THENL
    [REWRITE_TAC[FEVERY_res_var] THEN CONJ_TAC THENL
      [MATCH_MP_TAC fevery_to_drestrict THEN ASM_REWRITE_TAC[];
       X_GEN_TAC `w:(A)pan_v` THEN DISCH_TAC THEN
       MP_TAC(ISPECL [CASE_TERM `\p:mlstring#(A)pan_v. match p with
                                       (nm,v) -> v_flds_ok (pan_state_structs (s:(A,FFI)pan_state)) v`;
                      `pan_state_locals (s:(A,FFI)pan_state)`; `v:mlstring`; `w:(A)pan_v`]
                     FEVERY_FLOOKUP) THEN
       ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]];
     DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FMAP_MAP2; FLOOKUP_pan_res_var_thm; FLOOKUP_UPDATE] THEN
     DISCH_TAC THEN X_GEN_TAC `k:mlstring` THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `k:mlstring`) THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
     REWRITE_TAC[]]));
    (* Assign *)
    ((REPEAT GEN_TAC THEN STRIP_TAC THEN
   UNDISCH_TAC `pan_evaluate (panLang_Assign vk v src,s:(A,FFI)pan_state) = res,s'` THEN
   GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [pan_evaluate_def] THEN
   QCASES_ON "pan_eval (s:(A,FFI)pan_state) src" THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
   TRY(DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
   RENAME1 "pan_eval s src = SOME value" THEN
   COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
    [ALL_TAC; DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]] THEN
   DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   SUBGOAL_THEN
     `old_exp_shape ctxt src = shape_of (value:(A)pan_v) /\
      v_flds_ok (pan_state_structs (s:(A,FFI)pan_state)) value /\
      pan_eval (convert_s ctxt s) (pan_structs_compile_exp ctxt src) = SOME (convert_v value)`
     STRIP_ASSUME_TAC THENL
    [MP_TAC(ISPECL [`s:(A,FFI)pan_state`; `src:(A)panLang_exp`; `value:(A)pan_v`]
       pan_structsProof_compile_exp_correct) THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `is_wf_shape_v (pan_state_structs (s:(A,FFI)pan_state)) (value:(A)pan_v)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC eval_is_wf_shape_v THEN EXISTS_TAC `src:(A)panLang_exp` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   UNDISCH_TAC `pan_is_valid_value (s:(A,FFI)pan_state) vk v value` THEN
   REWRITE_TAC[pan_is_valid_value_def] THEN
   QCASES_ON "vk:varkind" THEN REWRITE_TAC[kvar_simps] THENL
    [QCASES_ON "FLOOKUP (pan_state_locals (s:(A,FFI)pan_state)) v";
     QCASES_ON "FLOOKUP (pan_state_globals (s:(A,FFI)pan_state)) v"] THEN
   CASE_REWRITE_TAC[] THEN DISCH_TAC THEN RENAME1 "SOME w") THENL
    [PPASS1AUX_ASG_CLOSE_TAC `pan_state_locals:(A,FFI)pan_state->(mlstring,(A)pan_v)fmap`;
     PPASS1AUX_ASG_CLOSE_TAC `pan_state_globals:(A,FFI)pan_state->(mlstring,(A)pan_v)fmap`]);
    (* Primitive *)
    ((REPEAT GEN_TAC THEN STRIP_TAC THEN
   UNDISCH_TAC `pan_evaluate (Primitive v pop es,s:(A,FFI)pan_state) = res,s'` THEN
   GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [pan_evaluate_def] THEN
   QCASES_ON "OPT_MMAP (pan_eval (s:(A,FFI)pan_state)) es" THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
   TRY(DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
   RENAME1 "OPT_MMAP (pan_eval s) es = SOME vs" THEN
   QCASES_ON "pan_primop pop (vs:((A)pan_v)list)" THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
   TRY(DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
   RENAME1 "pan_primop pop vs = SOME value" THEN
   COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
    [ALL_TAC; DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]] THEN
   DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   SUBGOAL_THEN
     `OPT_MMAP (pan_eval (convert_s ctxt (s:(A,FFI)pan_state)))
               (pan_structs_compile_exps ctxt es) = SOME (MAP convert_v vs)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC compile_exp_correct_mmap_helper THEN ASM_REWRITE_TAC[] THEN
     REPEAT STRIP_TAC THEN
     MP_TAC(ISPECL [`s:(A,FFI)pan_state`; `e:(A)panLang_exp`; `v':(A)pan_v`]
       pan_structsProof_compile_exp_correct) THEN
     ASM_REWRITE_TAC[] THEN SIMP_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN
     `MAP convert_v vs = (vs:((A)pan_v)list) /\ convert_v value = (value:(A)pan_v) /\
      compile_shape (pan_structs_context_structs ctxt) (shape_of value) = shape_of value /\
      v_flds_ok (pan_state_structs (s:(A,FFI)pan_state)) value`
     STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `pan_primop pop (vs:((A)pan_v)list) = SOME value` THEN
     QCASES_ON "pop:primop" THEN REWRITE_TAC[pan_primop_def] THEN
     COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
     REWRITE_TAC[LET_DEF; LET_END_DEF; pair_CASE_def; injectivity "option"] THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN
     REWRITE_TAC[convert_v_def; MAP; shape_of_def; compile_shape_def; v_flds_ok_def; ALL] THEN
     MATCH_MP_TAC every_convert_v_eq THEN
     UNDISCH_TAC `LENGTH (vs:((A)pan_v)list) = 3 /\ ALL isValWord vs` THEN
     DISCH_THEN(MP_TAC o CONJUNCT2) THEN MATCH_MP_TAC MONO_ALL THEN
     X_GEN_TAC `w:(A)pan_v` THEN QCASES_ON "w:(A)pan_v" THEN
     REWRITE_TAC[isValWord_def] THEN CASE_REWRITE_TAC[];
     ALL_TAC]) THEN
    (UNDISCH_TAC `pan_is_valid_value (s:(A,FFI)pan_state) panLang_Local v value` THEN
   REWRITE_TAC[pan_is_valid_value_def; kvar_simps] THEN
   QCASES_ON "FLOOKUP (pan_state_locals (s:(A,FFI)pan_state)) v" THEN
   CASE_REWRITE_TAC[] THEN DISCH_TAC THEN RENAME1 "SOME w" THEN
   SUBGOAL_THEN `v_flds_ok (pan_state_structs (s:(A,FFI)pan_state)) (w:(A)pan_v) /\
                 is_wf_shape_v (pan_state_structs s) w` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
      [MATCH_MP_TAC(ISPECL [`v_flds_ok (pan_state_structs (s:(A,FFI)pan_state)):(A)pan_v->bool`;
                            `pan_state_locals (s:(A,FFI)pan_state)`; `v:mlstring`; `w:(A)pan_v`]
                           PPASS1AUX_FEVERY_VAL);
       MATCH_MP_TAC(ISPECL [`is_wf_shape_v (pan_state_structs (s:(A,FFI)pan_state)):(A)pan_v->bool`;
                            `pan_state_locals (s:(A,FFI)pan_state)`; `v:mlstring`; `w:(A)pan_v`]
                           PPASS1AUX_FEVERY_VAL)] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `shape_of (convert_v (w:(A)pan_v)) = shape_of (value:(A)pan_v)` ASSUME_TAC THENL
    [MP_TAC(ISPEC `w:(A)pan_v`
       (INST [`pan_state_structs (s:(A,FFI)pan_state)`,`ctxt:(mlstring#struct_info)list`]
             shape_of_convert_v_rev)) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
     FIRST_X_ASSUM(fun th -> if concl th = `shape_of (value:(A)pan_v) = shape_of (w:(A)pan_v)`
                            then SUBST1_TAC(SYM th) else NO_TAC) THEN
     FIRST_X_ASSUM(fun th -> MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE
     (UNDISCH_TAC `compile_shape (pan_structs_context_structs ctxt) (shape_of (value:(A)pan_v)) =
                   shape_of value` THEN ASM_REWRITE_TAC[]);
     ALL_TAC] THEN
   REWRITE_TAC[pan_structs_compile_def; pan_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
   CASE_REWRITE_TAC[pan_is_valid_value_def; kvar_simps] THEN
   SIMP[convert_s_def; FLOOKUP_FMAP_MAP2; pan_set_var_def;
        FMAP_MAP2_FUPDATE; FEVERY_FUPDATE; convert_res_def; is_cont_res_def; res_vs_def;
        ALL; o_THM] THEN
   ASM_SIMP_TAC[fevery_to_drestrict; fupdate_elim2; FLOOKUP_FMAP_MAP2; o_THM] THEN
   CASE_REWRITE_TAC[] THEN
   TRY(CONV_TAC SYM_CONV THEN MATCH_MP_TAC fupdate_elim2 THEN
       ASM_REWRITE_TAC[FLOOKUP_FMAP_MAP2; OPTION_MAP_DEF; o_THM])));
    (* Store *)
    (PPASS1AUX_CC_SIMPLE_TAC);
    (* Store32 *)
    (PPASS1AUX_CC_SIMPLE_TAC);
    (* StoreByte *)
    (PPASS1AUX_CC_SIMPLE_TAC);
    (* ShMemLoad *)
    (PPASS1AUX_CC_SRC2_TAC [pan_sh_mem_load_def; pan_lookup_kvar_def; LET_DEF; LET_END_DEF] THEN
    PPASS1AUX_CC_SHL_TAC);
    (* ShMemStore *)
    (PPASS1AUX_CC_SRC2_TAC [pan_sh_mem_store_def; LET_DEF; LET_END_DEF] THEN
    PPASS1AUX_CC_SHS_TAC);
    (* Seq *)
    (REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih2") (LABEL_TAC "ih1")) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   MP_TAC(ISPEC `pan_evaluate (c1,s:(A,FFI)pan_state)` PAIR_SURJECTIVE) THEN
   REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
   MAP_EVERY X_GEN_TAC [`res1:((A)pan_result)option`; `s1:(A,FFI)pan_state`] THEN
   DISCH_TAC THEN
   UNDISCH_TAC `pan_evaluate (panLang_Seq c1 c2,s:(A,FFI)pan_state) = res,s'` THEN
   GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [pan_evaluate_def] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN `~(res1 = SOME (pan_Error:(A)pan_result))` ASSUME_TAC THENL
    [DISCH_TAC THEN UNDISCH_TAC `(if res1 = NONE then pan_evaluate (c2,s1)
                                  else res1,s1) = res,(s':(A,FFI)pan_state)` THEN
     ASM_REWRITE_TAC[distinctness "option"; PAIR_EQ] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   REMOVE_THEN "ih1" (MP_TAC o SPECL [`res1:((A)pan_result)option`; `s1:(A,FFI)pan_state`;
                                       `ctxt:pan_structs_context`]) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP evaluate_structs_code_inv o
     check (fun th -> concl th = `pan_evaluate (c1,s:(A,FFI)pan_state) = res1,s1`)) THEN
   MP_TAC(ISPECL [`c1:(A)panLang_prog`; `s:(A,FFI)pan_state`; `res1:((A)pan_result)option`;
                  `s1:(A,FFI)pan_state`] evaluate_is_wf_shape_invariant) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   REWRITE_TAC[pan_structs_compile_def] THEN
   GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [pan_evaluate_def] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[convert_res_eq_NONE] THEN
   ASM_CASES_TAC `res1:((A)pan_result)option = NONE` THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
     REMOVE_THEN "ih2" (MP_TAC o SPEC `s1:(A,FFI)pan_state`) THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `s':(A,FFI)pan_state`;
                                `ctxt:pan_structs_context`]) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[is_cont_res_def]) THEN
     ASM_REWRITE_TAC[];
     (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(lhs(concl th))) o
     check (fun th -> try is_eq(concl th) with Failure _ -> false)) THEN
   ASM_REWRITE_TAC[PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[])]);
    (* If *)
    (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    PPASS1AUX_CC_SRC3_TAC [] THEN PPASS1AUX_CC_IF_TAC);
    (* Break *)
    (PPASS1AUX_CC_SIMPLE_TAC);
    (* Continue *)
    (PPASS1AUX_CC_SIMPLE_TAC);
    (* While *)
    ((REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihw") (CONJUNCTS_THEN2 (LABEL_TAC "ihc")
     (LABEL_TAC "ihb"))) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   PPASS1AUX_CC_SRC3_TAC []) THENL
    [PPASS1AUX_CC_EXPS_TAC THEN PPASS1AUX_CC_WTGT_TAC THEN PPASS1AUX_CC_FIN_TAC;
     PPASS1AUX_CC_WLOOP_TAC "ihw"; PPASS1AUX_CC_WSTOP_TAC; PPASS1AUX_CC_WSTOP_TAC;
     PPASS1AUX_CC_WLOOP_TAC "ihc"; PPASS1AUX_CC_WSTOP_TAC; PPASS1AUX_CC_WSTOP_TAC;
     PPASS1AUX_CC_WSTOP_TAC;
     PPASS1AUX_CC_EXPS_TAC THEN PPASS1AUX_CC_WTGT_TAC THEN PPASS1AUX_CC_FIN_TAC]);
    (* Return *)
    (PPASS1AUX_CC_SRC_TAC THEN PPASS1AUX_CC_EXPS_TAC THEN PPASS1AUX_CC_SIZE_TAC THEN
   REWRITE_TAC[pan_structs_compile_def; pan_evaluate_def] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN SIMP[convert_s_def] THEN ASM_REWRITE_TAC[] THEN
   PPASS1AUX_CC_FIN_TAC);
    (* Raise *)
    ((PPASS1AUX_CC_SRC_TAC THEN PPASS1AUX_CC_EXPS_TAC THEN PPASS1AUX_CC_SIZE_TAC THEN
   REWRITE_TAC[pan_structs_compile_def; pan_evaluate_def] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   SIMP[convert_s_def; convert_eshapes_def; FLOOKUP_FMAP_MAP2] THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
   CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
   PPASS1AUX_CC_FIN_TAC) THEN
    (FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try
     fst(dest_const(rator(lhs(concl th)))) = "shape_of" && is_var(rhs(concl th))
     with Failure _ -> false)) THEN
   ASM_REWRITE_TAC[] THEN PPASS1AUX_CC_FIN_TAC));
    (* Tick *)
    (PPASS1AUX_CC_SRC_TAC THEN
   REWRITE_TAC[pan_structs_compile_def; pan_evaluate_def] THEN
   ASM_REWRITE_TAC[PPASS1AUX_convert_s_clock; PPASS1AUX_convert_s_dec_clock] THEN
   SIMP[pan_dec_clock_def] THEN PPASS1AUX_CC_FIN_TAC);
    (* Annot *)
    (PPASS1AUX_CC_SIMPLE_TAC);
    (* Call *)
    ((REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihm") (LABEL_TAC "ihh")) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   PPASS1AUX_CC_SRC3_TAC [LET_DEF; LET_END_DEF]) THENL
    [PPASS1AUX_CALL_LOOKUP_TAC THEN PPASS1AUX_CALL_TGT_TAC THEN PPASS1AUX_CC_FIN_TAC;
     PPASS1AUX_CALL_LOOKUP_TAC THEN PPASS1AUX_CALL_IH_TAC THEN PPASS1AUX_CALL_TGT2_TAC THEN PPASS1AUX_CC_FIN_TAC;
     PPASS1AUX_CC_CALLR_TAC;
     PPASS1AUX_CC_CALLR_TAC;
     PPASS1AUX_CALL_LOOKUP_TAC THEN PPASS1AUX_CALL_IH_TAC THEN PPASS1AUX_CALL_TGT2_TAC THEN
   PPASS1AUX_CALL_RESV_TAC THEN ASM_REWRITE_TAC[] THEN PPASS1AUX_CALL_ASG_TAC THEN
   SIMP[convert_s_def; FLOOKUP_FMAP_MAP2] THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
   CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
     PPASS1AUX_CC_FIN_TAC THEN TRY PPASS1AUX_GLOBALS_SHAPE_TAC;
     PPASS1AUX_CC_CALLR_TAC;
     PPASS1AUX_CC_CALLR_TAC;
     (PPASS1AUX_CALL_LOOKUP_TAC THEN PPASS1AUX_CALL_IH_TAC THEN PPASS1AUX_CALL_TGT2_TAC THEN
   REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
   PPASS1AUX_CALL_RESV_TAC THEN
   UNDISCH_TAC `pan_is_valid_value (s:(A,FFI)pan_state) panLang_Local x''''' a1` THEN
   DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
   REWRITE_TAC[pan_is_valid_value_def; kvar_simps] THEN
   PPASS1AUX_CALL_ASG_KIND_TAC `pan_state_locals:(A,FFI)pan_state->(mlstring,(A)pan_v)fmap`
     `x''''':mlstring` `a1:(A)pan_v` THEN
   PPASS1AUX_CALL_HANDLER_IH_TAC) THEN
     (REWRITE_TAC[PPASS1AUX_convert_s_set_var] THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[PPASS1AUX_convert_s_fields; convert_eshapes_def; FLOOKUP_FMAP_MAP2] THEN
   ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);
     PPASS1AUX_CC_CALLR_TAC;
     PPASS1AUX_CALL_LOOKUP_TAC THEN PPASS1AUX_CALL_IH_TAC THEN PPASS1AUX_CALL_TGT2_TAC THEN PPASS1AUX_CC_FIN_TAC]);
    (* DecCall *)
    ((REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihm") (LABEL_TAC "ihd")) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   PPASS1AUX_CC_SRC3_TAC [LET_DEF; LET_END_DEF]) THENL
    [PPASS1AUX_CALL_LOOKUP_TAC THEN PPASS1AUX_DCALL_TGT_TAC THEN PPASS1AUX_CC_FIN_TAC;
     PPASS1AUX_CALL_LOOKUP_TAC THEN PPASS1AUX_CALL_IH_TAC THEN PPASS1AUX_DCALL_TGT2_TAC THEN PPASS1AUX_CC_FIN_TAC;
     (PPASS1AUX_CALL_LOOKUP_TAC THEN PPASS1AUX_CALL_IH_TAC THEN PPASS1AUX_DCALL_TGT2_TAC THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try is_var(lhs(concl th)) &&
     rhs(concl th) = `shape:shape` with Failure _ -> false)) THEN
   PPASS1AUX_CALL_RESV_TAC THEN ASM_REWRITE_TAC[]) THEN
     (REWRITE_TAC[PPASS1AUX_convert_s_set_var] THEN PPASS1AUX_DCALL_IH2_TAC THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THEN
     (FIRST_ASSUM(fun th ->
     if (try let l = lhs(concl th) in
             fst(dest_const(fst(strip_comb l))) = "pan_evaluate" &&
             fst(dest_const(fst(strip_comb(snd(dest_pair(rand l)))))) = "pan_set_var"
         with Failure _ -> false)
     then MP_TAC(REWRITE_RULE[pan_set_var_def; PPASS1AUX_pan_state_accfupds; K_THM]
                   (MATCH_MP evaluate_structs_code_inv th))
     else NO_TAC) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   CONJ_TAC THENL
    [SIMP[convert_s_def; res_var_FMAP_MAP2_rev; FLOOKUP_FMAP_MAP2; pan_state_component_equality];
     ALL_TAC] THEN
   CONJ_TAC THENL
    [REWRITE_TAC[FEVERY_res_var] THEN CONJ_TAC THENL
      [MATCH_MP_TAC fevery_to_drestrict THEN ASM_REWRITE_TAC[];
       X_GEN_TAC `w:(A)pan_v` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
       MP_TAC(ISPECL [CASE_TERM `\p:mlstring#(A)pan_v. match p with
                                   (nm,v) -> v_flds_ok (pan_state_structs (s:(A,FFI)pan_state)) v`;
                      `pan_state_locals (s:(A,FFI)pan_state)`; `rt:mlstring`; `w:(A)pan_v`]
                     FEVERY_FLOOKUP) THEN
       ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]];
     DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> try is_imp(concl th) &&
       fst(dest_const(fst(strip_comb(lhand(concl th))))) = "is_cont_res"
       with Failure _ -> false)) THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FMAP_MAP2; FLOOKUP_pan_res_var_thm; FLOOKUP_UPDATE] THEN
     DISCH_TAC THEN X_GEN_TAC `k:mlstring` THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `k:mlstring`) THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
     REWRITE_TAC[]]);
     PPASS1AUX_CALL_LOOKUP_TAC THEN PPASS1AUX_CALL_IH_TAC THEN PPASS1AUX_DCALL_TGT2_TAC THEN PPASS1AUX_CALL_RESV_TAC THEN ASM_REWRITE_TAC[] THEN PPASS1AUX_CC_FIN_TAC;
     PPASS1AUX_CALL_LOOKUP_TAC THEN PPASS1AUX_CALL_IH_TAC THEN PPASS1AUX_DCALL_TGT2_TAC THEN PPASS1AUX_CC_FIN_TAC]);
    (* ExtCall *)
    (PPASS1AUX_CC_SRC2_TAC [LET_DEF; LET_END_DEF] THEN PPASS1AUX_CC_EXPS_TAC THEN
   REWRITE_TAC[pan_structs_compile_def; pan_evaluate_def] THEN
   ASM_REWRITE_TAC[convert_v_def] THEN CASE_REWRITE_TAC[] THEN
   SIMP[convert_s_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   PPASS1AUX_CC_FIN_TAC)]);;

let compile_decs_structs = prove
 (`!ctxt (decs:((A)decl)list) decs' ctxt'.
     pan_structs_compile_decs ctxt decs = (decs',ctxt') ==>
     pan_structs_context_structs ctxt' = pan_structs_context_structs ctxt`,
  MATCH_MP_TAC pan_structs_compile_decs_ind THEN
  REWRITE_TAC[pan_structs_compile_decs_def] THEN RW[] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN RES_TAC THEN FS[]);;

let compile_decls_correct = prove
 (CASE_TERM
  `!s decs ctxt decs' ctxt'.
     evaluate_decls s decs = SOME s' /\
     pan_structs_context_structs ctxt =
       MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info))
           (pan_state_structs (s:(A,FFI)pan_state)) /\
     pan_structs_context_locals ctxt = [] /\
     struct_infos_ok (pan_state_structs s) /\
     FEVERY (\p. match p with (nm,v) -> v_flds_ok (pan_state_structs s) v)
            (pan_state_globals s) /\
     FEVERY (\p. match p with (nm,v) -> is_wf_shape_v (pan_state_structs s) v)
            (pan_state_globals s) /\
     alist_to_fmap (pan_structs_context_globals ctxt) =
       FMAP_MAP2 (shape_of o SND) (pan_state_globals s) /\
     pan_structs_compile_decs ctxt (decs:((A)decl)list) = (decs',ctxt') ==>
     evaluate_decls (convert_s ctxt' s) decs' = SOME (convert_s ctxt' s') /\
     (?gb. ctxt' = pan_structs_context_globals_fupd (K gb) ctxt /\
           FEVERY (\p. match p with (nm,v) -> v_flds_ok (pan_state_structs s) v)
                  (pan_state_globals s') /\
           FEVERY (\p. match p with (nm,v) -> is_wf_shape_v (pan_state_structs s) v)
                  (pan_state_globals s') /\
           pan_state_structs s' = pan_state_structs s /\
           pan_state_locals s' = pan_state_locals s /\
           alist_to_fmap gb = FMAP_MAP2 (shape_of o SND) (pan_state_globals s'))`,
  REC_IND_TAC evaluate_decls_ind THEN REPEAT CONJ_TAC THENL
  [(REPEAT GEN_TAC THEN
   REWRITE_TAC[evaluate_decls_def; pan_structs_compile_decs_def; injectivity "option"; PAIR_EQ] THEN
   STRIP_TAC THEN
   REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
   REWRITE_TAC[evaluate_decls_def] THEN
   EXISTS_TAC `pan_structs_context_globals ctxt` THEN
   ASM_REWRITE_TAC[] THEN SIMP[pan_structs_context_component_equality]);
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[evaluate_decls_def; pan_structs_compile_decs_def] THEN
   FIRST_X_ASSUM MATCH_ACCEPT_TAC);
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[evaluate_decls_def; pan_structs_compile_decs_def] THEN
   QCASES_ON "pan_eval (pan_state_locals_fupd (K FEMPTY) (s:(A,FFI)pan_state)) e" THEN
   CASE_REWRITE_TAC[distinctness "option"] THEN
   RENAME1 "pan_eval (pan_state_locals_fupd (K FEMPTY) s) e = SOME res" THEN
   COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `res:(A)pan_v`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   PAIRARG_TAC) THEN
   (STRIP_TAC THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `decs':((A)decl)list`)) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> rhs(concl th) = `ctxt':pan_structs_context`)) THEN
   SUBGOAL_THEN
     `old_exp_shape ctxt e = shape_of (res:(A)pan_v) /\
      v_flds_ok (pan_state_structs (s:(A,FFI)pan_state)) res /\
      pan_eval (convert_s ctxt (pan_state_locals_fupd (K FEMPTY) s))
               (pan_structs_compile_exp ctxt e) = SOME (convert_v res)`
     STRIP_ASSUME_TAC THENL
    [MP_TAC(ISPECL [`pan_state_locals_fupd (K FEMPTY) (s:(A,FFI)pan_state)`;
                    `e:(A)panLang_exp`; `res:(A)pan_v`]
       pan_structsProof_compile_exp_correct) THEN
     SIMP[alist_to_fmap_thm; FMAP_MAP2_FEMPTY; FEVERY_FEMPTY] THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `is_wf_shape_v (pan_state_structs (s:(A,FFI)pan_state)) (res:(A)pan_v)`
     ASSUME_TAC THENL
    [MP_TAC(ISPECL [`pan_state_locals_fupd (K FEMPTY) (s:(A,FFI)pan_state)`;
                    `e:(A)panLang_exp`; `res:(A)pan_v`] eval_is_wf_shape_v) THEN
     ASM_REWRITE_TAC[] THEN SIMP[FEVERY_FEMPTY] THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
   (FIRST_X_ASSUM(MP_TAC o SPECL
     [`pan_structs_context_globals_fupd
         (K (CONS (v,shape_of (res:(A)pan_v)) (pan_structs_context_globals ctxt))) ctxt`;
      `ds':((A)decl)list`; `ctxt':pan_structs_context`] o check (is_forall o concl)) THEN
   SIMP[alist_to_fmap_thm; FMAP_MAP2_FUPDATE; FEVERY_FUPDATE; o_THM] THEN
   ASM_SIMP_TAC[fevery_to_drestrict]) THEN
   (SUBGOAL_THEN `pan_structs_context_structs ctxt' = pan_structs_context_structs ctxt`
     ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP compile_decs_structs) THEN SIMP[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `pan_eval (pan_state_locals_fupd (K FEMPTY) (convert_s ctxt' (s:(A,FFI)pan_state)))
               (pan_structs_compile_exp ctxt e) = SOME (convert_v (res:(A)pan_v))`
     ASSUME_TAC THENL
    [SUBGOAL_THEN
       `pan_state_locals_fupd (K FEMPTY) (convert_s ctxt' (s:(A,FFI)pan_state)) =
        pan_state_code_fupd (K (convert_code ctxt' (pan_state_code s)))
          (convert_s ctxt (pan_state_locals_fupd (K FEMPTY) s))` SUBST1_TAC THENL
      [SIMP[convert_s_def; pan_state_component_equality; FMAP_MAP2_FEMPTY] THEN
       ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     ASM_REWRITE_TAC[eval_upd_code_eq];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[evaluate_decls_def] THEN CASE_REWRITE_TAC[] THEN
   ASM_SIMP_TAC[shape_of_convert_v_rev] THEN
   DISCH_THEN(MP_TAC o CONJUNCT1) THEN MATCH_MP_TAC EQ_IMP THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   SIMP[convert_s_def; pan_state_component_equality; FMAP_MAP2_FUPDATE]);
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[evaluate_decls_def; pan_structs_compile_decs_def] THEN
   COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
   FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
   (PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `decs':((A)decl)list`)) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> rhs(concl th) = `ctxt':pan_structs_context`))) THEN
   (SUBGOAL_THEN `pan_structs_context_structs ctxt' = pan_structs_context_structs ctxt`
     ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP compile_decs_structs) THEN SIMP[]; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL
     [`ctxt:pan_structs_context`; `ds':((A)decl)list`; `ctxt':pan_structs_context`] o
     check (is_forall o concl)) THEN
   SIMP[] THEN ASM_REWRITE_TAC[]) THEN
   (DISCH_THEN(MP_TAC o CONJUNCT1) THEN
   REWRITE_TAC[evaluate_decls_def] THEN SIMP[convert_s_def]) THEN
   (SUBGOAL_THEN
     (CASE_TERM
       `MAP (\q. match q with
                   (p,sh0) -> (p,compile_shape
                                 (MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info))
                                      (pan_state_structs (s:(A,FFI)pan_state))) sh0))
            (fun_decl_params (fi:(A)fun_decl)) =
        MAP (I ## compile_shape
                    (MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info))
                         (pan_state_structs s)))
            (fun_decl_params fi)`) SUBST1_TAC THENL
    [MATCH_MP_TAC MAP_CONG THEN REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM; I_THM] THEN
     CASE_REWRITE_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[ALL_MAP; o_DEF; SND_PAIR_MAP; is_wf_shape_compile_shape; ALL_T] THEN
   REWRITE_TAC[convert_code_def; FMAP_MAP2_FUPDATE] THEN CASE_REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[]);
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[evaluate_decls_def; pan_structs_compile_decs_def] THEN
   COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
   FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `decs':((A)decl)list`)) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> rhs(concl th) = `ctxt':pan_structs_context`)) THEN
   SUBGOAL_THEN `pan_structs_context_structs ctxt' = pan_structs_context_structs ctxt`
     ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP compile_decs_structs) THEN SIMP[]; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL
     [`ctxt:pan_structs_context`; `ds':((A)decl)list`; `ctxt':pan_structs_context`] o
     check (is_forall o concl)) THEN
   SIMP[] THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o CONJUNCT1) THEN
   REWRITE_TAC[evaluate_decls_def] THEN SIMP[convert_s_def] THEN
   REWRITE_TAC[convert_eshapes_def; FLOOKUP_FMAP_MAP2; FMAP_MAP2_FUPDATE;
               is_wf_shape_compile_shape] THEN
   ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[])]);;

let decs_stcnames_compile_decs = prove
 (`!ctxt (decs:((A)decl)list).
     decs_stcnames (acc:(stcname#struct_info)list)
                   (FST (pan_structs_compile_decs ctxt decs)) = SOME acc`,
  MATCH_MP_TAC pan_structs_compile_decs_ind THEN
  REWRITE_TAC[pan_structs_compile_decs_def; decs_stcnames_def] THEN RW[] THEN
  PAIRARG_TAC THEN FS[decs_stcnames_def]);;

let decs_stcnames_to_get_names = prove
 (CASE_TERM
  `!acc (code:((A)decl)list) res ctxt.
     decs_stcnames acc code = SOME res /\
     pan_structs_context_structs ctxt =
       MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info)) acc ==>
     get_names ctxt code =
       pan_structs_context_structs_fupd
         (K (MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info)) res)) ctxt`,
  REC_IND_TAC decs_stcnames_ind THEN
  SIMP[decs_stcnames_def; get_names_def] THEN RW[] THEN
  FS(all_case_eqs()) THEN SIMP[pan_structs_context_component_equality]);;

(* HOL4 also binds a vacuous ctxt (of a free type) *)
let decs_stcnames_infos_ok = prove
 (`!acc (code:((A)decl)list) res.
     decs_stcnames acc code = SOME res /\ struct_infos_ok acc ==>
     struct_infos_ok res`,
  REC_IND_TAC decs_stcnames_ind THEN SIMP[decs_stcnames_def] THEN RW[] THEN
  FS(all_case_eqs()) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC struct_infos_ok_cons THEN SIMP[] THEN
  ASM_REWRITE_TAC[GSYM ALOOKUP_NONE]);;

let PPASS1AUX_convert_res_outcome = prove
 (CASE_TERM
  `!r:((A)pan_result)option.
     ((match convert_res r with
         SOME pan_TimeOut -> F | SOME (pan_FinalFFI _) -> F | SOME (pan_Return _) -> F
       | _ -> T) <=>
      (match r with
         SOME pan_TimeOut -> F | SOME (pan_FinalFFI _) -> F | SOME (pan_Return _) -> F
       | _ -> T)) /\
     (!outcome.
        (match convert_res r with
           SOME (pan_FinalFFI e) -> outcome = FFI_outcome e
         | SOME (pan_Return _) -> outcome = Success
         | _ -> F) <=>
        (match r with
           SOME (pan_FinalFFI e) -> outcome = FFI_outcome e
         | SOME (pan_Return _) -> outcome = Success
         | _ -> F))`,
  GEN_TAC THEN QCASES_ON "r:((A)pan_result)option" THEN
  REWRITE_TAC[convert_res_def] THEN CASE_REWRITE_TAC[] THEN
  QCASES_ON "a:(A)pan_result" THEN REWRITE_TAC[convert_res_def] THEN CASE_REWRITE_TAC[]);;

(* the two semantics are equal when the runs of the program of pan_semantics *)
(* agree clock by clock, up to convert_res in the result                    *)
let PPASS1AUX_pan_semantics_cong2 = prove
 (`!(s:(A,FFI)pan_state) (t:(A,FFI)pan_state) start.
     (!k. FST (pan_evaluate (panLang_Call NONE start [],pan_state_clock_fupd (K k) t)) =
          convert_res
            (FST (pan_evaluate (panLang_Call NONE start [],pan_state_clock_fupd (K k) s)))) /\
     (!k. pan_state_ffi
            (SND (pan_evaluate (panLang_Call NONE start [],pan_state_clock_fupd (K k) t))) =
          pan_state_ffi
            (SND (pan_evaluate (panLang_Call NONE start [],pan_state_clock_fupd (K k) s))))
     ==> pan_semantics t start = pan_semantics s start`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[pan_semantics_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[PPASS1AUX_convert_res_outcome] THEN
  SUBGOAL_THEN
    (CASE_TERM
     `!res. (?k t' r outcome.
               pan_evaluate (panLang_Call NONE (start:mlstring) [],
                             pan_state_clock_fupd (K k) (t:(A,FFI)pan_state)) =
                 (r,t') /\
               (match r with
                  SOME (pan_FinalFFI e) -> outcome = FFI_outcome e
                | SOME (pan_Return _) -> outcome = Success
                | _ -> F) /\
               res = Terminate outcome (ffi_state_io_events (pan_state_ffi t'))) <=>
            (?k t' r outcome.
               pan_evaluate (panLang_Call NONE start [],
                             pan_state_clock_fupd (K k) (s:(A,FFI)pan_state)) =
                 (r,t') /\
               (match r with
                  SOME (pan_FinalFFI e) -> outcome = FFI_outcome e
                | SOME (pan_Return _) -> outcome = Success
                | _ -> F) /\
               res = Terminate outcome
                       (ffi_state_io_events (pan_state_ffi (t':(A,FFI)pan_state))))`)
    (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN REWRITE_TAC[PAIR_FST_SND_EQ; FST; SND] THEN
  EQ_TAC THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`k:num`] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    try let l,r = dest_eq(concl th) in is_var r && not (is_var l) &&
        (rator l = `SND:((A)pan_result)option#(A,FFI)pan_state->(A,FFI)pan_state` ||
         rator l = `FST:((A)pan_result)option#(A,FFI)pan_state->((A)pan_result)option`)
    with Failure _ -> false))) THEN
  (fun (asl,w as g) ->
     let _,b = strip_exists w in
     let cs = conjuncts b in
     MAP_EVERY EXISTS_TAC [lhs(el 1 cs); lhs(el 0 cs); `outcome:outcome`] g) THEN
  ASM_REWRITE_TAC[PPASS1AUX_convert_res_outcome] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> not(is_forall(concl th)) && not(is_eq(concl th)) &&
                                          not(is_neg(concl th)))) THEN
  ASM_REWRITE_TAC[PPASS1AUX_convert_res_outcome]);;

(* HOL4 proves it with pan_sem_is_wrapper and semantics_wrapper_eq; here  *)
(* compile_correct relates the runs at equal clocks (convert_s keeps the   *)
(* clock and the ffi state), so PPASS1AUX_pan_semantics_cong2 applies      *)

let semantics_eq = prove
 (CASE_TERM
  `~(pan_semantics s start = Fail) /\
   pan_structs_context_structs ctxt =
     MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info))
         (pan_state_structs (s:(A,FFI)pan_state)) /\
   pan_state_locals s = FEMPTY /\
   FEVERY (\p. match p with (nm,v) -> v_flds_ok (pan_state_structs s) v)
          (pan_state_globals s) /\
   FEVERY (\p. match p with (nm,v) -> is_wf_shape_v (pan_state_structs s) v)
          (pan_state_globals s) /\
   pan_structs_context_locals ctxt = [] /\
   alist_to_fmap (pan_structs_context_globals ctxt) =
     FMAP_MAP2 (shape_of o SND) (pan_state_globals s) /\
   struct_infos_ok (pan_state_structs s)
   ==> pan_semantics (convert_s ctxt s) start = pan_semantics s start`,
  STRIP_TAC THEN MATCH_MP_TAC PPASS1AUX_pan_semantics_cong2 THEN
  SUBGOAL_THEN
    `!k. pan_evaluate (panLang_Call NONE start [],
                       pan_state_clock_fupd (K k) (convert_s ctxt (s:(A,FFI)pan_state))) =
         (convert_res (FST (pan_evaluate (panLang_Call NONE start [],
                                          pan_state_clock_fupd (K k) s))),
          convert_s ctxt (SND (pan_evaluate (panLang_Call NONE start [],
                                             pan_state_clock_fupd (K k) s))))`
    (fun th -> REWRITE_TAC[th] THEN SIMP[convert_s_def]) THEN
  X_GEN_TAC `k:num` THEN
  MP_TAC(ISPEC `pan_evaluate (panLang_Call NONE start [],
                              pan_state_clock_fupd (K k) (s:(A,FFI)pan_state))`
         PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r:((A)pan_result)option`; `s1:(A,FFI)pan_state`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(r = SOME (pan_Error:(A)pan_result))` ASSUME_TAC THENL
   [UNDISCH_TAC `~(pan_semantics (s:(A,FFI)pan_state) start = Fail)` THEN
    REWRITE_TAC[pan_semantics_def; LET_DEF; LET_END_DEF] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[FST] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`panLang_Call NONE start []:(A)panLang_prog`;
                 `pan_state_clock_fupd (K k) (s:(A,FFI)pan_state)`;
                 `r:((A)pan_result)option`; `s1:(A,FFI)pan_state`;
                 `ctxt:pan_structs_context`] pan_structsProof_compile_correct) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SIMP[] THEN
    ASM_REWRITE_TAC[FEVERY_FEMPTY; FMAP_MAP2_FEMPTY; alist_to_fmap_thm];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `pan_structs_compile ctxt (panLang_Call NONE start []:(A)panLang_prog) =
                panLang_Call NONE start []` SUBST1_TAC THENL
   [REWRITE_TAC[PPASS1AUX_compile_call; pan_structs_compile_exp_def] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convert_s ctxt (pan_state_clock_fupd (K k) (s:(A,FFI)pan_state)) =
                pan_state_clock_fupd (K k) (convert_s ctxt s)` SUBST1_TAC THENL
   [SIMP[convert_s_def; pan_state_component_equality]; ALL_TAC] THEN
  SIMP_TAC[]);;

(* HOL4: compile_top_semantics_decls; HOL4's <| structs := [] |> is
   pan_structs_context_structs_fupd (K []) ARB *)

let pan_structsProof_compile_top_semantics_decls = prove
 (CASE_TERM
  `~(semantics_decls s start code = Fail) /\
   pan_state_locals (s:(A,FFI)pan_state) = FEMPTY /\ pan_state_code s = FEMPTY /\
   pan_state_globals s = FEMPTY ==>
   semantics_decls s start (code:((A)decl)list) =
   semantics_decls
     (pan_state_eshapes_fupd
        (K (FMAP_MAP2
              (\p. match p with
                     (eid,sh) ->
                       compile_shape
                         (pan_structs_context_structs
                            (get_names (pan_structs_context_structs_fupd (K [])
                                          (ARB:pan_structs_context)) code)) sh)
              (pan_state_eshapes s))) s)
     start (pan_structs_compile_top code)`,
  (STRIP_TAC THEN
   UNDISCH_TAC `~(semantics_decls (s:(A,FFI)pan_state) start (code:((A)decl)list) = Fail)` THEN
   REWRITE_TAC[semantics_decls_def] THEN
   QCASES_ON "decs_stcnames [] (code:((A)decl)list)" THEN CASE_REWRITE_TAC[] THEN
   RENAME1 "decs_stcnames [] code = SOME st_ctxt" THEN
   QCASES_ON "evaluate_decls (pan_state_structs_fupd (K st_ctxt) (s:(A,FFI)pan_state)) code" THEN
   CASE_REWRITE_TAC[] THEN
   RENAME1 "evaluate_decls (pan_state_structs_fupd (K st_ctxt) s) code = SOME s1" THEN
   DISCH_TAC THEN
   REWRITE_TAC[pan_structs_compile_top_def; LET_DEF; LET_END_DEF; decs_stcnames_compile_decs] THEN
   CASE_REWRITE_TAC[]) THEN
  (SUBGOAL_THEN `struct_infos_ok ([]:(mlstring#struct_info)list)` ASSUME_TAC THENL
    [REWRITE_TAC[struct_infos_ok_def; ALL; MAP; ALL_DISTINCT; LENGTH; LT]; ALL_TAC] THEN
   SUBGOAL_THEN `struct_infos_ok (st_ctxt:(mlstring#struct_info)list)` ASSUME_TAC THENL
    [MATCH_MP_TAC decs_stcnames_infos_ok THEN
     MAP_EVERY EXISTS_TAC [`[]:(mlstring#struct_info)list`; `code:((A)decl)list`] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`[]:(mlstring#struct_info)list`; `code:((A)decl)list`;
                  `st_ctxt:(mlstring#struct_info)list`;
                  `pan_structs_context_REC [] [] []`] decs_stcnames_to_get_names) THEN
   MP_TAC(ISPECL [`[]:(mlstring#struct_info)list`; `code:((A)decl)list`;
                  `st_ctxt:(mlstring#struct_info)list`;
                  `pan_structs_context_structs_fupd (K []) (ARB:pan_structs_context)`]
                 decs_stcnames_to_get_names) THEN
   ASM_REWRITE_TAC[MAP] THEN SIMP[] THEN
   DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN SIMP[]) THEN
  (MP_TAC(ISPEC (CASE_TERM `pan_structs_compile_decs
                    (pan_structs_context_REC
                       (MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info))
                            (st_ctxt:(mlstring#struct_info)list)) [] [])
                    (code:((A)decl)list)`) PAIR_SURJECTIVE) THEN
   REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
   MAP_EVERY X_GEN_TAC [`decs':((A)decl)list`; `ctxt':pan_structs_context`] THEN
   DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`pan_state_structs_fupd (K st_ctxt) (s:(A,FFI)pan_state)`;
                  `code:((A)decl)list`;
                  CASE_TERM `pan_structs_context_REC
                       (MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info))
                            (st_ctxt:(mlstring#struct_info)list)) [] []`;
                  `decs':((A)decl)list`; `ctxt':pan_structs_context`]
     (INST [`s1:(A,FFI)pan_state`,`s':(A,FFI)pan_state`] compile_decls_correct)) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN SIMP[] THEN
     ASM_REWRITE_TAC[FEVERY_FEMPTY; FMAP_MAP2_FEMPTY; alist_to_fmap_thm];
     ALL_TAC] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `gb:(mlstring#shape)list` STRIP_ASSUME_TAC))) THEN
  (SUBGOAL_THEN
     (CASE_TERM
      `pan_state_structs_fupd (K [])
         (pan_state_eshapes_fupd
            (K (FMAP_MAP2
                  (\p. match p with
                         (eid,sh) ->
                           compile_shape
                             (MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info))
                                  (st_ctxt:(mlstring#struct_info)list)) sh)
                  (pan_state_eshapes s))) (s:(A,FFI)pan_state)) =
       convert_s ctxt' (pan_state_structs_fupd (K st_ctxt) s)`) SUBST1_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     SIMP[convert_s_def; convert_code_def; convert_eshapes_def; FMAP_MAP2_FEMPTY;
          pan_state_component_equality] THEN
     ASM_REWRITE_TAC[FMAP_MAP2_FEMPTY];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC semantics_eq THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
   ASM_REWRITE_TAC[]));;

let compile_decs_no_names = prove
 (`!ctxt (decs:((A)decl)list).
     ALL (\d. is_function d \/ is_decl d \/ is_exn_decl d)
         (FST (pan_structs_compile_decs ctxt decs))`,
  MATCH_MP_TAC pan_structs_compile_decs_ind THEN
  REWRITE_TAC[pan_structs_compile_decs_def] THEN RW[] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN
  FS[ALL; is_function_def; is_decl_def; is_exn_decl_def]);;

let compile_top_no_names = prove
 (`ALL (\d. is_function d \/ is_decl d \/ is_exn_decl d)
       (pan_structs_compile_top (pan_code:((A)decl)list))`,
  REWRITE_TAC[pan_structs_compile_top_def; LET_DEF; LET_END_DEF; compile_decs_no_names]);;

let compile_shape_n_no_name = prove
 (`!(ctxt:(stcname#((B#shape)list))list) n sh.
     is_wf_shape ([]:(mlstring#struct_info)list) (compile_shape_n ctxt n sh)`,
  MATCH_MP_TAC compile_shape_n_ind THEN
  SIMP[compile_shape_n_def; is_wf_shape_def; EVERY_MAP] THEN RW[] THEN
  SIMP[EVERY_MEM] THEN EVERY_CASE_TAC THEN SIMP[is_wf_shape_def] THEN
  SIMP[is_wf_shape_def; EVERY_MAP; EVERY_MEM; MEM_MAP] THEN
  RW[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[MEM_MAP]);;

let pan_structsProof_compile_shape_no_name = prove
 (`!(ctxt:(stcname#((B#shape)list))list) sh.
     is_wf_shape ([]:(mlstring#struct_info)list) (compile_shape ctxt sh)`,
  REWRITE_TAC[compile_shape_n_eq_rev; compile_shape_n_no_name]);;

let size_of_shape_compile_pass_eq = prove
 (CASE_TERM
  `struct_infos_ok (pan_state_structs (s:(A,FFI)pan_state)) /\
   is_wf_shape (pan_state_structs s) shape /\
   str_ctxt =
     MAP (\p. match p with (nm,info) -> (nm,struct_info_fields info)) (pan_state_structs s) ==>
   size_of_shape (compile_shape str_ctxt shape) =
   size_of_sh_with_ctxt (pan_state_structs s) shape`,
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[size_of_sh_with_ctxt_eq; size_of_compile_shape;
                pan_structsProof_compile_shape_no_name]);;
