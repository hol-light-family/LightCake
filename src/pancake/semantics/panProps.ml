(* ========================================================================= *)
(* panProps: port of HOL4 pancake/semantics/panPropsScript.sml (CakeML      *)
(* v3479).  panLang Properties.                                              *)
(* ========================================================================= *)

needs "pancake/panLang.ml";;
needs "pancake/semantics/panSem.ml";;
needs "pancake/semantics/pan_commonProps.ml";;

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Shapes of values.                                                         *)
(* ------------------------------------------------------------------------- *)

let v2word_def = cake_def
  `v2word (pan_Val (Word (v:A word))) = Word v`;;

let shape_of_val = prove
 (`!x:(A)word_lab. shape_of (pan_Val x) = One`,
  GEN_TAC THEN QCASES_ON "x" THEN SIMP[shape_of_def]);;

(* HOL4 Overloads is_wf_shape_nil = is_wf_shape [] and is_wf_shape_v_nil =  *)
(* is_wf_shape_v [] (the EVAL of TAKE 0 s.structs, so [] is a              *)
(* (stcname # struct_info) list) are written out                            *)

let is_wf_shape_v_def = cake_def_wf
  `measure (\p:(mlstring#B)list#(A)pan_v. pan_v_size (ARB:A->num) (SND p))`
  PSEMAUX_V_TC_TAC
  `(is_wf_shape_v (sctxt:(mlstring#B)list) (pan_Val (v:(A)word_lab)) <=> T) /\
   (is_wf_shape_v sctxt (pan_RStruct vs) <=> ALL (is_wf_shape_v sctxt) vs) /\
   (is_wf_shape_v sctxt (pan_NStruct nm nm_vs) <=>
      ~(ALOOKUP sctxt nm = NONE) /\ ALL (is_wf_shape_v sctxt) (MAP SND nm_vs))`;;

let is_wf_shape_v_ind = cake_ind "is_wf_shape_v";;

let is_wf_shape_of_v = prove
 (`!sctxt (v:(A)pan_v). is_wf_shape_v (sctxt:(mlstring#B)list) v
                        ==> is_wf_shape sctxt (shape_of v)`,
  REC_IND_TAC is_wf_shape_v_ind THEN
  RW[is_wf_shape_def; shape_of_def; is_wf_shape_v_def; shape_of_val] THEN
  SIMP[ALL_MAP] THEN FS[EVERY_MEM] THEN EVERY_CASE_TAC THEN FS[]);;

(* HOL4 [local] *)

let is_wf_shape_v_nil_step1 = prove
 (`!sctxt (v:(A)pan_v).
     sctxt = [] /\ is_wf_shape (sctxt:(mlstring#B)list) (shape_of v)
     ==> is_wf_shape_v sctxt v`,
  REC_IND_TAC is_wf_shape_v_ind THEN
  RW[is_wf_shape_v_def; is_wf_shape_def; shape_of_def] THEN FS[ALL_MAP] THEN
  FS[EVERY_MEM]);;

let is_wf_shape_v_nil = prove
 (`!xs. xs = []
        ==> (is_wf_shape (xs:(mlstring#B)list) (shape_of (v:(A)pan_v)) <=>
             is_wf_shape_v xs v)`,
  MESON_TAC[is_wf_shape_v_nil_step1; is_wf_shape_of_v]);;

let is_wf_shape_v_drop = prove
 (`!sctxt (v:(A)pan_v).
     is_wf_shape_v (DROP k (sctxt:(mlstring#B)list)) v ==> is_wf_shape_v sctxt v`,
  REC_IND_TAC is_wf_shape_v_ind THEN RW[is_wf_shape_v_def] THEN FS[EVERY_MEM] THEN
  QSPECL_THEN ["TAKE k sctxt"; "DROP k sctxt"; "nm"] MP_TAC ALOOKUP_APPEND THEN
  REWRITE_TAC[TAKE_DROP] THEN ASM_REWRITE_TAC[] THEN
  TOP_CASE_TAC THEN FS[] THEN ASM_MESON_TAC[]);;

(* HOL4 [local] *)

let dropWhile_eq_cons_IMP = prove
 (`dropWhile P (xs:A list) = CONS y ys
   ==> ?n. n < LENGTH xs /\ y = EL n xs /\ ~P y /\ DROP n xs = CONS y ys`,
  QINDUCT_ON "xs" THEN RW[dropWhile_def] THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN QEXISTS_TAC "SUC n" THEN
    ASM_SIMP_TAC[EL; TL; DROP; ARITH_RULE `n < m ==> SUC n <= m`];
    QEXISTS_TAC "0" THEN SIMP[EL; HD; DROP; LE_0]]);;

(* HOL4 finds the struct by ALOOKUP_LEAST_EL; here the found pair is a      *)
(* member of the context, and the rest of the context is a DROP of it       *)

let mem_load_is_wf_shape_v = prove
 (`(!shape (w:A word) sa sm (sctxt:(mlstring#struct_info)list) v.
      pan_mem_load shape w sa sm sctxt = SOME v ==> is_wf_shape_v sctxt v) /\
   (!shapes (w:A word) sa sm (sctxt:(mlstring#struct_info)list) vs.
      mem_loads shapes w sa sm sctxt = SOME vs ==> ALL (is_wf_shape_v sctxt) vs) /\
   (!flds (w:A word) sa sm (sctxt:(mlstring#struct_info)list) nm_vs.
      mem_load_flds flds w sa sm sctxt = SOME nm_vs
      ==> ALL (is_wf_shape_v sctxt) (MAP SND nm_vs))`,
  MATCH_MP_TAC pan_mem_load_ind THEN RW[] THEN
  GVS(all_case_eqs() @ [pan_mem_load_def; is_wf_shape_v_def]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP dropWhile_eq_cons_IMP) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ALOOKUP_NONE; MEM_MAP; EXISTS_PAIR_THM] THEN
    ASM_MESON_TAC[MEM_EL; FST];
    QPAT_X_ASSUM "DROP _ _ = _"
      (MP_TAC o AP_TERM
         `DROP 1:(mlstring#struct_info)list->(mlstring#struct_info)list`) THEN
    ASM_SIMP_TAC[DROP_DROP; ARITH_RULE `n < m ==> 1 + n <= m`; DROP_DEF; ARITH_EQ;
                 SUB_REFL; CONJUNCT1 DROP] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    QPAT_X_ASSUM "ALL _ _" MP_TAC THEN
    MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[is_wf_shape_v_drop]]);;

let OPT_MMAP_MEM_IMP = prove
 (`OPT_MMAP (f:A->B option) xs = SOME ys /\ MEM y ys ==> ?x. MEM x xs /\ f x = SOME y`,
  RW[] THEN IMP_RES_TAC opt_mmap_length_eq THEN FS[list_MEM_EL] THEN
  RVEQ_TAC THEN EXISTS_TAC `EL i (xs:A list)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[opt_mmap_el]]);;

(* HOL4 FEVERY (\(nm,v). P v) is FEVERY (\p. match p with (nm,v) -> P v).  *)
(* The cases left by GVS, in order: Var Local, Var Global, RStruct, RField, *)
(* NStruct, NField, Load                                                     *)

let eval_is_wf_shape_v = prove
 (CASE_TERM `!s exp (v:(A)pan_v).
     pan_eval (s:(A,FFI)pan_state) exp = SOME v /\
     FEVERY (\p. match p with (nm,v) -> is_wf_shape_v (pan_state_structs s) v)
            (pan_state_locals s) /\
     FEVERY (\p. match p with (nm,v) -> is_wf_shape_v (pan_state_structs s) v)
            (pan_state_globals s)
     ==> is_wf_shape_v (pan_state_structs s) v`,
  REC_IND_TAC pan_eval_ind THEN SIMP[pan_eval_def; shape_of_def; is_wf_shape_v_def] THEN
  RW[] THEN GVS(all_case_eqs() @ [UNZIP_DEF; is_wf_shape_v_def; shape_of_def]) THENL
   [IMP_RES_TAC FEVERY_FLOOKUP THEN FS[pair_CASE];
    IMP_RES_TAC FEVERY_FLOOKUP THEN FS[pair_CASE];
    RW[EVERY_MEM] THEN ASM_MESON_TAC[OPT_MMAP_MEM_IMP];
    FS[EVERY_EL];
    IMP_RES_TAC opt_mmap_length_eq THEN FS[LENGTH_MAP] THEN
    FS[MAP_ZIP; LENGTH_MAP] THEN RW[EVERY_MEM] THEN ASM_MESON_TAC[OPT_MMAP_MEM_IMP];
    IMP_RES_TAC ALOOKUP_MEM THEN FS[EVERY_MEM; MEM_MAP; EXISTS_PAIR_THM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SND];
    IMP_RES_TAC mem_load_is_wf_shape_v THEN ASM_REWRITE_TAC[]]);;

let pan_primop_is_wf_shape_v = prove
 (`!(sctxt:(mlstring#B)list) pop args (value:(A)pan_v).
     pan_primop pop args = SOME value ==> is_wf_shape_v sctxt value`,
  REPEAT GEN_TAC THEN QCASES_ON "pop" THEN RW[pan_primop_def] THEN
  GVS(all_case_eqs()) THEN SIMP[is_wf_shape_v_def; ALL]);;

(* HOL4 sums the lengths with SUM_MAP_FOLDL and FOLDL_CONG; here MAP_CONG *)

let length_flatten_eq_size_of_shape = prove
 (`!v:(A)pan_v. is_wf_shape ([]:(mlstring#struct_info)list) (shape_of v)
       ==> LENGTH (flatten v) = size_of_shape (shape_of v)`,
  REC_IND_TAC flatten_ind THEN RW[] THEN
  FS[is_wf_shape_def; shape_of_def; shape_of_val; ALOOKUP_DEF] THEN
  SIMP[flatten_def; shape_of_def; size_of_shape_def] THEN
  SIMP[LENGTH_FLAT; MAP_MAP_o; o_DEF] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MAP_CONG THEN FS[ALL_MAP; EVERY_MEM; o_THM]);;

let size_of_sh_with_ctxt_eq = prove
 (`!sh (sctxt:(mlstring#struct_info)list).
     is_wf_shape ([]:(mlstring#struct_info)list) sh
     ==> size_of_sh_with_ctxt sctxt sh = size_of_shape sh`,
  REC_IND_TAC (cake_ind "size_of_shape") THEN
  SIMP[is_wf_shape_def; size_of_shape_def; size_of_sh_with_ctxt_def; ALOOKUP_DEF] THEN
  RW[EVERY_MEM] THEN AP_TERM_TAC THEN MATCH_MP_TAC MAP_CONG THEN ASM_MESON_TAC[]);;

(* the clause's own equation is unfolded once (not the induction          *)
(* hypotheses)                                                               *)

let mem_loads_some_shape_eq = prove
 (`(!sh (adr:A word) dm (m:A word->(A)word_lab) stcs v.
      pan_mem_load sh adr dm m stcs = SOME v ==> shape_of v = sh) /\
   (!shs (adr:A word) dm (m:A word->(A)word_lab) stcs vs.
      mem_loads shs adr dm m stcs = SOME vs ==> MAP shape_of vs = shs) /\
   (!flds (adr:A word) dm (m:A word->(A)word_lab) stcs vs.
      mem_load_flds flds adr dm m stcs = SOME vs
      ==> MAP (shape_of o SND) vs = MAP SND flds)`,
  MATCH_MP_TAC pan_mem_load_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST [QPAT_X_ASSUM "pan_mem_load _ _ _ _ _ = SOME _" MP_TAC;
         QPAT_X_ASSUM "mem_loads _ _ _ _ _ = SOME _" MP_TAC;
         QPAT_X_ASSUM "mem_load_flds _ _ _ _ _ = SOME _" MP_TAC] THEN
  ONCE_REWRITE_TAC[pan_mem_load_def] THEN RW[] THEN GVS(all_case_eqs()) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP dropWhile_eq_cons_IMP)) THEN
  FS[shape_of_def; shape_of_val; pair_CASE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM PAIR_EQ]) THEN FS[]);;

let mem_load_some_shape_eq = prove
 (`!sh (adr:A word) dm (m:A word->(A)word_lab) stcs v.
     pan_mem_load sh adr dm m stcs = SOME v ==> shape_of v = sh`,
  MESON_TAC[mem_loads_some_shape_eq]);;

let flookup_res_var_some_eq_lookup = prove
 (`FLOOKUP (pan_res_var lc (v,FLOOKUP lc' v)) v = SOME (value:(A)pan_v)
   ==> FLOOKUP lc' v = SOME value`,
  RW[] THEN QCASES_ON "FLOOKUP lc' v" THEN FS[pan_res_var_def; FLOOKUP_UPDATE] THEN
  FS[DOMSUB_FLOOKUP_THM]);;

let flookup_res_var_diff_eq_org = prove
 (`~(n = m) ==> FLOOKUP (pan_res_var lc (n,v)) m = FLOOKUP lc m:((A)pan_v)option`,
  RW[] THEN QCASES_ON "v" THEN
  FS[pan_res_var_def; FLOOKUP_UPDATE; DOMSUB_FLOOKUP_NEQ]);;

let FLOOKUP_pan_res_var_thm = prove
 (`FLOOKUP (pan_res_var l (m,v)) n =
   if n = m then v else FLOOKUP l n:((A)pan_v)option`,
  QCASES_ON "v" THEN RW[pan_res_var_def; DOMSUB_FLOOKUP_THM; FLOOKUP_UPDATE] THEN
  FS[]);;

(* ------------------------------------------------------------------------- *)
(* Flattened values and with_shape.                                          *)
(* ------------------------------------------------------------------------- *)

(* HOL4 [local] *)

let list_rel_length_shape_of_flatten_better = prove
 (`!vshs (args:((A)pan_v)list).
     ALL2 (\vsh arg. vsh = shape_of arg) vshs args /\
     ALL (is_wf_shape_v ([]:(mlstring#struct_info)list)) args
     ==> size_of_shape (Comb vshs) = LENGTH (FLAT (MAP flatten args))`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FS[EVERY2_THM; size_of_shape_def] THEN RES_TAC THEN
  GVS[length_flatten_eq_size_of_shape; is_wf_shape_v_def; is_wf_shape_v_nil;
      MAP; FLAT; LENGTH_APPEND; SUM]);;

let list_rel_length_shape_of_flatten = prove
 (`!vshs (args:((A)pan_v)list).
     ALL2 (\vsh arg. SND vsh = shape_of arg) (vshs:(B#shape)list) args /\
     ALL (is_wf_shape_v ([]:(mlstring#struct_info)list)) args
     ==> size_of_shape (Comb (MAP SND vshs)) = LENGTH (FLAT (MAP flatten args))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC list_rel_length_shape_of_flatten_better THEN
  ASM_SIMP_TAC[EVERY2_MAP]);;

let length_with_shape_eq_shape = prove
 (`!sh (ns:A list). LENGTH ns = size_of_shape (Comb sh)
                    ==> LENGTH sh = LENGTH (with_shape sh ns)`,
  LIST_INDUCT_TAC THEN RW[] THEN FS[with_shape_def] THEN
  FS[size_of_shape_def; MAP; SUM] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH_DROP] THEN ARITH_TAC);;

let fdoms_eq_flookup_some_none = prove
 (`!(fm:(A,B)fmap) (fm':(A,C)fmap) n v (v':D).
     FDOM fm = FDOM fm' /\ FLOOKUP fm n = SOME v ==> ?v. FLOOKUP fm' n = SOME v`,
  RW[] THEN FS[flookup_thm] THEN ASM SET_TAC[]);;

let all_distinct_with_shape = prove
 (`!sh (ns:A list) n.
     ALL_DISTINCT ns /\ n < LENGTH sh /\ LENGTH ns = size_of_shape (Comb sh)
     ==> ALL_DISTINCT (EL n (with_shape sh ns))`,
  LIST_INDUCT_TAC THEN RW[] THEN FS[with_shape_def] THEN
  NAMED_CASES_ON "n" ["";"n'"] THEN
  FS[ARITH_ss; EL; HD; TL; LT_SUC; size_of_shape_def; MAP; SUM] THENL
   [MATCH_MP_TAC all_distinct_take THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[LENGTH_DROP; all_distinct_drop; ADD_SUB2; LE_ADD]]);;

let el_mem_with_shape = prove
 (`!sh (ns:A list) n x.
     n < LENGTH (with_shape sh ns) /\ LENGTH ns = size_of_shape (Comb sh) /\
     MEM x (EL n (with_shape sh ns))
     ==> MEM x ns`,
  LIST_INDUCT_TAC THEN RW[] THEN FS[with_shape_def] THEN
  NAMED_CASES_ON "n" ["";"n'"] THEN
  FS[ARITH_ss; EL; HD; TL; LT_SUC; LENGTH; size_of_shape_def; MAP; SUM] THENL
   [ASM_MESON_TAC[MEM_TAKE];
    FIRST_X_ASSUM (QSPECL_THEN ["DROP (size_of_shape h) ns"; "n'"; "x"] MP_TAC) THEN
    ASM_SIMP_TAC[LENGTH_DROP; ADD_SUB2] THEN MESON_TAC[MEM_DROP_IMP]]);;

let mem_with_shape_length = prove
 (`!sh (ns:A list) n.
     LENGTH ns = size_of_shape (Comb sh) /\ n < LENGTH sh
     ==> MEM (EL n (with_shape sh ns)) (with_shape sh ns)`,
  LIST_INDUCT_TAC THEN RW[] THEN NAMED_CASES_ON "n" ["";"n'"] THEN
  FS[ARITH_ss; EL; HD; TL; LT_SUC; LENGTH; with_shape_def; MEM] THEN
  DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  FS[size_of_shape_def; MAP; SUM; LENGTH_DROP] THEN ARITH_TAC);;

let with_shape_el_take_drop_eq = prove
 (`!sh (ns:A list) n.
     LENGTH ns = size_of_shape (Comb sh) /\ n < LENGTH sh
     ==> EL n (with_shape sh ns) =
         TAKE (size_of_shape (EL n sh)) (DROP (size_of_shape (Comb (TAKE n sh))) ns)`,
  LIST_INDUCT_TAC THEN RW[] THEN NAMED_CASES_ON "n" ["";"n'"] THEN
  FS[ARITH_ss; EL; HD; TL; LT_SUC; LENGTH] THENL
   [FS[with_shape_def; size_of_shape_def; TAKE; MAP; SUM; DROP];
    FS[with_shape_def; size_of_shape_def; TAKE; MAP; SUM; SUC_SUB1] THEN
    FIRST_X_ASSUM (QSPECL_THEN ["DROP (size_of_shape h) ns"; "n'"] MP_TAC) THEN
    ANTS_TAC THENL [FS[LENGTH_DROP] THEN ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN FS[DROP_DROP_T; ADD_AC]]);;

(* the parts of with_shape after the first shape (HOL4 proves this         *)
(* rewriting inline in each of the next proofs)                             *)

let PSEMAUX_with_shape_tail_el = prove
 (`!h t (ns:A list) i.
     LENGTH ns = size_of_shape (Comb (CONS h t)) /\ i < LENGTH t
     ==> EL i (with_shape t (DROP (size_of_shape h) ns)) =
         TAKE (size_of_shape (EL i t))
              (DROP (size_of_shape h + size_of_shape (Comb (TAKE i t))) ns)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:shape list`; `DROP (size_of_shape h) (ns:A list)`; `i:num`]
                with_shape_el_take_drop_eq) THEN
  ANTS_TAC THENL
   [FS[LENGTH_DROP; size_of_shape_def; MAP; SUM] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_DROP_T] THEN REWRITE_TAC[ADD_SYM]]);;

let PSEMAUX_mem_with_shape_tail = prove
 (`!h t (ns:A list) z.
     LENGTH ns = size_of_shape (Comb (CONS h t)) /\
     MEM z (with_shape t (DROP (size_of_shape h) ns))
     ==> ?p m. z = TAKE p (DROP (size_of_shape h + m) ns)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[list_MEM_EL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `i < LENGTH (t:shape list)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_binary "<" o concl)) THEN
    MATCH_MP_TAC(ARITH_RULE `a = b ==> i < a ==> i < b`) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC length_with_shape_eq_shape THEN
    FS[LENGTH_DROP; size_of_shape_def; MAP; SUM] THEN ARITH_TAC;
    ASM_SIMP_TAC[PSEMAUX_with_shape_tail_el] THEN MESON_TAC[]]);;

let all_distinct_with_shape_distinct = prove
 (`!sh (ns:A list) x y.
     ALL_DISTINCT ns /\ LENGTH ns = size_of_shape (Comb sh) /\
     MEM x (with_shape sh ns) /\ MEM y (with_shape sh ns) /\ ~(x = y) /\
     ~(x = []) /\ ~(y = [])
     ==> DISJOINT (set_of_list x) (set_of_list y)`,
  LIST_INDUCT_TAC THEN RW[with_shape_def; MEM] THEN FS[] THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PSEMAUX_mem_with_shape_tail o
      CONJ (ASSUME `LENGTH (ns:A list) = size_of_shape (Comb (CONS h t))`)) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC disjoint_take_drop_sum THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PSEMAUX_mem_with_shape_tail o
      CONJ (ASSUME `LENGTH (ns:A list) = size_of_shape (Comb (CONS h t))`)) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DISJOINT_SYM] THEN
    MATCH_MP_TAC disjoint_take_drop_sum THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `DROP (size_of_shape h) (ns:A list)`) THEN
    ASM_SIMP_TAC[ALL_DISTINCT_DROP; LENGTH_DROP] THEN
    FS[size_of_shape_def; MAP; SUM] THEN ARITH_TAC]);;

let all_distinct_disjoint_with_shape = prove
 (`!sh (ns:A list) n n'.
     ALL_DISTINCT ns /\ n < LENGTH sh /\ n' < LENGTH sh /\ ~(n = n') /\
     LENGTH ns = size_of_shape (Comb sh)
     ==> DISJOINT (set_of_list (EL n (with_shape sh ns)))
                  (set_of_list (EL n' (with_shape sh ns)))`,
  LIST_INDUCT_TAC THEN RW[] THEN FS[with_shape_def] THEN
  NAMED_CASES_ON "n" ["";"n''"] THEN NAMED_CASES_ON "n'" ["";"n'''"] THEN
  FS[ARITH_ss; EL; HD; TL; LT_SUC; LENGTH] THENL
   [ASM_SIMP_TAC[PSEMAUX_with_shape_tail_el; disjoint_take_drop_sum];
    ASM_SIMP_TAC[PSEMAUX_with_shape_tail_el; disjoint_drop_take_sum];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[ALL_DISTINCT_DROP; LENGTH_DROP] THEN
    FS[size_of_shape_def; MAP; SUM] THEN ARITH_TAC]);;

let all_distinct_mem_zip_disjoint_with_shape = prove
 (`LENGTH (l:B list) = LENGTH sh /\ LENGTH sh = LENGTH (with_shape sh (ns:A list)) /\
   ALL_DISTINCT ns /\ LENGTH ns = size_of_shape (Comb sh) /\
   MEM (x,a,xs) (ZIP l (ZIP sh (with_shape sh ns))) /\
   MEM (y,b,ys) (ZIP l (ZIP sh (with_shape sh ns))) /\ ~(x = y)
   ==> DISJOINT (set_of_list xs) (set_of_list ys)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (l:B list) = LENGTH (ZIP sh (with_shape sh (ns:A list)))`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sh:shape list`; `with_shape sh (ns:A list)`] LENGTH_ZIP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP MEM_ZIP (ASSUME
    `LENGTH (l:B list) = LENGTH (ZIP sh (with_shape sh (ns:A list)))`)]) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  ASM_CASES_TAC `n = (n':num)` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `n < LENGTH (sh:shape list) /\ n' < LENGTH sh` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `xs = EL n' (with_shape sh (ns:A list)) /\ ys = EL n (with_shape sh ns)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sh:shape list`; `with_shape sh (ns:A list)`; `n:num`] EL_ZIP) THEN
    MP_TAC(ISPECL [`sh:shape list`; `with_shape sh (ns:A list)`; `n':num`] EL_ZIP) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST_ALL_TAC) THEN FS[PAIR_EQ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC all_distinct_disjoint_with_shape THEN
  ASM_MESON_TAC[]);;

(* an entry of the context ZIP vs (ZIP sh (with_shape sh ns)) (the shared  *)
(* first part of the HOL4 proofs of the next two theorems)                  *)

let PSEMAUX_alookup_zip_with_shape = prove
 (`!vs sh (ns:A list) (x:B) a xs.
     LENGTH ns = size_of_shape (Comb sh) /\ LENGTH vs = LENGTH sh /\
     ALOOKUP (ZIP vs (ZIP sh (with_shape sh ns))) x = SOME (a,xs)
     ==> MEM (x,a,xs) (ZIP vs (ZIP sh (with_shape sh ns))) /\
         ?n. n < LENGTH sh /\ xs = EL n (with_shape sh ns)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP ALOOKUP_MEM) THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP length_with_shape_eq_shape) THEN
  SUBGOAL_THEN `LENGTH (vs:B list) = LENGTH (ZIP sh (with_shape sh (ns:A list)))`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sh:shape list`; `with_shape sh (ns:A list)`] LENGTH_ZIP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DECIDE_TAC;
    ALL_TAC] THEN
  QPAT_X_ASSUM "MEM _ _" (MP_TAC o REWRITE_RULE[MATCH_MP MEM_ZIP (ASSUME
    `LENGTH (vs:B list) = LENGTH (ZIP sh (with_shape sh (ns:A list)))`)]) THEN
  STRIP_TAC THEN EXISTS_TAC `n:num` THEN
  SUBGOAL_THEN `n < LENGTH (sh:shape list)` ASSUME_TAC THENL
   [DECIDE_TAC; ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`sh:shape list`; `with_shape sh (ns:A list)`; `n:num`] EL_ZIP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN FS[PAIR_EQ]);;

let all_distinct_alist_no_overlap = prove
 (`ALL_DISTINCT (ns:num list) /\ LENGTH ns = size_of_shape (Comb sh) /\
   LENGTH (vs:A list) = LENGTH sh
   ==> pan_commonProps_no_overlap
         (alist_to_fmap (ZIP vs (ZIP sh (with_shape sh ns))))`,
  RW[] THEN REWRITE_TAC[pan_commonProps_no_overlap_def; ALOOKUP_EQ_FLOOKUP] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP PSEMAUX_alookup_zip_with_shape o
      CONJ (ASSUME `LENGTH (ns:num list) = size_of_shape (Comb sh)`) o
      CONJ (ASSUME `LENGTH (vs:A list) = LENGTH (sh:shape list)`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC all_distinct_with_shape THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN CCONTR_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP PSEMAUX_alookup_zip_with_shape o
      CONJ (ASSUME `LENGTH (ns:num list) = size_of_shape (Comb sh)`) o
      CONJ (ASSUME `LENGTH (vs:A list) = LENGTH (sh:shape list)`))) THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`sh:shape list`; `ns:num list`] length_with_shape_eq_shape) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~DISJOINT (set_of_list (xs:num list)) (set_of_list ys)` THEN
    REWRITE_TAC[] THEN
    MP_TAC(INST [`vs:A list`,`l:A list`]
      (INST_TYPE [`:A`,`:B`; `:num`,`:A`] all_distinct_mem_zip_disjoint_with_shape)) THEN
    ASM_REWRITE_TAC[]]);;

let all_distinct_alist_ctxt_max = prove
 (`ALL_DISTINCT (ns:num list) /\ LENGTH ns = size_of_shape (Comb sh) /\
   LENGTH (vs:A list) = LENGTH sh
   ==> pan_commonProps_ctxt_max (MAX_LIST ns)
         (alist_to_fmap (ZIP vs (ZIP sh (with_shape sh ns))))`,
  RW[] THEN REWRITE_TAC[pan_commonProps_ctxt_max_def; ALOOKUP_EQ_FLOOKUP; LE_0] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MEM (x:num) ns` (fun th -> MESON_TAC[th; MAX_LIST_PROPERTY]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PSEMAUX_alookup_zip_with_shape o
    CONJ (ASSUME `LENGTH (ns:num list) = size_of_shape (Comb sh)`) o
    CONJ (ASSUME `LENGTH (vs:A list) = LENGTH (sh:shape list)`)) THEN
  STRIP_TAC THEN MATCH_MP_TAC el_mem_with_shape THEN
  MAP_EVERY EXISTS_TAC [`sh:shape list`; `n:num`] THEN
  UNDISCH_TAC `MEM (x:num) xs` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`sh:shape list`; `ns:num list`] length_with_shape_eq_shape) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

let list_rel_flatten_with_shape_length = prove
 (`!sh (ns:B list) (args:((A)pan_v)list) v n.
     LENGTH ns = LENGTH (FLAT (MAP flatten args)) /\
     size_of_shape (Comb sh) = LENGTH (FLAT (MAP flatten args)) /\
     EL n args = v /\ n < LENGTH args /\ LENGTH args = LENGTH sh /\
     ALL2 (\sh arg. sh = shape_of arg) sh args /\
     ALL (is_wf_shape_v ([]:(mlstring#struct_info)list)) args
     ==> LENGTH (EL n (with_shape sh ns)) = LENGTH (flatten v)`,
  SUBGOAL_THEN `!y:(A)pan_v. is_wf_shape_v ([]:(mlstring#struct_info)list) y
                 ==> LENGTH (flatten y) = size_of_shape (shape_of y)` ASSUME_TAC THENL
   [MESON_TAC[length_flatten_eq_size_of_shape; is_wf_shape_v_nil]; ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN FS[EVERY2_THM] THEN
  RVEQ_TAC THEN
  FS[LENGTH; ALL; MAP; FLAT; LENGTH_APPEND; size_of_shape_def; SUM; with_shape_def] THEN
  NAMED_CASES_ON "n" ["";"n'"] THEN FS[EL; HD; TL; LT_SUC] THEN FS[ARITH_ss] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o SPECL
    [`DROP (size_of_shape (shape_of (y:(A)pan_v))) (ns:B list)`; `ys:((A)pan_v)list`]) THEN
  ASM_SIMP_TAC[LENGTH_DROP] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:(A)pan_v`) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* HOL4: by with_shape_el_take_drop_eq, EL_TAKE, EL_DROP and a split of shs *)
(* at n (LESS_LENGTH)                                                        *)

let el_el_with_shape = prove
 (`LENGTH (xs:A list) = size_of_shape (Comb shs) /\ n < LENGTH shs /\
   n' < size_of_shape (EL n shs) /\
   ALL (is_wf_shape ([]:(mlstring#struct_info)list)) shs
   ==> EL n' (EL n (with_shape shs xs)) =
       EL (n' + size_of_shape (Comb (TAKE n shs))) xs`,
  STRIP_TAC THEN ASM_SIMP_TAC[with_shape_el_take_drop_eq; EL_TAKE] THEN
  MATCH_MP_TAC EL_DROP THEN
  MP_TAC(ISPECL [`shs:shape list`; `n:num`] LESS_LENGTH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ys1:shape list` (X_CHOOSE_THEN `y:shape`
    (X_CHOOSE_THEN `ys2:shape list`
       (CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM))))) THEN
  FS[TAKE_LENGTH_APPEND; EL_LENGTH_APPEND; size_of_shape_def; MAP_APPEND;
     SUM_APPEND; MAP; SUM; HD; NULL] THEN
  ASM_ARITH_TAC);;

(* shapes of well-formed values are well formed *)

let PSEMAUX_all2_shape_of_wf = prove
 (`!shs (args:((A)pan_v)list) (ctxt:(mlstring#B)list).
     ALL2 (\sh arg. sh = shape_of arg) shs args /\ ALL (is_wf_shape_v ctxt) args
     ==> ALL (is_wf_shape ctxt) shs`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[EVERY2_THM; ALL] THEN
  STRIP_TAC THEN RVEQ_TAC THEN FS[ALL] THEN ASM_MESON_TAC[is_wf_shape_of_v]);;

(* HOL4 splits args and sh at n (LESS_LENGTH) and rewrites with             *)
(* el_el_with_shape and update_eq_zip_flookup (DEP_REWRITE_TAC)             *)

let list_rel_flatten_with_shape_flookup = prove
 (`!sh (ns:B list) (args:((A)pan_v)list) v n n'.
     ALL_DISTINCT ns /\ LENGTH ns = LENGTH (FLAT (MAP flatten args)) /\
     size_of_shape (Comb sh) = LENGTH (FLAT (MAP flatten args)) /\
     EL n args = v /\ n < LENGTH args /\ LENGTH args = LENGTH sh /\
     ALL2 (\sh arg. sh = shape_of arg) sh args /\
     ALL (is_wf_shape_v ([]:(mlstring#struct_info)list)) args /\
     LENGTH (EL n (with_shape sh ns)) = LENGTH (flatten v) /\
     n' < LENGTH (EL n (with_shape sh ns))
     ==> FLOOKUP (FEMPTY |++ ZIP ns (FLAT (MAP flatten args)))
                 (EL n' (EL n (with_shape sh ns))) = SOME (EL n' (flatten v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:(A)pan_v. is_wf_shape_v ([]:(mlstring#struct_info)list) y
                 ==> LENGTH (flatten y) = size_of_shape (shape_of y)` ASSUME_TAC THENL
   [MESON_TAC[length_flatten_eq_size_of_shape; is_wf_shape_v_nil]; ALL_TAC] THEN
  MP_TAC(ISPECL [`args:((A)pan_v)list`; `n:num`] LESS_LENGTH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:((A)pan_v)list` (X_CHOOSE_THEN `y:(A)pan_v`
    (X_CHOOSE_THEN `a2:((A)pan_v)list`
       (CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM))))) THEN
  MP_TAC(ISPECL [`sh:shape list`; `LENGTH (a1:((A)pan_v)list)`] LESS_LENGTH) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq (concl th) && rhs (concl th) = `LENGTH (sh:shape list)`)) THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:shape list` (X_CHOOSE_THEN `h:shape`
    (X_CHOOSE_THEN `s2:shape list` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EL_APPEND_EQN; LT_REFL; SUB_REFL; EL; HD; ALL_APPEND;
    ALL; MAP_APPEND; MAP; FLAT_APPEND; FLAT; LENGTH_APPEND; LENGTH]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq (concl th) && rhs (concl th) = `v:(A)pan_v`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP LIST_REL_APPEND_EQ (ASSUME
    `LENGTH (s1:shape list) = LENGTH (a1:((A)pan_v)list)`); ALL2]) THEN
  POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  SUBGOAL_THEN `size_of_shape (Comb s1) = LENGTH (FLAT (MAP flatten (a1:((A)pan_v)list)))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC list_rel_length_shape_of_flatten_better THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (flatten (y:(A)pan_v)) = size_of_shape (shape_of y)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (is_wf_shape ([]:(mlstring#struct_info)list))
                    (APPEND s1 (CONS (shape_of (y:(A)pan_v)) s2))` ASSUME_TAC THENL
   [REWRITE_TAC[ALL_APPEND; ALL] THEN
    ASM_MESON_TAC[PSEMAUX_all2_shape_of_wf; is_wf_shape_of_v];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `LENGTH (s1:shape list) = LENGTH (a1:((A)pan_v)list)`)) THEN
  MP_TAC(ISPECL [`ns:B list`; `APPEND s1 (CONS (shape_of (y:(A)pan_v)) s2)`;
                 `LENGTH (s1:shape list)`; `n':num`]
           (INST_TYPE [`:B`,`:A`]
              (GENL [`xs:A list`; `shs:shape list`; `n:num`; `n':num`]
                    el_el_with_shape))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; EL_APPEND_EQN; LT_REFL; SUB_REFL; EL; HD] THEN
    ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[TAKE_LENGTH_APPEND] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ns:B list`; `FEMPTY:(B,(A)word_lab)fmap`;
                 `FLAT (MAP flatten (APPEND a1 (CONS (y:(A)pan_v) a2)))`;
                 `n' + LENGTH (FLAT (MAP flatten (a1:((A)pan_v)list)))`]
                update_eq_zip_flookup) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MAP_APPEND; MAP; FLAT_APPEND; FLAT; LENGTH_APPEND] THEN
    ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[option_INJ; MAP_APPEND; MAP; FLAT_APPEND; FLAT; EL_APPEND_EQN] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(n' + l) - l = n':num`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* eval and the state.                                                       *)
(* ------------------------------------------------------------------------- *)

(* HOL4 [local]: OPT_MMAP_CONG instantiated (HOL4 writes the functions as   *)
(* \e. eval .. e; here eta-reduced, as in pan_eval_def)                      *)

let opt_mmap_helper_thm = prove
 (`!(f:(A,FFI)pan_state->(A,FFI)pan_state) st es.
     (!x. MEM x es ==> pan_eval (f st) x = pan_eval st x)
     ==> OPT_MMAP (pan_eval (f st)) es = OPT_MMAP (pan_eval st) es`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OPT_MMAP_CONG THEN ASM_REWRITE_TAC[]);;

let eval_some_var_exp_local_lookup = prove
 (`!s e (v:(A)pan_v) n.
     pan_eval (s:(A,FFI)pan_state) e = SOME v /\ MEM n (var_exp e)
     ==> ?w. FLOOKUP (pan_state_locals s) n = SOME w`,
  REC_IND_TAC pan_eval_ind THEN RW[] THEN
  GVS(all_case_eqs() @ [var_exp_def; MEM_FLAT; MEM_MAP; pan_eval_def; MEM_APPEND]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[UNZIP_DEF; PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN ASM_MESON_TAC[opt_mmap_mem_func; MEM_MAP]);;

let pan_eval_upd_clock_eq = prove
 (`!t e ck. pan_eval (pan_state_clock_fupd (K ck) (t:(A,FFI)pan_state)) e =
            pan_eval t e`,
  REC_IND_TAC pan_eval_ind THEN RW[] THEN ONCE_REWRITE_TAC[pan_eval_def] THEN
  ASM_SIMP_TAC[ISPEC `pan_state_clock_fupd (K (ck:num)):(A,FFI)pan_state->(A,FFI)pan_state`
                 opt_mmap_helper_thm] THEN
  SIMP[] THEN REPEAT(TOP_CASE_TAC THEN FS[]) THEN
  FS[ISPEC `pan_state_clock_fupd (K (ck:num)):(A,FFI)pan_state->(A,FFI)pan_state`
       opt_mmap_helper_thm] THEN
  GVS[] THEN RULE_ASSUM_TAC(REWRITE_RULE[o_DEF; GSYM NOT_ALL]) THEN ASM_MESON_TAC[]);;

let eval_upd_code_eq = prove
 (`!t e code. pan_eval (pan_state_code_fupd (K code) (t:(A,FFI)pan_state)) e =
              pan_eval t e`,
  REC_IND_TAC pan_eval_ind THEN RW[] THEN ONCE_REWRITE_TAC[pan_eval_def] THEN
  ASM_SIMP_TAC[ISPEC `pan_state_code_fupd (K code):(A,FFI)pan_state->(A,FFI)pan_state`
                 opt_mmap_helper_thm] THEN
  SIMP[] THEN REPEAT(TOP_CASE_TAC THEN FS[]) THEN
  FS[ISPEC `pan_state_code_fupd (K code):(A,FFI)pan_state->(A,FFI)pan_state`
       opt_mmap_helper_thm] THEN
  GVS[] THEN RULE_ASSUM_TAC(REWRITE_RULE[o_DEF; GSYM NOT_ALL]) THEN ASM_MESON_TAC[]);;

let eval_upd_eshapes_eq = prove
 (`!t e esh. pan_eval (pan_state_eshapes_fupd (K esh) (t:(A,FFI)pan_state)) e =
             pan_eval t e`,
  REC_IND_TAC pan_eval_ind THEN RW[] THEN ONCE_REWRITE_TAC[pan_eval_def] THEN
  ASM_SIMP_TAC[ISPEC `pan_state_eshapes_fupd (K esh):(A,FFI)pan_state->(A,FFI)pan_state`
                 opt_mmap_helper_thm] THEN
  SIMP[] THEN REPEAT(TOP_CASE_TAC THEN FS[]) THEN
  FS[ISPEC `pan_state_eshapes_fupd (K esh):(A,FFI)pan_state->(A,FFI)pan_state`
       opt_mmap_helper_thm] THEN
  GVS[] THEN RULE_ASSUM_TAC(REWRITE_RULE[o_DEF; GSYM NOT_ALL]) THEN ASM_MESON_TAC[]);;

(* HOL4: IMP_OPT_MMAP_EQ, MAP_EQ_EVERY2, LIST_REL_EL_EQN; here OPT_MMAP_CONG *)

let pan_opt_mmap_eval_upd_clock_eq = prove
 (`!es (s:(A,FFI)pan_state) ck.
     OPT_MMAP (pan_eval (pan_state_clock_fupd (K (ck + pan_state_clock s)) s)) es =
     OPT_MMAP (pan_eval s) es`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC OPT_MMAP_CONG THEN
  REWRITE_TAC[pan_eval_upd_clock_eq]);;

let opt_mmap_eval_upd_clock_eq1 = prove
 (`!es (s:(A,FFI)pan_state) ck.
     OPT_MMAP (pan_eval (pan_state_clock_fupd (K ck) s)) es = OPT_MMAP (pan_eval s) es`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC OPT_MMAP_CONG THEN
  REWRITE_TAC[pan_eval_upd_clock_eq]);;

(* ------------------------------------------------------------------------- *)
(* Clocks.                                                                   *)
(* ------------------------------------------------------------------------- *)

(* HOL4's >~ [`While`]: the first tactic on the goals whose conclusion       *)
(* mentions the constant, the second on the others                          *)

let PSEMAUX_IF_GOAL_HAS (c:string) (t1:tactic) (t2:tactic) : tactic =
  fun (asl,w as g) ->
    if can (find_term (fun t -> is_const t && fst(dest_const t) = c)) w
    then t1 g else t2 g;;

let pan_evaluate_add_clock_eq = prove
 (`!p t res st ck.
     pan_evaluate (p,t) = (res,st) /\ ~(res = SOME (pan_TimeOut:(A)pan_result))
     ==> pan_evaluate (p, pan_state_clock_fupd (K (pan_state_clock t + ck))
                            (t:(A,FFI)pan_state)) =
         (res, pan_state_clock_fupd (K (pan_state_clock st + ck)) st)`,
  REC_IND_TAC pan_evaluate_ind THEN RW[] THEN
  PSEMAUX_IF_GOAL_HAS "While"
    (ONCE_REWRITE_TAC[pan_evaluate_def] THEN QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
     RW[ONCE pan_evaluate_def] THEN GVS(pan_eval_upd_clock_eq :: all_case_eqs()) THEN
     REPEAT(PAIRARG_TAC THEN GVS[]) THEN
     GVS(ARITH_LIN_ss :: pan_dec_clock_def :: all_case_eqs()))
    (GVS(pan_evaluate_def :: pan_eval_upd_clock_eq :: all_case_eqs()) THEN
     REPEAT(PAIRARG_TAC THEN GVS[]) THEN
     GVS([ARITH_LIN_ss; ONELINE nb_op_def; pan_sh_mem_load_def; pan_sh_mem_store_def;
          pan_empty_locals_def; pan_dec_clock_def; opt_mmap_eval_upd_clock_eq1;
          kvar_defs] @ all_case_eqs()) THEN
     TRY(TOP_CASE_TAC THEN GVS[])));;

(* HOL4 proves evaluate_clock_sub by induction, with separate tactics for   *)
(* While, Seq, Dec, Call and DecCall.  Here the induction is for the         *)
(* equivalent form with ck <= the final clock (the shifted final state is   *)
(* then explicit), and every clause goes through the same steps: unfold      *)
(* the goal and the hypothesis once (the goal first: the hypothesis of the   *)
(* While clause has the loop again), split, the clock facts of               *)
(* pan_evaluate_clock, simplify with the hypotheses of the induction.        *)

let PSEMAUX_evaluate_clock_sub = prove
 (`!p s r s' ck.
     pan_evaluate (p,s) = (r,s') /\ ck <= pan_state_clock s' /\
     ~(r = SOME (pan_TimeOut:(A)pan_result))
     ==> pan_evaluate (p, pan_state_clock_fupd (K (pan_state_clock s - ck))
                            (s:(A,FFI)pan_state)) =
         (r, pan_state_clock_fupd (K (pan_state_clock s' - ck)) s')`,
  let simps = [ARITH_LIN_ss; ONELINE nb_op_def; pan_sh_mem_load_def;
               pan_sh_mem_store_def; pan_empty_locals_def; pan_dec_clock_def;
               kvar_defs; pan_state_INFO.ri_accfupds] in
  REC_IND_TAC pan_evaluate_ind THEN RW[] THEN
  ONCE_REWRITE_TAC[pan_evaluate_def] THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[pan_evaluate_def]) THEN
  REWRITE_TAC[pan_eval_upd_clock_eq; opt_mmap_eval_upd_clock_eq1;
              pan_state_INFO.ri_accfupds] THEN
  DISCH_TAC THEN GVS(all_case_eqs()) THEN REPEAT(PAIRARG_TAC THEN GVS[]) THEN
  IMP_RES_TAC pan_evaluate_clock THEN
  GVS(simps @ all_case_eqs()) THEN
  REPEAT(TOP_CASE_TAC THEN GVS(simps @ all_case_eqs())) THEN
  TRY(GVS(pan_state_component_equality :: simps) THEN NO_TAC));;

let evaluate_clock_sub = prove
 (`!p t res st ck.
     pan_evaluate (p,t) =
       (res, pan_state_clock_fupd (K (pan_state_clock st + ck)) st) /\
     ~(res = SOME (pan_TimeOut:(A)pan_result))
     ==> pan_evaluate (p, pan_state_clock_fupd (K (pan_state_clock t - ck))
                            (t:(A,FFI)pan_state)) = (res,st)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:(A)panLang_prog`; `t:(A,FFI)pan_state`;
                 `res:((A)pan_result)option`;
                 `pan_state_clock_fupd (K (pan_state_clock st + ck))
                    (st:(A,FFI)pan_state)`; `ck:num`]
                PSEMAUX_evaluate_clock_sub) THEN
  ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM; LE_ADDR; ADD_SUB] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[PAIR_EQ; pan_state_component_equality; pan_state_INFO.ri_accfupds;
              K_THM]);;

(* HOL4: from evaluate_clock_sub; here PSEMAUX_evaluate_clock_sub with the   *)
(* whole final clock                                                         *)

let evaluate_min_clock = prove
 (`pan_evaluate (prog,s) = (q,r) /\ ~(q = SOME (pan_TimeOut:(A)pan_result))
   ==> ?k. pan_evaluate (prog, pan_state_clock_fupd (K k) (s:(A,FFI)pan_state)) =
           (q, pan_state_clock_fupd (K 0) r)`,
  STRIP_TAC THEN
  EXISTS_TAC
    `pan_state_clock (s:(A,FFI)pan_state) - pan_state_clock (r:(A,FFI)pan_state)` THEN
  MP_TAC(ISPECL [`prog:(A)panLang_prog`; `s:(A,FFI)pan_state`;
                 `q:((A)pan_result)option`; `r:(A,FFI)pan_state`;
                 `pan_state_clock (r:(A,FFI)pan_state)`]
                PSEMAUX_evaluate_clock_sub) THEN
  ASM_REWRITE_TAC[LE_REFL; SUB_REFL]);;

let evaluate_add_clock_or_timeout = prove
 (`pan_evaluate (p,s) = (q, pan_state_clock_fupd (K 0) t) /\
   ~(q = SOME (pan_TimeOut:(A)pan_result))
   ==> pan_evaluate (p, pan_state_clock_fupd (K k) (s:(A,FFI)pan_state)) = (q',t')
   ==> (q' = SOME pan_TimeOut /\ k < pan_state_clock s \/
        q' = q /\ pan_state_clock s <= k /\
        t' = pan_state_clock_fupd (K (k - pan_state_clock s)) t)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `pan_state_clock (s:(A,FFI)pan_state) <= k` THENL
   [MP_TAC(ISPECL [`p:(A)panLang_prog`; `s:(A,FFI)pan_state`;
                   `q:((A)pan_result)option`;
                   `pan_state_clock_fupd (K 0) (t:(A,FFI)pan_state)`;
                   `k - pan_state_clock (s:(A,FFI)pan_state)`]
                  pan_evaluate_add_clock_eq) THEN
    ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[ARITH_RULE `a <= k ==> a + (k - a) = k:num`] THEN
    ASM_REWRITE_TAC[PAIR_EQ; pan_state_INFO.ri_fupdfupds; K_o_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISJ1_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN CCONTR_TAC THEN
  MP_TAC(ISPECL [`p:(A)panLang_prog`; `pan_state_clock_fupd (K k) (s:(A,FFI)pan_state)`;
                 `q':((A)pan_result)option`; `t':(A,FFI)pan_state`;
                 `pan_state_clock (s:(A,FFI)pan_state) - k`]
                pan_evaluate_add_clock_eq) THEN
  ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM; pan_state_INFO.ri_fupdfupds;
                  K_o_THM] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(a <= k) ==> k + (a - k) = a:num`] THEN
  SUBGOAL_THEN `pan_state_clock_fupd (K (pan_state_clock s)) (s:(A,FFI)pan_state) = s`
    SUBST1_TAC THENL
   [REWRITE_TAC[pan_state_component_equality; pan_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `pan_state_clock:(A,FFI)pan_state->num`) THEN
  REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* io events.                                                                *)
(* ------------------------------------------------------------------------- *)

(* HOL4 <<= is isPREFIX (infix <<=); the same steps for every clause (the   *)
(* hypothesis unfolded once, the induction hypotheses and IS_PREFIX_TRANS)  *)

let pan_evaluate_io_events_mono = prove
 (`!exps (s1:(A,FFI)pan_state) res s2.
     pan_evaluate (exps,s1) = (res,s2)
     ==> ffi_state_io_events (pan_state_ffi s1) <<=
         ffi_state_io_events (pan_state_ffi s2)`,
  REC_IND_TAC pan_evaluate_ind THEN RW[] THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[pan_evaluate_def]) THEN
  DISCH_TAC THEN
  GVS(all_case_eqs() @ [ONELINE nb_op_def; pan_sh_mem_load_def; pan_sh_mem_store_def;
      pan_empty_locals_def; kvar_defs; pan_dec_clock_def; call_FFI_def;
      pan_state_INFO.ri_accfupds; IS_PREFIX_REFL]) THEN
  REPEAT(PAIRARG_TAC THEN GVS[]) THEN
  GVS(all_case_eqs() @ [IS_PREFIX_REFL; IS_PREFIX_APPEND3; pan_state_INFO.ri_accfupds]) THEN
  ASM_MESON_TAC[IS_PREFIX_TRANS; IS_PREFIX_REFL]);;

(* the io events grow along any run *)

let PSEMAUX_io_events_mono_SND = prove
 (`!p (s:(A,FFI)pan_state).
     ffi_state_io_events (pan_state_ffi s) <<=
     ffi_state_io_events (pan_state_ffi (SND (pan_evaluate (p,s))))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC pan_evaluate_io_events_mono THEN
  EXISTS_TAC `p:(A)panLang_prog` THEN
  EXISTS_TAC `FST (pan_evaluate (p,s:(A,FFI)pan_state))` THEN REWRITE_TAC[]);;

(* the instances of PSEMAUX_io_events_mono_SND for the runs SND (pan_evaluate *)
(* (p,s0)) of the goal, then MESON with IS_PREFIX_TRANS on the prefix facts *)

let PSEMAUX_ADD_SND_MONO : tactic = fun (asl,w as g) ->
  let is_snd_eval t = try fst(dest_const(rator t)) = "SND" &&
                          fst(dest_const(fst(strip_comb(rand t)))) = "pan_evaluate"
                      with Failure _ -> false in
  let tms = setify (find_terms is_snd_eval w) in
  MAP_EVERY (fun t -> let p,s0 = dest_pair (rand(rand t)) in
      ASSUME_TAC (REWRITE_RULE[pan_state_INFO.ri_accfupds]
                   (ISPECL [p; s0] PSEMAUX_io_events_mono_SND))) tms g;;

let PSEMAUX_PREFIX_TAC : tactic = fun (asl,w as g) ->
  let pf = filter (fun (_,th) -> try fst(dest_const(fst(strip_comb(concl th)))) = "isPREFIX"
                                 with Failure _ -> false) asl in
  MESON_TAC (IS_PREFIX_TRANS :: IS_PREFIX_REFL :: map snd pf) g;;

(* HOL4 proves the form below (with res and s') by induction with separate  *)
(* tactics for While, Seq, Call and DecCall; here every clause goes through *)
(* the same steps: both runs unfolded once, the sub-runs that did not time  *)
(* out moved to the bigger clock by pan_evaluate_add_clock_eq, the          *)
(* induction hypotheses at the same extra clock, then the prefix facts      *)

let PSEMAUX_evaluate_add_clock_io_events_mono = prove
 (`!exps (s:(A,FFI)pan_state) extra res s'.
     pan_evaluate (exps,s) = (res,s')
     ==> ffi_state_io_events (pan_state_ffi s') <<=
         ffi_state_io_events (pan_state_ffi (SND (pan_evaluate
            (exps, pan_state_clock_fupd (K (pan_state_clock s + extra)) s))))`,
  let simps = [ARITH_LIN_ss; ONELINE nb_op_def; pan_sh_mem_load_def;
               pan_sh_mem_store_def; pan_empty_locals_def; kvar_defs; pan_dec_clock_def;
               pan_state_INFO.ri_accfupds; IS_PREFIX_REFL] in
  let is_forall_extra th =
    let c = concl th in
    is_forall c &&
    (let v,_ = dest_forall c in fst(dest_var v) = "extra" && type_of v = `:num`) in
  REC_IND_TAC pan_evaluate_ind THEN RW[] THEN
  ONCE_REWRITE_TAC[pan_evaluate_def] THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[pan_evaluate_def]) THEN
  REWRITE_TAC[pan_eval_upd_clock_eq; opt_mmap_eval_upd_clock_eq1;
              pan_state_INFO.ri_accfupds] THEN
  DISCH_TAC THEN GVS(all_case_eqs()) THEN REPEAT(PAIRARG_TAC THEN GVS[]) THEN
  GVS(simps @ all_case_eqs()) THEN
  IMP_RES_TAC pan_evaluate_add_clock_eq THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SPEC `extra:num` o check is_forall_extra)) THEN
  GVS(simps @ all_case_eqs()) THEN
  REPEAT(TOP_CASE_TAC THEN GVS(simps @ all_case_eqs())) THEN
  IMP_RES_TAC pan_evaluate_io_events_mono THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pan_state_INFO.ri_accfupds]) THEN PSEMAUX_ADD_SND_MONO THEN
  PSEMAUX_PREFIX_TAC);;

let pan_evaluate_add_clock_io_events_mono = prove
 (`!exps (s:(A,FFI)pan_state) extra.
     ffi_state_io_events (pan_state_ffi (SND (pan_evaluate (exps,s)))) <<=
     ffi_state_io_events (pan_state_ffi (SND (pan_evaluate
       (exps, pan_state_clock_fupd (K (pan_state_clock s + extra)) s))))`,
  MESON_TAC[PSEMAUX_evaluate_add_clock_io_events_mono; PAIR; SND]);;

(* the io events of a call of the oracle are longer *)

let PSEMAUX_APPEND_SING_NEQ = prove
 (`!l (x:A). ~(APPEND l [x] = l) /\ ~(l = APPEND l [x])`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `LENGTH:A list->num`) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC);;

let PSEMAUX_PREFIX_NEQ_TAC : tactic = fun (asl,w as g) ->
  let pf = filter (fun (_,th) -> let c = concl th in
             (try fst(dest_const(fst(strip_comb c))) = "isPREFIX" with Failure _ -> false) ||
             (is_neg c && is_eq (dest_neg c))) asl in
  MESON_TAC (IS_PREFIX_TRANS :: IS_PREFIX_ANTISYM :: map snd pf) g;;

(* HOL4 proves io_events_eq_imp_ffi_eq by induction, with a tactic per      *)
(* clause.  Here the induction is for the disjunctive form below (as a      *)
(* rewrite the HOL4 form would rewrite every pan_state_ffi t under          *)
(* conditions that mention pan_state_ffi t again), with the same steps for *)
(* every clause, then IS_PREFIX_TRANS and IS_PREFIX_ANTISYM                 *)

let PSEMAUX_io_events_eq_imp_ffi_eq = prove
 (`!p (s:(A,FFI)pan_state) res t.
     pan_evaluate (p,s) = (res,t)
     ==> pan_state_ffi t = pan_state_ffi s \/
         ~(ffi_state_io_events (pan_state_ffi s) =
           ffi_state_io_events (pan_state_ffi t))`,
  let simps = [PSEMAUX_APPEND_SING_NEQ; call_FFI_def; ONELINE nb_op_def;
               pan_sh_mem_load_def; pan_sh_mem_store_def; pan_empty_locals_def;
               kvar_defs; pan_dec_clock_def; pan_state_INFO.ri_accfupds] in
  REC_IND_TAC pan_evaluate_ind THEN RW[] THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[pan_evaluate_def]) THEN
  DISCH_TAC THEN GVS(all_case_eqs()) THEN REPEAT(PAIRARG_TAC THEN GVS[]) THEN
  GVS(simps @ all_case_eqs()) THEN
  REPEAT(TOP_CASE_TAC THEN GVS(simps @ all_case_eqs())) THEN
  IMP_RES_TAC pan_evaluate_io_events_mono THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pan_state_INFO.ri_accfupds]) THEN
  GVS(ffi_state_component_equality :: simps) THEN
  TRY(DISJ2_TAC THEN PSEMAUX_PREFIX_NEQ_TAC));;

let io_events_eq_imp_ffi_eq = prove
 (`pan_evaluate (p,s) = (res,t) /\
   ffi_state_io_events (pan_state_ffi s) = ffi_state_io_events (pan_state_ffi t)
   ==> pan_state_ffi t = pan_state_ffi (s:(A,FFI)pan_state)`,
  MESON_TAC[PSEMAUX_io_events_eq_imp_ffi_eq]);;

(* ------------------------------------------------------------------------- *)
(* Fresh variables, byte arrays.                                             *)
(* ------------------------------------------------------------------------- *)

(* HOL4 [local] *)

let not_mem_map_flat = prove
 (`~MEM (y:B) (FLAT (MAP (f:A->B list) xs)) <=> (!x. MEM x xs ==> ~MEM y (f x))`,
  REWRITE_TAC[MEM_MAP; MEM_FLAT] THEN MESON_TAC[]);;

(* HOL4 quantifies an unused v (of a free type) here and in                *)
(* update_locals_not_vars_eval_eq_NONE                                       *)

let update_locals_not_vars_eval_eq_eq = prove
 (`!s e (v:C) n w.
     ~MEM n (var_exp e)
     ==> pan_eval (pan_state_locals_fupd (K (pan_state_locals s |+ (n,w)))
                     (s:(A,FFI)pan_state)) e = pan_eval s e`,
  let helper = ISPEC `pan_state_locals_fupd
                        (K (pan_state_locals (s:(A,FFI)pan_state) |+
                            (n:mlstring,w:(A)pan_v))):(A,FFI)pan_state->(A,FFI)pan_state`
                 opt_mmap_helper_thm in
  REC_IND_TAC pan_eval_ind THEN RW[] THEN ONCE_REWRITE_TAC[pan_eval_def] THEN
  FS[var_exp_def; FLOOKUP_UPDATE; not_mem_map_flat; MEM_APPEND; DE_MORGAN_THM] THEN
  ASM_SIMP_TAC[helper] THEN SIMP[] THEN REPEAT(TOP_CASE_TAC THEN FS[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[UNZIP_DEF; PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN FS[helper] THEN
  GVS[] THEN RULE_ASSUM_TAC(REWRITE_RULE[o_DEF; GSYM NOT_ALL]) THEN ASM_MESON_TAC[]);;

let pan_update_locals_not_vars_eval_eq = prove
 (`!s e (v:(A)pan_v) n w.
     ~MEM n (var_exp e) /\ pan_eval s e = SOME v
     ==> pan_eval (pan_state_locals_fupd (K (pan_state_locals s |+ (n,w)))
                     (s:(A,FFI)pan_state)) e = SOME v`,
  SIMP_TAC[update_locals_not_vars_eval_eq_eq]);;

let update_locals_not_vars_eval_eq_NONE = prove
 (`!s e (v:C) n w.
     ~MEM n (var_exp e) /\ pan_eval s e = NONE
     ==> pan_eval (pan_state_locals_fupd (K (pan_state_locals s |+ (n,w)))
                     (s:(A,FFI)pan_state)) e = NONE`,
  SIMP_TAC[update_locals_not_vars_eval_eq_eq]);;

let eval_fresh_var = prove
 (`!s e n w.
     ~MEM n (var_exp e)
     ==> pan_eval (pan_state_locals_fupd (K (pan_state_locals s |+ (n,w)))
                     (s:(A,FFI)pan_state)) e = pan_eval s e`,
  REPEAT STRIP_TAC THEN QCASES_ON "pan_eval (s:(A,FFI)pan_state) e" THEN
  ASM_MESON_TAC[update_locals_not_vars_eval_eq_NONE;
                pan_update_locals_not_vars_eval_eq]);;

let OPT_MMAP_update_locals_not_vars_eval_eq = prove
 (`!s es (vs:((A)pan_v)list) n w.
     ~MEM n (FLAT (MAP var_exp es)) /\ OPT_MMAP (pan_eval s) es = SOME vs
     ==> OPT_MMAP (pan_eval (pan_state_locals_fupd (K (pan_state_locals s |+ (n,w)))
                               (s:(A,FFI)pan_state))) es = SOME vs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  RW[OPT_MMAP_def; MAP; FLAT; MEM_APPEND] THEN GVS(DE_MORGAN_THM :: all_case_eqs()) THEN
  ASM_SIMP_TAC[pan_update_locals_not_vars_eval_eq]);;

(* HOL4: by induction on bytes; here every (A)word_lab is a Word *)

let write_bytearray_update_byte = prove
 (`!bytes (ad:A word) ad' m adrs be.
     byte_aligned ad /\ (?w. m ad = Word w)
     ==> ?w. pan_write_bytearray ad' bytes m adrs be ad = Word w`,
  REPEAT STRIP_TAC THEN MESON_TAC[cases "word_lab"]);;

let read_write_bytearray_lemma = prove
 (`!n (addr:A word) bytes.
     good_dimindex(:A) /\
     read_bytearray addr n (pan_mem_load_byte m addrs be) = SOME bytes
     ==> pan_write_bytearray addr bytes m addrs be = m`,
  INDUCT_TAC THEN RW[read_bytearray_def] THEN
  GVS(all_case_eqs() @ [pan_mem_load_byte_def]) THEN
  RW[pan_write_bytearray_def] THEN ASM_REWRITE_TAC[pan_mem_store_byte_def] THEN
  SUBGOAL_THEN `8 <= dimindex(:A)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[good_dimindex_def] o
      check (fun th -> can (find_term ((=) `good_dimindex(:A)`)) (concl th))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SIMP[] THEN ASM_SIMP_TAC[set_byte_get_byte] THEN ASM_MESON_TAC[UPDATE_APPLY_ID]);;

let evaluate_clock_sub1 = prove
 (`!p t res st t' ck.
     pan_evaluate (p,t) = (res,st) /\ ~(res = SOME (pan_TimeOut:(A)pan_result)) /\
     pan_evaluate (p, pan_state_clock_fupd (K (ck + pan_state_clock t))
                        (t:(A,FFI)pan_state)) = pan_evaluate (p,t')
     ==> pan_evaluate (p,t) =
         pan_evaluate (p, pan_state_clock_fupd (K (pan_state_clock t' - ck)) t')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pan_evaluate (p,t') =
                (res, pan_state_clock_fupd (K (pan_state_clock st + ck))
                        (st:(A,FFI)pan_state))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SPECL [`ck:num`; `pan_state_clock (t:(A,FFI)pan_state)`] ADD_SYM] THEN
    MATCH_MP_TAC pan_evaluate_add_clock_eq THEN ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC evaluate_clock_sub THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Invariants of evaluate.                                                   *)
(* ------------------------------------------------------------------------- *)

(* HOL4 splits the conjunction and proves each part by induction; RW does    *)
(* the same here, and every clause of every part goes through the same      *)
(* steps (the hypothesis unfolded once and split)                           *)

let evaluate_invariants = prove
 (`!p t res (st:(A,FFI)pan_state).
     pan_evaluate (p,t) = (res,st)
     ==> pan_state_memaddrs st = pan_state_memaddrs t /\
         pan_state_sh_memaddrs st = pan_state_sh_memaddrs t /\
         pan_state_be st = pan_state_be t /\
         pan_state_eshapes st = pan_state_eshapes t /\
         pan_state_base_addr st = pan_state_base_addr t /\
         pan_state_structs st = pan_state_structs t /\
         pan_state_code st = pan_state_code t /\
         ffi_state_oracle (pan_state_ffi st) = ffi_state_oracle (pan_state_ffi t)`,
  let simps = [call_FFI_def; ONELINE nb_op_def; pan_sh_mem_load_def;
               pan_sh_mem_store_def; pan_empty_locals_def; kvar_defs; pan_dec_clock_def;
               pan_state_INFO.ri_accfupds] in
  REC_IND_TAC pan_evaluate_ind THEN RW[] THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[pan_evaluate_def]) THEN
  DISCH_TAC THEN GVS(all_case_eqs()) THEN REPEAT(PAIRARG_TAC THEN GVS[]) THEN
  GVS(simps @ all_case_eqs()) THEN
  REPEAT(TOP_CASE_TAC THEN GVS(simps @ all_case_eqs())));;

(* split on an equation x = y of variables whose negation occurs in the      *)
(* goal (a variable updated or not)                                          *)

let PSEMAUX_SPLIT_VAR_EQ_TAC : tactic = fun (asl,w as g) ->
  let eqs = find_terms (fun t -> is_neg t && is_eq (dest_neg t) &&
                          is_var (lhs (dest_neg t)) && is_var (rhs (dest_neg t))) w in
  match eqs with
    [] -> failwith "PSEMAUX_SPLIT_VAR_EQ_TAC"
  | t::_ -> ASM_CASES_TAC (dest_neg t) g;;

let evaluate_global_shape_invariant = prove
 (`!p s res (st:(A,FFI)pan_state) n v.
     pan_evaluate (p,s) = (res,st) /\ FLOOKUP (pan_state_globals s) n = SOME v
     ==> ?v'. FLOOKUP (pan_state_globals st) n = SOME v' /\
              shape_of v' = shape_of v`,
  let simps = [ONELINE nb_op_def; pan_sh_mem_load_def; pan_sh_mem_store_def;
               pan_empty_locals_def; kvar_defs; pan_dec_clock_def;
               pan_state_INFO.ri_accfupds; FLOOKUP_UPDATE] in
  REC_IND_TAC pan_evaluate_ind THEN RW[] THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[pan_evaluate_def]) THEN
  DISCH_TAC THEN GVS(all_case_eqs()) THEN REPEAT(PAIRARG_TAC THEN GVS[]) THEN
  GVS(simps @ all_case_eqs()) THEN
  REPEAT(TOP_CASE_TAC THEN GVS(simps @ all_case_eqs())) THEN
  TRY(PSEMAUX_SPLIT_VAR_EQ_TAC THEN
      GVS(shape_of_def :: shape_of_val :: all_case_eqs())) THEN
  TRY(ASM_MESON_TAC[]));;

(* HOL4 [local] *)

let evaluate_structs_invariant = prove
 (`pan_evaluate (p,s) = (res,s')
   ==> pan_state_structs s' = pan_state_structs (s:(A,FFI)pan_state)`,
  MESON_TAC[evaluate_invariants]);;

(* HOL4 [local]: the EVAL of the six accessor terms *)

let structs_simps = prove
 (`pan_state_structs (pan_dec_clock (s:(A,FFI)pan_state)) = pan_state_structs s /\
   pan_state_structs (pan_empty_locals s) = pan_state_structs s /\
   pan_state_globals (pan_dec_clock s) = pan_state_globals s /\
   pan_state_globals (pan_empty_locals s) = pan_state_globals s /\
   pan_state_locals (pan_dec_clock s) = pan_state_locals s /\
   pan_state_locals (pan_empty_locals s) = FEMPTY`,
  REWRITE_TAC[pan_dec_clock_def; pan_empty_locals_def; pan_state_INFO.ri_accfupds;
              K_THM]);;

(* HOL4 [local] *)

let FEVERY_res_var_FLOOKUP = prove
 (`FEVERY P (fm:(mlstring,(A)pan_v)fmap) /\ FEVERY P fm2
   ==> FEVERY P (pan_res_var fm (nm, FLOOKUP fm2 nm))`,
  QCASES_ON "FLOOKUP (fm2:(mlstring,(A)pan_v)fmap) nm" THEN
  SIMP[FEVERY_ALL_FLOOKUP; pan_res_var_def; FLOOKUP_UPDATE; DOMSUB_FLOOKUP_THM] THEN
  RW[] THEN EVERY_CASE_TAC THEN FS[] THEN ASM_MESON_TAC[]);;

let lookup_code_wf_shape_invariant_step = prove
 (CASE_TERM `OPT_MMAP (pan_eval s) argexps = SOME args /\
   pan_lookup_code (pan_state_code (s:(A,FFI)pan_state)) fname args =
     SOME (prog,newlocals,return_sh) /\
   FEVERY (\p. match p with (nm,v) -> is_wf_shape_v (pan_state_structs s) v)
          (pan_state_locals s) /\
   FEVERY (\p. match p with (nm,v) -> is_wf_shape_v (pan_state_structs s) v)
          (pan_state_globals s)
   ==> FEVERY (\p. match p with (nm,v) -> is_wf_shape_v (pan_state_structs s) v)
              newlocals`,
  RW[] THEN GVS(pan_lookup_code_def :: all_case_eqs()) THEN
  SIMP[FEVERY_ALL_FLOOKUP; flookup_fupdate_list; FLOOKUP_EMPTY] THEN RW[] THEN
  GVS(all_case_eqs()) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN REWRITE_TAC[MEM_REVERSE] THEN
  IMP_RES_TAC LIST_REL_LENGTH THEN
  SUBGOAL_THEN `LENGTH (MAP FST (x:(mlstring#shape)list)) = LENGTH (args:((A)pan_v)list)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  ASM_SIMP_TAC[MEM_ZIP; PAIR_EQ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `MEM (v:(A)pan_v) args` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEM_EL THEN ASM_MESON_TAC[LENGTH_MAP];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(MATCH_MP OPT_MMAP_MEM_IMP (CONJ
    (ASSUME `OPT_MMAP (pan_eval (s:(A,FFI)pan_state)) argexps = SOME args`)
    (ASSUME `MEM (v:(A)pan_v) args`))) THEN
  ASM_MESON_TAC[eval_is_wf_shape_v]);;

(* HOL4 has separate tactics for While, Call and DecCall; here every clause *)
(* goes through the same steps (the facts of evaluate_structs_invariant,    *)
(* lookup_code_wf_shape_invariant_step, eval_is_wf_shape_v and              *)
(* pan_primop_is_wf_shape_v for the hypotheses, then the FEVERY rules)      *)

let evaluate_is_wf_shape_invariant = prove
 (CASE_TERM `!p s res (s':(A,FFI)pan_state).
     pan_evaluate (p,s) = (res,s') /\
     FEVERY (\p. match p with (nm,v) -> is_wf_shape_v (pan_state_structs s) v)
            (pan_state_locals s) /\
     FEVERY (\p. match p with (nm,v) -> is_wf_shape_v (pan_state_structs s) v)
            (pan_state_globals s)
     ==> FEVERY (\p. match p with (nm,v) -> is_wf_shape_v (pan_state_structs s') v)
                (pan_state_locals s') /\
         FEVERY (\p. match p with (nm,v) -> is_wf_shape_v (pan_state_structs s') v)
                (pan_state_globals s') /\
         (match res with
            SOME (pan_Exception eid exn) -> is_wf_shape_v (pan_state_structs s) exn
          | SOME (pan_Return retv) -> is_wf_shape_v (pan_state_structs s) retv
          | _ -> T)`,
  let simps = [fevery_to_drestrict; FEVERY_res_var_FLOOKUP; ONELINE nb_op_def;
               pan_sh_mem_load_def; pan_sh_mem_store_def; pan_empty_locals_def; kvar_defs;
               pan_dec_clock_def; pan_state_INFO.ri_accfupds; FEVERY_FUPDATE;
               FEVERY_FEMPTY; is_wf_shape_v_def; ALL; structs_simps] in
  REC_IND_TAC pan_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT(GEN_TAC ORELSE DISCH_TAC) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[pan_evaluate_def]) THEN
  DISCH_TAC THEN GVS(all_case_eqs()) THEN REPEAT(PAIRARG_TAC THEN GVS[]) THEN
  IMP_RES_TAC evaluate_structs_invariant THEN
  IMP_RES_TAC (REWRITE_RULE[IMP_CONJ] lookup_code_wf_shape_invariant_step) THEN
  IMP_RES_TAC (REWRITE_RULE[IMP_CONJ] eval_is_wf_shape_v) THEN
  IMP_RES_TAC pan_primop_is_wf_shape_v THEN
  GVS(simps @ all_case_eqs()) THEN REPEAT(TOP_CASE_TAC THEN GVS(simps @ all_case_eqs())));;

(* every_exp: the quotations are split where a variable name (i, sh)     *)
(* changes type between clauses; the clauses are in HOL4 order              *)

let pan_every_exp_def = cake_def_wf_clauses
  `measure (\p:((A)panLang_exp->bool)#(A)panLang_exp. panLang_exp_size ARB (SND p))`
  PSEMAUX_EVAL_TC_TAC
  [`(pan_every_exp P (panLang_Const (w:A word)) <=> P (panLang_Const w)) /\
    (pan_every_exp P (panLang_Var vk v) <=> P (panLang_Var vk v)) /\
    (pan_every_exp P (RStruct es) <=> P (RStruct es) /\ ALL (pan_every_exp P) es) /\
    (pan_every_exp P (RField i e) <=> P (RField i e) /\ pan_every_exp P e) /\
    (pan_every_exp P (NStruct nm nm_es) <=>
       P (NStruct nm nm_es) /\ ALL (pan_every_exp P) (MAP SND nm_es))`;
   `(pan_every_exp P (NField i (e:(A)panLang_exp)) <=> P (NField i e) /\ pan_every_exp P e) /\
    (pan_every_exp P (panLang_Load sh e) <=> P (panLang_Load sh e) /\ pan_every_exp P e) /\
    (pan_every_exp P (panLang_Load32 e) <=> P (panLang_Load32 e) /\ pan_every_exp P e) /\
    (pan_every_exp P (LoadByte e) <=> P (LoadByte e) /\ pan_every_exp P e) /\
    (pan_every_exp P (panLang_Op bop es) <=> P (panLang_Op bop es) /\ ALL (pan_every_exp P) es) /\
    (pan_every_exp P (Panop op es) <=> P (Panop op es) /\ ALL (pan_every_exp P) es) /\
    (pan_every_exp P (Cmp c e1 e2) <=>
       P (Cmp c e1 e2) /\ pan_every_exp P e1 /\ pan_every_exp P e2)`;
   `(pan_every_exp P (panLang_Shift sh e1 (e2:(A)panLang_exp)) <=>
       P (panLang_Shift sh e1 e2) /\ pan_every_exp P e1 /\ pan_every_exp P e2) /\
    (pan_every_exp P BaseAddr <=> P BaseAddr) /\
    (pan_every_exp P TopAddr <=> P TopAddr) /\
    (pan_every_exp P BytesInWord <=> P BytesInWord)`];;
let pan_every_exp_ind = cake_ind "pan_every_exp";;

let pan_exps_of_def = sem1aux_def
  `(pan_exps_of (panLang_Raise eid (e:(A)panLang_exp)) = [e]) /\
   (pan_exps_of (Dec v sh e p) = CONS e (pan_exps_of p)) /\
   (pan_exps_of (panLang_Seq p q) = APPEND (pan_exps_of p) (pan_exps_of q)) /\
   (pan_exps_of (panLang_If e p q) = APPEND (CONS e (pan_exps_of p)) (pan_exps_of q)) /\
   (pan_exps_of (While e p) = CONS e (pan_exps_of p)) /\
   (pan_exps_of (panLang_Call NONE f es) = es) /\
   (pan_exps_of (panLang_Call (SOME (r, SOME (eid, v, ep))) f es) =
      APPEND es (pan_exps_of ep)) /\
   (pan_exps_of (panLang_Call (SOME (r, NONE)) f es) = es) /\
   (pan_exps_of (DecCall v sh f es p) = APPEND es (pan_exps_of p)) /\
   (pan_exps_of (panLang_Store e1 e2) = [e1;e2]) /\
   (pan_exps_of (panLang_Store32 e1 e2) = [e1;e2]) /\
   (pan_exps_of (StoreByte e1 e2) = [e1;e2]) /\
   (pan_exps_of (panLang_Return e) = [e]) /\
   (pan_exps_of (panLang_ExtCall f e1 e2 e3 e4) = [e1;e2;e3;e4]) /\
   (pan_exps_of (panLang_Assign vk v e) = [e]) /\
   (pan_exps_of (Primitive x y es) = es) /\
   (pan_exps_of (ShMemLoad op vk v e) = [e]) /\
   (pan_exps_of (ShMemStore op e1 e2) = [e1;e2]) /\
   (pan_exps_of (p:(A)panLang_prog) = [])`;;

(* HOL4's exp_cons_patterns: the constructor patterns of exp_nchotomy      *)

let PSEMAUX_exp_cons_patterns =
  let th = CONJUNCT1 (cases "panLang_exp") in
  map (fun t -> rand(snd(strip_exists t))) (disjuncts(snd(dest_forall(concl th))));;

(* HOL4 EVALs c pat for each pattern and folds the result back with GSYM   *)
(* real_def; the same here by rewriting, each conjunct quantified over the *)
(* variables of its pattern                                                *)

let PSEMAUX_EXP_SIMPS real_def =
  let c = lhs(concl real_def) in
  let conv = REWRITE_CONV[real_def] THENC REWRITE_CONV[pan_every_exp_def] THENC
             REWRITE_CONV[case_def "panLang_exp"] in
  let one pat =
    GENL (snd(strip_comb pat))
      (REWRITE_RULE[GSYM real_def] (conv (mk_icomb(c,pat)))) in
  end_itlist CONJ (map one PSEMAUX_exp_cons_patterns);;

let localised_exp_real_def = cake_def
  `localised_exp = pan_every_exp (\e:(A)panLang_exp.
     match e with panLang_Var tp _ -> tp = panLang_Local | _ -> T)`;;

let localised_exp_simps = PSEMAUX_EXP_SIMPS localised_exp_real_def;;

let nameless_exp_real_def = cake_def
  `nameless_exp = pan_every_exp (\e:(A)panLang_exp.
     match e with NStruct _ _ -> F | NField _ _ -> F | _ -> T)`;;

let nameless_exp_simps = PSEMAUX_EXP_SIMPS nameless_exp_real_def;;

let localised_prog_def = sem1aux_def
  `(localised_prog (panLang_Raise eid (e:(A)panLang_exp)) <=> localised_exp e) /\
   (localised_prog (Dec v sh e p) <=> localised_exp e /\ localised_prog p) /\
   (localised_prog (panLang_Seq p q) <=> localised_prog p /\ localised_prog q) /\
   (localised_prog (panLang_If e p q) <=>
      localised_exp e /\ localised_prog p /\ localised_prog q) /\
   (localised_prog (While e p) <=> localised_exp e /\ localised_prog p) /\
   (localised_prog (panLang_Store e1 e2) <=> localised_exp e1 /\ localised_exp e2) /\
   (localised_prog (panLang_Store32 e1 e2) <=> localised_exp e1 /\ localised_exp e2) /\
   (localised_prog (StoreByte e1 e2) <=> localised_exp e1 /\ localised_exp e2) /\
   (localised_prog (panLang_ExtCall fn e1 e2 e3 e4) <=>
      localised_exp e1 /\ localised_exp e2 /\ localised_exp e3 /\ localised_exp e4) /\
   (localised_prog (panLang_Return e) <=> localised_exp e) /\
   (localised_prog (ShMemStore op e1 e2) <=> localised_exp e1 /\ localised_exp e2) /\
   (localised_prog (ShMemLoad op vk v e) <=> vk = panLang_Local /\ localised_exp e) /\
   (localised_prog (panLang_Call hdl f args) <=>
      ALL localised_exp args /\
      (match hdl with SOME(_,SOME(_,_,p)) -> localised_prog p | _ -> T) /\
      (match hdl with SOME(SOME(panLang_Global,_),_) -> F | _ -> T)) /\
   (localised_prog (DecCall vn sh fn args p) <=>
      ALL localised_exp args /\ localised_prog p) /\
   (localised_prog (panLang_Assign panLang_Local v e) <=> localised_exp e) /\
   (localised_prog (panLang_Assign panLang_Global v e) <=> F) /\
   (localised_prog (Primitive x y es) <=> ALL localised_exp es) /\
   (localised_prog (p:(A)panLang_prog) <=> T)`;;

let evaluate_decls_eshapes = prove
 (`!s ds (s':(A,FFI)pan_state).
     evaluate_decls s ds = SOME s' ==>
     pan_state_eshapes s' = pan_state_eshapes s |++ exceptions ds`,
  REC_IND_TAC evaluate_decls_ind THEN
  RW[evaluate_decls_def; exceptions_def; FUPDATE_LIST_THM] THEN
  GVS(all_case_eqs()));;

let evaluate_decls_exns_wf = prove
 (CASE_TERM `!s ds (s':(A,FFI)pan_state).
     evaluate_decls s ds = SOME s' ==>
     ALL_DISTINCT (MAP FST (exceptions ds)) /\
     ALL (\p. match p with (eid,sh) -> FLOOKUP (pan_state_eshapes s) eid = NONE)
         (exceptions ds) /\
     ALL (is_wf_shape (pan_state_structs s) o SND) (exceptions ds)`,
  REC_IND_TAC evaluate_decls_ind THEN
  RW[evaluate_decls_def; exceptions_def] THEN GVS(all_case_eqs()) THEN
  GVS[GSYM ALL_MEM; MEM_MAP; FORALL_PAIR_THM; EXISTS_PAIR_THM; FLOOKUP_UPDATE] THEN
  ASM_MESON_TAC[]);;

let evaluate_decls_only_exn_decls = prove
 (`!s ds (s':(A,FFI)pan_state).
     ALL is_exn_decl ds /\ evaluate_decls s ds = SOME s' ==>
     s' = pan_state_eshapes_fupd (K (pan_state_eshapes s |++ exceptions ds)) s`,
  REC_IND_TAC evaluate_decls_ind THEN
  RW[evaluate_decls_def; exceptions_def; FUPDATE_LIST_THM] THEN
  GVS(RECORD_SELFID_ss :: is_exn_decl_def :: all_case_eqs()));;

(* HOL4 quantifies a variable s' that does not occur; here of type C         *)

let exns_wf_evaluate_decls = prove
 (CASE_TERM `!s ds (s':C).
     ALL is_exn_decl ds /\
     ALL_DISTINCT (MAP FST (exceptions ds)) /\
     ALL (\p. match p with (eid,sh) -> FLOOKUP (pan_state_eshapes s) eid = NONE)
         (exceptions ds) /\
     ALL (is_wf_shape (pan_state_structs s) o SND) (exceptions ds) ==>
     evaluate_decls (s:(A,FFI)pan_state) ds =
       SOME (pan_state_eshapes_fupd (K (pan_state_eshapes s |++ exceptions ds)) s)`,
  REC_IND_TAC evaluate_decls_ind THEN
  RW[exceptions_def; evaluate_decls_def; FUPDATE_LIST_THM; is_exn_decl_def] THEN
  GVS(RECORD_SELFID_ss :: all_case_eqs()) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  GVS[GSYM ALL_MEM; MEM_MAP; FORALL_PAIR_THM; EXISTS_PAIR_THM; FLOOKUP_UPDATE] THEN
  ASM_MESON_TAC[]);;

let evaluate_decl_commute = prove
 (`!s fi sh v' e (ds:((A)decl)list).
     evaluate_decls (s:(A,FFI)pan_state) (CONS (Function fi) (CONS (Decl sh v' e) ds)) =
     evaluate_decls s (CONS (Decl sh v' e) (CONS (Function fi) ds))`,
  RW[evaluate_decls_def] THEN
  TRY(REPEAT AP_THM_TAC THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC[GSYM pan_state_INFO.ri_fupdcanon] THEN
      REWRITE_TAC[eval_upd_code_eq] THEN NO_TAC) THEN
  TOP_CASE_TAC THEN SIMP[]);;

let functions_eq_FILTER = prove
 (CASE_TERM `!prog:((A)decl)list.
     functions prog =
     MAP (\x. match x with
                Function fi -> (fun_decl_name fi,fun_decl_params fi,fun_decl_body fi,
                                fun_decl_return fi)
              | _ -> ARB)
         (FILTER is_function prog)`,
  REC_IND_TAC (cake_ind "functions") THEN
  RW[functions_def; is_function_def; FILTER; MAP]);;

let functions_append = prove
 (`!prog1 prog2:((A)decl)list.
     functions (APPEND prog1 prog2) = APPEND (functions prog1) (functions prog2)`,
  RW[functions_eq_FILTER; MAP_APPEND; FILTER_APPEND]);;

let functions_FILTER = prove
 (`!prog:((A)decl)list. functions (FILTER is_function prog) = functions prog`,
  REC_IND_TAC (cake_ind "functions") THEN
  RW[functions_def; is_function_def; FILTER]);;

let functions_FILTER' = prove
 (`!prog:((A)decl)list. functions (FILTER is_decl prog) = []`,
  REC_IND_TAC (cake_ind "functions") THEN
  RW[functions_def; is_decl_def; FILTER]);;

let evaluate_decls_functions = prove
 (`!s pan_code (s':(A,FFI)pan_state).
     evaluate_decls s pan_code = SOME s' ==>
     pan_state_code s' = pan_state_code s |++ functions pan_code`,
  REC_IND_TAC evaluate_decls_ind THEN
  RW[evaluate_decls_def; functions_def; FUPDATE_LIST_THM] THEN
  GVS(all_case_eqs()));;

let evaluate_decls_only_functions = prove
 (`!s pan_code (s':(A,FFI)pan_state).
     ALL is_function pan_code /\ evaluate_decls s pan_code = SOME s' ==>
     s' = pan_state_code_fupd (K (pan_state_code s |++ functions pan_code)) s`,
  REC_IND_TAC evaluate_decls_ind THEN
  RW[evaluate_decls_def; functions_def; FUPDATE_LIST_THM] THEN
  GVS(RECORD_SELFID_ss :: is_function_def :: all_case_eqs()));;

let evaluate_decls_append = prove
 (CASE_TERM `!s ds1 (ds2:((A)decl)list).
     evaluate_decls (s:(A,FFI)pan_state) (APPEND ds1 ds2) =
     match evaluate_decls s ds1 with
       NONE -> NONE
     | SOME s' -> evaluate_decls s' ds2`,
  REC_IND_TAC evaluate_decls_ind THEN
  RW[evaluate_decls_def; APPEND] THEN
  REPEAT(TOP_CASE_TAC THEN GVS[]));;

let evaluate_decls_names = prove
 (`!s (decs:((A)decl)list).
     ALL is_name decs ==> evaluate_decls (s:(A,FFI)pan_state) decs = SOME s`,
  REC_IND_TAC evaluate_decls_ind THEN
  RW[evaluate_decls_def; is_name_def]);;

let evaluate_decls_only_funs_and_exn_decls = prove
 (`!s ds (s':(A,FFI)pan_state).
     ALL (\d. is_function d \/ is_exn_decl d) ds /\ evaluate_decls s ds = SOME s' ==>
     s' = pan_state_code_fupd (K (pan_state_code s |++ functions ds))
            (pan_state_eshapes_fupd (K (pan_state_eshapes s |++ exceptions ds)) s)`,
  REC_IND_TAC evaluate_decls_ind THEN
  RW[evaluate_decls_def; exceptions_def; functions_def; FUPDATE_LIST_THM] THEN
  GVS(RECORD_SELFID_ss :: is_exn_decl_def :: is_function_def :: all_case_eqs()));;

(* local in HOL4, where f and g are free                                    *)

let pan_opt_mmap_eq_some_helper = prove
 (`!(f:A->(B)option) g xs zs.
     OPT_MMAP f xs = SOME zs /\
     (!x. MEM x xs ==> !y. f x = SOME y ==> g x = SOME y) ==>
     OPT_MMAP g xs = SOME zs`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN RW[OPT_MMAP_def] THEN
  GVS(all_case_eqs()) THEN ASM_MESON_TAC[]);;

let eval_empty_locals_IMP = prove
 (`!s e (v:(A)pan_v).
     pan_eval (pan_state_locals_fupd (K FEMPTY) (s:(A,FFI)pan_state)) e = SOME v ==>
     pan_eval s e = SOME v`,
  REC_IND_TAC pan_eval_ind THEN RW[] THEN
  QPAT_X_ASSUM "pan_eval _ _ = _" (MP_TAC o ONCE_REWRITE_RULE[pan_eval_def]) THEN
  ONCE_REWRITE_TAC[pan_eval_def] THEN
  REWRITE_TAC[pan_state_INFO.ri_accfupds] THEN DISCH_TAC THEN
  GVS(all_case_eqs() @ [UNZIP_DEF; FLOOKUP_EMPTY]) THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  IMP_RES_TAC (REWRITE_RULE[IMP_CONJ] pan_opt_mmap_eq_some_helper) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ETA_AX]) THEN ASM_MESON_TAC[]);;

let decs_stcnames_only_functions = prove
 (`!ctxt (code:((A)decl)list).
     ALL (\d. is_function d \/ is_decl d \/ is_exn_decl d) code ==>
     decs_stcnames ctxt code = SOME ctxt`,
  REC_IND_TAC decs_stcnames_ind THEN
  SIMP[decs_stcnames_def; is_function_def; is_decl_def; is_exn_decl_def; ALL]);;

let decs_stcnames_only_functions2 = prove
 (`!ctxt (code:((A)decl)list).
     ALL is_function code ==> decs_stcnames ctxt code = SOME ctxt`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC decs_stcnames_only_functions THEN
  FS[GSYM ALL_MEM]);;

(* the main function is looked up by the call at clock 0                    *)

let semantics_decls_has_main = prove
 (`!(s:(A,FFI)pan_state) start (code:((A)decl)list).
     ~(semantics_decls s start code = Fail) ==>
     ?body rshape. FLOOKUP (pan_state_code s |++ functions code) start =
                   SOME ([],body,rshape)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[semantics_decls_def] THEN
  REPEAT(TOP_CASE_TAC THEN GVS[]) THEN
  IMP_RES_TAC evaluate_decls_functions THEN
  GVS[pan_semantics_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ONCE_REWRITE_TAC[pan_evaluate_def] THEN
  REWRITE_TAC[OPT_MMAP_def; pan_state_INFO.ri_accfupds; pan_lookup_code_def] THEN
  ASM_REWRITE_TAC[] THEN EVERY_CASE_TAC THEN GVS[]);;

(* HOL4 states and proves the same theorem twice                            *)

let pan_semantics_decls_has_main' = semantics_decls_has_main;;

let evaluate_decls_swap_locals = prove
 (`!s prog (s':(A,FFI)pan_state) locals.
     evaluate_decls s prog = SOME s' ==>
     evaluate_decls (pan_state_locals_fupd (K locals) s) prog =
       SOME (pan_state_locals_fupd (K locals) s')`,
  REC_IND_TAC evaluate_decls_ind THEN
  RW(evaluate_decls_def :: all_case_eqs()) THEN
  RES_TAC THEN FS[]);;

let mem_load_swap_memory = prove
 (`(!sh (addr:A word) addrs memory1 (stcs:(stcname#struct_info)list) v memory2.
      pan_mem_load sh addr addrs memory1 stcs = SOME v /\
      (!addr. addr IN addrs ==> memory1 addr = memory2 addr) ==>
      pan_mem_load sh addr addrs memory2 stcs = SOME v) /\
   (!shs (addr:A word) addrs memory1 (stcs:(stcname#struct_info)list) v memory2.
      mem_loads shs addr addrs memory1 stcs = SOME v /\
      (!addr. addr IN addrs ==> memory1 addr = memory2 addr) ==>
      mem_loads shs addr addrs memory2 stcs = SOME v) /\
   (!flds (addr:A word) addrs memory1 (stcs:(stcname#struct_info)list) vs memory2.
      mem_load_flds flds addr addrs memory1 stcs = SOME vs /\
      (!addr. addr IN addrs ==> memory1 addr = memory2 addr) ==>
      mem_load_flds flds addr addrs memory2 stcs = SOME vs)`,
  MATCH_MP_TAC pan_mem_load_ind THEN RW[pan_mem_load_def] THEN
  FS(all_case_eqs()) THEN GVS[]);;

(* HOL4's variable memory is mry here (memory is a constant of             *)
(* stack_removeProof, flagged by tools/const_capture.py)                    *)

let mem_load_swap_memaddrs = prove
 (`(!sh (addr:A word) addrs mry (stcs:(stcname#struct_info)list) v addrs2.
      pan_mem_load sh addr addrs mry stcs = SOME v /\ addrs SUBSET addrs2 ==>
      pan_mem_load sh addr addrs2 mry stcs = SOME v) /\
   (!shs (addr:A word) addrs mry (stcs:(stcname#struct_info)list) v addrs2.
      mem_loads shs addr addrs mry stcs = SOME v /\ addrs SUBSET addrs2 ==>
      mem_loads shs addr addrs2 mry stcs = SOME v) /\
   (!flds (addr:A word) addrs mry (stcs:(stcname#struct_info)list) vs addrs2.
      mem_load_flds flds addr addrs mry stcs = SOME vs /\ addrs SUBSET addrs2 ==>
      mem_load_flds flds addr addrs2 mry stcs = SOME vs)`,
  MATCH_MP_TAC pan_mem_load_ind THEN RW[pan_mem_load_def] THEN
  FS(all_case_eqs()) THEN GVS[] THEN ASM_MESON_TAC[SUBSET]);;

(* the induction is done with memaddrs fixed, so that the hypotheses of the *)
(* OPT_MMAP cases have the form of pan_opt_mmap_eq_some_helper             *)

let eval_swap_memaddrs = prove
 (`!s exp (v:(A)pan_v) memaddrs.
     pan_eval (s:(A,FFI)pan_state) exp = SOME v /\ pan_state_memaddrs s SUBSET memaddrs ==>
     pan_eval (pan_state_memaddrs_fupd (K memaddrs) s) exp = SOME v`,
  SUBGOAL_THEN
   `!memaddrs s exp (v:(A)pan_v).
      pan_eval (s:(A,FFI)pan_state) exp = SOME v /\
      pan_state_memaddrs s SUBSET memaddrs ==>
      pan_eval (pan_state_memaddrs_fupd (K memaddrs) s) exp = SOME v`
   (fun th -> MESON_TAC[th]) THEN
  GEN_TAC THEN REC_IND_TAC pan_eval_ind THEN RW[] THEN
  QPAT_X_ASSUM "pan_eval _ _ = _" (MP_TAC o ONCE_REWRITE_RULE[pan_eval_def]) THEN
  ONCE_REWRITE_TAC[pan_eval_def] THEN
  REWRITE_TAC[pan_state_INFO.ri_accfupds] THEN DISCH_TAC THEN
  GVS(all_case_eqs() @ [UNZIP_DEF; pan_mem_load_byte_def; pan_mem_load_32_def]) THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  IMP_RES_TAC mem_load_swap_memaddrs THEN
  IMP_RES_TAC (REWRITE_RULE[IMP_CONJ] pan_opt_mmap_eq_some_helper) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ETA_AX]) THEN
  ASM_REWRITE_TAC[SOME_11; UNWIND_THM1] THEN ASM_MESON_TAC[SUBSET]);;

let evaluate_decls_swap_memaddrs = prove
 (`!s prog (s':(A,FFI)pan_state) memaddrs.
     evaluate_decls s prog = SOME s' /\ pan_state_memaddrs s SUBSET memaddrs ==>
     evaluate_decls (pan_state_memaddrs_fupd (K memaddrs) s) prog =
       SOME (pan_state_memaddrs_fupd (K memaddrs) s')`,
  REC_IND_TAC evaluate_decls_ind THEN RW(evaluate_decls_def :: all_case_eqs()) THEN
  IMP_RES_TAC eval_swap_memaddrs THEN GVS[]);;

let eval_swap_memory = prove
 (`!s exp (v:(A)pan_v) mry.
     pan_eval (s:(A,FFI)pan_state) exp = SOME v /\
     (!addr. addr IN pan_state_memaddrs s ==> pan_state_memory s addr = mry addr) ==>
     pan_eval (pan_state_memory_fupd (K mry) s) exp = SOME v`,
  SUBGOAL_THEN
   `!mry s exp (v:(A)pan_v).
      pan_eval (s:(A,FFI)pan_state) exp = SOME v /\
      (!addr. addr IN pan_state_memaddrs s ==> pan_state_memory s addr = mry addr) ==>
      pan_eval (pan_state_memory_fupd (K mry) s) exp = SOME v`
   (fun th -> MESON_TAC[th]) THEN
  GEN_TAC THEN REC_IND_TAC pan_eval_ind THEN RW[] THEN
  QPAT_X_ASSUM "pan_eval _ _ = _" (MP_TAC o ONCE_REWRITE_RULE[pan_eval_def]) THEN
  ONCE_REWRITE_TAC[pan_eval_def] THEN
  REWRITE_TAC[pan_state_INFO.ri_accfupds] THEN DISCH_TAC THEN
  GVS(all_case_eqs() @ [UNZIP_DEF; pan_mem_load_byte_def; pan_mem_load_32_def]) THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  IMP_RES_TAC mem_load_swap_memory THEN
  IMP_RES_TAC (REWRITE_RULE[IMP_CONJ] pan_opt_mmap_eq_some_helper) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ETA_AX]) THEN
  ASM_REWRITE_TAC[SOME_11; UNWIND_THM1] THEN ASM_MESON_TAC[]);;

let evaluate_decls_swap_memory = prove
 (`!s prog (s':(A,FFI)pan_state) mry.
     evaluate_decls s prog = SOME s' /\
     (!addr. addr IN pan_state_memaddrs s ==> pan_state_memory s addr = mry addr) ==>
     evaluate_decls (pan_state_memory_fupd (K mry) s) prog =
       SOME (pan_state_memory_fupd (K mry) s')`,
  REC_IND_TAC evaluate_decls_ind THEN RW(evaluate_decls_def :: all_case_eqs()) THEN
  IMP_RES_TAC eval_swap_memory THEN GVS[]);;

(* HOL4 states and proves evaluate_decls_swap_memaddrs a second time        *)

let evaluate_decls_memaddrs_mono = evaluate_decls_swap_memaddrs;;

(* divergence *)

let evaluate_io_events_lprefix_chain = prove
 (`!p (s:(A,FFI)pan_state).
     lprefix_chain
       (IMAGE (\k. llist_fromList (ffi_state_io_events (pan_state_ffi
          (SND (pan_evaluate (p, pan_state_clock_fupd (K k) s)))))) (:num))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SET_RULE `IMAGE (\k. (g:B->C) ((f:A->B) k)) s = IMAGE g (IMAGE f s)`] THEN
  MATCH_MP_TAC prefix_chain_lprefix_chain THEN
  REWRITE_TAC[prefix_chain_def; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE;
              IN_UNIV] THEN
  SUBGOAL_THEN
   `!k1 k2. k1 <= k2 ==>
      ffi_state_io_events (pan_state_ffi (SND (pan_evaluate
        (p, pan_state_clock_fupd (K k1) (s:(A,FFI)pan_state))))) <<=
      ffi_state_io_events (pan_state_ffi (SND (pan_evaluate
        (p, pan_state_clock_fupd (K k2) s))))`
   (fun th -> MESON_TAC[th; LE_CASES]) THEN
  REWRITE_TAC[LE_EXISTS] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p:(A)panLang_prog`; `pan_state_clock_fupd (K k1) (s:(A,FFI)pan_state)`;
                 `d:num`] pan_evaluate_add_clock_io_events_mono) THEN
  SIMP[pan_state_INFO.ri_accfupds; pan_state_INFO.ri_fupdfupds]);;

(* ------------------------------------------------------------------------- *)
(* Semantics as a wrapper around a clocked function (HOL4: FIXME, port this  *)
(* or something like it to CakeML more broadly).                             *)
(* ------------------------------------------------------------------------- *)

let pan_semantics_run_res_INDUCT,pan_semantics_run_res_RECURSION = cake_type
  "pan_semantics_run_res = pan_RunError | pan_CompleteResult A | pan_Incomplete";;

(* HOL4's LUB is build_lprefix_lub, fromList is llist_fromList              *)

let pan_semantics_wrapper_def = cake_def
  `pan_semantics_wrapper (f:num->(outcome)pan_semantics_run_res#(io_event list)) =
     if ?k v. f k = (pan_RunError,v) then Fail
     else match (some res. ?k r ev. f k = (pan_CompleteResult r,ev) /\
                                    res = Terminate r ev) with
            SOME res -> res
          | NONE -> Diverge (build_lprefix_lub (IMAGE (llist_fromList o SND o f) (:num)))`;;

(* Helpers of semantics_wrapper_eq: results that are not Incomplete stay    *)
(* the same for larger clocks, so they are unique (det, some); results that *)
(* are always Incomplete give an lprefix chain (chain); the wrapper of a    *)
(* function without RunError (no_error) and without CompleteResult (none)   *)

let PSEMAUX_wrapper_det = prove
 (`!f:num->(B)pan_semantics_run_res#(C list).
     (!k k' r ev. f k = (r,ev) ==> ~(r = pan_Incomplete) ==> f (k + k') = (r,ev)) ==>
     !k1 k2 r1 ev1 r2 ev2.
       f k1 = (r1,ev1) /\ ~(r1 = pan_Incomplete) /\
       f k2 = (r2,ev2) /\ ~(r2 = pan_Incomplete) ==> r1 = r2 /\ ev1 = ev2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(SPECL [`k1:num`; `k2:num`] LE_CASES) THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  RES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN ASM_MESON_TAC[PAIR_EQ]);;

let PSEMAUX_wrapper_some = prove
 (`!f:num->(outcome)pan_semantics_run_res#(io_event list) k0 r0 ev0.
     (!k k' r ev. f k = (r,ev) ==> ~(r = pan_Incomplete) ==> f (k + k') = (r,ev)) /\
     f k0 = (pan_CompleteResult r0,ev0) ==>
     (some res. ?k r ev. f k = (pan_CompleteResult r,ev) /\ res = Terminate r ev) =
     SOME (Terminate r0 ev0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[some_DEF] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `res:behaviour` THEN BETA_TAC THEN EQ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `k0:num`; `pan_CompleteResult r:(outcome)pan_semantics_run_res`;
                `ev:io_event list`; `pan_CompleteResult r0:(outcome)pan_semantics_run_res`;
                `ev0:io_event list`]
         (UNDISCH(ISPEC `f:num->(outcome)pan_semantics_run_res#(io_event list)`
                       PSEMAUX_wrapper_det))) THEN
  ASM_REWRITE_TAC[distinctness "pan_semantics_run_res"; injectivity "pan_semantics_run_res"] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let PSEMAUX_wrapper_chain = prove
 (`!f:num->(B)pan_semantics_run_res#(C list).
     (!k k' ev. f (k + k') = (pan_Incomplete,ev) ==>
                ?r' ev'. f k = (r',ev') /\ ev' <<= ev) /\
     (!k. FST (f k) = pan_Incomplete) ==>
     lprefix_chain (IMAGE (llist_fromList o SND o f) (:num))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IMAGE_o] THEN
  MATCH_MP_TAC prefix_chain_lprefix_chain THEN
  REWRITE_TAC[prefix_chain_def; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE;
              IN_UNIV; o_THM] THEN
  SUBGOAL_THEN `!k1 k2. k1 <= k2 ==> SND ((f:num->(B)pan_semantics_run_res#(C list)) k1) <<=
                                     SND (f k2)`
    (fun th -> MESON_TAC[th; LE_CASES]) THEN
  REWRITE_TAC[LE_EXISTS] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k1:num`; `d:num`;
    `SND ((f:num->(B)pan_semantics_run_res#(C list)) (k1 + d))`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[PAIR]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let PSEMAUX_wrapper_no_error = prove
 (CASE_TERM `!f:num->(outcome)pan_semantics_run_res#(io_event list).
     (!k. ~(FST (f k) = pan_RunError)) ==>
     pan_semantics_wrapper f =
     match (some res. ?k r ev. f k = (pan_CompleteResult r,ev) /\ res = Terminate r ev) with
       SOME res -> res
     | NONE -> Diverge (build_lprefix_lub (IMAGE (llist_fromList o SND o f) (:num)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pan_semantics_wrapper_def] THEN
  SUBGOAL_THEN
    `~(?k v. (f:num->(outcome)pan_semantics_run_res#(io_event list)) k = (pan_RunError,v))`
    (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[FST]);;

let PSEMAUX_wrapper_none = prove
 (`!f:num->(outcome)pan_semantics_run_res#(io_event list).
     (!k. FST (f k) = pan_Incomplete) ==>
     (some res. ?k r ev. f k = (pan_CompleteResult r,ev) /\ res = Terminate r ev) = NONE`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[some_DEF] THEN COND_CASES_TAC THEN
  ASM_MESON_TAC[FST; distinctness "pan_semantics_run_res"]);;

(* HOL4's IS_PREFIX ev ev' is ev' <<= ev; absf and concf are free in HOL4   *)

let pan_semantics_wrapper_eq = prove
 (`!(absf:num->(outcome)pan_semantics_run_res#(io_event list)) concf.
   ~(pan_semantics_wrapper absf = Fail) ==>
   (!k r ev. absf k = (r,ev) /\ ~(r = pan_RunError) ==> ?k'. concf (k + k') = (r,ev)) ==>
   (!k k' r ev. concf k = (r,ev) ==> ~(r = pan_Incomplete) ==> concf (k + k') = (r,ev)) ==>
   (!k k' r ev. absf k = (r,ev) ==> ~(r = pan_Incomplete) ==> absf (k + k') = (r,ev)) ==>
   (!k k' ev. absf (k + k') = (pan_Incomplete,ev) ==>
              ?r' ev'. absf k = (r',ev') /\ ev' <<= ev) ==>
   (!k k' ev. concf (k + k') = (pan_Incomplete,ev) ==>
              ?r' ev'. concf k = (r',ev') /\ ev' <<= ev) ==>
   pan_semantics_wrapper concf = pan_semantics_wrapper absf`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(LABEL_TAC "h0") THEN DISCH_THEN(LABEL_TAC "h1") THEN
  DISCH_THEN(LABEL_TAC "h2") THEN DISCH_THEN(LABEL_TAC "h3") THEN
  DISCH_THEN(LABEL_TAC "h4") THEN DISCH_THEN(LABEL_TAC "h5") THEN
  (* neither function gives RunError *)
  SUBGOAL_THEN `!k. ~(FST ((absf:num->(outcome)pan_semantics_run_res#(io_event list)) k) = pan_RunError)` (LABEL_TAC "na") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REMOVE_THEN "h0" MP_TAC THEN REWRITE_TAC[pan_semantics_wrapper_def] THEN
    SUBGOAL_THEN `?k v. (absf:num->(outcome)pan_semantics_run_res#(io_event list)) k = (pan_RunError,v)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[PAIR];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. ~(FST ((concf:num->(outcome)pan_semantics_run_res#(io_event list)) k) = pan_RunError)` (LABEL_TAC "nc") THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?d. (concf:num->(outcome)pan_semantics_run_res#(io_event list)) (j + d) = (FST ((absf:num->(outcome)pan_semantics_run_res#(io_event list)) j), SND (absf j))`
      STRIP_ASSUME_TAC THENL
     [USE_THEN "h1" MATCH_MP_TAC THEN REWRITE_TAC[PAIR] THEN USE_THEN "na" MATCH_ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(concf:num->(outcome)pan_semantics_run_res#(io_event list)) (j + d) = (FST (concf j), SND (concf j))` ASSUME_TAC THENL
     [USE_THEN "h2" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
      ASM_REWRITE_TAC[PAIR; distinctness "pan_semantics_run_res"];
      ALL_TAC] THEN
    ASM_MESON_TAC[PAIR_EQ];
    ALL_TAC] THEN
  USE_THEN "na" (fun th -> REWRITE_TAC[MATCH_MP PSEMAUX_wrapper_no_error th]) THEN
  USE_THEN "nc" (fun th -> REWRITE_TAC[MATCH_MP PSEMAUX_wrapper_no_error th]) THEN
  ASM_CASES_TAC `?k0 r0 ev0. (absf:num->(outcome)pan_semantics_run_res#(io_event list)) k0 = (pan_CompleteResult r0,ev0)` THENL
   [(* a complete result: the same one for both *)
    FIRST_X_ASSUM(X_CHOOSE_THEN `k0:num` (X_CHOOSE_THEN `r0:outcome`
                    (X_CHOOSE_TAC `ev0:io_event list`))) THEN
    SUBGOAL_THEN `?d. (concf:num->(outcome)pan_semantics_run_res#(io_event list)) (k0 + d) = (pan_CompleteResult r0,ev0)`
      STRIP_ASSUME_TAC THENL
     [USE_THEN "h1" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[distinctness "pan_semantics_run_res"];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`absf:num->(outcome)pan_semantics_run_res#(io_event list)`; `k0:num`; `r0:outcome`; `ev0:io_event list`]
                  PSEMAUX_wrapper_some) THEN
    MP_TAC(ISPECL [`concf:num->(outcome)pan_semantics_run_res#(io_event list)`; `k0 + d:num`; `r0:outcome`; `ev0:io_event list`]
                  PSEMAUX_wrapper_some) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(DISCH_THEN(fun th -> REWRITE_TAC[th])) THEN REWRITE_TAC[option_CASE];
    ALL_TAC] THEN
  (* no complete result: both are always Incomplete *)
  SUBGOAL_THEN `!k. FST ((absf:num->(outcome)pan_semantics_run_res#(io_event list)) k) = pan_Incomplete` (LABEL_TAC "ia") THENL
   [X_GEN_TAC `k:num` THEN
    MP_TAC(ISPEC `FST ((absf:num->(outcome)pan_semantics_run_res#(io_event list)) k)` (cases "pan_semantics_run_res")) THEN
    STRIP_TAC THEN ASM_MESON_TAC[PAIR];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. FST ((concf:num->(outcome)pan_semantics_run_res#(io_event list)) k) = pan_Incomplete` (LABEL_TAC "ic") THENL
   [X_GEN_TAC `j:num` THEN
    SUBGOAL_THEN `?d. (concf:num->(outcome)pan_semantics_run_res#(io_event list)) (j + d) = (FST ((absf:num->(outcome)pan_semantics_run_res#(io_event list)) j), SND (absf j))`
      STRIP_ASSUME_TAC THENL
     [USE_THEN "h1" MATCH_MP_TAC THEN REWRITE_TAC[PAIR] THEN USE_THEN "na" MATCH_ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPEC `FST ((concf:num->(outcome)pan_semantics_run_res#(io_event list)) j)` (cases "pan_semantics_run_res")) THEN
    (* the Incomplete case is closed by STRIP_TAC *)
    STRIP_TAC THENL
     [ASM_MESON_TAC[];
      SUBGOAL_THEN `(concf:num->(outcome)pan_semantics_run_res#(io_event list)) (j + d) = (FST (concf j), SND (concf j))` ASSUME_TAC THENL
       [USE_THEN "h2" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
        ASM_REWRITE_TAC[PAIR; distinctness "pan_semantics_run_res"];
        ALL_TAC] THEN
      ASM_MESON_TAC[PAIR_EQ; distinctness "pan_semantics_run_res"]];
    ALL_TAC] THEN
  USE_THEN "ia" (fun th -> REWRITE_TAC[MATCH_MP PSEMAUX_wrapper_none th]) THEN
  USE_THEN "ic" (fun th -> REWRITE_TAC[MATCH_MP PSEMAUX_wrapper_none th]) THEN
  REWRITE_TAC[option_CASE] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC IMP_build_lprefix_lub_EQ THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PSEMAUX_wrapper_chain THEN CONJ_TAC THENL
     [USE_THEN "h5" MATCH_ACCEPT_TAC; USE_THEN "ic" MATCH_ACCEPT_TAC];
    MATCH_MP_TAC PSEMAUX_wrapper_chain THEN CONJ_TAC THENL
     [USE_THEN "h4" MATCH_ACCEPT_TAC; USE_THEN "ia" MATCH_ACCEPT_TAC];
    REWRITE_TAC[lprefix_rel_def; FORALL_IN_IMAGE; IN_UNIV; o_THM; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `k:num` THEN EXISTS_TAC `k:num` THEN
    REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE] THEN
    SUBGOAL_THEN `?d. (concf:num->(outcome)pan_semantics_run_res#(io_event list)) (k + d) = (FST ((absf:num->(outcome)pan_semantics_run_res#(io_event list)) k), SND (absf k))`
      STRIP_ASSUME_TAC THENL
     [USE_THEN "h1" MATCH_MP_TAC THEN REWRITE_TAC[PAIR] THEN USE_THEN "na" MATCH_ACCEPT_TAC;
      ALL_TAC] THEN
    USE_THEN "h5" (MP_TAC o SPECL [`k:num`; `d:num`; `SND ((absf:num->(outcome)pan_semantics_run_res#(io_event list)) k)`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[SND];
    REWRITE_TAC[lprefix_rel_def; FORALL_IN_IMAGE; IN_UNIV; o_THM; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `k:num` THEN
    SUBGOAL_THEN `?d. (concf:num->(outcome)pan_semantics_run_res#(io_event list)) (k + d) = (FST ((absf:num->(outcome)pan_semantics_run_res#(io_event list)) k), SND (absf k))`
      STRIP_ASSUME_TAC THENL
     [USE_THEN "h1" MATCH_MP_TAC THEN REWRITE_TAC[PAIR] THEN USE_THEN "na" MATCH_ACCEPT_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `k + d:num` THEN ASM_REWRITE_TAC[SND; LPREFIX_REFL]]);;

let pan_sem_is_wrapper = prove
 (CASE_TERM `!(s:(A,FFI)pan_state) start.
   pan_semantics s start =
   let prog = panLang_Call NONE start [] in
   pan_semantics_wrapper
     (((\res. match res with
                SOME pan_TimeOut -> pan_Incomplete
              | SOME (pan_FinalFFI e) -> pan_CompleteResult (FFI_outcome e)
              | SOME (pan_Return _) -> pan_CompleteResult Success
              | _ -> pan_RunError) ##
       (\s. ffi_state_io_events (pan_state_ffi s))) o
      (\k. pan_evaluate (prog, pan_state_clock_fupd (K k) s)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pan_semantics_def; pan_semantics_wrapper_def; LET_DEF; LET_END_DEF;
              o_THM; PAIR_MAP_DEF; PAIR_EQ] THEN
  MATCH_MP_TAC(MESON[] `(c1 <=> c2) /\ (x1:behaviour) = x2 ==>
                        (if c1 then (a:behaviour) else x1) = (if c2 then a else x2)`) THEN
  CONJ_TAC THENL
   [SIMP[] THEN AP_TERM_TAC THEN ABS_TAC THEN
    REPEAT(TOP_CASE_TAC THEN SIMP[distinctness "pan_semantics_run_res"]);
    ALL_TAC] THEN
  AP_THM_TAC THEN MK_COMB_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`k:num`; `outcome:outcome`;
        `ffi_state_io_events (pan_state_ffi (t:(A,FFI)pan_state))`] THEN
      ASM_REWRITE_TAC[] THEN POP_ASSUM(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
      REPEAT(TOP_CASE_TAC THEN SIMP[distinctness "pan_semantics_run_res";
                                    injectivity "pan_semantics_run_res"]);
      MAP_EVERY EXISTS_TAC [`k:num`;
        `SND (pan_evaluate (panLang_Call NONE start [],
                            pan_state_clock_fupd (K k) (s:(A,FFI)pan_state)))`;
        `FST (pan_evaluate (panLang_Call NONE start [],
                            pan_state_clock_fupd (K k) (s:(A,FFI)pan_state)))`;
        `r:outcome`] THEN
      ASM_REWRITE_TAC[PAIR] THEN
      POP_ASSUM(K ALL_TAC) THEN POP_ASSUM(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
      REPEAT(TOP_CASE_TAC THEN SIMP[distinctness "pan_semantics_run_res";
                                    injectivity "pan_semantics_run_res"])];
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM]]);;
